"""Retained-overlay checks use isolated copies of the immutable source snapshot."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import subprocess
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
sys.path.insert(0, str(ROOT / "scripts"))
import kraken_compat
from integrity import check_kraken_snapshot


class KrakenCompatibilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        WORK.mkdir(parents=True, exist_ok=True)

    def fixture(self, temporary: Path) -> Path:
        root = temporary / "bridge"
        shutil.copytree(ROOT / "vendor/kraken", root / "vendor/kraken",
                        ignore=shutil.ignore_patterns(".lake"))
        (root / "compatibility").mkdir()
        shutil.copyfile(ROOT / "compatibility/kraken-list-name.patch",
                        root / "compatibility/kraken-list-name.patch")
        shutil.copyfile(ROOT / "compatibility/kraken-immediate-shifts.patch",
                        root / "compatibility/kraken-immediate-shifts.patch")
        shutil.copyfile(ROOT / "compatibility/kraken-zero-destination.patch",
                        root / "compatibility/kraken-zero-destination.patch")
        shutil.copyfile(ROOT / "pins.json", root / "pins.json")
        return root

    def test_overlay_changes_only_reviewed_sources_and_preserves_snapshot(self):
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            temporary = Path(temporary)
            root = self.fixture(temporary)
            vendor = root / "vendor/kraken"
            manifest = json.loads((vendor / "UPSTREAM.json").read_text(encoding="utf-8"))
            original = {name: (vendor / name).read_bytes() for name in manifest["files"]}
            manifest_before = (vendor / "UPSTREAM.json").read_bytes()
            with patch.object(kraken_compat, "ROOT", root), \
                    patch.object(kraken_compat, "WORK", temporary / "work"):
                expected, record = kraken_compat.expected_sources()
                destination = kraken_compat.prepare()
            self.assertEqual(check_kraken_snapshot(vendor)["status"], "PASS")
            self.assertEqual((vendor / "UPSTREAM.json").read_bytes(), manifest_before)
            self.assertEqual({name: (vendor / name).read_bytes() for name in original}, original)
            changed = [name for name in original if expected[name] != original[name]]
            self.assertEqual(set(changed), {kraken_compat.RELATIVE, kraken_compat.PARSER_RELATIVE})
            before = original[kraken_compat.RELATIVE]
            after = expected[kraken_compat.RELATIVE]
            self.assertEqual(before.count(b"allSome"), 2)
            self.assertEqual(after.count(b"krakenAllSome"), 2)
            self.assertNotIn(b"allSome", after)
            self.assertEqual(after, before.replace(b"allSome", b"krakenAllSome"))
            self.assertEqual(after.replace(b"krakenAllSome", b"allSome"), before)
            parser = expected[kraken_compat.PARSER_RELATIVE]
            self.assertNotIn(b"\r", parser)
            restored = parser.replace(b"\n" + kraken_compat.SHIFT_HELPER.encode(), b"", 1)
            for mnemonic, shift, operation in (("lsl", "LSL", "LSLV"), ("lsr", "LSR", "LSRV")):
                restored = restored.replace(
                    f'  | "{mnemonic}"   => parseShiftAlias .{shift} .{operation}\n'.encode(),
                    f'  | "{mnemonic}"   => parseThreeRegs .{operation} -- Alias of {operation}\n'.encode())
            start = restored.index(b"def parseArithFlags ")
            end = restored.index(b"def parseCompare", start)
            restored = (restored[:start] + restored[start:end].replace(
                b"else if op2.isXzr then", b"else if op1W.2.isXzr || op2.isXzr then", 1) + restored[end:])
            self.assertEqual(restored, original[kraken_compat.PARSER_RELATIVE])
            self.assertEqual(expected["Kraken/AArch64/Semantics.lean"], original["Kraken/AArch64/Semantics.lean"])
            self.assertEqual({name: (destination / name).read_bytes() for name in expected}, expected)
            written_record = json.loads((destination / "COMPATIBILITY.json").read_text(encoding="utf-8"))
            self.assertEqual(written_record, record)
            for name, data in expected.items():
                self.assertEqual(record["files"][name], hashlib.sha256(data).hexdigest())

    def test_tampered_pinned_patch_hash_rejected(self):
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            root = self.fixture(Path(temporary))
            pins = json.loads((root / "pins.json").read_text(encoding="utf-8"))
            pins["kraken"]["compatibility_patch_sha256"] = "0" * 64
            (root / "pins.json").write_text(json.dumps(pins), encoding="utf-8")
            with patch.object(kraken_compat, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "patch differs from pins.json"):
                    kraken_compat.expected_sources()

    def test_tampered_retained_patch_rejected(self):
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            root = self.fixture(Path(temporary))
            retained = root / "compatibility/kraken-list-name.patch"
            retained.write_bytes(retained.read_bytes() + b"\n# unexpected patch bytes\n")
            with patch.object(kraken_compat, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "namespace patch is stale"):
                    kraken_compat.expected_sources()

    def test_unexpected_source_pattern_rejected(self):
        mutations = {
            "extra_occurrence": lambda data: data + b"\n-- allSome\n",
            "missing_occurrence": lambda data: data.replace(b"allSome", b"otherName", 1),
            "already_renamed": lambda data: data.replace(b"allSome", b"krakenAllSome"),
        }
        for name, mutate in mutations.items():
            with self.subTest(pattern=name), tempfile.TemporaryDirectory(dir=WORK) as temporary:
                root = self.fixture(Path(temporary))
                vendor = root / "vendor/kraken"
                source = vendor / kraken_compat.RELATIVE
                source.write_bytes(mutate(source.read_bytes()))
                # Refresh only this isolated test manifest to exercise the inner
                # namespace-pattern gate rather than the earlier snapshot gate.
                manifest_path = vendor / "UPSTREAM.json"
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                manifest["files"][kraken_compat.RELATIVE] = hashlib.sha256(source.read_bytes()).hexdigest()
                if "git_blobs" in manifest:
                    data = source.read_bytes()
                    manifest["git_blobs"][kraken_compat.RELATIVE] = hashlib.sha1(
                        b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
                self.assertEqual(check_kraken_snapshot(vendor)["status"], "PASS")
                with patch.object(kraken_compat, "ROOT", root):
                    with self.assertRaisesRegex(ValueError, "unexpected Kraken helper definition or use"):
                        kraken_compat.expected_sources()

    def test_tampered_parser_patch_and_pin_rejected(self):
        for tamper in ("patch", "pin"):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory(dir=WORK) as temporary:
                root = self.fixture(Path(temporary))
                if tamper == "patch":
                    retained = root / "compatibility/kraken-immediate-shifts.patch"
                    retained.write_bytes(retained.read_bytes() + b"\n")
                    message = "parser patch is stale"
                else:
                    pins = json.loads((root / "pins.json").read_text())
                    pins["kraken"]["immediate_shift_patch_sha256"] = "0" * 64
                    (root / "pins.json").write_text(json.dumps(pins), encoding="utf-8")
                    message = "parser patch differs from pins.json"
                with patch.object(kraken_compat, "ROOT", root):
                    with self.assertRaisesRegex(ValueError, message):
                        kraken_compat.expected_sources()

    def test_parser_insertion_and_dispatch_patterns_are_exact(self):
        before = (ROOT / "vendor/kraken" / kraken_compat.PARSER_RELATIVE).read_bytes()
        mutations = [
            before.replace(b"def parseFourRegs", b"def unexpectedFourRegs"),
            before + b"\n-- parseShiftAlias\n",
            before.replace(b'"lsl"   => parseThreeRegs .LSLV', b'"lsl"   => unexpected .LSLV'),
        ]
        for source in mutations:
            with self.subTest(source=hashlib.sha256(source).hexdigest()):
                with self.assertRaisesRegex(ValueError, "unexpected Kraken"):
                    kraken_compat.parser_alias_source(source)

    def test_zero_destination_patch_and_guard_reject_tampering(self):
        for tamper in ("patch", "pin"):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory(dir=WORK) as temporary:
                root = self.fixture(Path(temporary))
                if tamper == "patch":
                    retained = root / "compatibility/kraken-zero-destination.patch"
                    retained.write_bytes(retained.read_bytes() + b"\n")
                    message = "zero-destination parser patch is stale"
                else:
                    pins = json.loads((root / "pins.json").read_text())
                    pins["kraken"]["zero_destination_patch_sha256"] = "0" * 64
                    (root / "pins.json").write_text(json.dumps(pins), encoding="utf-8")
                    message = "zero-destination parser patch differs from pins.json"
                with patch.object(kraken_compat, "ROOT", root):
                    with self.assertRaisesRegex(ValueError, message):
                        kraken_compat.expected_sources()
        original = (ROOT / "vendor/kraken" / kraken_compat.PARSER_RELATIVE).read_bytes()
        shifted = kraken_compat.parser_alias_source(original)
        fixed = kraken_compat.zero_destination_source(shifted)
        with self.assertRaisesRegex(ValueError, "zero-destination parser guard"):
            kraken_compat.zero_destination_source(fixed)

    def test_crlf_snapshot_and_parser_input_are_rejected_without_normalization(self):
        before = (ROOT / "vendor/kraken" / kraken_compat.PARSER_RELATIVE).read_bytes()
        self.assertNotIn(b"\r", before)
        converted = before.replace(b"\n", b"\r\n")
        self.assertNotEqual(converted, before)
        for transform in (kraken_compat.parser_alias_source, kraken_compat.zero_destination_source):
            with self.subTest(transform=transform.__name__), self.assertRaisesRegex(ValueError, "exact LF Git-blob bytes"):
                transform(converted)
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            root = self.fixture(Path(temporary))
            target = root / "vendor/kraken" / kraken_compat.PARSER_RELATIVE
            target.write_bytes(converted)
            with patch.object(kraken_compat, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "changed or missing Kraken source: Kraken/AArch64/Parser"):
                    kraken_compat.expected_sources()
                manifest_path = root / "vendor/kraken/UPSTREAM.json"
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                manifest["files"][kraken_compat.PARSER_RELATIVE] = hashlib.sha256(converted).hexdigest()
                manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "Kraken Git blob mismatch: Kraken/AArch64/Parser"):
                    kraken_compat.expected_sources()


def entrypoint(name, path):
    specification = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


class FreshCheckoutBytePolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        WORK.mkdir(parents=True, exist_ok=True)

    def test_real_local_clone_overrides_global_autocrlf_and_keeps_git_blob_bytes(self):
        bootstrap = entrypoint("real_lf_source_bootstrap", ROOT / "scripts/bootstrap.py")
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            fixture = Path(temporary)
            origin = fixture / "origin"
            global_config = fixture / "global.gitconfig"
            global_config.write_bytes(b"[core]\n\tautocrlf = true\n\teol = crlf\n")
            environment = os.environ.copy()
            for key in list(environment):
                if key in {"GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_CONFIG", "GIT_CONFIG_COUNT", "GIT_TEMPLATE_DIR"} or key.startswith(("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_")):
                    environment.pop(key)
            # This identity labels only an ephemeral synthetic Git fixture.
            environment.update(GIT_CONFIG_GLOBAL=str(global_config), GIT_CONFIG_NOSYSTEM="1",
                GIT_AUTHOR_NAME="synthetic-byte-policy-test", GIT_COMMITTER_NAME="synthetic-byte-policy-test",
                GIT_AUTHOR_EMAIL="fixture@example.invalid", GIT_COMMITTER_EMAIL="fixture@example.invalid")

            def git(*arguments):
                return subprocess.check_output(["git", *map(str, arguments)], env=environment, stderr=subprocess.PIPE)

            git("init", origin)
            source = origin / "exact.txt"
            exact = b"synthetic fixture line one\nsynthetic fixture line two\n"
            source.write_bytes(exact)
            git("-C", origin, "add", "--", source.name)
            git("-C", origin, "commit", "-m", "ephemeral synthetic byte-policy fixture")
            revision = git("-C", origin, "rev-parse", "HEAD").decode("ascii").strip()
            blob = git("-C", origin, "cat-file", "blob", "HEAD:" + source.name)
            self.assertEqual(blob, exact)
            source.unlink()
            git("-C", origin, "checkout", "HEAD", "--", source.name)
            self.assertEqual(source.read_bytes(), exact.replace(b"\n", b"\r\n"))
            work = fixture / "work"
            work.mkdir()
            with patch.dict(os.environ, environment, clear=True), patch.object(bootstrap, "ROOT", fixture / "bridge"):
                fresh = bootstrap.checkout(work, "fresh", {"repository": str(origin), "revision": revision})
            self.assertEqual(git("-C", fresh, "config", "--local", "--get", "core.autocrlf").strip(), b"false")
            self.assertEqual(git("-C", fresh, "config", "--local", "--get", "core.eol").strip(), b"lf")
            self.assertEqual((fresh / source.name).read_bytes(), blob)
            (fresh / source.name).unlink()
            git("-C", fresh, "checkout", "HEAD", "--", source.name)
            self.assertEqual((fresh / source.name).read_bytes(), blob)

    def test_extraction_clone_persists_lf_policy_before_checkout(self):
        bootstrap = entrypoint("lf_source_bootstrap", ROOT / "scripts/bootstrap.py")
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            work = Path(temporary)
            pin = {"repository": "https://example.invalid/fixture.git", "revision": "a" * 40}
            with patch.object(bootstrap, "run") as run, \
                    patch.object(bootstrap, "output", side_effect=[pin["revision"], ""]):
                bootstrap.checkout(work, "fresh", pin)
            clone, checkout = [call.args[0] for call in run.call_args_list]
            self.assertEqual(clone[:7], ["git", "clone", "--config", "core.autocrlf=false", "--config", "core.eol=lf", "--no-checkout"])
            self.assertEqual(checkout, ["git", "checkout", "--detach", pin["revision"]])
            self.assertEqual(run.call_args_list[1].kwargs["cwd"], work / "fresh")

    def test_existing_extraction_checkout_is_not_reset_or_reconfigured(self):
        bootstrap = entrypoint("existing_source_bootstrap", ROOT / "scripts/bootstrap.py")
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            work = Path(temporary)
            path = work / "existing"
            path.mkdir()
            pin = {"repository": "https://example.invalid/fixture.git", "revision": "a" * 40}
            with patch.object(bootstrap, "run") as run, \
                    patch.object(bootstrap, "output", side_effect=[pin["revision"], ""]):
                self.assertTrue(bootstrap.checkout(work, "existing", pin).samefile(path))
            run.assert_not_called()

    def test_fresh_proof_package_sets_local_lf_policy_before_checkout(self):
        bootstrap = entrypoint("lf_proof_bootstrap", ROOT / "proofs/bootstrap.py")
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            root = Path(temporary)
            revision = "a" * 40
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{
                "type": "git", "name": "fixture", "rev": revision, "url": "https://example.invalid/fixture.git"}]}), encoding="utf-8")
            with patch.object(bootstrap, "ROOT", root), \
                    patch.object(bootstrap, "checked") as checked, \
                    patch.object(bootstrap.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, stdout="")), \
                    patch.object(bootstrap.subprocess, "check_output", return_value=revision):
                bootstrap.fetch_locked_dependencies()
            commands = [call.args[0] for call in checked.call_args_list]
            target = root / ".lake/packages/fixture"
            autocrlf = ["git", "-C", str(target), "config", "--local", "core.autocrlf", "false"]
            eol = ["git", "-C", str(target), "config", "--local", "core.eol", "lf"]
            checkout = ["git", "-C", str(target), "checkout", "--detach", revision]
            self.assertLess(commands.index(autocrlf), commands.index(checkout))
            self.assertLess(commands.index(eol), commands.index(checkout))

    def test_existing_proof_checkout_is_not_reconfigured(self):
        bootstrap = entrypoint("existing_proof_bootstrap", ROOT / "proofs/bootstrap.py")
        with tempfile.TemporaryDirectory(dir=WORK) as temporary:
            root = Path(temporary)
            target = root / ".lake/packages/fixture"
            (target / ".git").mkdir(parents=True)
            revision = "a" * 40
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{
                "type": "git", "name": "fixture", "rev": revision, "url": "https://example.invalid/fixture.git"}]}), encoding="utf-8")
            with patch.object(bootstrap, "ROOT", root), \
                    patch.object(bootstrap, "checked") as checked, \
                    patch.object(bootstrap.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, stdout=revision)), \
                    patch.object(bootstrap.subprocess, "check_output", return_value=revision):
                bootstrap.fetch_locked_dependencies()
            self.assertEqual([call.args[0] for call in checked.call_args_list],
                             [["git", "-C", str(target), "diff", "--quiet", "HEAD", "--"]])


if __name__ == "__main__":
    unittest.main()
