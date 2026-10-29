"""Retained-overlay checks use isolated copies of the immutable source snapshot."""
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
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
            parser = expected[kraken_compat.PARSER_RELATIVE].replace(b"\r\n", b"\n")
            restored = parser.replace(b"\n" + kraken_compat.SHIFT_HELPER.encode(), b"", 1)
            for mnemonic, shift, operation in (("lsl", "LSL", "LSLV"), ("lsr", "LSR", "LSRV")):
                restored = restored.replace(
                    f'  | "{mnemonic}"   => parseShiftAlias .{shift} .{operation}\n'.encode(),
                    f'  | "{mnemonic}"   => parseThreeRegs .{operation} -- Alias of {operation}\n'.encode())
            start = restored.index(b"def parseArithFlags ")
            end = restored.index(b"def parseCompare", start)
            restored = (restored[:start] + restored[start:end].replace(
                b"else if op2.isXzr then", b"else if op1W.2.isXzr || op2.isXzr then", 1) + restored[end:])
            self.assertEqual(restored, original[kraken_compat.PARSER_RELATIVE].replace(b"\r\n", b"\n"))
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


if __name__ == "__main__":
    unittest.main()
