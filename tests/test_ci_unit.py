"""Fail-closed CI tests use temporary source trees and captured child output."""
import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
sys.path.insert(0, str(ROOT / "scripts"))
import ci_unit
import check_proof_dependencies


class TemporarySourceTest(unittest.TestCase):
    def setUp(self):
        WORK.mkdir(exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="ci-unit-test-", dir=WORK)
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name).resolve()
        self.root = self.base / "source"
        self.root.mkdir()
        self.output = self.base / "artifacts"

    def manifest(self):
        files = ci_unit.source_files(self.root)
        value = {"format": 1, "archive_prefix": ci_unit.ARCHIVE_PREFIX,
                 "files": {name: ci_unit.digest(path) for name, path in files.items()}}
        (self.root / "SOURCE-MANIFEST.json").write_text(json.dumps(value), encoding="utf-8")
        return value


class SourceManifestTests(TemporarySourceTest):
    def setUp(self):
        super().setUp()
        (self.root / "source.py").write_text("retained source\n", encoding="utf-8")
        self.manifest()

    def test_fresh_manifest_and_hash_tampering(self):
        self.assertEqual(ci_unit.check_source_manifest(self.root)["checked_files"], 1)
        (self.root / "source.py").write_text("changed source\n", encoding="utf-8")
        with self.assertRaisesRegex(ci_unit.CiError, "hash mismatch"):
            ci_unit.check_source_manifest(self.root)

    def test_missing_and_unlisted_sources_fail(self):
        source = self.root / "source.py"
        source.unlink()
        with self.assertRaisesRegex(ci_unit.CiError, "file set differs"):
            ci_unit.check_source_manifest(self.root)
        source.write_text("retained source\n", encoding="utf-8")
        for relative in ("evidence/new.log", "proofs/New.lean", ".github/workflows/new.yml"):
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("unlisted input", encoding="utf-8")
            with self.subTest(path=relative), self.assertRaisesRegex(ci_unit.CiError, "unlisted"):
                ci_unit.check_source_manifest(self.root)
            path.unlink()

    def test_only_top_level_manifest_and_build_cache_are_excluded(self):
        for relative in (".lake/build/Cache.olean", "scripts/__pycache__/cache.pyc",
                         "work/scratch.log", ".git/config", "proofs/Cache.ilean"):
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"build/cache fixture")
        self.assertEqual(ci_unit.check_source_manifest(self.root)["checked_files"], 1)
        nested = self.root / "vendor/SOURCE-MANIFEST.json"
        nested.parent.mkdir()
        nested.write_text("{}", encoding="utf-8")
        with self.assertRaisesRegex(ci_unit.CiError, "unlisted"):
            ci_unit.check_source_manifest(self.root)

    def test_unsafe_paths_duplicate_keys_and_self_entry_fail(self):
        manifest_path = self.root / "SOURCE-MANIFEST.json"
        for relative in ("../escape", "/absolute", "C:/absolute", "a\\b", "a/../b", "./source.py"):
            value = {"format": 1, "archive_prefix": ci_unit.ARCHIVE_PREFIX,
                     "files": {relative: "0" * 64}}
            manifest_path.write_text(json.dumps(value), encoding="utf-8")
            with self.subTest(path=relative), self.assertRaisesRegex(ci_unit.CiError, "unsafe"):
                ci_unit.check_source_manifest(self.root)
        manifest_path.write_text('{"format":1,"format":1}', encoding="utf-8")
        with self.assertRaisesRegex(ci_unit.CiError, "duplicate JSON key"):
            ci_unit.check_source_manifest(self.root)
        value = self.manifest()
        value["files"]["SOURCE-MANIFEST.json"] = "0" * 64
        manifest_path.write_text(json.dumps(value), encoding="utf-8")
        with self.assertRaisesRegex(ci_unit.CiError, "file set differs"):
            ci_unit.check_source_manifest(self.root)


class RetainedExtractionTests(TemporarySourceTest):
    def setUp(self):
        super().setUp()
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        for name in ("charon-asm.json", "pasta_curves.llbc", "extraction-provenance.json"):
            shutil.copyfile(ROOT / "artifacts" / name, artifacts / name)
        self.pins = ci_unit.load_json(ROOT / "pins.json")

    def change_json(self, name, change):
        path = self.root / "artifacts" / name
        value = ci_unit.load_json(path)
        change(value)
        path.write_text(json.dumps(value), encoding="utf-8")

    def test_complete_retained_raw_and_pin_links(self):
        result = ci_unit.check_retained_extraction(self.root, self.pins)
        self.assertEqual(result["routines"], ["add", "mul"])
        self.assertFalse(result["raw_has_errors"])

    def test_changed_raw_or_operand_subtree_fails(self):
        raw = self.root / "artifacts/pasta_curves.llbc"
        original = raw.read_bytes()
        raw.write_bytes(original + b" ")
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            ci_unit.check_retained_extraction(self.root, self.pins)
        raw.write_bytes(original)
        self.change_json("charon-asm.json", lambda value:
                         value["routines"]["add"]["operands"].reverse())
        with self.assertRaisesRegex(ValueError, "envelope differs"):
            ci_unit.check_retained_extraction(self.root, self.pins)

    def test_changed_source_or_compiler_pin_fails(self):
        for component in ("pasta", "extraction"):
            pins = copy.deepcopy(self.pins)
            pins[component]["revision"] = "0" * 40
            with self.subTest(component=component), self.assertRaisesRegex(ci_unit.CiError, "pins? differ"):
                ci_unit.check_retained_extraction(self.root, pins)

    def test_raw_filename_traversal_is_rejected_before_open(self):
        self.change_json("charon-asm.json", lambda value:
                         value["extraction"].update(raw_artifact="../outside.llbc"))
        with patch.object(ci_unit, "verify_retained") as raw_check:
            with self.assertRaisesRegex(ci_unit.CiError, "extraction pins differ"):
                ci_unit.check_retained_extraction(self.root, self.pins)
        raw_check.assert_not_called()

    def test_inconsistent_build_provenance_fails(self):
        self.change_json("extraction-provenance.json", lambda value:
                         value["build_record"]["binaries"].update(charon="0" * 64))
        with self.assertRaisesRegex(ci_unit.CiError, "build record is inconsistent"):
            ci_unit.check_retained_extraction(self.root, self.pins)


class LockedDependencyTests(TemporarySourceTest):
    def setUp(self):
        super().setUp()
        (self.root / "proofs").mkdir()
        shutil.copyfile(ROOT / "pins.json", self.root / "pins.json")
        shutil.copyfile(ROOT / "proofs/lake-manifest.json", self.root / "proofs/lake-manifest.json")

    def check(self):
        pins = ci_unit.load_json(self.root / "pins.json")
        with patch.object(ci_unit, "check_pasta_snapshot", return_value={"commit": pins["pasta"]["revision"]}), \
                patch.object(ci_unit, "check_kraken_snapshot", return_value={"commit": pins["kraken"]["revision"]}), \
                patch.object(ci_unit, "check_retained_extraction", return_value={"fixture": True}), \
                patch.object(check_proof_dependencies, "git", side_effect=AssertionError("unit CI must not invoke Git")):
            return ci_unit.check_source_integrity(self.root)

    def test_locked_dependency_count_without_local_checkouts(self):
        result = self.check()
        self.assertEqual(result["locked_git_package_count"], 9)
        self.assertEqual(len(result["locked_git_packages"]), 9)
        self.assertFalse((self.root / "proofs/.lake").exists())

    def test_lock_revision_disagreeing_with_mathlib_pin_fails(self):
        path = self.root / "proofs/lake-manifest.json"
        lock = ci_unit.load_json(path)
        next(package for package in lock["packages"] if package["name"] == "mathlib")["rev"] = "0" * 40
        path.write_text(json.dumps(lock), encoding="utf-8")
        with self.assertRaisesRegex(check_proof_dependencies.ProofDependencyError, "Mathlib lock does not match"):
            self.check()


class CiRunnerTests(TemporarySourceTest):
    def setUp(self):
        super().setUp()
        (self.root / "source.py").write_text("fixture source", encoding="utf-8")
        self.manifest()

    def subprocess(self, command, *, stdout, **kwargs):
        if "unittest" in command:
            stdout.write(b"test_fixture ... ok\n\nRan 2 tests in 0.001s\n\nOK\n")
        else:
            self.assertIn("--check", command)
            stdout.write(b"PASS\n")
        self.assertTrue(Path(kwargs["cwd"]).samefile(self.root))
        self.assertEqual(kwargs["env"]["PYTHONDONTWRITEBYTECODE"], "1")
        return subprocess.CompletedProcess(command, 0)

    def run_fixture(self, child=None):
        with patch.object(ci_unit, "check_source_integrity", return_value={"fixture": "consistent"}), \
                patch.object(ci_unit.subprocess, "run", side_effect=child or self.subprocess), \
                redirect_stdout(io.StringIO()):
            return ci_unit.run_ci(self.root, self.output)

    def test_required_stages_and_logs_do_not_modify_sources(self):
        before = {path.name: path.read_bytes() for path in self.root.iterdir()}
        result = self.run_fixture()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["missing_or_failed_checks"], [])
        self.assertEqual({stage["name"] for stage in result["stages"]}, ci_unit.REQUIRED_STAGES)
        self.assertEqual(ci_unit.load_json(self.output / "report.json"), result)
        for stage in result["stages"]:
            self.assertTrue((self.output / stage["log"]).is_file())
        self.assertEqual({path.name: path.read_bytes() for path in self.root.iterdir()}, before)

    def test_subprocess_fixture_accepts_directory_alias_and_rejects_other_directory(self):
        # Existing paths may have different spellings, including Windows 8.3
        # aliases. Keep the guard about filesystem identity, not string equality.
        child = self.root / "alias-child"
        child.mkdir()
        alias = child / ".."
        other = self.base / "different-source"
        other.mkdir()
        command = [sys.executable, "fixture.py", "--check"]
        env = {"PYTHONDONTWRITEBYTECODE": "1"}
        self.assertEqual(self.subprocess(command, stdout=io.BytesIO(), cwd=alias, env=env).returncode, 0)
        with self.assertRaises(AssertionError):
            self.subprocess(command, stdout=io.BytesIO(), cwd=other, env=env)

    def test_zero_exit_skip_or_empty_suite_never_passes(self):
        outputs = ("Ran 2 tests in 0.001s\n\nOK (skipped=1)\n",
                   "Ran 0 tests in 0.001s\n\nOK\n", "OK\n")
        for output in outputs:
            with self.subTest(output=output), self.assertRaises(ci_unit.CiError):
                ci_unit.check_unittest_result(0, output)
        with self.assertRaises(ci_unit.CiError):
            ci_unit.check_unittest_result(1, "Ran 2 tests in 0.001s\n\nOK\n")

        def skipped(command, **kwargs):
            if "unittest" in command:
                kwargs["stdout"].write(outputs[0].encode())
                return subprocess.CompletedProcess(command, 0)
            return self.subprocess(command, **kwargs)

        result = self.run_fixture(skipped)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["missing_or_failed_checks"], ["unit-tests"])

    def test_generation_failure_and_stale_manifest_force_exit_one(self):
        (self.root / "unlisted.py").write_text("unexpected source", encoding="utf-8")

        def failed(command, **kwargs):
            if any("kraken_adapter.py" in arg for arg in command):
                kwargs["stdout"].write(b"stale generated artifacts\n")
                return subprocess.CompletedProcess(command, 1)
            return self.subprocess(command, **kwargs)

        with patch.object(ci_unit, "ROOT", self.root), \
                patch.object(sys, "argv", ["ci_unit.py", "--output", str(self.output)]), \
                patch.object(ci_unit, "check_source_integrity", return_value={}), \
                patch.object(ci_unit.subprocess, "run", side_effect=failed), \
                redirect_stdout(io.StringIO()):
            self.assertEqual(ci_unit.main(), 1)
        result = ci_unit.load_json(self.output / "report.json")
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["missing_or_failed_checks"], ["generated-current", "source-manifest"])

    def test_output_cannot_overwrite_package_or_existing_artifacts(self):
        for output in (self.root, self.root / "evidence/ci", self.base):
            with self.subTest(path=output), self.assertRaisesRegex(ci_unit.CiError, "outside"):
                ci_unit.prepare_output(self.root, output)
        self.output.mkdir()
        prior = self.output / "report.json"
        prior.write_bytes(b"previous CI evidence")
        with self.assertRaisesRegex(ci_unit.CiError, "new or empty"):
            ci_unit.prepare_output(self.root, self.output)
        self.assertEqual(prior.read_bytes(), b"previous CI evidence")


if __name__ == "__main__":
    unittest.main()
