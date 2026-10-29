"""Tamper checks use copies; retained source/artifacts are never modified."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from integrity import IntegrityError, check_pasta_snapshot, compare_generated, contained


class IntegrityTests(unittest.TestCase):
    def test_upstream_snapshot_and_changed_proof_rejected(self):
        upstream = ROOT / "vendor" / "pasta"
        self.assertEqual(check_pasta_snapshot(upstream)["status"], "PASS")
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp) / "pasta"
            shutil.copytree(upstream, copy, ignore=shutil.ignore_patterns(".lake"))
            spec = copy / "lean/PastaCurves/AArch64/Spec/Add.lean"
            spec.write_bytes(spec.read_bytes() + b"\n-- changed proof\n")
            with self.assertRaisesRegex(IntegrityError, "changed upstream source"):
                check_pasta_snapshot(copy)

    def test_pin_change_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = json.loads((ROOT / "vendor/pasta/UPSTREAM.json").read_text())
            manifest["commit"] = "0" * 40
            (root / "UPSTREAM.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(IntegrityError, "wrong immutable revision"):
                check_pasta_snapshot(root)

    def test_stale_and_extra_generated_files_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            expected = {"input.txt": b"retained bytes\n"}
            (root / "input.txt").write_bytes(expected["input.txt"])
            compare_generated(expected, root)
            (root / "input.txt").write_bytes(b"stale bytes\n")
            with self.assertRaisesRegex(IntegrityError, "stale generated"):
                compare_generated(expected, root)
            (root / "input.txt").write_bytes(expected["input.txt"])
            (root / "unexpected.txt").write_bytes(b"extra")
            with self.assertRaisesRegex(IntegrityError, "file set differs"):
                compare_generated(expected, root)

    def test_manifest_path_escape_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(IntegrityError, "escapes"):
                contained(Path(temp), "../outside")


if __name__ == "__main__":
    unittest.main()
