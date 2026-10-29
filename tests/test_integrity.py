"""Tamper checks use copies; retained source/artifacts are never modified."""
import json
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from integrity import (IntegrityError, check_kraken_snapshot, check_pasta_snapshot,
                       compare_generated, contained, git_blob_id)
import snapshot_sources


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

    def test_crlf_drift_and_real_source_edits_are_rejected_without_normalization(self):
        for name, relative, check in (
                ("pasta", "lean/PastaCurves/AArch64/Semantics.lean", check_pasta_snapshot),
                ("kraken", "Kraken/AArch64/Semantics.lean", check_kraken_snapshot)):
            with self.subTest(snapshot=name), tempfile.TemporaryDirectory() as temp:
                copy = Path(temp) / name
                shutil.copytree(ROOT / "vendor" / name, copy, ignore=shutil.ignore_patterns(".lake"))
                source = copy / relative
                original = source.read_bytes()
                self.assertIn(b"\n", original)
                self.assertNotIn(b"\r\n", original)
                source.write_bytes(original.replace(b"\n", b"\r\n"))
                with self.assertRaisesRegex(IntegrityError, "changed"):
                    check(copy)
                source.write_bytes(original + b"\ndef snapshot_source_tamper : Nat := 1\n")
                with self.assertRaisesRegex(IntegrityError, "changed"):
                    check(copy)

    def test_git_blob_identity_stays_required_after_sha256_is_refreshed(self):
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp) / "pasta"
            shutil.copytree(ROOT / "vendor/pasta", copy, ignore=shutil.ignore_patterns(".lake"))
            relative = "lean/PastaCurves/AArch64/Semantics.lean"
            source = copy / relative
            source.write_bytes(source.read_bytes() + b"\ndef snapshot_source_tamper : Nat := 1\n")
            manifest_path = copy / "UPSTREAM.json"
            manifest = json.loads(manifest_path.read_bytes())
            manifest["files"][relative] = hashlib.sha256(source.read_bytes()).hexdigest()
            manifest_path.write_bytes(json.dumps(manifest).encode("utf-8"))
            with self.assertRaisesRegex(IntegrityError, "Git blob mismatch"):
                check_pasta_snapshot(copy)
            del manifest["git_blobs"]
            manifest_path.write_bytes(json.dumps(manifest).encode("utf-8"))
            with self.assertRaisesRegex(IntegrityError, "identities are missing or incomplete"):
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


class GitBlobSnapshotTests(unittest.TestCase):
    """Synthetic Git objects include genuine CRLF and non-UTF-8 bytes."""
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="git-blob-snapshot-test-")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.repository = self.base / "repository"
        self.repository.mkdir()
        self.target = self.base / "snapshot"
        self.values = {"lf.txt": b"first\nsecond\n", "crlf.txt": b"first\r\nsecond\r\n",
                       "binary.bin": b"\0\xff\r\nblob 1\n\xfe\r\0"}
        self.environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        # This identity belongs only to an ephemeral Git-object test fixture.
        self.environment.update(GIT_AUTHOR_NAME="Snapshot test fixture",
            GIT_AUTHOR_EMAIL="snapshot-fixture@example.invalid", GIT_COMMITTER_NAME="Snapshot test fixture",
            GIT_COMMITTER_EMAIL="snapshot-fixture@example.invalid", GIT_AUTHOR_DATE="2000-01-01T00:00:00+00:00",
            GIT_COMMITTER_DATE="2000-01-01T00:00:00+00:00")
        self.git(["init"])
        self.git(["config", "core.autocrlf", "true"])
        self.oids = {path: self.git(["hash-object", "-w", "--stdin"], value).strip()
                     for path, value in self.values.items()}
        tree = b"".join(b"100644 blob " + self.oids[path] + b"\t" + path.encode("ascii") + b"\n"
                        for path in sorted(self.values))
        tree_oid = self.git(["mktree"], tree).strip().decode("ascii")
        self.revision = self.git(["commit-tree", tree_oid, "-m", "Exact-byte snapshot fixture"]).strip().decode("ascii")
        self.git(["update-ref", "HEAD", self.revision])
        self.manifest = {"repository": "synthetic fixture only", "revision": self.revision,
                         "files": {path: "0" * 64 for path in self.values}}

    def git(self, arguments, data=None):
        return subprocess.check_output(["git", "-C", str(self.repository), *arguments], input=data,
                                       stderr=subprocess.STDOUT, env=self.environment)

    def rebuild(self):
        return snapshot_sources.regenerate(self.repository, self.target, self.revision,
                                           self.manifest, write=True)

    def test_rebuild_preserves_pinned_crlf_binary_and_lf_bytes(self):
        # An unrelated/filtered worktree is not the snapshot byte source.
        (self.repository / "crlf.txt").write_bytes(b"different worktree bytes\n")
        result = self.rebuild()
        self.assertEqual(result["checked_files"], 3)
        retained = json.loads((self.target / "UPSTREAM.json").read_bytes())
        for relative, expected in self.values.items():
            with self.subTest(path=relative):
                self.assertEqual((self.target / relative).read_bytes(), expected)
                self.assertEqual(retained["git_blobs"][relative], self.oids[relative].decode("ascii"))
                self.assertEqual(git_blob_id(expected), retained["git_blobs"][relative])
                self.assertEqual(hashlib.sha256(expected).hexdigest(), retained["files"][relative])
        snapshot_sources.regenerate(self.repository, self.target, self.revision, retained, write=False)

    def test_check_rejects_drift_without_rewriting_files(self):
        self.rebuild()
        manifest_path = self.target / "UPSTREAM.json"
        manifest_bytes = manifest_path.read_bytes()
        retained = json.loads(manifest_bytes)
        source = self.target / "crlf.txt"
        source.write_bytes(b"first\nsecond\n")
        before = source.read_bytes()
        with self.assertRaisesRegex(ValueError, "differs from pinned Git blobs"):
            snapshot_sources.regenerate(self.repository, self.target, self.revision, retained, write=False)
        self.assertEqual(source.read_bytes(), before)
        self.assertEqual(manifest_path.read_bytes(), manifest_bytes)

    def test_wrong_revision_and_unsafe_selection_fail_before_write(self):
        with self.assertRaisesRegex(ValueError, "not at pinned revision"):
            snapshot_sources.regenerate(self.repository, self.target, "0" * 40, self.manifest, write=True)
        self.assertFalse(self.target.exists())
        unsafe = {**self.manifest, "files": {"../outside": "0" * 64}}
        with self.assertRaisesRegex(ValueError, "unsafe snapshot path"):
            snapshot_sources.regenerate(self.repository, self.target, self.revision, unsafe, write=True)
        self.assertFalse((self.base / "outside").exists())


if __name__ == "__main__":
    unittest.main()
