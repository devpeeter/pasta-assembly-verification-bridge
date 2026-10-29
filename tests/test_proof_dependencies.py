"""Proof dependency tamper checks use synthetic repositories under work/ only."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
sys.path.insert(0, str(ROOT / "scripts"))
from check_proof_dependencies import ProofDependencyError, check_proof_dependencies


class ProofDependencyTests(unittest.TestCase):
    def setUp(self):
        WORK.mkdir(exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="dependency-test-", dir=WORK)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.proofs = self.root / "proofs"
        self.package = self.proofs / ".lake/packages/mathlib"
        self.package.mkdir(parents=True)
        self.git("init")
        self.git("remote", "add", "origin", "https://github.com/leanprover-community/mathlib4")
        (self.package / ".gitignore").write_text(".lake/\nIgnored.lean\n", encoding="utf-8")
        (self.package / "Main.lean").write_text("example : True := True.intro\n", encoding="utf-8")
        (self.package / "lakefile.toml").write_text('name = "fixture"\n', encoding="utf-8")
        self.git("add", ".")
        # This clearly synthetic identity belongs only to an ephemeral fixture;
        # it is not attribution for delivered source or a public commit.
        self.git("-c", "user.name=Dependency test fixture", "-c",
                 "user.email=dependency-fixture@example.invalid", "-c", "core.hooksPath=",
                 "-c", "commit.gpgsign=false", "commit", "-m", "Synthetic dependency fixture")
        revision = self.git("rev-parse", "HEAD").strip()
        self.lock = {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{
            "type": "git", "name": "mathlib", "url": "https://github.com/leanprover-community/mathlib4",
            "rev": revision, "subDir": None, "manifestFile": "lake-manifest.json",
            "configFile": "lakefile.toml"}]}
        self.pins = self.root / "pins.json"
        self.pins.write_text(json.dumps({"aeneas": {"mathlib_revision": revision}}), encoding="utf-8")
        self.save_lock()

    def git(self, *arguments):
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        return subprocess.check_output(["git", "-C", str(self.package), *arguments],
                                       env=env, stderr=subprocess.STDOUT, text=True)

    def save_lock(self):
        (self.proofs / "lake-manifest.json").write_text(json.dumps(self.lock), encoding="utf-8")

    def check(self):
        return check_proof_dependencies(self.proofs, self.pins)

    def test_clean_locked_tree_and_ignored_build_cache_accepted_without_index_write(self):
        cache = self.package / ".lake/build/lib/lean/Main.olean"
        cache.parent.mkdir(parents=True)
        cache.write_bytes(b"synthetic cached build output")
        index = self.package / ".git/index"
        before = index.read_bytes()
        result = self.check()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["checked_packages"], 1)
        self.assertEqual(index.read_bytes(), before)

    def test_dirty_tracked_source_rejected_even_if_staged(self):
        source = self.package / "Main.lean"
        source.write_text("changed source\n", encoding="utf-8")
        for staged in (False, True):
            if staged:
                self.git("add", "Main.lean")
            with self.subTest(staged=staged), self.assertRaisesRegex(ProofDependencyError, "changed or untracked"):
                self.check()

    def test_untracked_and_ignored_source_outside_cache_rejected(self):
        for name in ("New.lean", "Ignored.lean"):
            path = self.package / name
            path.write_text("unreviewed source\n", encoding="utf-8")
            with self.subTest(name=name), self.assertRaisesRegex(ProofDependencyError, "changed or untracked"):
                self.check()
            path.unlink()

    def test_assume_unchanged_and_skip_worktree_cannot_hide_source_changes(self):
        for flag, undo in (("--assume-unchanged", "--no-assume-unchanged"),
                           ("--skip-worktree", "--no-skip-worktree")):
            self.git("update-index", flag, "Main.lean")
            with self.subTest(flag=flag), self.assertRaisesRegex(ProofDependencyError, "index flag"):
                self.check()
            self.git("update-index", undo, "Main.lean")

    def test_wrong_head_rejected(self):
        package = self.lock["packages"][0]
        package["rev"] = "0" * 40
        self.pins.write_text(json.dumps({"aeneas": {"mathlib_revision": "0" * 40}}), encoding="utf-8")
        self.save_lock()
        with self.assertRaisesRegex(ProofDependencyError, "wrong dependency revision"):
            self.check()

    def test_mathlib_pin_and_origin_mismatch_rejected(self):
        self.pins.write_text(json.dumps({"aeneas": {"mathlib_revision": "0" * 40}}), encoding="utf-8")
        with self.assertRaisesRegex(ProofDependencyError, "Mathlib lock"):
            self.check()
        revision = self.lock["packages"][0]["rev"]
        self.pins.write_text(json.dumps({"aeneas": {"mathlib_revision": revision}}), encoding="utf-8")
        self.git("remote", "set-url", "origin", "https://github.com/example/replacement")
        with self.assertRaisesRegex(ProofDependencyError, "repository differs"):
            self.check()

    def test_unsafe_names_paths_revisions_and_urls_rejected(self):
        original = copy.deepcopy(self.lock)
        mutations = [("name", "../escape"), ("rev", "main"), ("subDir", "../escape"),
                     ("configFile", "../../evil.lean"), ("url", "file:///elsewhere"),
                     ("url", "https://github.com/a/../escape")]
        for field, value in mutations:
            self.lock = copy.deepcopy(original)
            self.lock["packages"][0][field] = value
            self.save_lock()
            with self.subTest(field=field, value=value), self.assertRaises(ProofDependencyError):
                self.check()
        self.lock = copy.deepcopy(original)
        self.lock["packagesDir"] = "../escape"
        self.save_lock()
        with self.assertRaisesRegex(ProofDependencyError, "packagesDir"):
            self.check()

    def test_duplicates_unlocked_directories_and_missing_package_rejected(self):
        self.lock["packages"].append(copy.deepcopy(self.lock["packages"][0]))
        self.save_lock()
        with self.assertRaisesRegex(ProofDependencyError, "duplicate"):
            self.check()
        self.lock["packages"].pop()
        self.save_lock()
        extra = self.package.parent / "Unlocked"
        extra.mkdir()
        with self.assertRaisesRegex(ProofDependencyError, "unlocked package"):
            self.check()
        extra.rmdir()
        self.git("remote", "set-url", "origin", "https://github.com/leanprover-community/mathlib4")
        self.lock["packages"][0]["name"] = "Missing"
        self.save_lock()
        with self.assertRaises(ProofDependencyError):
            self.check()

    def test_inherited_git_redirection_is_ignored(self):
        with patch.dict(os.environ, {"GIT_DIR": str(self.root / "not-a-git-directory"),
                                     "GIT_WORK_TREE": str(self.root)}):
            self.assertEqual(self.check()["status"], "PASS")


if __name__ == "__main__":
    unittest.main()
