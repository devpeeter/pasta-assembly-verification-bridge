import sys
from pathlib import Path
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from extract import digest, validate_source_provenance


class ExtractionProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.source = Path(self.directory.name) / "aarch64.rs"
        self.lock = Path(self.directory.name) / "Cargo.lock"
        self.source.write_bytes(b"source\n")
        self.lock.write_bytes(b"locked dependencies\n")
        self.provenance = {"source_worktree_sha256": digest(self.source),
                           "source_cargo_lock_sha256": digest(self.lock)}

    def test_retained_exact_bytes_accepted(self):
        validate_source_provenance(self.provenance, self.source, self.lock)

    def test_changed_line_endings_are_stale_provenance(self):
        self.source.write_bytes(b"source\r\n")
        with self.assertRaisesRegex(ValueError, "source_worktree_sha256"):
            validate_source_provenance(self.provenance, self.source, self.lock)

    def test_changed_lock_or_missing_identity_rejected(self):
        self.lock.write_bytes(b"different dependencies\n")
        with self.assertRaisesRegex(ValueError, "source_cargo_lock_sha256"):
            validate_source_provenance(self.provenance, self.source, self.lock)
        with self.assertRaisesRegex(ValueError, "source_worktree_sha256"):
            validate_source_provenance({}, self.source, self.lock)
