import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from axiom_audit import audit_log, require_declarations


class AxiomAuditTests(unittest.TestCase):
    def test_standard_and_empty_censuses(self):
        self.assertEqual(audit_log("'a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
                                  "'b' does not depend on any axioms"),
                         {"a": ["propext", "Classical.choice", "Quot.sound"], "b": []})

    def test_correctness_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, "nonstandard"):
            audit_log("'target' depends on axioms: [propext, assumedCorrespondence]")

    def test_sorry_rejected(self):
        with self.assertRaisesRegex(ValueError, "sorryAx"):
            audit_log("'target' depends on axioms: [sorryAx]")

    def test_native_proof_trust_rejected(self):
        with self.assertRaisesRegex(ValueError, "nonstandard"):
            audit_log("'target' depends on axioms: [Lean.trustCompiler]")

    def test_missing_or_truncated_target_census_rejected(self):
        for log in ("", "'helper' does not depend on any axioms",
                    "'target' depends on axioms: [propext"):
            with self.subTest(log=log), self.assertRaisesRegex(ValueError, "missing"):
                require_declarations(log, {"target"})

    def test_requested_target_census_checked(self):
        self.assertEqual(require_declarations(
            "'target' depends on axioms: [propext, Quot.sound]", {"target"}),
            {"target": ["propext", "Quot.sound"]})
