"""MUL negative classification rejects unrelated failures and extra diagnostics."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_mul_formal_negatives as checker


def diagnostic(result, expected):
    return ("C:/work/mutant.lean:3:43: error: Tactic `decide` proved that the proposition\n"
            f"  {result} = {expected}\nis false\n")


class MulFormalNegativeClassifierTests(unittest.TestCase):
    def test_exact_both_original_equalities(self):
        for result, expected in checker.RESULTS.values():
            self.assertTrue(checker.is_semantic_rejection(result, expected, 1, diagnostic(result, expected)))

    def test_wrong_propositions_exit_codes_and_other_errors(self):
        valid = diagnostic("carryResult", "carryExpected")
        for result, expected in (("carryResult", "bindingExpected"), ("other", "carryExpected")):
            self.assertFalse(checker.is_semantic_rejection(result, expected, 1, diagnostic(result, expected)))
        for text in (diagnostic("bindingResult", "bindingExpected"), "error: decide false import failure",
                     valid + "warning: declaration uses sorry", "error: unrelated\n" + valid,
                     valid + valid):
            self.assertFalse(checker.is_semantic_rejection("carryResult", "carryExpected", 1, text))
        for code in (0, 2, -1):
            self.assertFalse(checker.is_semantic_rejection("carryResult", "carryExpected", code, valid))

    def test_census_requires_exact_nine_declarations_and_standard_axioms(self):
        valid = "\n".join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                          for name in sorted(checker.EXPECTED_DECLARATIONS))
        self.assertTrue(checker.check_census(valid)[0])
        for text in ("\n".join(valid.splitlines()[1:]), valid + "\n" + valid.splitlines()[0],
                     valid + "\n'other' does not depend on any axioms",
                     valid.replace("[propext,", "[correctnessAx,", 1),
                     valid + "\nwarning: unsafe proof", valid + "\nerror: failed theorem"):
            self.assertFalse(checker.check_census(text)[0])


if __name__ == "__main__":
    unittest.main()
