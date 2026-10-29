"""Semantic rejection must concern the intended false equality and nothing else."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_formal_negatives as checker


def diagnostic(result="carryResult"):
    return ("C:/work/broken-carry.lean:3:43: error: Tactic `decide` proved that the proposition\n"
            f"  {result} = expected\nis false\n")


def census():
    return "\n".join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                     for name in sorted(checker.EXPECTED_DECLARATIONS))


class FormalNegativeClassifierTests(unittest.TestCase):
    def test_exact_intended_propositions_are_rejected(self):
        for result in ("carryResult", "bindingResult"):
            with self.subTest(result=result):
                self.assertTrue(checker.is_semantic_rejection(result, 1, diagnostic(result)))
                self.assertTrue(checker.is_semantic_rejection(result, 1, diagnostic(result).replace("\n", "\r\n")))

    def test_different_proposition_is_not_semantic_evidence(self):
        self.assertFalse(checker.is_semantic_rejection("carryResult", 1, diagnostic("bindingResult")))
        self.assertFalse(checker.is_semantic_rejection("carryResult", 1, diagnostic("unrelatedResult")))
        self.assertFalse(checker.is_semantic_rejection("unrelatedResult", 1, diagnostic("unrelatedResult")))

    def test_unrelated_decide_false_error_is_rejected(self):
        unrelated = "C:/work/broken-carry.lean:3:43: error: cannot decide whether false is inhabited\n"
        self.assertFalse(checker.is_semantic_rejection("carryResult", 1, unrelated))
        imported = "C:/work/broken-carry.lean:1:0: error: object file of module FormalAdditionNegatives does not exist\n"
        self.assertFalse(checker.is_semantic_rejection("carryResult", 1, imported))

    def test_extra_errors_warnings_and_wrong_exit_code_are_rejected(self):
        for extra in ("warning: declaration uses 'sorry'\n", "error: unrelated failure\n", diagnostic()):
            for output in (extra + diagnostic(), diagnostic() + extra):
                with self.subTest(extra=extra, output=output):
                    self.assertFalse(checker.is_semantic_rejection("carryResult", 1, output))
        for code in (0, 2, -1):
            self.assertFalse(checker.is_semantic_rejection("carryResult", code, diagnostic()))

    def test_complete_standard_axiom_census(self):
        valid, actual = checker.check_census(census())
        self.assertTrue(valid)
        self.assertEqual(set(actual), checker.EXPECTED_DECLARATIONS)

    def test_missing_duplicate_unknown_and_unsafe_axioms_fail(self):
        first = next(iter(sorted(checker.EXPECTED_DECLARATIONS)))
        malformed = (
            "\n".join(census().splitlines()[1:]),
            census() + f"\n'{first}' depends on axioms: [propext]",
            census() + "\n'unrelated' does not depend on any axioms",
            census().replace("[propext,", "[correctnessAx,", 1),
            census().replace("[propext,", "[sorryAx,", 1),
            census() + "\nwarning: declaration uses 'sorry'",
            census() + "\nerror: failed target theorem",
        )
        for text in malformed:
            with self.subTest(output=text):
                self.assertFalse(checker.check_census(text)[0])


if __name__ == "__main__":
    unittest.main()
