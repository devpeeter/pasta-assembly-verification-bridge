"""Checks that executable vectors exercise, rather than exclude, generic X19."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import runtime_checks as runtime


class RuntimeRegisterPolicyTests(unittest.TestCase):
    def test_x19_is_protected_exactly_when_outside_written_allocation(self):
        initial = {"x0": 3, "x19": 7, "x29": 11, "sp": 13}
        actual = {"regs": dict(initial), "memory_preserved": True, "sp_preserved": True}
        actual["regs"]["x19"] = 17
        self.assertTrue(runtime.frames_preserved(actual, initial, {"x19"}))
        self.assertFalse(runtime.frames_preserved(actual, initial, {"x0"}))
        actual["regs"]["x29"] = 19
        self.assertFalse(runtime.frames_preserved(actual, initial, {"x19"}))
        actual["regs"]["x29"] = initial["x29"]
        actual["memory_preserved"] = False
        self.assertFalse(runtime.frames_preserved(actual, initial, {"x19"}))

    def test_coverage_requires_both_fields_and_every_incoming_flag_pattern(self):
        def input_operand(index):
            return {"In": {"reg": {"Class": "reg"}, "value": index}}
        block = {"operands": [input_operand(0), input_operand(1),
                              {"Out": {"reg": {"Class": "reg"}, "late": False, "place": None}}]}
        rows = []
        for field in ("pallasBase", "vestaBase"):
            for bits in range(16):
                flags = dict(zip(("n", "z", "c", "v"),
                                 [bool(bits & (1 << bit)) for bit in range(4)]))
                for binding in ({0: "x0", 1: "x1", 2: "x19"},
                                {0: "x19", 1: "x19", 2: "x2"}):
                    rows.append((None, {"field": field, "flags": flags, "binding": binding}))
        coverage = runtime.register_coverage(block, rows)
        self.assertEqual(coverage["x19_written"]["positive_cases"], 32)
        self.assertEqual(coverage["x19_shared_readonly"]["positive_cases"], 32)
        for incomplete in (rows[:32], rows[2:], rows[::2]):
            with self.subTest(count=len(incomplete)):
                with self.assertRaisesRegex(AssertionError, "register coverage"):
                    runtime.register_coverage(block, incomplete)


if __name__ == "__main__":
    unittest.main()
