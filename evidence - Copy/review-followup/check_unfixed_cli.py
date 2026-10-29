"""Confirm the focused regression rejects the retained unfixed CLI source.

The expected failures occur inside temporary fixtures. This diagnostic does not
run Lean or replace any verification report.
"""
import importlib.util
import io
import json
from pathlib import Path
import types
import unittest

ROOT = Path(__file__).resolve().parents[2]
source_file = Path(__file__).with_name("unfixed-verify.py.txt")


def main():
    spec = importlib.util.spec_from_file_location("cli_unfixed_regression", ROOT / "tests/test_cli_paths.py")
    tests = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tests)
    source = source_file.read_text(encoding="utf-8")
    if "args.lean_bin = args.lean_bin.resolve()" in source:
        raise ValueError("expected the retained unfixed verifier")
    baseline = types.ModuleType("retained_unfixed_verify")
    baseline.__file__ = str(source_file)
    exec(compile(source, str(source_file), "exec"), baseline.__dict__)
    tests.verify = baseline
    suite = unittest.TestSuite([
        tests.CliPathTests("test_verifier_relative_tool_directory_survives_nested_cwd_changes")])
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    print(stream.getvalue())
    expected = len(result.failures) == 2 and not result.errors
    print(json.dumps({"status": "PASS" if expected else "FAIL",
        "scope": "Regression sensitivity, not a target verification result",
        "expected_failing_caller_directories": 2,
        "observed_failures": len(result.failures), "unexpected_errors": len(result.errors)}))
    return 0 if expected else 1


if __name__ == "__main__":
    raise SystemExit(main())
