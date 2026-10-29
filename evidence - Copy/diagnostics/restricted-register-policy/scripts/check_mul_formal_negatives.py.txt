"""Check kernel multiplication counterexamples and exact false-equality rejection."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from check_formal_negatives import ALLOWED_AXIOMS, lean_environment
from measure import run

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
NAMESPACE = "PastaBridge.FormalMulNegatives."
EXPECTED_DECLARATIONS = {NAMESPACE + name for name in (
    "witness_words_bounded", "witness_field_inputs", "witness_input_values",
    "unmodified_models", "expected_values", "broken_carry_value", "broken_binding_value",
    "broken_carry_is_semantically_wrong", "broken_binding_is_semantically_wrong")}
RESULTS = {"broken-carry": ("carryResult", "carryExpected"),
           "wrong-binding": ("bindingResult", "bindingExpected")}


def check_census(output: str) -> tuple[bool, dict[str, list[str]]]:
    found: dict[str, set[str]] = {}
    duplicate = False
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        duplicate |= name in found
        found[name] = {value.strip() for value in axioms.split(",") if value.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        duplicate |= name in found
        found[name] = set()
    valid = (not duplicate and set(found) == EXPECTED_DECLARATIONS and
             all(values <= ALLOWED_AXIOMS for values in found.values()) and
             not any(marker in output for marker in ("sorryAx", "warning:", "error:")))
    return valid, {name: sorted(values) for name, values in found.items()}


def is_semantic_rejection(result: str, expected: str, exit_code: int, output: str) -> bool:
    """Only the intended original proposition's pinned diagnostic is evidence."""
    if (result, expected) not in RESULTS.values() or exit_code != 1:
        return False
    proposition = result + " = " + expected
    pattern = (r"[^\n]+:\d+:\d+: error: Tactic `decide` proved that the proposition\n  " +
               re.escape(proposition) + r"\nis false")
    return re.fullmatch(pattern, output.replace("\r\n", "\n").strip()) is not None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--module-dir", type=Path, action="append", default=[])
    args = parser.parse_args()
    lean_bin = args.lean_bin.resolve()
    lean = lean_bin / ("lean.exe" if os.name == "nt" else "lean")
    evidence = ROOT / "evidence/formal-multiplication-negatives"
    evidence.mkdir(parents=True, exist_ok=True)
    build = WORK / "formal-mul-negative-build"
    sources = WORK / "formal-mul-negative-sources"
    build.mkdir(parents=True, exist_ok=True)
    sources.mkdir(parents=True, exist_ok=True)
    helper = ROOT / "proofs/FormalMulNegatives.lean"
    report: dict = {"status": "RUNNING", "stages": [],
        "scope": "Kernel semantic counterexamples for algorithmic mutations of the actual decoded multiplication program; exact rejection of original false output equalities."}

    def save() -> None:
        (evidence / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    save()
    try:
        env = lean_environment(lean_bin)
        env["LEAN_PATH"] = os.pathsep.join([str(build),
            *(str(path.resolve()) for path in args.module_dir), str(WORK / "bridge-build"),
            str(WORK / "kraken-compat/.lake/build/lib/lean"), env.get("LEAN_PATH", "")])
        positive = run([str(lean), "-DautoImplicit=false", "-o", str(build / "FormalMulNegatives.olean"), str(helper)],
                       cwd=ROOT / "proofs", env=env, log=evidence / "counterexamples.log")
        output = Path(positive["log"]).read_text(encoding="utf-8", errors="replace")
        census_ok, actual_census = check_census(output)
        positive.update({"status": "PASS" if positive["exit_code"] == 0 and census_ok else "FAIL",
                         "axiom_census": actual_census, "strict_axiom_census_passed": census_ok,
                         "source_sha256": hashlib.sha256(helper.read_bytes()).hexdigest()})
        report["stages"].append({"name": "kernel-counterexample-certificates", **positive})
        save()
        if positive["status"] == "PASS":
            for name, (result, expected) in RESULTS.items():
                source = sources / (name + ".lean")
                text = ("import FormalMulNegatives\nopen PastaBridge.FormalMulNegatives\n"
                        f"example : {result} = {expected} := by decide +kernel\n")
                source.write_text(text, encoding="utf-8")
                (evidence / (name + ".lean.txt")).write_text(text, encoding="utf-8")
                item = run([str(lean), "-DautoImplicit=false", str(source)],
                           cwd=ROOT / "proofs", env=env, log=evidence / (name + ".log"))
                output = Path(item["log"]).read_text(encoding="utf-8", errors="replace")
                rejected = is_semantic_rejection(result, expected, item["exit_code"], output)
                item.update({"status": "PASS" if rejected else "FAIL", "expected_failure": True,
                             "intended_false_equality": result + " = " + expected,
                             "semantic_rejection_confirmed": rejected,
                             "source_sha256": hashlib.sha256(text.encode()).hexdigest()})
                report["stages"].append({"name": name, **item})
                save()
        report["status"] = "PASS" if len(report["stages"]) == 3 and all(
            stage["status"] == "PASS" for stage in report["stages"]) else "FAIL"
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        report.update({"status": "BLOCKED", "reason": str(error)})
    save()
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "PASS" else 2 if report["status"] == "BLOCKED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
