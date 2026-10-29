"""Check typed results and rejection boundaries of the retained parser patches."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys

from kraken_compat import prepare
from measure import run
from verify import lean_environment

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    tool = args.lean_bin.resolve()
    suffix = ".exe" if os.name == "nt" else ""
    env = os.environ.copy()
    env["PATH"] = str(tool) + os.pathsep + env.get("PATH", "")
    env = lean_environment(tool / ("lake" + suffix), prepare(), env)
    result = run([str(tool / ("lean" + suffix)), "-DautoImplicit=false", "--run", "ParserChecks.lean"],
                 cwd=ROOT / "bridge", env=env, log=ROOT / "evidence/parser-boundaries.log")
    output = Path(result["log"]).read_text(encoding="utf-8", errors="replace")
    result["status"] = "PASS" if result["exit_code"] == 0 and output.strip() == (
        "PASS: 15 exact typed parser results; 24 rejected forms") else "FAIL"
    result["scope"] = "Synthetic parser checks, including range-before-conversion and width boundaries; no arithmetic correctness claim."
    (ROOT / "evidence/parser-boundaries.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2), flush=True)
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
