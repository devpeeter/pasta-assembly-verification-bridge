"""Reproduce the selected Kraken pin's multiplication parsing blocker.

This is a parser compatibility diagnostic with zero execution cases. It does not
start multiplication verification or substitute instructions. Exit 2 means the
known immediate-shift blocker; 1 means an unexpected failure; 0 means parsing
succeeded and the recorded blocker needs review.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys

from measure import run
from verify import lean_environment
from kraken_compat import prepare

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    lean_bin = args.lean_bin.resolve()
    suffix = ".exe" if os.name == "nt" else ""
    env = os.environ.copy()
    env["PATH"] = str(lean_bin) + os.pathsep + env.get("PATH", "")
    env = lean_environment(lean_bin / ("lake" + suffix), prepare(), env)
    cases = WORK / "multiplication-parser-cases.json"
    cases.parent.mkdir(parents=True, exist_ok=True)
    cases.write_text("[]\n", encoding="utf-8")
    evidence = ROOT / "evidence"
    command = [str(lean_bin / ("lean" + suffix)), "--run", "KrakenRun.lean",
               "../generated/mul.S", str(cases)]
    item = run(command, cwd=ROOT / "bridge", env=env,
               log=evidence / "multiplication-parser.log")
    log = (evidence / "multiplication-parser.log").read_text(encoding="utf-8", errors="replace")
    lines = (ROOT / "generated/mul.S").read_text(encoding="utf-8").splitlines()
    if item["exit_code"] == 0:
        item.update(status="PASS", scope="parser only; no multiplication execution or proof")
        code = 0
    elif ("line 15: condition not satisfied" in log and
          len(lines) >= 15 and re.fullmatch(r"lsl x\d+, x\d+, #\d+", lines[14])):
        item.update(status="BLOCKED", scope="parser compatibility diagnostic only",
                    reason="Pinned Kraken parser rejects extracted immediate LSL at line 15",
                    extracted_line=lines[14])
        code = 2
    else:
        item.update(status="FAIL", reason="Unexpected multiplication parser diagnostic")
        code = 1
    (evidence / "multiplication-parser.json").write_text(json.dumps(item, indent=2) + "\n", encoding="utf-8")
    print(f"{item['status']}: {item.get('reason', item.get('scope'))}")
    return code


if __name__ == "__main__":
    sys.exit(main())
