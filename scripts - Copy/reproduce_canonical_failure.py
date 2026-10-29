"""Re-run a saved proof diagnostic (never part of target verification)."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from measure import run

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--source", type=Path,
                        default=ROOT / "evidence/diagnostics/AdditionCanonical.failed.lean.txt")
    args = parser.parse_args()
    tool_bin = args.lean_bin.resolve()
    suffix = ".exe" if os.name == "nt" else ""
    base = os.environ.copy()
    base["PATH"] = str(tool_bin) + os.pathsep + base.get("PATH", "")
    query = ("import os,json;print(json.dumps({k:os.environ.get(k,'') "
             "for k in ['LEAN_PATH','LEAN_SRC_PATH','PATH']}))")
    env = base.copy()
    env.update(json.loads(subprocess.check_output(
        [str(tool_bin / ("lake" + suffix)), "env", sys.executable, "-c", query],
        cwd=ROOT / "proofs", env=base, text=True)))
    project_work = ROOT.parent.parent / "work"
    extra = [project_work / "bridge-build", project_work / "kraken-compat/.lake/build/lib/lean"]
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in extra) + os.pathsep + env.get("LEAN_PATH", "")
    source = args.source.resolve()
    if (not source.is_relative_to((ROOT / "evidence/diagnostics").resolve()) or
            not source.name.endswith(".lean.txt")):
        raise ValueError("diagnostic source must be a retained evidence/diagnostics/*.lean.txt file")
    scratch = project_work / "proof-diagnostic"
    scratch.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, scratch / "Diagnostic.lean")
    label = "reproduced-" + source.name.removesuffix(".lean.txt")
    result = run([str(tool_bin / ("lean" + suffix)), "Diagnostic.lean"],
                 cwd=scratch, env=env, log=ROOT / "evidence/diagnostics" / (label + ".log"))
    (ROOT / "evidence/diagnostics" / (label + ".json")).write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return result["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
