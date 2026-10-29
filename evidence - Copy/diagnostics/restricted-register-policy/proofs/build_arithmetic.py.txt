"""Compile the retained Pasta arithmetic proof closure with one Lean worker.

Dependency `.olean` caches must already be fetched by bootstrap.py. Every retained
Pasta source and the final arithmetic audit is rechecked from source, serially.
The JSON/log evidence reports direct Lean child memory, not Lake parent memory.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "scripts"))
from measure import run


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    lean_bin = args.lean_bin.resolve()
    suffix = ".exe" if os.name == "nt" else ""
    env = os.environ.copy()
    env["PATH"] = str(lean_bin) + os.pathsep + env.get("PATH", "")
    query = ("import os,json;print(json.dumps({k:os.environ.get(k,'') "
             "for k in ['LEAN_PATH','LEAN_SRC_PATH','PATH']}))")
    env.update(json.loads(subprocess.check_output([str(lean_bin / ("lake" + suffix)), "env",
                    sys.executable, "-c", query], cwd=ROOT, env=env, text=True)))
    pasta = ROOT.parent / "vendor/pasta/lean"
    order = []
    visited = set()
    def visit(module):
        if module in visited:
            return
        visited.add(module)
        file = pasta / (module.replace(".", "/") + ".lean")
        for line in file.read_text(encoding="utf-8").splitlines():
            if line.startswith("import PastaCurves."):
                visit(line[7:].strip())
        order.append(module)
    for module in ["PastaCurves.Fields", "PastaCurves.AArch64.Spec.Add",
                   "PastaCurves.AArch64.Spec.Mul"]:
        visit(module)
    evidence = ROOT.parent / "evidence/arithmetic-modules"
    evidence.mkdir(parents=True, exist_ok=True)
    results = []
    started = time.perf_counter()
    for module in order + ["ArithmeticAudit"]:
        source_root = ROOT if module == "ArithmeticAudit" else pasta
        rel = Path(module.replace(".", "/"))
        output = source_root / ".lake/build/lib/lean" / rel.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean_bin / ("lean" + suffix)), "-DautoImplicit=false",
                   str(rel.with_suffix(".lean")), "-o", str(output)]
        print("Checking " + module, flush=True)
        item = run(command, cwd=source_root, env=env,
                   log=evidence / (module + ".log"))
        item["module"] = module
        results.append(item)
        record = {"status": ("FAIL" if any(x["exit_code"] != 0 for x in results) else
                             "PASS" if len(results) == len(order) + 1 else "RUNNING"),
                  "completed_modules": len(results), "expected_modules": len(order) + 1,
                  "wall_seconds": round(time.perf_counter() - started, 6),
                  "peak_rss_bytes": max((x["peak_rss_bytes"] or 0) for x in results),
                  "memory_metric": "maximum direct Lean child memory peak across serial modules; see each module memory_metric; imported dependencies cached",
                  "modules": results}
        (evidence.parent / "arithmetic-serial-build.json").write_text(
            json.dumps(record, indent=2) + "\n", encoding="utf-8")
        if item["exit_code"] != 0:
            print(Path(item["log"]).read_text(encoding="utf-8", errors="replace"))
            return item["exit_code"]
    print("PASS: serial arithmetic proof closure", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
