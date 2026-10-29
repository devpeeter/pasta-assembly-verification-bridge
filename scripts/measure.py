"""Run a check and retain its log, wall time, exit status and OS peak RSS.

Peak memory is for the direct child. Run Lean directly (not through Lake) when
reporting proof memory. On Windows this is PeakWorkingSetSize; on Unix it is
wait4.ru_maxrss. Neither number is a sum of concurrent descendants.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import time


def run(command: list[str], *, cwd: Path, log: Path,
        env: dict[str, str] | None = None) -> dict:
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    peak = None
    metric = None
    with log.open("wb") as output:
        child = subprocess.Popen(command, cwd=cwd, env=env, stdout=output,
                                 stderr=subprocess.STDOUT)
        if os.name == "nt":
            import ctypes
            from ctypes import wintypes

            class Counters(ctypes.Structure):
                _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD)] + [
                    (name, ctypes.c_size_t) for name in (
                        "PeakWorkingSetSize", "WorkingSetSize", "QuotaPeakPagedPoolUsage",
                        "QuotaPagedPoolUsage", "QuotaPeakNonPagedPoolUsage",
                        "QuotaNonPagedPoolUsage", "PagefileUsage", "PeakPagefileUsage")]

            get_memory = ctypes.WinDLL("psapi").GetProcessMemoryInfo
            get_memory.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
            get_memory.restype = wintypes.BOOL
            while True:
                counters = Counters()
                counters.cb = ctypes.sizeof(counters)
                if get_memory(wintypes.HANDLE(int(child._handle)), ctypes.byref(counters), counters.cb):
                    peak = max(peak or 0, counters.PeakWorkingSetSize)
                if child.poll() is not None:
                    break
                time.sleep(0.02)
            code = child.returncode
            metric = "Windows PeakWorkingSetSize (direct child), bytes"
        elif hasattr(os, "wait4"):
            _, status, usage = os.wait4(child.pid, 0)
            code = os.waitstatus_to_exitcode(status)
            child.returncode = code
            peak = int(usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024))
            metric = "wait4 ru_maxrss (direct child), bytes"
        else:
            code = child.wait()
    return {"command": command, "cwd": str(cwd), "exit_code": code,
            "wall_seconds": round(time.perf_counter() - started, 6),
            "peak_rss_bytes": peak, "memory_metric": metric, "log": str(log)}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--json", type=Path, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    result = run(command, cwd=args.cwd.resolve(), log=args.log.resolve())
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    raise SystemExit(result["exit_code"])
