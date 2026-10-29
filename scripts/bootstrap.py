#!/usr/bin/env python3
"""Fetch immutable extraction sources and build the real Charon rustc driver.

No instruction templates are reconstructed or copied by this script.
Requires Git, Python 3.11+, rustup, and a native Rust linker.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WORK = ROOT.parent.parent / "work"


def run(args: list[str], cwd: Path | None = None) -> None:
    print("+", subprocess.list2cmdline(args), flush=True)
    log_path = ROOT / "logs" / "bootstrap.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("ab") as log:
        log.write(("+ " + subprocess.list2cmdline(args) + "\n").encode())
        log.flush()
        proc = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert proc.stdout is not None
        with proc.stdout:
            for line in iter(proc.stdout.readline, b""):
                log.write(line)
                log.flush()
                sys.stdout.buffer.write(line)
                sys.stdout.buffer.flush()
        status = proc.wait()
        if status:
            raise subprocess.CalledProcessError(status, args)


def output(args: list[str], cwd: Path) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def checkout(work: Path, name: str, pin: dict) -> Path:
    path = work / name
    if not path.exists():
        run(["git", "clone", "--config", "core.autocrlf=false", "--config", "core.eol=lf", "--no-checkout",
             pin["repository"], str(path)])
        run(["git", "checkout", "--detach", pin["revision"]], cwd=path)
    actual = output(["git", "rev-parse", "HEAD"], path)
    if actual != pin["revision"]:
        raise RuntimeError(f"{path} is at {actual}, expected {pin['revision']}; restore the pinned checkout in the fixed work directory")
    dirty = output(["git", "status", "--porcelain", "--untracked-files=no"], path)
    if dirty:
        raise RuntimeError(f"refusing a modified checkout: {path}\n{dirty}")
    return path


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
        epilog=f"Sources and build records use the fixed workspace directory: {DEFAULT_WORK}")
    ap.add_argument("--sources-only", action="store_true")
    args = ap.parse_args()
    work = DEFAULT_WORK.resolve()
    work.mkdir(parents=True, exist_ok=True)
    pins = json.loads((ROOT / "pins.json").read_text())
    checkout(work, "pasta_curves", pins["pasta"])
    charon = checkout(work, "charon", pins["extraction"])
    checkout(work, "aeneas", pins["aeneas"])
    checkout(work, "kraken", pins["kraken"])
    from kraken_compat import prepare
    prepare()
    if args.sources_only:
        return
    toolchain = pins["extraction"]["rust_toolchain"]
    run(["rustup", "toolchain", "install", toolchain, "--profile", "minimal",
         "--no-self-update", "--component", "rustc-dev", "--component", "llvm-tools",
         "--component", "rust-src", "--target", pins["extraction"]["target"]])
    rustv = output(["rustup", "run", toolchain, "rustc", "-Vv"], charon)
    if f"commit-hash: {pins['extraction']['rust_commit']}" not in rustv:
        raise RuntimeError("installed Rust compiler does not match pins.json")
    run(["cargo", f"+{toolchain}", "build", "--locked", "--release", "--no-default-features",
         "--features", "rustc", "--bin", "charon", "--bin", "charon-driver"], charon / "charon")
    suffix = ".exe" if os.name == "nt" else ""
    binary_dir = charon / "charon" / "target" / "release"
    record = {
        "charon_revision": pins["extraction"]["revision"],
        "rustc": rustv,
        "binaries": {name: hashlib.sha256((binary_dir / (name + suffix)).read_bytes()).hexdigest()
                     for name in ("charon", "charon-driver")},
        "build_command": ["cargo", f"+{toolchain}", "build", "--locked", "--release",
                          "--no-default-features", "--features", "rustc", "--bin", "charon", "--bin", "charon-driver"],
    }
    (work / "charon-build-record.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Charon: {binary_dir / ('charon' + suffix)}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"bootstrap failed: {exc}", file=sys.stderr)
        sys.exit(1)
