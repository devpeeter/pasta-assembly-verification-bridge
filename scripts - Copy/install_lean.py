"""Install the checksum-pinned Lean release inside the workspace, without elan.

Uses official release ZIPs so Python's standard library suffices on each host.
The lock file records upstream release SHA-256 digests, not locally made hashes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import stat
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as data:
        for chunk in iter(lambda: data.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def install(directory: Path) -> Path:
    lock = json.loads((ROOT / "lean-release.lock.json").read_text())
    machine = platform.machine().lower()
    if os.name == "nt" and machine in ("amd64", "x86_64"):
        host = "windows"
    elif platform.system() in ("Linux", "Darwin"):
        host = platform.system().lower()
        if machine in ("aarch64", "arm64"):
            host += "_aarch64"
        elif machine not in ("amd64", "x86_64"):
            raise RuntimeError(f"unsupported host: {platform.platform()}")
    else:
        raise RuntimeError(f"unsupported host: {platform.platform()}")
    name = f"lean-{lock['version']}-{host}"
    pin = lock["archives"][name + ".zip"]
    directory = directory.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    archive = directory / (name + ".zip")
    if not archive.is_file() or digest(archive) != pin["sha256"]:
        partial = archive.with_suffix(".zip.part")
        print(f"Downloading {pin['url']} ({pin['bytes']} bytes)", flush=True)
        with urllib.request.urlopen(pin["url"]) as source, partial.open("wb") as dest:
            shutil.copyfileobj(source, dest)
        if partial.stat().st_size != pin["bytes"] or digest(partial) != pin["sha256"]:
            raise RuntimeError(f"official Lean archive checksum/size mismatch: {partial}")
        partial.replace(archive)
    # Re-extract on every invocation so edited tool executables cannot hide behind
    # a previously installed directory. Never execute bytes from an unchecked ZIP.
    print(f"Verified {archive.name}; extracting", flush=True)
    with zipfile.ZipFile(archive) as bundle:
        for member in bundle.infolist():
            path = (directory / member.filename).resolve()
            if not path.is_relative_to(directory) or not member.filename.startswith(name + "/"):
                raise RuntimeError("archive entry escapes the pinned tool directory")
            if stat.S_ISLNK(member.external_attr >> 16):
                raise RuntimeError("unexpected symlink in Lean ZIP")
            bundle.extract(member, directory)
            if os.name != "nt" and not member.is_dir():
                mode = member.external_attr >> 16
                path.chmod((mode & 0o777) or 0o644)
    return directory / name / "bin"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path,
                        default=ROOT.parent.parent / "work/toolchains")
    args = parser.parse_args()
    print(install(args.directory))
