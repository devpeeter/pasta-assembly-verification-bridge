"""Check the proof dependency lock against current local Git source trees.

This command performs no fetch, checkout, build or Git index update. Imported
dependency .olean caches under .lake remain trusted build artifacts, as described
in RESULTS.md; this gate checks their immutable source context, not their binary
source correspondence.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
PATH_PACKAGES = {
    "PastaBridgeArithmetic": "../vendor/pasta/lean",
    "Kraken": "../../../work/kraken-compat",
    "PastaAssemblyBridge": "../bridge",
}
NAME = re.compile(r"[A-Za-z0-9_]+\Z")
REVISION = re.compile(r"[a-f0-9]{40}\Z")


class ProofDependencyError(ValueError):
    pass


def repository_url(value: object) -> str:
    if not isinstance(value, str):
        raise ProofDependencyError("dependency URL must be a string")
    parsed = urlsplit(value)
    parts = parsed.path.strip("/").split("/")
    if (parsed.scheme != "https" or parsed.netloc != "github.com" or
            parsed.query or parsed.fragment or len(parts) != 2 or
            any(not re.fullmatch(r"[A-Za-z0-9_.-]+", part) or part in (".", "..")
                for part in parts)):
        raise ProofDependencyError(f"unsupported dependency repository URL: {value!r}")
    return value.rstrip("/").removesuffix(".git")


def locked_git_packages(proofs: Path, pins: Path) -> list[dict]:
    lock = json.loads((proofs / "lake-manifest.json").read_text(encoding="utf-8"))
    pinned = json.loads(pins.read_text(encoding="utf-8"))
    if lock.get("version") != "1.2.0" or lock.get("packagesDir") != ".lake/packages":
        raise ProofDependencyError("unsupported manifest version or packagesDir")
    packages = lock.get("packages")
    if not isinstance(packages, list):
        raise ProofDependencyError("manifest packages must be a list")
    seen = set()
    result = []
    for package in packages:
        if not isinstance(package, dict):
            raise ProofDependencyError("invalid manifest package")
        name = package.get("name")
        if not isinstance(name, str) or not NAME.fullmatch(name):
            raise ProofDependencyError(f"unsafe dependency name: {name!r}")
        if name.casefold() in seen:
            raise ProofDependencyError(f"duplicate dependency name: {name}")
        seen.add(name.casefold())
        if (package.get("manifestFile") != "lake-manifest.json" or
                package.get("configFile") not in ("lakefile.lean", "lakefile.toml")):
            raise ProofDependencyError(f"unsafe dependency metadata path: {name}")
        if package.get("type") == "path":
            if PATH_PACKAGES.get(name) != package.get("dir"):
                raise ProofDependencyError(f"unsupported path dependency: {name}")
            continue
        if package.get("type") != "git":
            raise ProofDependencyError(f"unsupported dependency type: {name}")
        revision = package.get("rev")
        if not isinstance(revision, str) or not REVISION.fullmatch(revision):
            raise ProofDependencyError(f"non-immutable dependency revision: {name}")
        if package.get("subDir") is not None:
            raise ProofDependencyError(f"dependency subDir is unsupported: {name}")
        repository_url(package.get("url"))
        result.append(package)
    mathlib = [package for package in result if package["name"] == "mathlib"]
    expected_mathlib = pinned.get("aeneas", {}).get("mathlib_revision")
    if (not isinstance(expected_mathlib, str) or not REVISION.fullmatch(expected_mathlib) or
            len(mathlib) != 1 or mathlib[0]["rev"] != expected_mathlib or
            repository_url(mathlib[0]["url"]) != "https://github.com/leanprover-community/mathlib4"):
        raise ProofDependencyError("Mathlib lock does not match the immutable Aeneas-context pin")
    return result


def git(path: Path, *arguments: str) -> bytes:
    # Do not let inherited alternate-index/worktree/config variables redirect the
    # check. Disable fsmonitor hooks and optional index-refresh writes as well.
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_OPTIONAL_LOCKS="0", GIT_NO_REPLACE_OBJECTS="1", GIT_TERMINAL_PROMPT="0")
    command = ["git", "-c", "core.fsmonitor=false", "-c", "core.untrackedCache=false",
               "-C", str(path), *arguments]
    result = subprocess.run(command, env=env, capture_output=True)
    if result.returncode:
        error = result.stderr.decode("utf-8", errors="replace").strip()
        raise ProofDependencyError(f"Git source check failed for {path.name}: {error}")
    return result.stdout


def cache_output(name: str, relative: str) -> bool:
    return (relative == ".lake" or relative.startswith(".lake/") or
            (name == "proofwidgets" and relative == "widget/package-lock.json.hash"))


def check_proof_dependencies(proofs: Path, pins: Path) -> dict:
    proofs = proofs.resolve()
    packages = locked_git_packages(proofs, pins)
    package_root = (proofs / ".lake/packages").resolve()
    if not package_root.is_relative_to(proofs) or not package_root.is_dir():
        raise ProofDependencyError("missing or escaping proof package directory")
    expected_names = {package["name"] for package in packages}
    extras = {path.name for path in package_root.iterdir() if path.is_dir() or path.is_symlink()} - expected_names
    if extras:
        raise ProofDependencyError(f"unlocked package directories: {sorted(extras)}")
    checked = []
    for package in packages:
        name = package["name"]
        path = (package_root / name).resolve()
        if not path.is_relative_to(package_root) or not path.is_dir():
            raise ProofDependencyError(f"missing or escaping dependency path: {name}")
        top = Path(os.fsdecode(git(path, "rev-parse", "--show-toplevel")).strip()).resolve()
        if top != path:
            raise ProofDependencyError(f"dependency is not its own Git worktree: {name}")
        head = git(path, "rev-parse", "HEAD").decode("ascii").strip()
        if head != package["rev"]:
            raise ProofDependencyError(f"wrong dependency revision: {name}: {head}")
        origin = os.fsdecode(git(path, "config", "--get", "remote.origin.url")).strip()
        if repository_url(origin) != repository_url(package["url"]):
            raise ProofDependencyError(f"dependency repository differs from lock: {name}")
        for entry in git(path, "ls-files", "-v", "-z").split(b"\0"):
            if entry and (chr(entry[0]).islower() or entry[:1] == b"S"):
                raise ProofDependencyError(f"assume-unchanged/skip-worktree index flag: {name}: {os.fsdecode(entry[2:])}")
        ignored = []
        status = git(path, "status", "--porcelain=v1", "--untracked-files=all", "--ignored=matching", "-z")
        for entry in status.split(b"\0"):
            if not entry:
                continue
            code, relative = entry[:2], os.fsdecode(entry[3:]).replace("\\", "/")
            if code in (b"??", b"!!") and cache_output(name, relative.rstrip("/")):
                ignored.append(relative)
                continue
            raise ProofDependencyError(f"changed or untracked dependency source: {name}: {os.fsdecode(entry)}")
        checked.append({"name": name, "revision": head, "repository": package["url"],
                        "allowed_build_outputs": ignored})
    return {"status": "PASS", "checked_packages": len(checked), "packages": checked,
            "scope": "current locked Git sources; .lake dependency build/cache provenance remains trusted"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proofs", type=Path, default=ROOT / "proofs")
    parser.add_argument("--pins", type=Path, default=ROOT / "pins.json")
    arguments = parser.parse_args()
    try:
        print(json.dumps(check_proof_dependencies(arguments.proofs, arguments.pins), indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"proof dependency check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
