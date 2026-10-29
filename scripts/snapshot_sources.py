"""Check or rebuild retained snapshots from exact immutable Git blob bytes.

Only the existing manifest-selected paths are retained. Source bytes are read
with binary Git plumbing and written with write_bytes; working-tree filters,
encoding conversion and newline conversion are never used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

from integrity import KRAKEN_COMMIT, PASTA_COMMIT, git_blob_id

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
BYTE_SOURCE = "git cat-file blob at the immutable revision; no text decoding or newline conversion"


def git(repository: Path, arguments: list[str], data: bytes | None = None) -> bytes:
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_NO_REPLACE_OBJECTS="1", GIT_OPTIONAL_LOCKS="0", GIT_TERMINAL_PROMPT="0")
    result = subprocess.run(["git", "-c", "core.fsmonitor=false", "-C", str(repository), *arguments],
                            input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    if result.returncode:
        raise ValueError("Git blob read failed: " + result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout


def retained_paths(manifest: dict) -> list[str]:
    files = manifest.get("files")
    if not isinstance(files, dict) or not files:
        raise ValueError("source snapshot must select a nonempty file set")
    for relative in files:
        path = PurePosixPath(relative)
        if (not relative or relative == "UPSTREAM.json" or path.is_absolute() or "\\" in relative or
                ":" in relative or any(part in ("", ".", "..") for part in relative.split("/"))):
            raise ValueError(f"unsafe snapshot path: {relative}")
    return sorted(files)


def pinned_blobs(repository: Path, revision: str, paths: list[str]) -> dict[str, tuple[str, bytes]]:
    """Read one pinned tree and batch its blobs without decoding source bytes."""
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("snapshot revision must be an immutable SHA-1 commit")
    if git(repository, ["rev-parse", "HEAD"]).strip() != revision.encode("ascii"):
        raise ValueError(f"source checkout is not at pinned revision {revision}")
    requested = {path.encode("utf-8"): path for path in paths}
    entries = {}
    for record in git(repository, ["ls-tree", "-r", "-z", revision]).split(b"\0"):
        if not record:
            continue
        metadata, name = record.split(b"\t", 1)
        if name not in requested:
            continue
        mode, kind, oid = metadata.split()
        if kind != b"blob" or mode not in (b"100644", b"100755"):
            raise ValueError(f"retained source is not a regular Git blob: {requested[name]}")
        entries[requested[name]] = oid
    if set(entries) != set(paths):
        raise ValueError(f"snapshot paths missing from pinned Git tree: {sorted(set(paths) - set(entries))}")
    batch = git(repository, ["cat-file", "--batch"], b"\n".join(entries[path] for path in paths) + b"\n")
    position = 0
    result = {}
    for path in paths:
        newline = batch.index(b"\n", position)
        oid, kind, length = batch[position:newline].split()
        size = int(length)
        position = newline + 1
        value = batch[position:position + size]
        position += size
        if (oid != entries[path] or kind != b"blob" or len(value) != size or
                batch[position:position + 1] != b"\n" or git_blob_id(value).encode("ascii") != oid):
            raise ValueError(f"invalid binary Git blob response: {path}")
        position += 1
        result[path] = (oid.decode("ascii"), value)
    if position != len(batch):
        raise ValueError("unexpected trailing Git blob output")
    return result


def regenerate(repository: Path, target: Path, revision: str, manifest: dict, *, write: bool) -> dict:
    paths = retained_paths(manifest)
    blobs = pinned_blobs(repository.resolve(), revision, paths)
    expected = {**manifest,
                "files": {path: hashlib.sha256(blobs[path][1]).hexdigest() for path in paths},
                "git_blobs": {path: blobs[path][0] for path in paths}, "byte_source": BYTE_SOURCE}
    mismatches = []
    for relative in paths:
        path = target / relative
        if not path.resolve().is_relative_to(target.resolve()):
            raise ValueError(f"snapshot destination escapes target: {relative}")
        if any(parent.is_symlink() for parent in (path, *path.parents) if parent.is_relative_to(target)):
            raise ValueError(f"snapshot destination is a symbolic link: {relative}")
        data = blobs[relative][1]
        if not path.is_file() or path.read_bytes() != data:
            mismatches.append(relative)
        if write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    manifest_path = target / "UPSTREAM.json"
    if write:
        manifest_path.write_bytes((json.dumps(expected, indent=2) + "\n").encode("utf-8"))
    elif mismatches or expected != manifest:
        raise ValueError(f"snapshot differs from pinned Git blobs: files={mismatches}; "
                         f"manifest_current={expected == manifest}")
    return {"status": "PASS", "revision": revision, "source": str(repository.resolve()),
            "snapshot": str(target.resolve()), "checked_files": len(paths),
            "replaced_files": mismatches if write else [], "mode": "rebuilt" if write else "checked",
            "byte_source": BYTE_SOURCE}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    operation = parser.add_mutually_exclusive_group(required=True)
    operation.add_argument("--check", action="store_true", help="reject stale bytes or blob metadata")
    operation.add_argument("--write", action="store_true", help="explicitly regenerate snapshots from pinned Git blobs")
    parser.add_argument("--pasta-source", type=Path, default=WORK / "pasta_curves")
    parser.add_argument("--kraken-source", type=Path, default=WORK / "kraken")
    args = parser.parse_args()
    pins = json.loads((ROOT / "pins.json").read_text(encoding="utf-8"))
    specifications = [("pasta", args.pasta_source, PASTA_COMMIT, "commit", "https://github.com/zcash/pasta_curves"),
                      ("kraken", args.kraken_source, KRAKEN_COMMIT, "revision", "https://github.com/AeneasVerif/kraken")]
    results = []
    for name, repository, revision, key, url in specifications:
        target = ROOT / "vendor" / name
        manifest = json.loads((target / "UPSTREAM.json").read_text(encoding="utf-8"))
        if (manifest.get(key) != revision or manifest.get("repository") != url or
                pins[name]["revision"] != revision or pins[name]["repository"].removesuffix(".git") != url):
            raise ValueError(f"{name} snapshot/source pins are inconsistent")
        results.append(regenerate(repository, target, revision, manifest, write=args.write))
    print(json.dumps({"status": "PASS", "snapshots": results}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"snapshot check failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
