#!/usr/bin/env python3
"""Extract Pasta's complete add/mul asm blocks with the pinned Charon driver.

The retained LLBC is the authority. The envelope copies structured JSON subtrees,
and its JSON pointers and SHA-256 link each subtree back to that LLBC. No Rust
source parser or handwritten instruction list is used here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WORK = ROOT.parent.parent / "work"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def checked_output(args: list[str], cwd: Path) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def assert_checkout(path: Path, revision: str) -> None:
    actual = checked_output(["git", "rev-parse", "HEAD"], path)
    if actual != revision:
        raise RuntimeError(f"{path}: expected {revision}, found {actual}")
    status = checked_output(["git", "status", "--porcelain", "--untracked-files=no"], path)
    if status:
        raise RuntimeError(f"modified pinned checkout {path}:\n{status}")


def reject_external_cargo_config(source: Path) -> None:
    # Cargo searches all ancestors, even outside a Git checkout. Those inputs
    # are not covered by the pinned source revision and can replace rustc.
    for directory in [source, *source.parents]:
        for name in ("config", "config.toml"):
            config = directory / ".cargo" / name
            if config.exists():
                raise RuntimeError(f"unreviewed Cargo configuration would influence extraction: {config}")
    cargo_home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
    for name in ("config", "config.toml"):
        if (cargo_home / name).exists():
            raise RuntimeError(f"global Cargo configuration would influence extraction: {cargo_home / name}")


def validate_source_provenance(provenance: dict, source: Path, lock: Path) -> None:
    for field, path in (("source_worktree_sha256", source), ("source_cargo_lock_sha256", lock)):
        if provenance.get(field) != digest(path):
            raise ValueError(f"current {path.name} bytes differ from retained {field}; regenerate explicitly")


def json_pointer(value: object, pointer: str) -> object:
    for piece in pointer.split("/")[1:]:
        key = piece.replace("~1", "/").replace("~0", "~")
        value = value[int(key)] if isinstance(value, list) else value[key]
    return value


def walk_asm(value: object, path: str = ""):
    if isinstance(value, dict):
        for key, child in value.items():
            child_path = path + "/" + key.replace("~", "~0").replace("/", "~1")
            if key == "InlineAsm":
                if not isinstance(child, dict) or "asm" not in child:
                    raise ValueError("unsupported Charon InlineAsm JSON structure")
                yield child_path + "/asm", child["asm"]
            yield from walk_asm(child, child_path)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from walk_asm(child, path + "/" + str(index))


def name_of(fun: dict) -> str:
    pieces = fun["item_meta"]["name"]
    names = []
    for piece in pieces:
        if not isinstance(piece, dict) or set(piece) != {"Ident"}:
            raise ValueError("target name contains an unsupported Charon path element")
        ident, disambiguator = piece["Ident"]
        if disambiguator != 0:
            raise ValueError("target name has a nonzero disambiguator")
        names.append(ident)
    return "::".join(names)


def selected_routines(raw: dict) -> dict:
    if raw.get("has_errors") is not False:
        raise ValueError("Charon reported errors; partial LLBC is rejected")
    expected = {"pasta_curves::asm::aarch64::" + name: name for name in ("add", "mul")}
    routines = {}
    for index, fun in enumerate(raw["translated"]["fun_decls"]):
        if fun is None:
            continue
        try:
            full_name = name_of(fun)
        except ValueError:
            continue
        if full_name not in expected:
            continue
        if fun["item_meta"]["has_errors"]:
            raise ValueError(f"{full_name} has translation errors")
        fun_pointer = f"/translated/fun_decls/{index}"
        blocks = list(walk_asm(fun["body"], fun_pointer + "/body"))
        if len(blocks) != 1:
            raise ValueError(f"{full_name}: expected one complete assembly block, found {len(blocks)}")
        pointer, asm = blocks[0]
        if set(asm) != {"kind", "template", "operands", "options"}:
            raise ValueError("unsupported inline assembly fields")
        routines[expected[full_name]] = {
            "name": full_name,
            "json_pointer": pointer,
            "function_json_pointer": fun_pointer,
            **asm,
        }
    if set(routines) != {"add", "mul"}:
        raise ValueError(f"missing target routines: {set(expected.values()) - set(routines)}")
    return routines


def verify_retained(envelope: dict, artifacts: Path) -> dict:
    raw_path = artifacts / envelope["extraction"]["raw_artifact"]
    if digest(raw_path) != envelope["extraction"]["raw_sha256"]:
        raise ValueError("retained raw Charon artifact SHA-256 mismatch")
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    routines = selected_routines(raw)
    if routines != envelope["routines"]:
        raise ValueError("envelope differs from structured assembly in the retained Charon artifact")
    for routine in routines.values():
        linked = json_pointer(raw, routine["json_pointer"])
        if linked != {k: routine[k] for k in ("kind", "template", "operands", "options")}:
            raise ValueError("invalid JSON-pointer link to retained extraction")
    return raw


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, default=DEFAULT_WORK / "pasta_curves")
    ap.add_argument("--charon-source", type=Path, default=DEFAULT_WORK / "charon")
    ap.add_argument("--charon", type=Path)
    ap.add_argument("--artifacts", type=Path, default=ROOT / "artifacts")
    ap.add_argument("--check", action="store_true", help="re-extract and fail if retained structured assembly is stale")
    args = ap.parse_args()
    args.source = args.source.resolve()
    args.charon_source = args.charon_source.resolve()
    args.artifacts = args.artifacts.resolve()
    suffix = ".exe" if os.name == "nt" else ""
    args.charon = (args.charon or args.charon_source / "charon" / "target" / "release" / ("charon" + suffix)).resolve()
    pins = json.loads((ROOT / "pins.json").read_text())
    pin = pins["extraction"]
    assert_checkout(args.source, pins["pasta"]["revision"])
    assert_checkout(args.charon_source, pin["revision"])
    reject_external_cargo_config(args.source)
    for binary in (args.charon, args.charon.with_name("charon-driver" + suffix)):
        if not binary.is_file():
            raise RuntimeError(f"missing Charon binary {binary}; run python scripts/bootstrap.py")
    rustv = checked_output(["rustup", "run", pin["rust_toolchain"], "rustc", "-Vv"], args.charon_source)
    if f"commit-hash: {pin['rust_commit']}" not in rustv:
        raise RuntimeError("compiler commit does not match pins.json")
    version = checked_output([str(args.charon), "version"], args.source)
    if version != f"{pin['charon_version']} ({pin['revision']})":
        raise RuntimeError(f"unexpected Charon version: {version}")
    toolchain = checked_output([str(args.charon), "toolchain-version"], args.source)
    if toolchain != pin["rust_toolchain"]:
        raise RuntimeError(f"unexpected Charon compiler toolchain: {toolchain}")
    binary_hashes = {name: digest(args.charon.with_name(name + suffix)) for name in ("charon", "charon-driver")}
    build_record_path = args.charon_source.parent / "charon-build-record.json"
    build_record = None
    if build_record_path.exists():
        build_record = json.loads(build_record_path.read_text(encoding="utf-8"))
        if build_record["charon_revision"] != pin["revision"] or build_record["rustc"] != rustv:
            raise RuntimeError("Charon build record does not match pinned source/compiler")
        if build_record["binaries"] != binary_hashes:
            raise RuntimeError("Charon binaries differ from the bootstrap build record")
    else:
        print("Provenance limitation: no bootstrap build record; binary hashes are recorded, source-to-binary correspondence is trusted.", flush=True)
    args.artifacts.mkdir(parents=True, exist_ok=True)
    (ROOT / "logs").mkdir(parents=True, exist_ok=True)
    source_path = args.source / pins["pasta"]["assembly_source"]
    source_blob = subprocess.check_output(["git", "show", "HEAD:" + pins["pasta"]["assembly_source"]], cwd=args.source)
    source_info = {**pins["pasta"], "sha256": hashlib.sha256(source_blob).hexdigest(),
                   "git_blob": checked_output(["git", "rev-parse", "HEAD:" + pins["pasta"]["assembly_source"]], args.source)}
    extraction_info = {"charon_revision": pin["revision"], "charon_version": pin["charon_version"],
                       "rust_toolchain": pin["rust_toolchain"], "rust_commit": pin["rust_commit"],
                       "target": pin["target"], "raw_artifact": "pasta_curves.llbc"}
    if args.check:
        retained = json.loads((args.artifacts / "charon-asm.json").read_text(encoding="utf-8"))
        verify_retained(retained, args.artifacts)
        if retained["source"] != source_info:
            raise ValueError("retained source provenance differs from pinned checkout")
        if {k: retained["extraction"][k] for k in extraction_info} != extraction_info:
            raise ValueError("retained extraction pins are stale")
        provenance = json.loads((args.artifacts / "extraction-provenance.json").read_text(encoding="utf-8"))
        validate_source_provenance(provenance, source_path, args.source / "Cargo.lock")
        for name in ("charon", "charon-driver"):
            key = "charon_binary_sha256" if name == "charon" else "driver_binary_sha256"
            if provenance[key] != binary_hashes[name]:
                raise ValueError(f"current {name} binary differs from retained extraction provenance; regenerate explicitly")
        if provenance.get("build_record") != build_record:
            raise ValueError("current build record differs from retained extraction provenance")
    with tempfile.TemporaryDirectory(prefix="charon-extract-", dir=DEFAULT_WORK) as temp:
        temp = Path(temp)
        fresh = temp / "pasta_curves.llbc"
        cmd = [str(args.charon), "cargo", "--no-dedup-serialized-ast"]
        for start in pin["start_from"]:
            cmd += ["--start-from", start]
        cmd += ["--dest-file", str(fresh), "--", "--lib", "--locked", "--target", pin["target"],
                "--features", ",".join(pin["features"])]
        env = os.environ.copy()
        env["CARGO_TARGET_DIR"] = str(temp / "target")
        for key in list(env):
            if key.startswith(("CARGO_BUILD_", "CARGO_TARGET_", "CARGO_PROFILE_")) or key in (
                "RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS",
                "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN"):
                env.pop(key, None)
        env["CARGO_TARGET_DIR"] = str(temp / "target")
        env["RUSTFLAGS"] = ""
        started = time.perf_counter()
        print("+", subprocess.list2cmdline(cmd), flush=True)
        proc = subprocess.run(cmd, cwd=args.source, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.perf_counter() - started
        (ROOT / "logs" / "charon-extraction.log").write_bytes(proc.stdout)
        if proc.returncode:
            if fresh.is_file():
                (ROOT / "logs" / "failed-charon-emission.llbc").write_bytes(fresh.read_bytes())
            sys.stderr.write(proc.stdout.decode("utf-8", errors="replace"))
            raise RuntimeError(f"Charon extraction failed with exit {proc.returncode}; see logs/charon-extraction.log")
        raw = json.loads(fresh.read_text(encoding="utf-8"))
        if raw["charon_version"] != pin["charon_version"]:
            raise ValueError("raw artifact Charon version mismatch")
        try:
            routines = selected_routines(raw)
        except (KeyError, TypeError, ValueError):
            (ROOT / "logs" / "failed-charon-emission.llbc").write_bytes(fresh.read_bytes())
            raise
        if args.check:
            if routines != retained["routines"]:
                raise ValueError("retained structured assembly is stale against fresh Charon extraction")
            print(f"PASS: fresh Charon extraction matches retained complete add/mul templates and structured operands ({elapsed:.3f}s)")
            return
        extraction_info["raw_sha256"] = digest(fresh)
        envelope = {"schema_version": 1, "source": source_info, "extraction": extraction_info, "routines": routines}
        (args.artifacts / "pasta_curves.llbc").write_bytes(fresh.read_bytes())
        (args.artifacts / "charon-asm.json").write_bytes(canonical(envelope))
        provenance = {"command": cmd, "cwd": str(args.source), "rustc": rustv, "charon_version_output": version,
                      "charon_binary_sha256": binary_hashes["charon"],
                      "driver_binary_sha256": binary_hashes["charon-driver"],
                      "build_record": build_record,
                      "source_cargo_lock_sha256": digest(args.source / "Cargo.lock"),
                      "source_worktree_sha256": digest(source_path),
                      "source_hash_convention": "source.sha256 hashes the immutable Git blob, independent of platform line endings; source_worktree_sha256 hashes the exact file Charon read.",
                      "extraction_seconds": elapsed,
                      "trust": "The extraction script, compiler, Charon implementation, local build, Git checkout and artifact hashes are trusted provenance. SHA-256 is an integrity link, not proof that a compiler faithfully extracted Rust."}
        (args.artifacts / "extraction-provenance.json").write_bytes(canonical(provenance))
        verify_retained(envelope, args.artifacts)
        print(f"PASS: retained Charon LLBC and exact add/mul assembly subtrees ({elapsed:.3f}s)")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"extraction failed: {exc}", file=sys.stderr)
        sys.exit(1)
