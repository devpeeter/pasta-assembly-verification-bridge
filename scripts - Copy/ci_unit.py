"""Run Python and retained-artifact CI checks without bootstrapping proof tools.

Logs and the report go only to a new external output directory. A successful
result checks source/artifact consistency; it is not a fresh extraction, Lean
proof rebuild, or execution on AArch64 hardware.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time
import traceback

from integrity import check_kraken_snapshot, check_pasta_snapshot
from extract import verify_retained
from check_proof_dependencies import locked_git_packages

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_PREFIX = "outputs/pasta-assembly-verification-bridge"
# These are the explicit build/cache exclusions used by the source packager.
BUILD_DIRECTORIES = frozenset({".git", ".lake", "__pycache__", "work", ".pytest_cache"})
BUILD_SUFFIXES = frozenset({".olean", ".ilean", ".pyc", ".o", ".obj", ".trace", ".hash"})
REQUIRED_STAGES = frozenset({"unit-tests", "source-integrity", "generated-current",
                             "mul-json-certificate-current", "source-manifest"})


class CiError(ValueError):
    pass


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CiError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_unique_object)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(root: Path) -> dict[str, Path]:
    """Inventory all source/evidence files, rejecting symbolic links."""
    result = {}
    for current, directories, filenames in os.walk(root):
        directory = Path(current)
        for name in directories + filenames:
            if (directory / name).is_symlink():
                raise CiError(f"source symlink is unsupported: {directory / name}")
        directories[:] = sorted(name for name in directories if name not in BUILD_DIRECTORIES)
        for name in sorted(filenames):
            path = directory / name
            relative = path.relative_to(root).as_posix()
            if relative == "SOURCE-MANIFEST.json" or path.suffix in BUILD_SUFFIXES:
                continue
            if not path.is_file():
                raise CiError(f"nonregular source entry: {path}")
            result[relative] = path
    return result


def check_source_manifest(root: Path) -> dict:
    manifest = load_json(root / "SOURCE-MANIFEST.json")
    if (manifest.get("format") != 1 or manifest.get("archive_prefix") != ARCHIVE_PREFIX or
            not isinstance(manifest.get("files"), dict) or not manifest["files"]):
        raise CiError("invalid or empty source manifest")
    expected = manifest["files"]
    for relative, expected_digest in expected.items():
        path = PurePosixPath(relative)
        if (not relative or "\\" in relative or ":" in relative or path.is_absolute() or
                any(part in ("", ".", "..") for part in relative.split("/"))):
            raise CiError(f"unsafe source manifest path: {relative}")
        if not isinstance(expected_digest, str) or not re.fullmatch(r"[0-9a-f]{64}", expected_digest):
            raise CiError(f"invalid source manifest digest: {relative}")
    actual = source_files(root)
    if set(actual) != set(expected):
        raise CiError(f"source manifest file set differs: missing={sorted(set(expected) - set(actual))}; "
                      f"unlisted={sorted(set(actual) - set(expected))}")
    for relative, path in actual.items():
        if digest(path) != expected[relative]:
            raise CiError(f"source manifest hash mismatch: {relative}")
    return {"checked_files": len(actual), "manifest_sha256": digest(root / "SOURCE-MANIFEST.json")}


def check_retained_extraction(root: Path, pins: dict) -> dict:
    """Check retained provenance identities and complete raw LLBC links offline."""
    artifact = root / "artifacts/charon-asm.json"
    envelope = load_json(artifact)
    if envelope.get("schema_version") != 1:
        raise CiError("unsupported retained extraction schema")
    for field in ("repository", "revision", "assembly_source"):
        if envelope["source"].get(field) != pins["pasta"][field]:
            raise CiError(f"retained Pasta source pin differs: {field}")
    if (pins["pasta"]["assembly_source"] != "src/asm/aarch64.rs" or
            pins["extraction"]["target"] != "aarch64-unknown-linux-gnu" or
            pins["extraction"]["features"] != ["asm"] or
            pins["extraction"]["start_from"] !=
            ["crate::asm::aarch64::add", "crate::asm::aarch64::mul"]):
        raise CiError("unsupported retained extraction source/target selection")
    expected = {"charon_revision": pins["extraction"]["revision"],
                "charon_version": pins["extraction"]["charon_version"],
                "rust_toolchain": pins["extraction"]["rust_toolchain"],
                "rust_commit": pins["extraction"]["rust_commit"],
                "target": pins["extraction"]["target"], "raw_artifact": "pasta_curves.llbc"}
    if any(envelope["extraction"].get(key) != value for key, value in expected.items()):
        raise CiError("retained compiler/Charon extraction pins differ")
    # Reject traversal before handing the retained filename to the existing
    # raw-artifact and JSON-pointer checker.
    raw = verify_retained(envelope, artifact.parent)
    provenance = load_json(artifact.with_name("extraction-provenance.json"))
    version = f"{expected['charon_version']} ({expected['charon_revision']})"
    if provenance.get("charon_version_output") != version:
        raise CiError("retained Charon version output differs from pins")
    rustc = provenance.get("rustc", "")
    if not re.search(r"^commit-hash: " + re.escape(expected["rust_commit"]) + r"$", rustc, re.MULTILINE):
        raise CiError("retained Rust compiler identity differs from pins")
    build = provenance.get("build_record")
    if (not isinstance(build, dict) or build.get("charon_revision") != expected["charon_revision"] or
            build.get("rustc") != rustc or build.get("binaries") != {
                "charon": provenance.get("charon_binary_sha256"),
                "charon-driver": provenance.get("driver_binary_sha256")}):
        raise CiError("retained Charon build record is inconsistent")
    hashes = [envelope["source"].get("sha256"), envelope["extraction"].get("raw_sha256"),
              *(provenance.get(key) for key in ("charon_binary_sha256", "driver_binary_sha256",
                  "source_worktree_sha256", "source_cargo_lock_sha256"))]
    if any(not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value) for value in hashes):
        raise CiError("missing or malformed retained provenance digest")
    if not re.fullmatch(r"[0-9a-f]{40}", envelope["source"].get("git_blob", "")):
        raise CiError("missing or malformed retained Git blob identity")
    return {"raw_sha256": envelope["extraction"]["raw_sha256"],
            "routines": sorted(envelope["routines"]), "raw_has_errors": raw["has_errors"],
            "scope": "Retained identity and JSON-pointer checks; no fresh extraction or compiler rebuild"}


def check_source_integrity(root: Path) -> dict:
    pasta = check_pasta_snapshot(root / "vendor/pasta")
    kraken = check_kraken_snapshot(root / "vendor/kraken")
    pins = load_json(root / "pins.json")
    if pins["pasta"]["revision"] != pasta["commit"] or pins["kraken"]["revision"] != kraken["commit"]:
        raise CiError("source pins differ from retained upstream snapshots")
    if (pins["pasta"]["repository"] != "https://github.com/zcash/pasta_curves.git" or
            pins["kraken"]["repository"] != "https://github.com/AeneasVerif/kraken.git"):
        raise CiError("source pin repositories differ from retained upstream snapshots")
    for value in [*(pins[name]["revision"] for name in ("pasta", "kraken", "aeneas", "extraction")),
                  pins["extraction"]["rust_commit"], pins["aeneas"]["mathlib_revision"]]:
        if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value):
            raise CiError("source/tool revision is not an immutable commit")
    locked = locked_git_packages(root / "proofs", root / "pins.json")
    return {"pasta": pasta, "kraken": kraken, "extraction": check_retained_extraction(root, pins),
            "locked_git_package_count": len(locked),
            "locked_git_packages": [{"name": package["name"], "revision": package["rev"],
                                     "repository": package["url"]} for package in locked],
            "dependency_check_scope": "Pure lock/schema/pin validation; no dependency checkout, Git invocation or cache verification"}


def check_unittest_result(exit_code: int, output: str) -> dict:
    summaries = re.findall(r"^Ran (\d+) tests? in ([0-9.]+)s$", output, re.MULTILINE)
    if (exit_code != 0 or len(summaries) != 1 or int(summaries[0][0]) == 0 or
            not output.rstrip().endswith("OK") or re.search(r"\bskipped\b", output)):
        raise CiError("Python tests failed, were skipped, or did not report a nonempty successful suite")
    return {"tests": int(summaries[0][0]), "reported_seconds": float(summaries[0][1]), "skips": 0}


def prepare_output(root: Path, output: Path) -> Path:
    output = output.resolve()
    root = root.resolve()
    if output.is_relative_to(root) or root.is_relative_to(output):
        raise CiError("CI output must be outside, and must not contain, the source package")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise CiError("CI output must be a new or empty directory")
    output.mkdir(parents=True, exist_ok=True)
    return output


def run_ci(root: Path, output: Path) -> dict:
    root = root.resolve()
    output = prepare_output(root, output)
    report = {"status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
              "scope": "Python/source/artifact integrity CI; no bootstrap, fresh extraction, Lean proof rebuild or ARM hardware execution",
              "source_root": str(root), "stages": []}

    def save():
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def check(name, function):
        started = time.perf_counter()
        log = output / (name + ".log")
        item = {"name": name, "log": log.name}
        try:
            item["details"] = function()
            item["status"] = "PASS"
            log.write_text(json.dumps(item["details"], indent=2) + "\n", encoding="utf-8")
        except Exception as exc:
            item.update(status="FAIL", reason=str(exc))
            log.write_text(traceback.format_exc(), encoding="utf-8")
        item["wall_seconds"] = round(time.perf_counter() - started, 6)
        report["stages"].append(item)
        save()
        print(f"{item['status']}: {name}", flush=True)

    def command(name, arguments, unittest=False):
        started = time.perf_counter()
        log = output / (name + ".log")
        item = {"name": name, "command": [sys.executable, *arguments], "cwd": str(root), "log": log.name}
        try:
            env = os.environ.copy()
            env["PYTHONDONTWRITEBYTECODE"] = "1"
            with log.open("wb") as stream:
                result = subprocess.run(item["command"], cwd=root, env=env,
                                        stdout=stream, stderr=subprocess.STDOUT)
            item["exit_code"] = result.returncode
            if unittest:
                item["details"] = check_unittest_result(result.returncode, log.read_text(encoding="utf-8", errors="replace"))
            elif result.returncode != 0:
                raise CiError(f"command exited {result.returncode}")
            item["status"] = "PASS"
        except Exception as exc:
            item.update(status="FAIL", reason=str(exc))
            if not log.exists():
                log.write_text(traceback.format_exc(), encoding="utf-8")
        item["wall_seconds"] = round(time.perf_counter() - started, 6)
        report["stages"].append(item)
        save()
        print(f"{item['status']}: {name}", flush=True)

    save()
    command("unit-tests", ["-m", "unittest", "discover", "-s", "tests", "-v"], unittest=True)
    check("source-integrity", lambda: check_source_integrity(root))
    command("generated-current", [str(root / "bridge/kraken_adapter.py"), "--artifact",
            str(root / "artifacts/charon-asm.json"), "--output", str(root / "generated"), "--check"])
    command("mul-json-certificate-current", [str(root / "scripts/generate_mul_json_certificate.py"), "--check"])
    check("source-manifest", lambda: check_source_manifest(root))
    passed = {stage["name"] for stage in report["stages"] if stage["status"] == "PASS"}
    report["status"] = "PASS" if passed == REQUIRED_STAGES else "FAIL"
    report["missing_or_failed_checks"] = sorted(REQUIRED_STAGES - passed)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    save()
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="new/empty artifact directory outside the source package")
    args = parser.parse_args()
    try:
        result = run_ci(ROOT, args.output)
    except (OSError, CiError) as exc:
        parser.error(str(exc))
    print(f"{result['status']}: CI unit/artifact checks; {args.output.resolve() / 'report.json'}")
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
