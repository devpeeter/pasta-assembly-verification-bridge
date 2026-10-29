"""Rebuild and check the implemented bridge stages, reporting incomplete proofs.

Exit 0 is reserved for complete target verification; 1 means a check failed;
2 means required verification remains incomplete or a prerequisite is missing.
Run from any directory. A local-only run is diagnostic and always exits 2.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from integrity import check_pasta_snapshot, check_kraken_snapshot
from measure import run
from kraken_compat import prepare as prepare_kraken
from axiom_audit import audit_log, require_declarations

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"


def lean_environment(lake: Path, cwd: Path, base: dict[str, str]) -> dict[str, str]:
    lake = lake.resolve()
    query = ("import os,json; print(json.dumps({k:os.environ.get(k,'') "
             "for k in ['LEAN_PATH','LEAN_SRC_PATH','PATH']}))")
    result = subprocess.check_output([str(lake), "env", sys.executable, "-c", query],
                                     cwd=cwd, env=base, text=True)
    env = base.copy()
    env.update(json.loads(result))
    return env


def safe_clean(path: Path, owner: Path, expected_name: str = "build") -> None:
    """Delete only a known build directory, never sources or retained artifacts."""
    resolved = path.resolve()
    workspace = ROOT.parent.parent.resolve()
    if (not resolved.is_relative_to(workspace) or
            not resolved.is_relative_to(owner.resolve()) or resolved.name != expected_name):
        raise ValueError(f"refusing to clean unexpected directory {resolved}")
    if resolved.exists():
        shutil.rmtree(resolved)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bootstrap", action="store_true", help="fetch/build the pinned tools first")
    parser.add_argument("--clean", action="store_true", help="remove local Lean build outputs before checking")
    parser.add_argument("--local-only", action="store_true", help="run policy/integrity tests only; never complete verification")
    parser.add_argument("--lean-bin", type=Path, help="directory containing the pinned Lean and Lake executables")
    args = parser.parse_args()
    if args.lean_bin is not None:
        args.lean_bin = args.lean_bin.resolve()
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    report = {"started_utc": datetime.now(timezone.utc).isoformat(),
              "status": "PARTIAL", "stages": [], "unresolved": []}
    started = time.perf_counter()
    failed = False
    blocked = False

    def save():
        report["wall_seconds"] = round(time.perf_counter() - started, 6)
        (evidence / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def stage(name: str, command: list[str], cwd: Path = ROOT,
              env: dict[str, str] | None = None,
              required_declarations: set[str] | None = None) -> bool:
        nonlocal failed
        print(f"Checking {name}...", flush=True)
        try:
            item = run(command, cwd=cwd, log=evidence / (name + ".log"), env=env)
        except OSError as exc:
            item = {"command": command, "status": "BLOCKED", "reason": str(exc)}
            report["stages"].append({"name": name, **item})
            save()
            print(f"BLOCKED: {name}: {exc}", flush=True)
            return False
        item["status"] = "PASS" if item["exit_code"] == 0 else "FAIL"
        # A Lean process may exit successfully after admitting a warning-backed
        # declaration. Successful compilation alone is not an axiom audit.
        log_text = (evidence / (name + ".log")).read_text(encoding="utf-8", errors="replace")
        if Path(command[0]).stem.lower() == "lean" and any(
                marker in log_text for marker in ("sorryAx", "warning:", "error:")):
            item["status"] = "FAIL"
            item["reason"] = "Lean warning/error or sorryAx in proof-check output"
        if Path(command[0]).stem.lower() == "lean":
            try:
                item["axiom_census"] = (require_declarations(log_text, required_declarations)
                                        if required_declarations else audit_log(log_text))
            except ValueError as exc:
                item["status"] = "FAIL"
                item["reason"] = str(exc)
        report["stages"].append({"name": name, **item})
        save()
        print(f"{item['status']}: {name} ({item['wall_seconds']:.3f}s)", flush=True)
        if item["status"] != "PASS":
            failed = True
            print(log_text[-5000:])
        return item["status"] == "PASS"

    try:
        snapshot = check_pasta_snapshot(ROOT / "vendor/pasta")
        report["stages"].append({"name": "upstream-snapshot", **snapshot})
        snapshot = check_kraken_snapshot(ROOT / "vendor/kraken")
        report["stages"].append({"name": "kraken-snapshot", **snapshot})
    except Exception as exc:
        failed = True
        report["stages"].append({"name": "upstream-snapshot", "status": "FAIL", "reason": str(exc)})

    if args.bootstrap and not args.local_only:
        if not stage("bootstrap-extraction", [sys.executable, str(ROOT / "scripts/bootstrap.py")]):
            blocked = True
        if not stage("bootstrap-lean", [sys.executable, str(ROOT / "scripts/install_lean.py")]):
            blocked = True

    suffix = ".exe" if os.name == "nt" else ""
    lean_bin = args.lean_bin
    if lean_bin is None:
        local_tool = WORK / "toolchains/lean-4.31.0-windows/bin"
        if os.name != "nt":
            candidates = list((WORK / "toolchains").glob("lean-4.31.0-*/bin"))
            local_tool = candidates[0] if candidates else local_tool
        lean_bin = local_tool if (local_tool / ("lean" + suffix)).is_file() else None
    if lean_bin is None and shutil.which("lean"):
        lean_bin = Path(shutil.which("lean")).parent
    if lean_bin is not None:
        lean_bin = lean_bin.resolve()

    if args.bootstrap and not args.local_only and lean_bin is not None:
        if not stage("bootstrap-proofs", [sys.executable, str(ROOT / "proofs/bootstrap.py"),
                                          "--lean-bin", str(lean_bin)]):
            blocked = True

    artifact = ROOT / "artifacts/charon-asm.json"
    if not args.local_only and not blocked:
        if not artifact.is_file():
            print("Creating the initial genuine extraction before the independent rebuild check.", flush=True)
            if not stage("initial-extraction", [sys.executable, str(ROOT / "scripts/extract.py")]):
                blocked = True
        if artifact.is_file():
            if not stage("fresh-extraction", [sys.executable, str(ROOT / "scripts/extract.py"), "--check"]):
                blocked = True
            generated = ROOT / "generated"
            adapter_command = [sys.executable, str(ROOT / "bridge/kraken_adapter.py"),
                               "--artifact", str(artifact), "--output", str(generated)]
            if not generated.exists():
                stage("initial-adapter", adapter_command)
            if not stage("generated-current", adapter_command + ["--check"]):
                blocked = True

    if not stage("negative-policy-tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"]):
        blocked = True
    test_log = (evidence / "negative-policy-tests.log").read_text(encoding="utf-8", errors="replace")
    if "skipped" in test_log:
        blocked = True
        report["stages"][-1]["status"] = "INCOMPLETE"
        report["unresolved"].append("Some artifact integration tests were skipped; this is not a complete test pass.")

    if not args.local_only and not blocked and lean_bin is not None:
        if not stage("proof-dependencies", [sys.executable,
                str(ROOT / "scripts/check_proof_dependencies.py")]):
            blocked = True

    if args.local_only:
        report["unresolved"].append("Local-only diagnostic: extraction rebuild, Kraken execution, Lean proofs and target correctness were not verified.")
    elif not lean_bin or not (lean_bin / ("lean" + suffix)).is_file():
        blocked = True
        report["unresolved"].append("Pinned Lean is unavailable. Run with --bootstrap or supply --lean-bin.")
    elif not blocked:
        lean = lean_bin / ("lean" + suffix)
        lake = lean_bin / ("lake" + suffix)
        env = os.environ.copy()
        env["PATH"] = str(lean_bin) + os.pathsep + env.get("PATH", "")
        version = subprocess.check_output([str(lean), "--version"], env=env, text=True).strip()
        report["lean_version"] = version
        release = json.loads((ROOT / "lean-release.lock.json").read_text(encoding="utf-8"))
        if (f"version {release['version']}" not in version or
                f"commit {release['compiler_commit']}" not in version):
            failed = blocked = True
            report["unresolved"].append(f"Wrong Lean toolchain: {version}")
        kraken = WORK / "kraken"
        proofs = ROOT / "proofs"
        pins = json.loads((ROOT / "pins.json").read_text(encoding="utf-8"))
        try:
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=kraken,
                                                text=True).strip()
            if revision != pins["kraken"]["revision"]:
                raise ValueError("Kraken build checkout is at the wrong revision")
            subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=kraken, check=True)
            from integrity import sha256
            manifest = json.loads((ROOT / "vendor/kraken/UPSTREAM.json").read_text())
            for relative, expected in manifest["files"].items():
                if sha256(kraken / relative) != expected:
                    raise ValueError(f"Kraken build source differs from snapshot: {relative}")
            report["stages"].append({"name": "used-kraken-source", "status": "PASS", "revision": revision})
        except (OSError, ValueError, subprocess.CalledProcessError) as exc:
            failed = blocked = True
            report["stages"].append({"name": "used-kraken-source", "status": "FAIL", "reason": str(exc)})
        if not blocked:
            try:
                kraken = prepare_kraken()
                report["stages"].append({"name": "kraken-compatibility-overlay", "status": "PASS",
                    "path": str(kraken), "patch_sha256": pins["kraken"]["compatibility_patch_sha256"],
                    "immediate_shift_patch_sha256": pins["kraken"]["immediate_shift_patch_sha256"],
                    "zero_destination_patch_sha256": pins["kraken"]["zero_destination_patch_sha256"]})
            except (OSError, ValueError) as exc:
                failed = blocked = True
                report["stages"].append({"name": "kraken-compatibility-overlay", "status": "FAIL", "reason": str(exc)})
        if args.clean:
            safe_clean(kraken / ".lake/build", kraken)
            safe_clean(WORK / "bridge-build", WORK, "bridge-build")
        if not blocked:
            if not stage("kraken-build", [str(lake), "build", "Kraken.AArch64.Parser", "Kraken.AArch64.Semantics"], kraken, env):
                blocked = True
            else:
                kenv = lean_environment(lake, kraken, env)
                (WORK / "bridge-build").mkdir(parents=True, exist_ok=True)
                for label, filename in (("kraken-word", "KrakenWord.lean"),
                                        ("kraken-binding", "KrakenBinding.lean")):
                    if not stage(label, [str(lean), "-o", str(WORK / "bridge-build" / Path(filename).with_suffix(".olean")),
                                         filename], proofs, kenv):
                        blocked = True
                bridge = ROOT / "bridge"
                compiled_bridge = WORK / "bridge-build"
                compiled_bridge.mkdir(parents=True, exist_ok=True)
                kenv["LEAN_PATH"] = str(compiled_bridge) + os.pathsep + kenv.get("LEAN_PATH", "")
                decoder_ok = True
                modules = ["KernelJson", "Artifact"]
                if (bridge / "Retained.lean").is_file():
                    modules.append("Retained")
                modules.append("KrakenRun")
                for module in modules:
                    if not stage(module.lower(), [str(lean), "-o", str(compiled_bridge / (module + ".olean")),
                                   module + ".lean"], bridge, kenv):
                        decoder_ok = False
                        blocked = True
                        break
                link = bridge / "CheckAddition.lean"
                if link.is_file():
                    if decoder_ok and not stage("artifact-link", [str(lean), "-o", str(compiled_bridge / "CheckAddition.olean"),
                                                                  link.name], bridge, kenv):
                        blocked = True
                else:
                    report["unresolved"].append("Kernel checked representation-to-artifact correspondence is unavailable.")
                runtime = ROOT / "scripts/runtime_checks.py"
                if runtime.is_file():
                    if not stage("addition-semantics", [sys.executable, str(runtime), "--lean", str(lean),
                              "--lake", str(lake), "--kraken", str(kraken)], ROOT, env):
                        blocked = True
                else:
                    report["unresolved"].append("Addition execution and semantic mutation checks are unavailable.")
            if args.clean:
                safe_clean(proofs / ".lake/build", proofs)
                safe_clean(ROOT / "vendor/pasta/lean/.lake/build", ROOT / "vendor/pasta/lean")
            if stage("arithmetic-build", [sys.executable, str(ROOT / "proofs/build_arithmetic.py"),
                                          "--lean-bin", str(lean_bin)], ROOT, env):
                penv = lean_environment(lake, proofs, env)
                penv["LEAN_PATH"] = os.pathsep.join([str(WORK / "bridge-build"),
                    str(kraken / ".lake/build/lib/lean"), penv.get("LEAN_PATH", "")])
                if stage("arithmetic-proof", [str(lean), "ArithmeticAudit.lean"], proofs, penv):
                    output = (evidence / "arithmetic-proof.log").read_text(encoding="utf-8", errors="replace")
                    if "sorryAx" in output or "warning:" in output or "error:" in output:
                        failed = True
                        report["unresolved"].append("Arithmetic axiom/warning audit failed; see evidence/arithmetic-proof.log.")
                for module in ("WordCorrespondence", "AdditionStep", "AdditionMachine",
                               "AdditionNat", "AdditionNatSequence", "AdditionNatData", "AdditionNatObservation",
                               "AdditionParametricBase", "AdditionParametricModel",
                               "AdditionNatDataModel", "AdditionNatLiftBase", "AdditionNatModel",
                               "AdditionNatLift", "BindingArtifact",
                               "AdditionCorrectness"):
                    if (proofs / (module + ".lean")).is_file():
                        required = {
                            "AdditionNat": {"PastaBridge.AdditionNat.step_project"},
                            "AdditionNatSequence": {"PastaBridge.AdditionNat.sequence_project"},
                            "AdditionNatData": {"PastaBridge.AdditionNatData.retained_data_readback"},
                            "AdditionNatObservation": {"PastaBridge.AdditionNat.words_transition",
                                                       "PastaBridge.AdditionNatData.words_sequence_cons"},
                            "AdditionParametricBase": {"PastaBridge.AdditionParametric.model_specializes",
                                                       "PastaBridge.AdditionParametric.transition_specializes",
                                                       "PastaBridge.AdditionParametric.sequence_specializes"},
                            "AdditionParametricModel": {"PastaBridge.AdditionParametric.generic_model",
                                                        "PastaBridge.AdditionParametric.retained_data_model"},
                            "AdditionNatDataModel": {"PastaBridge.AdditionNatData.retained_data_model"},
                            "AdditionNatModel": {"PastaBridge.AdditionNat.decoded_program_model"},
                            "AdditionNatLift": {"PastaBridge.AdditionNat.all_bindings_model"},
                            "BindingArtifact": {"PastaBridge.BindingArtifact.bound_program_matches_template"},
                            "AdditionCorrectness": {"PastaBridge.AdditionCorrectness.addition_correct"},
                        }.get(module)
                        if not stage(module.lower(), [str(lean), "-DautoImplicit=false", "-o", str(WORK / "bridge-build" / (module + ".olean")),
                                                       module + ".lean"], proofs, penv,
                                     required_declarations=required):
                            blocked = True
                addition_targets = {
                    "PastaBridge.AdditionCorrectness.addition_correct",
                    "PastaBridge.BindingArtifact.bound_program_matches_template",
                    "PastaBridge.AdditionNat.all_bindings_model",
                    "addition_target_type",
                }
                final_addition_sources = all((proofs / (module + ".lean")).is_file()
                    for module in ("AdditionCorrectness", "AdditionNatLift", "BindingArtifact"))
                if not stage("proof-inventory", [str(lean), "-DautoImplicit=false", "Audit.lean"], proofs, penv,
                             required_declarations=addition_targets if final_addition_sources else None):
                    blocked = True
                formal_negatives = ROOT / "scripts/check_formal_negatives.py"
                if final_addition_sources and formal_negatives.is_file():
                    if not stage("addition-formal-negatives", [sys.executable, str(formal_negatives),
                                                              "--lean-bin", str(lean_bin)], ROOT, env):
                        blocked = True
            else:
                blocked = True

    # Require the actual closed target, all-binding artifact link and semantic
    # negatives in this invocation. Source presence or an earlier run is insufficient.
    completed = {item["name"] for item in report["stages"] if item.get("status") == "PASS"}
    addition_required = {
        "upstream-snapshot", "kraken-snapshot", "fresh-extraction", "generated-current",
        "negative-policy-tests", "used-kraken-source",
        "proof-dependencies",
        "kraken-compatibility-overlay", "kraken-build", "artifact-link", "addition-semantics",
        "kraken-word", "kraken-binding", "kerneljson", "artifact", "retained", "krakenrun",
        "wordcorrespondence", "additionstep", "additionmachine",
        "arithmetic-build", "arithmetic-proof", "additionnat", "additionnatsequence", "additionnatlift",
        "additionnatdata", "additionnatobservation", "additionnatdatamodel", "additionnatliftbase", "additionnatmodel",
        "additionparametricbase", "additionparametricmodel",
        "bindingartifact", "additioncorrectness", "proof-inventory", "addition-formal-negatives",
    }
    addition_passed = addition_required <= completed
    report["stages"].append({
        "name": "addition-target-correctness", "status": "PASS" if addition_passed else "INCOMPLETE",
        "missing_checks": sorted(addition_required - completed),
        "theorem": "PastaBridge.AdditionCorrectness.addition_correct"})

    # All multiplication target checks follow the actual addition gate in this
    # invocation, including a fresh elaboration of constants that include files.
    mul_bridge_modules = ("StringBytes", "MulArtifact", "MulRetained", "MulMetadata",
                          "MulJsonTextDagBase", "MulJsonTextDagFinal", "MulJsonCertificate")
    mul_proof_modules = ("MulWord", "MulStep", "MulMachine", "MulProgramData", "MulSequenceFrame", "MulNat",
                         "MulNatSequence", "MulParametricBase", "MulParametricRounds",
                         "MulParametricModel", "MulNatLift", "MulFormatting", "MulPieceFormatting", "MulBindingArtifact",
                         "MulCertificate", "MulCorrectness")
    mul_censuses = {
        "StringBytes": {"PastaBridge.StringBytes.injective", "PastaBridge.StringBytes.append",
                        "PastaBridge.StringBytes.intercalate"},
        "MulMetadata": {"PastaBridge.multiplication_pieces_match_retained_value",
                        "PastaBridge.multiplication_operand_metadata_matches"},
        "MulJsonTextDagBase": {"PastaBridge.MulJsonTextDag.encoded_124"},
        "MulJsonTextDagFinal": {"PastaBridge.MulJsonTextDag.retained_encoding",
                               "PastaBridge.MulJsonTextDag.retained_value_readback",
                               "PastaBridge.MulJsonTextDag.retained_bytes_readback"},
        "MulJsonCertificate": {"PastaBridge.multiplication_value_encodes_retained_artifact",
                               "PastaBridge.multiplication_artifact_chars_readback"},
        "MulCertificate": {"PastaBridge.multiplication_artifact_matches_retained_program",
                                "PastaBridge.multiplication_retained_representation_certificate"},
        "MulProgramData": {"PastaBridge.MulProgramData.retained_instructions_readback"},
        "MulSequenceFrame": {"PastaBridge.MulSequenceFrame.readonly"},
        "MulNat": {"PastaBridge.MulNat.step_project"},
        "MulNatSequence": {"PastaBridge.MulNat.sequence_project"},
        "MulParametricModel": {"PastaBridge.MulParametric.retained_data_model"},
        "MulNatLift": {"PastaBridge.MulNat.all_bindings_model"},
        "MulFormatting": {"PastaBridge.MulFormatting.serialize_instruction",
                          "PastaBridge.MulFormatting.serialize_program"},
        "MulPieceFormatting": {"PastaBridge.MulPieceFormatting.render_program",
                               "PastaBridge.MulPieceFormatting.render_normalize"},
        "MulBindingArtifact": {"PastaBridge.MulBindingArtifact.bound_program_matches_template"},
        "MulCorrectness": {"PastaBridge.MulCorrectness.multiplication_correct"},
    }
    mul_required = {module.lower() for module in mul_bridge_modules + mul_proof_modules} | {
        "parser-boundaries", "multiplication-parser", "mul-json-certificate-current", "multiplication-semantics",
        "mul-proof-inventory", "mul-formal-negatives"}
    if addition_passed and not blocked:
        if not stage("parser-boundaries", [sys.executable, str(ROOT / "scripts/parser_checks.py"),
                                          "--lean-bin", str(lean_bin)], ROOT, env):
            blocked = True
        if not stage("multiplication-parser", [sys.executable, str(ROOT / "scripts/probe_multiplication.py"),
                                              "--lean-bin", str(lean_bin)], ROOT, env):
            blocked = True
        if not stage("mul-json-certificate-current", [sys.executable,
                str(ROOT / "scripts/generate_mul_json_certificate.py"), "--check"], ROOT, env):
            blocked = True
        for module in mul_bridge_modules:
            source = ROOT / "bridge" / (module + ".lean")
            if not source.is_file():
                break
            if not stage(module.lower(), [str(lean), "-DautoImplicit=false", "-o",
                    str(WORK / "bridge-build" / (module + ".olean")), source.name],
                    ROOT / "bridge", kenv, required_declarations=mul_censuses.get(module)):
                blocked = True
                break
        if not blocked:
            for module in mul_proof_modules:
                source = proofs / (module + ".lean")
                if not source.is_file():
                    break
                if not stage(module.lower(), [str(lean), "-DautoImplicit=false", "-o",
                        str(WORK / "bridge-build" / (module + ".olean")), source.name],
                        proofs, penv, required_declarations=mul_censuses.get(module)):
                    blocked = True
                    break
        if not blocked:
            if not stage("multiplication-semantics", [sys.executable,
                    str(ROOT / "scripts/multiplication_runtime_checks.py"),
                    "--lean", str(lean), "--lake", str(lake), "--kraken", str(kraken)], ROOT, env):
                blocked = True
            ready = all((proofs / (module + ".lean")).is_file() for module in mul_proof_modules)
            if ready and not blocked:
                if not stage("mul-proof-inventory", [str(lean), "-DautoImplicit=false", "MulAudit.lean"],
                        proofs, penv, required_declarations={"multiplication_target_type",
                            "PastaBridge.MulCorrectness.multiplication_correct"}):
                    blocked = True
                if not stage("mul-formal-negatives", [sys.executable,
                        str(ROOT / "scripts/check_mul_formal_negatives.py"), "--lean-bin", str(lean_bin)],
                        ROOT, env):
                    blocked = True
    completed = {item["name"] for item in report["stages"] if item.get("status") == "PASS"}
    multiplication_passed = addition_passed and mul_required <= completed
    report["stages"].append({
        "name": "multiplication-target-correctness", "status": "PASS" if multiplication_passed else "INCOMPLETE",
        "missing_checks": sorted(mul_required - completed),
        "theorem": "PastaBridge.MulCorrectness.multiplication_correct",
        "reason": None if multiplication_passed else "Required checks missing or failed." if addition_passed
                  else "Deferred until addition target correctness is complete."})
    if not addition_passed:
        report["unresolved"].append("Addition target verification is incomplete in this invocation; see its missing_checks.")
    if not multiplication_passed:
        report["unresolved"].append("Multiplication target verification is incomplete. Arithmetic-model proofs and test vectors do not replace it.")
    complete = addition_passed and multiplication_passed and not failed and not blocked
    report["status"] = "PASS" if complete else "BLOCKED" if blocked else "PARTIAL"
    report["checks_failed"] = failed
    save()
    print("PASS: both target verifications complete; see evidence/verification.json" if complete else
          f"{report['status']}: full target verification is incomplete; see evidence/verification.json", flush=True)
    return 0 if complete else 1 if failed else 2


if __name__ == "__main__":
    raise SystemExit(main())
