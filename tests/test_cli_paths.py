"""Exercise CLI path handling with subprocess working directories isolated.

Tools and reports are temporary fixtures. No Lean proof or historical evidence
is produced or replaced by these tests.
"""
from contextlib import ExitStack, chdir, redirect_stderr, redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
sys.path.insert(0, str(ROOT / "scripts"))
import check_formal_negatives
import kraken_compat
import verify


def load_entrypoint(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


source_bootstrap = load_entrypoint("cli_source_bootstrap", ROOT / "scripts/bootstrap.py")
proof_bootstrap = load_entrypoint("cli_proof_bootstrap", ROOT / "proofs/bootstrap.py")
arithmetic_builder = load_entrypoint("cli_arithmetic_builder", ROOT / "proofs/build_arithmetic.py")


class ReachedToolInvocation(Exception):
    """Stop a fixture at the tool boundary without running a compiler."""


class CliPathTests(unittest.TestCase):
    def setUp(self):
        WORK.mkdir(exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="cli-path-test-", dir=WORK)
        self.addCleanup(temporary.cleanup)
        self.workspace = Path(temporary.name).resolve()
        self.package = self.workspace / "outputs/bridge"
        self.work = self.workspace / "work"
        self.tools = self.work / "tools/bin"
        self.tools.mkdir(parents=True)
        self.suffix = ".exe" if os.name == "nt" else ""
        self.lean = self.tools / ("lean" + self.suffix)
        self.lake = self.tools / ("lake" + self.suffix)
        self.lean.touch()
        self.lake.touch()
        for directory in ("artifacts", "evidence", "generated", "proofs", "vendor/kraken"):
            (self.package / directory).mkdir(parents=True)
        self.pins = json.loads((ROOT / "pins.json").read_text(encoding="utf-8"))
        self.release = json.loads((ROOT / "lean-release.lock.json").read_text(encoding="utf-8"))
        (self.package / "pins.json").write_text(json.dumps(self.pins), encoding="utf-8")
        (self.package / "lean-release.lock.json").write_text(json.dumps(self.release), encoding="utf-8")
        (self.package / "artifacts/charon-asm.json").write_text("{}", encoding="utf-8")
        (self.package / "vendor/kraken/UPSTREAM.json").write_text('{"files":{}}', encoding="utf-8")

    def test_verifier_relative_tool_directory_survives_nested_cwd_changes(self):
        # Package invocation matches the documented ../../work/... spelling;
        # workspace invocation passes work/... while children run in the package.
        for caller in (self.package, self.workspace):
            with self.subTest(caller=caller):
                seen = []
                overlay = self.work / "kraken-compat"
                overlay.mkdir(exist_ok=True)

                def tool_path(command, cwd):
                    path = Path(command[0])
                    if path.name in (self.lean.name, self.lake.name):
                        self.assertTrue(path.is_absolute(), command)
                        self.assertTrue(path.samefile(self.tools / path.name), command)
                        self.assertFalse(Path(cwd or caller).samefile(caller))
                        seen.append(path.name)

                def measured(command, *, cwd, log, env=None):
                    if "--lean-bin" in command:
                        forwarded = Path(command[command.index("--lean-bin") + 1])
                        self.assertTrue(forwarded.is_absolute(), command)
                        self.assertTrue(forwarded.samefile(self.tools), command)
                        seen.append("forwarded")
                    if Path(command[0]).name == self.lean.name:
                        tool_path(command, cwd)
                        raise ReachedToolInvocation
                    if Path(command[0]).name == self.lake.name:
                        tool_path(command, cwd)
                    log.write_text("", encoding="utf-8")
                    return {"command": command, "exit_code": 0,
                            "wall_seconds": 0, "log": str(log)}

                def output(command, **kwargs):
                    if Path(command[0]).name == self.lean.name:
                        self.assertTrue(Path(command[0]).samefile(self.lean), command)
                        return f"Lean (version {self.release['version']}, commit {self.release['compiler_commit']})"
                    if command[:3] == ["git", "rev-parse", "HEAD"]:
                        return self.pins["kraken"]["revision"]
                    if Path(command[0]).name == self.lake.name:
                        tool_path(command, kwargs["cwd"])
                        return json.dumps({"PATH": str(self.tools), "LEAN_PATH": "fixture"})
                    self.fail(f"unexpected subprocess: {command}")

                relative = os.path.relpath(self.tools, caller)
                with ExitStack() as stack:
                    stack.enter_context(chdir(caller))
                    stack.enter_context(redirect_stdout(io.StringIO()))
                    stack.enter_context(patch.object(sys, "argv", ["verify.py", "--bootstrap", "--lean-bin", relative]))
                    stack.enter_context(patch.object(verify, "ROOT", self.package))
                    stack.enter_context(patch.object(verify, "WORK", self.work))
                    stack.enter_context(patch.object(verify, "check_pasta_snapshot", return_value={"status": "PASS"}))
                    stack.enter_context(patch.object(verify, "check_kraken_snapshot", return_value={"status": "PASS"}))
                    stack.enter_context(patch.object(verify, "prepare_kraken", return_value=overlay))
                    stack.enter_context(patch.object(verify, "run", side_effect=measured))
                    stack.enter_context(patch.object(subprocess, "check_output", side_effect=output))
                    stack.enter_context(patch.object(subprocess, "run", return_value=subprocess.CompletedProcess([], 0)))
                    with self.assertRaises(ReachedToolInvocation):
                        verify.main()
                self.assertIn("forwarded", seen)
                self.assertIn(self.lake.name, seen)
                self.assertIn(self.lean.name, seen)

    def test_shared_environment_helpers_resolve_tools_before_child_cwd(self):
        for caller in (self.package, self.workspace):
            for helper in ("verify", "formal-negatives"):
                with self.subTest(caller=caller, helper=helper), chdir(caller):
                    relative = Path(os.path.relpath(self.tools, caller))
                    child_cwd = self.package / "proofs"

                    def output(command, *, cwd, **kwargs):
                        self.assertTrue(Path(command[0]).samefile(self.lake), command)
                        self.assertTrue(Path(command[0]).is_absolute())
                        self.assertTrue(Path(cwd).samefile(child_cwd))
                        return '{"LEAN_PATH":"fixture"}'

                    with patch.object(subprocess, "check_output", side_effect=output):
                        if helper == "verify":
                            result = verify.lean_environment(relative / self.lake.name, child_cwd, {})
                        else:
                            with patch.object(check_formal_negatives, "ROOT", self.package):
                                result = check_formal_negatives.lean_environment(relative)
                    self.assertEqual(result["LEAN_PATH"], "fixture")

    def test_proof_entrypoints_resolve_relative_tools(self):
        for module in (proof_bootstrap, arithmetic_builder):
            for caller in (self.package, self.workspace):
                with self.subTest(entrypoint=module.__name__, caller=caller), chdir(caller):
                    relative = os.path.relpath(self.tools, caller)

                    def output(command, **kwargs):
                        expected = self.lean if module is proof_bootstrap else self.lake
                        self.assertTrue(Path(command[0]).samefile(expected), command)
                        self.assertTrue(Path(command[0]).is_absolute())
                        if module is arithmetic_builder:
                            self.assertTrue(Path(kwargs["cwd"]).samefile(self.package / "proofs"))
                        raise ReachedToolInvocation

                    with patch.object(module, "ROOT", self.package / "proofs"), \
                            patch.object(sys, "argv", ["entrypoint.py", "--lean-bin", relative]), \
                            patch.object(subprocess, "check_output", side_effect=output):
                        with self.assertRaises(ReachedToolInvocation):
                            module.main()

    def test_bootstrap_has_one_fixed_workspace_and_rejects_work_override(self):
        self.assertTrue(source_bootstrap.DEFAULT_WORK.samefile(kraken_compat.WORK))
        with patch.object(sys, "argv", ["bootstrap.py", "--work", "somewhere-else"]), \
                redirect_stderr(io.StringIO()) as errors, \
                patch.object(source_bootstrap, "checkout") as checkout:
            with self.assertRaises(SystemExit) as rejected:
                source_bootstrap.main()
        self.assertEqual(rejected.exception.code, 2)
        self.assertIn("unrecognized arguments: --work", errors.getvalue())
        checkout.assert_not_called()
        with patch.object(sys, "argv", ["bootstrap.py", "--help"]), \
                redirect_stdout(io.StringIO()) as help_text:
            with self.assertRaises(SystemExit) as helped:
                source_bootstrap.main()
        self.assertEqual(helped.exception.code, 0)
        self.assertNotIn("--work", help_text.getvalue())
        self.assertIn("fixed workspace directory", help_text.getvalue())

    def test_bootstrap_default_places_all_sources_in_fixed_workspace(self):
        with patch.object(source_bootstrap, "ROOT", self.package), \
                patch.object(source_bootstrap, "DEFAULT_WORK", self.work), \
                patch.object(sys, "argv", ["bootstrap.py", "--sources-only"]), \
                patch.object(source_bootstrap, "checkout", side_effect=lambda work, name, pin: work / name) as checkout, \
                patch.object(kraken_compat, "prepare") as prepare:
            source_bootstrap.main()
        self.assertEqual([call.args[1] for call in checkout.call_args_list],
                         ["pasta_curves", "charon", "aeneas", "kraken"])
        for call in checkout.call_args_list:
            self.assertTrue(Path(call.args[0]).samefile(self.work))
        prepare.assert_called_once_with()


if __name__ == "__main__":
    unittest.main()
