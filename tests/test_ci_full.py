"""Full-CI orchestration fixtures; no real toolchain build or proof claim."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import ci_full


def dump(path, data):
    ci_full.write_json(path, data)


def measurement(command, cwd, log, code=0):
    return {'command': command, 'cwd': str(cwd), 'log': str(log), 'exit_code': code,
            'wall_seconds': 1.0, 'peak_rss_bytes': 100, 'memory_metric': 'synthetic fixture only'}


def complete_report(project):
    """Emit synthetic data to exercise the runner's gates, not Lean evidence."""
    evidence = project / 'evidence'
    required, censuses = ci_full.verification_requirements(project)
    rows = []
    for name in sorted(required):
        log = evidence / (name + '.log')
        text = '\n'.join(f"'{declaration}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                         for declaration in sorted(censuses.get(name, set()))) + '\n'
        if name == 'negative-policy-tests':
            text = 'Ran 59 tests in 1.0s\n\nOK\n'
        log.write_text(text, encoding='utf-8')
        command = ['lean', 'fixture.lean'] if name in censuses else ['python', 'fixture.py']
        row = {'name': name, 'status': 'PASS', **measurement(command, project, log)}
        if name.endswith('-target-correctness'):
            row['missing_checks'] = []
        rows.append(row)
    dump(evidence / 'verification.json', {'status': 'PASS', 'checks_failed': False,
        'unresolved': [], 'started_utc': datetime.now(timezone.utc).isoformat(), 'wall_seconds': 42,
        'stages': rows})
    log = evidence / 'arithmetic.log'
    log.write_text('synthetic fixture\n', encoding='utf-8')
    measured = measurement(['lean', 'fixture.lean'], project, log)
    dump(evidence / 'arithmetic-serial-build.json', {'status': 'PASS', 'completed_modules': 13,
        'expected_modules': 13, 'modules': [measured.copy() for _ in range(13)]})
    for name in ('addition', 'multiplication'):
        dump(evidence / (name + '-runtime.json'), {'status': 'PASS', 'positive_cases': 32,
            'incoming_flag_patterns': 16, 'register_coverage': {kind: {'flag_patterns_by_field':
                {'pallasBase': 16, 'vestaBase': 16}} for kind in ('x19_written', 'x19_shared_readonly')},
            'negative_semantic_checks': {kind: {'status': 'PASS: semantic mismatch detected', 'mismatches': 3}
                for kind in ('broken-carry', 'wrong-operand-binding')}})
        directory = 'formal-addition-negatives' if name == 'addition' else 'formal-multiplication-negatives'
        (evidence / directory).mkdir(parents=True)
        checker = ci_full.addition_negative if name == 'addition' else ci_full.multiplication_negative
        certificate_log = evidence / directory / 'certificates.log'
        certificate_log.write_text('\n'.join(f"'{declaration}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for declaration in sorted(checker.EXPECTED_DECLARATIONS)) + '\n', encoding='utf-8')
        checks = [{**measured, 'name': 'kernel-counterexample-certificates', 'status': 'PASS',
                   'log': str(certificate_log), 'strict_axiom_census_passed': True}]
        for kind, result in checker.RESULTS.items():
            proposition = (result + ' = expected') if name == 'addition' else ' = '.join(result)
            diagnostic = evidence / directory / (kind + '.log')
            diagnostic.write_text('fixture.lean:1:1: error: Tactic `decide` proved that the proposition\n  ' +
                                  proposition + '\nis false\n', encoding='utf-8')
            checks.append({**measured, 'name': kind, 'status': 'PASS', 'exit_code': 1,
                           'log': str(diagnostic), 'semantic_rejection_confirmed': True})
        dump(evidence / directory / 'report.json', {'status': 'PASS', 'stages': checks})


class FakeExecutor:
    def __init__(self, mutation=None, verify_exit=0, fail_stage=None):
        self.calls = []
        self.mutation = mutation
        self.verify_exit = verify_exit
        self.fail_stage = fail_stage

    def __call__(self, args, cwd, log, env):
        self.calls.append((args.copy(), cwd, env.copy()))
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text('mock expensive command; no verification claim\n', encoding='utf-8')
        stage = Path(args[1]).name
        if stage == 'install_lean.py':
            binary = cwd.parent.parent / 'work/toolchains/lean-4.31.0-test/bin'
            binary.mkdir(parents=True)
            suffix = '.exe' if os.name == 'nt' else ''
            for name in ('lean', 'lake'):
                (binary / (name + suffix)).write_bytes(b'synthetic tool fixture')
        if stage == 'extract.py':
            raw = cwd / 'artifacts/pasta_curves.llbc'
            raw.write_text('{"fresh_metadata":true}\n', encoding='utf-8')
            envelope = ci_full.read_json(cwd / 'artifacts/charon-asm.json')
            envelope['extraction']['raw_sha256'] = ci_full.digest(raw)
            dump(cwd / 'artifacts/charon-asm.json', envelope)
            provenance = ci_full.read_json(cwd / 'artifacts/extraction-provenance.json')
            provenance['charon_binary_sha256'] = 'fresh test binary hash'
            dump(cwd / 'artifacts/extraction-provenance.json', provenance)
        if stage == 'kraken_adapter.py':
            generated = ci_full.read_json(cwd / 'generated/manifest.json')
            generated['artifact_sha256'] = ci_full.digest(cwd / 'artifacts/charon-asm.json')
            dump(cwd / 'generated/manifest.json', generated)
        if stage == 'verify.py':
            complete_report(cwd)
        if self.mutation:
            self.mutation(stage, cwd)
        code = self.verify_exit if stage == 'verify.py' else 1 if stage == self.fail_stage else 0
        return measurement(args, cwd, log, code)


class FullCITests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='pasta-ci-full-test-')
        self.addCleanup(self.temp.cleanup)
        self.top = Path(self.temp.name)
        self.source = self.top / 'checkout'
        self.output = self.top / 'output'
        self.tool = self.top / 'mock-tool'
        self.tool.write_bytes(b'mocked tool identity, never executed')
        for directory in ('scripts', 'proofs', 'bridge', 'generated', 'artifacts', 'evidence', 'logs', '.git', '.lake', '__pycache__'):
            (self.source / directory).mkdir(parents=True)
        # Use the delivered gate syntax; the executor is still entirely mocked.
        shutil.copyfile(ci_full.ROOT / 'scripts/verify.py', self.source / 'scripts/verify.py')
        (self.source / 'proofs/Target.lean').write_text('-- source fixture\n', encoding='utf-8')
        dump(self.source / 'pins.json', {'immutable_test_pin': 'a' * 40})
        (self.source / 'evidence/history.json').write_text('old report must stay in checkout', encoding='utf-8')
        for name in ('.git', '.lake', '__pycache__'):
            (self.source / name / 'old').write_text('must not stage', encoding='utf-8')
        raw = self.source / 'artifacts/pasta_curves.llbc'
        raw.write_text('{"original_metadata":true}\n', encoding='utf-8')
        dump(self.source / 'artifacts/charon-asm.json', {'schema_version': 1, 'source': {'revision': 'a' * 40},
            'extraction': {'rust_commit': 'b' * 40, 'raw_sha256': ci_full.digest(raw)},
            'routines': {name: {'kind': 'Asm', 'template': [{'Text': 'fixture'}],
                'operands': [{'In': {'reg': 'reg'}}], 'options': {'nomem': True}} for name in ('add', 'mul')}})
        dump(self.source / 'artifacts/extraction-provenance.json', {'build_record': {'pin': 'fixture'},
            'charon_binary_sha256': 'old', 'driver_binary_sha256': 'driver',
            'rustc': 'compiler fixture', 'charon_version_output': 'Charon fixture'})
        for name in ('add-check.json', 'mul-check.json', 'add.S', 'mul.S'):
            (self.source / 'generated' / name).write_text('fixture\n', encoding='utf-8')
        dump(self.source / 'generated/manifest.json', {'schema_version': 1,
            'artifact_sha256': ci_full.digest(self.source / 'artifacts/charon-asm.json'), 'routines': {}})
        self.original = ci_full.manifest(self.source)

    def run_fixture(self, **kwargs):
        executor = FakeExecutor(**kwargs)
        report = ci_full.run_full(self.source, self.output, executor=executor, find_tool=lambda _: str(self.tool))
        self.assertEqual(ci_full.manifest(self.source), self.original)
        return report, executor

    def test_complete_isolated_orchestration_and_exact_command(self):
        report, executor = self.run_fixture()
        self.assertEqual(report['technical_status'], 'PASS')
        self.assertEqual(report['acceptance_status'], 'PASS')
        project = self.output / 'workspace/outputs/pasta-assembly-verification-bridge'
        self.assertFalse((project / 'evidence/history.json').exists())
        self.assertTrue((self.source / 'evidence/history.json').exists())
        for name in ('.git', '.lake', '__pycache__'):
            self.assertFalse((project / name).exists())
        args, cwd, env = executor.calls[-1]
        self.assertEqual(args, [sys.executable, 'scripts/verify.py', '--clean'])
        self.assertEqual(cwd, project)
        self.assertEqual(env['CARGO_HOME'], str(self.output / 'workspace/work/cargo-home'))
        self.assertEqual(env['RUSTUP_HOME'], str(self.output / 'workspace/work/rustup-home'))
        proof_bootstrap = executor.calls[2][0]
        self.assertTrue(Path(proof_bootstrap[-1]).is_absolute())
        self.assertEqual(ci_full.read_json(self.output / 'verification-input-seal.json')['status'], 'PASS')
        measured = ci_full.read_json(self.output / 'measurements.json')
        self.assertEqual(measured['technical_status'], 'PASS')
        self.assertEqual(measured['acceptance_status'], 'PASS')
        comparison = ci_full.read_json(self.output / 'extraction-provenance-comparison.json')
        for item in (report, measured, comparison):
            self.assertFalse({'human_review_status', 'independent_specialist_acceptance',
                              'independent_specialist_review', 'review_required', 'outstanding_acceptance'} & item.keys())
            self.assertNotIn('OUTSTANDING', json.dumps(item))

    def test_missing_tools_fail_without_bootstrap(self):
        report = ci_full.run_full(self.source, self.output, executor=lambda *args: self.fail('must not execute'), find_tool=lambda _: None)
        self.assertEqual(report['status'], 'FAIL')
        self.assertEqual(report['acceptance_status'], 'FAIL')
        self.assertTrue((self.output / 'ci-full.json').exists())

    def test_nonempty_output_is_never_removed(self):
        self.output.mkdir()
        sentinel = self.output / 'sentinel'
        sentinel.write_text('preserve', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'must be empty'):
            ci_full.run_full(self.source, self.output)
        self.assertEqual(sentinel.read_text(), 'preserve')

    def test_bootstrap_failure_stops_and_keeps_logs(self):
        report, executor = self.run_fixture(fail_stage='bootstrap.py')
        self.assertEqual(report['status'], 'FAIL')
        self.assertEqual(len(executor.calls), 1)
        self.assertTrue((self.output / 'logs/bootstrap-extraction.log').is_file())

    def test_partial_report_and_nonzero_actual_exit_fail(self):
        def partial(stage, project):
            if stage == 'verify.py':
                path = project / 'evidence/verification.json'
                data = ci_full.read_json(path)
                data['status'] = 'PARTIAL'
                dump(path, data)
        report, _ = self.run_fixture(mutation=partial)
        self.assertEqual(report['status'], 'FAIL')

    def test_nonzero_actual_exit_cannot_be_hidden_by_pass_report(self):
        report, _ = self.run_fixture(verify_exit=2)
        self.assertEqual(report['status'], 'FAIL')
        project = self.output / 'workspace/outputs/pasta-assembly-verification-bridge'
        self.assertEqual(ci_full.read_json(project / 'evidence/verification-exit.json')['exit_code'], 2)

    def test_old_report_fails_even_when_file_was_just_written(self):
        def old(stage, project):
            if stage == 'verify.py':
                path = project / 'evidence/verification.json'
                data = ci_full.read_json(path)
                data['started_utc'] = '2000-01-01T00:00:00+00:00'
                dump(path, data)
        report, _ = self.run_fixture(mutation=old)
        self.assertEqual(report['status'], 'FAIL')

    def test_missing_audit_or_measurement_fails(self):
        def missing(stage, project):
            if stage == 'verify.py':
                (project / 'evidence/mul-proof-inventory.log').write_text('no declaration census\n', encoding='utf-8')
        report, _ = self.run_fixture(mutation=missing)
        self.assertEqual(report['status'], 'FAIL')

    def test_compact_projection_changes_are_not_accepted_as_metadata(self):
        def changed(stage, project):
            if stage == 'kraken_adapter.py':
                (project / 'generated/add-check.json').write_text('changed', encoding='utf-8')
        report, executor = self.run_fixture(mutation=changed)
        self.assertEqual(report['status'], 'FAIL')
        self.assertFalse(any(call[0][1] == 'scripts/verify.py' for call in executor.calls))

    def test_input_tampering_during_verify_fails_seal(self):
        def changed(stage, project):
            if stage == 'verify.py':
                (project / 'proofs/Target.lean').write_text('changed source', encoding='utf-8')
        report, _ = self.run_fixture(mutation=changed)
        self.assertEqual(report['status'], 'FAIL')
        self.assertEqual(ci_full.read_json(self.output / 'verification-input-seal.json')['status'], 'FAIL')

    def test_report_negative_cases_fail_closed(self):
        def modify(kind):
            def mutate(stage, project):
                if stage != 'verify.py':
                    return
                path = project / 'evidence/verification.json'
                data = ci_full.read_json(path)
                if kind == 'process-omitted':
                    next(row for row in data['stages'] if row['name'] == 'additionnat')['command'] = []
                elif kind == 'peak-omitted':
                    next(row for row in data['stages'] if row['name'] == 'mulcorrectness')['peak_rss_bytes'] = None
                elif kind == 'stage-omitted':
                    data['stages'] = [row for row in data['stages'] if row['name'] != 'mulcorrectness']
                elif kind == 'policy-omission':
                    (project / 'evidence/negative-policy-tests.log').write_text('Ran 1 test\nOK (skipped=1)\n', encoding='utf-8')
                elif kind == 'stale-runtime':
                    os.utime(project / 'evidence/addition-runtime.json', (1, 1))
                elif kind == 'escaped-mutant':
                    runtime_path = project / 'evidence/addition-runtime.json'
                    runtime = ci_full.read_json(runtime_path)
                    runtime['negative_semantic_checks']['broken-carry']['mismatches'] = 0
                    dump(runtime_path, runtime)
                elif kind == 'unrelated-false-proposition':
                    (project / 'evidence/formal-multiplication-negatives/broken-carry.log').write_text(
                        'fixture.lean:1:1: error: unrelated failure\n', encoding='utf-8')
                dump(path, data)
            return mutate
        for kind in ('process-omitted', 'peak-omitted', 'stage-omitted', 'policy-omission',
                     'stale-runtime', 'escaped-mutant', 'unrelated-false-proposition'):
            with self.subTest(kind=kind):
                self.output = self.top / ('output-' + kind)
                report, _ = self.run_fixture(mutation=modify(kind))
                self.assertEqual(report['status'], 'FAIL')

    def test_original_operand_changes_fail_before_verification(self):
        def mutate(stage, project):
            if stage == 'extract.py':
                path = project / 'artifacts/charon-asm.json'
                data = ci_full.read_json(path)
                data['routines']['add']['operands'] = []
                dump(path, data)
        report, _ = self.run_fixture(mutation=mutate)
        self.assertEqual(report['status'], 'FAIL')
        self.assertEqual(ci_full.read_json(self.output / 'extraction-provenance-comparison.json')['status'], 'FAIL')

    def test_unsupported_output_inside_checkout_fails(self):
        with self.assertRaisesRegex(ValueError, 'separate directory trees'):
            ci_full.run_full(self.source, self.source / 'runtime')


if __name__ == '__main__':
    unittest.main()
