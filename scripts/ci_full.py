"""Run the complete technical CI check in a fresh, isolated staged workspace.

The source checkout and its historical evidence are never updated. Upload the
output directory excluding workspace/work, .lake and compiled build products.
PASS requires every automated technical verification gate to succeed.
"""
from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import sys
from typing import Callable

from axiom_audit import audit_log, require_declarations
import check_formal_negatives as addition_negative
import check_mul_formal_negatives as multiplication_negative
from measure import run

ROOT = Path(__file__).resolve().parents[1]
OMIT_DIRS = {'.git', '.lake', '__pycache__'}
COMPILED = {'.olean', '.ilean', '.pyc', '.o', '.obj', '.exe', '.dll', '.lib', '.so', '.dylib', '.a'}
TARGETS = {'addition': 'PastaBridge.AdditionCorrectness.addition_correct',
           'multiplication': 'PastaBridge.MulCorrectness.multiplication_correct'}
Executor = Callable[[list[str], Path, Path, dict[str, str]], dict]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    hashed = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            hashed.update(block)
    return hashed.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def read_json(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def resource_snapshot(path: Path) -> dict:
    """Record capacity without inventing a minimum-memory or disk threshold."""
    disk = shutil.disk_usage(path)
    result = {'disk_total_bytes': disk.total, 'disk_free_bytes': disk.free}
    try:
        if os.name == 'nt':
            import ctypes

            class Memory(ctypes.Structure):
                _fields_ = [('length', ctypes.c_ulong), ('load', ctypes.c_ulong)] + [
                    (name, ctypes.c_ulonglong) for name in ('total', 'available', 'page_total',
                        'page_available', 'virtual_total', 'virtual_available', 'extended_available')]

            memory = Memory()
            memory.length = ctypes.sizeof(Memory)
            require(bool(ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(memory))), 'memory query failed')
            result.update(memory_total_bytes=memory.total, memory_available_bytes=memory.available)
        else:
            result['memory_total_bytes'] = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
            result['memory_available_bytes'] = os.sysconf('SC_AVPHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    except (AttributeError, OSError, ValueError) as error:
        result['memory_query_limitation'] = str(error)
    return result


def manifest(root: Path, *, protected_only: bool = False) -> dict[str, str]:
    result = {}
    for directory, dirs, names in os.walk(root):
        dirs[:] = sorted(name for name in dirs if name not in OMIT_DIRS)
        relative = Path(directory).relative_to(root)
        if protected_only and not relative.parts:
            dirs[:] = [name for name in dirs if name not in {'artifacts', 'generated', 'evidence', 'logs'}]
        for name in sorted(names):
            path = Path(directory) / name
            if name == '.git' or path.suffix in COMPILED:
                continue
            require(not path.is_symlink(), 'symlink source is unsupported: ' + str(path))
            result[path.relative_to(root).as_posix()] = digest(path)
        for name in dirs:
            require(not (Path(directory) / name).is_symlink(), 'symlink directory is unsupported')
    return result


def stage_copy(source: Path, output: Path) -> Path:
    source, output = source.resolve(), output.resolve()
    require(source.is_dir(), 'source project is missing')
    require(not output.is_relative_to(source) and not source.is_relative_to(output),
            'output and source must be separate directory trees')
    require(not output.exists() or not any(output.iterdir()), 'output directory must be empty')
    output.mkdir(parents=True, exist_ok=True)
    target = output / 'workspace/outputs/pasta-assembly-verification-bridge'

    def ignore(directory, names):
        ignored = {name for name in names if name in OMIT_DIRS or Path(name).suffix in COMPILED}
        if Path(directory) == source:
            ignored |= {'evidence', 'logs'}
        return ignored

    shutil.copytree(source, target, ignore=ignore)
    (target / 'evidence').mkdir()
    (target / 'logs').mkdir()
    for name in ('artifacts', 'generated'):
        require((source / name).is_dir(), 'missing retained baseline: ' + name)
        shutil.copytree(source / name, output / 'baseline' / name, ignore=ignore)
    return target


def same_manifest(expected: dict, root: Path, *, protected_only=False) -> None:
    require(manifest(root, protected_only=protected_only) == expected,
            'source/pin/Lean input bytes or file set changed')


def provenance_comparison(project: Path, baseline: Path) -> dict:
    old = read_json(baseline / 'artifacts/charon-asm.json')
    new = read_json(project / 'artifacts/charon-asm.json')
    require(new['schema_version'] == old['schema_version'], 'extraction schema changed')
    require(new['source'] == old['source'], 'immutable Pasta source identity changed')
    require(set(new['routines']) == set(old['routines']) == {'add', 'mul'}, 'target routines changed')
    require(new['routines'] == old['routines'], 'original complete templates/operands/options changed')
    require({k: v for k, v in new['extraction'].items() if k != 'raw_sha256'} ==
            {k: v for k, v in old['extraction'].items() if k != 'raw_sha256'}, 'extraction tool/source pins changed')
    require(new['extraction']['raw_sha256'] == digest(project / 'artifacts/pasta_curves.llbc'),
            'new raw artifact hash does not match extraction envelope')
    require(manifest(project / 'generated').keys() == manifest(baseline / 'generated').keys(),
            'generated file set changed')
    for name in manifest(baseline / 'generated'):
        if name == 'manifest.json':
            before, after = read_json(baseline / 'generated' / name), read_json(project / 'generated' / name)
            require({k: v for k, v in before.items() if k != 'artifact_sha256'} ==
                    {k: v for k, v in after.items() if k != 'artifact_sha256'}, 'generated manifest semantics changed')
            require(after['artifact_sha256'] == digest(project / 'artifacts/charon-asm.json'), 'stale adapter provenance')
        else:
            require(digest(project / 'generated' / name) == digest(baseline / 'generated' / name),
                    'compact projection/assembly bytes changed: ' + name)
    before = read_json(baseline / 'artifacts/extraction-provenance.json')
    after = read_json(project / 'artifacts/extraction-provenance.json')
    require(after.get('build_record') is not None, 'fresh bootstrap build record missing')
    for name in ('charon_binary_sha256', 'driver_binary_sha256', 'rustc', 'charon_version_output'):
        require(bool(after.get(name)), 'fresh tool identity missing: ' + name)
    return {'status': 'PASS', 'complete_templates_operands_options_unchanged': True,
        'compact_projections_and_assembly_bytes_unchanged': True,
        'raw_artifact_sha256': {'original': old['extraction']['raw_sha256'], 'fresh': new['extraction']['raw_sha256']},
        'provenance_field_changes': {key: {'original': before.get(key), 'fresh': after.get(key)}
                                    for key in sorted(before.keys() | after.keys()) if before.get(key) != after.get(key)},
        'metadata_policy': 'Fresh raw metadata, command paths, binary hashes and extraction timings may differ. Differences are retained as provenance; source pins, complete routines and checked program bytes must match.'}


def verification_requirements(project: Path) -> tuple[set[str], dict[str, set[str]]]:
    """Read literal gate declarations without executing the verification module."""
    tree = ast.parse((project / 'scripts/verify.py').read_text(encoding='utf-8'))
    literals = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in {'addition_required', 'mul_bridge_modules', 'mul_proof_modules', 'mul_censuses', 'addition_targets'}:
                literals[node.targets[0].id] = ast.literal_eval(node.value)
    required = set(literals['addition_required']) | {name.lower() for name in
        literals['mul_bridge_modules'] + literals['mul_proof_modules']} | {
        'addition-target-correctness', 'multiplication-target-correctness', 'parser-boundaries',
        'multiplication-parser', 'mul-json-certificate-current', 'multiplication-semantics',
        'mul-proof-inventory', 'mul-formal-negatives'}
    censuses = {name.lower(): set(names) for name, names in literals['mul_censuses'].items()}
    censuses.update({'proof-inventory': set(literals['addition_targets']),
        'arithmetic-proof': {'PastaAssemblyBridge.Arithmetic.addition', 'PastaAssemblyBridge.Arithmetic.multiplication'},
        'additioncorrectness': {TARGETS['addition']}, 'mulcorrectness': {TARGETS['multiplication']},
        'mul-proof-inventory': {TARGETS['multiplication'], 'multiplication_target_type'}})
    return required, censuses


def check_measurement(item: dict) -> None:
    require(isinstance(item.get('wall_seconds'), (int, float)) and math.isfinite(item['wall_seconds']) and item['wall_seconds'] >= 0,
            'wall measurement missing')
    require(isinstance(item.get('peak_rss_bytes'), int) and item['peak_rss_bytes'] > 0,
            'peak memory measurement missing')


def validate_report(project: Path, started: str, actual_exit: int) -> dict:
    evidence = project / 'evidence'
    threshold = datetime.fromisoformat(started).timestamp()

    def fresh(path: Path):
        require(path.is_file() and path.stat().st_mtime >= threshold, 'missing/stale report or log: ' + str(path))
        return path

    report = read_json(fresh(evidence / 'verification.json'))
    require(actual_exit == 0 and report.get('status') == 'PASS' and report.get('checks_failed') is False,
            'complete verification did not PASS with actual exit 0')
    require(not report.get('unresolved'), 'verification has unresolved obligations')
    require(isinstance(report.get('wall_seconds'), (int, float)) and math.isfinite(report['wall_seconds']) and
            report['wall_seconds'] > 0, 'consolidated wall measurement missing')
    require(datetime.fromisoformat(report['started_utc']).timestamp() >= threshold, 'old verification report')
    rows = report['stages']
    stages = {row['name']: row for row in rows}
    required, censuses = verification_requirements(project)
    require(len(rows) == len(stages) and required <= stages.keys(), 'missing/duplicate required verification stages')
    require(all(row.get('status') == 'PASS' for row in rows), 'a stage is failed, skipped or partial')
    nonprocess = {'upstream-snapshot', 'kraken-snapshot', 'used-kraken-source',
                  'kraken-compatibility-overlay', 'addition-target-correctness', 'multiplication-target-correctness'}
    require(all(bool(stages[name].get('command')) for name in required - nonprocess),
            'required process command or measurement is missing')
    direct_lean = []
    for name, item in stages.items():
        if item.get('command'):
            require(item.get('exit_code') == 0, 'nonzero stage process: ' + name)
            check_measurement(item)
            path = Path(item['log'])
            text = fresh(path if path.is_absolute() else project / path).read_text(encoding='utf-8')
            if Path(item['command'][0]).stem.lower() == 'lean':
                require(not any(token in text for token in ('sorryAx', 'warning:', 'error:')), 'Lean proof diagnostics: ' + name)
                if name in censuses:
                    require_declarations(text, censuses[name])
                else:
                    audit_log(text)
                direct_lean.append(item)
            if name == 'negative-policy-tests':
                require('skipped' not in text.lower() and '\nOK' in text, 'policy tests skipped or incomplete')
        require(name not in censuses or bool(item.get('command')), 'missing measured proof audit: ' + name)
    for target in TARGETS:
        require(stages[target + '-target-correctness'].get('missing_checks') == [], 'incomplete target gate')
    arithmetic = read_json(fresh(evidence / 'arithmetic-serial-build.json'))
    require(arithmetic.get('status') == 'PASS' and arithmetic.get('completed_modules') ==
            arithmetic.get('expected_modules') == len(arithmetic.get('modules', [])) == 13, 'incomplete arithmetic closure')
    for item in arithmetic['modules']:
        require(item.get('exit_code') == 0, 'arithmetic module failed')
        check_measurement(item)
        fresh(Path(item['log']))
    direct_lean += arithmetic['modules']
    for target in TARGETS:
        runtime = read_json(fresh(evidence / (target + '-runtime.json')))
        require(runtime.get('status') == 'PASS' and runtime.get('positive_cases', 0) > 0 and
                runtime.get('incoming_flag_patterns') == 16, 'runtime check incomplete')
        for kind in ('broken-carry', 'wrong-operand-binding'):
            mutant = runtime.get('negative_semantic_checks', {}).get(kind, {})
            require(mutant.get('status') == 'PASS: semantic mismatch detected' and mutant.get('mismatches', 0) > 0,
                    'runtime mutant did not produce a semantic mismatch')
        for kind in ('x19_written', 'x19_shared_readonly'):
            require(runtime.get('register_coverage', {}).get(kind, {}).get('flag_patterns_by_field') ==
                    {'pallasBase': 16, 'vestaBase': 16}, 'missing X19 model-vector coverage')
        formal_dir = 'formal-addition-negatives' if target == 'addition' else 'formal-multiplication-negatives'
        negatives = read_json(fresh(evidence / formal_dir / 'report.json'))
        checks = negatives.get('stages', [])
        require(negatives.get('status') == 'PASS' and len(checks) == 3 and
                all(item.get('status') == 'PASS' for item in checks), 'formal negatives incomplete')
        require(checks[0].get('strict_axiom_census_passed') is True and checks[0].get('exit_code') == 0,
                'formal certificate census failed')
        for item in checks:
            check_measurement(item)
            fresh(Path(item['log']))
        require(all(item.get('semantic_rejection_confirmed') is True and item.get('exit_code') == 1
                    for item in checks[1:]), 'false equality did not fail on intended semantics')
        checker = addition_negative if target == 'addition' else multiplication_negative
        certificate_output = Path(checks[0]['log']).read_text(encoding='utf-8')
        require(checker.check_census(certificate_output)[0], 'formal helper census is invalid')
        expected = dict(checker.RESULTS)
        for item in checks[1:]:
            require(item.get('name') in expected, 'unexpected formal semantic rejection')
            text = Path(item['log']).read_text(encoding='utf-8')
            arguments = expected[item['name']]
            confirmed = (checker.is_semantic_rejection(arguments, item['exit_code'], text) if target == 'addition'
                         else checker.is_semantic_rejection(*arguments, item['exit_code'], text))
            require(confirmed, 'formal failure is not the exact intended-proposition diagnostic')
        require({item['name'] for item in checks[1:]} == expected.keys(), 'formal mutant check missing or duplicated')
        direct_lean += checks
    require(bool(direct_lean), 'no measured Lean proof checks')
    return {'technical_status': 'PASS', 'acceptance_status': 'PASS',
        'verification_wall_seconds': report['wall_seconds'],
        'direct_lean_wall_seconds': round(sum(row['wall_seconds'] for row in direct_lean), 6),
        'maximum_direct_lean_peak_bytes': max(row['peak_rss_bytes'] for row in direct_lean),
        'measurement_scope': 'Direct Lean source checks, audits and formal negatives; peak is maximum individual child, not process-tree sum.',
        'required_stages': sorted(required), 'direct_lean_checks': direct_lean}


def execute(command, cwd, log, env):
    return run(command, cwd=cwd, log=log, env=env)


def run_full(source: Path, output: Path, *, executor: Executor = execute,
             find_tool: Callable = shutil.which) -> dict:
    source, output = source.resolve(), output.resolve()
    source_before = manifest(source)
    project = stage_copy(source, output)
    protected = manifest(project, protected_only=True)
    work = output / 'workspace/work'
    work.mkdir()
    report = {'status': 'RUNNING', 'technical_status': 'RUNNING', 'acceptance_status': 'RUNNING',
        'started_utc': utc(), 'source': str(source), 'runtime_project': str(project), 'stages': [],
        'environment': {'platform': platform.platform(), 'python': sys.version,
                        **{key: os.environ.get(key) for key in ('ImageOS', 'ImageVersion', 'GITHUB_SHA',
                            'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_EVENT_NAME')}},
        'resources_before': resource_snapshot(output),
        'scope': 'Automated technical verification of register-entry Kraken models; no Rust wrapper load/store or ARM hardware-vector claim.'}
    write_json(output / 'source-inputs.json', source_before)

    def save():
        write_json(output / 'ci-full.json', report)

    env = os.environ.copy()
    env['CARGO_HOME'] = str(work / 'cargo-home')
    env['RUSTUP_HOME'] = str(work / 'rustup-home')
    save()

    def command(name, args):
        print('Checking ' + name + '...', flush=True)
        record = executor(args, project, output / 'logs' / (name + '.log'), env)
        record.update(name=name, status='PASS' if record.get('exit_code') == 0 else 'FAIL')
        report['stages'].append(record)
        save()
        require(record.get('exit_code') == 0, name + ' failed; see its retained command log')
        check_measurement(record)
        require(record.get('command') == args, 'command identity missing from measured process')
        return record

    try:
        tools = {name: find_tool(name) for name in ('git', 'rustup', 'cargo')}
        require(all(tools.values()), 'missing git, rustup or cargo')
        require(all(Path(path).is_file() for path in tools.values()), 'tool path is not a file')
        report['tools'] = {name: {'path': str(Path(path).resolve()), 'sha256': digest(Path(path))}
                           for name, path in tools.items()}
        report['private_toolchain_directories'] = {key: env[key] for key in ('CARGO_HOME', 'RUSTUP_HOME')}
        save()
        command('bootstrap-extraction', [sys.executable, 'scripts/bootstrap.py'])
        command('install-lean', [sys.executable, 'scripts/install_lean.py'])
        suffix = '.exe' if os.name == 'nt' else ''
        candidates = list((work / 'toolchains').glob('lean-*/bin'))
        require(len(candidates) == 1 and all((candidates[0] / (name + suffix)).is_file()
                    for name in ('lean', 'lake')), 'pinned Lean/Lake installation missing or ambiguous')
        lean_bin = candidates[0].resolve()
        env['PATH'] = str(lean_bin) + os.pathsep + env.get('PATH', '')
        report['lean_bin'] = str(lean_bin)
        report['tools'].update({name: {'path': str(lean_bin / (name + suffix)),
            'sha256': digest(lean_bin / (name + suffix))} for name in ('lean', 'lake')})
        write_json(output / 'tool-identities.json', report['tools'])
        command('bootstrap-proofs', [sys.executable, 'proofs/bootstrap.py', '--lean-bin', str(lean_bin)])
        command('fresh-binary-extraction', [sys.executable, 'scripts/extract.py'])
        command('regenerate-adapter', [sys.executable, 'bridge/kraken_adapter.py', '--artifact',
                                      'artifacts/charon-asm.json', '--output', 'generated'])
        same_manifest(protected, project, protected_only=True)
        try:
            comparison = provenance_comparison(project, output / 'baseline')
        except (OSError, ValueError, KeyError, TypeError) as error:
            write_json(output / 'extraction-provenance-comparison.json', {'status': 'FAIL', 'reason': str(error),
                'evidence': 'Original and fresh raw artifacts, envelopes, provenance and generated files retained separately.'})
            raise
        write_json(output / 'extraction-provenance-comparison.json', comparison)
        seal_before = manifest(project)
        write_json(output / 'verification-inputs.json', seal_before)
        started = utc()
        # Do not add flags, replace the command, or count a local-only run here.
        args = [sys.executable, 'scripts/verify.py', '--clean']
        actual = executor(args, project, output / 'logs/verify-clean.log', env)
        write_json(project / 'evidence/verification-exit.json', {**actual, 'observed_utc': utc(),
            'method': 'Actual measured subprocess return code; no shell status mapping'})
        report['stages'].append({**actual, 'name': 'verify-clean',
                                'status': 'PASS' if actual.get('exit_code') == 0 else 'FAIL'})
        save()
        # Evidence/log files are expected outputs, not sealed verification inputs.
        sealed_after = manifest(project)
        sealed_after = {k: v for k, v in sealed_after.items() if not k.startswith(('evidence/', 'logs/'))}
        sealed_before = {k: v for k, v in seal_before.items() if not k.startswith(('evidence/', 'logs/'))}
        changed = sorted(set(sealed_before) ^ set(sealed_after) |
                         {key for key in sealed_before.keys() & sealed_after.keys() if sealed_before[key] != sealed_after[key]})
        write_json(output / 'verification-input-seal.json', {'status': 'PASS' if not changed else 'FAIL',
            'changed_inputs': changed, 'actual_exit_code': actual.get('exit_code'), 'checked_files': len(sealed_before)})
        require(not changed, 'verification source/artifact inputs changed during clean run')
        require(actual.get('command') == args, 'documented verification command identity missing')
        check_measurement(actual)
        summary = validate_report(project, started, actual.get('exit_code'))
        write_json(output / 'measurements.json', summary)
        report.update(status='PASS', technical_status='PASS', acceptance_status='PASS')
    except (OSError, ValueError, KeyError, TypeError, SyntaxError) as error:
        report.update(status='FAIL', technical_status='FAIL', acceptance_status='FAIL', reason=str(error))
    finally:
        try:
            same_manifest(source_before, source)
            report['original_checkout_unchanged'] = True
        except (OSError, ValueError) as error:
            report.update(status='FAIL', technical_status='FAIL', acceptance_status='FAIL', original_checkout_unchanged=False, reason=str(error))
        report['finished_utc'] = utc()
        report['resources_after'] = resource_snapshot(output)
        save()
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='empty directory outside the source project')
    parser.add_argument('--source', type=Path, default=ROOT)
    args = parser.parse_args()
    report = run_full(args.source, args.output)
    print(json.dumps(report, indent=2))
    return 0 if report['technical_status'] == 'PASS' else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit('Full CI failed: ' + str(error)) from error
