"""Mechanically quote the retained JSON as shared values and compositional text.

Candidates are generated only from the retained projection. Kernel readback and
encoding certificates, including one final exact byte comparison, are required.
No instruction sequence is transcribed. The generated source remains an
untrusted candidate until its readback and encoding proofs pass Lean.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
projection = ROOT / 'generated/mul-check.json'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='reject stale generated candidates')
args = parser.parse_args()
raw = projection.read_bytes()
value = json.loads(raw.decode('utf-8'))


def compact(x):
    return json.dumps(x, ensure_ascii=True, separators=(',', ':'))


def literal(x):
    return json.dumps(x, ensure_ascii=True)


if raw != (compact(value) + '\n').encode('ascii'):
    raise SystemExit('multiplication projection must be compact ordered ASCII JSON with one final LF')


nodes = []
interned = {}
keys = {}


def intern(x, fuel):
    if fuel <= 0:
        raise SystemExit('JSON encoding depth exceeds the checked budget')
    if isinstance(x, str) and any(ord(c) not in (8, 9, 10, 12, 13) and not 32 <= ord(c) < 127 for c in x):
        raise SystemExit('unsupported non-ASCII or control character in JSON encoding')
    key = (compact(x), fuel)
    if key in interned:
        return interned[key]
    children = []
    if isinstance(x, dict):
        for field, child in x.items():
            if any(ord(c) not in (8, 9, 10, 12, 13) and not 32 <= ord(c) < 127 for c in field):
                raise SystemExit('unsupported non-ASCII or control character in JSON key')
            keys.setdefault(field, len(keys))
            children.append(intern(child, fuel - 1))
    elif isinstance(x, list):
        children = [intern(child, fuel - 1) for child in x]
    number = len(nodes)
    interned[key] = number
    nodes.append((x, fuel, children))
    return number


root = intern(value, 64)
lines = ['import MulRetained', 'import StringBytes', '',
    'namespace PastaBridge.MulJsonTextDag', '',
    'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
    'set_option linter.unusedSimpArgs false', '',
    'theorem array_encoding (fuel : Nat) (values : List KernelJson.Value) :',
    '    JsonEncoding.valueText (fuel + 1) (.array values) =',
    '      (values.mapM (JsonEncoding.valueText fuel)).map',
    '        (fun pieces => "[" ++ String.intercalate "," pieces ++ "]") := by rfl', '',
    'theorem object_encoding (fuel : Nat) (fields : List (String × KernelJson.Value)) :',
    '    JsonEncoding.valueText (fuel + 1) (.object fields) =',
    '      (fields.mapM (fun (key, value) => do',
    '        let key ← JsonEncoding.stringText key',
    '        let value ← JsonEncoding.valueText fuel value',
    '        pure (key ++ ":" ++ value))).map',
    '        (fun pieces => "{" ++ String.intercalate "," pieces ++ "}") := by rfl', '']

for key, index in keys.items():
    lines += [f'theorem key_{index} : JsonEncoding.stringText {literal(key)} =',
        f'    .ok {literal(compact(key))} := by decide +kernel', '']

for index, (x, fuel, children) in enumerate(nodes):
    chunks = []
    if isinstance(x, dict):
        fields = ', '.join(f'({literal(key)}, value_{child})'
                           for key, child in zip(x, children))
        expression = f'.object [{fields}]'
        text_fields = ', '.join(f'({literal(compact(key))} ++ ":" ++ text_{child})'
                               for key, child in zip(x, children))
        text_expression = f'"{{" ++ String.intercalate "," [{text_fields}] ++ "}}"'
    elif isinstance(x, list):
        if len(children) > 64:
            for start in range(0, len(children), 32):
                chunk = children[start:start + 32]
                name = f'chunk_{index}_{len(chunks)}'
                chunks.append(name)
                lines += [f'def {name} : List KernelJson.Value := [' +
                    ', '.join(f'value_{child}' for child in chunk) + ']',
                    f'attribute [local irreducible] {name}',
                    f'def texts_{name} : List String := [' +
                    ', '.join(f'text_{child}' for child in chunk) + ']',
                    f'attribute [local irreducible] texts_{name}',
                    f'theorem mapped_{name} : {name}.mapM (JsonEncoding.valueText {fuel - 1}) =',
                    f'    .ok texts_{name} := by',
                    f'  unfold {name} texts_{name}',
                    '  simp only [' + ', '.join(['List.mapM_cons', 'List.mapM_nil',
                        'Except.bind', 'Except.pure', 'Pure.pure', 'Bind.bind'] +
                        [f'encoded_{child}' for child in dict.fromkeys(chunk)]) + ']', '',
                    f'run_cmd IO.FS.writeFile "mul-json-text-dag-progress.txt" "checked {name}"', '']
            expression = '.array (' + ' ++ '.join(chunks) + ')'
            text_list = '(' + ' ++ '.join('texts_' + name for name in chunks) + ')'
        else:
            expression = '.array [' + ', '.join(f'value_{child}' for child in children) + ']'
            text_list = '[' + ', '.join(f'text_{child}' for child in children) + ']'
        text_expression = f'"[" ++ String.intercalate "," {text_list} ++ "]"'
    elif x is None:
        expression = '.null'
        text_expression = literal(compact(x))
    elif isinstance(x, bool):
        expression = '.bool ' + str(x).lower()
        text_expression = literal(compact(x))
    elif isinstance(x, int):
        expression = f'.number ({x})'
        text_expression = literal(compact(x))
    elif isinstance(x, str):
        expression = '.string ' + literal(x)
        text_expression = literal(compact(x))
    else:
        raise ValueError(type(x))
    lines += [f'def value_{index} : KernelJson.Value := {expression}',
        f'attribute [local irreducible] value_{index}',
        f'def text_{index} : String := {text_expression}',
        f'attribute [local irreducible] text_{index}', '',
        f'theorem encoded_{index} : JsonEncoding.valueText {fuel} value_{index} =',
        f'    .ok text_{index} := by', f'  unfold value_{index} text_{index}']
    if isinstance(x, (dict, list)):
        rules = ['object_encoding' if isinstance(x, dict) else 'array_encoding',
            'List.mapM_cons', 'List.mapM_nil', 'Except.bind', 'Except.pure',
            'Except.map', 'Bind.bind', 'Pure.pure']
        if isinstance(x, dict):
            rules += [f'key_{keys[key]}' for key in x]
        if chunks:
            rules += ['List.mapM_append'] + [f'mapped_{name}' for name in chunks]
        else:
            rules += [f'encoded_{child}' for child in dict.fromkeys(children)]
        lines += ['  simp only [' + ', '.join(rules) + ']']
        lines += ['  all_goals rfl', '']
    else:
        lines += ['  decide +kernel', '']
    if index % 16 == 0:
        lines += [f'run_cmd IO.FS.writeFile "mul-json-text-dag-progress.txt" "checked node {index}"', '']

chunk_value_defs = [f'chunk_{index}_{n}'
    for index, (x, _fuel, children) in enumerate(nodes)
    if isinstance(x, list) and len(children) > 64
    for n in range((len(children) + 31) // 32)]
unfold_order = ['retainedMultiplicationArtifactValue']
for index in reversed(range(len(nodes))):
    unfold_order.append('value_' + str(index))
    unfold_order.extend(name for name in chunk_value_defs if name.startswith(f'chunk_{index}_'))
lines += [f'theorem retained_value_readback : retainedMultiplicationArtifactValue = value_{root} := by',
    '  delta ' + ' '.join(unfold_order),
    '  rfl', '',
    'attribute [local irreducible] retainedMultiplicationArtifactBytes', '',
    'theorem retained_bytes_readback :',
    f'    StringBytes.bytes (text_{root} ++ "\\n") = retainedMultiplicationArtifactBytes := by',
    f'  have checked : (StringBytes.bytes (text_{root} ++ "\\n") ==',
    '      retainedMultiplicationArtifactBytes) = true := by',
    '    simp only [↓StringBytes.append, ↓StringBytes.intercalate,',
    '      List.map_cons, List.map_nil, List.map_append,',
    '      ↓List.append_assoc,',
    '      List.intercalate_cons_cons, List.intercalate_singleton,']
lines += ['      ' + ', '.join('↓text_' + str(index) for index in range(len(nodes))) + ',']
chunk_text_defs = [f'texts_chunk_{index}_{n}'
    for index, (x, _fuel, children) in enumerate(nodes)
    if isinstance(x, list) and len(children) > 64
    for n in range((len(children) + 31) // 32)]
lines += ['      ' + ', '.join(chunk_text_defs) + ']',
    '    all_goals decide +kernel',
    '  exact eq_of_beq checked', '',
    'theorem retained_encoding :',
    '    (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map StringBytes.bytes =',
    '      .ok retainedMultiplicationArtifactBytes := by',
    f'  rw [JsonEncoding.documentText, retained_value_readback, encoded_{root}]',
    '  change Except.ok _ = Except.ok _',
    '  exact congrArg Except.ok retained_bytes_readback', '',
    '#print axioms retained_value_readback', '#print axioms retained_bytes_readback',
    '#print axioms retained_encoding', '', 'end PastaBridge.MulJsonTextDag', '']
lines = [line for line in lines if not line.startswith('run_cmd IO.FS.writeFile')]
boundary = next(i for i, line in enumerate(lines) if line.startswith('theorem retained_value_readback'))
header = '-- Candidate generated mechanically from generated/mul-check.json; checked readback follows.\n'
base = lines[:boundary] + [f'#print axioms encoded_{root}', '', 'end PastaBridge.MulJsonTextDag', '']
final = ['import MulJsonTextDagBase', '', 'namespace PastaBridge.MulJsonTextDag', '',
         'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0',
         'set_option pp.maxSteps 1000', 'set_option pp.deepTerms false', ''] + lines[boundary:]
targets = {'MulJsonTextDagBase.lean': base, 'MulJsonTextDagFinal.lean': final}
for name, source_lines in targets.items():
    target = ROOT / 'bridge' / name
    data = (header + '\n'.join(source_lines)).encode('utf-8')
    if args.check:
        if not target.is_file() or target.read_bytes() != data:
            raise SystemExit(f'stale multiplication JSON certificate candidate {name}; regenerate it')
    else:
        target.write_bytes(data)
if args.check:
    print(f'PASS: {len(nodes)} interned JSON nodes match the retained projection')
else:
    print(f'Wrote {len(nodes)} interned JSON nodes as candidates for kernel checking')
