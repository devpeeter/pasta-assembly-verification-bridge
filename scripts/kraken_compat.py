"""Prepare and verify retained overlays of immutable Kraken sources.

The selected upstream Kraken and Batteries independently define List.allSome.
Rename only Kraken's helper and its single call; retain its exact implementation.
The separate parser patch recognizes bounded 64-bit immediate LSL/LSR aliases
using existing ORR_s/XZR/shift nodes. No instruction semantic body is changed.
Another parser-only guard permits XZR destinations in the existing immediate
flag-setting arithmetic branch, without treating XZR sources as SP.
"""
from __future__ import annotations

import difflib
import hashlib
import json
from pathlib import Path

from integrity import check_kraken_snapshot

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent / "work"
RELATIVE = "Kraken/Mem.lean"
PARSER_RELATIVE = "Kraken/AArch64/Parser.lean"

SHIFT_HELPER = '''/-- Bounded 64-bit immediate aliases use the existing shifted logical operand. -/
def parseShiftAlias (shift : ShiftType)
    (mkVariable : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) :
    Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  parseComma
  skipHWs
  if (← peek!) == '#' then
    let dst ← checkWidth .W64 w dstW.reg
    let src ← checkWidth .W64 w src
    let _ ← pchar '#'
    let amount ← parseDec
    if amount < 0 || amount >= 64 then
      fail "64-bit immediate logical shift must be in [0, 63]"
    pure ⟨.W64, .ORR_s dst .XZR
      { reg := src, amount := Int64.ofInt amount, shift := shift }⟩
  else
    let amountReg ← parseRegOrZr w
    pure ⟨w, mkVariable dstW.reg src amountReg⟩
'''


def parser_alias_source(before: bytes) -> bytes:
    """Apply only the reviewed helper insertion and two dispatch substitutions."""
    if b"\r" in before:
        raise ValueError("Kraken compatibility inputs must use exact LF Git-blob bytes")
    source = before
    anchor = b"\ndef parseFourRegs\n"
    if source.count(anchor) != 1 or b"parseShiftAlias" in source:
        raise ValueError("unexpected Kraken parser insertion pattern")
    source = source.replace(anchor, b"\n" + SHIFT_HELPER.encode() + anchor)
    for mnemonic, shift, operation in (("lsl", "LSL", "LSLV"), ("lsr", "LSR", "LSRV")):
        old = f'  | "{mnemonic}"   => parseThreeRegs .{operation} -- Alias of {operation}\n'.encode()
        new = f'  | "{mnemonic}"   => parseShiftAlias .{shift} .{operation}\n'.encode()
        if source.count(old) != 1:
            raise ValueError("unexpected Kraken immediate-shift dispatch pattern")
        source = source.replace(old, new)
    return source


def zero_destination_source(before: bytes) -> bytes:
    """Permit a zero destination in the existing immediate arithmetic branch."""
    if b"\r" in before:
        raise ValueError("Kraken compatibility inputs must use exact LF Git-blob bytes")
    start = before.index(b"def parseArithFlags ")
    end = before.index(b"def parseCompare", start)
    body = before[start:end]
    old = b"else if op1W.2.isXzr || op2.isXzr then"
    new = b"else if op2.isXzr then"
    if body.count(old) != 1:
        raise ValueError("unexpected Kraken zero-destination parser guard")
    return before[:start] + body.replace(old, new) + before[end:]


def expected_sources() -> tuple[dict[str, bytes], dict]:
    vendor = ROOT / "vendor/kraken"
    check_kraken_snapshot(vendor)
    manifest = json.loads((vendor / "UPSTREAM.json").read_text(encoding="utf-8"))
    sources = {name: (vendor / name).read_bytes() for name in manifest["files"]}
    before = sources[RELATIVE]
    if b"\r" in before:
        raise ValueError("Kraken compatibility inputs must use exact LF Git-blob bytes")
    if before.count(b"allSome") != 2 or b"krakenAllSome" in before:
        raise ValueError("unexpected Kraken helper definition or use; compatibility patch rejected")
    after = before.replace(b"allSome", b"krakenAllSome")
    patch = "".join(difflib.unified_diff(before.decode().splitlines(True), after.decode().splitlines(True),
                    fromfile="a/" + RELATIVE, tofile="b/" + RELATIVE)).encode()
    retained_patch = ROOT / "compatibility/kraken-list-name.patch"
    if retained_patch.read_bytes() != patch:
        raise ValueError("retained Kraken namespace patch is stale")
    pins = json.loads((ROOT / "pins.json").read_text(encoding="utf-8"))
    patch_hash = hashlib.sha256(patch).hexdigest()
    if pins["kraken"]["compatibility_patch_sha256"] != patch_hash:
        raise ValueError("Kraken compatibility patch differs from pins.json")
    sources[RELATIVE] = after
    parser_before = sources[PARSER_RELATIVE]
    parser_after = parser_alias_source(parser_before)
    parser_patch = "".join(difflib.unified_diff(
        parser_before.decode().splitlines(True), parser_after.decode().splitlines(True),
        fromfile="a/" + PARSER_RELATIVE, tofile="b/" + PARSER_RELATIVE)).encode()
    if (ROOT / "compatibility/kraken-immediate-shifts.patch").read_bytes() != parser_patch:
        raise ValueError("retained Kraken immediate-shift parser patch is stale")
    parser_patch_hash = hashlib.sha256(parser_patch).hexdigest()
    if pins["kraken"]["immediate_shift_patch_sha256"] != parser_patch_hash:
        raise ValueError("Kraken immediate-shift parser patch differs from pins.json")
    zero_after = zero_destination_source(parser_after)
    zero_patch = "".join(difflib.unified_diff(
        parser_after.decode().splitlines(True), zero_after.decode().splitlines(True),
        fromfile="a/" + PARSER_RELATIVE, tofile="b/" + PARSER_RELATIVE)).encode()
    if (ROOT / "compatibility/kraken-zero-destination.patch").read_bytes() != zero_patch:
        raise ValueError("retained Kraken zero-destination parser patch is stale")
    zero_patch_hash = hashlib.sha256(zero_patch).hexdigest()
    if pins["kraken"]["zero_destination_patch_sha256"] != zero_patch_hash:
        raise ValueError("Kraken zero-destination parser patch differs from pins.json")
    sources[PARSER_RELATIVE] = zero_after
    record = {"upstream_revision": pins["kraken"]["revision"],
              "patch": "compatibility/kraken-list-name.patch", "patch_sha256": patch_hash,
              "change": "List.allSome -> List.krakenAllSome, definition and one call only",
              "parser_patch": "compatibility/kraken-immediate-shifts.patch",
              "parser_patch_sha256": parser_patch_hash,
              "parser_change": "64-bit #decimal LSL/LSR aliases in [0,63] through existing ORR_s/XZR/shift semantics",
              "zero_destination_patch": "compatibility/kraken-zero-destination.patch",
              "zero_destination_patch_sha256": zero_patch_hash,
              "zero_destination_change": "parseArithFlags permits XZR destination through existing extended/immediate fallback",
              "files": {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()}}
    return sources, record


def prepare() -> Path:
    destination = (WORK / "kraken-compat").resolve()
    if not destination.is_relative_to(WORK.resolve()) or destination.name != "kraken-compat":
        raise ValueError("compatibility build directory escapes the intended workspace")
    if (destination / ".git").exists():
        raise ValueError("refusing to overwrite a Git checkout with a build overlay")
    sources, record = expected_sources()
    for relative, data in sources.items():
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_bytes() != data:
            target.write_bytes(data)
    extras = {p.relative_to(destination).as_posix() for p in destination.rglob("*.lean")
              if ".lake" not in p.relative_to(destination).parts} - set(sources)
    if extras:
        raise ValueError(f"unexpected source modules in compatibility overlay: {sorted(extras)}")
    (destination / "COMPATIBILITY.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    return destination


if __name__ == "__main__":
    print(prepare())
