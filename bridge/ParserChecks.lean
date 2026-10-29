import Kraken.AArch64.Parser

/- Synthetic parser boundary checks; no Pasta instruction list is maintained here. -/
namespace PastaBridge.ParserChecks

def reg (width : Width) (name : XReg) : RegOrZr width := .low (.reg name) width

def shiftProgram (shift : ShiftType) (amount : Nat) : Program :=
  [.instr ⟨.W64, .ORR_s (reg .W64 .X0) .XZR
    { reg := reg .W64 .X1, amount := Int64.ofInt (Int.ofNat amount), shift }⟩]

def matchesProgram (text : String) (expected : Program) : Bool :=
  match Kraken.AArch64.Parser.parse text with
  | .ok actual => actual == expected
  | .error _ => false

def rejects (text : String) : Bool :=
  match Kraken.AArch64.Parser.parse text with
  | .error _ => true
  | .ok _ => false

def positive : List (String × Program) :=
  ([0, 2, 62, 63].flatMap fun amount =>
    [(s!"lsl x0, x1, #{amount}", shiftProgram .LSL amount),
     (s!"lsr x0, x1, #{amount}", shiftProgram .LSR amount)]) ++
  [ ("lsl x0, x1, x2", [.instr ⟨.W64, .LSLV (reg .W64 .X0) (reg .W64 .X1) (reg .W64 .X2)⟩]),
    ("lsr x0, x1, x2", [.instr ⟨.W64, .LSRV (reg .W64 .X0) (reg .W64 .X1) (reg .W64 .X2)⟩]),
    ("lsl w0, w1, w2", [.instr ⟨.W32, .LSLV (reg .W32 .X0) (reg .W32 .X1) (reg .W32 .X2)⟩]),
    ("lsr w0, w1, w2", [.instr ⟨.W32, .LSRV (reg .W32 .X0) (reg .W32 .X1) (reg .W32 .X2)⟩]),
    ("subs xzr, x1, #1", [.instr ⟨.W64, .SUBS_e .XZR (.low (.reg .X1) .W64)
       (.imm { imm := 1, shift := .S0 })⟩]),
    ("subs xzr, x1, x2", [.instr ⟨.W64, .SUBS_s .XZR (reg .W64 .X1)
       { reg := reg .W64 .X2, amount := 0, shift := .LSL }⟩]),
    ("mov x0, #0x4000000000000000", [.instr ⟨.W64, .MOVZ (reg .W64 .X0) 0x4000 .LSL48⟩]) ]

def negative : List String :=
  [ "lsl x0, x1, #64", "lsr x0, x1, #64",
    "lsl x0, x1, #-1", "lsr x0, x1, #-1",
    "lsl x0, x1, #184467440737095516160000000000000000000000",
    "lsr x0, x1, #184467440737095516160000000000000000000000",
    "lsl x0, x1, #", "lsr x0, x1, #", "lsl x0, x1, 2",
    "lsl x0, x1, ##2", "lsl x0, x1, #label", "lsl x0, x1, #0x3f",
    "lsr x0, x1, #0b10", "lsl x0, x1, #2, x3", "lsr x0, x1, #2 garbage",
    "lsl w0, w1, #2", "lsr w0, w1, #2", "lsl x0, w1, #2",
    "lsl sp, x1, #2", "lsr x0, sp, #2", "lsl x0, x1, x2, x3",
    "subs sp, x1, #1", "subs x0, xzr, #1", "subs xzr, x1, #1, x2" ]

end PastaBridge.ParserChecks

def main : IO UInt32 := do
  let mut failures := 0
  for (text, expected) in PastaBridge.ParserChecks.positive do
    unless PastaBridge.ParserChecks.matchesProgram text expected do
      IO.eprintln s!"FAIL typed parser result: {text}"
      failures := failures + 1
  for text in PastaBridge.ParserChecks.negative do
    unless PastaBridge.ParserChecks.rejects text do
      IO.eprintln s!"FAIL unsupported parser form accepted: {text}"
      failures := failures + 1
  if failures != 0 then return 1
  IO.println s!"PASS: {PastaBridge.ParserChecks.positive.length} exact typed parser results; {PastaBridge.ParserChecks.negative.length} rejected forms"
  return 0
