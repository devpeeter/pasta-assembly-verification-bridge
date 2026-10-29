import Kraken.AArch64.Parser
import KernelJson
import Lean

open Lean Elab Term

deriving instance DecidableEq for Except

namespace PastaBridge

elab "retainedText(" path:str ")" : term => do
  return mkStrLit (← IO.FS.readFile path.getString)

elab "retainedChars(" path:str ")" : term => do
  return Lean.toExpr ((← IO.FS.readFile path.getString).toList)

elab "retainedProgram(" path:str ")" : term => do
  let bytes ← IO.FS.readFile path.getString
  match Kraken.AArch64.Parser.parse bytes with
  | .ok program => return Lean.toExpr program
  | .error reason => throwError reason

/-- Stable canonical order: retain the old prefix and append the additional
generic register x19. The target routines use only the unchanged prefix. -/
def allowedRegisters : Array String :=
  (((List.range 31).filter (fun n => n != 19 && n != 29)) ++ [19]).toArray.map (fun n => s!"x{n}")

def renderPiece (piece : KernelJson.Value) : Except String String := do
  match piece with
  | .object [_] => pure ()
  | _ => throw "invalid template piece"
  if let .ok text := (piece.field "Text").bind KernelJson.Value.text then return text
  let placeholder ← piece.field "Placeholder"
  match ← placeholder.field "modifier" with
  | .null => pure ()
  | _ => throw "unsupported placeholder modifier"
  let index ← (← placeholder.field "operand_id").nat
  match allowedRegisters[index]? with
  | some reg => return reg
  | none => throw "operand outside the supported register allocation"

def renderArtifact (artifact : String) (routine : String) : Except String String := do
  let json ← KernelJson.parse artifact
  if (← (← json.field "schema_version").nat) != 1 then
    throw "unsupported artifact schema"
  let block ← (← json.field "routines").field routine
  if (← (← block.field "kind").text) != "Asm" then
    throw "only asm! is supported"
  let pieces ← (← block.field "template").items
  let strings ← pieces.mapM renderPiece
  return String.join strings

def programFromArtifact (artifact routine : String) : Except String Program := do
  Kraken.AArch64.Parser.parse (← renderArtifact artifact routine)

def registerName : XReg → String
  | .X0 => "x0" | .X1 => "x1" | .X2 => "x2" | .X3 => "x3"
  | .X4 => "x4" | .X5 => "x5" | .X6 => "x6" | .X7 => "x7"
  | .X8 => "x8" | .X9 => "x9" | .X10 => "x10" | .X11 => "x11"
  | .X12 => "x12" | .X13 => "x13" | .X14 => "x14" | .X15 => "x15"
  | .X16 => "x16" | .X17 => "x17" | .X18 => "x18" | .X19 => "x19"
  | .X20 => "x20" | .X21 => "x21" | .X22 => "x22" | .X23 => "x23"
  | .X24 => "x24" | .X25 => "x25" | .X26 => "x26" | .X27 => "x27"
  | .X28 => "x28" | .X29 => "x29" | .X30 => "x30"

def register64 : RegOrZr .W64 → Except String String
  | .low .XZR _ => .ok "xzr"
  | .low (.reg r) _ =>
    if r == .X29 then .error "reserved register"
    else .ok (registerName r)

def threeRegisters (mnemonic : String) (d a b : RegOrZr .W64) : Except String String := do
  return mnemonic ++ " " ++ (← register64 d) ++ ", " ++ (← register64 a) ++ ", " ++ (← register64 b)

def serializeAdditionOperation : Operation .W64 → Except String String
  | .ADDS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported shifted operand"
    threeRegisters "adds" d a b.reg
  | .ADCS d a b => threeRegisters "adcs" d a b
  | .ADC d a b => threeRegisters "adc" d a b
  | .SUBS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported shifted operand"
    threeRegisters "subs" d a b.reg
  | .SBCS d a b => threeRegisters "sbcs" d a b
  | .CSEL d a b .CS => do return (← threeRegisters "csel" d a b) ++ ", cs"
  | _ => .error "unsupported addition instruction"

def serializeAdditionProgram (program : Program) : Except String String := do
  let lines ← program.mapM fun directive => do
    match directive with
    | .instr ⟨.W64, operation⟩ => serializeAdditionOperation operation
    | _ => throw "unsupported directive or instruction width"
  return String.intercalate "\n" lines

def canonicalAssembly (assembly : String) : String :=
  String.intercalate "\n" ((assembly.splitOn "\n").map (fun line => line.trimAscii.toString)
    |>.filter (fun line => !line.isEmpty))

inductive OperandMode where
  | input
  | output
  | inputOutput
  deriving DecidableEq, Repr

def operandMode (operand : KernelJson.Value) : Except String OperandMode := do
  let (kind, payload) ← match operand with
    | .object [field] => pure field
    | _ => throw "invalid operand metadata"
  let fields ← match payload with
    | .object fields => pure fields
    | _ => throw "invalid operand payload"
  match ← payload.field "reg" with
  | .object [("Class", .string "reg")] => pure ()
  | _ => throw "unsupported register operand"
  if kind == "In" then
    if fields.length != 1 then throw "unexpected input metadata"
    return .input
  if fields.length != 2 then throw "unexpected output metadata"
  match ← payload.field "late" with
  | .bool false => pure ()
  | _ => throw "late output unsupported"
  if kind == "Out" then return .output
  if kind == "InOut" then return .inputOutput
  throw "unsupported operand kind"

def checkOptions (options : KernelJson.Value) : Except String Unit := do
  let fields ← match options with
    | .object fields => pure fields
    | _ => throw "invalid options"
  if fields.length != 8 then throw "unsupported assembly options"
  let expected : List (String × Bool) := [
    ("pure", true), ("nomem", true), ("nostack", true), ("readonly", false),
    ("preserves_flags", false), ("noreturn", false), ("att_syntax", false), ("may_unwind", false)]
  for (name, flag) in expected do
    match ← options.field name with
    | .bool actual => if actual != flag then throw "unsupported assembly option"
    | _ => throw "option must be a boolean"

def operandModesFromArtifact (artifact routine : String) : Except String (List OperandMode) := do
  let json ← KernelJson.parse artifact
  if (← (← json.field "schema_version").nat) != 1 then throw "unsupported artifact schema"
  let block ← (← json.field "routines").field routine
  if (← (← block.field "kind").text) != "Asm" then throw "unsupported assembly kind"
  checkOptions (← block.field "options")
  (← (← block.field "operands").items).mapM operandMode

def additionExpectedOperandMode (index : Fin 15) : OperandMode :=
  if index.val < 4 then .inputOutput else if index.val < 11 then .input else .output

end PastaBridge
