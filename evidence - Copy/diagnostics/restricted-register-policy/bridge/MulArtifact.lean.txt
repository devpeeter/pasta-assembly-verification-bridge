import Artifact

open Lean Elab Term

namespace PastaBridge

set_option maxRecDepth 100000

deriving instance Lean.ToExpr for KernelJson.Value

namespace JsonEncoding

/-- The retained compact projection is ASCII JSON. Other characters are rejected. -/
def escapeChar (char : Char) : Except String (List Char) :=
  match char with
  | '"' => .ok ['\\', '"']
  | '\\' => .ok ['\\', '\\']
  | '\n' => .ok ['\\', 'n']
  | '\r' => .ok ['\\', 'r']
  | '\t' => .ok ['\\', 't']
  | char =>
    if char.toNat == 8 then .ok ['\\', 'b']
    else if char.toNat == 12 then .ok ['\\', 'f']
    else if 32 ≤ char.toNat && char.toNat < 127 then .ok [char]
    else .error "unsupported non-ASCII or control character in JSON encoding"

/-- Compact ASCII JSON text. The character encoder rejects unsupported escapes. -/
def stringText (value : String) : Except String String := do
  let pieces ← value.toList.mapM fun char => do
    return String.ofList (← escapeChar char)
  return "\"" ++ String.join pieces ++ "\""

/-- Total text encoder. It preserves object-field order and checks exact retained text. -/
def valueText : Nat → KernelJson.Value → Except String String
  | 0, _ => .error "JSON encoding depth exceeded"
  | _ + 1, .null => .ok "null"
  | _ + 1, .bool true => .ok "true"
  | _ + 1, .bool false => .ok "false"
  | _ + 1, .number value => .ok (toString value)
  | _ + 1, .string value => stringText value
  | fuel + 1, .array values => do
    let pieces ← values.mapM (valueText fuel)
    return "[" ++ String.intercalate "," pieces ++ "]"
  | fuel + 1, .object fields => do
    let pieces ← fields.mapM fun (key, value) => do
      let key ← stringText key
      let value ← valueText fuel value
      return key ++ ":" ++ value
    return "{" ++ String.intercalate "," pieces ++ "}"

/-- The retained compact JSON document includes one final newline. -/
def documentText (fuel : Nat) (value : KernelJson.Value) : Except String String :=
  (valueText fuel value).map (fun text => text ++ "\n")

end JsonEncoding

elab "retainedJsonValue(" path:str ")" : term => do
  let bytes ← IO.FS.readFile path.getString
  match KernelJson.parse bytes with
  | .ok value => return Lean.toExpr value
  | .error reason => throwError reason

/-- Direct file inclusion; the candidate bytes are later checked against the encoder. -/
elab "retainedByteList(" path:str ")" : term => do
  let bytes ← IO.FS.readBinFile path.getString
  return Lean.toExpr bytes.data.toList

namespace MultiplicationArtifact

abbrev Binding := Fin 21 → XReg

inductive Piece where
  | text (value : String)
  | operand (index : Fin 21)
  deriving Repr, DecidableEq, Lean.ToExpr

def block (value : KernelJson.Value) : Except String KernelJson.Value := do
  match value with
  | .object fields => if fields.length != 2 then throw "unexpected artifact fields"
  | _ => throw "artifact object required"
  if (← (← value.field "schema_version").nat) != 1 then throw "unsupported artifact schema"
  let routines ← value.field "routines"
  match routines with
  | .object [("mul", routine)] =>
    match routine with
    | .object fields => if fields.length != 4 then throw "unexpected routine fields"
    | _ => throw "routine object required"
    if (← (← routine.field "kind").text) != "Asm" then throw "only asm! is supported"
    return routine
  | _ => throw "exactly the multiplication routine is required"

def decodePiece (piece : KernelJson.Value) : Except String Piece := do
  match piece with
  | .object [("Text", .string text)] => return .text text
  | .object [("Placeholder", placeholder)] =>
    match placeholder with
    | .object fields => if fields.length != 2 then throw "unsupported placeholder metadata"
    | _ => throw "placeholder object required"
    match ← placeholder.field "modifier" with
    | .null => pure ()
    | _ => throw "unsupported placeholder modifier"
    let index ← (← placeholder.field "operand_id").nat
    if bound : index < 21 then return .operand ⟨index, bound⟩
    else throw "operand outside retained multiplication domain"
  | _ => throw "unsupported template piece"

def pieces (value : KernelJson.Value) : Except String (List Piece) := do
  (← (← (← block value).field "template").items).mapM decodePiece

def operandModes (value : KernelJson.Value) : Except String (List OperandMode) := do
  let routine ← block value
  checkOptions (← routine.field "options")
  (← (← routine.field "operands").items).mapM operandMode

def expectedOperandMode (index : Fin 21) : OperandMode :=
  if index.val < 11 then .input else .output

def renderPieces (binding : Binding) (template : List Piece) : String :=
  String.join (template.map fun
    | .text text => text
    | .operand index => registerName (binding index))

def renderValue (binding : Binding) (value : KernelJson.Value) : Except String String :=
  (pieces value).map (renderPieces binding)

def canonicalBinding (index : Fin 21) : XReg :=
  match index.val with
  | 0 => .X0 | 1 => .X1 | 2 => .X2 | 3 => .X3 | 4 => .X4 | 5 => .X5
  | 6 => .X6 | 7 => .X7 | 8 => .X8 | 9 => .X9 | 10 => .X10 | 11 => .X11
  | 12 => .X12 | 13 => .X13 | 14 => .X14 | 15 => .X15 | 16 => .X16
  | 17 => .X17 | 18 => .X18 | 19 => .X20 | _ => .X21

def registerSp64 : RegOrSp .W64 → Except String String
  | .low (.reg register) _ => register64 (.low (.reg register) .W64)
  | .low .SP _ => .error "stack-pointer operand unsupported"

/-- A rejecting serializer for precisely the multiplication forms retained here. -/
def serializeOperation : Operation .W64 → Except String String
  | .MADD d a b (.low .XZR _) => threeRegisters "mul" d a b
  | .UMULH d a b => threeRegisters "umulh" d a b
  | .ADDS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported shifted operand"
    threeRegisters "adds" d a b.reg
  | .ADCS d a b => threeRegisters "adcs" d a b
  | .ADC d a b => threeRegisters "adc" d a b
  | .SUBS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported shifted operand"
    threeRegisters "subs" d a b.reg
  | .SUBS_e d a (.imm immediate) => do
    if immediate.imm != .int64 1 || immediate.shift != .S0 then
      throw "unsupported subtraction immediate"
    return "subs " ++ (← register64 d) ++ ", " ++ (← registerSp64 a) ++ ", #1"
  | .SBCS d a b => threeRegisters "sbcs" d a b
  | .CSEL d a b .CC => do return (← threeRegisters "csel" d a b) ++ ", lo"
  | .ORR_s d (.low .XZR _) source => do
    let mnemonic ←
      if source.shift == .LSL && source.amount == 62 then pure "lsl"
      else if source.shift == .LSR && source.amount == 2 then pure "lsr"
      else throw "unsupported immediate shift alias"
    let amount := if source.shift == .LSL then "62" else "2"
    return mnemonic ++ " " ++ (← register64 d) ++ ", " ++ (← register64 source.reg) ++ ", #" ++ amount
  | .MOVZ d (.int64 immediate) .LSL48 => do
    if immediate != 0x4000 then throw "unsupported move immediate"
    return "mov " ++ (← register64 d) ++ ", #0x4000000000000000"
  | _ => .error "unsupported multiplication operation"

def serializeProgram (program : Program) : Except String String := do
  let lines ← program.mapM fun directive => do
    match directive with
    | .instr ⟨.W64, operation⟩ => serializeOperation operation
    | _ => throw "unsupported directive or instruction width"
  return String.intercalate "\n" lines

end MultiplicationArtifact
end PastaBridge
