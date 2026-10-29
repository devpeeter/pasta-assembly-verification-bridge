import AdditionMachine
import Init.Data.String.Lemmas

open Lean Elab Term

namespace PastaBridge.BindingArtifact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive Piece where
  | text (value : String)
  | operand (index : Fin 15)
  deriving Repr, DecidableEq, Lean.ToExpr

def decodePiece (piece : KernelJson.Value) : Except String Piece := do
  match piece with
  | .object [_] => pure ()
  | _ => throw "invalid template piece"
  if let .ok text := (piece.field "Text").bind KernelJson.Value.text then
    return .text text
  let placeholder ← piece.field "Placeholder"
  match placeholder with
  | .object fields => if fields.length != 2 then throw "unsupported placeholder metadata"
  | _ => throw "invalid placeholder"
  match ← placeholder.field "modifier" with
  | .null => pure ()
  | _ => throw "unsupported placeholder modifier"
  let index ← (← placeholder.field "operand_id").nat
  if bound : index < 15 then return .operand ⟨index, bound⟩
  else throw "operand outside the retained addition domain"

def decodeArtifact (artifact routine : String) : Except String (List Piece) := do
  let json ← KernelJson.parse artifact
  if (← (← json.field "schema_version").nat) != 1 then
    throw "unsupported artifact schema"
  let block ← (← json.field "routines").field routine
  if (← (← block.field "kind").text) != "Asm" then
    throw "only asm! is supported"
  (← (← block.field "template").items).mapM decodePiece

elab "retainedAdditionPieces" : term => do
  match decodeArtifact retainedCharonArtifact "add" with
  | .ok pieces => return Lean.toExpr pieces
  | .error reason => throwError reason

/-- This literal is produced by decoding the retained artifact, never transcribed. -/
def retainedPieces : List Piece := retainedAdditionPieces

theorem retained_pieces_match_artifact :
    decodeArtifact retainedCharonArtifact "add" = .ok retainedPieces := by
  rw [← retained_artifact_chars_readback]
  unfold decodeArtifact KernelJson.parse
  simp only [String.toList_ofList]
  decide +kernel

def renderPieces (binding : AdditionMachine.Binding) (pieces : List Piece) : String :=
  String.join (pieces.map fun
    | .text text => text
    | .operand index => registerName (binding index))

def renderArtifactWithBinding (binding : AdditionMachine.Binding)
    (artifact routine : String) : Except String String :=
  (decodeArtifact artifact routine).map (renderPieces binding)

theorem register64_allowed (r : XReg) (allowed : KrakenBinding.Allowed r) :
    register64 (.low (.reg r) .W64) = .ok (registerName r) := by
  cases r <;> simp_all [KrakenBinding.Allowed, register64] <;> decide +kernel

theorem bound_program_matches_template (binding : AdditionMachine.Binding)
    (allowed : ∀ i, KrakenBinding.Allowed (binding i)) :
    renderArtifactWithBinding binding retainedCharonArtifact "add" =
      serializeAdditionProgram (AdditionMachine.boundProgram binding) := by
  rw [renderArtifactWithBinding, retained_pieces_match_artifact]
  have asInstantiated :
      serializeAdditionProgram (AdditionMachine.boundProgram binding) =
        (AdditionMachine.instantiatedProgram binding).bind serializeAdditionProgram := by
    rw [AdditionMachine.instantiation_certificate]
    rfl
  rw [asInstantiated]
  have registers (i : Fin 15) :
      register64 (.low (.reg (binding i)) .W64) = .ok (registerName (binding i)) :=
    register64_allowed _ (allowed i)
  have zeroRegister : register64 (.low .XZR .W64) = .ok "xzr" := rfl
  have shiftSelf : (ShiftType.LSL != ShiftType.LSL) = false := by decide +kernel
  have intSelf : ((0 : Int64) != (0 : Int64)) = false := by decide +kernel
  simp (instances := true) only [Except.map, Pure.pure, Bind.bind,
    AdditionMachine.instantiatedProgram, retainedAdditionProgram,
    AdditionMachine.instantiateDirective, AdditionMachine.instantiateOperation,
    AdditionMachine.renameRegister, AdditionMachine.canonicalOperand,
    List.mapM_cons, List.mapM_nil, Except.bind, Except.pure,
    serializeAdditionProgram, serializeAdditionOperation, threeRegisters,
    renderPieces, retainedPieces, List.map_cons, List.map_nil,
    registers, zeroRegister, shiftSelf, intSelf, Bool.or_false, Bool.false_eq_true, if_false]
  simp (ground := true) only [String.join, List.foldl_cons, List.foldl_nil,
    String.intercalate_cons_cons, String.intercalate_singleton,
    String.append_assoc, String.empty_append]
  congr 1

#print axioms retained_pieces_match_artifact
#print axioms bound_program_matches_template

end PastaBridge.BindingArtifact
