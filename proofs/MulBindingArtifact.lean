import MulMetadata
import MulProgramData
import MulPieceFormatting
import Init.Data.String.Lemmas

namespace PastaBridge.MulBindingArtifact

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option pp.maxSteps 1000
set_option pp.deepTerms false

theorem register64_allowed (r : XReg) (allowed : KrakenBinding.Allowed r) :
    register64 (.low (.reg r) .W64) = .ok (registerName r) := by
  cases r <;> simp_all [KrakenBinding.Allowed, register64] <;> decide +kernel

/-- Closed structural comparison derived from the retained template and actual AST. -/
theorem normalized_retained_pieces :
    MulPieceFormatting.normalize retainedMultiplicationPieces =
      MulPieceFormatting.normalize
        (MulPieceFormatting.programPieces MulProgramData.retainedInstructions) := by
  decide +kernel

theorem bound_program_matches_template (binding : MulMachine.Binding)
    (allowed : ∀ i, KrakenBinding.Allowed (binding i)) :
    MultiplicationArtifact.renderValue binding retainedMultiplicationArtifactValue =
      MultiplicationArtifact.serializeProgram (MulMachine.boundProgram binding) := by
  rw [MultiplicationArtifact.renderValue, multiplication_pieces_match_retained_value]
  unfold MulMachine.boundProgram
  rw [MulProgramData.retained_instructions_readback]
  rw [MulFormatting.serialize_program binding allowed _
    (List.all_eq_true.mp MulFormatting.retained_supported)]
  change Except.ok (MultiplicationArtifact.renderPieces binding retainedMultiplicationPieces) = _
  apply congrArg Except.ok
  have checked := congrArg (MultiplicationArtifact.renderPieces binding) normalized_retained_pieces
  rw [MulPieceFormatting.render_normalize, MulPieceFormatting.render_normalize] at checked
  exact checked.trans (MulPieceFormatting.render_program binding _)

def modeWrites (mode : OperandMode) : Bool := mode != .input

theorem written_matches_checked_modes (i : Fin 21) :
    MulStep.written i = modeWrites (MultiplicationArtifact.expectedOperandMode i) := by
  simp only [MulStep.written, modeWrites, MultiplicationArtifact.expectedOperandMode]
  split <;> simp_all <;> omega

theorem retained_written_mask :
    (MultiplicationArtifact.operandModes retainedMultiplicationArtifactValue).map
      (List.map modeWrites) = .ok (List.ofFn MulStep.written) := by
  rw [multiplication_operand_metadata_matches]
  simp only [Except.map, List.map_ofFn]
  congr 1

#print axioms bound_program_matches_template
#print axioms normalized_retained_pieces
#print axioms written_matches_checked_modes
#print axioms retained_written_mask

end PastaBridge.MulBindingArtifact
