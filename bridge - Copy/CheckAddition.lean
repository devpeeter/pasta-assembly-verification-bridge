import Retained

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PastaBridge

theorem retained_artifact_chars_readback :
    String.ofList retainedArtifactChars = retainedCharonArtifact := by
  rfl

theorem addition_template_matches_retained_assembly :
    renderArtifact retainedCharonArtifact "add" = .ok retainedAdditionAssembly := by
  rw [← retained_artifact_chars_readback]
  unfold renderArtifact KernelJson.parse
  simp only [String.toList_ofList]
  decide +kernel

theorem addition_program_serializes_to_retained_assembly :
    serializeAdditionProgram retainedAdditionProgram = .ok retainedAdditionAssembly := by
  decide +kernel

theorem addition_artifact_matches_retained_program :
    renderArtifact retainedCharonArtifact "add" =
      serializeAdditionProgram retainedAdditionProgram := by
  rw [addition_template_matches_retained_assembly,
    addition_program_serializes_to_retained_assembly]

theorem addition_operand_metadata_matches :
    operandModesFromArtifact retainedCharonArtifact "add" =
      .ok (List.ofFn additionExpectedOperandMode) := by
  rw [← retained_artifact_chars_readback]
  unfold operandModesFromArtifact KernelJson.parse
  simp only [String.toList_ofList]
  decide +kernel

#print axioms retained_artifact_chars_readback
#print axioms addition_template_matches_retained_assembly
#print axioms addition_program_serializes_to_retained_assembly
#print axioms addition_artifact_matches_retained_program
#print axioms addition_operand_metadata_matches

end PastaBridge
