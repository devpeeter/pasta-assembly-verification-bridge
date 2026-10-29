import MulJsonCertificate
import MulBindingArtifact

namespace PastaBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem multiplication_canonical_binding_allowed :
    ∀ i, KrakenBinding.Allowed (MulMachine.canonicalBinding i) := by
  intro i
  unfold MulMachine.canonicalBinding MultiplicationArtifact.canonicalBinding KrakenBinding.Allowed
  split <;> intro impossible <;> cases impossible

/-- The universally checked template renders to the actual parsed native program. -/
theorem multiplication_artifact_matches_retained_program :
    MultiplicationArtifact.renderValue MultiplicationArtifact.canonicalBinding
      retainedMultiplicationArtifactValue =
      MultiplicationArtifact.serializeProgram retainedMultiplicationProgram := by
  have checked := MulBindingArtifact.bound_program_matches_template
    MulMachine.canonicalBinding multiplication_canonical_binding_allowed
  rw [MulMachine.canonical_identity] at checked
  exact checked

/-- Exact retained JSON bytes, native program correspondence, and operand modes. -/
theorem multiplication_retained_representation_certificate :
    String.ofList retainedMultiplicationArtifactChars = retainedMultiplicationCharonArtifact ∧
    (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map StringBytes.bytes =
      .ok retainedMultiplicationArtifactBytes ∧
    MultiplicationArtifact.renderValue MultiplicationArtifact.canonicalBinding
      retainedMultiplicationArtifactValue =
      MultiplicationArtifact.serializeProgram retainedMultiplicationProgram ∧
    MultiplicationArtifact.operandModes retainedMultiplicationArtifactValue =
      .ok (List.ofFn MultiplicationArtifact.expectedOperandMode) :=
  ⟨multiplication_artifact_chars_readback, multiplication_value_encodes_retained_artifact,
    multiplication_artifact_matches_retained_program, multiplication_operand_metadata_matches⟩

#print axioms multiplication_canonical_binding_allowed
#print axioms multiplication_artifact_matches_retained_program
#print axioms multiplication_retained_representation_certificate

end PastaBridge
