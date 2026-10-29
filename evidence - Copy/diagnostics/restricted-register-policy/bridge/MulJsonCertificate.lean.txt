import MulJsonTextDagFinal

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PastaBridge

theorem multiplication_artifact_chars_readback :
    String.ofList retainedMultiplicationArtifactChars = retainedMultiplicationCharonArtifact := by
  exact String.ofList_toList

/-- Exact encoder readback checks the candidate JSON value against retained bytes. -/
theorem multiplication_value_encodes_retained_artifact :
    (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map StringBytes.bytes =
      .ok retainedMultiplicationArtifactBytes := by
  exact MulJsonTextDag.retained_encoding

#print axioms multiplication_artifact_chars_readback
#print axioms multiplication_value_encodes_retained_artifact

end PastaBridge
