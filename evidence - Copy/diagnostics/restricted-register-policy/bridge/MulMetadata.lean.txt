import MulRetained

open Lean Elab Term

namespace PastaBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

elab "quotedMultiplicationPieces" : term => do
  match MultiplicationArtifact.pieces retainedMultiplicationArtifactValue with
  | .ok pieces => return Lean.toExpr pieces
  | .error reason => throwError reason

/-- Candidate pieces are derived from the retained value, then checked below. -/
def retainedMultiplicationPieces : List MultiplicationArtifact.Piece := quotedMultiplicationPieces

theorem multiplication_pieces_match_retained_value :
    MultiplicationArtifact.pieces retainedMultiplicationArtifactValue =
      .ok retainedMultiplicationPieces := by rfl

theorem multiplication_operand_metadata_matches :
    MultiplicationArtifact.operandModes retainedMultiplicationArtifactValue =
      .ok (List.ofFn MultiplicationArtifact.expectedOperandMode) := by decide +kernel

#print axioms multiplication_pieces_match_retained_value
#print axioms multiplication_operand_metadata_matches

end PastaBridge
