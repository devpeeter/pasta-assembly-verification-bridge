import MulParametricBase

namespace PastaBridge.MulParametric

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open MulStep

section
attribute [local irreducible] MulSequenceFrame.sequence transition MulNat.read MulNat.update

theorem firstRound_model (ops : Arithmetic) (state : State) :
    accumulator (sequence ops firstRound state) =
      round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state) := by
  simp (ground := true) only [↓accumulator, ↓lhs, ↓modulus, ↓inv,
    firstRound, MulProgramData.retainedInstructions,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    ↓words_sequence_cons, ↓words_sequence_nil, ↓words_transition, ↓carry_transition,
    ↓value, ↓carry, ↓destination, ↓read_operand, ↓read_zero, ↓reduceIte, round]
  all_goals rfl

theorem secondRound_model (ops : Arithmetic) (state : State) :
    accumulator (sequence ops secondRound state) =
      round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state) := by
  simp (ground := true) only [↓accumulator, ↓lhs, ↓modulus, ↓inv,
    secondRound, MulProgramData.retainedInstructions,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    ↓words_sequence_cons, ↓words_sequence_nil, ↓words_transition, ↓carry_transition,
    ↓value, ↓carry, ↓destination, ↓read_operand, ↓read_zero, ↓reduceIte, round]
  all_goals rfl

theorem thirdRound_model (ops : Arithmetic) (state : State) :
    accumulator (sequence ops thirdRound state) =
      round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state) := by
  simp (ground := true) only [↓accumulator, ↓lhs, ↓modulus, ↓inv,
    thirdRound, MulProgramData.retainedInstructions,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    ↓words_sequence_cons, ↓words_sequence_nil, ↓words_transition, ↓carry_transition,
    ↓value, ↓carry, ↓destination, ↓read_operand, ↓read_zero, ↓reduceIte, round]
  all_goals rfl

end

#print axioms firstRound_model
#print axioms secondRound_model
#print axioms thirdRound_model

end PastaBridge.MulParametric
