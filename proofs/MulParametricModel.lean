import MulParametricRounds

namespace PastaBridge.MulParametric

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open MulStep

theorem firstRound_r0 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 16 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).r0 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r0 (firstRound_model ops state)

theorem firstRound_r1 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 17 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).r1 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r1 (firstRound_model ops state)

theorem firstRound_r2 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 18 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).r2 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r2 (firstRound_model ops state)

theorem firstRound_r3 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 19 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).r3 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r3 (firstRound_model ops state)

theorem firstRound_r4 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 20 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).r4 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r4 (firstRound_model ops state)

theorem firstRound_q (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 11 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).q :=
  congrArg PastaCurves.AArch64.MulMontAcc.q (firstRound_model ops state)

theorem firstRound_t1 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 13 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).t1 :=
  congrArg PastaCurves.AArch64.MulMontAcc.t1 (firstRound_model ops state)

theorem firstRound_t3 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 15 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)).t3 :=
  congrArg PastaCurves.AArch64.MulMontAcc.t3 (firstRound_model ops state)

theorem secondRound_r0 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 16 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).r0 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r0 (secondRound_model ops state)

theorem secondRound_r1 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 17 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).r1 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r1 (secondRound_model ops state)

theorem secondRound_r2 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 18 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).r2 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r2 (secondRound_model ops state)

theorem secondRound_r3 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 19 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).r3 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r3 (secondRound_model ops state)

theorem secondRound_r4 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 20 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).r4 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r4 (secondRound_model ops state)

theorem secondRound_q (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 11 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).q :=
  congrArg PastaCurves.AArch64.MulMontAcc.q (secondRound_model ops state)

theorem secondRound_t1 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 13 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).t1 :=
  congrArg PastaCurves.AArch64.MulMontAcc.t1 (secondRound_model ops state)

theorem secondRound_t3 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 15 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)).t3 :=
  congrArg PastaCurves.AArch64.MulMontAcc.t3 (secondRound_model ops state)

theorem thirdRound_r0 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 16 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).r0 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r0 (thirdRound_model ops state)

theorem thirdRound_r1 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 17 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).r1 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r1 (thirdRound_model ops state)

theorem thirdRound_r2 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 18 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).r2 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r2 (thirdRound_model ops state)

theorem thirdRound_r3 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 19 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).r3 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r3 (thirdRound_model ops state)

theorem thirdRound_r4 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 20 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).r4 :=
  congrArg PastaCurves.AArch64.MulMontAcc.r4 (thirdRound_model ops state)

theorem thirdRound_q (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 11 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).q :=
  congrArg PastaCurves.AArch64.MulMontAcc.q (thirdRound_model ops state)

theorem thirdRound_t1 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 13 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).t1 :=
  congrArg PastaCurves.AArch64.MulMontAcc.t1 (thirdRound_model ops state)

theorem thirdRound_t3 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 15 =
      (round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)).t3 :=
  congrArg PastaCurves.AArch64.MulMontAcc.t3 (thirdRound_model ops state)

theorem initial_input_0 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 0 = state.words 0 :=
  sequence_readonly ops initial initial_valid state 0 (by decide +kernel)

theorem initial_input_1 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 1 = state.words 1 :=
  sequence_readonly ops initial initial_valid state 1 (by decide +kernel)

theorem initial_input_2 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 2 = state.words 2 :=
  sequence_readonly ops initial initial_valid state 2 (by decide +kernel)

theorem initial_input_3 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 3 = state.words 3 :=
  sequence_readonly ops initial initial_valid state 3 (by decide +kernel)

theorem initial_input_4 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 4 = state.words 4 :=
  sequence_readonly ops initial initial_valid state 4 (by decide +kernel)

theorem initial_input_5 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 5 = state.words 5 :=
  sequence_readonly ops initial initial_valid state 5 (by decide +kernel)

theorem initial_input_6 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 6 = state.words 6 :=
  sequence_readonly ops initial initial_valid state 6 (by decide +kernel)

theorem initial_input_7 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 7 = state.words 7 :=
  sequence_readonly ops initial initial_valid state 7 (by decide +kernel)

theorem initial_input_8 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 8 = state.words 8 :=
  sequence_readonly ops initial initial_valid state 8 (by decide +kernel)

theorem initial_input_9 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 9 = state.words 9 :=
  sequence_readonly ops initial initial_valid state 9 (by decide +kernel)

theorem initial_input_10 (ops : Arithmetic) (state : State) :
    (sequence ops initial state).words 10 = state.words 10 :=
  sequence_readonly ops initial initial_valid state 10 (by decide +kernel)

theorem firstRound_input_0 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 0 = state.words 0 :=
  sequence_readonly ops firstRound firstRound_valid state 0 (by decide +kernel)

theorem firstRound_input_1 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 1 = state.words 1 :=
  sequence_readonly ops firstRound firstRound_valid state 1 (by decide +kernel)

theorem firstRound_input_2 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 2 = state.words 2 :=
  sequence_readonly ops firstRound firstRound_valid state 2 (by decide +kernel)

theorem firstRound_input_3 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 3 = state.words 3 :=
  sequence_readonly ops firstRound firstRound_valid state 3 (by decide +kernel)

theorem firstRound_input_4 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 4 = state.words 4 :=
  sequence_readonly ops firstRound firstRound_valid state 4 (by decide +kernel)

theorem firstRound_input_5 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 5 = state.words 5 :=
  sequence_readonly ops firstRound firstRound_valid state 5 (by decide +kernel)

theorem firstRound_input_6 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 6 = state.words 6 :=
  sequence_readonly ops firstRound firstRound_valid state 6 (by decide +kernel)

theorem firstRound_input_7 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 7 = state.words 7 :=
  sequence_readonly ops firstRound firstRound_valid state 7 (by decide +kernel)

theorem firstRound_input_8 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 8 = state.words 8 :=
  sequence_readonly ops firstRound firstRound_valid state 8 (by decide +kernel)

theorem firstRound_input_9 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 9 = state.words 9 :=
  sequence_readonly ops firstRound firstRound_valid state 9 (by decide +kernel)

theorem firstRound_input_10 (ops : Arithmetic) (state : State) :
    (sequence ops firstRound state).words 10 = state.words 10 :=
  sequence_readonly ops firstRound firstRound_valid state 10 (by decide +kernel)

theorem secondRound_input_0 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 0 = state.words 0 :=
  sequence_readonly ops secondRound secondRound_valid state 0 (by decide +kernel)

theorem secondRound_input_1 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 1 = state.words 1 :=
  sequence_readonly ops secondRound secondRound_valid state 1 (by decide +kernel)

theorem secondRound_input_2 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 2 = state.words 2 :=
  sequence_readonly ops secondRound secondRound_valid state 2 (by decide +kernel)

theorem secondRound_input_3 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 3 = state.words 3 :=
  sequence_readonly ops secondRound secondRound_valid state 3 (by decide +kernel)

theorem secondRound_input_4 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 4 = state.words 4 :=
  sequence_readonly ops secondRound secondRound_valid state 4 (by decide +kernel)

theorem secondRound_input_5 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 5 = state.words 5 :=
  sequence_readonly ops secondRound secondRound_valid state 5 (by decide +kernel)

theorem secondRound_input_6 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 6 = state.words 6 :=
  sequence_readonly ops secondRound secondRound_valid state 6 (by decide +kernel)

theorem secondRound_input_7 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 7 = state.words 7 :=
  sequence_readonly ops secondRound secondRound_valid state 7 (by decide +kernel)

theorem secondRound_input_8 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 8 = state.words 8 :=
  sequence_readonly ops secondRound secondRound_valid state 8 (by decide +kernel)

theorem secondRound_input_9 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 9 = state.words 9 :=
  sequence_readonly ops secondRound secondRound_valid state 9 (by decide +kernel)

theorem secondRound_input_10 (ops : Arithmetic) (state : State) :
    (sequence ops secondRound state).words 10 = state.words 10 :=
  sequence_readonly ops secondRound secondRound_valid state 10 (by decide +kernel)

theorem thirdRound_input_0 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 0 = state.words 0 :=
  sequence_readonly ops thirdRound thirdRound_valid state 0 (by decide +kernel)

theorem thirdRound_input_1 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 1 = state.words 1 :=
  sequence_readonly ops thirdRound thirdRound_valid state 1 (by decide +kernel)

theorem thirdRound_input_2 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 2 = state.words 2 :=
  sequence_readonly ops thirdRound thirdRound_valid state 2 (by decide +kernel)

theorem thirdRound_input_3 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 3 = state.words 3 :=
  sequence_readonly ops thirdRound thirdRound_valid state 3 (by decide +kernel)

theorem thirdRound_input_4 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 4 = state.words 4 :=
  sequence_readonly ops thirdRound thirdRound_valid state 4 (by decide +kernel)

theorem thirdRound_input_5 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 5 = state.words 5 :=
  sequence_readonly ops thirdRound thirdRound_valid state 5 (by decide +kernel)

theorem thirdRound_input_6 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 6 = state.words 6 :=
  sequence_readonly ops thirdRound thirdRound_valid state 6 (by decide +kernel)

theorem thirdRound_input_7 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 7 = state.words 7 :=
  sequence_readonly ops thirdRound thirdRound_valid state 7 (by decide +kernel)

theorem thirdRound_input_8 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 8 = state.words 8 :=
  sequence_readonly ops thirdRound thirdRound_valid state 8 (by decide +kernel)

theorem thirdRound_input_9 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 9 = state.words 9 :=
  sequence_readonly ops thirdRound thirdRound_valid state 9 (by decide +kernel)

theorem thirdRound_input_10 (ops : Arithmetic) (state : State) :
    (sequence ops thirdRound state).words 10 = state.words 10 :=
  sequence_readonly ops thirdRound thirdRound_valid state 10 (by decide +kernel)

theorem epilogue_input_0 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 0 = state.words 0 :=
  sequence_readonly ops epilogue epilogue_valid state 0 (by decide +kernel)

theorem epilogue_input_1 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 1 = state.words 1 :=
  sequence_readonly ops epilogue epilogue_valid state 1 (by decide +kernel)

theorem epilogue_input_2 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 2 = state.words 2 :=
  sequence_readonly ops epilogue epilogue_valid state 2 (by decide +kernel)

theorem epilogue_input_3 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 3 = state.words 3 :=
  sequence_readonly ops epilogue epilogue_valid state 3 (by decide +kernel)

theorem epilogue_input_4 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 4 = state.words 4 :=
  sequence_readonly ops epilogue epilogue_valid state 4 (by decide +kernel)

theorem epilogue_input_5 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 5 = state.words 5 :=
  sequence_readonly ops epilogue epilogue_valid state 5 (by decide +kernel)

theorem epilogue_input_6 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 6 = state.words 6 :=
  sequence_readonly ops epilogue epilogue_valid state 6 (by decide +kernel)

theorem epilogue_input_7 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 7 = state.words 7 :=
  sequence_readonly ops epilogue epilogue_valid state 7 (by decide +kernel)

theorem epilogue_input_8 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 8 = state.words 8 :=
  sequence_readonly ops epilogue epilogue_valid state 8 (by decide +kernel)

theorem epilogue_input_9 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 9 = state.words 9 :=
  sequence_readonly ops epilogue epilogue_valid state 9 (by decide +kernel)

theorem epilogue_input_10 (ops : Arithmetic) (state : State) :
    (sequence ops epilogue state).words 10 = state.words 10 :=
  sequence_readonly ops epilogue epilogue_valid state 10 (by decide +kernel)

section
attribute [local irreducible] MulSequenceFrame.sequence transition round MulNat.read MulNat.update
  firstRound secondRound thirdRound

theorem generic_model_of_rounds (ops : Arithmetic) (roundFunction : RoundOp)
    (firstModel : ∀ state, accumulator (sequence ops firstRound state) =
      roundFunction (lhs state) (modulus state) (inv state) (state.words 5) (accumulator state))
    (secondModel : ∀ state, accumulator (sequence ops secondRound state) =
      roundFunction (lhs state) (modulus state) (inv state) (state.words 6) (accumulator state))
    (thirdModel : ∀ state, accumulator (sequence ops thirdRound state) =
      roundFunction (lhs state) (modulus state) (inv state) (state.words 7) (accumulator state))
    (state : State) :
    output (sequence ops MulProgramData.retainedInstructions state) =
      model ops roundFunction (lhs state) (rhs state) (modulus state) (inv state) := by
  have firstRound_generic_r0 (state : State) :
      (sequence ops firstRound state).words 16 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).r0 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r0 (firstModel state)
  have firstRound_generic_r1 (state : State) :
      (sequence ops firstRound state).words 17 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).r1 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r1 (firstModel state)
  have firstRound_generic_r2 (state : State) :
      (sequence ops firstRound state).words 18 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).r2 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r2 (firstModel state)
  have firstRound_generic_r3 (state : State) :
      (sequence ops firstRound state).words 19 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).r3 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r3 (firstModel state)
  have firstRound_generic_r4 (state : State) :
      (sequence ops firstRound state).words 20 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).r4 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r4 (firstModel state)
  have firstRound_generic_q (state : State) :
      (sequence ops firstRound state).words 11 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).q :=
    congrArg PastaCurves.AArch64.MulMontAcc.q (firstModel state)
  have firstRound_generic_t1 (state : State) :
      (sequence ops firstRound state).words 13 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).t1 :=
    congrArg PastaCurves.AArch64.MulMontAcc.t1 (firstModel state)
  have firstRound_generic_t3 (state : State) :
      (sequence ops firstRound state).words 15 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 5)
          (accumulator state)).t3 :=
    congrArg PastaCurves.AArch64.MulMontAcc.t3 (firstModel state)
  have secondRound_generic_r0 (state : State) :
      (sequence ops secondRound state).words 16 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).r0 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r0 (secondModel state)
  have secondRound_generic_r1 (state : State) :
      (sequence ops secondRound state).words 17 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).r1 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r1 (secondModel state)
  have secondRound_generic_r2 (state : State) :
      (sequence ops secondRound state).words 18 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).r2 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r2 (secondModel state)
  have secondRound_generic_r3 (state : State) :
      (sequence ops secondRound state).words 19 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).r3 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r3 (secondModel state)
  have secondRound_generic_r4 (state : State) :
      (sequence ops secondRound state).words 20 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).r4 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r4 (secondModel state)
  have secondRound_generic_q (state : State) :
      (sequence ops secondRound state).words 11 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).q :=
    congrArg PastaCurves.AArch64.MulMontAcc.q (secondModel state)
  have secondRound_generic_t1 (state : State) :
      (sequence ops secondRound state).words 13 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).t1 :=
    congrArg PastaCurves.AArch64.MulMontAcc.t1 (secondModel state)
  have secondRound_generic_t3 (state : State) :
      (sequence ops secondRound state).words 15 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 6)
          (accumulator state)).t3 :=
    congrArg PastaCurves.AArch64.MulMontAcc.t3 (secondModel state)
  have thirdRound_generic_r0 (state : State) :
      (sequence ops thirdRound state).words 16 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).r0 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r0 (thirdModel state)
  have thirdRound_generic_r1 (state : State) :
      (sequence ops thirdRound state).words 17 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).r1 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r1 (thirdModel state)
  have thirdRound_generic_r2 (state : State) :
      (sequence ops thirdRound state).words 18 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).r2 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r2 (thirdModel state)
  have thirdRound_generic_r3 (state : State) :
      (sequence ops thirdRound state).words 19 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).r3 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r3 (thirdModel state)
  have thirdRound_generic_r4 (state : State) :
      (sequence ops thirdRound state).words 20 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).r4 :=
    congrArg PastaCurves.AArch64.MulMontAcc.r4 (thirdModel state)
  have thirdRound_generic_q (state : State) :
      (sequence ops thirdRound state).words 11 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).q :=
    congrArg PastaCurves.AArch64.MulMontAcc.q (thirdModel state)
  have thirdRound_generic_t1 (state : State) :
      (sequence ops thirdRound state).words 13 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).t1 :=
    congrArg PastaCurves.AArch64.MulMontAcc.t1 (thirdModel state)
  have thirdRound_generic_t3 (state : State) :
      (sequence ops thirdRound state).words 15 =
        (roundFunction (lhs state) (modulus state) (inv state) (state.words 7)
          (accumulator state)).t3 :=
    congrArg PastaCurves.AArch64.MulMontAcc.t3 (thirdModel state)
  rw [program_partition]
  simp only [sequence_append]
  simp only [↓output, ↓lhs, ↓rhs, ↓modulus, ↓inv,
    ↓accumulator, epilogue, initial, MulProgramData.retainedInstructions,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    ↓firstRound_generic_r0, ↓firstRound_generic_r1, ↓firstRound_generic_r2, ↓firstRound_generic_r3, ↓firstRound_generic_r4, ↓firstRound_generic_q, ↓firstRound_generic_t1, ↓firstRound_generic_t3,
    ↓secondRound_generic_r0, ↓secondRound_generic_r1, ↓secondRound_generic_r2, ↓secondRound_generic_r3, ↓secondRound_generic_r4, ↓secondRound_generic_q, ↓secondRound_generic_t1, ↓secondRound_generic_t3,
    ↓thirdRound_generic_r0, ↓thirdRound_generic_r1, ↓thirdRound_generic_r2, ↓thirdRound_generic_r3, ↓thirdRound_generic_r4, ↓thirdRound_generic_q, ↓thirdRound_generic_t1, ↓thirdRound_generic_t3,
    ↓initial_input_0, ↓initial_input_1, ↓initial_input_2, ↓initial_input_3, ↓initial_input_4, ↓initial_input_5, ↓initial_input_6, ↓initial_input_7, ↓initial_input_8, ↓initial_input_9, ↓initial_input_10,
    ↓firstRound_input_0, ↓firstRound_input_1, ↓firstRound_input_2, ↓firstRound_input_3, ↓firstRound_input_4, ↓firstRound_input_5, ↓firstRound_input_6, ↓firstRound_input_7, ↓firstRound_input_8, ↓firstRound_input_9, ↓firstRound_input_10,
    ↓secondRound_input_0, ↓secondRound_input_1, ↓secondRound_input_2, ↓secondRound_input_3, ↓secondRound_input_4, ↓secondRound_input_5, ↓secondRound_input_6, ↓secondRound_input_7, ↓secondRound_input_8, ↓secondRound_input_9, ↓secondRound_input_10,
    ↓thirdRound_input_0, ↓thirdRound_input_1, ↓thirdRound_input_2, ↓thirdRound_input_3, ↓thirdRound_input_4, ↓thirdRound_input_5, ↓thirdRound_input_6, ↓thirdRound_input_7, ↓thirdRound_input_8, ↓thirdRound_input_9, ↓thirdRound_input_10,
    ↓epilogue_input_0, ↓epilogue_input_1, ↓epilogue_input_2, ↓epilogue_input_3, ↓epilogue_input_4, ↓epilogue_input_5, ↓epilogue_input_6, ↓epilogue_input_7, ↓epilogue_input_8, ↓epilogue_input_9, ↓epilogue_input_10,
    ↓words_sequence_cons, ↓words_sequence_nil, ↓words_transition, ↓carry_transition,
    ↓value, ↓carry, ↓destination, ↓read_operand, ↓read_zero, ↓reduceIte, model]
  all_goals rfl
end

theorem generic_model (ops : Arithmetic) (state : State) :
    output (sequence ops MulProgramData.retainedInstructions state) =
      model ops (round ops) (lhs state) (rhs state) (modulus state) (inv state) :=
  generic_model_of_rounds ops (round ops) (firstRound_model ops) (secondRound_model ops)
    (thirdRound_model ops) state

section
attribute [local irreducible] MulSequenceFrame.sequence transition round model output lhs rhs modulus inv MulNat.sequence

theorem retained_data_model (state : State) :
    output (MulNat.sequence MulProgramData.retainedInstructions state) =
      PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (inv state) := by
  calc
    output (MulNat.sequence MulProgramData.retainedInstructions state) =
        output (sequence actualArithmetic MulProgramData.retainedInstructions state) :=
      congrArg output (sequence_specializes MulProgramData.retainedInstructions state).symm
    _ = model actualArithmetic (round actualArithmetic)
        (lhs state) (rhs state) (modulus state) (inv state) := generic_model actualArithmetic state
    _ = model actualArithmetic PastaCurves.AArch64.mulMontRound
        (lhs state) (rhs state) (modulus state) (inv state) :=
      congrArg (fun roundFunction => model actualArithmetic roundFunction
        (lhs state) (rhs state) (modulus state) (inv state)) round_specializes
    _ = PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (inv state) :=
      congrArg (fun function => function (lhs state) (rhs state) (modulus state) (inv state))
        model_specializes
end

#print axioms generic_model_of_rounds
#print axioms generic_model
#print axioms retained_data_model

end PastaBridge.MulParametric
