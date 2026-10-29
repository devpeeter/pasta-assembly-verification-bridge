import AdditionNatData

namespace PastaBridge.AdditionNat

theorem read_operand (state : State) (operand : AdditionStep.Operand) :
    read state (.operand operand) = state.words operand := rfl

theorem read_zero (state : State) : read state .zero = 0 := rfl

theorem words_update (state : State) (destination query : AdditionStep.Operand)
    (value carry : Nat) :
    (update state destination value carry).words query =
      if query = destination then value else state.words query := rfl

theorem carry_update (state : State) (destination : AdditionStep.Operand)
    (value carry : Nat) :
    (update state destination value carry).carry = carry := rfl

theorem words_transition (kind : AdditionStep.Kind) (destination query : AdditionStep.Operand)
    (first second : AdditionStep.Source) (state : State) :
    (transition kind destination first second state).words query =
      if query = destination then
        let a := read state first
        let b := read state second
        match kind with
        | .adds => (PastaCurves.addc a b 0).1
        | .adcs | .adc => (PastaCurves.addc a b state.carry).1
        | .subs => (PastaCurves.AArch64.subc a b 1).1
        | .sbcs => (PastaCurves.AArch64.subc a b state.carry).1
        | .csel => PastaCurves.AArch64.cselCs state.carry a b
      else state.words query := by
  cases kind <;> rfl

theorem carry_transition (kind : AdditionStep.Kind) (destination : AdditionStep.Operand)
    (first second : AdditionStep.Source) (state : State) :
    (transition kind destination first second state).carry =
      let a := read state first
      let b := read state second
      match kind with
      | .adds => (PastaCurves.addc a b 0).2
      | .adcs => (PastaCurves.addc a b state.carry).2
      | .adc | .csel => state.carry
      | .subs => (PastaCurves.AArch64.subc a b 1).2
      | .sbcs => (PastaCurves.AArch64.subc a b state.carry).2 := by
  cases kind <;> rfl

#print axioms words_update
#print axioms carry_update
#print axioms words_transition
#print axioms carry_transition

end PastaBridge.AdditionNat

namespace PastaBridge.AdditionNatData

theorem words_sequence_nil (state : AdditionNat.State) (query : AdditionStep.Operand) :
    (sequence [] state).words query = state.words query := rfl

theorem words_sequence_cons (instruction : Instruction) (remaining : List Instruction)
    (state : AdditionNat.State) (query : AdditionStep.Operand) :
    (sequence (instruction :: remaining) state).words query =
      (sequence remaining (AdditionNat.transition instruction.kind instruction.destination
        instruction.first instruction.second state)).words query := rfl

theorem carry_sequence_nil (state : AdditionNat.State) :
    (sequence [] state).carry = state.carry := rfl

theorem carry_sequence_cons (instruction : Instruction) (remaining : List Instruction)
    (state : AdditionNat.State) :
    (sequence (instruction :: remaining) state).carry =
      (sequence remaining (AdditionNat.transition instruction.kind instruction.destination
        instruction.first instruction.second state)).carry := rfl

#print axioms words_sequence_nil
#print axioms words_sequence_cons
#print axioms carry_sequence_nil
#print axioms carry_sequence_cons

end PastaBridge.AdditionNatData
