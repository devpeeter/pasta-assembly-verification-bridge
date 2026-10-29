import MulCorrectness

/- This assignment rejects an extra program/model correspondence premise. -/
theorem multiplication_target_type :
    ∀ (field : PastaCurves.PastaField)
      (binding : PastaBridge.MulMachine.Binding) (state : MachineData),
      PastaBridge.MulMachine.Admissible binding →
      PastaBridge.MulCorrectness.InputContract field binding state →
      ∃ after : MachineData,
        PastaBridge.MulMachine.runWithBinding binding state = .ok after ∧
        PastaBridge.MulCorrectness.Postcondition field binding state after :=
  PastaBridge.MulCorrectness.multiplication_correct

#print PastaBridge.MulMachine.Admissible
#print PastaBridge.MulCorrectness.InputContract
#print PastaBridge.MulCorrectness.Postcondition
#check PastaBridge.MulCorrectness.multiplication_correct PastaCurves.pallasBase
#check PastaBridge.MulCorrectness.multiplication_correct PastaCurves.vestaBase
#print axioms multiplication_target_type
#print axioms PastaBridge.MulCorrectness.multiplication_correct
