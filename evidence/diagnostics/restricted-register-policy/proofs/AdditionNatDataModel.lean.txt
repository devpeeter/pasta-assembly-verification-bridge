import AdditionParametricModel

namespace PastaBridge.AdditionNatData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def output (state : AdditionNat.State) : PastaCurves.Limbs :=
  ⟨state.words 0, state.words 1, state.words 2, state.words 3⟩

def rhs (state : AdditionNat.State) : PastaCurves.Limbs :=
  ⟨state.words 4, state.words 5, state.words 6, state.words 7⟩

def modulus (state : AdditionNat.State) : PastaCurves.Limbs :=
  ⟨state.words 8, state.words 9, 0, state.words 10⟩

attribute [local irreducible] sequence AdditionParametric.sequence AdditionParametric.model
  AdditionNat.transition AdditionNat.update PastaCurves.AArch64.addMod

theorem retained_data_model (state : AdditionNat.State) :
    output (sequence retainedData state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state) :=
  AdditionParametric.retained_data_model state

#print axioms retained_data_model

end PastaBridge.AdditionNatData
