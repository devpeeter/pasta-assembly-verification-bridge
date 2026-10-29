import AdditionNatLiftBase
import AdditionNatDataModel

namespace PastaBridge.AdditionNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

attribute [local irreducible] sequence AdditionNatData.sequence project transition
  AdditionLift.sequence AdditionStep.step PastaCurves.AArch64.addMod

theorem decoded_program_model (state : State) :
    output (sequence AdditionLift.decodedProgram state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state) := by
  have quotedModel : output (AdditionNatData.sequence AdditionNatData.retainedData state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state) :=
    AdditionNatData.retained_data_model state
  exact (congrArg output (AdditionNatData.retained_sequence state)).trans quotedModel

#print axioms decoded_program_model

end PastaBridge.AdditionNat
