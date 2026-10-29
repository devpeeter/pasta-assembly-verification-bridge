import AdditionNatModel

namespace PastaBridge.AdditionNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open AdditionStep

attribute [local irreducible] run AdditionMachine.runWithBinding AdditionMachine.boundProgram
  AdditionLift.sequence AdditionStep.step project transition sequence output rhs modulus

theorem all_bindings_model (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (AdditionMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.addMod (output (project binding state))
        (rhs (project binding state)) (modulus (project binding state))) :=
  all_bindings_model_of decoded_program_model binding state separated

#print axioms all_bindings_model

end PastaBridge.AdditionNat
