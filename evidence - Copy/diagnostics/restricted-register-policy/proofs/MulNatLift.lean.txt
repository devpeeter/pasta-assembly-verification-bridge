import MulParametricModel

namespace PastaBridge.MulNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MulStep

def lhs (state : State) : PastaCurves.Limbs := MulParametric.lhs state
def rhs (state : State) : PastaCurves.Limbs := MulParametric.rhs state
def modulus (state : State) : PastaCurves.Limbs := MulParametric.modulus state
def inv (state : State) : Nat := MulParametric.inv state
def output (state : State) : PastaCurves.Limbs := MulParametric.output state

private theorem map_comp {A B C : Type} (execution : Except String A)
    (first : A → B) (second : B → C) :
    execution.map (fun value => second (first value)) =
      (execution.map first).map second := by cases execution <;> rfl

attribute [local irreducible] sequence transition project MulStep.step MulMachine.sequence
  MulMachine.runWithBinding MulMachine.boundProgram run PastaCurves.AArch64.mulMont

theorem decoded_program_model (state : State) :
    output (sequence MulMachine.decodedProgram state) =
      PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (inv state) :=
  (congrArg (fun program => output (sequence program state))
    MulProgramData.retained_instructions_readback).trans (MulParametric.retained_data_model state)

attribute [local irreducible] lhs rhs modulus inv output

theorem all_bindings_model (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (MulMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.mulMont (lhs (project binding state))
        (rhs (project binding state)) (modulus (project binding state)) (inv (project binding state))) := by
  have execution : MulMachine.runWithBinding binding state =
      MulMachine.sequence binding MulMachine.decodedProgram state :=
    (MulMachine.run_binding binding state).trans (MulMachine.full_run_is_sequence binding state)
  calc
    (MulMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
        (MulMachine.sequence binding MulMachine.decodedProgram state).map
          (fun after => output (project binding after)) :=
      congrArg (fun result => result.map (fun after => output (project binding after))) execution
    _ = ((MulMachine.sequence binding MulMachine.decodedProgram state).map
          (project binding)).map output := map_comp _ _ _
    _ = (Except.ok (sequence MulMachine.decodedProgram (project binding state))).map output :=
      congrArg (fun result => result.map output) (decoded_sequence_project binding state separated)
    _ = Except.ok (output (sequence MulMachine.decodedProgram (project binding state))) := rfl
    _ = Except.ok (PastaCurves.AArch64.mulMont (lhs (project binding state))
          (rhs (project binding state)) (modulus (project binding state)) (inv (project binding state))) :=
      congrArg Except.ok (decoded_program_model (project binding state))

#print axioms decoded_program_model
#print axioms all_bindings_model

end PastaBridge.MulNat
