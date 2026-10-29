import AdditionNatSequence
import PastaCurves.AArch64.Transcription

namespace PastaBridge.AdditionNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open AdditionStep

def output (state : State) : PastaCurves.Limbs :=
  ⟨state.words 0, state.words 1, state.words 2, state.words 3⟩

def rhs (state : State) : PastaCurves.Limbs :=
  ⟨state.words 4, state.words 5, state.words 6, state.words 7⟩

def modulus (state : State) : PastaCurves.Limbs :=
  ⟨state.words 8, state.words 9, 0, state.words 10⟩

theorem map_comp {A B C : Type} (execution : Except String A) (first : A → B) (second : B → C) :
    execution.map (fun value => second (first value)) =
      (execution.map first).map second := by cases execution <;> rfl

def Correspondence : Prop := ∀ state : State,
  output (sequence AdditionLift.decodedProgram state) =
    PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state)

attribute [local irreducible] run AdditionMachine.runWithBinding AdditionMachine.boundProgram
  AdditionLift.sequence AdditionStep.step project transition sequence output rhs modulus

theorem all_bindings_model_of (model : Correspondence)
    (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (AdditionMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.addMod (output (project binding state))
        (rhs (project binding state)) (modulus (project binding state))) := by
  have execution : AdditionMachine.runWithBinding binding state =
      AdditionLift.sequence binding AdditionLift.decodedProgram state :=
    (AdditionMachine.run_binding binding state).trans
      (AdditionLift.full_run_is_sequence binding state)
  calc
    (AdditionMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
        (AdditionLift.sequence binding AdditionLift.decodedProgram state).map
          (fun after => output (project binding after)) :=
      congrArg (fun result => result.map (fun after => output (project binding after))) execution
    _ = ((AdditionLift.sequence binding AdditionLift.decodedProgram state).map
          (project binding)).map output := map_comp _ _ _
    _ = (Except.ok (sequence AdditionLift.decodedProgram (project binding state))).map output :=
      congrArg (fun result => result.map output)
        (sequence_project binding AdditionLift.decodedProgram state separated)
    _ = Except.ok (output (sequence AdditionLift.decodedProgram (project binding state))) := rfl
    _ = Except.ok (PastaCurves.AArch64.addMod (output (project binding state))
          (rhs (project binding state)) (modulus (project binding state))) :=
      congrArg Except.ok (model (project binding state))

#print axioms map_comp
#print axioms all_bindings_model_of

end PastaBridge.AdditionNat
