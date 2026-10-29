import AdditionNat
import AdditionMachine

namespace PastaBridge.AdditionNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open AdditionStep

def sequence : List AdditionLift.Decoded → State → State
  | [], state => state
  | instruction :: remaining, state =>
    sequence remaining (transition instruction.kind instruction.destination
      instruction.first instruction.second state)

theorem bind_project {A B : Type} (first : Except String A)
    (rest : A → Except String A) (project : A → B) (next : B) (finish : B → B)
    (firstProjects : first.map project = .ok next)
    (restProjects : ∀ state, (rest state).map project = .ok (finish (project state))) :
    (first.bind rest).map project = .ok (finish next) := by
  cases first with
  | error message => cases firstProjects
  | ok state =>
    have projected : project state = next := Except.ok.inj firstProjects
    change (rest state).map project = .ok (finish next)
    rw [restProjects state, projected]

theorem machine_sequence_nil (binding : Binding) (state : MachineData) :
    AdditionLift.sequence binding [] state = .ok state := rfl

theorem machine_sequence_cons (binding : Binding) (instruction : AdditionLift.Decoded)
    (remaining : List AdditionLift.Decoded) (state : MachineData) :
    AdditionLift.sequence binding (instruction :: remaining) state =
      (AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second state).bind
        (fun after => AdditionLift.sequence binding remaining after) := rfl

section
attribute [local irreducible] AdditionStep.step AdditionLift.sequence project transition

theorem sequence_project (binding : Binding) (program : List AdditionLift.Decoded)
    (state : MachineData) (separated : KrakenBinding.Separated written binding) :
    (AdditionLift.sequence binding program state).map (project binding) =
      .ok (sequence program (project binding state)) := by
  induction program generalizing state with
  | nil => rw [machine_sequence_nil]; rfl
  | cons instruction remaining ih =>
    rw [machine_sequence_cons]
    change ((AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second state).bind
        (fun after => AdditionLift.sequence binding remaining after)).map (project binding) =
      .ok (sequence remaining (transition instruction.kind instruction.destination
        instruction.first instruction.second (project binding state)))
    exact bind_project _ _ (project binding) _ (sequence remaining)
      (step_project instruction.kind binding state separated instruction.destination
        instruction.destinationWritten instruction.first instruction.second) ih
end

#print axioms bind_project
#print axioms machine_sequence_nil
#print axioms machine_sequence_cons
#print axioms sequence_project

end PastaBridge.AdditionNat
