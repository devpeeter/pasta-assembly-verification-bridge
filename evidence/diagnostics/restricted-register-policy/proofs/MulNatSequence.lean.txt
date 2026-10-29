import MulNat
import MulMachine
import AdditionNatSequence

namespace PastaBridge.MulNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MulStep

def sequence : List Instruction → State → State
  | [], state => state
  | operation :: remaining, state => sequence remaining (transition operation state)

theorem machine_sequence_nil (binding : Binding) (state : MachineData) :
    MulMachine.sequence binding [] state = .ok state := rfl

theorem machine_sequence_cons (binding : Binding) (operation : Instruction)
    (remaining : List Instruction) (state : MachineData) :
    MulMachine.sequence binding (operation :: remaining) state =
      (MulStep.step operation binding state).bind
        (fun after => MulMachine.sequence binding remaining after) := rfl

section
attribute [local irreducible] MulStep.step MulMachine.sequence project transition

theorem sequence_project (binding : Binding) (program : List Instruction)
    (state : MachineData) (separated : KrakenBinding.Separated written binding)
    (valid : ∀ operation ∈ program, Valid operation) :
    (MulMachine.sequence binding program state).map (project binding) =
      .ok (sequence program (project binding state)) := by
  revert valid
  induction program generalizing state with
  | nil => intro valid; rw [machine_sequence_nil]; rfl
  | cons operation remaining ih =>
    intro valid
    have headValid : Valid operation := valid operation (List.mem_cons_self)
    have tailValid : ∀ item ∈ remaining, Valid item :=
      fun item member => valid item (List.mem_cons_of_mem operation member)
    rw [machine_sequence_cons]
    change ((MulStep.step operation binding state).bind
        (fun after => MulMachine.sequence binding remaining after)).map (project binding) =
      .ok (sequence remaining (transition operation (project binding state)))
    exact AdditionNat.bind_project _ _ (project binding) _ (sequence remaining)
      (step_project operation binding state separated headValid)
      (fun after => ih after tailValid)
end

theorem decoded_sequence_project (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (MulMachine.sequence binding MulMachine.decodedProgram state).map (project binding) =
      .ok (sequence MulMachine.decodedProgram (project binding state)) :=
  sequence_project binding MulMachine.decodedProgram state separated MulMachine.decoded_valid

#print axioms machine_sequence_nil
#print axioms machine_sequence_cons
#print axioms sequence_project
#print axioms decoded_sequence_project

end PastaBridge.MulNat
