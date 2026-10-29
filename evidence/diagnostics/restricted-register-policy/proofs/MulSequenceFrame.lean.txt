import MulStep

namespace PastaBridge.MulSequenceFrame

open MulStep

def sequence {State : Type} (next : Instruction → State → State) :
    List Instruction → State → State
  | [], state => state
  | operation :: remaining, state => sequence next remaining (next operation state)

theorem readonly {State Value : Type} (observe : State → Operand → Value)
    (next : Instruction → State → State)
    (preserves : ∀ operation, Valid operation → ∀ state queried,
      written queried = false → observe (next operation state) queried = observe state queried)
    (program : List Instruction) (valid : ∀ operation ∈ program, Valid operation)
    (state : State) (queried : Operand) (isReadonly : written queried = false) :
    observe (sequence next program state) queried = observe state queried := by
  induction program generalizing state with
  | nil => rfl
  | cons operation remaining ih =>
    change observe (sequence next remaining (next operation state)) queried = observe state queried
    rw [ih (fun instruction member => valid instruction (List.mem_cons_of_mem _ member))
      (next operation state)]
    exact preserves operation (valid operation List.mem_cons_self) state queried isReadonly

#print axioms readonly

end PastaBridge.MulSequenceFrame
