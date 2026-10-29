import AdditionNatSequence
import Lean

namespace PastaBridge.AdditionNatData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Elab Term

-- Only data fields are retained; the checked decoder's destination proof is erased.
deriving instance Lean.ToExpr for AdditionStep.Kind
deriving instance Lean.ToExpr for AdditionStep.Source

structure Instruction where
  kind : AdditionStep.Kind
  destination : Fin 15
  first : AdditionStep.Source
  second : AdditionStep.Source
  deriving Lean.ToExpr

def erase (instruction : AdditionLift.Decoded) : Instruction :=
  ⟨instruction.kind, instruction.destination, instruction.first, instruction.second⟩

elab "quotedAdditionData" : term => do
  return Lean.toExpr (AdditionLift.decodedProgram.map erase)

/-- Produced by evaluating the actual retained program decoder, never transcribed. -/
def retainedData : List Instruction := quotedAdditionData

theorem retained_data_readback :
    AdditionLift.decodedProgram.map erase = retainedData := by rfl

def sequence : List Instruction → AdditionNat.State → AdditionNat.State
  | [], state => state
  | instruction :: remaining, state =>
    sequence remaining (AdditionNat.transition instruction.kind instruction.destination
      instruction.first instruction.second state)

section
attribute [local irreducible] AdditionNat.transition

theorem sequence_erase (program : List AdditionLift.Decoded) (state : AdditionNat.State) :
    AdditionNat.sequence program state = sequence (program.map erase) state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction remaining ih =>
    exact ih (AdditionNat.transition instruction.kind instruction.destination
      instruction.first instruction.second state)
end

theorem retained_sequence (state : AdditionNat.State) :
    AdditionNat.sequence AdditionLift.decodedProgram state = sequence retainedData state := by
  rw [sequence_erase, retained_data_readback]

#print axioms retained_data_readback
#print axioms sequence_erase
#print axioms retained_sequence

end PastaBridge.AdditionNatData
