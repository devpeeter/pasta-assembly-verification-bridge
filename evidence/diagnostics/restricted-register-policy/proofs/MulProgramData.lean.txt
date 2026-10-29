import MulMachine
import Lean

open Lean Elab Term

namespace PastaBridge.MulProgramData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

deriving instance Lean.ToExpr for MulStep.Source
deriving instance Lean.ToExpr for MulStep.Instruction

elab "quotedRetainedMultiplicationInstructions" : term => do
  return Lean.toExpr MulMachine.decodedProgram

/-- Evaluated from the actual retained AST decoder; no instruction is transcribed. -/
def retainedInstructions : List MulStep.Instruction := quotedRetainedMultiplicationInstructions

theorem retained_instructions_readback :
    MulMachine.decodedProgram = retainedInstructions := by
  rfl

#print axioms retained_instructions_readback

end PastaBridge.MulProgramData
