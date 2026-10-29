import AdditionNatObservation
import PastaCurves.AArch64.Transcription
import Lean

namespace PastaBridge.AdditionParametric

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Meta Elab Term
open AdditionStep

abbrev CarryOp := Nat → Nat → Nat → Nat × Nat
abbrev SelectOp := Nat → Nat → Nat → Nat
abbrev State := AdditionNat.State

private def abstractArithmeticBody (name : Name) : TermElabM Expr := do
  let definition ← getConstInfoDefn name
  let operations := #[`PastaCurves.addc, `PastaCurves.AArch64.subc,
    `PastaCurves.AArch64.cselCs]
  for operation in operations do
    unless (definition.value.find? (fun term => term.isConstOf operation)).isSome do
      throwError "expected arithmetic operation {operation} in {name}"
  let addType := (← getConstInfo operations[0]!).type
  let subType := (← getConstInfo operations[1]!).type
  let selectType := (← getConstInfo operations[2]!).type
  withLocalDeclD `addOp addType fun addOp =>
    withLocalDeclD `subOp subType fun subOp =>
      withLocalDeclD `selectOp selectType fun selectOp => do
        let body := definition.value.replace fun term =>
          if term.isConstOf operations[0]! then some addOp
          else if term.isConstOf operations[1]! then some subOp
          else if term.isConstOf operations[2]! then some selectOp
          else none
        return ← mkLambdaFVars #[addOp, subOp, selectOp] body

elab "abstractPastaAddition" : term => abstractArithmeticBody `PastaCurves.AArch64.addMod
elab "abstractNatTransition" : term => abstractArithmeticBody `PastaBridge.AdditionNat.transition

-- These are candidates derived from existing definitions; the specialization
-- equalities below must be checked before their use in a closed target theorem.
def model : CarryOp → CarryOp → SelectOp →
    PastaCurves.Limbs → PastaCurves.Limbs → PastaCurves.Limbs → PastaCurves.Limbs :=
  abstractPastaAddition

def transition : CarryOp → CarryOp → SelectOp → Kind → Operand → Source → Source →
    State → State := abstractNatTransition

theorem model_specializes :
    model PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs =
      PastaCurves.AArch64.addMod := rfl

theorem transition_specializes :
    transition PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs =
      AdditionNat.transition := rfl

def sequence (addOp subOp : CarryOp) (selectOp : SelectOp) :
    List AdditionNatData.Instruction → State → State
  | [], state => state
  | instruction :: remaining, state =>
    sequence addOp subOp selectOp remaining
      (transition addOp subOp selectOp instruction.kind instruction.destination
        instruction.first instruction.second state)

theorem sequence_specializes (program : List AdditionNatData.Instruction) (state : State) :
    sequence PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs program state =
      AdditionNatData.sequence program state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction remaining ih =>
    change sequence _ _ _ remaining (transition _ _ _ instruction.kind instruction.destination
      instruction.first instruction.second state) =
        AdditionNatData.sequence remaining
          (AdditionNat.transition instruction.kind instruction.destination
            instruction.first instruction.second state)
    rw [transition_specializes]
    exact ih _

theorem words_transition (addOp subOp : CarryOp) (selectOp : SelectOp)
    (kind : Kind) (destination query : Operand) (first second : Source) (state : State) :
    (transition addOp subOp selectOp kind destination first second state).words query =
      if query = destination then
        let a := AdditionNat.read state first
        let b := AdditionNat.read state second
        match kind with
        | .adds => (addOp a b 0).1
        | .adcs | .adc => (addOp a b state.carry).1
        | .subs => (subOp a b 1).1
        | .sbcs => (subOp a b state.carry).1
        | .csel => selectOp state.carry a b
      else state.words query := by
  cases kind <;> rfl

theorem carry_transition (addOp subOp : CarryOp) (selectOp : SelectOp)
    (kind : Kind) (destination : Operand) (first second : Source) (state : State) :
    (transition addOp subOp selectOp kind destination first second state).carry =
      let a := AdditionNat.read state first
      let b := AdditionNat.read state second
      match kind with
      | .adds => (addOp a b 0).2
      | .adcs => (addOp a b state.carry).2
      | .adc | .csel => state.carry
      | .subs => (subOp a b 1).2
      | .sbcs => (subOp a b state.carry).2 := by
  cases kind <;> rfl

theorem words_sequence_nil (addOp subOp : CarryOp) (selectOp : SelectOp)
    (state : State) (query : Operand) :
    (sequence addOp subOp selectOp [] state).words query = state.words query := rfl

theorem words_sequence_cons (addOp subOp : CarryOp) (selectOp : SelectOp)
    (instruction : AdditionNatData.Instruction) (remaining : List AdditionNatData.Instruction)
    (state : State) (query : Operand) :
    (sequence addOp subOp selectOp (instruction :: remaining) state).words query =
      (sequence addOp subOp selectOp remaining
        (transition addOp subOp selectOp instruction.kind instruction.destination
          instruction.first instruction.second state)).words query := rfl

theorem carry_sequence_nil (addOp subOp : CarryOp) (selectOp : SelectOp) (state : State) :
    (sequence addOp subOp selectOp [] state).carry = state.carry := rfl

theorem carry_sequence_cons (addOp subOp : CarryOp) (selectOp : SelectOp)
    (instruction : AdditionNatData.Instruction) (remaining : List AdditionNatData.Instruction)
    (state : State) :
    (sequence addOp subOp selectOp (instruction :: remaining) state).carry =
      (sequence addOp subOp selectOp remaining
        (transition addOp subOp selectOp instruction.kind instruction.destination
          instruction.first instruction.second state)).carry := rfl

def output (state : State) : PastaCurves.Limbs :=
  ⟨state.words 0, state.words 1, state.words 2, state.words 3⟩

def rhs (state : State) : PastaCurves.Limbs :=
  ⟨state.words 4, state.words 5, state.words 6, state.words 7⟩

def modulus (state : State) : PastaCurves.Limbs :=
  ⟨state.words 8, state.words 9, 0, state.words 10⟩


#print axioms model_specializes
#print axioms transition_specializes
#print axioms sequence_specializes
#print axioms words_transition
#print axioms carry_transition

end PastaBridge.AdditionParametric
