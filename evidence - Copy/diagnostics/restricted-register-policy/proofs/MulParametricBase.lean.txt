import MulNatSequence
import MulProgramData
import MulSequenceFrame
import PastaCurves.AArch64.Transcription
import Lean

namespace PastaBridge.MulParametric

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Meta Elab Term
open MulStep

abbrev State := MulNat.State
abbrev CarryOp := Nat → Nat → Nat → Nat × Nat
abbrev BinaryOp := Nat → Nat → Nat
abbrev SelectOp := Nat → Nat → Nat → Nat
abbrev RoundOp := PastaCurves.Limbs → PastaCurves.Limbs → Nat → Nat →
  PastaCurves.AArch64.MulMontAcc → PastaCurves.AArch64.MulMontAcc

structure Arithmetic where
  add : CarryOp
  sub : CarryOp
  select : SelectOp
  mul : BinaryOp
  high : BinaryOp
  left : BinaryOp
  right : BinaryOp

def actualArithmetic : Arithmetic :=
  ⟨PastaCurves.addc, PastaCurves.AArch64.subc, PastaCurves.AArch64.cselLo,
    PastaCurves.mulLo, PastaCurves.umulh, PastaCurves.lsl, PastaCurves.lsr⟩

private def abstractBody (name : Name) (includeRound : Bool) : TermElabM Expr := do
  let definition ← getConstInfoDefn name
  let operations := #[`PastaCurves.addc, `PastaCurves.AArch64.subc,
    `PastaCurves.AArch64.cselLo, `PastaCurves.mulLo, `PastaCurves.umulh,
    `PastaCurves.lsl, `PastaCurves.lsr]
  withLocalDeclD `ops (mkConst ``Arithmetic) fun ops => do
    let replaceBody (round : Option Expr) := definition.value.replace fun term => Id.run do
      for i in [:operations.size] do
        if term.isConstOf operations[i]! then return some (mkProj ``Arithmetic i ops)
      if term.isConstOf `PastaCurves.AArch64.mulMontRound then return round
      return none
    if includeRound then
      let roundType := (← getConstInfo `PastaCurves.AArch64.mulMontRound).type
      withLocalDeclD `round roundType fun round =>
        mkLambdaFVars #[ops, round] (replaceBody (some round))
    else
      mkLambdaFVars #[ops] (replaceBody none)

elab "abstractMulTransition" : term => abstractBody `PastaBridge.MulNat.transition false
elab "abstractMulRound" : term => abstractBody `PastaCurves.AArch64.mulMontRound false
elab "abstractMulModel" : term => abstractBody `PastaCurves.AArch64.mulMont true

-- Candidates are obtained from the existing definitions. Their specializations
-- are checked below rather than assumed by the bridge.
def transition : Arithmetic → Instruction → State → State := abstractMulTransition
def round : Arithmetic → RoundOp := abstractMulRound
def model : Arithmetic → RoundOp → PastaCurves.Limbs → PastaCurves.Limbs →
    PastaCurves.Limbs → Nat → PastaCurves.Limbs := abstractMulModel

theorem transition_specializes : transition actualArithmetic = MulNat.transition := rfl
theorem round_specializes : round actualArithmetic = PastaCurves.AArch64.mulMontRound := rfl
theorem model_specializes : model actualArithmetic PastaCurves.AArch64.mulMontRound =
    PastaCurves.AArch64.mulMont := rfl

abbrev sequence (ops : Arithmetic) : List Instruction → State → State :=
  MulSequenceFrame.sequence (transition ops)

theorem sequence_specializes (program : List Instruction) (state : State) :
    sequence actualArithmetic program state = MulNat.sequence program state := by
  induction program generalizing state with
  | nil => rfl
  | cons operation remaining ih =>
    change sequence actualArithmetic remaining (transition actualArithmetic operation state) =
      MulNat.sequence remaining (MulNat.transition operation state)
    rw [transition_specializes]
    exact ih _

def value (ops : Arithmetic) (operation : Instruction) (state : State) : Nat :=
  match operation with
  | .adds _ a b => (ops.add (MulNat.read state a) (MulNat.read state b) 0).1
  | .adcs _ a b | .adc _ a b =>
    (ops.add (MulNat.read state a) (MulNat.read state b) state.carry).1
  | .subs _ a b => (ops.sub (MulNat.read state a) (MulNat.read state b) 1).1
  | .sbcs _ a b => (ops.sub (MulNat.read state a) (MulNat.read state b) state.carry).1
  | .cselLo _ a b => ops.select state.carry (MulNat.read state a) (MulNat.read state b)
  | .mul _ a b => ops.mul (MulNat.read state a) (MulNat.read state b)
  | .umulh _ a b => ops.high (MulNat.read state a) (MulNat.read state b)
  | .lsl _ a n => ops.left (MulNat.read state a) n.val
  | .lsr _ a n => ops.right (MulNat.read state a) n.val
  | .subsOne _ => 0
  | .movMask _ => 2^62

def carry (ops : Arithmetic) (operation : Instruction) (state : State) : Nat :=
  match operation with
  | .adds _ a b => (ops.add (MulNat.read state a) (MulNat.read state b) 0).2
  | .adcs _ a b => (ops.add (MulNat.read state a) (MulNat.read state b) state.carry).2
  | .subs _ a b => (ops.sub (MulNat.read state a) (MulNat.read state b) 1).2
  | .sbcs _ a b => (ops.sub (MulNat.read state a) (MulNat.read state b) state.carry).2
  | .subsOne a => (ops.sub (state.words a) 1 1).2
  | _ => state.carry

theorem words_transition (ops : Arithmetic) (operation : Instruction) (state : State)
    (query : Operand) :
    (transition ops operation state).words query =
      match destination operation with
      | none => state.words query
      | some d => if query = d then value ops operation state else state.words query := by
  cases operation <;> rfl

theorem carry_transition (ops : Arithmetic) (operation : Instruction) (state : State) :
    (transition ops operation state).carry = carry ops operation state := by
  cases operation <;> rfl

theorem words_sequence_nil (ops : Arithmetic) (state : State) (query : Operand) :
    (sequence ops [] state).words query = state.words query := rfl
theorem words_sequence_cons (ops : Arithmetic) (operation : Instruction)
    (remaining : List Instruction) (state : State) (query : Operand) :
    (sequence ops (operation :: remaining) state).words query =
      (sequence ops remaining (transition ops operation state)).words query := rfl
theorem carry_sequence_nil (ops : Arithmetic) (state : State) :
    (sequence ops [] state).carry = state.carry := rfl
theorem carry_sequence_cons (ops : Arithmetic) (operation : Instruction)
    (remaining : List Instruction) (state : State) :
    (sequence ops (operation :: remaining) state).carry =
      (sequence ops remaining (transition ops operation state)).carry := rfl

theorem read_operand (state : State) (i : Operand) :
    MulNat.read state (.operand i) = state.words i := rfl
theorem read_zero (state : State) : MulNat.read state .zero = 0 := rfl

def lhs (state : State) : PastaCurves.Limbs :=
  ⟨state.words 0, state.words 1, state.words 2, state.words 3⟩
def rhs (state : State) : PastaCurves.Limbs :=
  ⟨state.words 4, state.words 5, state.words 6, state.words 7⟩
def modulus (state : State) : PastaCurves.Limbs :=
  ⟨state.words 8, state.words 9, 0, 2^62⟩
def inv (state : State) : Nat := state.words 10
def output (state : State) : PastaCurves.Limbs :=
  ⟨state.words 16, state.words 17, state.words 18, state.words 19⟩
def accumulator (state : State) : PastaCurves.AArch64.MulMontAcc :=
  ⟨state.words 16, state.words 17, state.words 18, state.words 19, state.words 20,
    state.words 11, state.words 13, state.words 15⟩

-- Partition only the checked, mechanically quoted program; no instructions are
-- transcribed here. The complete reassembly is itself checked below.
def initial : List Instruction := MulProgramData.retainedInstructions.take 15
def firstRound : List Instruction := (MulProgramData.retainedInstructions.drop 15).take 33
def secondRound : List Instruction := (MulProgramData.retainedInstructions.drop 48).take 33
def thirdRound : List Instruction := (MulProgramData.retainedInstructions.drop 81).take 33
def epilogue : List Instruction := MulProgramData.retainedInstructions.drop 114

theorem program_partition : MulProgramData.retainedInstructions =
    initial ++ firstRound ++ secondRound ++ thirdRound ++ epilogue := by
  decide +kernel

theorem retained_valid (operation : Instruction)
    (member : operation ∈ MulProgramData.retainedInstructions) : Valid operation := by
  apply MulMachine.decoded_valid operation
  rw [MulProgramData.retained_instructions_readback]
  exact member

theorem initial_valid (operation : Instruction) (member : operation ∈ initial) :
    Valid operation := retained_valid operation (List.mem_of_mem_take member)
theorem firstRound_valid (operation : Instruction) (member : operation ∈ firstRound) :
    Valid operation := retained_valid operation (List.mem_of_mem_drop (List.mem_of_mem_take member))
theorem secondRound_valid (operation : Instruction) (member : operation ∈ secondRound) :
    Valid operation := retained_valid operation (List.mem_of_mem_drop (List.mem_of_mem_take member))
theorem thirdRound_valid (operation : Instruction) (member : operation ∈ thirdRound) :
    Valid operation := retained_valid operation (List.mem_of_mem_drop (List.mem_of_mem_take member))
theorem epilogue_valid (operation : Instruction) (member : operation ∈ epilogue) :
    Valid operation := retained_valid operation (List.mem_of_mem_drop member)

theorem transition_readonly (ops : Arithmetic) (operation : Instruction)
    (valid : Valid operation) (state : State) (query : Operand)
    (readonly : written query = false) :
    (transition ops operation state).words query = state.words query := by
  rw [words_transition]
  cases hd : destination operation with
  | none => rfl
  | some d =>
    have different : query ≠ d := by
      intro same
      have isWritten := valid d hd
      rw [← same, readonly] at isWritten
      cases isWritten
    exact if_neg different

theorem sequence_readonly (ops : Arithmetic) (program : List Instruction)
    (valid : ∀ operation ∈ program, Valid operation) (state : State) (query : Operand)
    (readonly : written query = false) :
    (sequence ops program state).words query = state.words query :=
  MulSequenceFrame.readonly MulNat.State.words (transition ops) (transition_readonly ops)
    program valid state query readonly

theorem sequence_append (ops : Arithmetic) (first second : List Instruction) (state : State) :
    sequence ops (first ++ second) state = sequence ops second (sequence ops first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons operation remaining ih => exact ih (transition ops operation state)

#print axioms transition_specializes
#print axioms round_specializes
#print axioms model_specializes
#print axioms sequence_specializes
#print axioms words_transition
#print axioms carry_transition
#print axioms program_partition
#print axioms sequence_readonly
#print axioms sequence_append

end PastaBridge.MulParametric
