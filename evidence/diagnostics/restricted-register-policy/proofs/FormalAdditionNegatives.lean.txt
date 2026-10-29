import AdditionNatLift
import PastaCurves.Fields

namespace PastaBridge.FormalAdditionNegatives

open AdditionStep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def breakCarry : List AdditionLift.Decoded → List AdditionLift.Decoded
  | [] => []
  | instruction :: remaining =>
    match instruction.kind with
    | .adcs => { instruction with kind := .adds } :: remaining
    | _ => instruction :: breakCarry remaining

def changeRhsSource : Source → Option Source
  | .operand index => if index.val = 4 then some (.operand 5) else none
  | .zero => none

def breakBinding : List AdditionLift.Decoded → List AdditionLift.Decoded
  | [] => []
  | instruction :: remaining =>
    match changeRhsSource instruction.first with
    | some source => { instruction with first := source } :: remaining
    | none =>
      match changeRhsSource instruction.second with
      | some source => { instruction with second := source } :: remaining
      | none => instruction :: breakBinding remaining

def witness : AdditionNat.State :=
  ⟨fun index => match index.val with
    | 0 => 2^64 - 1
    | 4 => 1
    | 8 => PastaCurves.pallasBase.modulus.l0
    | 9 => PastaCurves.pallasBase.modulus.l1
    | 10 => PastaCurves.pallasBase.modulus.l3
    | _ => 0,
    0⟩

def expected : PastaCurves.Limbs := PastaCurves.AArch64.addMod
  (AdditionNat.output witness) (AdditionNat.rhs witness) (AdditionNat.modulus witness)

def carryResult : PastaCurves.Limbs := AdditionNat.output
  (AdditionNat.sequence (breakCarry AdditionLift.decodedProgram) witness)

def bindingResult : PastaCurves.Limbs := AdditionNat.output
  (AdditionNat.sequence (breakBinding AdditionLift.decodedProgram) witness)

theorem unmodified_model :
    AdditionNat.output (AdditionNat.sequence AdditionLift.decodedProgram witness) = expected :=
  AdditionNat.decoded_program_model witness

theorem witness_words_bounded : ∀ index : Fin 15, witness.words index < 2^64 := by decide +kernel

theorem witness_field_inputs :
    AdditionNat.modulus witness = PastaCurves.pallasBase.modulus ∧
    (AdditionNat.output witness).toNat < PastaCurves.pallasBase.modulus.toNat ∧
    (AdditionNat.rhs witness).toNat < PastaCurves.pallasBase.modulus.toNat := by decide +kernel

theorem expected_value : expected.toNat = 2^64 := by decide +kernel

theorem broken_carry_value : carryResult.toNat = 0 := by decide +kernel

theorem broken_binding_value : bindingResult.toNat = 2^64 - 1 := by decide +kernel

theorem broken_carry_is_semantically_wrong : carryResult ≠ expected := by decide +kernel

theorem broken_binding_is_semantically_wrong : bindingResult ≠ expected := by decide +kernel

#print axioms unmodified_model
#print axioms witness_words_bounded
#print axioms witness_field_inputs
#print axioms expected_value
#print axioms broken_carry_value
#print axioms broken_binding_value
#print axioms broken_carry_is_semantically_wrong
#print axioms broken_binding_is_semantically_wrong

end PastaBridge.FormalAdditionNegatives
