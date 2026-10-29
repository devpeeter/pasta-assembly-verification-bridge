import MulNatSequence
import PastaCurves.Fields
import PastaCurves.Compositions
import PastaCurves.AArch64.Transcription

namespace PastaBridge.FormalMulNegatives

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MulStep

def breakCarry : List Instruction → List Instruction
  | [] => []
  | operation :: remaining =>
    match operation with
    | .adcs d a b => .adds d a b :: remaining
    | _ => operation :: breakCarry remaining

def breakBinding : List Instruction → List Instruction
  | [] => []
  | operation :: remaining =>
    match operation with
    | .mul d a (.operand i) =>
      if i.val = 4 then .mul d a (.operand 5) :: remaining
      else operation :: breakBinding remaining
    | _ => operation :: breakBinding remaining

def lhs (state : MulNat.State) : PastaCurves.Limbs :=
  ⟨state.words 0, state.words 1, state.words 2, state.words 3⟩

def rhs (state : MulNat.State) : PastaCurves.Limbs :=
  ⟨state.words 4, state.words 5, state.words 6, state.words 7⟩

def modulus (state : MulNat.State) : PastaCurves.Limbs :=
  ⟨state.words 8, state.words 9, 0, 2^62⟩

def output (state : MulNat.State) : PastaCurves.Limbs :=
  ⟨state.words 16, state.words 17, state.words 18, state.words 19⟩

def carryWitness : MulNat.State :=
  ⟨fun index => match index.val with
    | 0 => PastaCurves.pallasBase.modulus.l0 - 1
    | 1 => PastaCurves.pallasBase.modulus.l1
    | 2 => PastaCurves.pallasBase.modulus.l2
    | 3 => PastaCurves.pallasBase.modulus.l3
    | 4 => 2^64 - 1
    | 8 => PastaCurves.pallasBase.modulus.l0
    | 9 => PastaCurves.pallasBase.modulus.l1
    | 10 => PastaCurves.pallasBase.inv
    | _ => 0, 0⟩

def bindingWitness : MulNat.State :=
  ⟨fun index => match index.val with
    | 0 => 1
    | 4 => 1
    | 8 => PastaCurves.pallasBase.modulus.l0
    | 9 => PastaCurves.pallasBase.modulus.l1
    | 10 => PastaCurves.pallasBase.inv
    | _ => 0, 0⟩

def model (state : MulNat.State) : PastaCurves.Limbs :=
  PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (state.words 10)

def carryExpected : PastaCurves.Limbs := model carryWitness
def bindingExpected : PastaCurves.Limbs := model bindingWitness

def carryResult : PastaCurves.Limbs :=
  output (MulNat.sequence (breakCarry MulMachine.decodedProgram) carryWitness)

def bindingResult : PastaCurves.Limbs :=
  output (MulNat.sequence (breakBinding MulMachine.decodedProgram) bindingWitness)

theorem witness_words_bounded : ∀ i : Fin 21,
    carryWitness.words i < 2^64 ∧ bindingWitness.words i < 2^64 := by decide +kernel

theorem witness_field_inputs :
    modulus carryWitness = PastaCurves.pallasBase.modulus ∧
    modulus bindingWitness = PastaCurves.pallasBase.modulus ∧
    carryWitness.words 10 = PastaCurves.pallasBase.inv ∧
    bindingWitness.words 10 = PastaCurves.pallasBase.inv ∧
    PastaCurves.mulContract (lhs carryWitness) (rhs carryWitness) PastaCurves.pallasBase.modulus = true ∧
    PastaCurves.mulContract (lhs bindingWitness) (rhs bindingWitness) PastaCurves.pallasBase.modulus = true := by
  decide +kernel

theorem witness_input_values :
    (lhs carryWitness).toNat = PastaCurves.pallasBase.modulus.toNat - 1 ∧
    (rhs carryWitness).toNat = 2^64 - 1 ∧
    (lhs bindingWitness).toNat = 1 ∧ (rhs bindingWitness).toNat = 1 := by decide +kernel

theorem unmodified_models :
    output (MulNat.sequence MulMachine.decodedProgram carryWitness) = carryExpected ∧
    output (MulNat.sequence MulMachine.decodedProgram bindingWitness) = bindingExpected := by decide +kernel

theorem expected_values :
    carryExpected.toNat = 22231542348441172891284605428601131325858369222844048941495033842303251860735 ∧
    bindingExpected.toNat = 15353493766103302224812374511606760489073247795810767472367693728416386214313 := by
  decide +kernel

theorem broken_carry_value :
    carryResult.toNat = 10270262512448670424778123679734987708571182949051932638396965445873668699797 := by
  decide +kernel

theorem broken_binding_value : bindingResult.toNat = 0 := by decide +kernel

theorem broken_carry_is_semantically_wrong : carryResult ≠ carryExpected := by decide +kernel
theorem broken_binding_is_semantically_wrong : bindingResult ≠ bindingExpected := by decide +kernel

#print axioms witness_words_bounded
#print axioms witness_field_inputs
#print axioms witness_input_values
#print axioms unmodified_models
#print axioms expected_values
#print axioms broken_carry_value
#print axioms broken_binding_value
#print axioms broken_carry_is_semantically_wrong
#print axioms broken_binding_is_semantically_wrong

end PastaBridge.FormalMulNegatives
