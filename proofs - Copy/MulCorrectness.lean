import MulMachine
import ArithmeticAudit
import MulNatLift
import MulBindingArtifact
import MulCertificate

/-!
Field correctness and frame properties of the complete retained multiplication
program under every admissible physical register allocation. The internal
composition is instantiated with the checked actual Kraken-to-Pasta model law.
-/

namespace PastaBridge.MulCorrectness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PastaCurves
abbrev Binding := MulStep.Binding

attribute [local irreducible] MulMachine.runWithBinding

def lhs (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 0)).toNat, (state.regs.getXReg (binding 1)).toNat,
    (state.regs.getXReg (binding 2)).toNat, (state.regs.getXReg (binding 3)).toNat⟩

def rhs (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 4)).toNat, (state.regs.getXReg (binding 5)).toNat,
    (state.regs.getXReg (binding 6)).toNat, (state.regs.getXReg (binding 7)).toNat⟩

def modulus (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 8)).toNat, (state.regs.getXReg (binding 9)).toNat, 0, 2^62⟩

def inv (binding : Binding) (state : MachineData) : Nat :=
  (state.regs.getXReg (binding 10)).toNat

def output (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 16)).toNat, (state.regs.getXReg (binding 17)).toNat,
    (state.regs.getXReg (binding 18)).toNat, (state.regs.getXReg (binding 19)).toNat⟩

theorem lhs_bounded (binding : Binding) (state : MachineData) : (lhs binding state).Bounded :=
  ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

theorem rhs_bounded (binding : Binding) (state : MachineData) : (rhs binding state).Bounded :=
  ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

def Protected (binding : Binding) (queried : XReg) : Prop :=
  ∀ destination : Fin 21, MulStep.written destination = true → queried ≠ binding destination

structure Frames (binding : Binding) (before after : MachineData) : Prop where
  memory : after.dmem = before.dmem
  stack : after.regs.SP = before.regs.SP
  protected_registers : ∀ queried, Protected binding queried →
    after.regs.getXReg queried = before.regs.getXReg queried
  readonly_registers : ∀ queried : Fin 21, MulStep.written queried = false →
    after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried)
  protected_x19 : Protected binding .X19 → after.regs.X19 = before.regs.X19
  protected_x29 : after.regs.X29 = before.regs.X29

theorem execution_frames (binding : Binding) (before after : MachineData)
    (admissible : MulMachine.Admissible binding)
    (executed : MulMachine.runWithBinding binding before = .ok after) :
    Frames binding before after := by
  have memory := MulMachine.binding_memory_frame binding before
  rw [executed] at memory
  have stack := MulMachine.binding_stack_frame binding before
  rw [executed] at stack
  have protectedFrames : ∀ queried, Protected binding queried →
      after.regs.getXReg queried = before.regs.getXReg queried := by
    intro queried isProtected
    have frame := MulMachine.binding_register_frame binding before queried isProtected
    rw [executed] at frame
    exact Except.ok.inj frame
  have readonlyFrames : ∀ queried : Fin 21, MulStep.written queried = false →
      after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried) := by
    intro queried readonly
    have frame := MulMachine.binding_readonly_frame binding before admissible.2 queried readonly
    rw [executed] at frame
    exact Except.ok.inj frame
  have x29 : Protected binding .X29 := by
    intro destination _ equality
    exact admissible.1 destination equality.symm
  exact ⟨Except.ok.inj memory, Except.ok.inj stack, protectedFrames, readonlyFrames,
    protectedFrames .X19, protectedFrames .X29 x29⟩

structure InputContract (field : PastaField) (binding : Binding) (state : MachineData) : Prop where
  modulus_eq : modulus binding state = field.modulus
  inv_eq : inv binding state = field.inv
  operands : mulContract (lhs binding state) (rhs binding state) field.modulus = true

structure ArithmeticPostcondition (field : PastaField) (binding : Binding)
    (before after : MachineData) : Prop where
  model_eq : output binding after =
    AArch64.mulMont (lhs binding before) (rhs binding before) field.modulus field.inv
  bounded : (output binding after).Bounded
  canonical : (output binding after).toNat < field.modulus.toNat
  congruent : 2^256 * (output binding after).toNat ≡
    (lhs binding before).toNat * (rhs binding before).toNat [MOD field.modulus.toNat]
  frames : Frames binding before after

private def ModelCorrespondence : Prop := ∀ (binding : Binding) (state : MachineData),
  KrakenBinding.Separated MulStep.written binding →
  (MulMachine.runWithBinding binding state).map (output binding) =
    .ok (AArch64.mulMont (lhs binding state) (rhs binding state)
      (modulus binding state) (inv binding state))

private theorem field_endpoint_of_model (correspondence : ModelCorrespondence)
    (field : PastaField) (binding : Binding) (state : MachineData)
    (admissible : MulMachine.Admissible binding)
    (inputs : InputContract field binding state) :
    ∃ after : MachineData, MulMachine.runWithBinding binding state = .ok after ∧
      ArithmeticPostcondition field binding state after := by
  have model := correspondence binding state admissible.2
  cases executed : MulMachine.runWithBinding binding state with
  | error error =>
    rw [executed] at model
    cases model
  | ok after =>
    rw [executed] at model
    have outputModel := Except.ok.inj model
    rw [inputs.modulus_eq, inputs.inv_eq] at outputModel
    have fieldSpec := PastaAssemblyBridge.Arithmetic.multiplication field
      (lhs binding state) (rhs binding state) (lhs_bounded binding state)
      (rhs_bounded binding state) inputs.operands
    change (AArch64.mulMont (lhs binding state) (rhs binding state) field.modulus field.inv).Bounded ∧
      (AArch64.mulMont (lhs binding state) (rhs binding state) field.modulus field.inv).toNat < field.modulus.toNat ∧
      2^256 * (AArch64.mulMont (lhs binding state) (rhs binding state) field.modulus field.inv).toNat ≡
        (lhs binding state).toNat * (rhs binding state).toNat [MOD field.modulus.toNat] at fieldSpec
    rw [← outputModel] at fieldSpec
    exact ⟨after, rfl, ⟨outputModel, fieldSpec.1, fieldSpec.2.1, fieldSpec.2.2,
      execution_frames binding state after admissible executed⟩⟩

#print axioms lhs_bounded
#print axioms rhs_bounded
#print axioms execution_frames

end PastaBridge.MulCorrectness


namespace PastaBridge.MulCorrectness

open PastaCurves

private theorem checked_model : ModelCorrespondence := by
  intro binding state separated
  exact MulNat.all_bindings_model binding state separated

structure Postcondition (field : PastaField) (binding : Binding)
    (before after : MachineData) : Prop where
  model_eq : output binding after =
    AArch64.mulMont (lhs binding before) (rhs binding before) field.modulus field.inv
  bounded : (output binding after).Bounded
  canonical : (output binding after).toNat < field.modulus.toNat
  congruent : 2^256 * (output binding after).toNat ≡
    (lhs binding before).toNat * (rhs binding before).toNat [MOD field.modulus.toNat]
  memory : after.dmem = before.dmem
  stack : after.regs.SP = before.regs.SP
  protected_registers : ∀ queried, Protected binding queried →
    after.regs.getXReg queried = before.regs.getXReg queried
  readonly_registers : ∀ queried : Fin 21, MulStep.written queried = false →
    after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried)
  protected_x19 : Protected binding .X19 → after.regs.X19 = before.regs.X19
  protected_x29 : after.regs.X29 = before.regs.X29
  retained_bytes : String.ofList retainedMultiplicationArtifactChars = retainedMultiplicationCharonArtifact
  retained_encoding : (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map
    StringBytes.bytes = .ok retainedMultiplicationArtifactBytes
  retained_template : MultiplicationArtifact.renderValue binding retainedMultiplicationArtifactValue =
    MultiplicationArtifact.serializeProgram (MulMachine.boundProgram binding)
  operand_metadata : MultiplicationArtifact.operandModes retainedMultiplicationArtifactValue =
    .ok (List.ofFn MultiplicationArtifact.expectedOperandMode)

theorem multiplication_correct (field : PastaField) (binding : Binding) (state : MachineData)
    (admissible : MulMachine.Admissible binding)
    (inputs : InputContract field binding state) :
    ∃ after : MachineData, MulMachine.runWithBinding binding state = .ok after ∧
      Postcondition field binding state after := by
  obtain ⟨after, executed, post⟩ := field_endpoint_of_model checked_model field binding state admissible inputs
  exact ⟨after, executed, ⟨post.model_eq, post.bounded, post.canonical, post.congruent,
    post.frames.memory, post.frames.stack, post.frames.protected_registers,
    post.frames.readonly_registers, post.frames.protected_x19, post.frames.protected_x29,
    multiplication_artifact_chars_readback, multiplication_value_encodes_retained_artifact,
    MulBindingArtifact.bound_program_matches_template binding admissible.1,
    multiplication_operand_metadata_matches⟩⟩

#print axioms multiplication_correct
#check multiplication_correct PastaCurves.pallasBase
#check multiplication_correct PastaCurves.vestaBase

end PastaBridge.MulCorrectness
