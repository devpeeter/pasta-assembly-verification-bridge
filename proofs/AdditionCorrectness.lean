import AdditionMachine
import ArithmeticAudit
import AdditionNatLift
import BindingArtifact

/-!
Field correctness and frame properties of the retained addition program for
every admissible physical register allocation. The internal composition lemma
is instantiated with the checked actual Kraken-to-Pasta correspondence.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PastaBridge.AdditionCorrectness

open PastaCurves

abbrev Binding := AdditionMachine.Binding

def lhs (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 0)).toNat, (state.regs.getXReg (binding 1)).toNat,
    (state.regs.getXReg (binding 2)).toNat, (state.regs.getXReg (binding 3)).toNat⟩

def rhs (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 4)).toNat, (state.regs.getXReg (binding 5)).toNat,
    (state.regs.getXReg (binding 6)).toNat, (state.regs.getXReg (binding 7)).toNat⟩

def modulus (binding : Binding) (state : MachineData) : Limbs :=
  ⟨(state.regs.getXReg (binding 8)).toNat, (state.regs.getXReg (binding 9)).toNat,
    0, (state.regs.getXReg (binding 10)).toNat⟩

abbrev output := lhs

theorem lhs_bounded (binding : Binding) (state : MachineData) :
    (lhs binding state).Bounded := by
  exact ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

theorem rhs_bounded (binding : Binding) (state : MachineData) :
    (rhs binding state).Bounded := by
  exact ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

def Protected (binding : Binding) (queried : XReg) : Prop :=
  ∀ destination : Fin 15, AdditionStep.written destination = true → queried ≠ binding destination

structure Frames (binding : Binding) (before after : MachineData) : Prop where
  memory : after.dmem = before.dmem
  stack : after.regs.SP = before.regs.SP
  protected_registers : ∀ queried, Protected binding queried →
    after.regs.getXReg queried = before.regs.getXReg queried
  readonly_registers : ∀ queried : Fin 15, AdditionStep.written queried = false →
    after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried)
  protected_x19 : Protected binding .X19 → after.regs.X19 = before.regs.X19
  protected_x29 : after.regs.X29 = before.regs.X29

theorem execution_frames (binding : Binding) (before after : MachineData)
    (admissible : AdditionMachine.Admissible binding)
    (executed : AdditionMachine.runWithBinding binding before = .ok after) :
    Frames binding before after := by
  have memory := AdditionMachine.binding_memory_frame binding before
  rw [executed] at memory
  have stack := AdditionLift.binding_stack_frame binding before
  rw [executed] at stack
  have protectedFrames : ∀ queried, Protected binding queried →
      after.regs.getXReg queried = before.regs.getXReg queried := by
    intro queried isProtected
    have frame := AdditionLift.binding_register_frame binding before queried isProtected
    rw [executed] at frame
    exact Except.ok.inj frame
  have readonlyFrames : ∀ queried : Fin 15, AdditionStep.written queried = false →
      after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried) := by
    intro queried readonly
    have frame := AdditionLift.binding_readonly_frame binding before admissible.2 queried readonly
    rw [executed] at frame
    exact Except.ok.inj frame
  have x29 : Protected binding .X29 := by
    intro destination _ equality
    exact (admissible.1 destination) equality.symm
  exact ⟨Except.ok.inj memory, Except.ok.inj stack, protectedFrames, readonlyFrames,
    protectedFrames .X19, protectedFrames .X29 x29⟩

#print axioms lhs_bounded
#print axioms rhs_bounded
#print axioms execution_frames

end PastaBridge.AdditionCorrectness

namespace PastaBridge.AdditionCorrectness

open PastaCurves

structure InputContract (field : PastaField) (binding : Binding) (state : MachineData) : Prop where
  modulus_eq : modulus binding state = field.modulus
  lhs_lt : (lhs binding state).toNat < field.modulus.toNat
  rhs_lt : (rhs binding state).toNat < field.modulus.toNat

structure Postcondition (field : PastaField) (binding : Binding)
    (before after : MachineData) : Prop where
  model_eq : output binding after = AArch64.addMod (lhs binding before) (rhs binding before) field.modulus
  bounded : (output binding after).Bounded
  canonical : (output binding after).toNat < field.modulus.toNat
  congruent : (output binding after).toNat ≡
    (lhs binding before).toNat + (rhs binding before).toNat [MOD field.modulus.toNat]
  memory : after.dmem = before.dmem
  stack : after.regs.SP = before.regs.SP
  protected_registers : ∀ queried, Protected binding queried →
    after.regs.getXReg queried = before.regs.getXReg queried
  readonly_registers : ∀ queried : Fin 15, AdditionStep.written queried = false →
    after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried)
  protected_x19 : Protected binding .X19 → after.regs.X19 = before.regs.X19
  protected_x29 : after.regs.X29 = before.regs.X29
  retained_template : BindingArtifact.renderArtifactWithBinding binding retainedCharonArtifact "add" =
    serializeAdditionProgram (AdditionMachine.boundProgram binding)
  operand_metadata : operandModesFromArtifact retainedCharonArtifact "add" =
    .ok (List.ofFn additionExpectedOperandMode)

private def CanonicalCorrespondence : Prop := ∀ state : MachineData,
  (run retainedAdditionProgram state).map (output AdditionMachine.canonicalBinding) =
    .ok (AArch64.addMod (lhs AdditionMachine.canonicalBinding state)
      (rhs AdditionMachine.canonicalBinding state) (modulus AdditionMachine.canonicalBinding state))

theorem canonical_lhs (binding : Binding) (state : MachineData) :
    lhs AdditionMachine.canonicalBinding (AdditionLift.canonicalState binding state) = lhs binding state := rfl

theorem canonical_rhs (binding : Binding) (state : MachineData) :
    rhs AdditionMachine.canonicalBinding (AdditionLift.canonicalState binding state) = rhs binding state := rfl

theorem canonical_modulus (binding : Binding) (state : MachineData) :
    modulus AdditionMachine.canonicalBinding (AdditionLift.canonicalState binding state) =
      modulus binding state := rfl

private theorem field_endpoint_of_canonical
    (correspondence : CanonicalCorrespondence)
    (field : PastaField) (binding : Binding) (state : MachineData)
    (admissible : AdditionMachine.Admissible binding)
    (inputs : InputContract field binding state) :
    ∃ after : MachineData, AdditionMachine.runWithBinding binding state = .ok after ∧
      Postcondition field binding state after := by
  have related := AdditionLift.all_bindings_simulation binding admissible.2 state
  obtain ⟨after, reference, executed, referenceExecuted, finalRelated⟩ :=
    AdditionStep.related_results_exist binding AdditionMachine.canonicalBinding _ _ related
  have canonicalModel := correspondence (AdditionLift.canonicalState binding state)
  rw [referenceExecuted] at canonicalModel
  have canonicalOutput := Except.ok.inj canonicalModel
  have outputsEqual : output binding after = output AdditionMachine.canonicalBinding reference := by
    simp only [output, lhs, finalRelated.1 0, finalRelated.1 1,
      finalRelated.1 2, finalRelated.1 3]
  have model : output binding after =
      AArch64.addMod (lhs binding state) (rhs binding state) field.modulus := by
    rw [outputsEqual, canonicalOutput, canonical_lhs, canonical_rhs, canonical_modulus, inputs.modulus_eq]
  have fieldSpec := PastaAssemblyBridge.Arithmetic.addition field (lhs binding state) (rhs binding state)
    (lhs_bounded binding state) (rhs_bounded binding state) inputs.lhs_lt inputs.rhs_lt
  change (AArch64.addMod (lhs binding state) (rhs binding state) field.modulus).Bounded ∧
    (AArch64.addMod (lhs binding state) (rhs binding state) field.modulus).toNat < field.modulus.toNat ∧
    (AArch64.addMod (lhs binding state) (rhs binding state) field.modulus).toNat ≡
      (lhs binding state).toNat + (rhs binding state).toNat [MOD field.modulus.toNat] at fieldSpec
  rw [← model] at fieldSpec
  have frames := execution_frames binding state after admissible executed
  exact ⟨after, executed, ⟨model, fieldSpec.1, fieldSpec.2.1, fieldSpec.2.2,
    frames.memory, frames.stack, frames.protected_registers, frames.readonly_registers,
    frames.protected_x19, frames.protected_x29,
    BindingArtifact.bound_program_matches_template binding admissible.1,
    addition_operand_metadata_matches⟩⟩


end PastaBridge.AdditionCorrectness

namespace PastaBridge.AdditionCorrectness

private theorem checked_canonical_correspondence : CanonicalCorrespondence := by
  intro state
  have model := AdditionNat.all_bindings_model AdditionMachine.canonicalBinding state
    AdditionMachine.canonical_separated
  rw [AdditionMachine.canonical_run_identity] at model
  exact model

theorem addition_correct (field : PastaCurves.PastaField) (binding : Binding) (state : MachineData)
    (admissible : AdditionMachine.Admissible binding)
    (inputs : InputContract field binding state) :
    ∃ after : MachineData, AdditionMachine.runWithBinding binding state = .ok after ∧
      Postcondition field binding state after :=
  field_endpoint_of_canonical checked_canonical_correspondence field binding state admissible inputs

#print axioms addition_correct

#check addition_correct PastaCurves.pallasBase
#check addition_correct PastaCurves.vestaBase

end PastaBridge.AdditionCorrectness
