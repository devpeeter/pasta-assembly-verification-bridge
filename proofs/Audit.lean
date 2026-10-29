import ArithmeticAudit
import KrakenWord
import KrakenBinding
import WordCorrespondence
import CheckAddition
import AdditionMachine
import AdditionStep
import BindingArtifact
import AdditionNatSequence
import AdditionNatLift
import AdditionCorrectness

/-!
Run this module after rebuilding its imports. Each printed census belongs to the
exact declaration named below; it does not establish missing bridge endpoints.
-/
#print axioms PastaAssemblyBridge.Arithmetic.addition
#print axioms PastaAssemblyBridge.Arithmetic.multiplication

#check PastaAssemblyBridge.Arithmetic.addition PastaCurves.pallasBase
#check PastaAssemblyBridge.Arithmetic.addition PastaCurves.vestaBase
#check PastaAssemblyBridge.Arithmetic.multiplication PastaCurves.pallasBase
#check PastaAssemblyBridge.Arithmetic.multiplication PastaCurves.vestaBase

#print axioms PastaBridge.addition_artifact_matches_retained_program
#print axioms PastaBridge.addition_operand_metadata_matches
#print axioms PastaBridge.AdditionMachine.instantiation_certificate
#print axioms PastaBridge.AdditionMachine.binding_memory_frame

#print axioms PastaBridge.AdditionStep.preserve
#print axioms PastaBridge.AdditionStep.interp_of_step

#print axioms PastaBridge.AdditionLift.all_bindings_simulation
#print axioms PastaBridge.AdditionLift.binding_stack_frame
#print axioms PastaBridge.AdditionLift.binding_register_frame
#print axioms PastaBridge.AdditionLift.binding_readonly_frame

#print axioms PastaBridge.BindingArtifact.retained_pieces_match_artifact
#print axioms PastaBridge.BindingArtifact.bound_program_matches_template

#print axioms PastaBridge.AdditionNat.step_project
#print axioms PastaBridge.AdditionNat.sequence_project

/- A hidden correspondence hypothesis would make this assignment fail. -/
theorem addition_target_type :
    ∀ (field : PastaCurves.PastaField)
      (binding : PastaBridge.AdditionMachine.Binding) (state : MachineData),
      PastaBridge.AdditionMachine.Admissible binding →
      PastaBridge.AdditionCorrectness.InputContract field binding state →
      ∃ after : MachineData,
        PastaBridge.AdditionMachine.runWithBinding binding state = .ok after ∧
        PastaBridge.AdditionCorrectness.Postcondition field binding state after :=
  PastaBridge.AdditionCorrectness.addition_correct

#print PastaBridge.AdditionMachine.Admissible
#print PastaBridge.AdditionCorrectness.InputContract
#print PastaBridge.AdditionCorrectness.Protected
#print PastaBridge.AdditionCorrectness.Postcondition
#check PastaBridge.AdditionCorrectness.addition_correct PastaCurves.pallasBase
#check PastaBridge.AdditionCorrectness.addition_correct PastaCurves.vestaBase
#print axioms addition_target_type
#print axioms PastaBridge.AdditionCorrectness.addition_correct
#print axioms PastaBridge.AdditionNat.all_bindings_model
