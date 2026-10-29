import KrakenRun
import Retained
import KrakenBinding
import CheckAddition
import AdditionStep

/-!
Allocation and frame properties for the program retained from Charon. Program
instantiation traverses the parsed AST; this file contains no instruction list.
Unsupported instructions and directives return an explicit error.
-/
namespace PastaBridge.AdditionMachine

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Binding := Fin 15 → XReg

def canonicalOperand : XReg → Option (Fin 15)
  | .X0 => some 0 | .X1 => some 1 | .X2 => some 2 | .X3 => some 3
  | .X4 => some 4 | .X5 => some 5 | .X6 => some 6 | .X7 => some 7
  | .X8 => some 8 | .X9 => some 9 | .X10 => some 10 | .X11 => some 11
  | .X12 => some 12 | .X13 => some 13 | .X14 => some 14
  | _ => none

def renameRegister (binding : Binding) (r : RegOrZr .W64) : Except String (RegOrZr .W64) :=
  match r with
  | .low .XZR _ => .ok (.low .XZR .W64)
  | .low (.reg r) _ =>
    match canonicalOperand r with
    | some i => .ok (.low (.reg (binding i)) .W64)
    | none => .error "register outside the retained addition operand domain"

def instantiateOperation (binding : Binding) : Operation .W64 → Except String (Operation .W64)
  | .ADDS_s d a b => do
    if b.shift != .LSL || b.amount != 0 then throw "unsupported shift"
    return .ADDS_s (← renameRegister binding d) (← renameRegister binding a)
      { b with reg := ← renameRegister binding b.reg }
  | .ADCS d a b => do return .ADCS (← renameRegister binding d) (← renameRegister binding a) (← renameRegister binding b)
  | .ADC d a b => do return .ADC (← renameRegister binding d) (← renameRegister binding a) (← renameRegister binding b)
  | .SUBS_s d a b => do
    if b.shift != .LSL || b.amount != 0 then throw "unsupported shift"
    return .SUBS_s (← renameRegister binding d) (← renameRegister binding a)
      { b with reg := ← renameRegister binding b.reg }
  | .SBCS d a b => do return .SBCS (← renameRegister binding d) (← renameRegister binding a) (← renameRegister binding b)
  | .CSEL d a b .CS => do return .CSEL (← renameRegister binding d) (← renameRegister binding a) (← renameRegister binding b) .CS
  | _ => .error "unsupported addition operation"

def instantiateDirective (binding : Binding) : Directive → Except String Directive
  | .instr ⟨.W64, operation⟩ => do return .instr ⟨.W64, ← instantiateOperation binding operation⟩
  | _ => .error "unsupported directive or width"

def instantiatedProgram (binding : Binding) : Except String Program :=
  retainedAdditionProgram.mapM (instantiateDirective binding)

/- The following total specialization is used only on this retained program.
`instantiation_certificate` checks it against the rejecting renamer above for
every binding, so none of its otherwise/default cases are trusted. -/
private def renameKnownRegister (binding : Binding) : RegOrZr .W64 → RegOrZr .W64
  | .low .XZR _ => .low .XZR .W64
  | .low (.reg r) _ => .low (.reg ((canonicalOperand r).map binding |>.getD r)) .W64

private def renameKnownOperation (binding : Binding) : Operation .W64 → Operation .W64
  | .ADDS_s d a b => .ADDS_s (renameKnownRegister binding d) (renameKnownRegister binding a)
      { b with reg := renameKnownRegister binding b.reg }
  | .ADCS d a b => .ADCS (renameKnownRegister binding d) (renameKnownRegister binding a) (renameKnownRegister binding b)
  | .ADC d a b => .ADC (renameKnownRegister binding d) (renameKnownRegister binding a) (renameKnownRegister binding b)
  | .SUBS_s d a b => .SUBS_s (renameKnownRegister binding d) (renameKnownRegister binding a)
      { b with reg := renameKnownRegister binding b.reg }
  | .SBCS d a b => .SBCS (renameKnownRegister binding d) (renameKnownRegister binding a) (renameKnownRegister binding b)
  | .CSEL d a b condition => .CSEL (renameKnownRegister binding d) (renameKnownRegister binding a) (renameKnownRegister binding b) condition
  | other => other

private def renameKnownDirective (binding : Binding) : Directive → Directive
  | .instr ⟨.W64, operation⟩ => .instr ⟨.W64, renameKnownOperation binding operation⟩
  | other => other

def boundProgram (binding : Binding) : Program := retainedAdditionProgram.map (renameKnownDirective binding)

theorem instantiation_certificate (binding : Binding) :
    instantiatedProgram binding = .ok (boundProgram binding) := by rfl

def runWithBinding (binding : Binding) (state : MachineData) : Except String MachineData := do
  run (← instantiatedProgram binding) state

theorem run_binding (binding : Binding) (state : MachineData) :
    runWithBinding binding state = run (boundProgram binding) state := by
  rw [runWithBinding, instantiation_certificate]
  rfl

def written (i : Fin 15) : Bool := i.val < 4 || 11 ≤ i.val

def modeWrites : OperandMode → Bool
  | .input => false
  | _ => true

theorem written_matches_checked_modes : ∀ i : Fin 15,
    written i = modeWrites (additionExpectedOperandMode i) := by decide

theorem retained_written_mask :
    (operandModesFromArtifact retainedCharonArtifact "add").map (List.map modeWrites) =
      .ok (List.ofFn written) := by
  rw [addition_operand_metadata_matches]
  change Except.ok ((List.ofFn additionExpectedOperandMode).map modeWrites) =
    (Except.ok (List.ofFn written) : Except String (List Bool))
  congr 1

def Admissible (binding : Binding) : Prop := KrakenBinding.Admissible written binding

attribute [local irreducible] Reg64s.setXReg Reg64s.getXReg

def canonicalBinding (i : Fin 15) : XReg :=
  match i.val with
  | 0 => .X0 | 1 => .X1 | 2 => .X2 | 3 => .X3 | 4 => .X4
  | 5 => .X5 | 6 => .X6 | 7 => .X7 | 8 => .X8 | 9 => .X9
  | 10 => .X10 | 11 => .X11 | 12 => .X12 | 13 => .X13 | _ => .X14

theorem canonical_identity :
    instantiatedProgram canonicalBinding = .ok retainedAdditionProgram := by
  rfl

theorem canonical_inverse : ∀ i : Fin 15,
    canonicalOperand (canonicalBinding i) = some i := by
  decide

theorem canonical_separated : KrakenBinding.Separated written canonicalBinding := by
  intro x y _ h
  have h' := congrArg canonicalOperand h
  rw [canonical_inverse, canonical_inverse] at h'
  exact Option.some.inj h'


theorem canonical_run_identity (state : MachineData) :
    runWithBinding canonicalBinding state = run retainedAdditionProgram state := by
  simp only [runWithBinding, canonical_identity]
  rfl

theorem binding_memory_frame (binding : Binding) (state : MachineData) :
    (runWithBinding binding state).map MachineData.dmem = .ok state.dmem := by
  rfl


#print axioms instantiation_certificate
#print axioms canonical_identity
#print axioms canonical_inverse
#print axioms canonical_separated
#print axioms binding_memory_frame
#print axioms written_matches_checked_modes
#print axioms retained_written_mask
end PastaBridge.AdditionMachine

namespace PastaBridge.AdditionLift
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Binding := AdditionMachine.Binding

structure Decoded where
  kind : AdditionStep.Kind
  destination : Fin 15
  first : AdditionStep.Source
  second : AdditionStep.Source
  destinationWritten : AdditionStep.written destination = true

def decodeSource : RegOrZr .W64 → Except String AdditionStep.Source
  | .low .XZR _ => .ok .zero
  | .low (.reg register) _ =>
    match AdditionMachine.canonicalOperand register with
    | some index => .ok (.operand index)
    | none => .error "source outside extracted operand domain"

def decodeDestination (register : RegOrZr .W64) :
    Except String { i : Fin 15 // AdditionStep.written i = true } := do
  match ← decodeSource register with
  | .zero => throw "zero register destination unsupported"
  | .operand i =>
    if h : AdditionStep.written i = true then return ⟨i, h⟩
    else throw "destination is not an extracted output"

def decoded (kind : AdditionStep.Kind) (destination first second : RegOrZr .W64) :
    Except String Decoded := do
  let destination ← decodeDestination destination
  let first ← decodeSource first
  let second ← decodeSource second
  return ⟨kind, destination.val, first, second, destination.property⟩

def decodeOperation : Operation .W64 → Except String Decoded
  | .ADDS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported shift"
    decoded .adds d a b.reg
  | .ADCS d a b => decoded .adcs d a b
  | .ADC d a b => decoded .adc d a b
  | .SUBS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported shift"
    decoded .subs d a b.reg
  | .SBCS d a b => decoded .sbcs d a b
  | .CSEL d a b .CS => decoded .csel d a b
  | _ => .error "unsupported addition instruction"

def decodeDirective : Directive → Except String Decoded
  | .instr ⟨.W64, operation⟩ => decodeOperation operation
  | _ => .error "unsupported directive or width"

def decodedProgram : List Decoded :=
  (retainedAdditionProgram.mapM decodeDirective).toOption.getD []

theorem decoding_certificate :
    retainedAdditionProgram.mapM decodeDirective = .ok decodedProgram := by rfl

def encode (binding : Binding) (program : List Decoded) : Program :=
  program.map fun instruction => .instr (AdditionStep.instruction instruction.kind binding
    instruction.destination instruction.first instruction.second)

theorem encoding_certificate (binding : Binding) :
    encode binding decodedProgram = AdditionMachine.boundProgram binding := by rfl

def sequence (binding : Binding) : List Decoded → MachineData → Except String MachineData
  | [], state => .ok state
  | instruction :: remaining, state => do
    let next ← AdditionStep.step instruction.kind binding instruction.destination
      instruction.first instruction.second state
    sequence binding remaining next

def execFrom [Labels] (binding : Binding) (program : List Decoded)
    (pc : Int64) (state : MachineData) : Except String MachineData :=
  finishEffects ((encode binding program).length + 1)
    (Directives.interp ((encode binding program).map (fun directive => (directive, 4)))
      state pc (fun pc state => .done (state, pc)))

theorem execFrom_is_sequence [Labels] (binding : Binding) (program : List Decoded)
    (pc : Int64) (state : MachineData) :
    execFrom binding program pc state = sequence binding program state := by
  induction program generalizing pc state with
  | nil => rfl
  | cons instruction remaining ih =>
    have memory := AdditionStep.memory_frame instruction.kind binding instruction.destination
      instruction.first instruction.second state
    cases executed : AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second state with
    | error error =>
      rw [executed] at memory
      change (Except.error error : Except String DataMem) = .ok state.dmem at memory
      cases memory
    | ok after =>
      have interp := AdditionStep.interp_of_step instruction.kind binding instruction.destination
        instruction.first instruction.second state after executed
        (.mk pc (pc + .ofNat 4))
        (fun next => Directives.interp
          ((encode binding remaining).map (fun directive => (directive, 4)))
          next (pc + .ofNat 4) (fun pc state => .done (state, pc)))
        (fun pc state => .done (state, pc))
      simp only [execFrom, encode, List.map_cons, List.length_cons,
        Directives.interp, Directive.interp] at ⊢
      dsimp only [encode] at interp
      rw [interp]
      change execFrom binding remaining (pc + .ofNat 4) after =
        sequence binding (instruction :: remaining) state
      rw [sequence, executed]
      exact ih (pc + .ofNat 4) after

theorem full_run_is_sequence (binding : Binding) (state : MachineData) :
    run (AdditionMachine.boundProgram binding) state = sequence binding decodedProgram state := by
  rw [← encoding_certificate]
  letI : Labels := { label _ := 0 }
  exact execFrom_is_sequence binding decodedProgram 0 state

theorem sequence_preserves (program : List Decoded) (binding canonical : Binding)
    (separated : KrakenBinding.Separated AdditionStep.written binding)
    (canonicalSeparated : KrakenBinding.Separated AdditionStep.written canonical)
    (actual reference : MachineData)
    (related : AdditionStep.Rel binding canonical actual reference) :
    AdditionStep.LiftedRel binding canonical
      (sequence binding program actual) (sequence canonical program reference) := by
  induction program generalizing actual reference with
  | nil => exact related
  | cons instruction remaining ih =>
    have nextRelated := AdditionStep.preserve instruction.kind binding canonical actual reference
      separated canonicalSeparated related instruction.destination instruction.destinationWritten
      instruction.first instruction.second
    cases ha : AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second actual with
    | error error => simp [AdditionStep.LiftedRel, ha] at nextRelated
    | ok actual' =>
      cases hr : AdditionStep.step instruction.kind canonical instruction.destination
          instruction.first instruction.second reference with
      | error error => simp [AdditionStep.LiftedRel, ha, hr] at nextRelated
      | ok reference' =>
        have relates : AdditionStep.Rel binding canonical actual' reference' := by
          simpa only [AdditionStep.LiftedRel, ha, hr] using nextRelated
        simp only [sequence, ha, hr]
        change AdditionStep.LiftedRel binding canonical
          (sequence binding remaining actual') (sequence canonical remaining reference')
        exact ih actual' reference' relates

def canonicalState (binding : Binding) (state : MachineData) : MachineData :=
  { state with regs := { state.regs with
    X0 := state.regs.getXReg (binding 0), X1 := state.regs.getXReg (binding 1),
    X2 := state.regs.getXReg (binding 2), X3 := state.regs.getXReg (binding 3),
    X4 := state.regs.getXReg (binding 4), X5 := state.regs.getXReg (binding 5),
    X6 := state.regs.getXReg (binding 6), X7 := state.regs.getXReg (binding 7),
    X8 := state.regs.getXReg (binding 8), X9 := state.regs.getXReg (binding 9),
    X10 := state.regs.getXReg (binding 10), X11 := state.regs.getXReg (binding 11),
    X12 := state.regs.getXReg (binding 12), X13 := state.regs.getXReg (binding 13),
    X14 := state.regs.getXReg (binding 14) } }

theorem initial_relation (binding : Binding) (state : MachineData) :
    AdditionStep.Rel binding AdditionMachine.canonicalBinding state
      (canonicalState binding state) := by
  constructor
  · intro i
    rcases i with ⟨n, hn⟩
    have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
        n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 := by omega
    rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst n; rfl
  · rfl

theorem canonical_bound_identity :
    AdditionMachine.boundProgram AdditionMachine.canonicalBinding = retainedAdditionProgram := by rfl

theorem all_bindings_simulation (binding : Binding)
    (separated : KrakenBinding.Separated AdditionStep.written binding) (state : MachineData) :
    AdditionStep.LiftedRel binding AdditionMachine.canonicalBinding
      (AdditionMachine.runWithBinding binding state)
      (run retainedAdditionProgram (canonicalState binding state)) := by
  rw [AdditionMachine.run_binding, ← canonical_bound_identity,
    full_run_is_sequence, full_run_is_sequence]
  exact sequence_preserves decodedProgram binding AdditionMachine.canonicalBinding separated
    AdditionMachine.canonical_separated state (canonicalState binding state)
    (initial_relation binding state)

#print axioms decoding_certificate
#print axioms encoding_certificate
#print axioms full_run_is_sequence
#print axioms sequence_preserves
#print axioms initial_relation
#print axioms all_bindings_simulation
end PastaBridge.AdditionLift

namespace PastaBridge.AdditionLift

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sequence_observation {α : Type} (binding : Binding) (program : List Decoded)
    (observation : MachineData → α)
    (preserved : ∀ instruction : Decoded, ∀ state : MachineData,
      (AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second state).map observation = .ok (observation state))
    (state : MachineData) :
    (sequence binding program state).map observation = .ok (observation state) := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction remaining ih =>
    have frame := preserved instruction state
    cases executed : AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second state with
    | error error =>
      rw [executed] at frame
      change (Except.error error : Except String α) = .ok (observation state) at frame
      cases frame
    | ok after =>
      rw [executed] at frame
      have same : observation after = observation state := Except.ok.inj frame
      simp only [sequence, executed]
      change (sequence binding remaining after).map observation = .ok (observation state)
      rw [ih after, same]

theorem binding_stack_frame (binding : Binding) (state : MachineData) :
    (AdditionMachine.runWithBinding binding state).map (fun final => final.regs.SP) =
      .ok state.regs.SP := by
  rw [AdditionMachine.run_binding, full_run_is_sequence]
  exact sequence_observation binding decodedProgram (fun final => final.regs.SP)
    (fun instruction state => AdditionStep.stack_frame instruction.kind binding
      instruction.destination instruction.first instruction.second state) state

theorem binding_register_frame (binding : Binding) (state : MachineData) (queried : XReg)
    (isProtected : ∀ destination : Fin 15, AdditionStep.written destination = true →
      queried ≠ binding destination) :
    (AdditionMachine.runWithBinding binding state).map
      (fun final => final.regs.getXReg queried) = .ok (state.regs.getXReg queried) := by
  rw [AdditionMachine.run_binding, full_run_is_sequence]
  exact sequence_observation binding decodedProgram (fun final => final.regs.getXReg queried)
    (fun instruction state => AdditionStep.register_frame instruction.kind binding
      instruction.destination instruction.first instruction.second state queried
      (isProtected instruction.destination instruction.destinationWritten)) state

theorem binding_readonly_frame (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated AdditionStep.written binding)
    (queried : Fin 15) (readonly : AdditionStep.written queried = false) :
    (AdditionMachine.runWithBinding binding state).map
      (fun final => final.regs.getXReg (binding queried)) =
        .ok (state.regs.getXReg (binding queried)) := by
  rw [AdditionMachine.run_binding, full_run_is_sequence]
  exact sequence_observation binding decodedProgram (fun final => final.regs.getXReg (binding queried))
    (fun instruction state => AdditionStep.readonly_frame instruction.kind binding
      instruction.destination instruction.first instruction.second state separated
      instruction.destinationWritten queried readonly) state

#print axioms sequence_observation
#print axioms binding_stack_frame
#print axioms binding_register_frame
#print axioms binding_readonly_frame

end PastaBridge.AdditionLift
