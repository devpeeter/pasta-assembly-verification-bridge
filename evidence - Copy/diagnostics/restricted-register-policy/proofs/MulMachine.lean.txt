import MulStep
import MulRetained

/-!
The retained parsed multiplication program is decoded, with explicit rejection,
into typed supported forms. Encoding is allocation-parametric; closed readback
certificates tie the complete program to the retained AST. No instruction list
is transcribed here.
-/
namespace PastaBridge.MulMachine

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MulStep
abbrev Binding := MulStep.Binding
abbrev Operand := MulStep.Operand
abbrev written := MulStep.written

def Admissible (binding : Binding) : Prop := KrakenBinding.Admissible written binding

def canonicalOperand : XReg → Option Operand
  | .X0 => some 0 | .X1 => some 1 | .X2 => some 2 | .X3 => some 3
  | .X4 => some 4 | .X5 => some 5 | .X6 => some 6 | .X7 => some 7
  | .X8 => some 8 | .X9 => some 9 | .X10 => some 10 | .X11 => some 11
  | .X12 => some 12 | .X13 => some 13 | .X14 => some 14 | .X15 => some 15
  | .X16 => some 16 | .X17 => some 17 | .X18 => some 18
  | .X20 => some 19 | .X21 => some 20
  | _ => none

abbrev canonicalBinding := MultiplicationArtifact.canonicalBinding

def decodeSource : RegOrZr .W64 → Except String Source
  | .low .XZR _ => .ok .zero
  | .low (.reg register) _ =>
    match canonicalOperand register with
    | some index => .ok (.operand index)
    | none => .error "source outside retained multiplication operand domain"

def decodePhysical : RegOrSp .W64 → Except String Operand
  | .low (.reg register) _ =>
    match canonicalOperand register with
    | some index => .ok index
    | none => .error "physical register outside retained multiplication operand domain"
  | .low .SP _ => .error "stack pointer operand unsupported"

def decodeDestination (register : RegOrZr .W64) : Except String Operand := do
  match ← decodeSource register with
  | .zero => throw "zero register destination requires the dedicated flag-setting form"
  | .operand index =>
    if written index then return index
    else throw "destination is not a retained multiplication output"

def decodeBinary (constructor : Operand → Source → Source → Instruction)
    (d a b : RegOrZr .W64) : Except String Instruction := do
  return constructor (← decodeDestination d) (← decodeSource a) (← decodeSource b)

def decodeShift (constructor : Operand → Source → Fin 64 → Instruction)
    (d : RegOrZr .W64) (source : ShiftRegExpr .W64) : Except String Instruction := do
  let destination ← decodeDestination d
  let a ← decodeSource source.reg
  if h : 0 ≤ source.amount.toInt ∧ source.amount.toInt < 64 then
    return constructor destination a ⟨source.amount.toInt.toNat, by omega⟩
  else throw "multiplication shift immediate outside 0..63"

def decodeOperation : Operation .W64 → Except String Instruction
  | .ADDS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported arithmetic shift"
    decodeBinary .adds d a b.reg
  | .ADCS d a b => decodeBinary .adcs d a b
  | .ADC d a b => decodeBinary .adc d a b
  | .SUBS_s d a b => do
    if b.amount != 0 || b.shift != .LSL then throw "unsupported arithmetic shift"
    decodeBinary .subs d a b.reg
  | .SBCS d a b => decodeBinary .sbcs d a b
  | .CSEL d a b .CC => decodeBinary .cselLo d a b
  | .MADD d a b (.low .XZR _) => decodeBinary .mul d a b
  | .UMULH d a b => decodeBinary .umulh d a b
  | .ORR_s d (.low .XZR _) source =>
    match source.shift with
    | .LSL => decodeShift .lsl d source
    | .LSR => decodeShift .lsr d source
    | _ => .error "unsupported multiplication logical shift"
  | .SUBS_e (.low .XZR _) a (.imm immediate) => do
    if immediate.imm != (1 : ConstExpr) || immediate.shift != .S0 then
      throw "unsupported multiplication flag-setting immediate"
    return .subsOne (← decodePhysical a)
  | .MOVZ d immediate .LSL48 => do
    if immediate != (0x4000 : ConstExpr) then throw "unsupported multiplication mask immediate"
    return .movMask (← decodeDestination d)
  | _ => .error "unsupported multiplication operation or operand form"

def decodeDirective : Directive → Except String Instruction
  | .instr ⟨.W64, operation⟩ => decodeOperation operation
  | _ => .error "unsupported multiplication directive or width"

def decodedProgram : List Instruction :=
  (retainedMultiplicationProgram.mapM decodeDirective).toOption.getD []

theorem decoding_certificate :
    retainedMultiplicationProgram.mapM decodeDirective = .ok decodedProgram := by rfl

def encode (binding : Binding) (program : List Instruction) : Program :=
  program.map fun operation => .instr (MulStep.instruction operation binding)

def instantiatedProgram (binding : Binding) : Except String Program := do
  let decoded ← retainedMultiplicationProgram.mapM decodeDirective
  return encode binding decoded

def boundProgram (binding : Binding) : Program := encode binding decodedProgram

theorem instantiation_certificate (binding : Binding) :
    instantiatedProgram binding = .ok (boundProgram binding) := by
  rw [instantiatedProgram, decoding_certificate]
  rfl

theorem canonical_identity : boundProgram canonicalBinding = retainedMultiplicationProgram := by rfl

def validBoolean (operation : Instruction) : Bool :=
  match destination operation with
  | none => true
  | some d => written d

theorem validBoolean_iff (operation : Instruction) : validBoolean operation = true ↔ Valid operation := by
  unfold validBoolean Valid
  cases h : destination operation <;> simp

theorem valid_certificate : decodedProgram.all validBoolean = true := by rfl

theorem decoded_valid (operation : Instruction) (member : operation ∈ decodedProgram) : Valid operation :=
  (validBoolean_iff operation).mp (List.all_eq_true.mp valid_certificate operation member)

def runWithBinding (binding : Binding) (state : MachineData) : Except String MachineData := do
  let program ← instantiatedProgram binding
  run program state

theorem run_binding (binding : Binding) (state : MachineData) :
    runWithBinding binding state = run (boundProgram binding) state := by
  rw [runWithBinding, instantiation_certificate]
  rfl

def sequence (binding : Binding) : List Instruction → MachineData → Except String MachineData
  | [], state => .ok state
  | operation :: remaining, state => do
    let after ← MulStep.step operation binding state
    sequence binding remaining after

def execFrom [Labels] (binding : Binding) (program : List Instruction)
    (pc : Int64) (state : MachineData) : Except String MachineData :=
  finishEffects ((encode binding program).length + 1)
    (Directives.interp ((encode binding program).map (fun directive => (directive, 4)))
      state pc (fun pc state => .done (state, pc)))

theorem execFrom_is_sequence [Labels] (binding : Binding) (program : List Instruction)
    (pc : Int64) (state : MachineData) :
    execFrom binding program pc state = sequence binding program state := by
  induction program generalizing pc state with
  | nil => rfl
  | cons operation remaining ih =>
    have memory := MulStep.memory_frame operation binding state
    cases executed : MulStep.step operation binding state with
    | error error =>
      rw [executed] at memory
      change (Except.error error : Except String DataMem) = .ok state.dmem at memory
      cases memory
    | ok after =>
      have interp := MulStep.interp_of_step operation binding state after executed
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
        sequence binding (operation :: remaining) state
      rw [sequence, executed]
      exact ih (pc + .ofNat 4) after

theorem full_run_is_sequence (binding : Binding) (state : MachineData) :
    run (boundProgram binding) state = sequence binding decodedProgram state := by
  letI : Labels := { label _ := 0 }
  exact execFrom_is_sequence binding decodedProgram 0 state

theorem sequence_observation {α : Type} (binding : Binding) (program : List Instruction)
    (observation : MachineData → α)
    (preserved : ∀ operation ∈ program, ∀ state : MachineData,
      (MulStep.step operation binding state).map observation = .ok (observation state))
    (state : MachineData) :
    (sequence binding program state).map observation = .ok (observation state) := by
  induction program generalizing state with
  | nil => rfl
  | cons operation remaining ih =>
    have frame := preserved operation (List.mem_cons_self) state
    cases executed : MulStep.step operation binding state with
    | error error =>
      rw [executed] at frame
      change (Except.error error : Except String α) = .ok (observation state) at frame
      cases frame
    | ok after =>
      rw [executed] at frame
      have same : observation after = observation state := Except.ok.inj frame
      simp only [sequence, executed]
      change (sequence binding remaining after).map observation = .ok (observation state)
      rw [ih (fun instruction member state => preserved instruction (List.mem_cons_of_mem _ member) state) after, same]

theorem binding_memory_frame (binding : Binding) (state : MachineData) :
    (runWithBinding binding state).map MachineData.dmem = .ok state.dmem := by
  rw [run_binding, full_run_is_sequence]
  exact sequence_observation binding decodedProgram MachineData.dmem
    (fun instruction _ state => MulStep.memory_frame instruction binding state) state

theorem binding_stack_frame (binding : Binding) (state : MachineData) :
    (runWithBinding binding state).map (fun after => after.regs.SP) = .ok state.regs.SP := by
  rw [run_binding, full_run_is_sequence]
  exact sequence_observation binding decodedProgram (fun after => after.regs.SP)
    (fun instruction _ state => MulStep.stack_frame instruction binding state) state

theorem binding_register_frame (binding : Binding) (state : MachineData) (queried : XReg)
    (isProtected : ∀ d, written d = true → queried ≠ binding d) :
    (runWithBinding binding state).map (fun after => after.regs.getXReg queried) =
      .ok (state.regs.getXReg queried) := by
  rw [run_binding, full_run_is_sequence]
  apply sequence_observation
  intro operation member before
  apply MulStep.register_frame
  intro d destination
  exact isProtected d (decoded_valid operation member d destination)

theorem binding_readonly_frame (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) (queried : Operand)
    (readonly : written queried = false) :
    (runWithBinding binding state).map (fun after => after.regs.getXReg (binding queried)) =
      .ok (state.regs.getXReg (binding queried)) := by
  rw [run_binding, full_run_is_sequence]
  exact sequence_observation binding decodedProgram (fun after => after.regs.getXReg (binding queried))
    (fun instruction member state => MulStep.readonly_frame instruction binding state separated
      (decoded_valid instruction member) queried readonly) state

#print axioms decoding_certificate
#print axioms instantiation_certificate
#print axioms canonical_identity
#print axioms valid_certificate
#print axioms decoded_valid
#print axioms full_run_is_sequence
#print axioms binding_memory_frame
#print axioms binding_stack_frame
#print axioms binding_register_frame
#print axioms binding_readonly_frame

end PastaBridge.MulMachine
