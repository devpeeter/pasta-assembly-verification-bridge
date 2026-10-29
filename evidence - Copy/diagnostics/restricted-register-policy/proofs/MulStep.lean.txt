import KrakenRun
import KrakenBinding

/-!
Typed supported forms for the retained multiplication routine. Every constructor
denotes an actual 64-bit Kraken instruction. Immediates have their real operand
types; the zero-register flag setter has no physical write destination.
-/
namespace PastaBridge.MulStep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Operand := Fin 21
abbrev Binding := Operand → XReg

def written (i : Operand) : Bool := 11 ≤ i.val

inductive Source where
  | operand (i : Operand)
  | zero
  deriving DecidableEq

inductive Instruction where
  | adds (destination : Operand) (first second : Source)
  | adcs (destination : Operand) (first second : Source)
  | adc (destination : Operand) (first second : Source)
  | subs (destination : Operand) (first second : Source)
  | sbcs (destination : Operand) (first second : Source)
  | cselLo (destination : Operand) (first second : Source)
  | mul (destination : Operand) (first second : Source)
  | umulh (destination : Operand) (first second : Source)
  | lsl (destination : Operand) (source : Source) (amount : Fin 64)
  | lsr (destination : Operand) (source : Source) (amount : Fin 64)
  | subsOne (source : Operand)
  | movMask (destination : Operand)
  deriving DecidableEq

def destination : Instruction → Option Operand
  | .adds d _ _ | .adcs d _ _ | .adc d _ _ | .subs d _ _ | .sbcs d _ _
  | .cselLo d _ _ | .mul d _ _ | .umulh d _ _ | .lsl d _ _ | .lsr d _ _
  | .movMask d => some d
  | .subsOne _ => none

def Valid (operation : Instruction) : Prop :=
  ∀ d, destination operation = some d → written d = true

def sourceRegister (binding : Binding) : Source → RegOrZr .W64
  | .operand i => .low (.reg (binding i)) .W64
  | .zero => .low .XZR .W64

def destinationRegister (binding : Binding) (d : Operand) : RegOrZr .W64 :=
  .low (.reg (binding d)) .W64

def physicalRegister (binding : Binding) (i : Operand) : RegOrSp .W64 :=
  .low (.reg (binding i)) .W64

def instruction (operation : Instruction) (binding : Binding) : Instr :=
  ⟨.W64, match operation with
  | .adds d a b => .ADDS_s (destinationRegister binding d) (sourceRegister binding a)
      { reg := sourceRegister binding b, amount := 0, shift := .LSL }
  | .adcs d a b => .ADCS (destinationRegister binding d) (sourceRegister binding a) (sourceRegister binding b)
  | .adc d a b => .ADC (destinationRegister binding d) (sourceRegister binding a) (sourceRegister binding b)
  | .subs d a b => .SUBS_s (destinationRegister binding d) (sourceRegister binding a)
      { reg := sourceRegister binding b, amount := 0, shift := .LSL }
  | .sbcs d a b => .SBCS (destinationRegister binding d) (sourceRegister binding a) (sourceRegister binding b)
  | .cselLo d a b => .CSEL (destinationRegister binding d) (sourceRegister binding a) (sourceRegister binding b) .CC
  | .mul d a b => .MADD (destinationRegister binding d) (sourceRegister binding a)
      (sourceRegister binding b) (.low .XZR .W64)
  | .umulh d a b => .UMULH (destinationRegister binding d) (sourceRegister binding a) (sourceRegister binding b)
  | .lsl d a n => .ORR_s (destinationRegister binding d) (.low .XZR .W64)
      { reg := sourceRegister binding a, amount := Int64.ofNat n.val, shift := .LSL }
  | .lsr d a n => .ORR_s (destinationRegister binding d) (.low .XZR .W64)
      { reg := sourceRegister binding a, amount := Int64.ofNat n.val, shift := .LSR }
  | .subsOne a => .SUBS_e (.low .XZR .W64) (physicalRegister binding a)
      (.imm { imm := 1, shift := .S0 })
  | .movMask d => .MOVZ (destinationRegister binding d) 0x4000 .LSL48⟩

def step (operation : Instruction) (binding : Binding) (state : MachineData) :
    Except String MachineData := run [.instr (instruction operation binding)] state

def store (binding : Binding) (state : MachineData) (d : Option Operand)
    (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  match d with
  | none => { state with status := flags }
  | some i => { state with regs := state.regs.setXReg (binding i) value, status := flags }

attribute [local irreducible] Reg64s.getXReg Reg64s.setXReg

theorem memory_frame (operation : Instruction) (binding : Binding) (state : MachineData) :
    (step operation binding state).map MachineData.dmem = .ok state.dmem := by
  cases operation <;> rfl

theorem stack_frame (operation : Instruction) (binding : Binding) (state : MachineData) :
    (step operation binding state).map (fun after => after.regs.SP) = .ok state.regs.SP := by
  cases operation <;>
    simp only [step, instruction, destinationRegister, physicalRegister, run,
      List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      finishEffects, Except.map, MachineData.setRegOrZr, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, KrakenBinding.set_sp]

theorem register_frame (operation : Instruction) (binding : Binding) (state : MachineData)
    (queried : XReg)
    (isProtected : ∀ d, destination operation = some d → queried ≠ binding d) :
    (step operation binding state).map (fun after => after.regs.getXReg queried) =
      .ok (state.regs.getXReg queried) := by
  cases operation
  case subsOne source => rfl
  all_goals simp only [destination, Option.some.injEq, forall_eq'] at isProtected
  all_goals
    simp only [step, instruction, destinationRegister, run,
      List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      finishEffects, Except.map, MachineData.setRegOrZr, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, KrakenBinding.get_set, if_neg isProtected]

theorem readonly_frame (operation : Instruction) (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) (valid : Valid operation)
    (queried : Operand) (readonly : written queried = false) :
    (step operation binding state).map (fun after => after.regs.getXReg (binding queried)) =
      .ok (state.regs.getXReg (binding queried)) := by
  apply register_frame
  intro d isDestination same
  have isWritten := valid d isDestination
  have indices := separated d queried isWritten same.symm
  subst queried
  rw [readonly] at isWritten
  cases isWritten

theorem interp_of_step [Labels] (operation : Instruction) (binding : Binding)
    (state after : MachineData) (executed : step operation binding state = .ok after)
    (position : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) :
    (instruction operation binding).interp state position next jump =
      .require_exec_access position (fun _ => next after) := by
  cases operation <;>
    simp only [step, instruction, run, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, finishEffects] at executed <;>
    cases executed <;> rfl

#print axioms memory_frame
#print axioms stack_frame
#print axioms register_frame
#print axioms readonly_frame
#print axioms interp_of_step

end PastaBridge.MulStep
