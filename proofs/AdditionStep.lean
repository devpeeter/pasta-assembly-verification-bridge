import KrakenRun
import KrakenBinding

namespace PastaBridge.AdditionStep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Operand := Fin 15
abbrev Binding := Operand → XReg

def written (i : Operand) : Bool := i.val < 4 || 11 ≤ i.val

inductive Source where
  | operand (i : Operand)
  | zero

def sourceRegister (binding : Binding) : Source → RegOrZr .W64
  | .operand i => .low (.reg (binding i)) .W64
  | .zero => .low .XZR .W64

def ReadRel (binding canonical : Binding) (actual reference : MachineData) : Prop :=
  ∀ i, actual.regs.getXReg (binding i) = reference.regs.getXReg (canonical i)

def Rel (binding canonical : Binding) (actual reference : MachineData) : Prop :=
  ReadRel binding canonical actual reference ∧ actual.status = reference.status

def LiftedRel (binding canonical : Binding) :
    Except String MachineData → Except String MachineData → Prop
  | .ok actual, .ok reference => Rel binding canonical actual reference
  | _, _ => False

def store (state : MachineData) (destination : XReg)
    (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  { state with regs := state.regs.setXReg destination value, status := flags }

attribute [local irreducible] Reg64s.getXReg Reg64s.setXReg

theorem read_sources (binding canonical : Binding) (actual reference : MachineData)
    (reads : ReadRel binding canonical actual reference) (source : Source) :
    actual.regs.getRegOrZr (sourceRegister binding source) =
      reference.regs.getRegOrZr (sourceRegister canonical source) := by
  cases source with
  | zero => rfl
  | operand i =>
    simpa only [sourceRegister, Width.type, Width.bits, Reg64s.getRegOrZr, RegOrZr.base,
      Reg64s.getRegOrZr64] using
      congrArg (fun word : UInt64 => word.toBitVec.take 64) (reads i)

theorem store_rel (binding canonical : Binding) (actual reference : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (canonicalSeparated : KrakenBinding.Separated written canonical)
    (reads : ReadRel binding canonical actual reference)
    (destination : Operand) (isWritten : written destination = true)
    (actualValue referenceValue : BitVec 64) (sameValue : actualValue = referenceValue)
    (actualFlags referenceFlags : StatusFlags) (sameFlags : actualFlags = referenceFlags) :
    Rel binding canonical
      (store actual (binding destination) actualValue actualFlags)
      (store reference (canonical destination) referenceValue referenceFlags) := by
  constructor
  · intro i
    change (actual.regs.setXReg (binding destination) actualValue).getXReg (binding i) =
      (reference.regs.setXReg (canonical destination) referenceValue).getXReg (canonical i)
    rw [KrakenBinding.get_set_binding actual.regs written binding separated destination i isWritten,
      KrakenBinding.get_set_binding reference.regs written canonical canonicalSeparated destination i isWritten]
    by_cases h : i = destination
    · simp only [if_pos h, sameValue]
    · simpa only [if_neg h] using reads i
  · exact sameFlags

inductive Kind where
  | adds | adcs | adc | subs | sbcs | csel

def instruction (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) : Instr :=
  let dst : RegOrZr .W64 := .low (.reg (binding destination)) .W64
  let a := sourceRegister binding first
  let b := sourceRegister binding second
  ⟨.W64, match kind with
    | .adds => .ADDS_s dst a { reg := b, amount := 0, shift := .LSL }
    | .adcs => .ADCS dst a b
    | .adc => .ADC dst a b
    | .subs => .SUBS_s dst a { reg := b, amount := 0, shift := .LSL }
    | .sbcs => .SBCS dst a b
    | .csel => .CSEL dst a b .CS⟩

def step (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) : Except String MachineData :=
  run [.instr (instruction kind binding destination first second)] state

theorem adds_initial (binding canonical : Binding) (actual reference : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (canonicalSeparated : KrakenBinding.Separated written canonical)
    (reads : ReadRel binding canonical actual reference)
    (destination : Operand) (isWritten : written destination = true)
    (first second : Source) :
    LiftedRel binding canonical
      (step .adds binding destination first second actual)
      (step .adds canonical destination first second reference) := by
  simp only [step, instruction, run, List.length_cons, List.length_nil,
    List.map_cons, List.map_nil, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, finishEffects, LiftedRel,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    ShiftRegExpr.interp]
  apply store_rel binding canonical actual reference separated canonicalSeparated reads
    destination isWritten
  · rw [read_sources binding canonical actual reference reads first,
      read_sources binding canonical actual reference reads second]
  · rw [read_sources binding canonical actual reference reads first,
      read_sources binding canonical actual reference reads second]

theorem preserve (kind : Kind) (binding canonical : Binding) (actual reference : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (canonicalSeparated : KrakenBinding.Separated written canonical)
    (related : Rel binding canonical actual reference)
    (destination : Operand) (isWritten : written destination = true)
    (first second : Source) :
    LiftedRel binding canonical
      (step kind binding destination first second actual)
      (step kind canonical destination first second reference) := by
  cases kind with
  | adds =>
    exact adds_initial binding canonical actual reference separated canonicalSeparated related.1 destination isWritten first second
  | adcs | adc | subs | sbcs | csel =>
    simp only [step, instruction, run, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, finishEffects, LiftedRel,
      MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
      ShiftRegExpr.interp]
    apply store_rel binding canonical actual reference separated canonicalSeparated related.1
      destination isWritten
    all_goals simp only [read_sources binding canonical actual reference related.1 first,
      read_sources binding canonical actual reference related.1 second, related.2]

#print axioms adds_initial
#print axioms preserve

theorem memory_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) :
    (step kind binding destination first second state).map MachineData.dmem = .ok state.dmem := by
  cases kind <;> rfl

theorem stack_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) :
    (step kind binding destination first second state).map (fun final => final.regs.SP) =
      .ok state.regs.SP := by
  cases kind <;>
    simp only [step, instruction, run, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, finishEffects, Except.map,
      MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
      KrakenBinding.set_sp]

theorem register_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) (queried : XReg)
    (isProtected : queried ≠ binding destination) :
    (step kind binding destination first second state).map
      (fun final => final.regs.getXReg queried) = .ok (state.regs.getXReg queried) := by
  cases kind <;>
    simp only [step, instruction, run, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, finishEffects, Except.map,
      MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
      KrakenBinding.get_set, if_neg isProtected]

theorem readonly_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (isWritten : written destination = true) (queried : Operand)
    (readonly : written queried = false) :
    (step kind binding destination first second state).map
      (fun final => final.regs.getXReg (binding queried)) =
        .ok (state.regs.getXReg (binding queried)) := by
  apply register_frame
  intro same
  have indices := separated destination queried isWritten same.symm
  subst queried
  rw [readonly] at isWritten
  cases isWritten

theorem related_results_exist (binding canonical : Binding)
    (actual reference : Except String MachineData)
    (related : LiftedRel binding canonical actual reference) :
    ∃ actualState referenceState,
      actual = .ok actualState ∧ reference = .ok referenceState ∧
        Rel binding canonical actualState referenceState := by
  cases actual with
  | error error => cases related
  | ok actualState =>
    cases reference with
    | error error => cases related
    | ok referenceState => exact ⟨actualState, referenceState, rfl, rfl, related⟩

theorem interp_of_step [Labels] (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state after : MachineData)
    (executed : step kind binding destination first second state = .ok after)
    (position : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) :
    (instruction kind binding destination first second).interp state position next jump =
      .require_exec_access position (fun _ => next after) := by
  cases kind <;>
    simp only [step, instruction, run, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, finishEffects] at executed <;>
    cases executed <;> rfl

#print axioms memory_frame
#print axioms stack_frame
#print axioms register_frame
#print axioms readonly_frame
#print axioms related_results_exist
#print axioms interp_of_step

end PastaBridge.AdditionStep
