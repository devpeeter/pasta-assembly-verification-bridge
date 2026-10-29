import AdditionStep
import WordCorrespondence

namespace PastaBridge.AdditionNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open AdditionStep

structure State where
  words : Operand → Nat
  carry : Nat

def project (binding : Binding) (state : MachineData) : State :=
  ⟨fun i => (state.regs.getXReg (binding i)).toNat, state.status.c.toNat⟩

def read (state : State) : Source → Nat
  | .operand i => state.words i
  | .zero => 0

def update (state : State) (destination : Operand) (value carry : Nat) : State :=
  ⟨fun i => if i = destination then value else state.words i, carry⟩

def transition (kind : Kind) (destination : Operand) (first second : Source)
    (state : State) : State :=
  let a := read state first
  let b := read state second
  match kind with
  | .adds => let result := PastaCurves.addc a b 0
      update state destination result.1 result.2
  | .adcs => let result := PastaCurves.addc a b state.carry
      update state destination result.1 result.2
  | .adc => let result := PastaCurves.addc a b state.carry
      update state destination result.1 state.carry
  | .subs => let result := PastaCurves.AArch64.subc a b 1
      update state destination result.1 result.2
  | .sbcs => let result := PastaCurves.AArch64.subc a b state.carry
      update state destination result.1 result.2
  | .csel => update state destination
      (PastaCurves.AArch64.cselCs state.carry a b) state.carry

attribute [local irreducible] Reg64s.getXReg Reg64s.setXReg

theorem read_project (binding : Binding) (state : MachineData) (source : Source) :
    (state.regs.getRegOrZr (sourceRegister binding source)).toNat =
      read (project binding state) source := by
  cases source with
  | zero => rfl
  | operand i =>
    simp only [sourceRegister, Reg64s.getRegOrZr, RegOrZr.base,
      Reg64s.getRegOrZr64, Width.type, Width.bits, BitVec.take,
      BitVec.extractLsb'_eq_self, UInt64.toNat_toBitVec, read, project]

theorem read_project64 (binding : Binding) (state : MachineData) (source : Source) :
    @BitVec.toNat 64 (state.regs.getRegOrZr (sourceRegister binding source)) =
      read (project binding state) source := read_project binding state source

theorem native_shift_zero (word : Width.W64.type) :
    word <<< (0 : Nat) = word := BitVec.shiftLeft_zero word

theorem scalar_shift_zero (word : BitVec 64) :
    word <<< (0 : Nat) = word := BitVec.shiftLeft_zero word

theorem store_project (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (destination : Operand) (isWritten : written destination = true)
    (value : BitVec 64) (flags : StatusFlags) :
    project binding (store state (binding destination) value flags) =
      update (project binding state) destination value.toNat flags.c.toNat := by
  unfold project store update
  apply congrArg₂ State.mk
  · funext i
    rw [KrakenBinding.get_set_binding state.regs written binding separated destination i isWritten]
    by_cases h : i = destination
    · simp only [if_pos h, UInt64.toNat_ofBitVec]
    · simp only [if_neg h]
  · rfl

#print axioms read_project
#print axioms store_project

theorem step_project (kind : Kind) (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (destination : Operand) (isWritten : written destination = true)
    (first second : Source) :
    (step kind binding destination first second state).map (project binding) =
      .ok (transition kind destination first second (project binding state)) := by
  have hzero : (Int64.toInt (0 : Int64)).toNat = 0 := by decide +kernel
  have hsubplain (a b : BitVec 64) :
      (a - b).toNat = (a.toNat + 2^64 - b.toNat) % 2^64 := by
    simpa using KrakenWord.sub_value a b true
  cases kind <;>
    simp only [step, instruction, run, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, finishEffects, Except.map,
      MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
      ShiftRegExpr.interp]
  all_goals dsimp (instances := true) only [Width.type, Width.bits, Width.instCoeBoolType]
  all_goals
    have stored := store_project binding state separated destination isWritten
    simp only [store] at stored
    rw [stored]
  all_goals simp (config := { failIfUnchanged := false }) only [hzero, native_shift_zero, scalar_shift_zero]
  all_goals simp (config := { failIfUnchanged := false }) only [KrakenWord.add_value, KrakenWord.sub_value]
  all_goals simp (config := { failIfUnchanged := false }) only [KrakenWord.add_carry, KrakenWord.adds_carry,
    KrakenWord.sub_carry, KrakenWord.subs_carry, KrakenWord.csel_cs_value,
    StatusFlags.from_result]
  all_goals simp (config := { failIfUnchanged := false }) only [hsubplain, BitVec.toNat_add]
  all_goals simp (config := { failIfUnchanged := false }) only [read_project, read_project64]
  all_goals simp only [transition, project,
    PastaCurves.addc, PastaCurves.AArch64.subc, PastaCurves.AArch64.cselCs,
    PastaCurves.regMod, Nat.add_zero, Nat.sub_zero, Nat.sub_self]

#print axioms step_project

end PastaBridge.AdditionNat
