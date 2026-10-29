import MulStep
import MulWord

namespace PastaBridge.MulNat

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open MulStep

structure State where
  words : Operand → Nat
  carry : Nat

def project (binding : Binding) (state : MachineData) : State :=
  ⟨fun i => (state.regs.getXReg (binding i)).toNat, state.status.c.toNat⟩

def read (state : State) : Source → Nat
  | .operand i => state.words i
  | .zero => 0

def update (state : State) (destination : Option Operand) (value carry : Nat) : State :=
  match destination with
  | none => ⟨state.words, carry⟩
  | some d => ⟨fun i => if i = d then value else state.words i, carry⟩

def transition (operation : Instruction) (state : State) : State :=
  match operation with
  | .adds d a b => let result := PastaCurves.addc (read state a) (read state b) 0
      update state (some d) result.1 result.2
  | .adcs d a b => let result := PastaCurves.addc (read state a) (read state b) state.carry
      update state (some d) result.1 result.2
  | .adc d a b => update state (some d)
      (PastaCurves.addc (read state a) (read state b) state.carry).1 state.carry
  | .subs d a b => let result := PastaCurves.AArch64.subc (read state a) (read state b) 1
      update state (some d) result.1 result.2
  | .sbcs d a b => let result := PastaCurves.AArch64.subc (read state a) (read state b) state.carry
      update state (some d) result.1 result.2
  | .cselLo d a b => update state (some d)
      (PastaCurves.AArch64.cselLo state.carry (read state a) (read state b)) state.carry
  | .mul d a b => update state (some d)
      (PastaCurves.mulLo (read state a) (read state b)) state.carry
  | .umulh d a b => update state (some d)
      (PastaCurves.umulh (read state a) (read state b)) state.carry
  | .lsl d a n => update state (some d) (PastaCurves.lsl (read state a) n.val) state.carry
  | .lsr d a n => update state (some d) (PastaCurves.lsr (read state a) n.val) state.carry
  | .subsOne a => update state none 0 (PastaCurves.AArch64.subc (state.words a) 1 1).2
  | .movMask d => update state (some d) (2^62) state.carry

attribute [local irreducible] Reg64s.getXReg Reg64s.setXReg

theorem native_shift_zero (word : Width.W64.type) : word <<< (0 : Nat) = word :=
  BitVec.shiftLeft_zero word

theorem scalar_shift_zero (word : BitVec 64) : word <<< (0 : Nat) = word :=
  BitVec.shiftLeft_zero word

theorem zero_read (registers : Reg64s) :
    (registers.getRegOrZr (.low .XZR .W64) : BitVec 64) = BitVec.ofNat 64 0 := rfl

theorem native_zero_or (word : Width.W64.type) : BitVec.ofNat 64 0 ||| word = word :=
  BitVec.zero_or

theorem scalar_zero_or (word : BitVec 64) : BitVec.ofNat 64 0 ||| word = word :=
  BitVec.zero_or

theorem read_project (binding : Binding) (state : MachineData) (source : Source) :
    @BitVec.toNat 64 (state.regs.getRegOrZr (sourceRegister binding source)) =
      read (project binding state) source := by
  cases source with
  | zero => rfl
  | operand i =>
    simp only [sourceRegister, Reg64s.getRegOrZr, RegOrZr.base,
      Reg64s.getRegOrZr64, Width.type, Width.bits, BitVec.take,
      BitVec.extractLsb'_eq_self, UInt64.toNat_toBitVec, read, project]

theorem physical_project (binding : Binding) (state : MachineData) (i : Operand) :
    @BitVec.toNat 64 (state.regs.getRegOrSp (physicalRegister binding i)) =
      (project binding state).words i := by
  simp only [physicalRegister, Reg64s.getRegOrSp, RegOrSp.base,
    Reg64s.getRegOrSp64, Width.type, Width.bits, BitVec.take,
    BitVec.extractLsb'_eq_self, UInt64.toNat_toBitVec, project]

theorem store_project (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    {operation : Instruction} (valid : Valid operation)
    (value : BitVec 64) (flags : StatusFlags) :
    project binding (store binding state (destination operation) value flags) =
      update (project binding state) (destination operation) value.toNat flags.c.toNat := by
  cases hd : destination operation with
  | none => rfl
  | some d =>
    have isWritten := valid d hd
    unfold project store update
    apply congrArg₂ State.mk
    · funext i
      rw [KrakenBinding.get_set_binding state.regs written binding separated d i isWritten]
      by_cases same : i = d
      · simp only [if_pos same, UInt64.toNat_ofBitVec]
      · simp only [if_neg same]
    · rfl

theorem native_mask_literal :
    ((BitVec.ofInt 64 (Int64.toInt (16384 : Int64))) &&& (65535 : BitVec 64)).toNat * (2 : Nat)^48 % (2 : Nat)^64 = (2 : Nat)^62 := by
  decide +kernel

theorem step_project (operation : Instruction) (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) (valid : Valid operation) :
    (step operation binding state).map (project binding) =
      .ok (transition operation (project binding state)) := by
  have hzero : (Int64.toInt (0 : Int64)).toNat = 0 := by decide +kernel
  have hone : (BitVec.ofInt 64 (Int64.toInt (1 : Int64))).toNat = 1 := by decide +kernel
  have hsubplain (a b : BitVec 64) :
      (a - b).toNat = (a.toNat + 2^64 - b.toNat) % 2^64 := by
    simpa using KrakenWord.sub_value a b true
  cases operation <;>
    simp only [step, instruction, destinationRegister, run,
      List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      finishEffects, Except.map, MachineData.setRegOrZr, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, MachineData.setRegOrSp, Reg64s.setRegOrSp,
      Reg64s.setRegOrSp64, ShiftRegExpr.interp, ExtOrImmReg.interp,
      ConstExpr.interp, MovShift.toNat]
  all_goals dsimp (instances := true) only [Width.type, Width.bits, Width.instCoeBoolType]
  all_goals
    have stored := store_project binding state separated valid
    simp only [MulStep.store, destination] at stored
    rw [stored]
  all_goals try exact BitVec.ofNat 64 0
  all_goals simp (config := { failIfUnchanged := false }) only
    [hzero, hone, zero_read, native_shift_zero, scalar_shift_zero,
      native_zero_or, scalar_zero_or, MulWord.shift_amount]
  all_goals simp (config := { failIfUnchanged := false }) only
    [KrakenWord.add_value, KrakenWord.sub_value, MulWord.mul_value,
      MulWord.umulh_value, MulWord.lsl_value, MulWord.lsr_value,
      MulWord.csel_lo_value, MulWord.mask_value]
  all_goals simp (config := { failIfUnchanged := false }) only
    [KrakenWord.add_carry, KrakenWord.adds_carry,
      KrakenWord.sub_carry, KrakenWord.subs_carry, StatusFlags.from_result]
  all_goals simp (config := { failIfUnchanged := false }) only
    [hsubplain, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      read_project, physical_project]
  all_goals simp (config := { failIfUnchanged := false }) only
    [transition, update, destination, project, read,
      PastaCurves.addc, PastaCurves.AArch64.subc, PastaCurves.AArch64.cselLo,
      PastaCurves.mulLo, PastaCurves.umulh, PastaCurves.lsl, PastaCurves.lsr,
      PastaCurves.regMod, Nat.add_zero, Nat.sub_zero, Nat.sub_self,
      Nat.zero_mod, Nat.mod_mod, hone]
  all_goals apply congrArg Except.ok
  all_goals apply congrArg₂ State.mk
  all_goals try rfl
  all_goals
    funext i
    split
    · exact native_mask_literal
    · rfl

#print axioms read_project
#print axioms physical_project
#print axioms store_project
#print axioms step_project

end PastaBridge.MulNat
