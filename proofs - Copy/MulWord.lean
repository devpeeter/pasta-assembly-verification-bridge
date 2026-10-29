import WordCorrespondence

namespace PastaBridge.MulWord

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mul_value (a b : BitVec 64) :
    (a * b + (0 : BitVec 64)).toNat = PastaCurves.mulLo a.toNat b.toNat := by
  change (a * b + BitVec.ofNat 64 0).toNat = _
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.add_zero, Nat.mod_mod, PastaCurves.mulLo, PastaCurves.regMod]

theorem umulh_value (a b : BitVec 64) :
    (BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)).toNat =
      PastaCurves.umulh a.toNat b.toNat := by
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    PastaCurves.umulh, PastaCurves.regMod]
  apply Nat.mod_eq_of_lt
  apply (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < 2^64)).2
  simpa only [← Nat.pow_add] using (BitVec.toNat_mul_toNat_lt (x := a) (y := b))

theorem lsl_value (word : BitVec 64) (amount : Nat) :
    (word <<< amount).toNat = PastaCurves.lsl word.toNat amount := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rfl

theorem lsr_value (word : BitVec 64) (amount : Nat) :
    (word.ushiftRight amount).toNat = PastaCurves.lsr word.toNat amount := by
  change word.toNat >>> amount = word.toNat / 2^amount
  exact Nat.shiftRight_eq_div_pow _ _

theorem csel_lo_value (flags : StatusFlags) (x y : BitVec 64) :
    (if CondCode.CC.interp flags then x else y).toNat =
      PastaCurves.AArch64.cselLo flags.c.toNat x.toNat y.toNat := by
  cases flags with
  | mk n z c v => cases c <;> rfl

theorem shift_amount (amount : Fin 64) :
    (Int64.toInt (Int64.ofNat amount.val)).toNat = amount.val := by
  have bound : amount.val < 2^63 :=
    Nat.lt_trans amount.isLt (by decide +kernel : 64 < 2^63)
  rw [Int64.toInt_ofNat_of_lt bound]
  rfl

theorem mask_value :
    (((BitVec.ofInt 64 (Int64.toInt (0x4000 : Int64))) &&&
      (0xFFFF : BitVec 64)) <<< (48 : Nat)).toNat = 2^62 := by
  decide +kernel

#print axioms mul_value
#print axioms umulh_value
#print axioms lsl_value
#print axioms lsr_value
#print axioms csel_lo_value
#print axioms shift_amount
#print axioms mask_value

end PastaBridge.MulWord
