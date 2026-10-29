import Kraken.AArch64.Semantics
namespace PastaBridge.KrakenWord

theorem add_value (a b : BitVec 64) (carry : Bool) :
    (a + b + BitVec.ofNat 64 carry.toNat).toNat =
      (a.toNat + b.toNat + carry.toNat) % 2^64 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_carry (a b : BitVec 64) (carry : Bool) :
    ((a + b + BitVec.ofNat 64 carry.toNat).unsigned !=
      a.unsigned + b.unsigned + (if carry then 1 else 0)).toNat =
      (a.toNat + b.toNat + carry.toNat) / 2^64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hv := add_value a b carry
  cases hf : ((a + b + BitVec.ofNat 64 carry.toNat).unsigned !=
      a.unsigned + b.unsigned + (if carry then 1 else 0)) with
  | false =>
    have heq : ((a + b + BitVec.ofNat 64 carry.toNat).toNat : Int) =
        (a.toNat : Int) + (b.toNat : Int) + (if carry then 1 else 0) := by
      simpa [BitVec.unsigned] using hf
    cases carry <;> simp_all <;> omega
  | true =>
    have hne : ((a + b + BitVec.ofNat 64 carry.toNat).toNat : Int) ≠
        (a.toNat : Int) + (b.toNat : Int) + (if carry then 1 else 0) := by
      simpa [BitVec.unsigned] using hf
    cases carry <;> simp_all <;> omega

theorem adds_carry (a b : BitVec 64) :
    (StatusFlags.adds (a + b) a b).c.toNat =
      (a.toNat + b.toNat) / 2^64 := by
  simpa [StatusFlags.adds, StatusFlags.from_result] using add_carry a b false

theorem sub_value (a b : BitVec 64) (carry : Bool) :
    (a - b - BitVec.ofNat 64 (!carry).toNat).toNat =
      (a.toNat + 2^64 - b.toNat - (1 - carry.toNat)) % 2^64 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  cases carry <;> simp_all <;> omega

theorem sub_carry (a b : BitVec 64) (carry : Bool) :
    (decide (a.unsigned >= b.unsigned + (if carry then 0 else 1))).toNat =
      (a.toNat + 2^64 - b.toNat - (1 - carry.toNat)) / 2^64 := by
  have ha := a.isLt
  have hb := b.isLt
  cases hf : decide (a.unsigned >= b.unsigned + (if carry then 0 else 1)) with
  | false =>
    have hlt : (a.toNat : Int) < (b.toNat : Int) + (if carry then 0 else 1) := by
      have hn : ¬ ((a.toNat : Int) >= (b.toNat : Int) +
          (if carry then 0 else 1)) := by
        simpa [BitVec.unsigned] using hf
      omega
    cases carry <;> simp_all <;> omega
  | true =>
    have hge : (a.toNat : Int) >= (b.toNat : Int) + (if carry then 0 else 1) := by
      simpa [BitVec.unsigned] using hf
    cases carry <;> simp_all <;> omega

theorem subs_carry (a b : BitVec 64) :
    (StatusFlags.subs (a - b) a b).c.toNat =
      (a.toNat + 2^64 - b.toNat) / 2^64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hv : (a - b).toNat = (a.toNat + 2^64 - b.toNat) % 2^64 := by
    simpa using sub_value a b true
  change ((a - b).unsigned == a.unsigned - b.unsigned).toNat = _
  cases hf : ((a - b).unsigned == a.unsigned - b.unsigned) with
  | false =>
    have hne : ((a - b).toNat : Int) ≠ (a.toNat : Int) - (b.toNat : Int) := by
      simpa [BitVec.unsigned] using hf
    simp only [Bool.toNat_false]
    omega
  | true =>
    have heq : ((a - b).toNat : Int) = (a.toNat : Int) - (b.toNat : Int) := by
      simpa [BitVec.unsigned] using hf
    simp only [Bool.toNat_true]
    omega

theorem csel_cs_value (flags : StatusFlags) (x y : BitVec 64) :
    (if CondCode.CS.interp flags then x else y).toNat =
      (if flags.c.toNat = 0 then y.toNat else x.toNat) := by
  cases flags with
  | mk n z c v => cases c <;> rfl

#print axioms csel_cs_value
#print axioms sub_value
#print axioms sub_carry
#print axioms subs_carry
#print axioms adds_carry
#print axioms add_value
#print axioms add_carry
end PastaBridge.KrakenWord
