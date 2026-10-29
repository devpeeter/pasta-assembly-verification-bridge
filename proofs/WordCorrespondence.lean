import KrakenWord
import PastaCurves.AArch64.Semantics

/-! Primitive correspondence to the retained upstream Pasta arithmetic semantics.
These are word-level laws, not a complete program or allocation theorem. -/
namespace PastaBridge.WordCorrespondence

open PastaCurves

theorem addc (a b : BitVec 64) (carry : Bool) :
    PastaCurves.addc a.toNat b.toNat carry.toNat =
      ((a + b + BitVec.ofNat 64 carry.toNat).toNat,
       ((a + b + BitVec.ofNat 64 carry.toNat).unsigned !=
        a.unsigned + b.unsigned + (if carry then 1 else 0)).toNat) := by
  apply Prod.ext
  · exact (KrakenWord.add_value a b carry).symm
  · exact (KrakenWord.add_carry a b carry).symm

theorem subc (a b : BitVec 64) (carry : Bool) :
    PastaCurves.AArch64.subc a.toNat b.toNat carry.toNat =
      ((a - b - BitVec.ofNat 64 (!carry).toNat).toNat,
       (decide (a.unsigned >= b.unsigned + (if carry then 0 else 1))).toNat) := by
  apply Prod.ext
  · exact (KrakenWord.sub_value a b carry).symm
  · exact (KrakenWord.sub_carry a b carry).symm

theorem cselCs (flags : StatusFlags) (x y : BitVec 64) :
    PastaCurves.AArch64.cselCs flags.c.toNat x.toNat y.toNat =
      (if CondCode.CS.interp flags then x else y).toNat := by
  exact (KrakenWord.csel_cs_value flags x y).symm

#print axioms addc
#print axioms subc
#print axioms cselCs
end PastaBridge.WordCorrespondence
