import PastaCurves.Fields
import PastaCurves.AArch64.Spec.Add
import PastaCurves.AArch64.Spec.Mul

/-!
Arithmetic endpoints reused without modifying their upstream proof bodies.
These statements concern the existing Pasta value models. They are not
correspondence theorems for a Charon artifact or a Kraken execution.
-/
namespace PastaAssemblyBridge.Arithmetic
open PastaCurves PastaCurves.AArch64

theorem addition (F : PastaField) (lhs rhs : Limbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hlhs_lt : lhs.toNat < F.modulus.toNat)
    (hrhs_lt : rhs.toNat < F.modulus.toNat) :
    let res := addMod lhs rhs F.modulus
    res.Bounded ∧ res.toNat < F.modulus.toNat ∧
      res.toNat ≡ lhs.toNat + rhs.toNat [MOD F.modulus.toNat] :=
  addMod_spec_of_lt lhs rhs F.modulus hlhs hrhs F.bounded F.shape
    hlhs_lt hrhs_lt _ rfl

theorem multiplication (F : PastaField) (lhs rhs : Limbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hcontract : mulContract lhs rhs F.modulus = true) :
    let res := mulMont lhs rhs F.modulus F.inv
    res.Bounded ∧ res.toNat < F.modulus.toNat ∧
      2^256 * res.toNat ≡ lhs.toNat * rhs.toNat [MOD F.modulus.toNat] := by
  rcases (mulContract_iff lhs rhs F.modulus hlhs hrhs F.bounded).mp hcontract with
    hlt | ⟨hlt, hlimbs⟩
  · exact mulMont_spec_of_lhs_lt lhs rhs F.modulus F.inv hlhs hrhs F.bounded
      F.shape F.inv_lt F.inv_spec hlt _ rfl
  · exact mulMont_spec_of_rhs_lt lhs rhs F.modulus F.inv hlhs hrhs F.bounded
      F.shape F.inv_lt F.inv_spec hlt hlimbs _ rfl

#print axioms addition
#print axioms multiplication
end PastaAssemblyBridge.Arithmetic
