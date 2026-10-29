import Kraken.AArch64.Semantics

/-!
Physical-register lookup laws for Kraken's actual state representation. An
allocation only needs to separate registers written by the block; read-only
operand names may share. These are machine-state helper theorems, not a theorem
about an extracted program.
-/
namespace PastaBridge.KrakenBinding

/-- Generic `reg` on the pinned default Linux target may allocate x19. The
target's `non-leaf` frame-pointer policy reserves x29 in its pinned LLVM. -/
def Allowed (r : XReg) : Prop := r ≠ .X29

/-- Every written operand must be separated from every other operand. -/
def Separated {Operand : Type} (written : Operand → Bool)
    (binding : Operand → XReg) : Prop :=
  ∀ x y, written x = true → binding x = binding y → x = y

def Admissible {Operand : Type} (written : Operand → Bool)
    (binding : Operand → XReg) : Prop :=
  (∀ x, Allowed (binding x)) ∧ Separated written binding

theorem get_set (regs : Reg64s) (written queried : XReg) (value : BitVec 64) :
    (regs.setXReg written value).getXReg queried =
      if queried = written then UInt64.ofBitVec value else regs.getXReg queried := by
  cases written <;> cases queried <;> rfl

theorem set_sp (regs : Reg64s) (written : XReg) (value : BitVec 64) :
    (regs.setXReg written value).SP = regs.SP := by
  cases written <;> rfl

theorem get_set_binding {Operand : Type} [DecidableEq Operand]
    (regs : Reg64s) (written : Operand → Bool) (binding : Operand → XReg)
    (h : Separated written binding) (x y : Operand) (hx : written x = true)
    (value : BitVec 64) :
    (regs.setXReg (binding x) value).getXReg (binding y) =
      if y = x then UInt64.ofBitVec value else regs.getXReg (binding y) := by
  rw [get_set]
  by_cases heq : y = x
  · simp [heq]
  · have hne : binding y ≠ binding x := by
      intro hreg
      exact heq (h x y hx hreg.symm).symm
    simp [heq, hne]

/-- Equal physical input registers imply equal input values; this is consistency,
not a prohibition on legal sharing by read-only operands. -/
theorem shared_input_values {Operand : Type}
    (regs : Reg64s) (binding : Operand → XReg) (values : Operand → UInt64)
    (hvalues : ∀ x, regs.getXReg (binding x) = values x)
    (x y : Operand) (hshare : binding x = binding y) : values x = values y := by
  rw [← hvalues x, ← hvalues y, hshare]

theorem readonly_sharing_admissible {Operand : Type} :
    Admissible (fun _ : Operand => false) (fun _ => XReg.X0) := by
  constructor
  · intro x
    intro h
    cases h
  · intro x y hx
    cases hx

#print axioms get_set
#print axioms set_sp
#print axioms get_set_binding
#print axioms shared_input_values
#print axioms readonly_sharing_admissible
end PastaBridge.KrakenBinding
