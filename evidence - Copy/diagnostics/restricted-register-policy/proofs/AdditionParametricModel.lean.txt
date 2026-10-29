import AdditionParametricBase

namespace PastaBridge.AdditionParametric

set_option maxRecDepth 100000
set_option maxHeartbeats 0

section
attribute [local irreducible] sequence transition AdditionNat.read AdditionNat.update

theorem generic_model (addOp subOp : CarryOp) (selectOp : SelectOp) (state : State) :
    output (sequence addOp subOp selectOp AdditionNatData.retainedData state) =
      model addOp subOp selectOp (output state) (rhs state) (modulus state) := by
  simp (ground := true) only [↓output, ↓rhs, ↓modulus, AdditionNatData.retainedData,
    ↓words_sequence_cons, ↓words_sequence_nil,
    ↓words_transition, ↓carry_transition,
    ↓AdditionNat.read_operand, ↓AdditionNat.read_zero, ↓reduceIte,
    model]
end

section
attribute [local irreducible] sequence transition output rhs modulus model AdditionNatData.sequence

theorem retained_data_model (state : State) :
    output (AdditionNatData.sequence AdditionNatData.retainedData state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state) := by
  calc
    output (AdditionNatData.sequence AdditionNatData.retainedData state) =
        output (sequence PastaCurves.addc PastaCurves.AArch64.subc
          PastaCurves.AArch64.cselCs AdditionNatData.retainedData state) :=
      congrArg output (sequence_specializes AdditionNatData.retainedData state).symm
    _ = model PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs
        (output state) (rhs state) (modulus state) :=
      generic_model PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs state
    _ = PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state) :=
      congrArg (fun function => function (output state) (rhs state) (modulus state))
        model_specializes
end

#print axioms model_specializes
#print axioms transition_specializes
#print axioms sequence_specializes
#print axioms generic_model
#print axioms retained_data_model

end PastaBridge.AdditionParametric
