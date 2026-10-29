# Parametric arithmetic readback

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

`AdditionParametricBase.lean` is checked. It abstracts exactly the three existing
arithmetic constants `PastaCurves.addc`, `PastaCurves.AArch64.subc`, and
`PastaCurves.AArch64.cselCs` into function parameters. The candidate `model`
comes directly from the pinned upstream `addMod` definition's expression body;
the candidate `transition` comes from the checked `AdditionNat.transition`
definition's expression body. The elaborator rejects a source body in which
any of those three constants is missing.

`model_specializes` and `transition_specializes` are closed kernel-checked
function equalities. They certify that supplying the existing arithmetic
functions yields exactly the original definitions. The expression producer is
not a correctness assumption: an incorrect candidate must still satisfy those
equalities. No target instruction list is copied or introduced here.

`sequence` folds the already checked `AdditionNatData.Instruction` data. Its
generic specialization theorem is proved by list induction. The query laws
allow one register word or carry to be observed while states remain opaque.
`CarryOp` abbreviates `Nat → Nat → Nat → Nat × Nat`, `SelectOp` abbreviates
`Nat → Nat → Nat → Nat`, and `State` is `AdditionNat.State`. No property of
the function parameters is assumed in these generic definitions and laws.

The module passed in 26.029168 seconds with peak working set 926,711,808 bytes.
Exact command, source hash, and log are in `evidence/addition-parametric-base.*`.
All five printed specialization/transition statements have an empty axiom
census. The other query laws are checked reflexivity proofs. This base module
alone does not prove the complete arithmetic program/model equality.

The following exact statements are in `PastaBridge.AdditionParametric`.

```lean
theorem model_specializes :
    model PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs =
      PastaCurves.AArch64.addMod
```

```lean
theorem transition_specializes :
    transition PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs =
      AdditionNat.transition
```

```lean
theorem sequence_specializes (program : List AdditionNatData.Instruction) (state : State) :
    sequence PastaCurves.addc PastaCurves.AArch64.subc PastaCurves.AArch64.cselCs program state =
      AdditionNatData.sequence program state
```

```lean
theorem words_transition (addOp subOp : CarryOp) (selectOp : SelectOp)
    (kind : Kind) (destination query : Operand) (first second : Source) (state : State) :
    (transition addOp subOp selectOp kind destination first second state).words query =
      if query = destination then
        let a := AdditionNat.read state first
        let b := AdditionNat.read state second
        match kind with
        | .adds => (addOp a b 0).1
        | .adcs | .adc => (addOp a b state.carry).1
        | .subs => (subOp a b 1).1
        | .sbcs => (subOp a b state.carry).1
        | .csel => selectOp state.carry a b
      else state.words query
```

```lean
theorem carry_transition (addOp subOp : CarryOp) (selectOp : SelectOp)
    (kind : Kind) (destination : Operand) (first second : Source) (state : State) :
    (transition addOp subOp selectOp kind destination first second state).carry =
      let a := AdditionNat.read state first
      let b := AdditionNat.read state second
      match kind with
      | .adds => (addOp a b 0).2
      | .adcs => (addOp a b state.carry).2
      | .adc | .csel => state.carry
      | .subs => (subOp a b 1).2
      | .sbcs => (subOp a b state.carry).2
```

```lean
theorem words_sequence_nil (addOp subOp : CarryOp) (selectOp : SelectOp)
    (state : State) (query : Operand) :
    (sequence addOp subOp selectOp [] state).words query = state.words query
```

```lean
theorem words_sequence_cons (addOp subOp : CarryOp) (selectOp : SelectOp)
    (instruction : AdditionNatData.Instruction) (remaining : List AdditionNatData.Instruction)
    (state : State) (query : Operand) :
    (sequence addOp subOp selectOp (instruction :: remaining) state).words query =
      (sequence addOp subOp selectOp remaining
        (transition addOp subOp selectOp instruction.kind instruction.destination
          instruction.first instruction.second state)).words query
```

```lean
theorem carry_sequence_nil (addOp subOp : CarryOp) (selectOp : SelectOp) (state : State) :
    (sequence addOp subOp selectOp [] state).carry = state.carry
```

```lean
theorem carry_sequence_cons (addOp subOp : CarryOp) (selectOp : SelectOp)
    (instruction : AdditionNatData.Instruction) (remaining : List AdditionNatData.Instruction)
    (state : State) :
    (sequence addOp subOp selectOp (instruction :: remaining) state).carry =
      (sequence addOp subOp selectOp remaining
        (transition addOp subOp selectOp instruction.kind instruction.destination
          instruction.first instruction.second state)).carry
```

## Complete data-program/model correspondence

`AdditionParametricModel.lean` proves the following structural equality for
every choice of the three function parameters. It then specializes through the
checked readback equalities to obtain the actual program's equality with the
existing `PastaCurves.AArch64.addMod`. The retained instruction data is the
same `AdditionNatData.retainedData` checked against the actual decoded program;
there is no model-correspondence premise in either theorem.

The marker-free final module passed in 36.601372 seconds with peak working set
923,090,944 bytes. Both model theorems depend only on `propext`; exact command,
source hash, and census are in `evidence/addition-parametric-model.*`.
The successful diagnostic predecessor also recorded `goals=0` after simp and
an after-declaration marker, retained separately under `evidence/diagnostics/`.
These statements establish computational correspondence; field output bounds
and congruence are supplied by the existing arithmetic specifications in the
separate final endpoint.

```lean
theorem generic_model (addOp subOp : CarryOp) (selectOp : SelectOp) (state : State) :
    output (sequence addOp subOp selectOp AdditionNatData.retainedData state) =
      model addOp subOp selectOp (output state) (rhs state) (modulus state)
```

```lean
theorem retained_data_model (state : State) :
    output (AdditionNatData.sequence AdditionNatData.retainedData state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state)
```

