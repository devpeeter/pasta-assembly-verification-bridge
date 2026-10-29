# Addition field correctness endpoint

This is an assembly-block theorem from a register-entry `MachineData` state.
It assumes the register inputs satisfy `InputContract`; it does not prove the
surrounding Rust wrapper's argument loads or result stores. The compact checked
representation omits MIR operand-value expressions and destination places.
The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

`AdditionCorrectness.lean` checks the complete retained addition program through
the actual Kraken semantics and the existing Pasta `AArch64.addMod` model and
field specification. The main theorem has no correspondence premise:

```lean
PastaBridge.AdditionCorrectness.addition_correct
    (field : PastaCurves.PastaField)
    (binding : Fin 15 → XReg)
    (state : MachineData)
    (admissible : AdditionMachine.Admissible binding)
    (inputs : InputContract field binding state) :
  ∃ after : MachineData,
    AdditionMachine.runWithBinding binding state = .ok after ∧
    Postcondition field binding state after
```

This statement applies to both `PastaCurves.pallasBase` and
`PastaCurves.vestaBase`. The field parameter is the existing upstream
`PastaField`, whose properties discharge the arithmetic specification's
requirements. The checked model correspondence is proved from the decoded
retained program, rather than supplied as an input to this theorem.

The following definitions expand the input and output contract. Here `binding`
maps the fifteen retained operand indices to physical registers, and a limb is
the natural-number value of a 64-bit machine register.

```lean
lhs binding state =
  ⟨(state.regs.getXReg (binding 0)).toNat,
   (state.regs.getXReg (binding 1)).toNat,
   (state.regs.getXReg (binding 2)).toNat,
   (state.regs.getXReg (binding 3)).toNat⟩

rhs binding state =
  ⟨(state.regs.getXReg (binding 4)).toNat,
   (state.regs.getXReg (binding 5)).toNat,
   (state.regs.getXReg (binding 6)).toNat,
   (state.regs.getXReg (binding 7)).toNat⟩

modulus binding state =
  ⟨(state.regs.getXReg (binding 8)).toNat,
   (state.regs.getXReg (binding 9)).toNat,
   0,
   (state.regs.getXReg (binding 10)).toNat⟩

output = lhs

structure InputContract (field : PastaField) (binding : Binding)
    (state : MachineData) : Prop where
  modulus_eq : modulus binding state = field.modulus
  lhs_lt : (lhs binding state).toNat < field.modulus.toNat
  rhs_lt : (rhs binding state).toNat < field.modulus.toNat
```

`Limbs.toNat` interprets the four little-endian limbs in base `2^64`.
`Limbs.Bounded` requires each limb to be less than `2^64`; this follows
automatically for input register projections from `UInt64.toNat_lt`.
There is no additional limb-bound assumption.

`Admissible binding` expands to:

```lean
(∀ i : Fin 15, binding i ≠ .X29) ∧
KrakenBinding.Separated AdditionStep.written binding
```

`XReg` contains X0 through X30. Thus the allowed set has 30 registers; SP and
XZR are separate register forms. The fixed target reserves X29; generic Rust
`reg` operands may use X19. Function-specific reservations may reduce this set.
The retained compiler/LLVM evidence is in `../evidence/register-policy.json`.
`written` is true exactly at indices 0–3 and
11–14, as checked against the retained structured operand declarations.
`Separated written binding` requires every written operand's register to differ
from every other operand's register. It does not require distinct read-only
operands to have different registers. Legal read-only aliases therefore appear
in the quantified domain; their initial values agree because they are reads of
the same physical register. Every register outside the written allocation is
protected, including read-only operand registers.

The complete postcondition is:

```lean
def Protected (binding : Binding) (queried : XReg) : Prop :=
  ∀ destination : Fin 15, AdditionStep.written destination = true →
    queried ≠ binding destination

structure Postcondition (field : PastaField) (binding : Binding)
    (before after : MachineData) : Prop where
  model_eq : output binding after =
    AArch64.addMod (lhs binding before) (rhs binding before) field.modulus
  bounded : (output binding after).Bounded
  canonical : (output binding after).toNat < field.modulus.toNat
  congruent : (output binding after).toNat ≡
    (lhs binding before).toNat + (rhs binding before).toNat
      [MOD field.modulus.toNat]
  memory : after.dmem = before.dmem
  stack : after.regs.SP = before.regs.SP
  protected_registers : ∀ queried, Protected binding queried →
    after.regs.getXReg queried = before.regs.getXReg queried
  readonly_registers : ∀ queried : Fin 15,
    AdditionStep.written queried = false →
    after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried)
  protected_x19 : Protected binding .X19 → after.regs.X19 = before.regs.X19
  protected_x29 : after.regs.X29 = before.regs.X29
  retained_template :
    BindingArtifact.renderArtifactWithBinding binding retainedCharonArtifact "add" =
      serializeAdditionProgram (AdditionMachine.boundProgram binding)
  operand_metadata : operandModesFromArtifact retainedCharonArtifact "add" =
    .ok (List.ofFn additionExpectedOperandMode)
```

`MachineData` is universally quantified. Incoming flags, scratch operands
11–14, memory, SP, and other registers may contain arbitrary values. No initial
flag or scratch-value invariant is assumed. Output flags may change.

The artifact fields connect the exact retained template and structured operand
metadata to the same instantiated program used by `runWithBinding`.
`AdditionMachine.instantiation_certificate` checks the total specialization
against the rejecting AST traversal for every binding;
`AdditionMachine.retained_written_mask` checks the write policy against the
retained declarations. The extraction, source and artifact-provenance trust
boundary remains documented in the project README: the theorem does not verify
the Rust compiler, Charon extraction, or emitted binaries.

The widened 30-register target and its complete dependency closure passed the final clean check. Target source: 30.354161 s, 1,445,429,248 bytes peak; exact-type audit: 28.565895 s. See `../evidence/verification.json`.
Earlier checked results used a restricted 29-register domain and are retained
under `../evidence/diagnostics/restricted-register-policy/`; the complete generic-register coverage above is established by the fresh integrated run. The documented clean command
checks the module with pinned Lean 4.31.0 and `-DautoImplicit=false`, rejects
`sorryAx` or new correctness axioms, and requires the exact public type above.
Its current invocation, timing and axiom census are retained in
`../evidence/verification.json` and `../evidence/additioncorrectness.log`.

The two formal mutation checks traverse the actual decoded program:
the first ADCS becomes ADDS, or the first operand-4 source becomes operand 5.
The checked witness uses bounded limbs, the Pallas modulus, and inputs below the
modulus. Lean proves that the carry mutant returns 0, the binding mutant returns
`2^64 - 1`, and the existing model returns `2^64`. The verification command
then asks Lean to prove each original false output equality and requires the
precise intended-proposition rejection diagnostic, with no other errors or
warnings. See `FormalAdditionNegatives.lean` and
`../evidence/formal-addition-negatives/` for the checked witness and logs.
