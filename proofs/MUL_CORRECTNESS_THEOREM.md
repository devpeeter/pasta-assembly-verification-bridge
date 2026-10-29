# Multiplication field correctness endpoint

This is an assembly-block theorem from a register-entry `MachineData` state.
It assumes the register inputs satisfy `InputContract`; it does not prove the
surrounding Rust wrapper's argument loads or result stores. The compact checked
representation omits MIR operand-value expressions and destination places.
The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

**Historical full automated technical status: PASS (2026-10-23).**
The current target admits X19 as a generic `reg` allocation and conditionally
preserves it when it is outside the written allocation. The previous 29-register
target and exact type/axiom audit passed and were archived; those results do not
establish the current 30-register target. The 2026-10-23 run checked the widened dependencies, target, exact-type audit and complete clean command.

The exact public target is:

```lean
PastaBridge.MulCorrectness.multiplication_correct
    (field : PastaCurves.PastaField)
    (binding : Fin 21 → XReg)
    (state : MachineData)
    (admissible : MulMachine.Admissible binding)
    (inputs : InputContract field binding state) :
  ∃ after : MachineData,
    MulMachine.runWithBinding binding state = .ok after ∧
    Postcondition field binding state after
```

The statement has only the admissible allocation and input contract as explicit
proof premises. Its internal model correspondence is instantiated with the
checked `MulNat.all_bindings_model`, whose theorem has no model-correctness
premise. The field parameter is the existing upstream `PastaField`; the target
specializes to `PastaCurves.pallasBase` and `PastaCurves.vestaBase`.

The register projections are:

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
   (state.regs.getXReg (binding 9)).toNat, 0, 2^62⟩

inv binding state = (state.regs.getXReg (binding 10)).toNat

output binding state =
  ⟨(state.regs.getXReg (binding 16)).toNat,
   (state.regs.getXReg (binding 17)).toNat,
   (state.regs.getXReg (binding 18)).toNat,
   (state.regs.getXReg (binding 19)).toNat⟩
```

`Limbs.toNat` interprets the four little-endian limbs in base `2^64`.
`Limbs.Bounded` requires each limb to be less than `2^64`. All input limb bounds
follow automatically from the machine register type using `UInt64.toNat_lt`.
The modulus's upper limbs are fixed by the retained routine and agree with the
existing Pasta field shape. The inverse word is the existing field inverse
constant, satisfying the upstream field's low-word inverse specification.

The full input contract is:

```lean
structure InputContract (field : PastaField) (binding : Binding)
    (state : MachineData) : Prop where
  modulus_eq : modulus binding state = field.modulus
  inv_eq : inv binding state = field.inv
  operands : mulContract (lhs binding state) (rhs binding state)
    field.modulus = true
```

By the existing `PastaCurves.mulContract_iff` and automatic limb bounds, the
operand condition means:

```lean
(lhs binding state).toNat < field.modulus.toNat ∨
  ((rhs binding state).toNat < field.modulus.toNat ∧
   (rhs binding state).l1 + 3 ≤ 2^64 ∧
   (rhs binding state).l2 + 3 ≤ 2^64 ∧
   (rhs binding state).l3 + 3 ≤ 2^64)
```

In particular, two canonical field inputs satisfy the contract. The statement
also covers the wider input domain proved by the existing multiplication
specification.

`Admissible binding` expands to:

```lean
(∀ i : Fin 21, binding i ≠ .X29) ∧
KrakenBinding.Separated MulStep.written binding
```

`XReg` contains X0 through X30, so the allowed allocation set has 30 registers;
X19 may be allocated, while X29 remains reserved by the pinned default non-leaf
target policy. SP and XZR are separate register forms. `MulStep.written i` is true exactly at
indices 11–20, the retained early output operands. The checked metadata/write
mask theorem ties this classification to the extracted structured declarations.
`Separated` requires every written operand's register to differ from every
other operand's register. Read-only operands 0–10 may share registers. Their
values then agree because they are reads of the same physical register.

The exact complete postcondition is:

```lean
def Protected (binding : Binding) (queried : XReg) : Prop :=
  ∀ destination : Fin 21, MulStep.written destination = true →
    queried ≠ binding destination

structure Postcondition (field : PastaField) (binding : Binding)
    (before after : MachineData) : Prop where
  model_eq : output binding after =
    AArch64.mulMont (lhs binding before) (rhs binding before)
      field.modulus field.inv
  bounded : (output binding after).Bounded
  canonical : (output binding after).toNat < field.modulus.toNat
  congruent : 2^256 * (output binding after).toNat ≡
    (lhs binding before).toNat * (rhs binding before).toNat
      [MOD field.modulus.toNat]
  memory : after.dmem = before.dmem
  stack : after.regs.SP = before.regs.SP
  protected_registers : ∀ queried, Protected binding queried →
    after.regs.getXReg queried = before.regs.getXReg queried
  readonly_registers : ∀ queried : Fin 21,
    MulStep.written queried = false →
    after.regs.getXReg (binding queried) = before.regs.getXReg (binding queried)
  protected_x19 : Protected binding .X19 → after.regs.X19 = before.regs.X19
  protected_x29 : after.regs.X29 = before.regs.X29
  retained_bytes : String.ofList retainedMultiplicationArtifactChars =
    retainedMultiplicationCharonArtifact
  retained_encoding : (JsonEncoding.documentText 64
    retainedMultiplicationArtifactValue).map StringBytes.bytes =
      .ok retainedMultiplicationArtifactBytes
  retained_template : MultiplicationArtifact.renderValue binding
    retainedMultiplicationArtifactValue =
      MultiplicationArtifact.serializeProgram (MulMachine.boundProgram binding)
  operand_metadata : MultiplicationArtifact.operandModes
    retainedMultiplicationArtifactValue =
      .ok (List.ofFn MultiplicationArtifact.expectedOperandMode)
```

The congruence is Montgomery multiplication: multiplying the output by
`2^256` recovers the input product modulo the field modulus. The result is
bounded and canonical. Every modeled physical register outside the written
allocation is preserved, as are read-only operand registers, memory and SP.
X19 is preserved when it is outside the written allocation, as required by the
generic protected-register clause; X29 is preserved unconditionally.

`state : MachineData` is universally quantified. Incoming NZCV flags, output and
scratch registers 11–20, memory, SP, and other registers may contain arbitrary
values. The input contract imposes no initial flag or scratch invariant. Output
flags may change.

The artifact clauses connect the exact retained JSON file bytes, including its
terminal LF, to the decoded template and structured operand metadata, and connect every
allowed physical rendering to the same native program used by the execution
theorem. `MulMachine.decoding_certificate` checks the complete retained AST;
`instantiation_certificate` checks the allocation-specific encoding, and the
universal template certificate also specializes through `canonical_identity`
to the retained native program. A separate equality with a redundant assembly
string is not needed for this link.

`retainedMultiplicationArtifactBytes : List UInt8` is included directly by reading
the same retained `generated/mul-check.json` file as raw bytes. `StringBytes.bytes`
is `text.toByteArray.data.toList`. The encoding clause compares the document's
complete UTF-8 byte list with that included list; it is not a hash comparison or
an assumed decoding relation. File inclusion and artifact provenance remain
explicit parts of the extraction trust boundary, as with the retained String
literal. No equality of the document String with a separately included String
has been claimed as a checked certificate.

The extraction and artifact-provenance trust boundary is documented in the
project README. This endpoint concerns the retained inline assembly program and
Kraken's modeled machine state; it does not verify the Rust compiler, Charon's
implementation, emitted binaries, or a complete hardware model.

The archived 29-register `MulCorrectness.lean` module passed with pinned Lean 4.31.0 and
`-DautoImplicit=false` in **120.810189 seconds**, with direct-process peak working
set **1,471,270,912 bytes**. `MulAudit.lean` passed in **25.426160 seconds**, with
peak working set **1,453,047,808 bytes**. The main target and exact type guard
depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx`, added correctness axiom, or model-correctness premise.

The archived exact direct Lean commands, exit codes, logs, source/output SHA-256 values,
and strict declaration-by-declaration axiom censuses are retained in
[mul-target-proof-provenance.json](../evidence/mul-target-proof-provenance.json),
[mul-correctness.log](../evidence/mul-correctness.log), and
[mul-target-audit.log](../evidence/mul-target-audit.log). These are component
results for the narrower allocation policy, not a check of the current source.
The widened target passed in 31.765274 s with 1,470,312,448 bytes peak; its exact-type audit passed in 23.210511 s. Current records are `../evidence/mulcorrectness.log`, `../evidence/mul-proof-inventory.log` and `../evidence/verification.json`.

The separate formal mutation checks passed; their exact nine certificates,
bounded admitted witnesses, strict original-proposition rejection checks and
measurements are documented in [MUL_NEGATIVE_THEOREMS.md](MUL_NEGATIVE_THEOREMS.md).
