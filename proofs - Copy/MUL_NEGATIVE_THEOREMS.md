# Formal multiplication mutation checks

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

`FormalMulNegatives.lean` traverses the actual decoded retained program. It
changes the first ADCS to ADDS for the carry mutation. For the binding mutation,
it changes the first MUL source using RHS operand 4 to operand 5. The instruction
list is never transcribed. These are semantic checks. The universal positive
correspondence and field endpoint are separate proof obligations.

The carry witness is Pallas `lhs = p - 1`, `rhs = 2^64 - 1`. The binding witness
has `lhs = rhs = 1`. Both have the Pallas low modulus limbs and inverse in input
roles 8–10, and zero initial scratch words and carry. Lean checks every limb
bound and the existing `mulContract`, so the mutations fail on admitted inputs.

The exact statements, in `PastaBridge.FormalMulNegatives`, are:

```lean
witness_words_bounded : ∀ i : Fin 21,
  carryWitness.words i < 2^64 ∧ bindingWitness.words i < 2^64

witness_field_inputs :
  modulus carryWitness = PastaCurves.pallasBase.modulus ∧
  modulus bindingWitness = PastaCurves.pallasBase.modulus ∧
  carryWitness.words 10 = PastaCurves.pallasBase.inv ∧
  bindingWitness.words 10 = PastaCurves.pallasBase.inv ∧
  PastaCurves.mulContract (lhs carryWitness) (rhs carryWitness)
    PastaCurves.pallasBase.modulus = true ∧
  PastaCurves.mulContract (lhs bindingWitness) (rhs bindingWitness)
    PastaCurves.pallasBase.modulus = true

witness_input_values :
  (lhs carryWitness).toNat = PastaCurves.pallasBase.modulus.toNat - 1 ∧
  (rhs carryWitness).toNat = 2^64 - 1 ∧
  (lhs bindingWitness).toNat = 1 ∧ (rhs bindingWitness).toNat = 1

unmodified_models :
  output (MulNat.sequence MulMachine.decodedProgram carryWitness) = carryExpected ∧
  output (MulNat.sequence MulMachine.decodedProgram bindingWitness) = bindingExpected

expected_values :
  carryExpected.toNat =
    22231542348441172891284605428601131325858369222844048941495033842303251860735 ∧
  bindingExpected.toNat =
    15353493766103302224812374511606760489073247795810767472367693728416386214313

broken_carry_value : carryResult.toNat =
  10270262512448670424778123679734987708571182949051932638396965445873668699797

broken_binding_value : bindingResult.toNat = 0

broken_carry_is_semantically_wrong : carryResult ≠ carryExpected

broken_binding_is_semantically_wrong : bindingResult ≠ bindingExpected
```

`carryExpected` and `bindingExpected` use the unchanged upstream
`PastaCurves.AArch64.mulMont`; the result definitions run the corresponding
mutated program through `MulNat.sequence`. All nine certificates use
`decide +kernel` and depend only on `propext`, `Classical.choice`, and
`Quot.sound`. They contain no `sorryAx` or new correctness axiom.

The delivered `scripts/check_mul_formal_negatives.py` rebuilds the nine
certificates and requires an exact declaration/axiom census. It then asks Lean
to prove these original false equalities directly:

```lean
example : carryResult = carryExpected := by decide +kernel
example : bindingResult = bindingExpected := by decide +kernel
```

Each attempt must exit 1 with the pinned diagnostic that `decide` proved that
specific proposition false. An import error, an unrelated false proposition,
another error or warning, or a different exit code makes the check fail. The
invalid proof attempts remain outside the delivered checked proof roots; their
exact source is retained as `.lean.txt` evidence.

<!-- verification-negative-measurements:start -->
All three multiplication semantic-negative checks passed in the final clean run.

| Actual direct Lean check | Wall time | Peak working set |
| --- | ---: | ---: |
| Nine kernel counterexample certificates | 28.292918 s | 1,568,849,920 bytes |
| Intended false carry equality rejected | 25.669372 s | 1,436,209,152 bytes |
| Intended false binding equality rejected | 25.204334 s | 1,436,176,384 bytes |

The two original false equalities exited 1 with the exact intended rejection diagnostics. The certificate compilation exited 0 with its strict standard-axiom census. Memory is direct-child `PeakWorkingSetSize`, not a process-tree total.
<!-- verification-negative-measurements:end -->

Exact commands, source hashes, censuses and intended-proposition diagnostics
are retained in `../evidence/formal-multiplication-negatives/report.json` and
adjacent logs. Overall verification status is in `../RESULTS.md`.
