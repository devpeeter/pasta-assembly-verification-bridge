# Checked addition representation certificate

Status: **PASS for the representation and operand metadata certificate**. This is not an execution-to-arithmetic correctness result. The required target correctness theorem is reported separately in [RESULTS.md](../RESULTS.md).

The declarations below are in namespace `PastaBridge` in `CheckAddition.lean`. The measured direct Lean invocation exited 0 in **44.565786 seconds**, with **1,341,435,904 bytes** of Windows direct-child `PeakWorkingSetSize`. Its command and output are retained in `evidence/addition-artifact-proof.json` and `evidence/addition-artifact-proof.log`.

## Retained constants and provenance

`Retained.lean` reads `generated/add-check.json` as `retainedCharonArtifact`, quotes its characters as `retainedArtifactChars`, and reads `generated/add.S` as `retainedAdditionAssembly`. `retainedAdditionProgram` is the actual typed Kraken `Program` produced by invoking the pinned Kraken parser on that assembly at elaboration. There is no handwritten instruction list in these modules.

`generated/add-check.json` contains the complete template text and placeholder IDs/modifiers, operand kinds/register classes/late-output flags, and all represented assembly options. The generator obtains these fields from the retained exact Charon subtree. Full spans, MIR values/places, names and JSON pointers remain in `artifacts/charon-asm.json`, `artifacts/pasta_curves.llbc`, and the exact subtree in `generated/add-asm.json`. The semantic projection omits those fields; Python regeneration and provenance checks establish this external link. Lean does not prove the Rust compiler, Charon extraction, projection script, or Rust MIR prefix/suffix.

File inclusion occurs at elaboration. The verification script recompiles `Retained.lean` before this certificate on every run. A cached Lake build alone does not track changes to the included external files.

## Exact theorem statements

All five are closed statements about the retained artifacts; they have no input hypotheses.

```lean
theorem PastaBridge.retained_artifact_chars_readback :
    String.ofList retainedArtifactChars = retainedCharonArtifact
```

The kernel checks the quoted character list by reconstructing the actual retained file string. The parser then uses this list through `String.toList_ofList`, avoiding costly kernel UTF-8 decoding. Character quotation is a candidate computation checked by this equality.

```lean
theorem PastaBridge.addition_template_matches_retained_assembly :
    renderArtifact retainedCharonArtifact "add" =
      .ok retainedAdditionAssembly
```

The total fuel-bounded JSON decoder checks the projection schema and `Asm` kind, substitutes every template placeholder through the canonical register allocation, and rejects nonempty modifiers. The resulting string equals the retained assembly exactly.

```lean
theorem PastaBridge.addition_program_serializes_to_retained_assembly :
    serializeAdditionProgram retainedAdditionProgram =
      .ok retainedAdditionAssembly
```

The total serializer accepts only the selected 64-bit addition instruction forms, zero shifts, permitted registers and the expected carry condition. The equality checks the candidate program's constructors and every register operand against the retained assembly. Kraken's partial parser is a candidate producer; its full parser computation is not assumed correct or evaluated by the kernel.

```lean
theorem PastaBridge.addition_artifact_matches_retained_program :
    renderArtifact retainedCharonArtifact "add" =
      serializeAdditionProgram retainedAdditionProgram
```

This composes the two exact string equalities, connecting the retained semantic extraction artifact to the precise parsed representation used by the semantics.

```lean
theorem PastaBridge.addition_operand_metadata_matches :
    operandModesFromArtifact retainedCharonArtifact "add" =
      .ok (List.ofFn additionExpectedOperandMode)
```

`additionExpectedOperandMode : Fin 15 → OperandMode` is `inputOutput` at indices 0–3, `input` at 4–10, and `output` at 11–14. Successful decoding additionally checks every register class is exactly `reg`, every output is early, and all eight represented option flags equal: `pure`, `nomem`, `nostack` true; `readonly`, `preserves_flags`, `noreturn`, `att_syntax`, `may_unwind` false. These checks reject unknown/missing metadata rather than assuming the writable-index predicate.

## Axiom census and limits

| Declaration | Transitive axioms printed by Lean |
| --- | --- |
| `retained_artifact_chars_readback` | none |
| `addition_template_matches_retained_assembly` | `propext`, `Classical.choice`, `Quot.sound` |
| `addition_program_serializes_to_retained_assembly` | `propext` |
| `addition_artifact_matches_retained_program` | `propext`, `Classical.choice`, `Quot.sound` |
| `addition_operand_metadata_matches` | `propext`, `Classical.choice`, `Quot.sound` |

No declaration depends on `sorryAx` or a new correctness axiom. Kernel reductions use `rfl`, `String.toList_ofList`, and `decide +kernel`; no native evaluator supplies a proof assumption.

The certificate establishes representation identity and operand metadata. It does not prove arithmetic results, bounds, generic allocation correspondence, arbitrary flag/scratch independence, or frame preservation. It also does not establish the MIR operand values' relationship to Rust function arguments. Those obligations and the remaining extraction/provenance trust are reported in `RESULTS.md`.
