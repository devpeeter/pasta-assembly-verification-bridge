# Universal retained-template certificate

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

`BindingArtifact.lean` was checked with Lean 4.31.0 and `-DautoImplicit=false`.
The final measured command, exit status, wall time and direct-child peak memory are in
`../evidence/verification.json`, stage `bindingartifact`; the complete axiom census
is in `../evidence/bindingartifact.log`. Both theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The exact declarations are in namespace `PastaBridge.BindingArtifact`:

```lean
theorem retained_pieces_match_artifact :
    decodeArtifact retainedCharonArtifact "add" = .ok retainedPieces

theorem bound_program_matches_template (binding : AdditionMachine.Binding)
    (allowed : ∀ i, KrakenBinding.Allowed (binding i)) :
    renderArtifactWithBinding binding retainedCharonArtifact "add" =
      serializeAdditionProgram (AdditionMachine.boundProgram binding)
```

`AdditionMachine.Binding` is `Fin 15 → XReg`. `Allowed r` means
`r ≠ XReg.X29`; `XReg` itself contains only X0 through X30. Generic allocation may use X19. The fixed default Linux target reserves X29 through the pinned compiler's frame-pointer policy; see `../evidence/register-policy.json`. The widened policy passed in the final clean run; `bindingartifact` took 14.777750 s with 1,078,272,000 bytes peak. Earlier 29-register measurements remain historical.
The certificate does not require register injectivity or writable-register
separation. It therefore applies to every admissible binding, including legal
sharing between read-only inputs. The machine correctness theorem separately
requires writable-register separation.

`decodeArtifact` is a total, rejecting decoder of the retained JSON semantic
projection. It checks the schema, assembly kind, template-piece shape, absent
placeholder modifiers, exact placeholder metadata fields, and operand indices
below 15. Its result contains only literal text and typed operand indices.
`retainedPieces` is produced by running that decoder during elaboration; the
first theorem independently checks its exact value through kernel reduction.
No instruction or template-piece list is transcribed in this source.

`renderArtifactWithBinding` decodes the retained template and substitutes each
typed operand index with the corresponding physical register name. The second
theorem proves that this text is exactly the serialization of the program used
by the machine proofs for the same binding. Its proof uses the existing rejecting
AST renamer and its universally checked instantiation certificate.

Operand modes, register classes, late-output settings and all eight assembly
options are checked by the separate retained metadata certificate in
`CheckAddition.lean`. Both certificates use the same `retainedCharonArtifact`
constant. This closes the template-substitution link for arbitrary bindings; it
does not prove arithmetic correctness by itself. The external provenance chain
from the original Charon artifact to this retained semantic projection remains
subject to the extraction/provenance trust documented in the main README.
