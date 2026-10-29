# Multiplication retained-representation boundary

The retained file is `generated/mul-check.json`, including its final newline.
It is generated from the complete Charon assembly subtree: all 898 template
pieces, all 21 structured operand declarations, and every represented option.
The external regeneration check connects this compact projection to the full
retained LLBC and exact source pin. No instruction list is maintained by hand.

`MulRetained.lean` quotes a candidate `KernelJson.Value` from that file and the
actual native `Program` produced by Kraken's parser from `generated/mul.S`.
Quotation and parsing produce candidates; the following kernel certificates
connect the candidates to the retained document. Their integrated status is
reported by `../evidence/verification.json`.

```lean
PastaBridge.multiplication_artifact_chars_readback :
  String.ofList retainedMultiplicationArtifactChars =
    retainedMultiplicationCharonArtifact

PastaBridge.multiplication_value_encodes_retained_artifact :
  (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map StringBytes.bytes =
    .ok retainedMultiplicationArtifactBytes

PastaBridge.multiplication_pieces_match_retained_value :
  MultiplicationArtifact.pieces retainedMultiplicationArtifactValue =
    .ok retainedMultiplicationPieces

PastaBridge.multiplication_operand_metadata_matches :
  MultiplicationArtifact.operandModes retainedMultiplicationArtifactValue =
    .ok (List.ofFn MultiplicationArtifact.expectedOperandMode)

PastaBridge.MulBindingArtifact.bound_program_matches_template
    (binding : MulMachine.Binding)
    (allowed : ∀ i, KrakenBinding.Allowed (binding i)) :
  MultiplicationArtifact.renderValue binding retainedMultiplicationArtifactValue =
    MultiplicationArtifact.serializeProgram (MulMachine.boundProgram binding)

PastaBridge.multiplication_artifact_matches_retained_program :
  MultiplicationArtifact.renderValue MultiplicationArtifact.canonicalBinding
    retainedMultiplicationArtifactValue =
    MultiplicationArtifact.serializeProgram retainedMultiplicationProgram
```

The total ASCII JSON encoder preserves object order and checks exact document
bytes, including the trailing newline. `retainedMultiplicationArtifactBytes`
quotes the actual file with `IO.FS.readBinFile` and `Lean.ToExpr`; this has the
same explicit file-inclusion trust as quoting the retained text. The kernel
checks the encoder output against those retained bytes. The separate text/Char
roundtrip is not used as a replacement for this byte certificate.
The encoder rejects unsupported control/non-ASCII
characters and exhausted nesting depth. Candidate parser correctness is not an
assumption in the template theorem: the total native serializer checks the
program actually used by the semantics. `MulMachine.canonical_identity` checks
that the encoded decoded program is the actual parsed retained program.

The universal template theorem needs only the allowed register class. It does
not require injectivity or written-register separation. The execution proofs
add separation for written operands, allowing equal-valued read-only inputs to
share. Metadata checks require the exact supported class, early-output modes,
and represented options. The main field theorem includes the byte, encoding,
universal template and operand-metadata clauses in its postcondition.

`proofs/MulCertificate.lean` bundles these checks without adding a correctness
premise. The obsolete experiments that compared an additional assembly-string
literal are retained under `evidence/diagnostics/`; they are not part of the
checked source graph. The direct template/native-program certificate above
provides the required representation connection.

Source selection, Rust MIR production, Charon extraction, JSON projection and
file provenance remain externally checked trust boundaries. These certificates
do not establish compiler, register allocator, assembler or binary correctness.
