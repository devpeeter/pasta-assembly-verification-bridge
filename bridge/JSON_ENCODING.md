# Multiplication JSON encoding certificate

`generate_mul_json_certificate.py` reads only the retained
`generated/mul-check.json`. It rejects noncanonical JSON, duplicate object keys,
unsupported characters, or a missing final LF. It quotes a shared value and text
DAG; it does not construct an instruction sequence. Its output is an untrusted
candidate until Lean checks the following declarations.

The checked declarations are in `PastaBridge.MulJsonTextDag`:

```lean
retained_value_readback :
  retainedMultiplicationArtifactValue = value_124

encoded_124 :
  JsonEncoding.valueText 64 value_124 = .ok text_124

retained_bytes_readback :
  StringBytes.bytes (text_124 ++ "\n") = retainedMultiplicationArtifactBytes

retained_encoding :
  (JsonEncoding.documentText 64 retainedMultiplicationArtifactValue).map StringBytes.bytes =
    .ok retainedMultiplicationArtifactBytes
```

The public declaration `PastaBridge.multiplication_value_encodes_retained_artifact`
has the same type as `retained_encoding`. The encoder is total: it returns an
error for unsupported non-ASCII/control characters or exhausted nesting fuel.
It preserves object-field order and includes the document's final newline.

`retainedMultiplicationArtifactBytes` is a `List UInt8` quoted directly from
`IO.FS.readBinFile "../generated/mul-check.json"`. The closed byte certificate
uses `decide +kernel`, followed by `eq_of_beq`; it does not use a native decision
procedure, an external hash assumption, or a new axiom. `StringBytes.bytes`
observes a String's underlying UTF-8 byte array. The theorem checks all 27,152
retained bytes. No large String-literal equality is claimed.

File inclusion, source selection, Charon extraction, and the Python projection
from the retained complete extraction remain provenance trust boundaries.
The separate `multiplication_artifact_chars_readback` is only the generic
String/character-list roundtrip; it is not substituted for the byte certificate.
The universal template/native-program and operand-metadata certificates in
`MulCertificate.lean` connect this checked value to execution.

Regenerate with `python scripts/generate_mul_json_certificate.py`; check
freshness with the same command plus `--check`. The documented complete command
in `../README.md` performs freshness, compilation, axiom inspection, and target
checks. Individual compiler measurements and exact source hashes are retained
in `../evidence/mul-muljsontextdagbase.json`,
`../evidence/mul-muljsontextdagfinal.json`, and
`../evidence/mul-muljsoncertificate.json`.
