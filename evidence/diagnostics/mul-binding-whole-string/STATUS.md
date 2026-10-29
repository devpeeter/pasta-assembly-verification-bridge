# Superseded proof strategy

Accepted as proof: **false**. This actual compilation failed at line 31 with
`simp`'s ten-million-step limit. The later `sorryAx` census is a consequence of
that rejected declaration; the verification policy rejects it. The measured
command, wall time, peak memory and complete diagnostics are retained here.

The costly step expanded the complete symbolic template string using
`String.join`, `List.foldl_cons`, `List.foldl_nil`,
`String.intercalate_cons_cons`, `String.intercalate_singleton`,
`String.append_assoc`, and `String.empty_append` with ground simplification.

It was replaced by generic structural formatting laws in
`proofs/MulPieceFormatting.lean`, a closed equality of normalized retained and
typed-program pieces, and generic rendering invariance under normalization.
The replacement universal theorem passed; its exact source hash, command and
measurements are in `evidence/mul-mulbindingartifact.json`. The unsuccessful
whole-string proof source was superseded; its diagnostics are historical
evidence, not a claim that the old declaration passed.
