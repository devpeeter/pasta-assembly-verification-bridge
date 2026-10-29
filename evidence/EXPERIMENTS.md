# Archived certificate experiments

These records describe superseded attempts, not delivered target proofs. The successful certificate is `bridge/CheckAddition.lean`; its exit-0 measurement and axiom census are in `addition-artifact-proof.json` and `addition-artifact-proof.log`. Only successful source modules belong to the proof build.

The archived commands used the filename `CheckAddition.lean` while that file contained an earlier experiment. Running that logged filename now executes the final checked source, not the old experiment.

| Archived record stem | Actual disposition |
| --- | --- |
| `full-envelope-kernel-interrupted` | Owned Lean process stopped after 234.583711 s and 6,080,806,912 bytes peak memory; full 260 KB envelope computation superseded by an exact addition view |
| `pretty-subtree-kernel-interrupted` | Owned process stopped after 193.008379 s and 5,615,091,712 bytes peak memory; pretty-printed 29 KB addition view superseded by compact JSON |
| `compact-subtree-kernel-interrupted` | Owned process stopped after 311.178816 s and 5,922,279,424 bytes peak memory; exact 9 KB view superseded by a semantic projection retaining template and operand contract metadata |
| `string-decoding-kernel-interrupted` | Owned process stopped after 298.074229 s and 4,023,742,464 bytes peak memory; direct string decoding superseded by kernel-checked character readback |
| `char-readback-normalization-failed` | Actual exit 1 after 36.082301 s and 1,289,670,656 bytes peak memory; standard string split/trim prevented kernel reduction of the serializer comparison. The final proof uses the stronger exact-string equality instead |

Each stem has a `.json` measurement and `.log` compiler output. A nonzero exit or interruption is never counted as a passing proof. Diagnostics mentioning `sorryAx` in the failed normalization attempt arise from Lean's error recovery for failed declarations; those declarations have no delivered target module or successful build. The final certificate's printed axiom census has no `sorryAx`.

`full-envelope-check-source.lean.txt` preserves the source of the full-envelope experiment. Its `.txt` suffix deliberately excludes it from proof-source discovery. To reproduce it, copy it to a scratch `.lean` file and run the pinned Lean compiler on that file **with the working directory set to `bridge/`** and the same `LEAN_PATH` used for the successful certificate. Its `../artifacts/charon-asm.json` input is the retained full envelope whose hash is recorded in `full-envelope-kernel-interrupted.json`. The archived command's `CheckAddition.lean` argument corresponds to this saved source. The experiment may again require substantial memory and is not part of the documented verification command.

`pretty-add-asm.json` preserves the earlier pretty-printed view. The compact exact view remains `generated/add-asm.json`. The final small semantic projection is `generated/add-check.json`; regeneration verifies both against the retained Charon subtree. Character quotation plus checked `String.ofList` readback made its total decoder practical without introducing a native evaluation assumption.
# Nat lifting normalization diagnostic

`diagnostics/nat-lift-attempt-1.json` records a controlled interruption after
377.914323 seconds and a 3,702,849,536-byte direct-child peak working set. The
exact work-only source is `diagnostics/nat-lift-attempt-1-source.lean.txt`; its
logged filename was `work/AdditionNatLift.lean`. Restore that snapshot to the
logged filename to reproduce the attempted command. The next attempt adds
flushed declaration boundaries to locate the expensive normalization. This
interrupted attempt is not a target theorem or a semantic counterexample.

`diagnostics/nat-lift-attempt-2.json` similarly preserves the instrumented
work-only attempt, interrupted after 243.403591 seconds with a 3,101,401,088-byte
peak. Its frontend output remained buffered, so the next diagnostic uses a
separate compiler invocation ending at the sequence lemma. The source snapshot
is explicitly non-target evidence and has a `.lean.txt` suffix.

`diagnostics/nat-lift-attempt-3.*` preserves the run after separating the generic
sequence lemma. It was interrupted after 340.595763 seconds / 3,811,028,992 bytes.
`diagnostics/nat-model-attempt-1.*` then isolates only the reflexivity proof for
the actual decoded Nat program: that run was interrupted after 364.546452
seconds / 3,658,272,768 bytes. This compiler-exit isolation identifies expensive
model conversion independently of the generic sequence proof, which passed.
The subsequent approach quotes a proof-free data view from the actual decoder,
kernel-checks readback, and uses controlled state-rewrite proofs.
