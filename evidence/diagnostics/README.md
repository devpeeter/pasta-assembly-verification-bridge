# Proof diagnostics

This is the exact failed candidate for the fixed canonical register allocation, not a delivered proof or target theorem. It is saved with `.lean.txt` so normal Lean builds do not import it. The failed Lean command and direct process measurement are retained alongside its complete log; an error-recovery `sorryAx` printed by that failed check is evidence of failure, not an accepted theorem.

All four stage markers ran. The final goal still contains the actual Kraken conditional-select word expressions and zero-shift terms; the attempted primitive rewrite pipeline did not normalize them to the retained Pasta `addMod` value function. This is unfinished proof engineering, not a discovered arithmetic counterexample. No correspondence premise or new correctness axiom substitutes for the missing proof.

After completing normal dependency bootstrap and the arithmetic source rebuild, reproduce with:

```powershell
python scripts/reproduce_canonical_failure.py --lean-bin C:/path/to/lean-4.31.0-windows/bin
```

The reproducer copies this exact candidate into the workspace `work/` directory, obtains the combined pinned Lean import paths, and runs Lean directly. Exit 1 is the observed failed proof check. Runtime depends heavily on host memory pressure; this diagnostic is excluded from the documented verification command and from successful proof timing totals.

The focused `NormalizationProbe.lean.txt` check subsequently passed (see `normalization-probe-4.json`). Full pretty-printing in probe 3 showed native `HShiftLeft` instances indexed by `Width.bits Width.W64`, while scalar rewrite lemmas use literal `64`. Lean simplification skips instance arguments by default. `dsimp (instances := true) only [Width.type, Width.bits]` normalizes these indices and makes the isolated native shift and conditional-selection checks pass. This diagnoses the matching problem; it is not a complete routine-correctness theorem.

The `nat-lift-attempt-*` and `nat-model-attempt-*` records preserve controlled
interruptions of expensive conversion attempts. Their nonzero exit codes,
wall times and OS peak working sets are retained. They are not passing proofs
or arithmetic counterexamples. The later generic sequence projection passed
using an abstract `Except` lemma instead of broad native-state simplification.

After rebuilding the delivered proof dependencies with the verification command,
an archived candidate can be selected explicitly:

```console
python scripts/reproduce_canonical_failure.py --lean-bin ../../work/toolchains/lean-4.31.0-windows/bin --source evidence/diagnostics/nat-model-attempt-1-source.lean.txt
```

This command reuses the checked compatibility overlay and current compiled proof
dependencies. Interrupted candidates may again consume substantial time and
memory; the reproducer does not impose a new resource limit. It records a new
measurement separately from the original evidence. These reproduction commands
are outside the target verification command.
