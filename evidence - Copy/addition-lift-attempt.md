# Superseded whole-program allocation proof attempt

`addition-lift-before-step-glue.lean.txt` is the exact source snapshot of the
first algorithmic decoding and allocation-lifting attempt. It is evidence,
outside the checked Lean source roots. Its theorems are **not delivered target
theorems**.

The checker was explicitly stopped after 256.977700 seconds, at a measured peak
working set of 880,312,320 bytes. The observed process exit was 4294967295.
The retained JSON contains the actual command and process measurements. The
checker had not flushed any diagnostics; this version did not instrument
declaration boundaries, so the exact expensive declaration is unconfirmed.
The attempt used definitional conversion of complete symbolic machine states
for `full_run_is_sequence`. A subsequent proof replaced that conversion with
induction using the checked one-instruction continuation lemma. That proof
passed and is delivered in `proofs/AdditionMachine.lean`, namespace
`PastaBridge.AdditionLift`; see `addition-machine-lift.log` and `.json`.

To replay after rebuilding the pinned Lean dependencies, copy the `.lean.txt`
snapshot to a work directory as `AdditionLift.lean`, use the same `LEAN_PATH`
as the documented proof command, and run the pinned Lean executable on that
file. The original invocation, relative to the workspace, was:

```powershell
work/toolchains/lean-4.31.0-windows/bin/lean.exe work/addition-machine-attempt/AdditionLift.lean
```

The proposition relates arbitrary allocated executions to canonical allocated
executions and permits read-only input aliases, provided all written operands
are separated. The successful allocation relation still requires composition
with the Pasta arithmetic model correspondence and arithmetic specifications to
establish field correctness. This retained failed approach is historical
evidence, not an unresolved allocation blocker.
