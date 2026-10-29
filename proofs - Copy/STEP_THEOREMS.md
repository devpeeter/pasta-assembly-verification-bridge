# Checked single-instruction simulation and frames

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

Status: **PASS** for `AdditionStep.lean`. The final measured direct Lean check exited 0 in **55.841633 seconds**, with **941,699,072 bytes** of direct-child Windows peak working set. `evidence/addition-step.json` records its exact command and `evidence/addition-step.log` records the printed axiom census. Earlier core-only/frame-only measurements are separate records.

This module contains no instruction stream. `instruction` builds one actual Kraken AArch64 instruction of `Kind.adds`, `adcs`, `adc`, `subs`, `sbcs`, or `csel`; the shifted forms use zero shift and conditional select uses `CS`. `step` invokes the real `PastaBridge.run` on that single instruction. These lemmas do not by themselves establish execution correspondence for the complete extracted program or its arithmetic outputs.

`Operand` is `Fin 15`, `Binding` is `Operand → XReg`, and `Source` is either an operand index or the literal zero register. `written i` is true exactly at indices 0–3 and 11–14. The separate checked operand metadata certificate ties this mask to the extraction.

`ReadRel binding canonical actual reference` states that all fifteen operand-indexed physical-register reads agree. `Rel` additionally requires equality of the complete NZCV status. It imposes no memory or SP equality. `LiftedRel` holds only when both `Except` results are successful states related by `Rel`.

`KrakenBinding.Separated written binding` requires every written operand's register to differ from every other operand's register. Read-only operands may share a physical register. Their equal values follow from register-read consistency; global injectivity is not assumed. `adds_initial` requires only `ReadRel`, so the two incoming flag states may be arbitrary and different. Later-step preservation uses the relation established after that first flag-setting instruction. Memory, stack and protected-register frame lemmas allow arbitrary initial contents.

## Exact checked declarations

The following source statements are in namespace `PastaBridge.AdditionStep`.

```lean
theorem read_sources (binding canonical : Binding) (actual reference : MachineData)
    (reads : ReadRel binding canonical actual reference) (source : Source) :
    actual.regs.getRegOrZr (sourceRegister binding source) =
      reference.regs.getRegOrZr (sourceRegister canonical source)
```

```lean
theorem store_rel (binding canonical : Binding) (actual reference : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (canonicalSeparated : KrakenBinding.Separated written canonical)
    (reads : ReadRel binding canonical actual reference)
    (destination : Operand) (isWritten : written destination = true)
    (actualValue referenceValue : BitVec 64) (sameValue : actualValue = referenceValue)
    (actualFlags referenceFlags : StatusFlags) (sameFlags : actualFlags = referenceFlags) :
    Rel binding canonical
      (store actual (binding destination) actualValue actualFlags)
      (store reference (canonical destination) referenceValue referenceFlags)
```

```lean
theorem adds_initial (binding canonical : Binding) (actual reference : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (canonicalSeparated : KrakenBinding.Separated written canonical)
    (reads : ReadRel binding canonical actual reference)
    (destination : Operand) (isWritten : written destination = true)
    (first second : Source) :
    LiftedRel binding canonical
      (step .adds binding destination first second actual)
      (step .adds canonical destination first second reference)
```

```lean
theorem preserve (kind : Kind) (binding canonical : Binding) (actual reference : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (canonicalSeparated : KrakenBinding.Separated written canonical)
    (related : Rel binding canonical actual reference)
    (destination : Operand) (isWritten : written destination = true)
    (first second : Source) :
    LiftedRel binding canonical
      (step kind binding destination first second actual)
      (step kind canonical destination first second reference)
```

```lean
theorem memory_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) :
    (step kind binding destination first second state).map MachineData.dmem = .ok state.dmem
```

```lean
theorem stack_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) :
    (step kind binding destination first second state).map (fun final => final.regs.SP) =
      .ok state.regs.SP
```

```lean
theorem register_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData) (queried : XReg)
    (isProtected : queried ≠ binding destination) :
    (step kind binding destination first second state).map
      (fun final => final.regs.getXReg queried) = .ok (state.regs.getXReg queried)
```

```lean
theorem readonly_frame (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (isWritten : written destination = true) (queried : Operand)
    (readonly : written queried = false) :
    (step kind binding destination first second state).map
      (fun final => final.regs.getXReg (binding queried)) =
        .ok (state.regs.getXReg (binding queried))
```

```lean
theorem related_results_exist (binding canonical : Binding)
    (actual reference : Except String MachineData)
    (related : LiftedRel binding canonical actual reference) :
    ∃ actualState referenceState,
      actual = .ok actualState ∧ reference = .ok referenceState ∧
        Rel binding canonical actualState referenceState
```

```lean
theorem interp_of_step [Labels] (kind : Kind) (binding : Binding) (destination : Operand)
    (first second : Source) (state after : MachineData)
    (executed : step kind binding destination first second state = .ok after)
    (position : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) :
    (instruction kind binding destination first second).interp state position next jump =
      .require_exec_access position (fun _ => next after)
```

## Axiom census

The printed census for `adds_initial`, `preserve`, all four frame lemmas, and `interp_of_step` is exactly `propext`, `Classical.choice`, `Quot.sound`. `related_results_exist` uses `propext` and `Quot.sound`. The support lemmas `read_sources` and `store_rel` are checked dependencies of these declarations. No successful declaration depends on `sorryAx` or a new correctness axiom. These single-step relational/frame facts support the separately checked complete execution-to-model correspondence and field endpoint; their exact declarations and current integrated status are in `NAT_THEOREMS.md`, `ADDITION_CORRECTNESS_THEOREM.md` and `../RESULTS.md`.
