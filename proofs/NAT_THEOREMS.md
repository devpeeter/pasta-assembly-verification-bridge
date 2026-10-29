# Nat projection and sequence correspondence

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

`AdditionNat.lean` and `AdditionNatSequence.lean` are checked. They contain no
target instruction list: the first handles one of six instruction kinds, and
the second handles an arbitrary list of the checked `AdditionLift.Decoded`
representation.

The measured direct Lean checks passed in 98.292112 seconds / 928,321,536 bytes
and 73.873383 seconds / 915,759,104 bytes respectively. The records are
`evidence/addition-nat.json` and `evidence/addition-nat-sequence.json`, with exact
commands and logs. Memory is the direct child Windows peak working set.

`State.words` is `Fin 15 → Nat` and `State.carry` is a natural number. `project`
reads the bound physical registers using `UInt64.toNat` and the incoming carry
using `Bool.toNat`. `transition` uses the existing `PastaCurves.addc`,
`PastaCurves.AArch64.subc`, and `PastaCurves.AArch64.cselCs`. It does not introduce
a replacement arithmetic specification.

`step_project` quantifies over every initial `MachineData`, including all NZCV
bits, scratch contents, and memory. Its only allocation hypothesis is separation
of each written operand from every other operand. Read-only operands may share
registers; equal read values follow from reading the same physical register.
`sequence_project` lifts this fact through the actual Kraken sequence executor.
The generic `bind_project` theorem has no machine-specific parameter or axiom.

The following exact statements are in namespace `PastaBridge.AdditionNat`.

```lean
theorem read_project (binding : Binding) (state : MachineData) (source : Source) :
    (state.regs.getRegOrZr (sourceRegister binding source)).toNat =
      read (project binding state) source
```

```lean
theorem read_project64 (binding : Binding) (state : MachineData) (source : Source) :
    @BitVec.toNat 64 (state.regs.getRegOrZr (sourceRegister binding source)) =
      read (project binding state) source
```

```lean
theorem native_shift_zero (word : Width.W64.type) :
    word <<< (0 : Nat) = word
```

```lean
theorem scalar_shift_zero (word : BitVec 64) :
    word <<< (0 : Nat) = word
```

```lean
theorem store_project (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (destination : Operand) (isWritten : written destination = true)
    (value : BitVec 64) (flags : StatusFlags) :
    project binding (store state (binding destination) value flags) =
      update (project binding state) destination value.toNat flags.c.toNat
```

```lean
theorem step_project (kind : Kind) (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    (destination : Operand) (isWritten : written destination = true)
    (first second : Source) :
    (step kind binding destination first second state).map (project binding) =
      .ok (transition kind destination first second (project binding state))
```

```lean
theorem bind_project {A B : Type} (first : Except String A)
    (rest : A → Except String A) (project : A → B) (next : B) (finish : B → B)
    (firstProjects : first.map project = .ok next)
    (restProjects : ∀ state, (rest state).map project = .ok (finish (project state))) :
    (first.bind rest).map project = .ok (finish next)
```

```lean
theorem machine_sequence_nil (binding : Binding) (state : MachineData) :
    AdditionLift.sequence binding [] state = .ok state
```

```lean
theorem machine_sequence_cons (binding : Binding) (instruction : AdditionLift.Decoded)
    (remaining : List AdditionLift.Decoded) (state : MachineData) :
    AdditionLift.sequence binding (instruction :: remaining) state =
      (AdditionStep.step instruction.kind binding instruction.destination
        instruction.first instruction.second state).bind
        (fun after => AdditionLift.sequence binding remaining after)
```

```lean
theorem sequence_project (binding : Binding) (program : List AdditionLift.Decoded)
    (state : MachineData) (separated : KrakenBinding.Separated written binding) :
    (AdditionLift.sequence binding program state).map (project binding) =
      .ok (sequence program (project binding state))
```

The printed axiom census for `step_project` and `sequence_project` is exactly
`propext`, `Classical.choice`, `Quot.sound`. `bind_project` uses no axioms. The
other support declarations are checked dependencies. No delivered declaration
depends on `sorryAx` or a new correctness axiom. These sequence/projection
lemmas alone do not state the final field arithmetic postcondition.

## Checked data and field observations

`AdditionNatData.lean` erases only the decoder's proof field and quotes the
remaining instruction data directly from the checked retained program. It
does not contain a manually copied instruction list. The closed
`retained_data_readback` equality and generic `sequence_erase` theorem connect
that quoted list to the same Nat execution sequence.

`AdditionNatObservation.lean` provides generic read, update, transition, and
sequence projection laws. It supports observing one field while keeping whole
states opaque; these are proved by reflexivity or cases on an instruction kind.
Its printed transition/sequence/update axiom census is empty.

The exact data statements below are in `PastaBridge.AdditionNatData`.

```lean
theorem retained_data_readback :
    AdditionLift.decodedProgram.map erase = retainedData
```

```lean
theorem sequence_erase (program : List AdditionLift.Decoded) (state : AdditionNat.State) :
    AdditionNat.sequence program state = sequence (program.map erase) state
```

```lean
theorem retained_sequence (state : AdditionNat.State) :
    AdditionNat.sequence AdditionLift.decodedProgram state = sequence retainedData state
```

The observation source contains two namespace blocks, first `PastaBridge.AdditionNat`, then `PastaBridge.AdditionNatData` for the four sequence laws.

```lean
theorem read_operand (state : State) (operand : AdditionStep.Operand) :
    read state (.operand operand) = state.words operand
```

```lean
theorem read_zero (state : State) : read state .zero = 0
```

```lean
theorem words_update (state : State) (destination query : AdditionStep.Operand)
    (value carry : Nat) :
    (update state destination value carry).words query =
      if query = destination then value else state.words query
```

```lean
theorem carry_update (state : State) (destination : AdditionStep.Operand)
    (value carry : Nat) :
    (update state destination value carry).carry = carry
```

```lean
theorem words_transition (kind : AdditionStep.Kind) (destination query : AdditionStep.Operand)
    (first second : AdditionStep.Source) (state : State) :
    (transition kind destination first second state).words query =
      if query = destination then
        let a := read state first
        let b := read state second
        match kind with
        | .adds => (PastaCurves.addc a b 0).1
        | .adcs | .adc => (PastaCurves.addc a b state.carry).1
        | .subs => (PastaCurves.AArch64.subc a b 1).1
        | .sbcs => (PastaCurves.AArch64.subc a b state.carry).1
        | .csel => PastaCurves.AArch64.cselCs state.carry a b
      else state.words query
```

```lean
theorem carry_transition (kind : AdditionStep.Kind) (destination : AdditionStep.Operand)
    (first second : AdditionStep.Source) (state : State) :
    (transition kind destination first second state).carry =
      let a := read state first
      let b := read state second
      match kind with
      | .adds => (PastaCurves.addc a b 0).2
      | .adcs => (PastaCurves.addc a b state.carry).2
      | .adc | .csel => state.carry
      | .subs => (PastaCurves.AArch64.subc a b 1).2
      | .sbcs => (PastaCurves.AArch64.subc a b state.carry).2
```

```lean
theorem words_sequence_nil (state : AdditionNat.State) (query : AdditionStep.Operand) :
    (sequence [] state).words query = state.words query
```

```lean
theorem words_sequence_cons (instruction : Instruction) (remaining : List Instruction)
    (state : AdditionNat.State) (query : AdditionStep.Operand) :
    (sequence (instruction :: remaining) state).words query =
      (sequence remaining (AdditionNat.transition instruction.kind instruction.destination
        instruction.first instruction.second state)).words query
```

```lean
theorem carry_sequence_nil (state : AdditionNat.State) :
    (sequence [] state).carry = state.carry
```

```lean
theorem carry_sequence_cons (instruction : Instruction) (remaining : List Instruction)
    (state : AdditionNat.State) :
    (sequence (instruction :: remaining) state).carry =
      (sequence remaining (AdditionNat.transition instruction.kind instruction.destination
        instruction.first instruction.second state)).carry
```

The data prefix passed in 199.216118 seconds / 904,835,072 bytes; the
observation prefix passed in 178.96157 seconds / 910,626,816 bytes. Exact commands,
source hashes, and logs are in `evidence/addition-nat-data.*` and
`evidence/addition-nat-observation.*`. The readback and retained-sequence
certificates use only `propext`; `sequence_erase` uses no axioms.

## Conditional composition helper

`AdditionNatLiftBase.lean` is a checked generic helper, not a closed arithmetic
correctness result. Its explicit `model : Correspondence` premise must be
discharged by a separate checked program/model theorem before it can establish
the target postcondition. `output` reads operand words 0–3, `rhs` reads 4–7,
and `modulus` is the tuple of words 8, 9, zero, and 10. These definitions use
the same operand roles as the field input contract.

```lean
def Correspondence : Prop := ∀ state : State,
  output (sequence AdditionLift.decodedProgram state) =
    PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state)
```

The following helper statements are in `PastaBridge.AdditionNat`.

```lean
theorem map_comp {A B C : Type} (execution : Except String A) (first : A → B) (second : B → C) :
    execution.map (fun value => second (first value)) =
      (execution.map first).map second
```

```lean
theorem all_bindings_model_of (model : Correspondence)
    (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (AdditionMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.addMod (output (project binding state))
        (rhs (project binding state)) (modulus (project binding state)))
```

The helper passed in 165.384634 seconds / 911,577,088 bytes. Its exact
command, source hash, and scope are in `evidence/addition-nat-lift-base.json`.
`map_comp` uses no axioms; `all_bindings_model_of` uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. The helper introduces no correctness
axiom and does not remove its stated premise.
## Closed correspondence for every separated binding

The `Correspondence` premise of the generic helper is now discharged by the
closed `decoded_program_model` theorem. `AdditionNatDataModel` imports the
checked parametric proof and specializes the data sequence to the existing
`PastaCurves.AArch64.addMod`; `AdditionNatModel` transfers it through the
kernel-checked data readback; `AdditionNatLift` composes it with the actual
Kraken execution projection. None of these three theorem statements assumes
a model-correspondence property.

`all_bindings_model` quantifies over every `MachineData` and every binding
whose written operands are separated. It assumes no initial flags, scratch
contents, or memory values. Read-only sharing is allowed. Allowed compiler
register classes and the retained-template equality are supplied separately
in the final field endpoint's admissibility contract and artifact certificate.
The result here is exact correspondence to `addMod`; field congruence and
output bounds are supplied by the existing arithmetic specifications there.

The direct checks passed in 23.475566 seconds / 910,458,880 bytes (DataModel),
42.395021 seconds / 907,538,432 bytes (Model), and 25.25302 seconds /
906,387,456 bytes (Lift). Exact source hashes, commands, and logs are in
`evidence/addition-nat-data-model.*`, `evidence/addition-nat-model.*`, and
`evidence/addition-nat-lift.*`. The first two closed statements use only
`propext`; the final all-bindings statement uses exactly `propext`,
`Classical.choice`, and `Quot.sound`.

In `PastaBridge.AdditionNatData`:

```lean
theorem retained_data_model (state : AdditionNat.State) :
    output (sequence retainedData state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state)
```

In `PastaBridge.AdditionNat`:

```lean
theorem decoded_program_model (state : State) :
    output (sequence AdditionLift.decodedProgram state) =
      PastaCurves.AArch64.addMod (output state) (rhs state) (modulus state)
```

In `PastaBridge.AdditionNat`:

```lean
theorem all_bindings_model (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (AdditionMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.addMod (output (project binding state))
        (rhs (project binding state)) (modulus (project binding state)))
```

