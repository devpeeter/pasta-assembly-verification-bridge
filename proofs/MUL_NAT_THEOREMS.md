# Multiplication Kraken semantics and arithmetic model bridge

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

The instruction data is mechanically quoted from `MulMachine.decodedProgram`,
which is decoded from the checked Kraken program. No instruction list is
transcribed in these modules. `MulProgramData.retained_instructions_readback`
checks the quote against that decoded program. The five chunk definitions use
`take`/`drop` on this same data; `program_partition` checks complete reassembly.

`MulNat.project` observes all 21 operand registers and the carry flag. Its
initial argument is arbitrary `MachineData`: no flags, scratch words, memory,
stack pointer or unrelated registers are initialized by these proofs.
`KrakenBinding.Separated written binding` separates every writable operand
(indices 11 through 20) from every other operand. It permits sharing among
read-only operands (indices 0 through 10); the full endpoint separately checks
that their common physical values satisfy the stated input contract.

The parametric candidates are produced from the existing Pasta definitions by
replacing seven arithmetic constants and the repeated round function with
function parameters. The specialization equalities are checked by the kernel.
The three round comparisons and the complete model comparison are structural
proofs for arbitrary operation functions; specialization then recovers the
existing `mulMont` without adding a correctness axiom.

The model observation roles are: lhs 0–3, rhs 4–7, modulus 8,9,0,2^62,
inverse 10, and result 16–19. Arithmetic input bounds and the field contracts
are imposed by the final `MulCorrectness` endpoint, not by an extra model
correspondence premise.

The exact principal declarations below are copied from delivered source. Lean's
reported axiom lists are retained in the corresponding evidence logs. Every
delivered declaration listed here has been compiled successfully; the only
axioms permitted in this inventory are `propext`, `Quot.sound`, and
`Classical.choice`. No `native_decide`, `sorryAx`, or custom correctness axiom
is used.

## MulWord

Checked in 77.143865 s; peak direct-child working set 910,036,992 bytes. [Source](MulWord.lean), [evidence](../evidence/mul-word.json).

```lean
theorem mul_value (a b : BitVec 64) :
    (a * b + (0 : BitVec 64)).toNat = PastaCurves.mulLo a.toNat b.toNat
```

```lean
theorem umulh_value (a b : BitVec 64) :
    (BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)).toNat =
      PastaCurves.umulh a.toNat b.toNat
```

```lean
theorem lsl_value (word : BitVec 64) (amount : Nat) :
    (word <<< amount).toNat = PastaCurves.lsl word.toNat amount
```

```lean
theorem lsr_value (word : BitVec 64) (amount : Nat) :
    (word.ushiftRight amount).toNat = PastaCurves.lsr word.toNat amount
```

```lean
theorem csel_lo_value (flags : StatusFlags) (x y : BitVec 64) :
    (if CondCode.CC.interp flags then x else y).toNat =
      PastaCurves.AArch64.cselLo flags.c.toNat x.toNat y.toNat
```

```lean
theorem shift_amount (amount : Fin 64) :
    (Int64.toInt (Int64.ofNat amount.val)).toNat = amount.val
```

```lean
theorem mask_value :
    (((BitVec.ofInt 64 (Int64.toInt (0x4000 : Int64))) &&&
      (0xFFFF : BitVec 64)) <<< (48 : Nat)).toNat = 2^62
```

## MulNat

Checked in 49.952958 s; peak direct-child working set 933,228,544 bytes. [Source](MulNat.lean), [evidence](../evidence/mul-nat.json).

```lean
theorem read_project (binding : Binding) (state : MachineData) (source : Source) :
    @BitVec.toNat 64 (state.regs.getRegOrZr (sourceRegister binding source)) =
      read (project binding state) source
```

```lean
theorem physical_project (binding : Binding) (state : MachineData) (i : Operand) :
    @BitVec.toNat 64 (state.regs.getRegOrSp (physicalRegister binding i)) =
      (project binding state).words i
```

```lean
theorem store_project (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding)
    {operation : Instruction} (valid : Valid operation)
    (value : BitVec 64) (flags : StatusFlags) :
    project binding (store binding state (destination operation) value flags) =
      update (project binding state) (destination operation) value.toNat flags.c.toNat
```

```lean
theorem step_project (operation : Instruction) (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) (valid : Valid operation) :
    (step operation binding state).map (project binding) =
      .ok (transition operation (project binding state))
```

## MulNatSequence

Checked in 33.282370 s; peak direct-child working set 918,355,968 bytes. [Source](MulNatSequence.lean), [evidence](../evidence/mul-nat-sequence.json).

```lean
theorem sequence_project (binding : Binding) (program : List Instruction)
    (state : MachineData) (separated : KrakenBinding.Separated written binding)
    (valid : ∀ operation ∈ program, Valid operation) :
    (MulMachine.sequence binding program state).map (project binding) =
      .ok (sequence program (project binding state))
```

```lean
theorem decoded_sequence_project (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (MulMachine.sequence binding MulMachine.decodedProgram state).map (project binding) =
      .ok (sequence MulMachine.decodedProgram (project binding state))
```

## MulParametricBase

Checked in 19.870048 s; peak direct-child working set 954,871,808 bytes. [Source](MulParametricBase.lean), [evidence](../evidence/mul-parametric-base.json).

```lean
theorem transition_specializes : transition actualArithmetic = MulNat.transition
```

```lean
theorem round_specializes : round actualArithmetic = PastaCurves.AArch64.mulMontRound
```

```lean
theorem model_specializes : model actualArithmetic PastaCurves.AArch64.mulMontRound =
    PastaCurves.AArch64.mulMont
```

```lean
theorem sequence_specializes (program : List Instruction) (state : State) :
    sequence actualArithmetic program state = MulNat.sequence program state
```

```lean
theorem program_partition : MulProgramData.retainedInstructions =
    initial ++ firstRound ++ secondRound ++ thirdRound ++ epilogue
```

```lean
theorem sequence_readonly (ops : Arithmetic) (program : List Instruction)
    (valid : ∀ operation ∈ program, Valid operation) (state : State) (query : Operand)
    (readonly : written query = false) :
    (sequence ops program state).words query = state.words query :=
  MulSequenceFrame.readonly MulNat.State.words (transition ops) (transition_readonly ops)
    program valid state query readonly

theorem sequence_append (ops : Arithmetic) (first second : List Instruction) (state : State) :
    sequence ops (first ++ second) state = sequence ops second (sequence ops first state)
```

## MulParametricRounds

Checked in 21.159524 s; peak direct-child working set 963,059,712 bytes. [Source](MulParametricRounds.lean), [evidence](../evidence/mul-parametric-rounds.json).

```lean
theorem firstRound_model (ops : Arithmetic) (state : State) :
    accumulator (sequence ops firstRound state) =
      round ops (lhs state) (modulus state) (inv state) (state.words 5)
        (accumulator state)
```

```lean
theorem secondRound_model (ops : Arithmetic) (state : State) :
    accumulator (sequence ops secondRound state) =
      round ops (lhs state) (modulus state) (inv state) (state.words 6)
        (accumulator state)
```

```lean
theorem thirdRound_model (ops : Arithmetic) (state : State) :
    accumulator (sequence ops thirdRound state) =
      round ops (lhs state) (modulus state) (inv state) (state.words 7)
        (accumulator state)
```

## MulParametricModel

Checked in 227.049348 s; peak direct-child working set 957,423,616 bytes. [Source](MulParametricModel.lean), [evidence](../evidence/mul-parametric-model.json).

```lean
theorem generic_model (ops : Arithmetic) (state : State) :
    output (sequence ops MulProgramData.retainedInstructions state) =
      model ops (round ops) (lhs state) (rhs state) (modulus state) (inv state) :=
  generic_model_of_rounds ops (round ops) (firstRound_model ops) (secondRound_model ops)
    (thirdRound_model ops) state

section
attribute [local irreducible] MulSequenceFrame.sequence transition round model output lhs rhs modulus inv MulNat.sequence

theorem retained_data_model (state : State) :
    output (MulNat.sequence MulProgramData.retainedInstructions state) =
      PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (inv state)
```

```lean
theorem retained_data_model (state : State) :
    output (MulNat.sequence MulProgramData.retainedInstructions state) =
      PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (inv state)
```

## MulNatLift

Checked in 37.867038 s; peak direct-child working set 916,574,208 bytes. [Source](MulNatLift.lean), [evidence](../evidence/mul-nat-lift.json).

```lean
theorem decoded_program_model (state : State) :
    output (sequence MulMachine.decodedProgram state) =
      PastaCurves.AArch64.mulMont (lhs state) (rhs state) (modulus state) (inv state) :=
  (congrArg (fun program => output (sequence program state))
    MulProgramData.retained_instructions_readback).trans (MulParametric.retained_data_model state)

attribute [local irreducible] lhs rhs modulus inv output

theorem all_bindings_model (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (MulMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.mulMont (lhs (project binding state))
        (rhs (project binding state)) (modulus (project binding state)) (inv (project binding state)))
```

```lean
theorem all_bindings_model (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) :
    (MulMachine.runWithBinding binding state).map (fun after => output (project binding after)) =
      .ok (PastaCurves.AArch64.mulMont (lhs (project binding state))
        (rhs (project binding state)) (modulus (project binding state)) (inv (project binding state)))
```

Whole-program frame and checked artifact correspondence declarations are documented in the machine/artifact inventories and final endpoint source.
