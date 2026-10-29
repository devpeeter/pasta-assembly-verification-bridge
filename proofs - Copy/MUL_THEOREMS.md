# Multiplication execution and frame theorems

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

The allocation policy now admits X19 and reserves X29, giving 30 potential
generic registers. The widened dependency closure passed the 2026-10-23 clean check; prior
measurements below remain historical narrower-policy results.

`MulStep.lean` and `MulMachine.lean` use the actual Kraken AArch64 semantics.
The machine module algorithmically decodes all 135 retained instructions; it
contains no transcribed instruction list. It rejects unrecognized instructions,
directives, widths, physical registers, conditions, shifts, immediates, and
operand forms. A destination must be one of the extracted output operands.

`MulStep.Operand` is `Fin 21`; `Binding` is `Operand → XReg`. The write mask is
`written i := 11 ≤ i.val`. Inputs 0–10 are read-only, and outputs 11–20 are early
outputs. Canonical roles 0–18 use X0–X18, role 19 uses X20, and role 20 uses X21.

Typed instruction constructors cover ADDS, ADCS, ADC, SUBS, SBCS, CSEL with CC
(the LO spelling), MADD with zero accumulator (MUL), UMULH, 64-bit immediate
LSL/LSR, SUBS with zero destination and immediate 1, and MOVZ with immediate
`0x4000` shifted by 48. The shift constructors require `Fin 64`, so an invalid
shift amount has no representation. SUBS with zero destination has a real
physical-register source and no write destination; it does not substitute a
fake register for SP or XZR. MOV's parsed native form represents `2^62`.

The checked readback and execution statements, in `PastaBridge.MulMachine`, are:

```lean
decoding_certificate :
  retainedMultiplicationProgram.mapM decodeDirective = .ok decodedProgram

instantiation_certificate (binding : Binding) :
  instantiatedProgram binding = .ok (boundProgram binding)

canonical_identity :
  boundProgram canonicalBinding = retainedMultiplicationProgram

valid_certificate : decodedProgram.all validBoolean = true

decoded_valid (operation : MulStep.Instruction)
    (member : operation ∈ decodedProgram) : MulStep.Valid operation

full_run_is_sequence (binding : Binding) (state : MachineData) :
  run (boundProgram binding) state = sequence binding decodedProgram state
```

`Valid operation` requires every physical write destination to satisfy the
extracted write mask. `instantiatedProgram` rejects decoding failures;
`boundProgram` encodes the checked decoded list under a physical binding.
`sequence` invokes the actual Kraken singleton runner at every step.
`full_run_is_sequence` proves its equality with the complete actual Kraken
runner by induction with an opaque continuation.

The complete frame theorems are:

```lean
binding_memory_frame (binding : Binding) (state : MachineData) :
  (runWithBinding binding state).map MachineData.dmem = .ok state.dmem

binding_stack_frame (binding : Binding) (state : MachineData) :
  (runWithBinding binding state).map (fun after => after.regs.SP) =
    .ok state.regs.SP

binding_register_frame (binding : Binding) (state : MachineData) (queried : XReg)
    (isProtected : ∀ d, written d = true → queried ≠ binding d) :
  (runWithBinding binding state).map (fun after => after.regs.getXReg queried) =
    .ok (state.regs.getXReg queried)

binding_readonly_frame (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated written binding) (queried : Fin 21)
    (readonly : written queried = false) :
  (runWithBinding binding state).map
    (fun after => after.regs.getXReg (binding queried)) =
    .ok (state.regs.getXReg (binding queried))
```

Memory and SP preservation require no input bounds or allocation separation.
The protected-register statement covers every register outside the written
allocation. `Admissible` excludes X29 from the operand allocation, so X29 is
preserved unconditionally. X19 is preserved when it is outside the written
allocation. `Separated` separates written operands from
all other operands; read-only inputs may alias and then have equal values. All
statements quantify over arbitrary incoming flags, scratch values, memory, SP,
and other registers.

The actual single-instruction frame and CPS glue theorem statements are:

```lean
MulStep.memory_frame operation binding state :
  (MulStep.step operation binding state).map MachineData.dmem = .ok state.dmem

MulStep.stack_frame operation binding state :
  (MulStep.step operation binding state).map (fun after => after.regs.SP) =
    .ok state.regs.SP

MulStep.register_frame operation binding state queried
    (isProtected : ∀ d, MulStep.destination operation = some d →
      queried ≠ binding d) :
  (MulStep.step operation binding state).map
    (fun after => after.regs.getXReg queried) =
    .ok (state.regs.getXReg queried)

MulStep.readonly_frame operation binding state
    (separated : KrakenBinding.Separated MulStep.written binding)
    (valid : MulStep.Valid operation) queried
    (readonly : MulStep.written queried = false) :
  (MulStep.step operation binding state).map
    (fun after => after.regs.getXReg (binding queried)) =
    .ok (state.regs.getXReg (binding queried))

MulStep.interp_of_step [Labels] operation binding state after
    (executed : MulStep.step operation binding state = .ok after)
    (position : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) :
  (MulStep.instruction operation binding).interp state position next jump =
    .require_exec_access position (fun _ => next after)
```

Both modules passed pinned Lean 4.31.0 with `-DautoImplicit=false`, without
warnings. `MulStep` took 32.019528 seconds and peak working set 942,960,640
bytes; `MulMachine` took 70.344862 seconds and peak working set 938,283,008
bytes. These are direct Lean process measurements. The machine readback and
validity declarations use `propext` and `Quot.sound`; the execution/frame
declarations use only `propext`, `Classical.choice`, and `Quot.sound`. There is
no `sorryAx` or new correctness axiom. Exact commands and censuses are retained
in `../evidence/mul-step.json`, `.log`, `mul-machine.json`, and `.log`.

These execution and frame declarations do not alone establish multiplication
arithmetic correctness. That requires the separately checked native-to-Nat
projection, retained-program correspondence to upstream `mulMont`, and the
field endpoint.
