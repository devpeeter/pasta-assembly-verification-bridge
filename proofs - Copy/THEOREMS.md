# Arithmetic proof inventory

The recorded proof results predate the current CLI/CI revision. The complete
Windows clean check passed on 2026-10-23; full verification of the current
revision is **NOT RUN**. See [RESULTS.md](../RESULTS.md) for dated automated checks.

The first section inventories the reused arithmetic model theorems. The checked addition target and its execution-to-model correspondence are inventoried separately in `ADDITION_CORRECTNESS_THEOREM.md`, `NAT_THEOREMS.md` and `PARAMETRIC_THEOREMS.md`. No theorem verifies the Rust compiler or Charon itself.

## Arithmetic endpoints (source closure PASS)

The serial rebuild checked all thirteen retained modules, including the two endpoint wrappers. Both wrappers depend only on `propext`, `Classical.choice`, and `Quot.sound`. Commands, individual module wall times, peak memory, and the current total are in `../evidence/arithmetic-serial-build.json` and `../evidence/arithmetic-modules/`; imported Mathlib dependencies are cached. This is arithmetic model verification, not target program verification.

`PastaAssemblyBridge.Arithmetic.addition` has this exact source statement:

```lean
theorem addition (F : PastaField) (lhs rhs : Limbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hlhs_lt : lhs.toNat < F.modulus.toNat)
    (hrhs_lt : rhs.toNat < F.modulus.toNat) :
    let res := addMod lhs rhs F.modulus
    res.Bounded ∧ res.toNat < F.modulus.toNat ∧
      res.toNat ≡ lhs.toNat + rhs.toNat [MOD F.modulus.toNat]
```

`PastaAssemblyBridge.Arithmetic.multiplication` has this exact source statement:

```lean
theorem multiplication (F : PastaField) (lhs rhs : Limbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hcontract : mulContract lhs rhs F.modulus = true) :
    let res := mulMont lhs rhs F.modulus F.inv
    res.Bounded ∧ res.toNat < F.modulus.toNat ∧
      2^256 * res.toNat ≡ lhs.toNat * rhs.toNat [MOD F.modulus.toNat]
```

`Limbs.Bounded` requires each of four natural-number limbs to be strictly less than `2^64`. The two `PastaField` instances are the upstream `pallasBase` (`Fp`) and `vestaBase` (`Fq`). Their constants, modulus shape, Montgomery inverse conditions, and primality certificates are defined and proved in the retained upstream files. The generic field theorem quantifies over every `PastaField`, so both concrete fields instantiate it.

`mulContract` is the exact upstream disjunction: either `lhs.toNat < p`, or `rhs.toNat < p` together with `rhs.l1 + 3 ≤ 2^64`, `rhs.l2 + 3 ≤ 2^64`, `rhs.l3 + 3 ≤ 2^64`. The boundedness assumptions apply to both inputs in either branch. This includes a lazy left operand in the second branch; merely assuming both values are below `2^256` does not establish that contract.

Addition reuses `PastaCurves.AArch64.addMod_spec_of_lt`. Multiplication reuses `mulContract_iff`, `mulMont_spec_of_lhs_lt`, and `mulMont_spec_of_rhs_lt`. No upstream theorem body or generated transcription is edited.

## Complete target endpoints

The delivered `AdditionCorrectness.addition_correct` and `MulCorrectness.multiplication_correct` endpoints compose separately proved execution-to-model correspondence with the arithmetic statements above. They concern the actual retained Kraken programs under every admissible binding, arbitrary incoming flags and scratch contents, and complete memory/SP/protected-register frames. Their postconditions include retained-artifact correspondence. Neither public target assumes program/model correspondence. Exact contracts and the current integrated verification status are in `ADDITION_CORRECTNESS_THEOREM.md`, `MUL_CORRECTNESS_THEOREM.md` and `../RESULTS.md`; archived narrower-policy checks do not certify a changed allocation domain.

## Existing machine prototype audit

The requested prior work is available at commit `741a99456144eb1af25dad630f8aa05db721773a` in `zcash/pasta_curves`, branch `asm/2-machine-model`. Its `lean/PastaAArch64Asm/Machine.lean` models 31 general registers, a carry value, memory, and SP. Its generic `run_mem`, `run_sp`, and `run_reg_of_not_mem` show frames for its own restricted instruction datatype. `MachineAdd.lean` supplies a handwritten twelve-instruction addition list and proves equivalence to the arithmetic model for a globally injective operand allocation, with unconstrained initial scratch values and carry.

The handwritten instruction list is explicitly labeled a prototype by its upstream comment. It is not copied into this package. Global injectivity forbids legal sharing among equal-valued read-only inputs. The machine datatype is not Kraken semantics, and the prototype is not linked to structured Charon operands or an extraction artifact. Its results therefore do not discharge the required bridge, alias coverage, or artifact provenance obligations. Its Apache-2.0 notice must be retained if code is reused; this package only audits that source.

## Source and license preservation

`../vendor/pasta/UPSTREAM.json` records exact SHA-256 digests for every retained upstream source and notice at commit `e3c0f0246f56d351f1a94ff0a74c8d201dbf87d9`. The minimal Lean import closure is twelve files. It retains the generated upstream value transcription unchanged because existing arithmetic proofs refer to that model; the extraction-to-machine bridge must establish correspondence to it rather than treating its presence as extraction verification. Upstream MIT/Apache-2.0 licenses and the assembly attribution README are retained verbatim.

## Kraken word-semantic helper statements

These seven helper theorems concern the exact BitVec value/flag formulas used by pinned Kraken semantics. They accept arbitrary 64-bit words and either incoming carry. They do not execute a complete program, prove allocation coverage, or connect to the Charon artifact. The final measured direct Lean check passed; see the `kraken-word` stage in `../evidence/verification.json` and `../evidence/kraken-word.log`. The standalone `kraken-word.json` is historical.

```lean
theorem add_value (a b : BitVec 64) (carry : Bool) :
    (a + b + BitVec.ofNat 64 carry.toNat).toNat =
      (a.toNat + b.toNat + carry.toNat) % 2^64
```

```lean
theorem add_carry (a b : BitVec 64) (carry : Bool) :
    ((a + b + BitVec.ofNat 64 carry.toNat).unsigned !=
      a.unsigned + b.unsigned + (if carry then 1 else 0)).toNat =
      (a.toNat + b.toNat + carry.toNat) / 2^64
```

```lean
theorem adds_carry (a b : BitVec 64) :
    (StatusFlags.adds (a + b) a b).c.toNat =
      (a.toNat + b.toNat) / 2^64
```

```lean
theorem sub_value (a b : BitVec 64) (carry : Bool) :
    (a - b - BitVec.ofNat 64 (!carry).toNat).toNat =
      (a.toNat + 2^64 - b.toNat - (1 - carry.toNat)) % 2^64
```

```lean
theorem sub_carry (a b : BitVec 64) (carry : Bool) :
    (decide (a.unsigned >= b.unsigned + (if carry then 0 else 1))).toNat =
      (a.toNat + 2^64 - b.toNat - (1 - carry.toNat)) / 2^64
```

```lean
theorem subs_carry (a b : BitVec 64) :
    (StatusFlags.subs (a - b) a b).c.toNat =
      (a.toNat + 2^64 - b.toNat) / 2^64
```

```lean
theorem csel_cs_value (flags : StatusFlags) (x y : BitVec 64) :
    (if CondCode.CS.interp flags then x else y).toNat =
      (if flags.c.toNat = 0 then y.toNat else x.toNat)
```

## Kraken binding helper statements

These five helper theorems concern Kraken's actual `Reg64s` operations. `Separated written binding` requires separation of each written operand from every other operand, and imposes no injectivity restriction among read-only operands. `Admissible` also requires an allowed physical Rust `reg`: X0-X30 excluding X29, for the pinned default Linux AArch64 target. Generic allocation may use X19; see the pinned Rust/LLVM analysis in `../evidence/register-policy.json`. The previous 29-register check is archived; the widened policy and fresh dependent closure passed the final clean command. Equal read-only bindings imply equal values through consistent initial-state bindings. These are generic helper laws; they are not a complete allocation or frame theorem for the extracted addition program. The final measured direct Lean check passed; see the `kraken-binding` stage in `../evidence/verification.json` and `../evidence/kraken-binding.log`. The standalone `kraken-binding.json` is historical.

```lean
theorem get_set (regs : Reg64s) (written queried : XReg) (value : BitVec 64) :
    (regs.setXReg written value).getXReg queried =
      if queried = written then UInt64.ofBitVec value else regs.getXReg queried
```

```lean
theorem set_sp (regs : Reg64s) (written : XReg) (value : BitVec 64) :
    (regs.setXReg written value).SP = regs.SP
```

```lean
theorem get_set_binding {Operand : Type} [DecidableEq Operand]
    (regs : Reg64s) (written : Operand → Bool) (binding : Operand → XReg)
    (h : Separated written binding) (x y : Operand) (hx : written x = true)
    (value : BitVec 64) :
    (regs.setXReg (binding x) value).getXReg (binding y) =
      if y = x then UInt64.ofBitVec value else regs.getXReg (binding y)
```

```lean
theorem shared_input_values {Operand : Type}
    (regs : Reg64s) (binding : Operand → XReg) (values : Operand → UInt64)
    (hvalues : ∀ x, regs.getXReg (binding x) = values x)
    (x y : Operand) (hshare : binding x = binding y) : values x = values y
```

```lean
theorem readonly_sharing_admissible {Operand : Type} :
    Admissible (fun _ : Operand => false) (fun _ => XReg.X0)
```

## Primitive correspondence to the retained Pasta semantics

These three theorems connect the checked Kraken word formulas directly to existing Pasta `addc`, `subc`, and `cselCs` definitions. They passed a direct Lean check; the measured command, wall time, peak memory, and axiom census are in `../evidence/word-correspondence.json` and `.log`. They do not establish whole-program correspondence or field correctness of the extracted block.

```lean
theorem addc (a b : BitVec 64) (carry : Bool) :
    PastaCurves.addc a.toNat b.toNat carry.toNat =
      ((a + b + BitVec.ofNat 64 carry.toNat).toNat,
       ((a + b + BitVec.ofNat 64 carry.toNat).unsigned !=
        a.unsigned + b.unsigned + (if carry then 1 else 0)).toNat)
```

```lean
theorem subc (a b : BitVec 64) (carry : Bool) :
    PastaCurves.AArch64.subc a.toNat b.toNat carry.toNat =
      ((a - b - BitVec.ofNat 64 (!carry).toNat).toNat,
       (decide (a.unsigned >= b.unsigned + (if carry then 0 else 1))).toNat)
```

```lean
theorem cselCs (flags : StatusFlags) (x y : BitVec 64) :
    PastaCurves.AArch64.cselCs flags.c.toNat x.toNat y.toNat =
      (if CondCode.CS.interp flags then x else y).toNat
```

## Checked addition program instantiation and memory frame

The namespace below is `PastaBridge.AdditionMachine`. `Binding` abbreviates `Fin 15 → XReg`; `written i` means that operand `i` is 0–3 or 11–14. The rejecting instantiator traverses the actual retained parsed program. A private total specialization is accepted only through its checked equality with that rejecting instantiator.

```lean
instantiation_certificate (binding : Binding) :
  instantiatedProgram binding = .ok (boundProgram binding)

canonical_identity :
  instantiatedProgram canonicalBinding = .ok retainedAdditionProgram

canonical_inverse : ∀ i : Fin 15,
  canonicalOperand (canonicalBinding i) = some i

canonical_separated :
  KrakenBinding.Separated written canonicalBinding

binding_memory_frame (binding : Binding) (state : MachineData) :
  (runWithBinding binding state).map MachineData.dmem = .ok state.dmem
```

The first four declarations use only `propext`. `binding_memory_frame` uses the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. None uses `sorryAx` or a new correctness axiom. The checked memory statement quantifies over every physical binding and every initial machine state, including arbitrary flags, scratch values, and memory; it imposes no input bounds or register-separation assumption because addition does not access memory.

These declarations establish instantiation integrity and the memory frame. They do not establish arithmetic outputs, stack-pointer preservation, preservation of protected registers, or equivalence of all allocated executions with the arithmetic model. Unfinished proof attempts remain outside the delivered proof roots.

The extracted operand modes are also checked against the write classification:

```lean
written_matches_checked_modes : ∀ i : Fin 15,
  written i = modeWrites (additionExpectedOperandMode i)

retained_written_mask :
  (operandModesFromArtifact retainedCharonArtifact "add").map
    (List.map modeWrites) = .ok (List.ofFn written)
```

`modeWrites` maps read-only inputs to `false` and outputs/inouts to `true`. The first theorem uses only `propext`; the second uses the three standard axioms. These two statements connect the allocation policy's write mask to the checked extracted operand-mode projection. They do not assert arithmetic correctness.

## Single-instruction simulation and frame helpers

The checked `AdditionStep.lean` declarations, exact assumptions, final measurements and axiom census are listed in [STEP_THEOREMS.md](STEP_THEOREMS.md). They cover actual individual Kraken instructions and permit read-only sharing. They do not by themselves prove complete-program arithmetic correctness.

## Complete addition execution under register allocation

`PastaBridge.AdditionLift` is defined in `AdditionMachine.lean`. Its decoder traverses the retained parsed AST, rejecting unsupported instructions, widths, shifts and destinations; the two closed certificates below check the decoded program against that AST. No instruction list is transcribed into this module.

```lean
decoding_certificate :
  retainedAdditionProgram.mapM decodeDirective = .ok decodedProgram

encoding_certificate (binding : Binding) :
  encode binding decodedProgram = AdditionMachine.boundProgram binding

full_run_is_sequence (binding : Binding) (state : MachineData) :
  run (AdditionMachine.boundProgram binding) state =
    sequence binding decodedProgram state

all_bindings_simulation (binding : Binding)
    (separated : KrakenBinding.Separated AdditionStep.written binding)
    (state : MachineData) :
  AdditionStep.LiftedRel binding AdditionMachine.canonicalBinding
    (AdditionMachine.runWithBinding binding state)
    (run retainedAdditionProgram (canonicalState binding state))
```

`sequence` executes the actual Kraken singleton semantics. `full_run_is_sequence` proves its equality with the actual complete-program runner by induction, keeping the continuation opaque. `canonicalState` copies the fifteen operand values into canonical registers and retains the incoming flags. `LiftedRel` requires successful executions, equality of all fifteen corresponding final register reads, and equality of the complete flags. `Separated` requires each written operand's register to differ from every other operand's register. Read-only operands may share registers; their values are consequently equal. The theorem quantifies over arbitrary incoming flags, scratch contents, memory and stack pointer. Its scope includes all allowed physical bindings; it needs no arithmetic bounds because it proves allocation correspondence rather than field correctness.

The two certificates use only `propext`; the execution and simulation theorems use only the three standard axioms. No statement uses `sorryAx` or a new correctness axiom. The unified module passed in 69.80413 seconds with a measured peak working set of 914710528 bytes; see `../evidence/addition-machine-lift.json` and `.log`. The subsequent whole-program correspondence to Pasta `addMod` and the field endpoint are checked in the Nat/parametric and addition-correctness modules, respectively.

## Complete addition stack and register frames

The following statements, also in `PastaBridge.AdditionLift`, lift the actual single-instruction frame laws through the checked complete-program execution sequence.

```lean
binding_stack_frame (binding : Binding) (state : MachineData) :
  (AdditionMachine.runWithBinding binding state).map (fun final => final.regs.SP) =
    .ok state.regs.SP

binding_register_frame (binding : Binding) (state : MachineData) (queried : XReg)
    (isProtected : ∀ destination : Fin 15, AdditionStep.written destination = true →
      queried ≠ binding destination) :
  (AdditionMachine.runWithBinding binding state).map
    (fun final => final.regs.getXReg queried) = .ok (state.regs.getXReg queried)

binding_readonly_frame (binding : Binding) (state : MachineData)
    (separated : KrakenBinding.Separated AdditionStep.written binding)
    (queried : Fin 15) (readonly : AdditionStep.written queried = false) :
  (AdditionMachine.runWithBinding binding state).map
    (fun final => final.regs.getXReg (binding queried)) =
      .ok (state.regs.getXReg (binding queried))
```

All use only the three standard axioms. The stack statement has no register-separation or input-bound assumption. The register statement covers every physical register outside the written allocation; `Admissible` allocations therefore preserve reserved X29 unconditionally and preserve X19 whenever it is outside the written allocation. The read-only statement permits equal-valued read-only sharing. All statements quantify over arbitrary flags, scratch contents, memory and stack pointer. The frame extension passed in 27.042334 seconds with peak working set 849944576 bytes before its integration into the unified module. The final unified check is recorded in `../evidence/addition-machine-frames.json` and `.log`.

The universal retained-template/physical-binding certificate is specified in [BINDING_ARTIFACT_THEOREMS.md](BINDING_ARTIFACT_THEOREMS.md). It applies to every allowed register assignment, without injectivity, and connects the retained template directly to the instantiated program used by the machine proofs.

## Nat projection helpers

The exact checked one-step and generic sequence projection statements are in
[NAT_THEOREMS.md](NAT_THEOREMS.md), together with their allocation hypotheses,
arithmetic-specification reuse, axiom census, and measured resource use.

The checked abstraction and exact specialization of the existing arithmetic
functions are inventoried in [PARAMETRIC_THEOREMS.md](PARAMETRIC_THEOREMS.md).

## Complete addition field endpoint

The exact main theorem, fully expanded input contract and postcondition,
allocation domain, frame properties, retained-template and operand-metadata
certificates, axiom census, and measured proof resources are documented in
[ADDITION_CORRECTNESS_THEOREM.md](ADDITION_CORRECTNESS_THEOREM.md). The delivered
`AdditionCorrectness.addition_correct` requires only the stated admissible
allocation and bounded-field input contract; it has no correspondence premise.

## Complete multiplication execution and frames

The complete retained multiplication program's algorithmic decoder, canonical
readback, actual execution sequence, and whole-program memory, SP, protected and
read-only register frame theorems are inventoried in
[MUL_THEOREMS.md](MUL_THEOREMS.md), including supported typed forms, allocation
assumptions, exact statements, axiom census, and measured proof resources.

The kernel-certified multiplication mutation witnesses, exact nine theorem
statements, strict original-proposition rejection checks, axiom census and
measured resources are listed in
[MUL_NEGATIVE_THEOREMS.md](MUL_NEGATIVE_THEOREMS.md).

The promoted final multiplication target and fully expanded input and output
contracts are in [MUL_CORRECTNESS_THEOREM.md](MUL_CORRECTNESS_THEOREM.md). The
previous 29-register target and exact type/axiom audit passed, including the retained
raw-byte artifact certificate. The widened 30-register target, its dependency closure and the complete final clean rebuild all passed; see `../evidence/verification.json`.

The complete native-to-`mulMont` projection and closed correspondence for every
separated written allocation are specified in
[MUL_NAT_THEOREMS.md](MUL_NAT_THEOREMS.md). The exact retained JSON document,
operand declarations and universal template/native-program connection are
specified in [../bridge/MUL_THEOREMS.md](../bridge/MUL_THEOREMS.md).
