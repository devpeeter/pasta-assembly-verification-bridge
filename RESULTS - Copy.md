# Verification results

<!-- verification-status:start -->
**Historical full automated verification: PASS (2026-10-23). Current revision full verification: NOT RUN.**
Acceptance follows the required automated technical checks in
[ACCEPTANCE.md](ACCEPTANCE.md). GitHub Actions runs for this corrected local
revision remain **NOT RUN**. The preceding hosted failure is recorded below.

The Windows run on 2026-10-23 completed all 67 automated stages with exit code 0.
That result covers the assembly blocks from their register-entry states under
the documented contracts. It does not prove Rust wrapper argument loading or
result storage, and its vectors do not execute assembly on ARM hardware.
CLI and CI follow-ups have separate local evidence; the historical full run
does not certify changed script bytes.

Historical records are `evidence/verification.json`, `evidence/verification-exit.json`
and `evidence/final-clean-input-seal.json`. Their timestamps, source hashes and
results remain unchanged. Current automated acceptance criteria and execution
status are recorded separately in `evidence/acceptance.json`.
<!-- verification-status:end -->

## Scope, immutable tools and source

Only the complete AArch64 addition and Montgomery multiplication templates from
Pasta `e3c0f0246f56d351f1a94ff0a74c8d201dbf87d9` are in scope. Charon extracts
the unmodified crate: addition has 12 instructions, 15 operands and 86 template
pieces; multiplication has 135 instructions, 21 operands and 898 pieces. No
instruction list is maintained by hand. PR 159 was inspected; its handwritten
machine model and globally injective allocation assumption are not used.

| Component | Immutable pin |
| --- | --- |
| Rust | `nightly-2026-09-17`, compiler `923c95cdf5ba65cea505aa2ea829f578e1506ed8` |
| Charon | `53388d8887d106e46b4b1a24abe23498a38613e1`, version 0.1.282 |
| Aeneas proof context | `b86120db3183b0107eb5f2637b11c424cd06ef1c` |
| Kraken | `811ff7ce1dae0b9cae761585d33959f5302a2cc1` |
| Lean | 4.31.0, compiler `68218e876d2a38b1985b8590fff244a83c321783` |
| Mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |

`pins.json`, `lean-release.lock.json` and the Lake manifests fix source and
download contents. The Aeneas context predates Charon's structured assembly AST;
the bridge consumes the new LLBC directly and reuses existing proofs unchanged.
It does not claim new-LLBC compatibility with that older Aeneas executable.

Kraken's upstream snapshot is unchanged. Three exact build-overlay patches fix
the `List.allSome` namespace collision, parse bounded immediate LSL/LSR as
existing shifted ORR nodes, and allow destination XZR through the existing
immediate-arithmetic branch. Their SHA-256 values are
`7808946aee8db4c743b0af1e4904fbf942363a0305a27e003c6140306a400f4a`,
`9d21eea5b9768404e3faa91938c3e8ba613654ba93f055bb268f9393cf228f3a`, and
`19baac52a9fc44440c29a29c235dca3035233253c3b9c7bca4aa80c149e4cb59`.
Instruction-semantic bodies remain byte-identical to upstream. Selected modules
use Lean 4.31.0 despite the upstream nightly declaration.

## Historical implementer evidence (2026-10-23)

<!-- verification-checks:start -->
| Check | Actual result |
| --- | --- |
| Fresh extraction comparison of complete structured assembly subtrees | PASS |
| Policy, dependency, unsupported-feature and staleness tests | PASS; 59 tests |
| Arithmetic source closure and both universal field targets | PASS; 13 source arithmetic modules |
| Exact target types, standard-axiom censuses and retained representation links | PASS |
| Both formal carry/binding counterexamples and intended false-equality rejections | PASS |
| Addition Kraken model execution vectors | PASS; 3,232 cases, 5 allocations, 16 NZCV patterns |
| Addition mutants | PASS; carry 32, binding 32 semantic mismatches |
| Multiplication Kraken model execution vectors | PASS; 4,064 cases, 5 allocations, 16 NZCV patterns |
| Multiplication mutants | PASS; carry 192, binding 928 semantic mismatches |

Both runtime reports require X19-written and X19-shared-read-only executions for each field and all 16 NZCV patterns. Counts above come from the historical implementer clean run. Finite vectors supplement the universal proofs.
<!-- verification-checks:end -->

## Command-line review follow-up (2026-10-28)

**Local CLI checks: PASS.** Explicit
`--lean-bin` paths are resolved before subprocess working directories change.
Bootstrap's inconsistent `--work` override was removed; all builders use the
documented fixed workspace directory. Runtime labels now say **Kraken model
execution vectors**, explicitly Lean-host execution rather than ARM hardware.

The 5 focused regressions and all 64 unit tests passed with no skips.
The retained old verifier fails the new path regression in both caller directories,
so the test detects the reported defect. Real pinned Lean/Lake smoke checks also
passed from package and workspace callers. Exact commands, logs, timings and
tested source hashes are in `evidence/review-followup/cli-tests.json` and
`evidence/review-followup/real-cli-checks.json`.

All 101 original protected proof/pin/artifact files are byte-identical,
and all 453 original evidence files remain unchanged. The current scripts
have **not** received another full clean verification run. The previous full run
is retained as historical evidence; it does not cover changed script bytes.
The source delta is recorded in `evidence/review-followup/report.json`.

## GitHub Actions implementation (2026-10-28)

Two workflows are provided: `unit-integrity.yml` runs on pushes and pull
requests; `full-verification.yml` runs manually and on published releases.
Both use `windows-2025`, Python 3.11.9 and full action commit references.

<!-- ci-implementation-results:start -->
**Local CI implementation checks: PASS (2026-10-28, America/Toronto).** The exact
unit/integrity runner completed all 5 stages with exit 0 in 32.434612 s:
all 95 Python tests ran with zero omissions; source integrity covered
16 Pasta files, 112 Kraken files and 9 locked Git dependencies; both generated
freshness checks and the submitted source manifest passed. All 144 recorded
code/configuration/pin input hashes remained unchanged during that run.

Both workflows passed actionlint 1.7.12. The Python suite includes 13 full-CI
orchestration tests and failure-gate mutations; their tool builds/proof reports
are synthetic fixtures, not full verification evidence. Actual commands, logs,
source hashes and lint-tool provenance are retained in `evidence/ci-implementation/`.

GitHub Actions unit/integrity run: **NOT RUN**.
GitHub Actions full verification run: **NOT RUN**.
Fresh full toolchain/Lean verification for this CI revision: **NOT RUN**.

All 198 protected proof/pin/artifact/vendor files and 471 historical
evidence/log files were checked against the preceding source ZIP and remain
byte-identical. After recording this result, only documentation/evidence and
packaging-manifest metadata are refreshed; the tested code remains unchanged.
<!-- ci-implementation-results:end -->

Unit CI runs all Python tests, offline source/lock and retained-artifact
integrity checks, both generated-file freshness checks and the complete source
manifest check. It is not a fresh Charon extraction or Lean proof rebuild.
Full CI first requires the same unit/integrity gate, then bootstraps the pinned
dependencies in a new runtime tree with empty evidence/log directories. It
regenerates runner-specific extraction provenance, rejects changed complete
target templates/operands or checked program bytes, records the differences,
and runs exactly `python scripts/verify.py --clean`.

Automated full success requires actual exit 0, fresh complete `PASS` reports,
all required stages and both target gates, exact-type/standard-axiom audits,
proof measurements, model-vector mutants and intended formal-negative failures.
Missing tools, omitted proofs, stale evidence, `PARTIAL` reports, failed stages
or changed sealed inputs fail the job. The original checkout and historical
evidence must remain unchanged. Workflow artifacts retain command logs, all
reports, audits, source seals, baseline/fresh extraction provenance and measured
proof results even after failures. Compiled tools and caches are excluded.

Local orchestration fixtures do not establish a hosted run or a fresh full
proof run for this CI revision. A successful full job must satisfy every
automated technical criterion above. Runner image/download/cache availability
and disk/time headroom remain to be measured on the first actual hosted run.
Technical scope remains assembly-block register-entry correctness, with the
Rust wrapper load/store and ARM hardware limitations below. See
[workflow and upload instructions](.github/README.md).

## Automated acceptance cleanup (2026-10-28)

<!-- acceptance-cleanup-validation:start -->
Local cleanup validation: **PASS (2026-10-28, America/Toronto).**
The complete Python suite passed 95 tests with zero omissions. The actual
unit/integrity CI runner then passed all five stages, including its complete
Python-suite run, source/pin/lock integrity, generated-file freshness and the
source manifest. All 10 affected status-publisher regressions passed.
Commands, real exit codes, timings and logs are in `evidence/acceptance-cleanup/`.

All 203 checked proof/pin/artifact/workflow/verification files and
482 dated evidence/log files remain byte-identical. The full CI runner's
technical `require(...)` conditions and documented fenced Lean statements are
unchanged. Only the obsolete policy condition and its status expectations were
removed; incomplete `PARTIAL` verification still fails the automated gate.

Current-revision full verification: **NOT RUN**. GitHub unit and full workflows:
**NOT RUN**. The user selected ZIP delivery; no push or workflow dispatch occurred.
Result documentation, live acceptance status and packaging hashes are refreshed
after recording these tests; the tested code remains unchanged.
<!-- acceptance-cleanup-validation:end -->

## Hosted Windows path-alias fix (2026-10-29)

The [unit workflow](https://github.com/devpeeter/pasta-assembly-verification-bridge/actions/runs/40814585440)
failed one of 95 tests at `tests/test_ci_full.py:162` on source commit
`f5b61dbf85d646f15eb01f2c50ae0e977a703fec`. The same existing temporary directory
was spelled with `runneradmin` in the actual subprocess cwd and `RUNNER~1` in
the expected path. The preceding
[full workflow](https://github.com/devpeeter/pasta-assembly-verification-bridge/actions/runs/40815070636)
stopped at this initial unit gate; its bootstrap/full-proof step did not run.
These are observed hosted failures, not failed arithmetic proofs.

The test assertions now use `Path.samefile()` for existing staged directories,
private tool homes and related subprocess/tool paths. Literal command arguments,
absolute-tool requirements, proof/integrity checks and failure gates are retained.
The mock bootstrap creates its private home directories so identity comparisons
exercise existing filesystem objects. Regressions accept alternate spellings of
the same directory and reject genuinely different directories; no tests are omitted.

<!-- windows-path-ci-fix:start -->
Local validation: **PASS (2026-10-29, America/Toronto).** All 97 Python
tests passed with zero omissions, followed by all five stages of the actual
unit/integrity CI runner, including its own complete 97-test run. Exact
commands, exit codes, timings and logs are retained with the prior hosted failure
artifact in `evidence/windows-path-ci-fix/`.

Only the three affected test files change execution assertions. All 240
checked production/proof/pin/workflow files and 493 preceding historical
evidence/log files are byte-identical. No proof or verification failure check was
removed. Regression cases reject the wrong staged directory and wrong private
tool homes while accepting aliases of the correct existing directories.

Corrected-revision hosted unit/full workflows: **NOT RUN**. Current-revision full
proof verification: **NOT RUN**. Push was unavailable (`push: false`), so this
result is delivered as an updated source ZIP; no remote fix or successful hosted
rerun is claimed.
<!-- windows-path-ci-fix:end -->

The connected GitHub integration reports read access and `push: false` for the
repository. No push or workflow dispatch was attempted. The corrected source ZIP
is supplied for upload. Previous dated evidence and all production verification,
proof, pin and workflow sources are preserved.

## Acceptance and wrapper scope

Acceptance is determined by the recorded automated technical checks in
[ACCEPTANCE.md](ACCEPTANCE.md). The current revision's full run and both hosted
workflows remain **NOT RUN**; local checks and historical results are listed
separately above.

Both theorems take `MachineData` at the assembly block's register-entry state.
`InputContract` assumes that these registers already hold the intended limbs and
field constants. The compact checked representation omits the MIR operand-value
expressions and destination places. Retaining those expressions in full LLBC and
using a MIR evaluator for tests does not prove that the surrounding Rust wrapper
loads the intended argument limbs or stores the results in the correct Rust locations.
The endpoint therefore concerns assembly-block arithmetic and frames, not a proved
Rust-call result or end-to-end Rust wrapper correctness. This limitation remains.

## Exact public targets

```lean
theorem PastaBridge.AdditionCorrectness.addition_correct
    (field : PastaCurves.PastaField)
    (binding : PastaBridge.AdditionCorrectness.Binding) (state : MachineData)
    (admissible : PastaBridge.AdditionMachine.Admissible binding)
    (inputs : PastaBridge.AdditionCorrectness.InputContract field binding state) :
    ∃ after : MachineData,
      PastaBridge.AdditionMachine.runWithBinding binding state = .ok after ∧
      PastaBridge.AdditionCorrectness.Postcondition field binding state after

theorem PastaBridge.MulCorrectness.multiplication_correct
    (field : PastaCurves.PastaField)
    (binding : PastaBridge.MulCorrectness.Binding) (state : MachineData)
    (admissible : PastaBridge.MulMachine.Admissible binding)
    (inputs : PastaBridge.MulCorrectness.InputContract field binding state) :
    ∃ after : MachineData,
      PastaBridge.MulMachine.runWithBinding binding state = .ok after ∧
      PastaBridge.MulCorrectness.Postcondition field binding state after
```

Neither theorem assumes model correspondence. Exact expanded definitions are in
[ADDITION_CORRECTNESS_THEOREM.md](proofs/ADDITION_CORRECTNESS_THEOREM.md) and
[MUL_CORRECTNESS_THEOREM.md](proofs/MUL_CORRECTNESS_THEOREM.md). `Audit.lean` and
`MulAudit.lean` guard the public types and both field instances.

`Admissible` allows X0 through X30 except X29 and separates each written operand
from every other operand. The pinned Linux default `non-leaf` frame-pointer
policy reserves X29; generic `reg` may use X19 despite Rust rejecting that
explicit register name. SP and XZR are outside this class. Read-only inputs may
share registers; reading one physical register ensures equal values. Immutable
Rust/LLVM evidence is in `evidence/register-policy.json`. Function-specific
reservations may further reduce the allocation pool without weakening coverage.

Incoming NZCV, scratch contents, memory and SP are arbitrary. Both theorems
preserve memory, SP, every register outside the written allocation and read-only
inputs. X29 is preserved unconditionally; X19 is preserved whenever it is
outside the written allocation. `UInt64` supplies limb bounds.

Addition requires the supplied modulus words to equal the field modulus and
both inputs below it. The output is exactly existing `addMod`, is bounded and
below the modulus, and satisfies `output ≡ lhs + rhs [MOD p]`.

Multiplication supplies the field modulus/inverse and exact upstream
`mulContract`: `lhs.toNat < p`, or `rhs.toNat < p` and each of `rhs.l1 + 3`,
`rhs.l2 + 3`, `rhs.l3 + 3` is at most `2^64`. Both inputs are bounded. The output
is exactly `mulMont`, is bounded and below the modulus, and satisfies
`2^256 * output ≡ lhs * rhs [MOD p]`. This is Montgomery multiplication.

The field parameter covers `pallasBase` (Fp) and `vestaBase` (Fq). Existing
moduli, inverses, primality proofs and arithmetic proofs are reused unchanged.
The final arithmetic specifications are precisely:

```lean
PastaAssemblyBridge.Arithmetic.addition
    (F : PastaField) (lhs rhs : Limbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hlhs_lt : lhs.toNat < F.modulus.toNat)
    (hrhs_lt : rhs.toNat < F.modulus.toNat) :
    let res := addMod lhs rhs F.modulus
    res.Bounded ∧ res.toNat < F.modulus.toNat ∧
      res.toNat ≡ lhs.toNat + rhs.toNat [MOD F.modulus.toNat]

PastaAssemblyBridge.Arithmetic.multiplication
    (F : PastaField) (lhs rhs : Limbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hcontract : mulContract lhs rhs F.modulus = true) :
    let res := mulMont lhs rhs F.modulus F.inv
    res.Bounded ∧ res.toNat < F.modulus.toNat ∧
      2^256 * res.toNat ≡ lhs.toNat * rhs.toNat [MOD F.modulus.toNat]
```

## Explicit retained-artifact connection

`artifacts/pasta_curves.llbc` retains the full Charon result, `has_errors = false`.
`artifacts/charon-asm.json` retains both complete subtrees with SHA-256
`d5681b42cd2d5d1e33a3a8d53c381cb6cafce6728e58ad0303c38898f047ff9f`.
`artifacts/extraction-provenance.json` records commands, source bytes/Git
identities, compiler identity, binary hashes and raw artifact hashes.
The exact subtree pointers are
`/translated/fun_decls/0/body/Structured/body/statements/66/kind/InlineAsm/asm`
and `/translated/fun_decls/1/body/Structured/body/statements/87/kind/InlineAsm/asm`.

Fresh extraction compares complete structured assembly subtrees; retained raw
hashes, JSON-pointer links, and every generated byte/file are checked separately.
Addition's kernel certificate connects the compact JSON, structured
metadata, assembly text and actual typed Kraken candidate. Its universal
binding certificate checks the template against the allocated program.
Multiplication checks all 27,152 retained JSON bytes including the final LF,
using a total encoder and raw `List UInt8` included from the file. Its universal
template certificate checks the actual allocated AST for every allowed binding.
Metadata checks register class, modes, early outputs and represented options;
checked write masks connect those modes to allocation separation. Both public
postconditions explicitly include representation clauses.

Exact declarations are in [bridge/THEOREMS.md](bridge/THEOREMS.md),
[bridge/MUL_THEOREMS.md](bridge/MUL_THEOREMS.md) and
[bridge/JSON_ENCODING.md](bridge/JSON_ENCODING.md); helper statements are indexed
in [proofs/THEOREMS.md](proofs/THEOREMS.md). Kraken's partial parser produces an
untrusted candidate; total serializers and readback certificates check that
actual candidate. No parser-correctness axiom or handwritten list replaces it.

## Reproduction, negatives and measurements

After setup in `README.md`, run from this directory:

```console
python scripts/verify.py --clean
```

Addition gates multiplication in the same invocation. The command checks fresh
extraction, exact regeneration, dependency sources/pins, selected Kraken builds,
all 13 retained Pasta arithmetic source modules, every bridge/target module,
public types/axioms, Kraken model execution vectors and formal semantic negatives. Missing,
failed or skipped required checks prevent success. `--local-only` is diagnostic
and always reports incomplete verification.

Policy tests reject unsupported instructions, options and operands; illegal or
inconsistent sharing; reserved registers; uninitialized carry/scratch; altered
source/artifact links; and stale/extra generated files. Kernel-certified mutants
break carry propagation or operand binding by traversing the actual decoded
programs. Lean must establish the counterexamples and reject each intended
original false equality with its exact diagnostic. An unrelated parser/type
failure is not accepted as a semantic rejection.

Kraken model execution vectors run the Kraken model through Lean on the host,
not the original assembly on ARM hardware. They cover both fields, all 16 incoming
NZCV patterns, varying
scratch, allocations including X19 and equal read-only aliases, and
memory/SP/register frames. Multiplication covers both contract branches.
Finite vectors supplement the universal proofs.

<!-- verification-measurements:start -->
The historical implementer clean command took **3274.081270 s**. Direct Lean checks totalled **1140.288831 s**, with maximum individual peak **2,181,574,656 bytes**.

| Historical implementer clean check | Wall time | Peak direct-child memory |
| --- | ---: | ---: |
| `additioncorrectness` | 30.354161 s | 1,445,429,248 bytes |
| `proof-inventory` | 28.565895 s | 1,410,330,624 bytes |
| `muljsontextdagbase` | 44.569282 s | 2,181,574,656 bytes |
| `muljsontextdagfinal` | 22.918732 s | 1,802,600,448 bytes |
| `mulcorrectness` | 31.765274 s | 1,470,312,448 bytes |
| `mul-proof-inventory` | 23.210511 s | 1,416,138,752 bytes |

`evidence/final-measurements.json` lists every counted direct Lean check. These are actual Windows measurements; memory is not summed across processes.
<!-- verification-measurements:end -->

The measured host is Windows. Memory is direct-child `PeakWorkingSetSize` in
bytes, not a process-tree sum. Lean itself is measured for source proof checks;
cached imports contribute to its working set. The normal clean command rebuilds
retained Pasta sources and delivered checks while reusing checksum-checked tool
downloads and pinned imported dependency caches. It does not rebuild Lean or
every Mathlib dependency from source.

## Provenance trust and limits

Remaining trust includes Rust compiler/MIR production, Charon, source selection,
the full-LLBC-to-projection Python checks, file inclusion at elaboration, local
builds/downloads, upstream specifications, Kraken semantics, Lean and imported
libraries/caches. The MIR prefix/suffix evaluator used by vectors is test
infrastructure, not a proved Rust wrapper translation. Hashes detect changed
bytes relative to retained identities; they do not prove faithful extraction or
authenticate a compromised host.

Allowed logical axioms are `propext`, `Classical.choice` and `Quot.sound`. No
`sorryAx`, new correctness axiom, assumed assembly/model equality or native
proof evaluator is accepted. Compiler, allocator, assembler, binary, hardware
and constant-time verification are outside scope. Source spellings erased
before Charon's AST are handled by the immutable source boundary, not claimed
as reconstructed Rust syntax.

Parser failures, interrupted large JSON/string checks and restricted allocation
results remain under `evidence/diagnostics/` with their actual status. They are
not counted as passing targets. Upstream source, attribution and licenses remain
unchanged as documented in `README.md` and vendor manifests.
