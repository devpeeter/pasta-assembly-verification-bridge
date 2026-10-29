# Automated technical acceptance

Acceptance is determined by the recorded automated checks, exact theorem
contracts and disclosed trust boundary. The current snapshot-corrected revision
passed a fresh isolated local Windows full run on 2026-10-29 with actual exit 0:
all six runner stages and all 67 verification stages passed, including both
target gates and exact-type/standard-axiom audits. All 108 Python tests and all
five unit-CI stages also passed. The recorded verification time was 1,640.6108 s;
maximum individual direct Lean child peak memory was 1,824,825,344 bytes.

Corrected-revision GitHub Actions unit and full runs remain **NOT RUN**;
repository permission reports `push: false`. The preceding hosted run stopped
at the source-byte gate before proof compilation. Current local reports and
all dated historical attempts are distinguished in [RESULTS.md](RESULTS.md)
and retained in [evidence/git-blob-ci-fix/](evidence/git-blob-ci-fix/).

## Automated CI acceptance criteria

The push/pull-request job requires every Python test to run successfully,
source/lock and retained-artifact integrity, generated-file freshness and an
exact complete source manifest. The manual/published-release job additionally
bootstraps pinned tools in an isolated runtime, records fresh binary/extraction
provenance against the submitted target baseline, then runs:

```console
python scripts/verify.py --clean
```

An automated full PASS requires actual exit 0 and fresh complete `PASS` reports,
all required stages and both target gates, measured proof checks, exact theorem
type and standard-axiom audits, successful Kraken model execution vectors and
semantic mutants, and the exact intended formal-negative rejections. Missing
tools, omitted proofs, stale or `PARTIAL` reports, failed stages, changed checked
inputs or unrelated errors in place of semantic negatives fail the job.

Upload [.github/workflows/](.github/workflows/) at the GitHub repository root,
then commit/push and run **Full verification** from the Actions page. Publishing
a release triggers it too. Download the run artifacts and retain the runner
image version, original/fresh extraction comparison, source seals, actual exit,
logs, theorem audits and measurements. The original
historical evidence is preserved in the checkout; fresh results live in a
separate runtime/output tree. Detailed upload/artifact instructions are in
[.github/README.md](.github/README.md).

## Reproduction

Use a fresh checkout or unpack the source archive while preserving its
`outputs/pasta-assembly-verification-bridge/` layout. Record the archive digest
and the source manifest. Follow the pinned tool/dependency bootstrap procedure
in [README.md](README.md), then run from the project directory:

```console
python scripts/verify.py --clean
```

An explicit `--lean-bin` may be absolute or relative to the invocation directory.
It is resolved before subprocess working directories change. Bootstrap,
extraction, compatibility builds and verification share the fixed surrounding
workspace `work/` directory; bootstrap does not accept `--work`.

Record the host OS/architecture, caller directory, exact command, actual exit
code, immutable source/tool versions, executable/archive hashes, dependency
provenance, complete logs, proof time and direct-child peak memory. Retain the
run's `evidence/verification.json` and both target gates, exact-type audits,
axiom censuses, extraction and generation checks, model execution vectors,
formal-negative reports and source hashes. Missing stages or unrelated failures
in place of intended semantic rejections are not successful reproduction.

The bootstrap procedure may intentionally regenerate extraction provenance
for a different locally built Charon binary. Review and retain that difference:
the pinned source/tool revisions, complete templates, structured operands and
their raw-artifact links must agree. Do not edit instruction lists, add
assumptions, change pins or weaken negative checks to make a run pass. Imported
dependency caches remain part of the disclosed trust boundary.

## Exact source-byte boundary

The retained 112 Kraken and 16 Pasta source files are exact pinned Git blobs.
Their manifests contain both raw SHA-256 values and Git blob IDs. The earlier
snapshots differed only by CRLF versus LF; rebuilding from binary Git objects
corrected their byte identities without changing normalized source contents.
The three regenerated LF compatibility patches retain the same normalized edits
and have new exact byte hashes in `pins.json`; source/tool revisions are unchanged.

After obtaining the pinned checkouts, run:

```console
python scripts/snapshot_sources.py --check
```

An explicit `python scripts/snapshot_sources.py --write` reconstructs the
manifest-selected files from the immutable Git objects. It does not approve
edited files or normalize input during verification. Intentional source or
metadata updates also require `python scripts/source_manifest.py --write`,
followed by the ordinary integrity and full checks.

New source clones persist `core.autocrlf=false` and `core.eol=lf` before checkout;
proof dependencies set the same local policy on initialization. Existing
worktrees are not silently converted. Exact-byte checks, all proof obligations
and every rejection requirement remain in force.

The successful fresh isolated run used a short Windows output root. An earlier
attempt failed in the Charon native link at a 264-character private sysroot
library path before invoking verification. With the corresponding path shortened
to 203 characters, the unchanged full runner and pins completed successfully.
Use a short absolute directory outside the project for `ci_full.py --output`.
Both attempts, fresh checkout byte comparisons and input seals are retained
under [evidence/git-blob-ci-fix/](evidence/git-blob-ci-fix/).

## Proof obligations and automated audits

The delivered Lean sources and actual audit output establish the following
requirements for the assembly-block targets:

- `PastaBridge.AdditionCorrectness.addition_correct` and
  `PastaBridge.MulCorrectness.multiplication_correct`, guarded by `Audit.lean`
  and `MulAudit.lean`, for both `pallasBase` and `vestaBase`.
- Exact input bounds, modulus/inverse register mappings and output mappings:
  addition's reduced inputs and multiplication's exact upstream `mulContract`.
- All admissible bindings in the fixed 30-register pool, written-operand
  separation, and legal sharing by equal-valued read-only inputs. X19 may be
  allocated; it is preserved when outside the written allocation. X29 is reserved.
- Arbitrary incoming flags and scratch contents; complete memory/SP frames and
  preservation of every register outside the written allocation.
- Proved correspondence between the checked Kraken program and the existing
  arithmetic model, without an extra correspondence premise, plus the retained template/operand/byte
  certificates and their external link to the complete Charon extraction.
- Axiom censuses containing only `propext`, `Classical.choice`, `Quot.sound`;
  no `sorryAx`, new correctness axiom or unchecked correctness premise.
- Carry and operand-binding counterexamples, intended false-equality rejections,
  unsupported-feature rejection and stale-artifact checks.

Expanded statements are in
[ADDITION_CORRECTNESS_THEOREM.md](proofs/ADDITION_CORRECTNESS_THEOREM.md) and
[MUL_CORRECTNESS_THEOREM.md](proofs/MUL_CORRECTNESS_THEOREM.md).

## Boundary that must remain in the acceptance report

The proofs start at assembly entry with operands already in allocated registers.
The compact checked representation omits MIR operand-value expressions and
destination places. Full LLBC retains them for provenance, but the proofs do not
establish that the Rust wrapper loads the intended argument limbs or stores
results into the correct Rust locations. The MIR prefix/suffix evaluator used
by tests does not discharge this missing wrapper proof.

**Kraken model execution vectors** execute the Kraken model through Lean on
the host. They do not execute the original assembly on ARM hardware. Further
runs of these model checks remain model execution.

These limitations and the extraction, file-inclusion, library-cache and
semantic-model trust boundaries remain part of every reported result.
Automated success requires the complete checks above, with actual reports,
logs, exact-type and axiom audits, negative checks and unchanged checked inputs.
