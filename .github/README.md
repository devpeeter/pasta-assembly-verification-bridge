# GitHub Actions

Upload the contents of this project directory to the repository root, including
`.github/`, `.gitattributes`, `.gitignore`, `SOURCE-MANIFEST.json`, retained
artifacts and vendor sources. Do not upload only the ZIP, or place the workflows
under a nested `outputs/` directory in the repository. Start with an empty
repository to avoid unlisted auto-generated files.

Commit and push the files. The **Unit and integrity checks** workflow runs on
pushes and pull requests. Put both workflows on the default branch, then choose
**Actions → Full verification → Run workflow** for a manual run. Publishing a
GitHub release also starts full verification for that release. Nothing in these
workflows publishes a release or uploads source to another service.

The workflow checkout step recreates the documented
`outputs/pasta-assembly-verification-bridge/` filesystem layout inside the runner.
The source archive's outer directory layout and the GitHub repository layout
therefore differ intentionally. Byte conversion is disabled before checkout;
`.gitattributes` preserves the recorded file bytes.

Both retained upstream snapshots contain exact binary Git-blob bytes, with
SHA-256 and Git blob IDs in `UPSTREAM.json`. New bootstrap source clones persist
`core.autocrlf=false` and `core.eol=lf` before checkout; proof-dependency
repositories set those local settings on initialization. Verification compares
exact bytes and does not normalize CRLF/LF differences to make a check pass.

## Unit and integrity checks

The Windows job uses Python 3.11.9 and runs:

```console
python scripts/ci_unit.py --output <new-directory-outside-the-project>
```

This runs every Python test with no omissions, checks both upstream snapshots,
immutable lock/source identities and retained LLBC hash/pointer links, checks
generated files and the multiplication JSON-certificate candidate for freshness,
and checks the complete source manifest. This does not rebuild Charon, perform
a fresh extraction, or recheck the Lean target theorems.

The report and five stage logs are uploaded as
`unit-integrity-<run-id>-<attempt>` even if a check fails. Missing artifacts are
an upload error. A nonzero test/tool exit, any omitted test, stale generated file
or integrity mismatch fails the job.

## Full verification

The manual/release job first runs the same unit/integrity command, then:

```console
python scripts/ci_full.py --output <new-directory-outside-the-project>
```

On Windows, choose a short absolute output path. The first local attempt failed
at an MSVC Rust sysroot library path of 264 characters, before verification ran.
The unchanged runner and pins passed with a fresh short output root that reduced
the corresponding path to 203 characters. Both attempts are documented in
[RESULTS.md](../RESULTS.md).

The full runner copies source into an isolated runtime workspace, omitting
historical evidence, logs and build caches. It retains baseline artifacts and
source hashes alongside the new run. Private Cargo/Rustup homes avoid inheriting
unreviewed runner Cargo configuration. It bootstraps the pinned Charon/Rust,
Lean and locked proof dependencies using the existing scripts.

A new Charon build has a new binary identity. The runner intentionally runs
`scripts/extract.py` and the adapter's generation command in that isolated copy,
as the documented provenance procedure requires. It records the original/fresh
raw hashes and provenance differences. Immutable source/tool pins, complete
target templates/operands/options, compact checked projections and assembly
bytes must agree with the submitted baseline. A mismatch stops the job.

It then executes this exact command from the runtime project:

```console
python scripts/verify.py --clean
```

The job succeeds only with actual exit code 0, a fresh `PASS` verification
report, all required stages and both target gates complete, exact-type/axiom
audits, measured proof checks, both model-vector reports and their mutants,
and both formal-negative reports. Missing tools, stale/missing reports, omitted
proofs, `PARTIAL`/failed stages, new correctness axioms, `sorryAx` or unrelated
failures in place of the intended false-equality rejections fail the job.
The source/artifact seal must stay unchanged during verification, and the
original checkout must remain unchanged throughout.

The artifact `full-verification-<run-id>-<attempt>` retains the unit report,
runner context, all command logs, baseline extraction artifacts, provenance
comparison, input seals, fresh extraction/generation artifacts, fresh theorem
audits, all verification reports and measurements. Upload runs on success or
failure, including partially completed runs. Download it from the workflow run's
**Artifacts** section. Compiled tools, dependency `.lake` caches and compiled
products are excluded to keep the upload bounded. GitHub also retains setup and
action infrastructure output in the workflow's job log. Retention is 30 days,
subject to repository policy.

All third-party actions use full commit SHA references listed in
`actions.lock.json`. The `windows-2025` hosted image is not immutable; each run
records its image version and environment. Pinned downloads, source selection,
file inclusion, Lean/Mathlib caches and Kraken semantics remain disclosed trust
boundaries. The preceding hosted full attempt passed tool bootstrap and
extraction, then stopped at a snapshot byte mismatch before proof compilation.
The current correction rebuilds all 128 selected source files from pinned Git
objects and regenerates the three LF patches with unchanged normalized edits.
The corrected isolated full runner passed locally on Windows on 2026-10-29,
including all 67 verification stages. That establishes a local current run;
proof-stage resource viability on the hosted image is still unmeasured.

## Editing and acceptance

After intentional source or documentation changes, refresh the source
manifest and commit it with the changes:

```console
python scripts/source_manifest.py --write
python scripts/source_manifest.py
```

Refreshing hashes is packaging maintenance. The integrity and full verification
checks determine automated technical acceptance. Ordinary CI never refreshes
a stale submitted manifest silently.

With the pinned source checkouts present, the snapshot check verifies the selected
upstream bytes and blob metadata:

```console
python scripts/snapshot_sources.py --check
```

An intentional `python scripts/snapshot_sources.py --write`
reconstructs those selected snapshots from the immutable Git objects;
it is not a general newline-normalization or edited-source acceptance command.
Any resulting packaging changes require the manifest refresh above, and stale
compatibility patches or changed verification inputs still fail.

Current execution results and dates are in [RESULTS.md](../RESULTS.md). A green
full job means complete automated technical verification of the assembly blocks
from their register-entry state. Rust wrapper operand loads/result stores are
unproved. Kraken model execution vectors run through Lean on the host, not ARM
hardware. Acceptance follows the automated technical criteria in
[ACCEPTANCE.md](../ACCEPTANCE.md). The current local Windows full run passed on
2026-10-29 with actual exit 0, six runner stages and 67 verification stages;
the separate 108-test suite and all five unit-CI stages also passed. Corrected
hosted workflows remain **NOT RUN**, and connected repository access reports
`push: false`. No hosted success or corrected remote push is claimed. Actual
reports, measurements and preceding failures are linked from
[RESULTS.md](../RESULTS.md).

GitHub's primary documentation describes
[manual/release triggers](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows)
and the [artifact upload action](https://github.com/actions/upload-artifact).
Action source identities are recorded in `actions.lock.json`; hosted image
contents are documented by [runner-images](https://github.com/actions/runner-images/blob/main/images/windows/Windows2025-Readme.md).
