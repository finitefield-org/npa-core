# Nano Proof Auditor (NPA)

NPA is a certificate-first proof assistant and verification
toolchain for dependent proofs.

The project is designed around a small trusted base. Surface syntax,
elaboration, tactics, automation, theorem search, plugins, and AI systems may
help produce proof candidates, but they are not trusted proof evidence. The
object that matters is the canonical proof certificate checked by the Rust
kernel and source-free checkers.

```text
untrusted:
  parser / elaborator / tactic / automation / AI / plugin / theorem search
  source files / replay files / theorem indexes / publish plans / refactor plans
  command status
  release pages / registry metadata

trusted:
  canonical .npcert bytes
  Rust kernel / verifier verdict
  source-free reference checker verdict
  deterministic export_hash, certificate_hash, and axiom_report_hash
```

NPA is not a production replacement for Lean or Rocq. It is a research and
implementation repository for a proof-certificate-centered toolchain.

## Current Status

The current source tree emits `NPA-CERT-0.3.0` / `NPA-Core-0.3.0` from every
ordinary producer and ships `npa-checker-ref 0.4.0` and
`npa-checker-ext 0.3.0`. All three check paths also accept the exact historical
v0.2.0, v0.1.2, and v0.1 pairs without changing their bytes or immediate-opacity
semantics.

This source capability is newer than the last published external tag. The
published SRA-02-compatible toolchain pin for external theorem package
repositories remains:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

The earlier `v0.1.0` tag is historical and should not be used as the current
external package toolchain pin.

The current adjacent-source compatibility target is `npa-cli 0.8.0` with
`package_api::v1`; current package command results use
`npa.package.command_result.v0.4`. These host/API/result axes are independent
of both the current v0.3 certificate pair and the still-published v0.2.0 tag.
See the v0.8.0 toolchain reference before consuming the programmatic package
API, fuel diagnostics, performance measurements, theorem-premise report, or
artifact ledger audit. The v0.7.0 reference remains historical.

The public package repositories are:

- `npa-std`: <https://github.com/finitefield-org/npa-std>
- `npa-mathlib`: <https://github.com/finitefield-org/npa-mathlib>

This repository keeps the shared NPA core toolchain and package
infrastructure. Building, testing, and developing this repository must not
require a sibling checkout of any other NPA repository.

## Build From Source

Install the pinned Rust toolchain and build the CLI:

```sh
rustup toolchain install 1.95.0 --profile minimal
cargo +1.95.0 build -p npa-cli
```

The installed binary name is `npa`. From the repository build output:

```sh
target/debug/npa --version
```

Expected output when building the current source checkout:

```text
npa 0.8.0
```

## Package Verification Quick Start

The commands in this section describe the current v0.8 source CLI. External
theorem libraries still pinned to the published v0.2.0 tag should use the
historical v0.2.0 reference. The `npa package ...` command family uses an
explicit package root:

```sh
npa package check-source-structure --root . --json
npa package check --root . --json
npa package build-certs --root . --check --json
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
npa package check-hashes --root . --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
npa package audit-artifact-ledger --root . --json
```

Run `check-source-structure` after each direct Human Surface edit. With no
selector it checks every manifest module; repeated `--module` checks registered
modules, and repeated `--path` checks package-relative files without loading a
manifest. It uses the production lexer, ignores brackets inside comments and
strings, and reports both sides of a delimiter mismatch in structured JSON.
This read-only check is authoring feedback, not parsing or proof evidence.

For an advisory targeted authoring loop, `build-certs` has this closed
build-check cache mode set:

| `--build-check-cache` | Allowed build | Support behavior | Result boundary |
| --- | --- | --- | --- |
| `off` | every supported build shape | no cache-only work | ordinary live result |
| `read-through` | full or targeted `--check` | checks everything live; records diagnostics and may warm eligible entries | ordinary live result; cache metadata is not evidence |
| `local-hit` | targeted `--check --module ...` or `--check --changed` only | reuses exact eligible support contexts; checks misses live | local-only authoring feedback |

For example:

```sh
npa package build-certs --root . --check --module Proofs.Example \
  --build-check-cache read-through --json
npa package build-certs --root . --check --module Proofs.Example \
  --build-check-cache local-hit --json
```

`read-through` always performs every selected build and support check live.
`build-certs --build-check-cache local-hit` may avoid eligible support checks,
but every reached explicit target is still built fresh and the whole result is
`trusted=false`, `build_evidence=false`, and `proof_evidence=false`. Both
non-off modes may write only their automatically placed external local stores;
`build-certs --build-check-cache local-hit` publishes only eligible cache-free
live miss subtrees. They never write canonical package artifacts. Store failure
produces a bounded diagnostic and falls back to live work.

This option is distinct from `verify-certs --audit-cache local-hit`: the flags
belong to different commands and stores, and neither cache hit is proof
evidence. Canonical `.npcert` bytes become acceptable proof evidence only after
the ordinary cache-disabled source-free checker gates, including the reference
checker wherever package policy requires it. Keep completion and release
commands cache-off.

The Mathlib interface-proposal validator is a separate curation-only command:

```sh
npa package check-interface-proposals \
  --root testdata/package/interface-proposals-valid \
  --proposal-root proposals --json
```

It is deterministic, network-free, read-only, and emits
`npa.mathlib.interface_proposal_check.v1` with `proof_evidence: false`. It
reads only the selected package manifest and canonical `Mathlib/**/*.toml`
proposal files; it does not dereference evidence URLs, invoke Git or a proof
checker, read certificate/source sidecars, write files, admit catalog modules,
or turn curation status into proof evidence. Supplying
`--previous-proposal-root` enables only the locally detectable continuity
checks for the caller-selected immediately preceding snapshot.

For local certificate-only edits, use the source-free changed-certificate path:

```sh
npa package verify-certs --root . --changed --package-lock checked \
  --checker reference --audit-cache off --verifier-memo off --json
```

`--changed` selects package modules whose checked-in `certificate.npcert` files
are changed in Git, plus certificate imports needed by the verifier. It does not
run `build-certs` or read source/replay/meta artifacts.

For an explicit source-free subset, repeat `--module` with local logical module
names. The verifier checks those seeds plus their exact transitive import
closure in canonical order:

```sh
npa package verify-certs --root . \
  --module Proofs.Example --module Proofs.Support \
  --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
```

For a clean committed branch, `--base REF` resolves `REF`, `HEAD`, and their
unique merge base, rejects any staged, unstaged, deleted, or untracked protected
package input (including inputs hidden by `assume-unchanged`, `skip-worktree`,
incorrect fsmonitor hook output, weakened stat-cache settings, or a tracked
gitlink/symlink ancestor). It also rejects a protected leaf whose index entry
is not a stage-zero ordinary blob, including a symlink entry exposed as a
regular file by `core.symlinks=false`. Index-to-`HEAD` and worktree-to-index
diffs are checked separately so staged changes cannot be canceled by the final
worktree snapshot, and raw `git hash-object --no-filters` identities prevent
clean filters or end-of-line normalization from hiding different protected
bytes. Protected queries also force executable-bit checking, so
`core.fileMode=false` cannot hide a worktree mode change. The selector then
uses no-follow metadata checks to reject exact protected files hidden inside
an untracked embedded repository without reading their bodies. It then selects
only structurally
attributable committed module changes. Selector Git children discard every
inherited `GIT_*` variable
so the caller cannot redirect their repository, index, configuration injection,
or exact pathspec protocol. Exact candidate queries pair each top-literal path
with an atomic descendant exclusion and isolate path depths, so Git cannot
reinterpret a directory-valued candidate as a recursive package-prefix query.
Every selector child also disables replace-object
substitution; base-mode children additionally disable lazy object fetching, so
unavailable history fails locally and object IDs continue to name their
original bytes. Package-wide, deleted, renamed, or otherwise uncertain
changes escalate to the ordinary full verifier; an empty committed range fails
rather than reporting proof success:

```sh
npa package verify-certs --root . --base origin/main \
  --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
```

`--changed`, `--module`, and `--base` are mutually exclusive. Partial selectors
reject the external checker and non-off audit-cache or verifier-memo modes;
`--base` additionally requires the checked package lock. Its bounded
`npa.package.verify-selection.v0.1` summary is untrusted selection metadata,
not a complete PR gate: run the package's canonical build, hash, lock, axiom,
and policy gates at the same committed head/base boundary.

For release-ready packages that check in `generated/publish-plan.json`, also
run:

```sh
npa package publish-plan --root . --check --json
```

When intentionally refreshing local package artifacts after source changes,
use the supported local hash-pin refresh path:

```sh
npa package build-certs --root . --update-manifest-hashes --check --json
npa package build-certs --root . --update-manifest-hashes --json
npa package check-hashes --root . --json
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
```

The `--check` form is a no-write dry run. Write mode atomically updates local
certificate files, local module hash pins in `npa-package.toml`, declared
module `meta.json` ledgers, and `generated/package-lock.json`. It does not
update external import pins, and it is artifact maintenance rather than proof
evidence; source-free checker verification remains required.

Canonical refresh performs a context-free lexer and delimiter preflight before
reading certificates. Full refresh scans every local source first. Targeted
`--module` and `--changed` refresh scans the explicit selected seeds, then
processes only their dependency-closed priority prefix before reverse-only
dependents and unrelated package artifacts. A parenthesis, string, parser,
application-shape, resolver, elaborator, or kernel-handoff failure in selected
work therefore stops before the deferred package closure while successful runs
still verify and lock the complete package. Structured output reports
`package_build_refresh_schedule`; timing-enabled JSON additionally reports
`source_preflight_ms`, `priority_build_ms`, and `completion_build_ms` (full
refresh omits `priority_build_ms`). These diagnostics and timings are untrusted
authoring metadata, not proof evidence.

After a successful refresh, run the non-mutating ledger audit:

```sh
npa package audit-artifact-ledger --root . --json
```

Continue only when it reports consistent hash parity for the manifest,
metadata, raw files, and reference checker. Metadata refresh and ledger parity
are maintenance results, not proof evidence.

Checked mode is the core default and is required for release or audit parity.
For source-free authoring when `generated/package-lock.json` is intentionally
absent, the current v0.8 source CLI also supports explicit in-memory
reconstruction without package-root writes:

```sh
cargo run --locked --offline -p npa-cli -- package verify-certs \
  --root ../PACKAGE/proofs --package-lock reconstructed --checker reference \
  --audit-cache off --verifier-memo off --json
```

Both modes report a separate package-lock provenance diagnostic and canonical
hash. Reconstructed provenance is authoring evidence, not parity with a frozen
release lock.

The compatible clean-room external path keeps independent version axes:
`npa-cli 0.8.x` / `package_api::v1` hosts `npa-checker-ext 0.3.0`. The checker
advertises the current v0.3 capability pair while reporting each certificate's
actual v0.3, v0.2.0, v0.1.2, or v0.1 input pair separately. It requires a
checked lock and disables all local acceleration explicitly. From an aggregate
root containing
`npa-core/` and the target `proofs/` package:

```sh
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
  package verify-certs --root proofs --package-lock checked \
  --checker external --audit-cache off --verifier-memo off --jobs 1 \
  --runner-policy ci/runner.release.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json --json
```

This is the frozen invocation shape, not a currently enabled evidence path.
The host now fails it before creating checker-import or checker-result files
with `external_checker_supervisor_unavailable`. Re-enabling execution requires
a descendant-owning supervisor that enforces memory and timeout and an
authenticated checker step counter; reporting unavailable usage as zero is not
accepted evidence.

The `ci/...` locators are relative to `proofs`; Cargo's `--locked --offline`
flags apply only to the development invocation. External checked evidence,
generated-artifact v0.2 release evidence, and `verified_high_trust` remain
three distinct outcomes.

Fast and reference verification use the same explicit cache-disabled package
contract:

```sh
npa package verify-certs --root . --package-lock checked --checker fast \
  --audit-cache off --verifier-memo off --json
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
```

Fast per-module results and reference summaries report the decoded
`certificate_format` and `core_spec`. External raw-result v2 additionally
separates the checker capability fields `certificate_format` / `core_spec`
from `input_certificate_format` / `input_core_spec`; checked results also bind
`module`, `certificate_hash`, `export_hash`, and `axiom_report_hash`.

For advisory refactor planning from package metadata, use:

```sh
npa package refactor-plan --root . --scope modules --top 20 --json
npa package refactor-plan --root . --scope theorems --module Proofs.Ai.Basic --json
```

`refactor-plan` is source-free by default and emits planning diagnostics only.
It does not read source, replay, meta, tactic trace, AI trace, checker-result,
registry, or network data, and it is not proof evidence.

For local development against the compact package fixtures checked into this
repository, run the same commands through `cargo` or the built
`target/debug/npa` binary:

```sh
cargo run --locked --offline -p npa-cli -- package check --root testdata/package/npa-std --json
cargo run --locked --offline -p npa-cli -- package build-certs --root testdata/package/npa-std --check --json
cargo run --locked --offline -p npa-cli -- package verify-certs --root testdata/package/npa-std \
  --package-lock checked --checker reference --audit-cache off --verifier-memo off --json
cargo run --locked --offline -p npa-cli -- package check-hashes --root testdata/package/npa-std --json
```

For core package/verifier regression checks against the narrow proof-package
snapshot, use the local `testdata/package/proofs` fixture:

```sh
cargo run --locked --offline -q -p npa-cli -- package check --root testdata/package/proofs --json
cargo run --locked --offline -q -p npa-cli -- package check-generated --root testdata/package/proofs --timings summary --json
```

Run metadata-regeneration commands without `--check` only when intentionally
refreshing checked-in `npa-core/testdata` artifacts.

Package metadata, theorem indexes, theorem-premise reports, publish plans,
refactor plans, and command output are deterministic review and release
metadata. They are not proof evidence.
Downstream users must still verify hash-pinned certificate bytes with a
source-free checker.

Large theorem-premise reports use a bounded, hash-addressed chunk layout while
retaining their complete canonical logical report. Small reports keep their
existing bytes. See [bounded theorem-premise report storage](docs/npa-toolchain-reference-v0.8.0.md#bounded-theorem-premise-report-storage)
for the index/chunk format, resource bounds, and archive requirements.

## Repository Layout

```text
.
├── crates/
│   ├── npa-kernel/       trusted kernel core
│   ├── npa-cert/         canonical certificate encoding and checking handoff
│   ├── npa-checker-ref/  source-free reference checker
│   ├── npa-package/      package manifest, lock, artifact, and report tooling
│   ├── npa-cli/          installed `npa` command
│   ├── npa-frontend/     untrusted surface-language frontend
│   ├── npa-tactic/       untrusted tactic/proof-state layer
│   └── npa-api/          untrusted API and orchestration layer
├── checkers/
│   └── npa-checker-ext/  clean-room external checker prototype
├── docs/                user-facing documentation and package-author guides
└── scripts/             local verification gates
```

Compact, test-owned package and proof-agent snapshots needed by `npa-core` tests
live under `testdata/` so `cargo test -p npa-api` and `cargo test -p npa-cli`
do not need another NPA repository checkout. The `testdata/package/proofs`
snapshot is intentionally narrow and contains only the modules and generated
package metadata covered by core package/verifier tests.
Other historical support directories were not part of the listed-path
migration unless explicitly documented in a split repository.

## Documentation

Start with the user documentation:

- [NPA User Documentation](docs/README.md)

Package-author and toolchain references:

- [Toolchain Reference v0.8.0](docs/npa-toolchain-reference-v0.8.0.md):
  current adjacent-source Rust API, kernel fuel diagnostics, performance
  measurements, checker gates, and package operations.
- [Toolchain Reference v0.7.0](docs/npa-toolchain-reference-v0.7.0.md):
  historical `npa-cli 0.7.x` compatibility reference.
- [Toolchain Reference v0.6.0](docs/npa-toolchain-reference-v0.6.0.md):
  historical `npa-cli 0.6.x` compatibility reference.
- [Toolchain Reference v0.5.0](docs/npa-toolchain-reference-v0.5.0.md):
  historical `npa-cli 0.5.x` compatibility reference.
- [OCaml External Checker](docs/npa-checker-ext-ocaml.md): v0.3 clean-room
  checker contract, four-version input compatibility, and current
  `npa-cli 0.8.x` adapter boundary.
- [Toolchain Reference v0.2.0](docs/npa-toolchain-reference-v0.2.0.md):
  published historical external-toolchain contract.

Developer-facing package-author docs live under `docs/`. The crate-local
specification snapshot used by tests lives under `testdata/docs/npa-spec.md`.

The in-repo Phase 6 standard-library design documents the MVP release modules
`Std.Logic`, `Std.Nat`, `Std.List`, and `Std.Algebra.Basic`. The current SRA-02
external package fixture path is the split `npa-std` package.
Phase 6 release/build artifact profiles include `std.nat.mvp`, `std.list.mvp`,
and `std.all.mvp`; source layout fixtures remain authoring and debug context,
not trusted proof evidence.

## Opaque Definition Boundary

Human Surface and Machine Surface both accept `opaque def`; Machine terms still
use the fully explicit Machine grammar:

```text
opaque def Eval.cachedInvariant (x : Input) : Result := Eval.run x
```

The body is checked and remains locally transparent to later declarations in
the defining module. Its exported body is sealed, so importers can use only the
declared type and stable specification theorems. Put implementation-heavy
opaque definitions in semantic leaf modules and expose semantic laws, not a
whole-body equality theorem. No defining-module speedup is promised; the
benefit begins downstream after the sealed module is imported.

A rebuild under v0.3 changes certificate identity even for a plain module; it
is never a header-only migration from v0.2. Package manifest/lock profiles stay
on their independent v0.1 contract axes. `npa.package.build_check_cache.v0.2`,
`npa.package.audit_cache.v0.2`, and
`npa.package.verified_export_summary.v0.2` metadata record the exact decoded
certificate/core pair for each affected module. Targeted package refresh may
reuse an interface-stable consumer only after full-chain rebind and source-free
revalidation.

## Local Development Gates

For ordinary development, start with the fast gate:

```sh
./scripts/check-fast.sh
```

For package, verifier, or checked-fixture changes, add the focused cargo tests
for the touched subsystem and run the relevant local package checks:

```sh
cargo run --locked --offline -q -p npa-cli -- package check-generated --root testdata/package/proofs --json
cargo run --locked --offline -q -p npa-cli -- package check-hashes --root testdata/package/proofs --json
```

The compact fixtures in `testdata/` are regression data, not a full theorem
corpus. Do not make `npa-core` local gates depend on sibling NPA repository
checkouts.

For contribution policy and the full local-gate checklist, see
[CONTRIBUTING.md](CONTRIBUTING.md).

On Linux, the complete real-checker compatibility/release-evidence gate is:

```sh
checkers/npa-checker-ext/scripts/toolchain-v0.8.sh
```

On hosts with kernel-sealed immutable checker staging, use `--functional-only`
for a dirty developer checkout; its success message explicitly states that
release evidence was not evaluated. Unsupported hosts run the portable build
and host tests, then fail closed before policy preflight or external execution;
complete both functional closure and the full release gate on clean Linux.

## License

NPA is licensed under the [Apache License 2.0](LICENSE).

Copyright 2026 [Finite Field K.K.](https://finitefield.org/en/). See [NOTICE](NOTICE).
