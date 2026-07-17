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

The published SRA-02-compatible toolchain reference for external theorem
package repositories remains:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

The earlier `v0.1.0` tag is historical and should not be used as the current
external package toolchain pin.

The current adjacent-source compatibility target is `npa-cli 0.7.0` with
`package_api::v1`. This is a Rust crate/API boundary; it does not change the
published v0.2.0 certificate format or core specification. Current package
command results use `npa.package.command_result.v0.3`. See the v0.7.0 toolchain
reference before consuming the programmatic package API, theorem-premise
report, or artifact ledger audit.

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
npa 0.7.0
```

## Package Verification Quick Start

The commands in this section describe the current v0.7 source CLI. External
theorem libraries still pinned to the published v0.2.0 tag should use the
historical v0.2.0 reference. The `npa package ...` command family uses an
explicit package root:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
npa package check-hashes --root . --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
npa package audit-artifact-ledger --root . --json
```

For local certificate-only edits, use the source-free changed-certificate path:

```sh
npa package verify-certs --root . --changed --package-lock checked \
  --checker reference --audit-cache off --verifier-memo off --json
```

`--changed` selects package modules whose checked-in `certificate.npcert` files
are changed in Git, plus certificate imports needed by the verifier. It does not
run `build-certs` or read source/replay/meta artifacts.

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

After a successful refresh, run the non-mutating ledger audit:

```sh
npa package audit-artifact-ledger --root . --json
```

Continue only when it reports consistent hash parity for the manifest,
metadata, raw files, and reference checker. Metadata refresh and ledger parity
are maintenance results, not proof evidence.

Checked mode is the core default and is required for release or audit parity.
For source-free authoring when `generated/package-lock.json` is intentionally
absent, the current v0.7 source CLI also supports explicit in-memory
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
`npa-cli 0.7.x` / `package_api::v1` hosts `npa-checker-ext 0.2.0` over
`NPA-CERT-0.2.0` and `NPA-Core-0.2.0`. It requires a checked lock and disables
all local acceleration explicitly. From an aggregate root containing
`npa-core/` and the target `proofs/` package:

```sh
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
  package verify-certs --root proofs --package-lock checked \
  --checker external --audit-cache off --verifier-memo off --jobs 1 \
  --runner-policy ci/runner.release.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json --json
```

The `ci/...` locators are relative to `proofs`; Cargo's `--locked --offline`
flags apply only to the development invocation. External checked evidence,
generated-artifact v0.2 release evidence, and `verified_high_trust` remain
three distinct outcomes.

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

- [Toolchain Reference v0.7.0](docs/npa-toolchain-reference-v0.7.0.md):
  current adjacent-source Rust API, theorem-premise reporting, generated checks,
  package-lock modes, and ledger audit.
- [Toolchain Reference v0.6.0](docs/npa-toolchain-reference-v0.6.0.md):
  historical `npa-cli 0.6.x` compatibility reference.
- [Toolchain Reference v0.5.0](docs/npa-toolchain-reference-v0.5.0.md):
  historical `npa-cli 0.5.x` compatibility reference.
- [OCaml External Checker](docs/npa-checker-ext-ocaml.md): clean-room checker
  contract and current `npa-cli 0.7.x` adapter boundary.
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
checkers/npa-checker-ext/scripts/toolchain-v0.7.sh
```

Use `--functional-only` for a dirty developer checkout; its success message
explicitly states that release evidence was not evaluated.

## License

NPA is licensed under the [Apache License 2.0](LICENSE).

Copyright 2026 [Finite Field K.K.](https://finitefield.org/en/). See [NOTICE](NOTICE).
