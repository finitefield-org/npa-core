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
  source files / replay files / theorem indexes / publish plans / CI status
  GitHub release pages / registry metadata

trusted:
  canonical .npcert bytes
  Rust kernel / verifier verdict
  source-free reference checker verdict
  deterministic export_hash, certificate_hash, and axiom_report_hash
```

NPA is not a production replacement for Lean or Rocq. It is a research and
implementation repository for a proof-certificate-centered toolchain.

## Current Status

The current SRA-02-compatible toolchain reference for external theorem package
repositories is:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

The earlier `v0.1.0` tag is historical and should not be used as the current
external package toolchain pin.

The split theorem package repositories are:

- `npa-std`: <https://github.com/finitefield-org/npa-std>
- `npa-mathlib`: <https://github.com/finitefield-org/npa-mathlib>
- `npa-corpus`: <https://github.com/finitefield-org/npa-corpus>
- `npa-project-iut`: <https://github.com/finitefield-org/npa-project-iut>

IUT theory modules and project documents have moved to `npa-project-iut`; this
repository now keeps the shared NPA core toolchain and package infrastructure.
The former in-tree proof corpus moved to `npa-corpus`:
<https://github.com/finitefield-org/npa-corpus>.

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

Expected output for the current toolchain ref:

```text
npa 0.2.0
```

## Package Verification Quick Start

External theorem libraries use the `npa package ...` command family with an
explicit package root:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package verify-certs --root . --checker reference --json
npa package check-hashes --root . --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
```

For release-ready packages that check in `generated/publish-plan.json`, also
run:

```sh
npa package publish-plan --root . --check --json
```

For local development against the package fixtures that remain in the sibling
`../npa` checkout, run the same commands through `cargo` or the built
`target/debug/npa` binary:

```sh
cargo run -p npa-cli -- package check --root ../npa/fixtures/npa-std --json
cargo run -p npa-cli -- package build-certs --root ../npa/fixtures/npa-std --check --json
cargo run -p npa-cli -- package verify-certs --root ../npa/fixtures/npa-std --checker reference --json
cargo run -p npa-cli -- package check-hashes --root ../npa/fixtures/npa-std --json
```

To work on the proof corpus package hashes and generated metadata, use the
sibling `../npa-corpus` repository. From `../npa-corpus`, package commands can
use this repository's CLI through `--manifest-path`:

```sh
cargo run -q --manifest-path ../npa-core/Cargo.toml -p npa-cli -- package check --root proofs --json
cargo run -q --manifest-path ../npa-core/Cargo.toml -p npa-cli -- package check-generated --root proofs --timings summary --json
```

Run metadata-regeneration commands without `--check` from `../npa-corpus` only
when intentionally refreshing checked-in corpus artifacts.

Package metadata, theorem indexes, publish plans, and CI output are deterministic
review and release metadata. They are not proof evidence. Downstream users must
still verify hash-pinned certificate bytes with a source-free checker.

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

The `develop/`, `fixtures/`, `ci-templates/`, and web-tool support directories
were not part of the listed-path migration and remain in the sibling `../npa`
checkout until they are migrated separately.

## Documentation

Start with the user documentation:

- [NPA User Documentation](docs/README.md)

Public package-author and toolchain references:

- [Toolchain Reference v0.2.0](docs/npa-toolchain-reference-v0.2.0.md)
- [External Theorem Library CI](docs/external-theorem-library-ci.md)

Developer-facing specs, release evidence, internal planning, and Japanese
development notes remain in `../npa/develop/`.

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

The proof corpus now lives in the sibling `../npa-corpus` repository. For
ordinary theorem authoring, run its lightweight authoring gate there:

```sh
(cd ../npa-corpus && ./scripts/check-corpus-authoring.sh)
```

Reserve the corpus package/full gates for package verifier changes, canonical
certificate/checker compatibility, `npa-mathlib` promotion readiness, release
handoff, or high-trust evidence, and run them from `../npa-corpus`:

```sh
(cd ../npa-corpus && ./scripts/check-corpus-package.sh)
(cd ../npa-corpus && ./scripts/check-corpus-full.sh)
```

For contribution policy and the full local-gate checklist, see
[CONTRIBUTING.md](CONTRIBUTING.md).

## License

NPA is licensed under the [Apache License 2.0](LICENSE).

Copyright 2026 [Finite Field K.K.](https://finitefield.org/en/). See [NOTICE](NOTICE).
