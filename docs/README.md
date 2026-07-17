# NPA User Documentation

These docs are for people who use NPA to check, author, or publish theorem
packages. Compact package examples used by `npa-core` tests live under
`../testdata/package`.

NPA is certificate-first. Documentation, source files, theorem indexes,
theorem-premise reports, publish plans, refactor plans, command results,
registry metadata, tactic traces, replay files, and AI traces are not proof
evidence. Proof acceptance is based on canonical `.npcert` bytes, the Rust
kernel / verifier verdict, source-free checker verdicts, deterministic
certificate and import hashes, and axiom reports.

## Start Here

- [Repository README](../README.md): overview, trust boundary, build steps,
  package verification quick start, and repository layout.
- [Contributing](../CONTRIBUTING.md): local gates, checked-fixture triggers,
  certificate compatibility policy, and contribution workflow.
- [Toolchain Reference v0.7.0](npa-toolchain-reference-v0.7.0.md): current Rust
  CLI/API compatibility reference, theorem-premise reporting, generated checks,
  and read-only package artifact ledger audit.
- [Toolchain Reference v0.6.0](npa-toolchain-reference-v0.6.0.md): historical
  `npa-cli 0.6.x` compatibility reference.
- [Toolchain Reference v0.5.0](npa-toolchain-reference-v0.5.0.md): historical
  `npa-cli 0.5.x` compatibility reference.
- [Toolchain Reference v0.2.0](npa-toolchain-reference-v0.2.0.md): published
  tagged toolchain reference retained unchanged for external theorem packages
  pinned to the v0.2.0 release.

## Core References

- [Core Implementation Specification v0.2.0](core-spec-v0.2.0.md): current
  certificate-format, checker, and universe-constraint behavior.
- [Inductive Constructor Universe Bounds Design](inductive-constructor-universe-bounds-design.md):
  implemented security rule for constructor-field universe bounds across the
  Rust kernel, certificate paths, reference checker, and OCaml checker.
- [OCaml Clean-Room External Checker Specification](npa-checker-ext-ocaml.md):
  `npa-checker-ext` trust boundary and runner contract.
- [OCaml External Checker Core v0.2.0 Compatibility Audit And Task List](npa-checker-ext-core-v0.2.0-compatibility-todo.md):
  closed audit, completed compatibility tasks, and conformance/release-gate
  evidence for the OCaml checker.
- [Toolchain v0.7 External Checker Compatibility Gate](../checkers/npa-checker-ext/README.md):
  real `npa-cli 0.7.x` facade/direct closure for `npa-checker-ext 0.2.0`, plus
  the full and `--functional-only` Linux commands.
- [Public Package And Registry Roadmap](public-package-roadmap.md): public
  package boundaries, registry readiness, and non-goals.
- [Package Refactor Plan Command Design](refactor-plan-command-design.md):
  design record for the implemented read-only CLI command that ranks module and
  theorem-family refactor candidates from package metadata.
- [Package Artifact Refresh Command Design](package-artifact-refresh-command-design.md):
  initial design and implementation record for the package artifact refresh
  mode. The current v0.7 workflow additionally refreshes declared metadata and
  supports dependency-safe targeted selection as documented above.

## Verify A Package

Use these commands from an external theorem package root after installing or
pinning the `npa` toolchain described in the current toolchain reference.

```sh
npa package check --root .
npa package build-certs --root . --check
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off
npa package check-hashes --root .
npa package axiom-report --root . --check
npa package index --root . --check
npa package theorem-premise-report --root . --check
npa package publish-plan --root . --check
npa package audit-artifact-ledger --root . --json
```

Explicit export destinations are package-root-relative. Pair `--root` with an
`--out` that names only the path below that root:

```sh
npa package export-candidate-metadata --root proofs \
  --module Proofs.Example --declaration theorem_name \
  --out generated/theorem_name.metadata.json --json
npa package export-summary --root proofs \
  --out generated/custom-export-summary.json --json
```

These commands write below `proofs/generated/`. Do not repeat `proofs` or pass
a repository- or workspace-relative orchestration path in `--out`; the CLI
rejects such values before reading or writing the selected output.

Base package verification is source-free and reference-checker-only. Optional
high-trust external checker workflows are separate and must not be treated as
additional trusted proof input unless their checker identity and policy are
explicitly pinned.

Pinned external checked verification, generated-artifact manifest v0.2
evidence, and `verified_high_trust` are distinct results. The external path
requires `--package-lock checked`, one job, and cache/memo off; it never uses
the reconstructed authoring mode.

The core default is checked NPA package-lock input, which is the release/audit
parity mode. When normal authoring intentionally omits
`generated/package-lock.json`, use the current v0.7 source CLI with explicit
reconstructed mode:

```sh
cargo run --locked --offline -p npa-cli -- package verify-certs \
  --root ../PACKAGE/proofs --package-lock reconstructed --checker reference \
  --audit-cache off --verifier-memo off --json
```

Reconstructed mode reports its canonical lock hash and writes no package-root
file. It is authoring evidence, not a substitute for the exact checked lock in
a release or published-bundle audit. See the v0.7.0 toolchain reference for the
separate Cargo-lock, NPA-package-lock, provenance, and remediation contracts.
Run `audit-artifact-ledger` before repair when you need a once-read comparison
of manifest, metadata, certificate, source, and live-checker identities.

For advisory refactor planning, see the `npa package refactor-plan` section in
the current toolchain reference. It is source-free by default and emits planning
diagnostics only; refactor scores and recommendations are not proof evidence.

## Examples

These fixtures remain useful as public package examples:

- `../testdata/package/npa-std`: local standard-library package materialization.
- `../testdata/package/npa-mathlib`: public `Mathlib.*` theorem-library package
  example.
- `../testdata/package/npa-mathlib-downstream`: downstream certificate-vendoring
  example without a registry server.

The proof snapshot and seed fixtures remain repository test material unless a
specific README links them as examples. These examples are checked into
`npa-core`; using them does not require another NPA repository checkout.

## License

NPA is licensed under the [Apache License 2.0](../LICENSE). See
[NOTICE](../NOTICE) for attribution.
