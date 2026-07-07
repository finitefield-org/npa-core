# Contributing

NPA is certificate-first. Contributions are welcome, but proof acceptance must
remain based on canonical proof certificates and source-free checker verdicts,
not on convenience layers or repository metadata.

## Trust Boundary

NPA keeps a small trusted base:

```text
trusted:
  canonical .npcert bytes
  Rust kernel / verifier verdict
  source-free reference checker verdict
  deterministic export_hash, certificate_hash, and axiom_report_hash

not trusted:
  parser / elaborator / tactic / automation / AI / plugin / theorem search
  source files / replay files / theorem indexes / publish plans / refactor plans
  command status
  release pages / registry metadata
```

Do not make parser output, elaborator output, tactic traces, AI traces, theorem
search results, command status, release metadata, or registry metadata part of
proof acceptance.

## Local Gates

For ordinary development, run the fast gate first:

```sh
./scripts/check-fast.sh
```

This is the default hot-path check for core changes.

For package, verifier, or checked-fixture changes, add focused tests for the
touched subsystem and run the relevant local package checks against compact
fixtures in `testdata/`:

```sh
cargo run -q -p npa-cli -- package check-generated --root testdata/package/proofs --json
cargo run -q -p npa-cli -- package check-hashes --root testdata/package/proofs --json
```

Broaden the local test set when a change affects one of these areas:

- package metadata, package lock, or artifact generation
- `testdata/package/proofs/npa-package.toml`,
  `testdata/package/proofs/generated/package-lock.json`, axiom-report,
  theorem-index, publish-plan, or other package generated artifacts
- canonical certificate encode, decode, hash, import, or axiom report behavior
- kernel core semantics, typecheck, reduction, universe, or inductive behavior
- independent checker, package verifier, package lock, or artifact validation
- `.npcert` generation or verification compatibility
- public package fixture release behavior or high-trust evidence

For those changes, choose focused `cargo test` targets plus local package
commands that match the changed behavior. Typical package checks are:

```sh
cargo test -p npa-cli --test package_check_hashes
cargo test -p npa-cli --test package_cli package_cli_full_corpus_examples_pass_on_proof_corpus
cargo test -p npa-api package_fast_verifier_verifies_proof_package_source_free
```

`npa-core` local development must not require another NPA repository checkout.
The compact fixtures under `testdata/` are regression inputs, not a full
theorem authoring corpus.

## Certificate Compatibility

Changes around `.npcert` bytes, canonical encoding, declaration hashes, import
hashes, axiom reports, package locks, or source-free verification have a larger
blast radius. Include focused tests for deterministic hashes and for both
accepted and rejected cases.

Kernel-adjacent changes should include tests for:

- well-typed terms that pass
- ill-typed terms that are rejected
- definitional equality positive and negative cases
- universe constraint positive and negative cases
- deterministic certificate hash and import hash behavior
- axiom reports that do not grow unexpectedly

## Unsafe Rust

Do not use `unsafe` Rust by default. If `unsafe` is necessary, document why it
is necessary, what boundary contains it, and what safe alternatives were
rejected. Keep trusted-kernel changes small and directly testable.

## Working Tree Etiquette

Do not revert unrelated changes. If you see local modifications that are not
part of your task, treat them as user or teammate work and leave them alone.
If those changes affect your task, work with them rather than discarding them.

Keep changes scoped to the task. If a change crosses a phase boundary or
widens the trusted base, update the relevant design document and explain the
trust-boundary impact.

## Package Authoring

External theorem package checks use the installed `npa` binary with an explicit
package root:

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

For advisory cleanup planning, package authors may run:

```sh
npa package refactor-plan --root . --scope modules --top 20 --json
npa package refactor-plan --root . --scope theorems --module Proofs.Ai.Basic --json
```

This command is source-free by default and reads package metadata only. It does
not read source, replay, meta, tactic trace, AI trace, checker-result, registry,
or network data. Treat its scores and recommendations as planning diagnostics,
not as proof evidence or a package acceptance gate.

These commands produce deterministic diagnostics and release metadata. They do
not make source files, theorem indexes, publish plans, refactor plans, command
status, or release pages trusted proof evidence.
