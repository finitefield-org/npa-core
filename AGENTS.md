# AGENTS.md

Working guidelines for agents operating in this repository.

## Repository-wide Guidelines

- Use `/usr/bin/git` for git commands.
- Do not use Git LFS in this repository.
- Do not add `.gitattributes` rules that set `filter=lfs`, `diff=lfs`, or
  `merge=lfs`.
- When importing or updating subtree content, ensure LFS pointer files are not
  introduced into this repository history.
- Record any suggestions in `suggestions.md`.
- When adding proofs, make maximum effort to choose module and theorem names
  that accurately communicate their mathematical meaning and corpus role.
- When module or theorem refactoring is needed to preserve meaningful naming,
  semantic placement, or maintainable proof organization, perform it without
  hesitation rather than leaving proofs in ill-fitting modules or names.

## Project Purpose

NPA is a certificate-first dependently typed proof assistant. It is designed
around the canonical proof certificate that is ultimately checked, not around
convenient higher-level features.

The most important trust boundary is:

```text
Not trusted:
  parser / elaborator / tactic / automation / AI / plugin / theorem search

Trusted:
  small Rust kernel
  canonical certificate
  independent checker
```

## Implementation Policy

- Implement the kernel in Rust.
- Keep the kernel small; do not put I/O, networking, plugin loading, or AI calls
  in it.
- Tactics and elaborators only generate proof terms / certificates; do not treat
  them as the basis of correctness.
- Limit the representation read by the certificate checker to the canonical core
  AST.
- Do not put surface syntax, notation, implicit arguments, typeclass search, or
  holes into the core calculus.
- Make hashes, serialization, and error reporting deterministic.
- As a rule, do not use `unsafe` Rust. If it is necessary, document the reason
  and boundary.

## Documents To Read Before Work

Before making large implementation changes, review the current specification
and the documents for the relevant subsystem.

- Repository overview, trust boundary, and local gates: `README.md`.
- Package-author and toolchain references: `docs/README.md` and
  `docs/npa-toolchain-reference-v0.2.0.md`.
- Crate-local specification snapshot used by tests:
  `testdata/docs/npa-spec.md`.
- For implemented kernel / certificate / frontend / tactic / API / package
  behavior, inspect the relevant crate source and focused tests.

## Rust Kernel Design Rules

- Clearly separate type checking, definitional equality, reduction, universe
  constraints, and inductive checks.
- Treat ASTs as structured data, not string processing.
- Keep binding representations such as de Bruijn indexes / levels aligned with
  the specification and implementation.
- Make the responsibilities and termination of beta / delta / iota / zeta
  reduction explicit.
- Return errors not only as human-facing strings but also as testable structured
  enums.
- Make the kernel API directly callable from tests, and do not make it depend on
  a CLI or server.

## Test Policy

In normal development, use the fast core gate first. `npa-core` must remain
self-contained: its local tests and gates use in-repository code plus compact
snapshots under `testdata/`, not sibling NPA repository checkouts.

```sh
./scripts/check-fast.sh
```

Internally, this runs:

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace -- \
  --skip proof_corpus \
  --skip proof_package \
  --skip package_artifact_ \
  --skip package_artifact_extraction_ \
  --skip package_artifacts_checked_in_generated_ \
  --skip package_axiom_report_ \
  --skip package_axiom_report_projection_ \
  --skip package_build_certs_check_read_through_ \
  --skip package_build_certs_check_rejects_checked_in_certificate_byte_drift \
  --skip package_cache_aware_dag_verifier_ \
  --skip package_check_hashes_ \
  --skip package_cli_smoke_ \
  --skip package_cli_source_free_ \
  --skip package_cli_temp_fixture_rejects_stale_source_certificate_and_lock \
  --skip package_export_summary_ \
  --skip package_fast_verifier_ \
  --skip package_generated_check_command_ \
  --skip package_import_context_export_cache_ \
  --skip package_index_ \
  --skip package_lock_builder_ \
  --skip package_lock_import_identity_ \
  --skip package_projection_ \
  --skip package_publish_ \
  --skip package_reference_summary_cache_key_ \
  --skip package_reference_verifier_ \
  --skip package_shared_snapshot_ \
  --skip package_phase8_ \
  --skip package_source_free_ \
  --skip package_theorem_index_projection_ \
  --skip package_verified_result_cache_key_ \
  --skip package_verify_certs_ \
  --skip package_verify_external_ \
  --skip package_verifier_
```

If a local command reports `Killed` or exits with code `137`, treat it as an
external `SIGKILL` first: usually the Linux OOM killer, a container memory
limit, or a supervisor timeout / memory limit. Do not immediately rerun the same
heavy command unchanged. Check the exit code and, when available, OS/container
memory evidence, then retry with a narrower target or lower parallelism. For
Rust builds/tests, prefer package- or test-specific commands and use
`CARGO_BUILD_JOBS=1` when memory pressure is plausible. When subagents or
multiple Codex threads are involved, reduce concurrency before rerunning
expensive checks.

For package/verifier changes that touch checked fixture behavior, run focused
tests and local package checks against `testdata/package/proofs`. Keep full
theorem-corpus workflows out of this core repository's hot path.

Around the kernel, add at least the following cases.

- well-typed terms are accepted
- ill-typed terms are rejected
- positive and negative cases for definitional equality
- positive and negative cases for universe constraints
- certificate hashes / import hashes are deterministic
- axiom reports do not grow unintentionally

## Notes When Changing Files

- Do not revert unrelated design documents or user changes.
- For changes that cross subsystem responsibilities, also update the README,
  docs under `docs/`, or the crate-local specification snapshot in
  `testdata/docs/npa-spec.md` when those files describe the changed contract.
- If existing debug options are insufficient, add documentation that states
  which debug options are missing and why they are needed.
- For changes that expand the kernel trusted base, always document the reason,
  alternatives, and checking boundary.
- In the standard library, do not rely on `sorry`-equivalent behavior or
  unauthorized axioms.
- Do not add unresolved conjectures to standard-library theorem declarations.
  `npa-core` keeps only compact regression fixtures, not proof-corpus authoring
  policy.
