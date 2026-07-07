# NPA User Documentation

These docs are for people who use NPA to check, author, or publish theorem
packages. Development notes, phase specifications, milestone evidence, and
historical support directories were not part of the listed-path migration
unless explicitly documented in a split repository. Compact package examples
used by `npa-core` tests live under `../testdata/package`.

NPA is certificate-first. Documentation, source files, theorem indexes, publish
plans, refactor plans, command results, registry metadata, tactic traces,
replay files, and AI traces are not proof evidence. Proof acceptance is based
on canonical `.npcert` bytes, the Rust kernel / verifier verdict, source-free
checker verdicts, deterministic certificate and import hashes, and axiom
reports.

## Start Here

- [Repository README](../README.md): overview, trust boundary, build steps,
  package verification quick start, and repository layout.
- [Contributing](../CONTRIBUTING.md): local gates, checked-fixture triggers,
  certificate compatibility policy, and contribution workflow.
- [Toolchain Reference v0.2.0](npa-toolchain-reference-v0.2.0.md): current
  `npa` toolchain reference for external theorem packages.

## Core References

- [Core Implementation Specification v0.2.0](core-spec-v0.2.0.md): current
  certificate-format, checker, and universe-constraint behavior.
- [Universe Constraints v0.1.2 Compatibility Record](universe-constraints-v0.1.2-compatibility-record.md):
  compatibility notes for the universe-constraint alignment.
- [OCaml Clean-Room External Checker Specification](npa-checker-ext-ocaml.md):
  `npa-checker-ext` trust boundary and runner contract.
- [Public Package And Registry Roadmap](public-package-roadmap.md): public
  package boundaries, registry readiness, and non-goals.
- [Standalone Repository Activation Record](standalone-repository-activation-record.md):
  public repository split and retained `npa-core` evidence.
- [Package Refactor Plan Command Design](refactor-plan-command-design.md):
  design record for the implemented read-only CLI command that ranks module and
  theorem-family refactor candidates from package metadata.

## Verify A Package

Use these commands from an external theorem package root after installing or
pinning the `npa` toolchain described in the current toolchain reference.

```sh
npa package check --root .
npa package build-certs --root . --check
npa package verify-certs --root . --checker reference
npa package check-hashes --root .
npa package axiom-report --root . --check
npa package index --root . --check
npa package publish-plan --root . --check
```

Base package verification is source-free and reference-checker-only. Optional
high-trust external checker workflows are separate and must not be treated as
additional trusted proof input unless their checker identity and policy are
explicitly pinned.

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

## Historical References

- [Toolchain Reference v0.1.1](npa-toolchain-reference-v0.1.1.md): historical
  SRA-02 reference retained for audit context.
- [Toolchain Reference v0.1.0](npa-toolchain-reference-v0.1.0.md): historical
  SRA-01 reference retained for audit context. Use v0.2.0 as the current
  public package toolchain reference.

## License

NPA is licensed under the [Apache License 2.0](../LICENSE). See
[NOTICE](../NOTICE) for attribution.
