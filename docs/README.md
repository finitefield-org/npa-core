# NPA User Documentation

These docs are for people who use NPA to check, author, or publish theorem
packages. Development notes, phase specifications, milestone evidence, package
fixtures, and CI templates were not part of the listed-path migration and
remain in the sibling `../npa` checkout.

NPA is certificate-first. Documentation, source files, theorem indexes, publish
plans, CI results, registry metadata, tactic traces, replay files, and AI traces
are not proof evidence. Proof acceptance is based on canonical `.npcert` bytes,
the Rust kernel / verifier verdict, source-free checker verdicts, deterministic
certificate and import hashes, and axiom reports.

## Start Here

- [Repository README](../README.md): overview, trust boundary, build steps,
  package verification quick start, and repository layout.
- [Contributing](../CONTRIBUTING.md): local gates, corpus gate triggers,
  certificate compatibility policy, and contribution workflow.
- [Toolchain Reference v0.2.0](npa-toolchain-reference-v0.2.0.md): current
  `npa` toolchain reference for external theorem packages.
- [External Theorem Library CI](external-theorem-library-ci.md): package CI
  guide for external theorem libraries.

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

## Examples

These fixtures remain in the sibling `../npa` checkout and are useful as public
package examples:

- `../npa/fixtures/npa-std`: local standard-library package materialization.
- `../npa/fixtures/npa-mathlib`: public `Mathlib.*` theorem-library package
  example.
- `../npa/fixtures/npa-mathlib-downstream`: downstream certificate-vendoring
  example without a registry server.

The proof corpus and seed fixtures remain repository test material unless a
specific README links them as examples.

## Historical References

- [Toolchain Reference v0.1.1](npa-toolchain-reference-v0.1.1.md): historical
  SRA-02 reference retained for audit context.
- [Toolchain Reference v0.1.0](npa-toolchain-reference-v0.1.0.md): historical
  SRA-01 reference retained for audit context. Use v0.2.0 as the current
  public package toolchain reference.

## License

NPA is licensed under the [Apache License 2.0](../LICENSE). See
[NOTICE](../NOTICE) for attribution.
