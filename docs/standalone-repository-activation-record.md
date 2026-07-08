# NPA Standalone Repository Activation Record

This is the public activation record for the split between the `npa-core`
toolchain repository and standalone theorem-library package repositories.

## Trust Boundary

Repository activation does not move proof acceptance into Git hosting, release
pages, CI status, registry metadata, package indexes, or source review.

Trusted proof evidence remains:

```text
- canonical .npcert bytes
- Rust kernel / verifier verdict
- source-free checker verdict
- deterministic export_hash, certificate_hash, and axiom_report_hash
```

Package manifests, theorem indexes, publish plans, release notes, and registry
metadata remain untrusted orchestration.

## Activated Public Boundaries

The public split is:

```text
npa-core
  public toolchain and checker implementation

npa-std
  public standard-library package

npa-mathlib
  public theorem-library package

npa-web
  public web-facing repository

npa-project-fermat-last-theorem
  public project package
```

All other repositories are private.

## Evidence Retained In npa-core

`npa-core` keeps compact public package fixtures and toolchain references:

- `testdata/package/npa-std`
- `testdata/package/npa-mathlib`
- `testdata/package/npa-mathlib-downstream`
- `docs/npa-toolchain-reference-v0.2.0.md`
- historical toolchain references v0.1.0 and v0.1.1

These fixtures are examples and regression material. They do not require a
checkout of another NPA repository.

## Compatibility Rules

Standalone packages must use hash-pinned imports and checked package artifacts.
Release artifacts may distribute certificates and metadata, but consumers must
verify the certificate bytes and import hashes locally.

No registry server, network lookup, CI template, or hidden cache is required for
core package verification.
