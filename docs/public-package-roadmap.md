# NPA Public Package And Registry Roadmap

This document records the public package direction for `npa-core` and the
public theorem-library repositories. It replaces older development-tree notes
that mixed package planning with private development and CI details.

## Trust Boundary

NPA remains certificate-first. Trusted proof evidence is:

```text
- canonical .npcert bytes
- Rust kernel / verifier verdict
- source-free checker verdict
- deterministic export_hash, certificate_hash, and axiom_report_hash
```

Untrusted helper data includes source text, tactic scripts, replay files,
theorem indexes, publish plans, registry metadata, API responses, and CI status.
Those artifacts may organize packages, but they do not accept proofs.

## Public Package Boundaries

The public ecosystem is split across these repository roles:

```text
npa-core
  kernel, certificate format, checkers, frontend, tactic, and package CLI

npa-std
  small stable standard-library package

npa-mathlib
  public theorem-library package

npa-web
  public web-facing repository

npa-project-fermat-last-theorem
  public project package following the project-package layout
```

Other project packages may consume these public packages, but they should do so
through package manifests, generated package artifacts, and hash-pinned imports,
not by depending on another repository checkout.

## Current Package Contract

External packages use `npa-package.toml` plus generated package artifacts. The
public package commands are documented in
[`npa-toolchain-reference-v0.2.0.md`](npa-toolchain-reference-v0.2.0.md).

The current package contract requires:

- source-free package verification through checked `.npcert` files;
- imports pinned by module name plus `export_hash`, and by
  `certificate_hash` when high-trust policy requires it;
- deterministic lock, axiom-report, theorem-index, and publish-plan artifacts;
- no implicit registry lookup, hidden package cache, or network trust during
  proof acceptance.

## Registry Readiness

Git release artifacts and hash-pinned package imports are the current public
distribution path. A future registry can improve search and discovery, but it
must not become a proof acceptance boundary.

A registry entry may index package names, versions, modules, hashes, axiom
reports, and release artifact locations. Consumers must still verify the
certificate bytes and declared imports locally.

## Non-Goals

This roadmap does not make source text trusted, does not require hosted CI
workflow templates, does not depend on private repositories, and does not define
a network-backed package resolver as part of core checking.
