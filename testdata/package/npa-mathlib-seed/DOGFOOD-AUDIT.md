# CLR-09-08 Dogfood Review And Registry Handoff Audit

This audit reviews the seed package as both a new contributor repository and a
downstream release input. It records the CLR-10 handoff facts without changing
proof artifacts, package schemas, checker policy, or the `npa` trusted base.

## Audit Result

The CLR-09 seed is usable as a reference-checker-only release seed. The current
artifact set is sufficient for a downstream package to import hash-pinned
certificates without a registry service, and theorem-only seed changes remain
outside kernel, checker, certificate canonicalization, and package trust rules.

No blocking CLR-09 findings remain. The gaps below are intentionally deferred
to CLR-10 or later milestones.

## New Contributor Review

A new contributor can treat `testdata/package/npa-mathlib-seed/` as the package
root when working from this repository, or the fixture directory itself after it
is copied as a standalone package root. The check-mode command sequence is
local to the seed package:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package check-hashes --root . --json
npa package verify-certs --root . --checker reference --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
npa package publish-plan --root . --check --json
```

The proof-relevant part of the theorem-only workflow changes only
`Proofs/Ai/*/source.npa`, the corresponding `certificate.npcert`, manifest hash
pins, and generated package artifacts when canonical certificate bytes or public
exports change. Replay, meta, automation, and AI sidecars may explain how a
certificate was produced, but they do not require a kernel, checker,
certificate-format, package trust, automation trust, or registry behavior
change in `npa`.

Review evidence is explicit:

- theorem names and declaration summaries live in `npa-package.toml`;
- certificate, source, export, axiom report, and certificate hashes are pinned
  in `npa-package.toml` and `generated/package-lock.json`;
- axiom report drift is visible through `generated/axiom-report.json`;
- theorem index and publish-plan drift are review metadata, not trusted proof
  evidence;
- replay files, meta files, automation output, AI output, command status, and
  future registry metadata are not trusted proof evidence.

## Downstream Package Review

`testdata/package/npa-mathlib-seed-downstream/` consumes the seed as a downstream
package without a registry server. Its fixture imports `Proofs.Ai.Basic` by
package name, package version, export hash, certificate hash, and certificate
file hash, then verifies both the vendored seed certificate and downstream
certificate source-free.

The downstream fixture deliberately vendors only:

```text
vendor/npa-mathlib-seed/Proofs/Ai/Basic/certificate.npcert
```

It does not vendor seed source, replay files, meta files, theorem indexes, or
registry state. `crates/npa-cli/tests/package_import_fixture.rs` checks that
corrupt publish metadata, export hash pins, and certificate hash pins are
rejected before the dependency is accepted.

## Hash-Pinned Import Evidence

The seed package has two external standard-library imports. Both are pinned in
`npa-package.toml` and `generated/package-lock.json` by package, version,
certificate path, export hash, and certificate hash:

- `Std.Logic.Eq` from `npa-std` version `0.1.0`;
- `Std.Nat.Basic` from `npa-std` version `0.1.0`.

The generated release handoff also pins every exported seed module in
`generated/publish-plan.json` under `downstream_import_bundle.modules`:

- `Proofs.Ai.Basic`
- `Proofs.Ai.Prop`
- `Proofs.Ai.Eq`
- `Proofs.Ai.Nat`
- `Proofs.Ai.Reduction`

Each bundle module carries exported declaration identifiers, export hash,
certificate hash, axiom report hash, certificate path, certificate file hash,
and reference-checker summary data. Consumers still must pin the certificate
bytes and rerun source-free verification locally.

## Release Artifact Set

The seed publish plan is checksum-only:

```text
publish_plan_hash = sha256:163784bfed8f63e9631d638f7b1698d36d5e504a2c4194bbd31edd284b12ae6c
signature_required = false
```

CLR-10 should consume these concrete release artifacts and review inputs from
the seed:

- `generated/publish-plan.json`
- `generated/package-lock.json`
- `generated/axiom-report.json`
- `generated/theorem-index.json`
- `npa-package.toml`
- `Proofs/Ai/Basic/certificate.npcert`
- `Proofs/Ai/Prop/certificate.npcert`
- `Proofs/Ai/Eq/certificate.npcert`
- `Proofs/Ai/Nat/certificate.npcert`
- `Proofs/Ai/Reduction/certificate.npcert`
- `vendor/npa-std/Std/Logic/Eq/certificate.npcert`
- `vendor/npa-std/Std/Nat/Basic/certificate.npcert`
- `CONTRIBUTING.md` as contributor guidance input;
- this audit document as registry-readiness input.

The publish plan summary records five local modules, two external imports,
eleven release artifacts, five module registry seed entries, and fourteen
checker summaries. Those registry seed entries are discoverability metadata;
they do not imply a live registry service or a latest-version resolver.

## Automation Boundary Review

The seed fixture intentionally contains no repository-hosted release
automation. Release review is represented by local package command output,
checked generated package artifacts, and source-free verifier results. Those
files are review metadata, not proof evidence.

## Deferred Gaps

Move these gaps to CLR-10 or later milestones:

- Registry readiness: decide whether to continue Git-release-based registry
  seed consumption or start an untrusted registry service. CLR-09 provides
  `npa.registry.module.v0.1` seed entries only.
- High-trust release evidence: no `verified_high_trust` artifact is generated
  until the seed repository supplies CLR-08 external checker inputs.
- Standalone package publication: moving the fixture to a separate package
  distribution path is outside this parent-repository milestone.
- Public namespace polish: renaming `Proofs.Ai.*` to a library namespace is
  deferred until package metadata and downstream imports are stable.
- Larger corpus import: `Eq.rec`-dependent and larger proof-corpus modules are
  deferred until their axiom policy and artifact churn can be reviewed
  intentionally.

## Validation Commands

The repository-level validation for this milestone is:

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
git diff --check
rg -n "npa-mathlib-seed|publish-plan|downstream_import_bundle|reference-checker-only|verified_high_trust" README.md docs crates testdata
```
