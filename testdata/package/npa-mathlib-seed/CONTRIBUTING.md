# Contributing To npa-mathlib-seed

Visibility: internal test fixture note.

This contributor note is for the local `npa-mathlib-seed` regression fixture.
It is not the public package-author contribution guide.

This fixture models a standalone theorem-library repository. Treat
`testdata/package/npa-mathlib-seed/` as the package root when running from this
repository; package paths in
`npa-package.toml` are relative to that root and must keep working after the
directory is copied out as a standalone package root.

## Theorem-Only Changes

A theorem-only pull request changes `Proofs/Ai/*/source.npa` declarations and
the generated artifacts that follow from those declarations. It should not
change kernel, checker, certificate canonicalization, package import trust
rules, automation trust policy, or registry behavior.

To add or update a theorem:

1. Edit the relevant `source.npa` file under `Proofs/Ai/`.
2. Keep imports directed at the existing closed seed module set or the declared
   `npa-std` certificate artifacts.
3. Rebuild certificates when the source theorem text or imported theorem
   dependency changes.
4. Refresh generated package artifacts when certificates, source hashes, export
   hashes, certificate hashes, axiom report content, theorem index entries, or
   publish-plan downstream metadata change.
5. Run the base package command sequence from this package root:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package check-hashes --root . --json
npa package verify-certs --root . --checker reference --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
npa package publish-plan --root . --check --json
```

Before the `npa` binary is installed, use the parent workspace command shape:

```sh
cargo run -p npa-cli -- package check --root testdata/package/npa-mathlib-seed --json
```

Check mode must fail when generated artifacts are stale. If a theorem-only
change intentionally updates certificates or hashes, regenerate the affected
artifacts first and then rerun the sequence above.

For an intentional theorem update, refresh artifacts in this order:

```sh
npa package build-certs --root . --json
npa package axiom-report --root . --json
npa package index --root . --json
npa package publish-plan --root . --json
```

If the manifest hash pins are stale, update them deliberately as part of the
same theorem-only change and rerun the write-mode command that reported the
mismatch. Expected artifact drift is:

- source theorem edit: certificate, source hash, certificate file hash, export
  hash, certificate hash, and package lock may change;
- axiom dependency edit: `generated/axiom-report.json` and each affected
  module's axiom report hash may change;
- public declaration add, remove, or rename: `generated/theorem-index.json`,
  `generated/publish-plan.json`, downstream import bundle entries, and
  downstream compatibility may change;
- replay, meta, automation, or AI sidecar change only: no proof artifact hash
  should change unless the canonical certificate bytes also changed.

## Package Boundary

The seed package must not use absolute local filesystem paths or hidden paths
back into the parent `npa` repository. Standard-library dependencies are
declared as hash-pinned `npa-std` imports and resolved through vendored
certificate artifacts under `vendor/npa-std/`.

The base seed contains only:

- `Proofs.Ai.Basic`
- `Proofs.Ai.Prop`
- `Proofs.Ai.Eq`
- `Proofs.Ai.Nat`
- `Proofs.Ai.Reduction`

Adding larger proof-corpus modules, changing the axiom policy, adding
`Eq.rec`-dependent modules, or renaming the public namespace is outside
the current seed command wiring scope.

## Local Generated Artifact Review

Local check mode validates `package-lock.json`, `axiom-report.json`,
`theorem-index.json`, and `publish-plan.json`. A stale generated artifact
should be regenerated through the corresponding package command and reviewed as
ordinary metadata drift.

Release review records the generated package artifacts, checked certificates,
and JSON diagnostics needed by downstream packages. The release profile is
reference-checker-only; fast-kernel output is labeled separately and is not a
reference checker verdict. High-trust external verification remains disabled
until the seed package supplies the CLR-08 pinned external checker binary,
runner policies, checker registry, and release audit evidence.

## Review Policy

Review theorem-only pull requests for:

- theorem statement clarity, including whether names describe the exported
  proposition rather than the proof technique;
- module placement and dependency direction, especially whether new imports keep
  the initial seed set closed over declared `npa-std` artifacts;
- declaration summaries in `npa-package.toml`, including theorem names and any
  intentional module export changes;
- axiom report changes, with every new or removed axiom dependency called out
  explicitly in review;
- generated hash drift, confirming it follows from source or certificate
  artifact changes rather than manual metadata edits;
- downstream compatibility, especially changes to exported declaration names,
  export hashes, certificate hashes, certificate artifact paths, or
  `downstream_import_bundle` entries.

Do not accept package metadata, theorem indexes, publish-plan metadata, replay
files, tactics, automation logs, AI output, or command success as proof
evidence. They are useful review inputs, but they are not trusted proof evidence.
Acceptance still comes from canonical certificate bytes and source-free checker
verdicts.

## Reference-Checker-Only Release Policy

The base seed release remains reference-checker-only until the seed repository
supplies the CLR-08 high-trust inputs: a pinned external checker binary, runner
policies, checker registry, and release audit bundle evidence. In the base
profile:

- `npa package verify-certs --root . --checker reference --json` is the required
  source-free proof gate;
- fast-kernel output may be uploaded as labeled supplemental diagnostics, but
  it is not the reference checker verdict;
- no `verified_high_trust` artifact is generated;
- downstream users must pin certificate bytes and rerun source-free verification
  locally.

## CLR-10 Registry Handoff

CLR-10 should consume this release as registry input, not as an already
available registry service. The handoff bundle is:

- `generated/publish-plan.json`, including `module_registry_entries` and
  `downstream_import_bundle`;
- `generated/package-lock.json`;
- `generated/axiom-report.json`;
- `generated/theorem-index.json`;
- checked certificate artifacts under `Proofs/Ai/**/certificate.npcert` and
  vendored `npa-std` certificate artifacts;
- command JSON diagnostics from the reference-checker-only release review.

Registry seed entries are discoverability metadata. They must not become
trusted proof evidence or an implicit latest-version resolver.

## Trust Boundary

Source files, replay files, metadata, package manifests, generated indexes,
publish plans, and command diagnostics are useful contributor artifacts, but
they are not
trusted proof evidence. Acceptance remains based on canonical certificates plus
source-free checker verdicts.
