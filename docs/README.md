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
- [Toolchain Reference v0.9.0](npa-toolchain-reference-v0.9.0.md): current Rust
  CLI/API compatibility reference, kernel fuel diagnostics, common performance
  measurements, checker gates, and package operations.
- [Package-Verifier Process-Memo Execution-Scope Rollout](package-verifier-process-memo-execution-scope-rollout.md):
  caller-owned bounded memo migration, capacity and fallback semantics, and the
  diagnostic performance-evidence boundary.
- [Package Changed-Selection Git Query Rollout](package-changed-selection-git-query-rollout.md):
  exec-headroom-aware literal pathspec batching, exact error/process ordering,
  common measurement integration, and the reviewed release-evidence boundary.
- [Toolchain Reference v0.6.0](npa-toolchain-reference-v0.6.0.md): historical
  `npa-cli 0.6.x` compatibility reference.
- [Toolchain Reference v0.5.0](npa-toolchain-reference-v0.5.0.md): historical
  `npa-cli 0.5.x` compatibility reference.
- [Toolchain Reference v0.2.0](npa-toolchain-reference-v0.2.0.md): published
  tagged toolchain reference retained unchanged for external theorem packages
  pinned to the v0.2.0 release.

## Core References

- [Core Implementation Specification v0.4.0](core-spec-v0.4.0.md): frozen,
  implemented six-form let-free core and current-only certificate pair.
- [Toolchain Reference v0.9.0](npa-toolchain-reference-v0.9.0.md): current
  host, package, checker, and exporter contract.
- [v0.9.0 Release Notes](release-notes-v0.9.0.md): migration boundary,
  verification evidence, and retired-host cleanup record.
- [Term-Level `let` Removal Design](let-removal-plan.md): staged breaking
  migration to a let-free source language, kernel, certificate format, checker
  set, and package ecosystem; Milestones 0 through 7 are complete.
- [Core Implementation Specification v0.3.0](core-spec-v0.3.0.md): historical
  tagged local-implementation dependencies, checked same-module transparency,
  sealed exports, hash-domain migration, and four-version compatibility.
- [Core Specification v0.2.0](core-spec-v0.2.0.md): version-scoped historical
  contract for the retired exact-v0.2 compatibility input lane.
- [Inductive Constructor Universe Bounds Design](inductive-constructor-universe-bounds-design.md):
  implemented security rule for constructor-field universe bounds across the
  Rust kernel, certificate paths, reference checker, and OCaml checker.
- [OCaml Clean-Room External Checker Specification](npa-checker-ext-ocaml.md):
  `npa-checker-ext` trust boundary and runner contract.
- [OCaml External Checker Core v0.2.0 Compatibility Audit And Task List](npa-checker-ext-core-v0.2.0-compatibility-todo.md):
  closed audit, completed compatibility tasks, and conformance/release-gate
  evidence for the OCaml checker.
- [OCaml External Checker v0.4 Gate](../checkers/npa-checker-ext/README.md):
  strict v0.4 clean-room capability, shared three-checker conformance matrix,
  and actual-input versus checker-capability identity binding.
- [Public Package And Registry Roadmap](public-package-roadmap.md): public
  package boundaries, registry readiness, and non-goals.
- [Package Refactor Plan Command Design](refactor-plan-command-design.md):
  design record for the implemented read-only CLI command that ranks module and
  theorem-family refactor candidates from package metadata.
- [Package Artifact Refresh Command Design](package-artifact-refresh-command-design.md):
  initial design and implementation record for the package artifact refresh
  mode. The current v0.9 workflow additionally refreshes declared metadata and
  supports dependency-safe targeted selection as documented above.
- [Package Build Selected-Source Fail-Fast Design](package-build-selected-source-fail-fast-design.md):
  implemented ordering that reports selected Human source delimiter and
  frontend failures before reverse-only dependents and package-wide artifact
  traversal while preserving canonical refresh and complete-lock validation.
- [Interface Proposal Surface-Drift Contract v1](interface-proposal-surface-drift-v1.md):
  implemented read-only comparison between an adopted proposal and a prepared
  target module.
- [Promotion-Origin Registry Reconciliation Command](promotion-origin-registry-reconciliation.md):
  implemented recurring transaction for synchronizing any valid older catalog
  registry with a strictly newer mutable `npa-mathlib` target.

## Current Source And Published Tag

The current core checkout builds v0.4 certificates, and both current
independent checkers advertise and accept only the exact v0.4 certificate/core
pair. The public CLI and package ecosystem use v0.9.0.
The last published external toolchain tag is still v0.2.0; external packages
pinned to that tag continue to follow its historical toolchain reference. A
source checkout, checker capability, checked input pair, package profile, and
published tag are separate version axes.

Both Human and Machine source use `opaque def`; the Machine body remains fully
explicit. The checked body is transparent only to later declarations in the
defining module and is sealed from importers. Authors should isolate the
implementation in a semantic leaf module and publish stable specification
theorems rather than a theorem that repeats the complete body. This boundary
does not make the defining module faster to check.

Package manifests and locks retain the v0.1 profile axes.
`npa.package.build_check_cache.v0.2` and
`npa.package.audit_cache.v0.2` keys, and
`npa.package.verified_export_summary.v0.2` module rows, separately bind the
exact decoded certificate/core pair. Rebuilding under v0.4 and refreshing
affected package artifacts is required during the ecosystem migration; editing
only the header is invalid.

## Verify A Package

Use these commands from an external theorem package root after installing or
pinning the `npa` toolchain described in the current toolchain reference.

```sh
npa package check-source-structure --root .
npa package check --root .
npa package build-certs --root . --check
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off
npa package check-hashes --root .
npa package axiom-report --root . --check
npa package index --root . --check
npa package theorem-premise-report --root . --check
npa package export-summary --root . --check
npa package publish-plan --root . --check
npa package check-generated --root . --timings summary
npa package validate-promotion-origin-registry --root . --json
npa package audit-artifact-ledger --root . --json
```

Run `check-source-structure` immediately after editing Human Surface source.
With no selector it checks every manifest module in deterministic topological
order. Repeated `--module MODULE` checks registered modules, while repeated
`--path PACKAGE_RELATIVE_PATH` checks source files directly without requiring a
manifest entry; module and path selectors are mutually exclusive. The command
is read-only and dependency-free. Its JSON diagnostic identifies both the
unexpected close/EOF location in `source` and the corresponding opener in
`delimiter.opening_source` when one exists; that field is null for an
unexpected closer with no opener. Success proves only UTF-8, lexical validity,
and balanced/nested `()[]{}`; it is not a parser, elaborator, type checker,
certificate checker, or source of proof evidence.

`verify-certs` has a closed selector set: no selector verifies the full package,
`--changed` selects current working-tree certificate changes, repeated
`--module MODULE` selects explicit local seeds, and `--base REF` selects a clean
committed merge-base-to-`HEAD` range with structural full-verification
escalation. The selectors are mutually exclusive. Base mode requires a checked
lock and cache/memo off, rejects dirty protected package inputs, and fails on an
empty range. Its selection summary is review metadata rather than a replacement
for canonical build, hash, lock, axiom, or policy gates; see the
[v0.9.0 selector contract](npa-toolchain-reference-v0.9.0.md#verify-certs-selector-modes).

Targeted `build-certs --check` may use the explicit advisory command
`build-certs --build-check-cache local-hit`; an earlier live `read-through` run
can warm eligible support entries. `read-through` still performs all support
checks live; `build-certs --build-check-cache local-hit` may reuse exact eligible
support contexts, but it builds every reached target fresh and returns
local-only, non-evidence feedback. Both non-off build-check modes may write only
their automatically placed external local stores, and
`build-certs --build-check-cache local-hit` warms only eligible cache-free live
miss subtrees. An unavailable store falls back to live checking with a bounded
diagnostic.

Do not confuse this with `verify-certs --audit-cache local-hit`. The two flags
select different stores for different commands, and neither produces proof
evidence. Completion and release retain cache-off canonical build and ordinary
source-free verification, including reference verification when package policy
requires it. The [v0.9.0 toolchain reference](npa-toolchain-reference-v0.9.0.md#targeted-build-check-cache)
defines the complete mode matrix, placement, storage, recovery, and package API
contract.

For the compact Mathlib interface-proposal curation fixture, run this from
the `npa-core` repository root using the separate network-free, read-only
validator:

```sh
npa package check-interface-proposals \
  --root testdata/package/interface-proposals-valid \
  --proposal-root proposals --json
```

The command emits `npa.mathlib.interface_proposal_check.v1` rows, hashes,
lifecycle counts, and bounded diagnostics. An optional
`--previous-proposal-root` is a caller-supplied immediately preceding
snapshot; the command checks only locally detectable per-record continuity and
does not select history itself. It reads the local package manifest and the
canonical proposal tree, does not follow evidence URLs or invoke Git, network,
certificate verification, or proof checking, writes no files, and is not proof
verification or catalog admission. Its `proof_evidence` field is always
`false`.

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
`generated/package-lock.json`, use the current v0.9 source CLI with explicit
reconstructed mode:

```sh
cargo run --locked --offline -p npa-cli -- package verify-certs \
  --root ../PACKAGE/proofs --package-lock reconstructed --checker reference \
  --audit-cache off --verifier-memo off --json
```

Reconstructed mode reports its canonical lock hash and writes no package-root
file. It is authoring evidence, not a substitute for the exact checked lock in
a release or published-bundle audit. See the v0.9.0 toolchain reference for the
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
