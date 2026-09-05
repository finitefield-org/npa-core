# NPA Toolchain Reference v0.7.0

Historical snapshot: this document preserves the v0.7 host/result contract and
uses “current” only relative to that release. For the active adjacent-source
contract, use the [v0.8 reference](npa-toolchain-reference-v0.8.0.md).

This reference describes the adjacent-source `npa-cli 0.7.x` package
interface. It adds a source-free theorem-premise report and advances the shared
generated-artifact check from five to six deterministic subresults. Package
command results remain `npa.package.command_result.v0.3`. The current source
producer and independent checkers use Core v0.3; the last published external
tag remains v0.2.0 until a separate release changes that pin.

## Version axes

| Axis | Current value |
| --- | --- |
| Host CLI crate | `npa-cli 0.7.x` |
| Programmatic facade | `package_api::v1` |
| Package command result | `npa.package.command_result.v0.3` |
| Theorem-premise report | `npa.package.theorem_premise_report.v0.1` |
| Reference checker | `0.3.0` |
| External checker | `0.3.0` |
| Current emitted certificate/core pair | `NPA-CERT-0.3.0` / `NPA-Core-0.3.0` |
| Read-only compatibility input pairs | exact v0.2.0, v0.1.2, and v0.1 pairs |
| Generated-artifact release manifest | `npa.generated_artifact_release_manifest.v0.2` |

The release validator accepts these host/result pairs:

| Host CLI | Command-result schema |
| --- | --- |
| `npa-cli 0.3.x` / `0.4.x` | `npa.package.command_result.v0.1` |
| `npa-cli 0.5.x` | `npa.package.command_result.v0.2` |
| `npa-cli 0.6.x` / `0.7.x` | `npa.package.command_result.v0.3` |

Cross-pairs remain invalid. The v0.6 reference is historical and is not
rewritten by this release.

### Core v0.3 identity and migration

Every current Human and Machine producer emits the v0.3 pair, including for
plain-only modules. Both surfaces spell an opaque definition as `opaque def`;
the Machine term body remains fully explicit. Its body is checked and locally
transparent to later declarations in the defining module, then removed from
the exported interface. Importers cannot restore or unfold it.

V0.2 is an exact compatibility input, not a current output option. Migration
requires a rebuild, canonical re-encoding, new certificate identities, package
artifact refresh, and source-free revalidation; a header-only edit rejects.
Targeted refresh may reuse an interface-stable dependent only after rebinding
the affected certificate chain and verifying it against current imports.

The package manifest and package lock continue to use the independent
`npa.core.v0.1`, `npa.certificate.canonical.v0.1`, `npa.package.v0.1`, and
`npa.package.lock.v0.1` contract axes. The
`npa.package.build_check_cache.v0.2` key stores emitted
`output_certificate_format` / `output_core_spec`;
`npa.package.audit_cache.v0.2` keys and
`npa.package.verified_export_summary.v0.2` module rows store each decoded
module's `certificate_format` / `core_spec`. None derives the module pair from
the package profiles.

Author substantial opaque implementations in semantic leaf modules and expose
stable specification theorems. Do not expose a whole-body equality theorem,
which repeats the implementation despite the sealed constant. The defining
module still checks and may unfold the body, so the expected performance gain
begins only in importing modules.

## Theorem-premise report

Generate the fixed report or compare it with current checked certificate
artifacts:

```sh
npa package theorem-premise-report --root . --json
npa package theorem-premise-report --root . --check --json
```

The command reads the validated manifest, checked package lock, and local and
imported certificate bytes required by the existing source-free verifier. It
does not read proof source, replay, metadata sidecars, Git state, a network,
or theorem-search data.

Each public local theorem entry records:

- full certificate and declaration identity;
- theorem telescope binder classes and structural hashes;
- proposition-valued fact-premise dependencies and checked-proof use sites;
- direct resolved builtin or package-global dependencies;
- verifier-recomputed transitive axiom dependencies; and
- derived statement, premise-use, dependency-basis, and review classifications.

Existing packages use theorem declarations for proposition-valued and
data-valued conclusions. Both are included. A fact premise is specifically a
Pi binder whose domain infers to `Prop`; data parameters do not become fact
premises.

The report is deterministic audit metadata, not proof evidence. It cannot
change certificate acceptance, hashes, memo keys, theorem search, or package
locks. The fixed analysis limits are included in report identity. Limit
exhaustion fails the complete projection and writes no partial report.

In check mode the CLI first requires a real `generated` directory and a real,
regular `generated/theorem-premise-report.json`. Symlinked parents, symlinked
targets, non-regular targets, unreadable bytes, and non-UTF-8 bytes are
rejected. A valid canonical report that differs from current projection is
reported as stale with hashes, not report bodies or proof terms.

Write mode serializes the complete report before touching the target. It uses
a synced sibling temporary file, atomic rename, and parent-directory sync.
An identical existing file is not replaced.

Programmatic callers construct options through:

```rust
let options = npa_cli::package_api::v1::theorem_premise_report(common, true)
    .with_timings(npa_cli::args::PackageTimingMode::Summary);
```

Raw `PackageTheoremPremiseReportOptions` construction is outside the adjacent
consumer compatibility boundary.

## Package export output paths

Explicit output paths for `package export-candidate-metadata` and
`package export-summary` are relative to the package root selected by
`--root`. For example:

```sh
npa package export-candidate-metadata --root proofs \
  --module Proofs.Example --declaration theorem_name \
  --out generated/theorem_name.metadata.json --json
npa package export-summary --root proofs \
  --out generated/custom-export-summary.json --json
```

The destinations are `proofs/generated/theorem_name.metadata.json` and
`proofs/generated/custom-export-summary.json`. An explicit `--out` must not
repeat the terminal package-root directory as a complete path component.
Values such as `proofs/generated/output.json` or
`npa-project-example/proofs/generated/output.json` with `--root proofs` are
rejected as usage errors before the output is read or written. Absolute paths,
parent traversal, URI-like paths, and other lexically invalid package paths
retain their existing validation diagnostics.

The rule applies equally to export-summary check and write modes and to direct
Rust option construction. Omitting export-summary `--out` still uses
`generated/verified-export-summary.json`; artifact schemas, generated bytes,
and `package_api::v1` are unchanged.

## Generated-artifact closure

The current aggregate command is:

```sh
npa package check-generated --root . --json
```

It builds one process-local source-free package snapshot and reports these six
subresults in order:

1. axiom report;
2. theorem index;
3. theorem-premise report;
4. verified export summary;
5. publish plan; and
6. fast certificate verification.

The theorem-premise subresult reuses already decoded verified modules. It does
not run a second verifier. A stale or invalid report does not suppress the
other deterministic subresults; the group fails after collecting all six.
The snapshot, checker timings, and aggregate command result are local
orchestration metadata and are not proof evidence.

## Interface-proposal curation validator

`npa-cli 0.7.x` exposes the read-only v1 Mathlib interface-proposal check:

```sh
npa package check-interface-proposals \
  --root <package-root> [--proposal-root <path>] \
  [--previous-proposal-root <path>] --json
```

`--proposal-root` defaults to `interface-proposals` beneath `--root` and
`--previous-proposal-root` is an explicit caller-supplied earlier proposal
root. The JSON result is ordered and byte-stable, with proposal rows, exact
file/set hashes, five lifecycle counts, and bounded diagnostics. The previous
root is treated as the immediately preceding validated snapshot by caller
contract; the command reports only detectable per-record continuity and does
not inspect Git history.

This command is curation validation, not catalog admission or proof
verification. It always reports `proof_evidence: false`, reads only the local
manifest and canonical proposal TOML tree, never dereferences evidence URLs,
does not invoke Git, network, source rebuilds, certificate verification, or a
proof checker, and writes no files. The compact in-repository example is
`testdata/package/interface-proposals-valid`.

## Adopted surface and direct reconciliation gates

After an adopted proposal has an independently authored target artifact, use
the read-only exact-surface gate before accepting either catalog route:

```sh
npa package check-interface-proposal-surface \
  --root <package-root> --proposal-root interface-proposals \
  --proposal-path Mathlib/Logic/Function/Basic.toml \
  --proposal-sha256 sha256:<64 lowercase hexadecimal characters> \
  --target-module Mathlib.Logic.Function.Basic --json
```

`status = "parity"` means the proposal and prepared certificate surface are
equal on module name, imports, declaration order/names/kinds/surfaces,
signatures, definition bodies, inductive families, and exported support
closure. The command is local, read-only, Git-free, network-free, and always
emits `proof_evidence: false`; it does not edit the proposal or target.

For directly authored `npa-mathlib` content, the caller prepares the complete
strictly newer target and invokes the implemented registry transaction with an
explicit older target and audit. Review the deterministic dry-run first, then
apply the same inputs:

```sh
npa package reconcile-promotion-origin-registry \
  --root <current-npa-mathlib> \
  --previous-target-root <previous-validated-npa-mathlib> \
  --audit docs/promotion/catalog-sync.md \
  --out docs/promotion/catalog-sync.json \
  --dry-run --json
npa package reconcile-promotion-origin-registry \
  --root <current-npa-mathlib> \
  --previous-target-root <previous-validated-npa-mathlib> \
  --audit docs/promotion/catalog-sync.md \
  --out docs/promotion/catalog-sync.json \
  --apply --json
```

The transaction validates package and generated identities, writes its
attestation and registry last, and does not create or modify source,
certificates, metadata, replay, manifest, generated projections, released
snapshots, or Git state. `validate-promotion-origin-registry` is the post-apply
registry gate. Source-backed implementations remain owned by the separate
promotion materializer (`prepare-promotion`, `materialize-promotion`, and
`validate-promotion-materialization`); reconciliation must not be used to
replace that route.

Older published packages do not contain the new report. Their historical
release bundles remain governed by the recorded host/toolchain contract.
Current `npa-cli 0.7.x` source closure requires the sixth artifact.

## Unchanged v0.6 capabilities

The following v0.6 capabilities remain available with the same semantics:

- checked and reconstructed package-lock modes;
- targeted certificate authoring and atomic artifact refresh;
- bounded frontend source and kernel-conversion diagnostics;
- read-only package artifact-ledger audit;
- reference, fast, and pinned external checker modes; and
- `package_api::v1` construction for existing adjacent consumers.

See the historical [v0.6 reference](npa-toolchain-reference-v0.6.0.md) for
those contracts. The reference checker advances independently to `0.3.0` for
typed unknown-reference diagnostics. The current external checker is also
`0.3.0`; its v0.3 capability does not relabel an exact v0.2.0, v0.1.2, or v0.1
compatibility input.

Artifact refresh renders each declared `meta.json` `imports` field from the
module's validated manifest-declared direct imports. This is distinct from the
certificate import table, which may additionally contain transitive
dependencies required to check exported declaration bodies. Refresh does not
remove those certificate dependencies. A successful full or targeted refresh
therefore remains immediately compatible with `package audit-artifact-ledger`,
which compares metadata import identity with the manifest direct-import set.

Targeted `package build-certs --update-manifest-hashes` keeps the complete
local dependent closure as a conservative candidate set but no longer
unconditionally elaborates every dependent. Seeds, stale sources or checked
baselines, changed imported exports, unsupported formats/profiles, and
inexact source-interface projections retain the ordinary source-rebuild path.
An export-stable dependent with a qualified source and checked certificate may
instead update every changed local strict certificate pin in its complete
certificate import table. The format-owned operation structurally masks all
other fields, canonically re-encodes the certificate, and live source-free
verifies it against the newly verified exact imports. Exact-identity
dependents are also live verified before unchanged reuse.

Classification and execution proceed in package topological order, so rebound
certificate hashes propagate through chains and diamonds. Full refresh,
ordinary checks, external pins, staged writes, rollback, and reference
verification are unchanged. The additive `package_build_refresh_plan`
informational diagnostic reports candidate, source-rebuild, certificate-rebind,
unchanged, source-scan, source-interface, and bounded fallback counts for both
`--module` and `--changed` targeted refresh.

### Targeted external prerequisite closure

Targeted ordinary `package build-certs --check` expands directly selected
top-level external imports to their complete manifest-declared transitive
certificate dependency closure. It reads certificate import headers to build a
deterministic dependency-before-consumer plan, then subjects every planned
certificate to the existing canonical verification, axiom-policy, and manifest
pin checks. The plan uses an explicit heap work stack, so dependency depth does
not consume Rust call-stack depth; decoded headers select checked artifacts but
are not proof evidence.

Unrelated external certificates remain unread. Duplicate dependency edges are
deduplicated, and external dependency cycles fail with the existing
`lock_import_cycle` package-graph diagnostic. Explicit `--module` selection and
external-certificate-only `--changed` selection use the same closure logic. To
bound untrusted discovery inputs deterministically, targeted closure planning
accepts at most 65,536 top-level external imports, 1,048,576 cumulative unique
dependency edges, and 256 MiB of cumulative certificate bytes. Exceeding a cap
fails with `external_import_closure_limit_exceeded`. Command-result, manifest,
package-lock, and certificate schemas are unchanged.

## External checker closure

Run package verification without local acceleration when collecting comparable
fast/reference/external identities:

```sh
npa package verify-certs --root . --package-lock checked --checker fast \
  --audit-cache off --verifier-memo off --json
npa package verify-certs --root . --package-lock checked --checker reference \
  --audit-cache off --verifier-memo off --json
npa package verify-certs --root . --package-lock checked --checker external \
  --audit-cache off --verifier-memo off --jobs 1 \
  --runner-policy ci/runner.release.json \
  --runner-policy-hash "$NPA_RUNNER_POLICY_HASH" \
  --checker-registry ci/checker-binaries.json --json
```

The external command above records the intended compatibility ABI only. The
current host fails closed with `external_checker_supervisor_unavailable` before
creating imports or results because it cannot yet enforce descendant memory
and timeout together with authenticated step accounting. Fast and reference
commands remain operational; no external checked evidence may be inferred from
the fail-closed result.

The current Linux closure gate is:

```sh
npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.7.sh
npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.7.sh --functional-only
```

It binds the `npa-cli 0.7.x` host to the unchanged `package_api::v1` external
checker adapter. Raw result v2 advertises the checker capability in
`certificate_format` / `core_spec` and records the decoded certificate in
`input_certificate_format` / `input_core_spec`; checked results additionally
bind `module`, `certificate_hash`, `export_hash`, and `axiom_report_hash`. The
functional-only form is a developer gate and does not produce release
evidence.
