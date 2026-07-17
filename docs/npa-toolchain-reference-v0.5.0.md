# NPA Toolchain Reference v0.5.0

This reference describes the adjacent-source `npa-cli 0.5.x` package interface.
It adds structured source context to Human frontend failures and advances
package command results to `npa.package.command_result.v0.2`. It does not
change the published `NPA-CERT-0.2.0`, `NPA-Core-0.2.0`, reference-checker
`0.2.0`, external-checker `0.2.0`, or `package_api::v1` contracts.

## Version axes

| Axis | Current value |
| --- | --- |
| Host CLI crate | `npa-cli 0.5.x` |
| Programmatic facade | `package_api::v1` |
| Package command result | `npa.package.command_result.v0.2` |
| Reference and external checker | `0.2.0` |
| Certificate and core specification | `NPA-CERT-0.2.0` / `NPA-Core-0.2.0` |
| Generated-artifact release manifest | `npa.generated_artifact_release_manifest.v0.2` |

The host version is not a proof-format or checker-version label.

Historical release evidence pairs `npa-cli 0.3.x` or `0.4.x` with
`npa.package.command_result.v0.1`. New evidence pairs `npa-cli 0.5.x` with
v0.2. The release validator rejects either cross-pair without changing the
release-manifest schema.

## Frontend diagnostic source context

When `npa package build-certs` fails in the Human frontend, a valid span in the
current module is reported as an optional `diagnostics[].source` object:

```json
{
  "path": "Proofs/Ai/ExplicitFinite/source.npa",
  "start_byte": 4821,
  "end_byte": 4822,
  "declaration": "explicit_finite_product_intro"
}
```

`source.path` is the validated package-relative source path. The existing
diagnostic `path`, such as `modules[12].source`, remains the manifest field
locator. `start_byte..end_byte` is the frontend's zero-based, half-open UTF-8
byte range, not a character, UTF-16, line, or column range. Use those values to
open the reported file and repair the named top-level declaration. No source
excerpt is included.

The declaration is added only when the exact in-memory source can be reparsed
with the same direct imported notation interfaces and a containing top-level
declaration can be identified. A parser failure may therefore report path and
byte range without `declaration`. A foreign, reversed, or out-of-bounds span
omits the entire `source` object rather than attaching a misleading file.

Source context is untrusted authoring metadata. It does not enter certificate
bytes, checker input, package locks, hashes, proof evidence, or artifact lists.
Rust consumers construct and inspect it through
`CommandDiagnosticSourceContext` builders and getters; both public diagnostic
types are non-exhaustive at the `npa-cli 0.5` boundary.

## Artifact ledger audit

Run the audit from a package root without generating or repairing artifacts:

```sh
npa package audit-artifact-ledger --root . --json
npa package audit-artifact-ledger --root . \
  --module Proofs.Ai.Basic --module Proofs.Ai.Eq --json
```

Repeated `--module` values are deduplicated in insertion order. Without a
module selector, every local package module declaring `meta` is reported;
modules without metadata are counted as `skipped_without_meta`. The command
validates the manifest and selection before reading artifacts, snapshots every
package and vendored certificate once, snapshots the selected source and
metadata once, then runs the in-process reference checker over the selected
certificate closure with one job, verdict memoization disabled, and
decode-cache counters disabled. It does not require or create
`generated/package-lock.json`.

Each selected module always accounts for these ten comparison slots:

| Identity | Manifest | Metadata | Live checker |
| --- | --- | --- | --- |
| source hash | yes | yes | unavailable |
| certificate-file hash | yes | yes | yes |
| export hash | yes | yes | yes |
| axiom-report hash | yes | yes | yes |
| certificate hash | yes | yes | yes |

An available comparison emits its stable match or field-specific mismatch
diagnostic. A comparison whose required input could not be read, parsed, or
checked emits `artifact_ledger_comparison_unavailable`; it is never silently
omitted. Metadata is accepted only as `npa-ai-proof-meta-v0.1` with canonical
names, paths, and hashes, duplicate-free imports and axioms, and no duplicate
JSON keys. Unknown descriptive extension fields remain tolerated.

The summary keeps three independent classification axes:

- hash drift location: `consistent`, `metadata_only_drift`,
  `manifest_only_drift`, `both_ledgers_same_stale_identity`,
  `both_ledgers_diverge`, or `unavailable`;
- producer identity: `matches`, `drift`, or `incomplete`;
- live checker: `checked`, `rejected`, `blocked`, or `not_run`.

Identity differences do not rewrite hash-drift classification. A fully
available, matching, checker-accepted audit exits 0. Any mismatch, unavailable
slot, producer mismatch, rejection, blocked module, or command prerequisite
failure exits 1; invalid CLI syntax exits 2.

The audit is nonmutating: it performs no network access, lock generation,
certificate rebuild, metadata refresh, cache write, or package-root write.
Source and metadata bytes are used only for their declared ledger comparisons;
diagnostics do not render their contents. The package root is a trusted local
filesystem boundary, so a selected path may resolve through a trusted local
symlink. Published verification remains the separate source-free checked-lock
workflow.

Remediate drift explicitly with the existing authoring commands only after
reviewing the audit result. Do not treat a repair command or generated lock as
proof evidence.

## L2 review, acceptance, and namespace transport

Export a canonical theorem review input, collect two immutable structured
sub-agent reports, and aggregate them before validation:

```sh
npa package prepare-l2-review-input --root ../npa-corpus/proofs \
  --policy ../npa-mathlib/policy/l2-acceptance-policy.json \
  --module Proofs.Algebra.Basic --declaration theorem_name \
  --out l2-reviews/theorem.input.json --json

npa package aggregate-l2-acceptance --root ../npa-corpus/proofs \
  --policy ../npa-mathlib/policy/l2-acceptance-policy.json \
  --review-input l2-reviews/theorem.input.json \
  --review l2-reviews/theorem.semantic.json \
  --review l2-reviews/theorem.adversarial.json \
  --existing l2-acceptance.json --out l2-acceptance.json --json
```

Then validate repository-governed theorem-level decisions against the current
proof-package snapshot:

```sh
npa package validate-l2-acceptance \
  --root ../npa-corpus/proofs \
  --policy ../npa-mathlib/policy/l2-acceptance-policy.json \
  --acceptance ../npa-corpus/proofs/l2-acceptance.json \
  --module Proofs.Algebra.Basic --json
```

The current policy is policy version 2. Inputs use
`npa.l2.review-input.v2`, reports use `npa.l2.review-report.v1`, and the source
ledger uses `npa.l2_acceptance.v2`. The validator binds policy and report file
hashes, input path/file/self hashes, source package/version and theorem-index
identity, the non-voting aggregator, two distinct required sub-agent roles,
agent-task and decision-ID prefixes, ordered review checks, unanimous accepted
verdicts, local theorem identity, statement hash, canonical module certificate
hash, and the exact `L2 Derived certificate` level. Repeated `--module` selectors
additionally require complete acceptance coverage for every local public
theorem in those modules. Unrelated module changes do not invalidate decisions
whose exact theorem and certificate identities remain current.

The configured policy requires independent `semantic-review` and
`adversarial-review` sub-agents with 2-of-2 unanimous acceptance; the promotion
aggregator cannot vote. This command performs no semantic review and issues no
decisions. Repository metadata cannot cryptographically authenticate that the
named collaboration tasks actually ran; a future orchestrator-signed
attestation would be required for that stronger guarantee. Authority policy,
acceptance records, theorem indexes, and command results are promotion
metadata, not proof evidence; canonical certificate verification remains the
proof authority.

For a strictly rename-only target, use
`package validate-l2-namespace-transport` with explicit source, clean target
baseline, materialized target, acceptance/transport policies, source ledger,
mapping request, and source-owned output. It compares decoded ID-independent
certificate semantics and runs cache-free source-free reference verification;
logical changes require fresh exact target L2 review.

## Programmatic use

Adjacent Rust consumers should construct requests through
`npa_cli::package_api::v1::audit_artifact_ledger_all` or
`audit_artifact_ledger_modules` and pass them to
`run_package_artifact_ledger_audit`. Raw option-struct literals remain outside
the supported compatibility boundary.

## External checker closure

The current Linux closure gate is:

```sh
npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.5.sh
npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.5.sh --functional-only
```

It binds the `npa-cli 0.5.x` host and `package_api::v1` facade to the unchanged
external checker and certificate/core axes. The `--functional-only` form is a
developer gate, not release evidence. The obsolete v0.3/v0.4 scripts and
dedicated compatibility tests have been removed; historical design records do
not constitute callable support.
