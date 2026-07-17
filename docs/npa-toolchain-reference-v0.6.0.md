# NPA Toolchain Reference v0.6.0

This reference describes the adjacent-source `npa-cli 0.6.x` package interface.
It adds targeted certificate authoring, metadata refresh, directly displayable
source locations, and bounded kernel-conversion context. Package command
results advance to `npa.package.command_result.v0.3`. The published
`NPA-CERT-0.2.0`, `NPA-Core-0.2.0`, reference-checker `0.2.0`,
external-checker `0.2.0`, and `package_api::v1` contracts do not change.

## Version axes

| Axis | Current value |
| --- | --- |
| Host CLI crate | `npa-cli 0.6.x` |
| Programmatic facade | `package_api::v1` |
| Package command result | `npa.package.command_result.v0.3` |
| Reference and external checker | `0.2.0` |
| Certificate and core specification | `NPA-CERT-0.2.0` / `NPA-Core-0.2.0` |
| Generated-artifact release manifest | `npa.generated_artifact_release_manifest.v0.2` |

The host version is not a proof-format or checker-version label.

The release validator accepts exactly these host/result pairs:

| Host CLI | Command-result schema |
| --- | --- |
| `npa-cli 0.3.x` / `0.4.x` | `npa.package.command_result.v0.1` |
| `npa-cli 0.5.x` | `npa.package.command_result.v0.2` |
| `npa-cli 0.6.x` | `npa.package.command_result.v0.3` |

Cross-pairs are rejected without changing the release-manifest schema.

## Frontend diagnostic source context

When `npa package build-certs` fails in the Human frontend, a valid span in the
current module is reported as an optional `diagnostics[].source` object:

```json
{
  "path": "Proofs/Ai/ExplicitFinite/source.npa",
  "start_byte": 4821,
  "end_byte": 4822,
  "declaration": "explicit_finite_product_intro",
  "line": 133,
  "column": 17,
  "token": "x"
}
```

`source.path` is the validated package-relative source path. The existing
diagnostic `path`, such as `modules[12].source`, remains the manifest field
locator. `start_byte..end_byte` remains the canonical zero-based, half-open
UTF-8 byte range. `line` and `column` are one-based display coordinates;
column counts Unicode scalar values from the start of the line. `token` is the
exact reported span only when it is valid UTF-8, nonempty, non-control, and at
most 64 bytes. No source line or surrounding excerpt is included.

The declaration is added only when the exact in-memory source can be reparsed
with the same direct imported notation interfaces and a containing top-level
declaration can be identified. A parser failure may therefore report path and
byte range without `declaration`. A foreign, reversed, or out-of-bounds span
omits the entire `source` object rather than attaching a misleading file.

Source context is untrusted authoring metadata. It does not enter certificate
bytes, checker input, package locks, hashes, proof evidence, or artifact lists.
Rust consumers construct and inspect it through
`CommandDiagnosticSourceContext` builders and getters; public diagnostic types
are non-exhaustive at the `npa-cli 0.6` boundary.

## Bounded kernel-conversion context

Human `kernel_handoff` failures may include a `conversion` object after
`source`:

```json
{
  "phase": "definitional_equality",
  "outcome": "not_defeq",
  "lhs_head": "application",
  "rhs_head": "constant:Example.expected",
  "depth": 7
}
```

The object records only a stable phase, `not_defeq` or `fuel_exhausted`, two
bounded expression heads, and recursion depth. It never contains complete
expressions, local contexts, or source excerpts. Recording this diagnostic does
not alter reduction order, fuel, the returned kernel error, or acceptance.

## Targeted certificate authoring and refresh

Use repeatable `--module` values for an explicit local selection, or
`--changed` for package authoring paths changed relative to Git `HEAD`:

```sh
npa package build-certs --root proofs --check \
  --module Proofs.Ai.Example.Leaf --json

npa package build-certs --root proofs --update-manifest-hashes \
  --module Proofs.Ai.Example.Leaf --json

npa package build-certs --root proofs --update-manifest-hashes \
  --changed --json
```

Targeted ordinary check compiles only selected seeds and verifies prerequisite
certificates from checked bytes. Targeted refresh rebuilds the selected seeds
and their complete local dependent closure, then stages certificates, manifest
pins, declared `meta.json` sidecars, and the full package lock. Support modules
outside that closure must have current source pins. A changed manifest promotes
selection to the full package; a changed lock alone reconstructs the lock.

Targeted output is authoring information, not release evidence. Before release,
run full-package `build-certs --check`, full refresh parity, source-free
reference verification, the artifact-ledger audit, and the repository's
generated-artifact gates. Full selection remains the behavior when neither
selector is present.

Refresh renders canonical `npa-ai-proof-meta-v0.1` standard fields from the
verified rebuilt certificate while preserving valid unknown top-level
extension members. Import-set and import-identity drift is reported before a
generic certificate-file mismatch when the compared certificate is decodable.

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

## Programmatic use

Adjacent Rust consumers should construct requests through
`npa_cli::package_api::v1::audit_artifact_ledger_all` or
`audit_artifact_ledger_modules` and pass them to
`run_package_artifact_ledger_audit`. Raw option-struct literals remain outside
the supported compatibility boundary.

## External checker closure

The current Linux closure gate is:

```sh
npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.6.sh
npa-core/checkers/npa-checker-ext/scripts/toolchain-v0.6.sh --functional-only
```

It binds the `npa-cli 0.6.x` host and `package_api::v1` facade to the unchanged
external checker and certificate/core axes. The `--functional-only` form is a
developer gate, not release evidence. The v0.5 script and reference remain
historical compatibility evidence; the v0.6 script is the only current-host
closure lane.
