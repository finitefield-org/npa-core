# NPA Toolchain Reference v0.2.0

This is the current SRA-02-compatible toolchain reference for external theorem
package repositories. External package authors should use this ref for the
current `npa-std` standalone package path.

## Current Stable Ref

Use the Git tag:

```text
v0.2.0
```

External theorem repositories should set exactly one pinned `npa` source. The
recommended SRA-02-compatible setting is:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

`NPA_GIT_COMMIT` is also supported when a repository wants to pin the full
40-hex commit SHA instead of a tag. `NPA_BINARY_PATH` remains supported for
runner-local binary provisioning. `NPA_VERSION` is reserved for a later
release-download mode and is not a valid current package-command pin.

## SRA-02 Compatibility

This ref includes the `std-library-legacy-core-builder` producer profile used
by the first `npa-std` package fixture. The local `npa-core` regression fixture
is checked in at `testdata/package/npa-std` and can be rebuilt and checked
without registry or network package resolution.

The previous `v0.1.1` ref remains a historical SRA-02-compatible toolchain
reference, but it is no longer the current package-author pin.

Do not use `v0.1.1` as the current external package pin for SRA-02-compatible
package fixtures.

## Package Commands

The reference-checker PR gate uses:

```sh
npa package check --root . --json
npa package build-certs --root . --check --json
npa package check-hashes --root . --json
npa package verify-certs --root . --checker reference --json
npa package axiom-report --root . --check --json
npa package index --root . --check --json
```

### Package Artifact Refresh

When an intentional local source change alters local certificate identities,
use refresh mode instead of editing manifest hashes by hand. A dry run rebuilds
local certificates in memory, refreshes the local module hash pins in memory,
regenerates the package lock in memory, writes no files, and fails if any
checked artifact would change:

```sh
npa package build-certs --root . --update-manifest-hashes --check --json
```

Write mode performs the same rebuild and, after the whole refresh succeeds,
updates only local module certificate files, the local module hash fields in
`npa-package.toml`, and `generated/package-lock.json`:

```sh
npa package build-certs --root . --update-manifest-hashes --json
npa package check-hashes --root . --json
npa package verify-certs --root . --checker reference --json
```

After a write refresh, regenerate or check any release metadata your package
tracks, such as `axiom-report`, `index`, `export-summary`, or `publish-plan`,
using the existing package metadata commands.

Use write mode only at explicit package artifact refresh boundaries. Refresh
mode is metadata and artifact maintenance; it is not proof evidence. Source
files, refreshed manifest pins, generated JSON, and command success remain
untrusted. Proof acceptance still depends on canonical `.npcert` bytes and
source-free checker or kernel verification.

Refresh mode does not update top-level external `[[imports]]` pins. External
`export_hash` and `certificate_hash` mismatches remain hard failures; updating
external package pins is future work and must be handled outside this command.
`package lock write` remains a source-free lock rewrite from the current
manifest and certificate artifacts, and ordinary `build-certs`,
`build-certs --check`, `check-hashes`, and `verify-certs` behavior is unchanged
when `--update-manifest-hashes` is absent.

Refresh mode is incompatible with `--build-check-cache read-through`.

For local certificate-only edits after certificates have already been generated,
`verify-certs --changed` selects changed checked-in certificate paths from Git
and verifies only those package modules, plus source-free imports required for a
sound import context:

```sh
npa package verify-certs --root . --changed --checker reference --json
```

This path does not invoke `build-certs` and does not read source, replay, meta,
theorem-index, AI trace, registry, or checker-result sidecars. It requires the
package lock to remain consistent with checked-in certificate bytes.

The base release gate additionally records:

```sh
npa package verify-certs --root . --checker fast --json
```

`publish-plan` remains release metadata and is enabled by setting
`NPA_ENABLE_PUBLISH_PLAN=true` when `generated/publish-plan.json` is checked in:

```sh
npa package publish-plan --root . --check --json
```

For advisory refactor planning, use `refactor-plan` after package metadata has
been generated:

```sh
npa package refactor-plan --root . --scope modules --top 20 --json
npa package refactor-plan --root . --scope theorems --module Proofs.Ai.Basic --json
```

`refactor-plan` ranks local package-lock modules, and optionally theorem-family
clusters, using package metadata only. Default mode is source-free: it reads
`npa-package.toml`, `generated/package-lock.json`, optional
`generated/theorem-index.json`, and certificate file metadata for byte length.
It does not read source files, replay files, meta files, tactic traces, AI
traces, checker-result sidecars, registry data, or network data.

The command is planning metadata only. It emits standard
`npa.package.command_result.v0.1` diagnostics with `proof_evidence=false`; it
does not emit command-specific JSON payloads or `CommandArtifact` entries.
Theorem-family output is based on family and statement-constant signals from
the theorem index. It does not claim exact theorem proof dependents. Source
metrics, a certificate-derived dependency index, recommendation filters, score
thresholds, and markdown issue output are future work, not current CLI
behavior.

## Package Theorem Index Annotations

`generated/theorem-index.json` uses the
`npa.package.theorem_index.v0.1` schema and the
`npa.package.theorem_index.v0.1.certificate_derived` index profile. In this
profile, theorem identities, statement projections, axiom dependencies, checker
summaries, and artifact locators are source-free package metadata. They are
deterministic sidecar data, not proof evidence.

For theorem roles that help search, ranking, documentation, or AI premise
selection, use the existing entry-local `entries[].tags` array before adding a
new top-level structure. Examples include classifying an abstract law-package
fact that merely projects a bundled component:

```json
{
  "global_ref": {
    "module": "Mathlib.Algebra.Field.Basic",
    "name": "field_inv_mul_cancel"
  },
  "kind": "theorem",
  "tags": ["abstract-law-package", "field", "law-package-projection"]
}
```

Use `law-package-projection` for public theorems whose proof eliminates a packed
law argument and returns one of its fields/components. This tag should describe
the theorem's retrieval role; it must not be treated as proof evidence, a tactic
kind, or a reason to accept a proof.

Standard package-theorem-index tags should be short lower-case ASCII
kebab-case strings. Tags are entry-local, duplicate-free, and serialized in
canonical order. Adding, removing, or renaming tags changes
`theorem_index_hash`, but it must not change certificate bytes,
`certificate_hash`, `export_hash`, or source-free checker acceptance.

When richer information is needed, such as the exact packed argument
(`FieldLawArgs`) and component name (`inv_mul_cancel_law`), keep that information
in package or module metadata bound to the full theorem `global_ref`. The
current theorem-index profile should copy only stable retrieval tags into
`entries[].tags`.

Do not add a top-level structure such as `law_package_projections` to the
package theorem index merely to classify theorem roles. A dedicated top-level
structure is appropriate only for a future schema/profile that has a concrete
consumer requiring a complete typed listing, no duplicated source of truth, and
explicit validation against the corresponding `entries[]` identities. Such a
change must use a new theorem-index profile, and a schema change if new fields
are emitted.

## Trust Boundary

This reference is reference-checker-only. It does not produce
`verified_high_trust`.

Trusted proof evidence remains:

- canonical `.npcert` bytes
- Rust kernel / verifier verdict
- source-free reference checker verdict
- deterministic `export_hash`, `certificate_hash`, and `axiom_report_hash`

Untrusted helper data remains:

- source files
- replay and meta files
- theorem indexes
- publish plans
- refactor plans
- command status
- Git tags and release pages
- registry seed entries
- future registry or API responses

## Local Verification

The SRA-02-compatible local gate is:

```sh
cargo build -p npa-cli
cargo run -p npa-cli -- package check --root testdata/package/npa-std --json
cargo run -p npa-cli -- package build-certs --root testdata/package/npa-std --check --json
cargo run -p npa-cli -- package verify-certs --root testdata/package/npa-std --checker reference --json
cargo run -p npa-cli -- package check-hashes --root testdata/package/npa-std --json
cargo run -p npa-cli -- package axiom-report --root testdata/package/npa-std --check --json
cargo run -p npa-cli -- package index --root testdata/package/npa-std --check --json
cargo run -p npa-cli -- package publish-plan --root testdata/package/npa-std --check --json
cargo test -q -p npa-cli package_cli_args
./scripts/check-fast.sh
```
