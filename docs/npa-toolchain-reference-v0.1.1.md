# Historical NPA Toolchain Reference v0.1.1

This is the previous SRA-02-compatible toolchain reference for external theorem
package repositories. External package authors should use
`npa-toolchain-reference-v0.2.0.md` and Git tag `v0.2.0` as the current
toolchain pin.

## Historical Stable Ref

Use the Git tag:

```text
v0.1.1
```

External theorem repositories should set exactly one pinned `npa` source. The
historical SRA-02-compatible setting was:

```text
NPA_GIT_TAG = v0.1.1
RUST_TOOLCHAIN_VERSION = 1.95.0
```

`NPA_GIT_COMMIT` is also supported when a repository wants to pin the full
40-hex commit SHA instead of a tag. `NPA_BINARY_PATH` remains supported for
runner-local binary provisioning. `NPA_VERSION` is reserved for a later
release-download mode and is not a valid current package-command pin.

## Current Recommendation

External theorem package authors should use the current SRA-02-compatible ref:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

## SRA-02 Compatibility

This ref includes the `std-library-legacy-core-builder` producer profile used
by the first `npa-std` package fixture. The local `npa-core` regression fixture
is checked in at `testdata/package/npa-std` and can be rebuilt and checked
without registry or network package resolution.

The previous `v0.1.0` ref remains the original SRA-01 toolchain reference, but
it does not contain the SRA-02 `npa-std` fixture builder path and cannot pass
`package build-certs --check` for `testdata/package/npa-std`.

Do not use `v0.1.0` as the current external package pin for SRA-02-compatible
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

The base release gate additionally records:

```sh
npa package verify-certs --root . --checker fast --json
```

`publish-plan` remains release metadata and is enabled by setting
`NPA_ENABLE_PUBLISH_PLAN=true` when `generated/publish-plan.json` is checked in:

```sh
npa package publish-plan --root . --check --json
```

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
