# Historical NPA Toolchain Reference v0.1.0

This is the SRA-01 toolchain reference for external theorem package
repositories.

This ref is historical. Do not use it as the current package-author toolchain
pin. SRA-02-compatible `npa-std` standalone activation must use
`npa-toolchain-reference-v0.2.0.md` and Git tag `v0.2.0`.

## Current Recommendation

External theorem package authors should use the current SRA-02-compatible ref:

```text
NPA_GIT_TAG = v0.2.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

`v0.1.0` does not contain the SRA-02 `npa-std` fixture builder path and must
not be used to build or check the SRA-02 `testdata/package/npa-std` package
fixture.

## Historical Ref

The SRA-01 Git tag was:

```text
v0.1.0
```

For this historical SRA-01 reference, external theorem repositories set exactly
one pinned `npa` source. The SRA-01-only setting was:

```text
NPA_GIT_TAG = v0.1.0
RUST_TOOLCHAIN_VERSION = 1.95.0
```

`NPA_GIT_COMMIT` is also supported when a repository wants to pin the full
40-hex commit SHA instead of a tag. `NPA_BINARY_PATH` remains supported for
runner-local binary provisioning. `NPA_VERSION` is reserved for a later
release-download mode and is not a valid current package-command pin.

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

The SRA-01 local gate is:

```sh
cargo build -p npa-cli
cargo run -p npa-cli -- package check --root testdata/package/npa-mathlib --json
cargo test -q -p npa-cli package_cli_args
./scripts/check-fast.sh
```
