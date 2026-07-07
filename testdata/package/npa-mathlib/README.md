# npa-mathlib Fixture

Visibility: public example fixture.

This fixture models the first public `npa-mathlib` theorem-library package.
It is derived from the earlier seed fixture's Layer 0 modules, but uses the
public `Mathlib.*` namespace and package name `npa-mathlib`.

The fixture is reference-checker-only. Source, replay, metadata, generated
theorem indexes, publish metadata, command status, and future registry metadata
are not proof evidence. Proof acceptance comes from canonical certificate
artifacts and local source-free checker verification.

Layer 0 modules:

- `Mathlib.Logic.Basic`
- `Mathlib.Logic.Prop`
- `Mathlib.Logic.Eq`
- `Mathlib.Data.Nat.Basic`
- `Mathlib.Core.Reduction`

The only external imports are hash-pinned `npa-std` certificate artifacts:

- `Std.Logic.Eq`
- `Std.Nat.Basic`

These vendored certificates are pinned to the `npa-std v0.1.0` release bundle:

- Release:
  <https://github.com/finitefield-org/npa-std/releases/tag/v0.1.0>
- Bundle:
  `npa-std-v0.1.0-release-artifacts.tar.gz`
- Bundle SHA-256:
  `3ed967d1870f97f7042e87a75efebd3cf553e8c86d8959c720080115a78fe85c`
- `Std.Logic.Eq` certificate file SHA-256:
  `7aa25a1adf44de35cdaaa514484c1220fec0e543d3f65803805b5e6efc5b36a1`
- `Std.Nat.Basic` certificate file SHA-256:
  `d057dbc0e3c1e21649968eeaf882616602cfeb1f1cbb8393031c2010ea9596fb`

Baseline checks from the repository root:

```sh
cargo run -q -p npa-cli -- package check --root testdata/package/npa-mathlib --json
cargo run -q -p npa-cli -- package build-certs --root testdata/package/npa-mathlib --check --json
cargo run -q -p npa-cli -- package verify-certs --root testdata/package/npa-mathlib --checker reference --json
cargo run -q -p npa-cli -- package check-hashes --root testdata/package/npa-mathlib --json
cargo run -q -p npa-cli -- package axiom-report --root testdata/package/npa-mathlib --check --json
cargo run -q -p npa-cli -- package index --root testdata/package/npa-mathlib --check --json
cargo run -q -p npa-cli -- package publish-plan --root testdata/package/npa-mathlib --check --json
```
