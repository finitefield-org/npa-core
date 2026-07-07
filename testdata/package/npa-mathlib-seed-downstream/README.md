# npa-mathlib-seed downstream fixture

Visibility: internal test fixture note.

This fixture is retained to regression-test downstream consumption of the
historical `npa-mathlib-seed` artifact set. It is not the public downstream
package example; use `testdata/package/npa-mathlib-downstream/` for that path.

This fixture models a downstream package that consumes the local
`npa-mathlib-seed` release artifact set without a registry server.

Consumed seed release artifact:

- release metadata: `../npa-mathlib-seed/generated/publish-plan.json`
- downstream import bundle module: `Proofs.Ai.Basic`
- source-free proof artifact:
  `../npa-mathlib-seed/Proofs/Ai/Basic/certificate.npcert`

The fixture vendors only that certificate artifact under
`vendor/npa-mathlib-seed/Proofs/Ai/Basic/certificate.npcert`. The import in
`npa-package.toml` is pinned to the package name, package version, export hash,
and certificate hash from the publish plan's `downstream_import_bundle`. Tests
also check the certificate file hash from the same bundle before accepting the
vendored artifact.

Seed source files, replay files, meta files, theorem indexes, and registry
state are not proof evidence for this fixture. They are deliberately absent
from the vendored dependency tree; source-free verification reads only the
hash-pinned certificate bytes and the downstream package certificate.

The local theorem `Downstream.SeedBasic::seed_id_passthrough` imports
`Proofs.Ai.Basic` and applies the exported seed theorem `id`.
