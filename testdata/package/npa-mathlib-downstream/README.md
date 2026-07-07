# npa-mathlib downstream fixture

Visibility: public example fixture.

This fixture models a downstream package that consumes the local
`npa-mathlib` release artifact set without a registry server.

Consumed public release artifact:

- release metadata: `../npa-mathlib/generated/publish-plan.json`
- downstream import bundle module: `Mathlib.Logic.Basic`
- source-free proof artifact:
  `../npa-mathlib/Mathlib/Logic/Basic/certificate.npcert`

The fixture vendors only that certificate artifact under
`vendor/npa-mathlib/Mathlib/Logic/Basic/certificate.npcert`. The import in
`npa-package.toml` is pinned to the package name, package version, export hash,
and certificate hash from the publish plan's `downstream_import_bundle`. Tests
also check the certificate file hash from the same bundle before accepting the
vendored artifact.

Source files, replay files, meta files, theorem indexes, and registry
state are not proof evidence for this fixture. They are deliberately absent
from the vendored dependency tree; source-free verification reads only the
hash-pinned certificate bytes and the downstream package certificate.

The local theorem `Downstream.MathlibBasic::mathlib_id_passthrough` imports
`Mathlib.Logic.Basic` and applies the exported theorem `id`.
