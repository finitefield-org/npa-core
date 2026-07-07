# Generated Package Artifacts

Visibility: internal generated-artifact fixture note.

This directory documents generated metadata checked into the local
`npa-mathlib-seed` regression fixture. It is not public package-author
guidance, and these files are not proof evidence.

CLR-09-03 checks in deterministic package artifacts produced by the package
commands:

- `package-lock.json`
- `axiom-report.json`
- `theorem-index.json`
- `publish-plan.json`

These files let a fresh checkout run the base command sequence in check mode.
They remain generated metadata, not trusted proof evidence.

`publish-plan.json` is the CLR-09-05 release handoff artifact. Its
downstream_import_bundle has one entry for each exported seed module and
includes exported declaration identifiers, export hash, certificate hash,
certificate path, certificate file hash, and source-free checker summaries.

The base seed release is reference-checker-only for proof acceptance. It does
not claim external-checker evidence and does not include a
`verified_high_trust` artifact because no CLR-08 high-trust inputs are supplied.
