# NPA v0.9.0 Release Notes

## Current release

The v0.9.0 release is the let-free current toolchain. It ships `npa-cli
0.9.0`, the rebuilt package ecosystem, and the exact certificate/core pair
`NPA-CERT-0.4.0` / `NPA-Core-0.4.0`. The Rust reference checker, OCaml
clean-room checker, package APIs, cache keys, diagnostics, and Lean exporter
bind their current behavior to these identities.

## Breaking source boundary

This release replaces the previous v0.8 source/API host at the boundary
between the final v0.8 checkpoint commit
`5d22858ffed16d75bcf01a61381abdb4040ae275` and the migrated source commit
`2b8078d6e629f12dadaf7c5b36586a8e4a7a4a0c`. Term-level `let` and its local
definition context are removed; packages must be regenerated rather than
header-relabeled. The standalone npa-core package sync used by the exporter is
`3726cc54278b95b3aa554e454de2b9f89dce9607`.

## Verification summary

The canonical writer rebuilt all active package closures. All 8,067 declared
certificates carry the exact v0.4 pair. Cache-disabled source-free reference
verification passed, including 2,107 Fermat modules; package locks, generated
indexes, export summaries, publish plans, and axiom reports were regenerated,
and the axiom inventory did not grow. The exporter workspace tests and direct
Lean 4.31.0 conformance suite passed.

## Retired identities and cleanup

The v0.7.0 and v0.8.0 toolchain references, scripts, facade examples, checker
host allowlists, compatibility tests, raw command transcripts, temporary
migration ledgers, and runnable links are retired. The former v0.7.0 remote tag
was re-resolved at `34b62dc0de4fed4cbf726627775bd62a9c8b0a20` before deletion;
no v0.8.0 tag or hosted release resolved. No retained document teaches or
invokes either retired host. Numeric v0.7/v0.8 strings that remain in this
repository are distinct measurement axes, version-scoped historical evidence,
or this non-executable cleanup record.

## Publication verification

The container's annotated `v0.9.0` tag object is
`83bd29b0d1786e92f20c9ea62d6cee06b606a69b` and peels to release commit
`f29b490a1564446871c09bd81bf7dd4940f8d45c`; its hosted release is
`RE_kwDOTPY1v84W2Oex`. The standalone `npa-core` v0.9.0 release is
`RE_kwDOTPfoj84W2OyB` at synchronized commit
`a47514e176e742b7b623108be2acda4f838449d5`. Both releases intentionally have
no binary assets because their source tags are the release artifacts. The
standalone v0.7.0 tag was re-resolved as
`34b62dc0de4fed4cbf726627775bd62a9c8b0a20` and its hosted release as
`RE_kwDOTPfoj84VT9eE`; both were then deleted with cleanup-tag. Exact remote
and hosted-release queries now find neither v0.7.0 nor v0.8.0. The v0.9.0
tags remain unchanged.
