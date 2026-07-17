# Security Certificate Fixtures

## `inductive-constructor-universe-bound-v0.1.npcert`

This is a deliberately invalid, axiom-free certificate used to test the
inductive constructor universe bound. Rejection is the expected result.

```text
format:           NPA-CERT-0.1
core spec:        NPA-Core-0.1
module:           Audit.Universe
file size:        1129 bytes
SHA-256:          8f446714cf1a8842aea3f20e86bbc6a112045824987f586e5c5c94f41425a38d
module axioms:     empty
invalid field:    Audit.Code.mk field 0
field obligation: 2 <= 1
```

The module declares `Audit.Code : Sort 1` with constructor
`Audit.Code.mk : Sort 1 -> Audit.Code`, then uses the generated recursor to
define `Audit.Universe.El : Audit.Code -> Sort 1` with the computation rule
`El (mk A) = A`. The field type `Sort 1` itself inhabits `Sort 2`, which is
above the inductive family's declared `Sort 1`.

The legacy unconstrained encoding is intentional: it is the common format
accepted by the Rust verifier, Rust reference checker, and the current OCaml
external-checker semantic substrate. Its internal export, axiom-report, and
certificate hashes are valid under the legacy hash domains.

The fixture was generated before enforcing the bound by building the full
module with `build_module_cert`, applying the
`legacy_bytes_from_current_cert` test helper pattern in
`crates/npa-cert/src/tests.rs`, recomputing the legacy hashes, and confirming
that the pre-fix Rust high-trust verifier accepted it with an empty axiom
report. The one-off file-writing helper was removed after these bytes were
frozen.

Keep this file as ordinary Git content. Do not move it to Git LFS or use it as
a package dependency.

## `mutual-inductive-constructor-universe-bound-v0.2.npcert`

This smaller, current-format certificate freezes the same invalid constructor
inside a mutual block so the independent reference checker exercises its
mutual-constructor path.

```text
format:           NPA-CERT-0.2.0
core spec:        NPA-Core-0.2.0
module:           Audit.Mutual
file size:        937 bytes
SHA-256:          6d94ac08cc7146e4c5b9e3bd3b8aa60698a3f27a72531ab58dadcac0a607138a
module axioms:     empty
invalid field:    Audit.Mutual.Code.mk field 0
field obligation: 2 <= 1
```

The block also contains a valid `Audit.Mutual.Unit` member. This makes the
fixture an atomicity regression: rejection of the invalid `Code` member must
prevent every family and generated constructor in the block from being
installed. The fixture was generated with the pre-fix `build_module_cert` and
then frozen; the one-off generator was removed.

Keep this file as ordinary Git content. Do not move it to Git LFS or use it as
a package dependency.
