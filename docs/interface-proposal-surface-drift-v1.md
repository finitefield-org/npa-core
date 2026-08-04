# Interface Proposal Surface-Drift Contract v1

Status: implemented by UIA-15/UIA-16; v1 contract frozen on 2026-08-02.

This document defines the read-only comparison between one adopted interface
proposal revision and one prepared target package module. It is a curation and
implementation-handoff gate. Its result is always non-proof metadata with
`proof_evidence = false`; it does not verify a theorem, establish catalog
maturity, grant L2 acceptance, or replace the certificate/package gates.

## Command choice and boundary

Surface drift uses a separate package subcommand so the existing
`package check-interface-proposals` parser, proposal-set snapshot semantics,
and JSON schema remain backward compatible. The new command reuses the
existing `CommandResult` boundary and frontend/package APIs but has its own
surface-drift schema and target selection.

The command is:

```sh
npa package check-interface-proposal-surface \
  --root PATH \
  --proposal-root PATH \
  --proposal-path Mathlib/Logic/Function/Basic.toml \
  --proposal-sha256 sha256:<64 lowercase hexadecimal characters> \
  --target-module Mathlib.Logic.Function.Basic \
  --json
```

It is read-only, local-only, network-free, Git-free, and does not invoke a
writer. It reads only the selected proposal and the target package artifact
closure described below. It never scans an entire proposal set, changes
`interface_status`, edits source or certificates, or creates a generated
projection.

### Frozen parser and help contract

The command accepts each option at most once. Both `--option VALUE` and
`--option=VALUE` forms are accepted; a duplicate, missing value, unknown
option, or positional argument is a usage error. `--help` prints the exact
usage and boundary statement and performs no filesystem read.

| Option | Required/default | Contract |
| --- | --- | --- |
| `--root PATH` | Optional; default `.` | Package root. The resolved directory itself and every selected artifact path must be confined, non-symlink, and regular where a file is required. |
| `--proposal-root PATH` | Optional; default `interface-proposals` | Package-root-relative canonical proposal root. It is not a scan of the proposal set. |
| `--proposal-path PATH` | Required | Relative to `--proposal-root`; valid UTF-8, `/` separators, no absolute path, no `.`/`..` component, no symlink, under `Mathlib/`, and ending in `.toml`. |
| `--proposal-sha256 HASH` | Required | Exact `sha256:` plus 64 lowercase hexadecimal characters. The hash is over the exact selected proposal bytes before parsing. |
| `--target-module MODULE` | Required | Exactly one canonical `Mathlib.*` module name. The module must occur exactly once in the validated package manifest. |
| `--json` | Required | Emits the v1 JSON payload below. Human output is not a second contract in v1. |

The command exits with `0` only for `status = "parity"`, `1` for
`status = "drift"` or `status = "invalid"`, and `2` for usage or unexpected
internal failure, matching the existing `CommandExitCode` classes.

## JSON result contract

The exact schema string is
`npa.mathlib.interface_proposal_surface_drift.v1`. JSON object keys are
emitted in this order:

```text
schema
proof_evidence
status
proposal_path
proposal_sha256
target
comparison
diagnostics
```

`status` is one of:

| Status | Meaning |
| --- | --- |
| `parity` | All target inputs are valid and every comparison axis is equal. `diagnostics` is empty. |
| `drift` | All required inputs are valid and comparison completed, but one or more axes differ. Every diagnostic is a designated drift reason. |
| `invalid` | A proposal, manifest, source, certificate, import, elaboration, or resource precondition failed. No parity or handoff claim is made. |

The exact top-level payload shape is:

```json
{
  "schema": "npa.mathlib.interface_proposal_surface_drift.v1",
  "proof_evidence": false,
  "status": "parity",
  "proposal_path": "Mathlib/Logic/Function/Basic.toml",
  "proposal_sha256": "sha256:<64 lowercase hexadecimal characters>",
  "target": {
    "module": "Mathlib.Logic.Function.Basic",
    "source": "Mathlib/Logic/Function/Basic/source.npa",
    "source_file_sha256": "sha256:<64 lowercase hexadecimal characters>",
    "certificate": "Mathlib/Logic/Function/Basic/certificate.npcert",
    "certificate_file_sha256": "sha256:<64 lowercase hexadecimal characters>",
    "certificate_sha256": "sha256:<64 lowercase hexadecimal characters>",
    "export_sha256": "sha256:<64 lowercase hexadecimal characters>"
  },
  "comparison": {
    "module_name": "equal",
    "direct_imports": "equal",
    "declaration_order": "equal",
    "declaration_names": "equal",
    "declaration_kinds": "equal",
    "declaration_surfaces": "equal",
    "signatures": "equal",
    "definition_bodies": "equal",
    "inductive_family_members": "equal",
    "exported_support_closure": "equal"
  },
  "diagnostics": []
}
```

Every `target` scalar is `null` when that identity was not available because an
earlier input failed. Every comparison value is one of `equal`, `drift`, or
`not_checked`. The exact diagnostic object key order is:

```json
{
  "category": "drift",
  "reason": "signature_drift",
  "path": "declarations[1].signature",
  "field": "signature",
  "expected": "sha256:<64 lowercase hexadecimal characters>",
  "actual": "sha256:<64 lowercase hexadecimal characters>"
}
```

`path`, `field`, `expected`, and `actual` are nullable strings. Rendered values
are sanitized, contain no absolute filesystem path, and are capped at 256
UTF-8 bytes. Long exact core terms are rendered as their lowercase
`sha256:<64 hex>` digest; comparison still uses the complete canonical bytes.
Diagnostics are sorted by category, reason, path, field, expected, and actual,
with null before non-null, and capped at 1024 entries. A cap emits one final
`resource/diagnostic_count_exceeded` diagnostic.

## Target input authority and read set

The command resolves `--root/npa-package.toml` through the existing package
manifest parser and validator. It selects one `PackageModule` by exact
`--target-module` equality. The manifest is metadata and a freshness binding;
it is not proof evidence.

For the selected module, the command reads exactly:

1. the selected proposal TOML under `proposal-root`;
2. `npa-package.toml`;
3. the selected module's declared source file;
4. the selected module's declared certificate file;
5. each direct and transitive package certificate required by the manifest's
   hash-pinned module/import graph; and
6. deterministic imported source-interface metadata needed by the Human
   frontend, constructed through the existing certificate-bound resolver
   reconciliation/fallback from those exact prepared certificate artifacts;
   no imported source file is read for this metadata.

It does not read Git history, remote URLs, upstream source repositories,
proposal siblings, arbitrary files in the package root, replay/meta files,
generated indexes, promotion registries, L2 records, or unrelated authoring
sidecars. `meta` and `replay` paths in a manifest are not part of the v1 read
set.

### Freshness and authority rules

The following checks are preconditions. A failure is `status = "invalid"`, not
surface drift:

| Input | Required check | Failure behavior |
| --- | --- | --- |
| Proposal | Read exact bytes, verify `--proposal-sha256`, parse and validate the v1 proposal, require `interface_status = "adopted"` and `proof_evidence = false`, and require `proposal.module = --target-module`. | Stop comparison with `proposal_*` diagnostic. The proposal is not edited. |
| Manifest | Read exact UTF-8 bytes, validate the closed manifest schema and package graph, and find one target module. | Missing/invalid/ambiguous manifest or module is `manifest_*`/`target_module_*`; no comparison. |
| Source | Resolve the manifest's package-relative source path without symlinks or escapes, read UTF-8 bytes within the limit, and require the exact manifest `expected_source_hash`. | Missing, unsafe, malformed, or stale source is `target_source_*`; no comparison. Source text is a freshness/input-boundary check, never proof evidence. |
| Certificate | Resolve the manifest's package-relative certificate path without symlinks or escapes, read within the certificate limit, decode it, and require its module, certificate hash, and export hash to match the manifest identity. | Missing, unsafe, undecodable, or stale certificate is `target_certificate_*`; no comparison. |
| Imports | Resolve every direct/transitive import from the validated manifest/package graph and require the declared module, export hash, certificate-file hash, and certificate hash to match the prepared artifact. | Missing or stale import is `import_*`; no comparison. No floating or remote import is accepted. |
| Prepared core | Use the existing source-free certificate verification API with the exact verified import closure to obtain target core declarations. | A verifier/decode failure is `target_certificate_verification_failed`; this command still emits `proof_evidence = false` and does not publish the verifier result. |

The certificate is the target-core authority after those identity checks. The
source is not substituted for a certificate, and a source file that happens to
parse cannot make a stale certificate current. Existing certificate verification
may be used to prepare the in-memory target core, but surface-drift output is
not a verifier verdict and does not widen the trusted kernel base.

## Canonical comparison model

Comparison is performed on structured core data, not source spelling or raw
Human notation. Proposal declaration and import array order is meaningful and
preserved. Target declaration order is the canonical certificate declaration
order; target direct-import order is the manifest/certificate order after the
manifest and certificate have been checked for identity agreement.

### Human proposal elaboration

For each adopted proposal, the checker:

1. parses each `signature` and adopted definition `body` with the existing
   Human frontend parser;
2. resolves names using only the selected target module's exact verified
   direct-import interfaces and their hash-bound source-interface metadata;
3. elaborates the proposal's signatures and definition bodies to an in-memory
   `npa_cert::CoreModule` using the existing Human-to-core API; and
4. represents theorem declarations with an in-memory surface-only axiom stub
   solely to elaborate their type. The stub is never written, certified,
   compared as a proof, or included in output. Theorem proof terms are not an
   adopted interface term and are intentionally ignored for body comparison.

An elaboration failure is invalid (`proposal_signature_*` or
`proposal_definition_*`), not drift. Proposal terms remain untrusted input;
the checker does not call them proof evidence.

### Canonical module and declaration records

The comparison uses these fields in the stated order. All names are canonical
UTF-8 dotted identifiers. Core terms are encoded as the lowercase hexadecimal
bytes returned by `npa_cert::core_expr_canonical_bytes`; their corresponding
hash is used only for bounded diagnostics. Binder names and source spans are
not included; de Bruijn binders, universe parameters, universe constraints,
and global identities are included.

| Record | Canonical fields |
| --- | --- |
| Module | `module_name` |
| Direct import | `ordinal`, `module_name`, `export_sha256`, `certificate_sha256` |
| Declaration | `ordinal`, `name`, `kind`, `surface`, `universe_parameters`, `universe_constraints`, `type_core_hex`, `body_core_hex_or_null`, `reducibility_or_opacity` |
| Inductive family member | `ordinal`, `owner`, `name`, `kind`, `parent`, `decl_interface_sha256`, `type_core_hex_or_null` |
| Support-closure member | `ordinal`, `name`, `kind`, `surface`, `parent`, `decl_interface_sha256`, `dependency_ordinals` |

`kind` is one of `axiom`, `definition`, `theorem`, `inductive`,
`constructor`, or `recursor`. Proposal `definition`, `theorem`, and
`inductive` kinds map to the corresponding target core/export kinds; an
`axiom` target is not accepted as a substitute for an adopted theorem or
definition. `surface` is `public` for an adopted root and `support` for a
same-module support declaration. Generated constructors and recursors are
family members, not silently added proposal roots.

Signatures compare the complete canonical type representation, including
universe parameters and constraints, not only a statement hash or declaration
name. Definition bodies compare the complete canonical core expression bytes;
an absent target body differs from an adopted definition body. Theorem proof
bodies are excluded because the adopted proposal fixes their exported type,
not an implementation proof term.

### Axis rules

The command computes every applicable axis and emits all bounded mismatches in
deterministic order:

| Axis | Equal rule | Drift rule |
| --- | --- | --- |
| Module name | Proposal `module` equals target certificate module. | Any difference is `module_name_drift`. |
| Direct imports | Ordered proposal imports equal ordered target module imports, including hash-bound import identities. | Any addition, removal, reorder, or identity change is `direct_imports_drift`. |
| Declaration order | The adopted declaration sequence maps to the target declaration sequence in the same order. | Any ordinal change is `declaration_order_drift`. |
| Declaration names | Every mapped declaration has the exact canonical name. | Addition, removal, or rename is `declaration_name_drift`. |
| Declaration kinds | Definition/theorem/inductive kind and generated family kind agree. | Any kind change is `declaration_kind_drift`. |
| Declaration surfaces | Public roots and support declarations have the exact public/support boundary. | Any public/support change is `declaration_surface_drift`. |
| Signatures | Complete canonical type, universe parameter, and constraint records match byte-for-byte. | Any difference is `signature_drift`. |
| Definition bodies | Complete canonical definition-body core bytes and reducibility metadata match. | Any difference or missing body is `definition_body_drift`. |
| Inductive family members | The complete ordered member identity list, member kinds, parents, interface hashes, and available member core types match. | Any addition, removal, reorder, or member-term difference is `inductive_family_drift`. |
| Exported support closure | Recursive same-module dependencies and generated exports reachable from every adopted root match exactly, with no extra exported support. | Extra, missing, reordered, or differently owned support is `exported_support_added`, `exported_support_removed`, or `support_closure_drift`. |

The proposal's `depends_on` graph is the expected support-closure seed. The
target closure follows canonical certificate declaration dependencies and
complete generated families. A target declaration newly exported for proof
convenience is therefore an observable drift, even when all adopted root names
and statement types remain unchanged.

## Stable diagnostic contract

All diagnostics use the existing command-result error boundary and the
following lower-case categories and reasons. No implementation may invent a
new v1 reason code.

### Input and proposal reasons

| Category | Reason |
| --- | --- |
| `input` | `invalid_proposal_path`, `proposal_path_escape`, `proposal_path_symlink`, `proposal_missing`, `proposal_hash_invalid`, `proposal_hash_mismatch`, `proposal_parse_invalid`, `proposal_status_not_adopted`, `proposal_proof_evidence_not_false`, `proposal_module_mismatch`, `target_module_invalid`, `target_module_missing`, `target_module_ambiguous` |

### Target and import reasons

| Category | Reason |
| --- | --- |
| `target` | `manifest_missing`, `manifest_invalid`, `target_source_missing`, `target_source_not_regular`, `target_source_symlink`, `target_source_path_escape`, `target_source_invalid_utf8`, `target_source_hash_mismatch`, `target_certificate_missing`, `target_certificate_not_regular`, `target_certificate_symlink`, `target_certificate_path_escape`, `target_certificate_decode_failed`, `target_certificate_file_hash_mismatch`, `target_certificate_identity_mismatch`, `target_certificate_verification_failed`, `target_manifest_hash_mismatch`, `import_missing`, `import_hash_mismatch`, `import_certificate_missing`, `import_certificate_file_hash_mismatch`, `import_certificate_identity_mismatch`, `import_source_interface_missing` |

### Elaboration and comparison reasons

| Category | Reason |
| --- | --- |
| `elaboration` | `proposal_signature_parse_failed`, `proposal_signature_elaboration_failed`, `proposal_definition_parse_failed`, `proposal_definition_elaboration_failed`, `proposal_family_invalid`, `target_core_normalization_failed`, `target_family_invalid` |
| `drift` | `module_name_drift`, `direct_imports_drift`, `declaration_order_drift`, `declaration_name_drift`, `declaration_kind_drift`, `declaration_surface_drift`, `signature_drift`, `definition_body_drift`, `inductive_family_drift`, `exported_support_added`, `exported_support_removed`, `support_closure_drift` |

### Resource reasons

| Category | Reason |
| --- | --- |
| `resource` | `proposal_bytes_exceeded`, `manifest_bytes_exceeded`, `source_bytes_exceeded`, `certificate_bytes_exceeded`, `direct_import_count_exceeded`, `declaration_count_exceeded`, `family_member_count_exceeded`, `support_closure_count_exceeded`, `diagnostic_count_exceeded` |

Input, target, elaboration, and resource reasons produce `invalid`. Drift
reasons produce `drift`. A single run may report several drift reasons, but a
precondition failure prevents comparison diagnostics from being emitted.

## Resource limits and allocation order

All limits count bytes or entries before cloning nested values. The limits are
fixed for v1:

| Limit | Value | Scope |
| --- | ---: | --- |
| `max_proposal_bytes` | `262144` | Exact selected TOML bytes |
| `max_manifest_bytes` | `262144` | Exact `npa-package.toml` bytes |
| `max_source_bytes` | `16777216` | Selected target source bytes |
| `max_certificate_bytes` | `67108864` | One certificate file; matches `npa_cert::MAX_CERTIFICATE_BYTES` |
| `max_direct_imports` | `4096` | Target certificate/import closure direct entries |
| `max_declarations` | `262144` | One target certificate declaration table; matches certificate structural limits |
| `max_family_members` | `262144` | All generated family members in one target module |
| `max_support_closure` | `262144` | Unique target support-closure members |
| `max_diagnostics` | `1024` | One command result |
| `max_diagnostic_value_bytes` | `256` | Each rendered diagnostic string |
| `max_path_bytes` | `1024` | Each package/proposal-relative path |
| `max_identifier_bytes` | `1024` | Each module/declaration identifier |
| `max_core_term_bytes` | `67108864` | One complete canonical core-term representation before digest-only rendering |

The command validates the scalar/path limits, then reads one bounded file at a
time, then decodes the bounded certificate, then allocates declaration/family
and closure vectors. It never follows a symlink, allocates from a file length
before checking the corresponding bound, or reads an unrelated directory tree.

## Missing, stale, and malformed artifact behavior

The command is fail-closed. Missing, malformed, or stale target inputs are not
interpreted as empty surfaces and cannot be reported as parity or drift:

- A missing manifest, missing source, missing certificate, or missing imported
  certificate returns `invalid` with its designated `*_missing` reason.
- A source/certificate/manifest/import hash mismatch returns `invalid` with the
  corresponding stale/hash reason. The command never repairs hashes.
- A malformed manifest, source UTF-8 stream, certificate, or imported source
  interface returns `invalid`; no partial target is compared.
- A missing or hash-inconsistent import interface returns `invalid`; no
  transitive import is inferred from names or fetched remotely.
- A missing proposal, wrong proposal hash, non-adopted status, or module mismatch
  returns `invalid`; the proposal is not rewritten to `proposed` by the tool.
- If comparison completes and finds drift, the result is `drift`. The human
  curation decision is that the handoff is blocked and the proposal must return
  to `proposed` through a separately reviewed proposal revision. The checker
  only reports this fact and never edits either side.

## Trust and non-mutation statement

The command compares untrusted proposal metadata and prepared package terms.
Human syntax, elaboration, source interfaces, hashes, JSON, and drift results
are all outside the trusted proof base. Existing certificate verification and
the Rust kernel remain the authorities for certificate correctness. A parity
result means only that the selected metadata and prepared target surface match
under this contract; it is not proof evidence, a maturity claim, an adoption
decision, or a release authorization.

The checker never edits the proposal, target source, certificate, manifest,
package lock, generated projection, registry, or route. It returns a nonzero
package-validation exit for drift or invalid input and leaves the next human or
authorized workflow to create a new proposal revision or proceed through the
existing certificate-first gates.

## UIA-16 implementation checklist

UIA-16 is implementation-complete only when it can use this document without
choosing new semantics:

- [ ] Add the exact parser/help contract for
      `check-interface-proposal-surface`.
- [ ] Bind one proposal path to one exact proposal hash and target module.
- [ ] Enforce the complete read set, freshness checks, and fail-closed reasons.
- [ ] Implement all ten comparison axes, including exact definition bodies,
      complete inductive families, and exported support closure.
- [ ] Render the exact JSON key order, statuses, nullable target identity,
      comparison fields, bounded diagnostics, and `proof_evidence = false`.
- [ ] Add exact parity plus negative fixtures for module, imports, order,
      names, kinds, surfaces, signatures, bodies, families, and support
      additions/removals.
- [ ] Assert that repeated runs are byte-identical and that neither proposal
      nor target files are written.
