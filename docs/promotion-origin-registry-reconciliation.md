# Promotion-Origin Registry Reconciliation Command

Status: introduced in historical `npa-cli 0.7.x`, implemented in current
`npa-cli 0.8.x`; v1 contract frozen on 2026-08-02.

Date: 2026-07-28

## Goal

This document specifies the package command that keeps the promotion-origin
registry synchronized with frequent changes to the mutable `npa-mathlib`
catalog without rewriting released history:

```text
npa package reconcile-promotion-origin-registry
```

The command is a routine catalog-maintenance path as well as a recovery path
for releases that changed public target modules without recording a
promotion-origin transaction. It
must:

- prove that every existing registry row matches a supplied previous catalog
  snapshot;
- classify every difference between that snapshot and the current target;
- preserve all existing entries, reservations, revisions, and evidence;
- append hash-bound events for additions, revisions, renames, replacements,
  and retirements;
- migrate the registry to a schema that represents those events explicitly;
- validate the proposed registry and current target before any write; and
- replace the registry last in one recoverable, locked transaction.

The immediate migration is from the v0.2.1 legacy registry to the v0.2.4
catalog. It covers 44 unchanged or revised legacy reservations and creates
catalog-owned target entries for:

- `Mathlib.Algebra.Group.TwoElement`;
- `Mathlib.Algebra.Monoid.Power`; and
- `Mathlib.Algebra.OrderedField.Strict`.

The command is generic, reusable for later catalog versions, and must not
hard-code these versions or module names.

## Non-goals

This command does not:

- discover or infer source-package provenance;
- convert an unresolved legacy reservation into a sourced promotion entry;
- infer a rename, replacement, split, or merge without an explicit request;
- establish `reviewed` or `recommended` maturity;
- verify a theorem's mathematical meaning beyond the existing package gates;
- mutate source packages, proof artifacts, generated package projections, or
  released snapshots;
- reconstruct exact introduction versions or intermediate identities from
  skipped snapshots;
- invoke Git, fetch a tag, create a release, commit, or push; or
- replace the source-backed promotion materializer.

Ordinary source-backed promotion remains owned by the promotion materializer.
Direct catalog maintenance may use this command whenever its explicit
target-history contract is sufficient.

## Target preparation boundary

The caller prepares the proposed current catalog before running reconciliation,
using the ordinary package artifact tooling and without publishing it. The
command treats `--root` as that complete proposed target. It validates all
proof and generated identities but never creates, edits, deletes, or rolls back
module source, certificate, metadata, replay, manifest, or generated package
files.

Apply makes only the attestation and registry replacement recoverable. If apply
fails after the caller prepared target artifacts, those target changes remain
in place and the catalog remains unpublished and registry-invalid until the
printed recovery command succeeds or the caller independently restores the
prepared target.

## Command-line contract

```text
npa package reconcile-promotion-origin-registry \
  --root PATH \
  --previous-target-root PATH \
  --audit PATH \
  --out PATH \
  [--request PATH] \
  [--dry-run | --apply] \
  [--json]
```

`--dry-run` is the default. `--dry-run` and `--apply` are mutually exclusive.
All paths are explicit; the command must not consult Git or resolve a version
tag itself.

Recovery has a separate form:

```text
npa package reconcile-promotion-origin-registry \
  --root PATH \
  --recover PATH \
  [--json]
```

`--recover` is mutually exclusive with every normal-mode option other than
`--root` and `--json`.

### Arguments

`--root PATH`

: Current `npa-mathlib` package root. It contains the stale
  `promotion-origins.json` and is the only package the command may modify.

`--previous-target-root PATH`

: Read-only, clean package root containing the latest effective target snapshot
  represented by the input registry. It may be any older release and need not
  immediately precede the current target. Its package ID must match the
  registry and current target. It must not resolve to the same canonical
  directory as `--root`.

`--audit PATH`

: Existing UTF-8 Markdown audit, relative to `--root`, that explains why the
  catalog changes require reconciliation. It must be below
  `docs/promotion/`, must not be a symlink, and is read but not written by the
  command. Its file hash is stored in the reconciliation event.

`--out PATH`

: Target-relative path for the generated canonical reconciliation
  attestation. It must be below `docs/promotion/`, end in `.json`, differ from
  `--audit`, and must not name `promotion-origins.json`. Apply mode is
  create-or-identical: differing existing bytes fail closed.

`--request PATH`

: Optional target-relative canonical change request below `docs/promotion/`.
  It declares renames, replacements, splits, merges, or retirements that cannot
  be inferred safely from exact module-name comparison. Plain additions and
  in-place revisions need no request. A missing request is valid when the diff
  contains only additions and revisions.

`--recover PATH`

: Target-relative recovery journal printed by a failed apply. It must resolve
  below `target/registry-reconciliation/`, must not be a symlink, and must
  describe the same canonical target root.

Unknown, repeated singleton, missing-value, absolute governance-path, and
conflicting mode arguments are usage errors. Existing common `--root` and
`--json` behavior remains unchanged.

## Preconditions

The command accepts only this input state:

1. The input registry parses and self-validates as v1, v2, or v3.
2. The supplied previous target exactly matches every active target identity
   recorded by the registry.
3. Every active route matches exactly one module in the previous target,
   including source-file hash, certificate-file hash, certificate hash, export
   hash, axiom-report hash, and sorted theorem statement inventory. An
   unchanged identity's first-observed revision version may be older than the
   previous package version.
4. The previous target has no unowned local `Mathlib.*` module, except when
   migrating a pre-registry release under the v1 recovery case.
5. The current root passes checked generated-artifact loading, manifest
   validation, current hash checks, source/import resolution, and axiom policy
   checks. The immutable previous root passes checked generated-artifact
   loading, manifest validation, current hash checks, package-lock import
   resolution, axiom policy checks, and cache-off source-free reference
   verification. It is not rebuilt from historical authoring source: source
   text remains a hash-bound identity sidecar, so a stale legacy source-import
   list does not require rewriting the old snapshot before migration.
6. Both packages have ID `npa-mathlib`; the current version is strictly newer
   than the previous version. Any number of intermediate releases may be
   skipped.
7. Every removed or renamed module is covered exactly once by the optional
   request.
8. Every current local module remains in the `Mathlib.*` namespace and has
   canonical source, certificate, meta, and replay paths.
9. The audit exists and passes the confined governance-path rules.

A failure in any precondition produces no writes.

## Supported differences

The comparison is keyed by exact module name.

### Unchanged module

If all artifact and theorem identities equal the latest recorded revision,
preserve the owner's base row byte-for-byte and emit an `unchanged` comparison
row in the attestation. Do not append a duplicate revision.

`target_version` means the first registry-observed catalog snapshot binding
that exact target identity, not necessarily the historical release where the
identity first appeared. Registry
coverage validation therefore compares current artifact and theorem identities
with the latest effective revision and requires only
`revision.target_version <= package.version`. A later catalog-change event
binds the unchanged module's continued presence in its target projection.
Package-version advancement alone is never an identity mismatch and never
forces duplicate revisions.

When the previous and current projections differ only by package version and
every module identity is unchanged, reconciliation is a successful no-op. It
must preserve `promotion-origins.json` and its generation, must not append a
catalog-change event or create the attestation output, and must report that
the registry is unchanged after running the normal current/previous target
gates. Publication records the new package version in its release audit and
ledger; it does not manufacture a registry event for the version-only
snapshot.

When intermediate releases are skipped, one event proves only the two supplied
endpoints. It must not infer or claim which intermediate release introduced a
module or identity.

### Revised module

If the module exists in both packages but its current identity differs, append
one complete current target revision to the new catalog-change event. Do not
modify the existing legacy reservation or sourced entry. The old revisions,
owner ID, base lifecycle, source identities, and original evidence remain
unchanged.

The new revision version must equal the current target package version and be
strictly greater than the previous revision version. The complete current
theorem statement inventory is recorded. Declaration additions and removals
inside the same target module are allowed. For a sourced route, this records
target history only and does not assert that the new target is
artifact-identical to the unchanged source.

### Newly added module

If a current module is absent from the previous target and registry, add one
`catalog_target_v1` owner whose first revision is the current target identity,
unless a promotion plan already supplies a sourced registry entry. The stable
catalog-target ID is a domain-separated hash of the module and first unified
v3 target revision. Its evidence binds the audit and change-set hash; the
enclosing event binds the owner and reconciliation attestation.

Do not create new unresolved legacy reservations. That array is reserved for
historical target identities whose original source provenance is genuinely
unknown.

### Rename, split, merge, replacement, and retirement

These changes require a canonical
`npa.mathlib.catalog_registry_change_request.v1`. The request records:

- previous and current package versions;
- `kind`: `rename`, `split`, `merge`, `replacement`, or `retirement`;
- sorted old and new module names;
- the intended lifecycle transition;
- an explanation string;
- audit path and hash; and
- `proof_evidence: false`.

Canonical request shape:

```json
{
  "schema": "npa.mathlib.catalog_registry_change_request.v1",
  "previous_version": "0.2.4",
  "target_version": "0.3.0",
  "changes": [
    {
      "kind": "replacement",
      "old_modules": ["Mathlib.Old"],
      "new_modules": ["Mathlib.New"],
      "explanation": "Replace the old carrier with the meaning-first module."
    }
  ],
  "audit": {
    "path": "docs/promotion/v0.3.0-catalog-change.md",
    "file_hash": "sha256:..."
  },
  "request_hash": "sha256:...",
  "proof_evidence": false
}
```

Fields and array elements use the displayed order. `changes` is sorted by
`(kind, old_modules, new_modules)`; each module list is nonempty except
`retirement.new_modules`, which is empty. The request hash is
domain-separated and computed with `request_hash` zeroed.
The request audit path and hash must equal `--audit` and its current file hash.

Relation cardinalities are exact:

- `rename`: one old module and one new module;
- `replacement`: one old module and one new module;
- `split`: one old module and at least two new modules;
- `merge`: at least two old modules and one new module; and
- `retirement`: at least one old module and no new module.

The command validates that request rows partition all removed modules and do
not claim unchanged or unrelated modules. Old identifiers remain reserved.
Renames, splits, merges, and replacements append new `catalog_target_v1`
owners and retire the old routes with a relation to the new owner IDs.
Retirement records no replacement. The current catalog need not retain
compatibility aliases.

Sourced entries may receive target revisions or lifecycle events, but their
canonical and equivalent source identities remain immutable. A target revision
does not claim new source equivalence or higher maturity.

Lifecycle is monotonic per `(owner_id, target_module)` route. An effective
active route may become retired exactly once. A retired route cannot be
revised, reactivated, renamed again, or reused as a later relation endpoint.
Every non-retirement relation creates active new routes, and every old route
becomes retired at the target version. Other routes held by the same historical
whole-module owner remain active unless the event names them.

### Unsupported difference

Fail closed for:

- an existing reservation whose target module or first revision would change;
- an altered historical revision;
- package-ID changes;
- a current version not newer than the previous target;
- a removed module not covered by exactly one request row;
- a request relation that is cyclic or names an absent endpoint; or
- a change that would assign two active owners to one target module or artifact.

The diagnostic must identify the missing or conflicting request row. Resolving
source provenance still requires a separately versioned source-resolution
transaction.

## Registry v3

Introduce schema:

```text
npa.mathlib.promotion_origin_registry.v3
```

V3 preserves every v2 entry variant and unresolved legacy reservation. It adds
the `catalog_target_v1` entry variant and one top-level event array:

```json
{
  "catalog_change_events": []
}
```

The complete top-level order is:

```text
schema
registry_id
registry_version
generation
target_package
entries
unresolved_legacy_targets
catalog_change_events
registry_hash
proof_evidence
```

`registry_version` is `3`. The registry ID, target package, domain-separated
self-hash behavior, strict JSON rules, and `proof_evidence: false` boundary are
unchanged. Existing row fields remain immutable base history. Validators and
lookups compute effective lifecycle by applying the ordered change-event
overlay. V1/v2 entry and reservation revision arrays never change in v3.
Later target revisions live only in catalog-change events.

V3 entries remain strictly sorted by their stable owner ID across all variants,
and owner IDs are globally unique. Events are strictly sorted by target package
version and event ID, with at most one event per target version. Version
ordering uses the existing validated `PackageVersion` numeric tuple, never
lexical string ordering.

`catalog_target_v1` has this canonical payload:

```json
{
  "catalog_target_id": "sha256:...",
  "lifecycle": "active",
  "introduced_version": "0.2.4",
  "target_module": "Mathlib.Example",
  "first_revision": {
    "target_version": "0.2.4",
    "target_source_file_hash": "sha256:...",
    "target_meta_file_hash": "sha256:...",
    "target_replay_file_hash": "sha256:...",
    "target_certificate_file_hash": "sha256:...",
    "target_certificate_hash": "sha256:...",
    "target_export_hash": "sha256:...",
    "target_axiom_report_hash": "sha256:...",
    "theorems": []
  },
  "evidence": {
    "kind": "catalog_registry_sync_v1",
    "audit_path": "docs/promotion/example.md",
    "audit_file_hash": "sha256:...",
    "change_set_hash": "sha256:..."
  }
}
```

The owner ID derives from `target_module` and `first_revision`. Its base
lifecycle and first revision are immutable. Later revisions and lifecycle
relations are event overlays.

### Catalog change event v1

Each event has this canonical field order:

```json
{
  "event_id": "sha256:...",
  "kind": "catalog_registry_sync_v1",
  "input_registry_hash": "sha256:...",
  "change_set_hash": "sha256:...",
  "previous_target": {
    "package": "npa-mathlib",
    "version": "0.2.1",
    "manifest_file_hash": "sha256:...",
    "package_lock_file_hash": "sha256:...",
    "axiom_report_file_hash": "sha256:...",
    "theorem_index_file_hash": "sha256:...",
    "export_summary_file_hash": "sha256:...",
    "publish_plan_file_hash": "sha256:..."
  },
  "target": {
    "package": "npa-mathlib",
    "version": "0.2.4",
    "manifest_file_hash": "sha256:...",
    "package_lock_file_hash": "sha256:...",
    "axiom_report_file_hash": "sha256:...",
    "theorem_index_file_hash": "sha256:...",
    "export_summary_file_hash": "sha256:...",
    "publish_plan_file_hash": "sha256:..."
  },
  "audit": {
    "path": "docs/promotion/example.md",
    "file_hash": "sha256:..."
  },
  "request": {
    "path": "docs/promotion/example.change-request.json",
    "file_hash": "sha256:...",
    "request_hash": "sha256:..."
  },
  "attestation": {
    "path": "docs/promotion/example.reconciliation.json",
    "payload_hash": "sha256:..."
  },
  "revised_routes": [
    {
      "owner_kind": "legacy_reservation",
      "owner_id": "sha256:...",
      "target_module": "Mathlib.Example",
      "previous_revision_hash": "sha256:...",
      "target_revision": {
        "target_version": "0.2.4",
        "target_source_file_hash": "sha256:...",
        "target_meta_file_hash": "sha256:...",
        "target_replay_file_hash": "sha256:...",
        "target_certificate_file_hash": "sha256:...",
        "target_certificate_hash": "sha256:...",
        "target_export_hash": "sha256:...",
        "target_axiom_report_hash": "sha256:...",
        "theorems": [
          {
            "target_name": "example",
            "target_statement_hash": "sha256:..."
          }
        ]
      }
    }
  ],
  "added_targets": [
    {
      "owner_kind": "catalog_target_v1",
      "owner_id": "sha256:...",
      "target_module": "Mathlib.NewExample",
      "first_revision_hash": "sha256:..."
    }
  ],
  "lifecycle_changes": [
    {
      "kind": "replacement",
      "effective_version": "0.2.5",
      "old_routes": [
        {
          "owner_kind": "legacy_reservation",
          "owner_id": "sha256:...",
          "target_module": "Mathlib.OldExample"
        }
      ],
      "new_routes": [
        {
          "owner_kind": "catalog_target_v1",
          "owner_id": "sha256:...",
          "target_module": "Mathlib.NewExample"
        }
      ]
    }
  ]
}
```

Owner kind is `whole_module_v1`, `declaration_closure_v1`,
`catalog_target_v1`, or `legacy_reservation`. Arrays are sorted by
`(owner_kind, owner_id, target_module)`. The previous-target and target
projection hashes bind the checked generated files actually consumed by the
command.
Lifecycle rows are sorted by `(kind, old_routes, new_routes)`; their nested
route arrays use the owner sort order above. `retirement.new_routes` is empty.
`request` is `null` when the transition contains only additions and in-place
revisions.
`target_revision` is the unified v3 projection used for both legacy and sourced
owners. Its theorem rows are sorted by target name. `previous_revision_hash`
and `first_revision_hash` use a new domain-separated canonical hash of that
complete projection. For a v1 row that does not store meta/replay hashes, the
previous-target package supplies them before the hash is computed.

`change_set_hash` is a domain-separated hash of the input registry hash,
previous and target projections, audit, optional request, and all sorted
revision, addition, and lifecycle rows. It excludes the attestation, event ID,
and proposed registry hash. The attestation records the same change-set hash.
`payload_hash` hashes the attestation with its own `attestation_hash` field
zeroed. `event_id` is a domain-separated hash of every event field except
`event_id`, including `change_set_hash` and `payload_hash`. The registry
self-hash is computed last. Neither the event nor attestation contains the
proposed registry hash, so the hash graph is acyclic.

### Transition rules

Add:

```text
validate_promotion_origin_registry_v1_to_v3_reconciliation
validate_promotion_origin_registry_v2_to_v3_reconciliation
validate_promotion_origin_registry_v3
validate_promotion_origin_registry_v3_transition
```

The v1/v2-to-v3 validator requires:

- the applicable preconditions above;
- when the input is v1, its entries migrated losslessly using the existing
  v1-to-v2 wrapper;
- generation incremented exactly once;
- old entries and reservations preserved exactly;
- at most one revised-route event row per old active target module;
- new catalog-target entries only for modules absent from the previous target;
- when at least one revision, target owner, or lifecycle transition is
  present, exactly one change event describing all of them; and
- no other change.

Normal v3 transitions preserve all prior events byte-for-byte, increment the
generation once, preserve all old entries and reservations exactly except for
newly added catalog-target entries, and append exactly one event for the
requested older-to-newer version interval. Versions
must increase strictly, but need not be consecutive; one event may summarize
any number of skipped releases. Reconciliation may be run again for every
later target version. Existing v1 and v2 readers remain supported. Any tracked
writer that receives v3 must preserve v3 and its events.

V1 and v2 validation retains its historical strict behavior. V3 target
coverage uses the first-observed version semantics above. The v1/v2-to-v3
migration validator proves the old registry against the supplied older target
before applying v3 coverage rules to the new target.

### Resource limits

V3 reuses existing package limits for entries, modules, theorem rows, paths,
and strings. It adds explicit bounded counts for catalog-change events, revised
routes, added targets, and lifecycle rows; the implementation constants live
beside the existing promotion registry limits. Parsing checks limits before
allocating nested data. One event must cover the complete package diff, so the
CLI never silently truncates or splits a transition to fit a limit.

## Attestation

The generated file uses:

```text
npa.mathlib.catalog_registry_sync_attestation.v1
```

It records:

- command and schema versions;
- previous-target and target projections from the event;
- input registry schema, file hash, and registry hash;
- domain-separated change-set hash;
- audit path and hash;
- optional request path, file hash, and request hash;
- one comparison row for every previous or current local module;
- the exact old and new revision hashes for revised modules;
- the exact owner ID and first revision hash for added modules;
- every request-bound lifecycle relation;
- all package-gate verdicts used during preparation;
- `proof_evidence: false`; and
- its domain-separated `attestation_hash`.

Comparison rows use `unchanged`, `revision_appended`, `catalog_target_added`,
`renamed`, `replaced`, `split`, `merged`, or `retired` and are sorted by module
name. The attestation is governance evidence, not proof evidence and not an L2
maturity record.

## Verification gates

The command runs the equivalent library APIs directly. The current target must
pass `package check`, `check-hashes`, `build-certs --check`, cache-off
source-free reference verification, `axiom-report --check`, and `index
--check`. The immutable previous target must pass `check-hashes`, checked
generated-artifact loading, package-lock import resolution, and cache-off
source-free reference verification; reconciliation never rebuilds it from
historical authoring source. The current target must additionally pass all checked projections
that are both used for registry/publication identity and tracked by
`npa-mathlib`:

```sh
npa package export-summary --root <current> --check --json
npa package publish-plan --root <current> --check --json
```

The theorem-premise report is not a direct registry identity input and does not
receive a hash field in the event projection. It is nevertheless a transitive
input to the current publish-plan gate, so the current target must carry its
checked form before reconciliation. Reconciliation validates but does not
create package projections.

The authoritative proof gate for both roots is:

```sh
npa package verify-certs \
  --root <root> \
  --checker reference \
  --audit-cache off \
  --json
```

No event may be created from cached verifier success, unchecked generated
files, source/replay content, or registry metadata alone. A reconciliation
attestation records every gate and exact command-equivalent option.

## Processing algorithm

The command performs these steps in order:

1. Canonicalize and compare roots; validate confined audit, request, and output
   paths.
2. Acquire a shared/read lock in dry-run mode or the existing exclusive
   `TargetLock` in apply mode.
3. Reject an existing promotion recovery journal or another registry writer.
4. Read the registry once and retain its exact file hash.
5. Parse and shape-validate v1, v2, or v3 without comparing it to the current
   target.
6. Load and gate the previous and current packages as specified above.
7. Before ordinary transition preconditions, detect an existing v3 event and attestation
   with the requested previous version, current target identity, audit,
   request, and output path. If all bytes and hashes match, validate current
   target coverage and return `already_applied`; any partial match fails
   closed.
8. Prove the input registry exactly owns the previous package.
9. Build deterministic previous/current module maps, parse the optional request,
   and classify differences.
10. Reject every unsupported difference before constructing output.
11. Construct the v3 registry and attestation in memory.
12. Validate the applicable transition, v3 shape/self-hash, attestation,
    current-target coverage, namespace policy, import policy, and axiom policy.
13. In dry-run mode, return the proposed hashes and change counts without
    writing.
14. In apply mode, re-read and compare all input file identities while holding
    the exclusive lock.
15. Write a recovery journal containing expected old and new hashes.
16. Write the attestation create-or-identical and fsync it.
17. Atomically replace `promotion-origins.json` last and fsync it.
18. Re-run registry validation against the current target.
19. Remove the recovery journal only after validation passes.

Apply is idempotent. Repeating the same command after success returns passed
with `already_applied`; it must not add another event or generation. If the
registry is v3 but the requested attestation or event differs, fail closed.

Recovery uses the existing promotion recovery mechanism. It reacquires the
exclusive target lock, validates the journal's root and old/new hashes, and
either completes the attestation-plus-registry replacement or reports a
specific irreconcilable state without guessing. A post-write failure returns
`promotion_recovery_required` and prints the exact `--recover` command. The
user must not delete or steal the transaction journal.

## Command result and diagnostics

The historical 0.7 introduction emitted
`npa.package.command_result.v0.3`; current 0.8 writers use the shared
`npa.package.command_result.v0.4` envelope. Artifacts include:

- input registry file hash;
- proposed or written registry file and self-hash;
- attestation path and hash;
- previous and target package versions;
- unchanged, revised, added, renamed, replaced, split, merged, and retired
  module counts; and
- dry-run, applied, or already-applied disposition.

Use these stable reason codes:

| Reason code | Meaning |
| --- | --- |
| `promotion_registry_reconciliation_input_schema_unsupported` | Input is not registry v1, v2, or v3. |
| `promotion_registry_reconciliation_previous_target_mismatch` | Registry does not exactly cover the previous target. |
| `promotion_registry_reconciliation_target_not_newer` | Target version is not later. |
| `promotion_registry_reconciliation_request_required` | A removal or relation lacks an explicit request. |
| `promotion_registry_reconciliation_request_invalid` | Request endpoints, versions, relation, or hash are invalid. |
| `promotion_registry_reconciliation_owner_collision` | Two active routes would own one target. |
| `promotion_registry_reconciliation_unsupported_difference` | The change would alter immutable source provenance or history. |
| `promotion_registry_reconciliation_audit_invalid` | Audit path or bytes are invalid. |
| `promotion_registry_reconciliation_output_conflict` | Existing output differs. |
| `promotion_registry_reconciliation_input_changed` | An input changed between preparation and apply. |
| `promotion_registry_reconciliation_transition_invalid` | Proposed v3 is not the exact allowed transition. |
| `promotion_registry_reconciliation_attestation_invalid` | Attestation hash or content is invalid. |
| `promotion_registry_reconciliation_target_identity_mismatch` | Proposed v3 does not exactly own current target. |
| `promotion_recovery_required` | A tracked write began and recovery must finish. |

Diagnostics must point to a JSON path, module, or filesystem path when one is
available. Dry-run failures are pre-write. Any failure after the recovery
journal is created is post-write.

## Code changes

Implementation touches these areas:

- `npa-package`
  - add the `catalog_target_v1` owner, event-overlay resolver, registry v3
    types, strict parser/serializer, hashes, lookup, migration, and transition
    validators;
  - export the new public contracts from `src/lib.rs`;
  - retain v1/v2 parsing and validation.
- `npa-cli`
  - add argument, help-topic, dispatch, and command-result plumbing;
  - add `package_promotion_registry_reconcile.rs`;
  - extend the versioned registry enum and every registry consumer for v3;
  - reuse audit-snapshot loading, governance path confinement, target locking,
    atomic writing, and recovery journaling, adding shared dry-run locking to
    the registry lock abstraction.
- promotion materialization and equivalent-origin registration
  - preserve v3 catalog change events;
  - emit v3 after a v3 input rather than downgrading it;
  - leave direct catalog revisions and lifecycle requests to the reconciliation
    command.
- discovery tooling
  - accept and validate v3;
  - resolve sourced, catalog-target, and legacy owners plus their event
    overlays before candidate exclusion.
- documentation
  - update the CLI reference, promotion-origin registry policy, and mathlib
    operator instructions.

No implementation may add a general “ignore registry mismatch” flag.

## Test plan

### `npa-package` unit tests

- canonical v3 round trip and self-hash;
- rejection of unknown, missing, reordered, and duplicate fields;
- deterministic event, revision, change-set, registry, and attestation hashes;
- accepted exact v1-to-v3 and v2-to-v3 reconciliation;
- accepted repeated v3-to-v3 synchronization across nonconsecutive versions;
- unchanged old revision accepted in a newer v3 target without a duplicate
  revision;
- old artifact identity rejected when hashes differ despite a newer event;
- rejection when an old entry, reservation, revision, lifecycle, or evidence
  changes outside an event;
- rejection of unsorted or incomplete event inventories;
- normal v3 transition preservation;
- v1 and v2 regression parsing.

### CLI argument tests

- complete dry-run and apply forms;
- complete recovery form and rejection of mixed normal/recovery options;
- default dry-run;
- help output;
- missing required flags;
- conflicting modes;
- repeated singleton flags;
- absolute or escaping governance paths;
- same canonical previous and target root.

### Integration tests

Create compact fixtures for:

- all modules unchanged, including a package-version-only no-op that leaves the
  registry and attestation output untouched;
- one revised legacy route;
- one new catalog target;
- revised plus new catalog targets;
- differing existing attestation;
- already-applied idempotence;
- previous-target mismatch;
- requested retirement, rename, replacement, split, and merge;
- unrequested removal;
- sourced-entry target revision with immutable source provenance;
- stale generated projection;
- custom-axiom rejection;
- simulated failure before journal, after attestation write, and after registry
  replacement;
- exact recovery and final validation.

The integration test must also reproduce the real topology shape: a v0.2.1
registry, a later target with three unowned modules, and one existing module
revision. A second transition must skip at least two package versions and prove
that synchronization remains available at any later time.

### Repository validation

Run:

```sh
cargo +1.95.0 fmt --all -- --check
cargo +1.95.0 clippy --workspace --all-targets -- -D warnings
cargo +1.95.0 test -p npa-package
cargo +1.95.0 test -p npa-cli package_promotion_registry
cargo +1.95.0 run -q -p npa-cli -- package \
  reconcile-promotion-origin-registry --help
```

After applying the real reconciliation:

```sh
cargo +1.95.0 run -q -p npa-cli -- package \
  validate-promotion-origin-registry --root ../npa-mathlib --json
```

Then rerun the `promote-to-mathlib` structural scanner for every top-level
`npa-corpus` and `npa-project-*` package containing
`proofs/npa-package.toml`.

## Acceptance criteria

The command is complete when:

1. Dry-run proves the registry against an explicit older target and reports the
   exact deterministic v3 transition without writing.
2. Apply writes only the attestation, registry, and recovery journal; the
   registry is replaced last.
3. Existing registry history is preserved and every appended identity is bound
   to the audit and attestation.
4. The resulting registry validates against the current catalog and excludes
   all current modules from false discovery candidacy.
5. Repeating apply is idempotent.
6. Additions and revisions work without a request; explicit valid rename,
   replacement, split, merge, and retirement requests work without rewriting
   released history.
7. All registry readers and writers preserve v3 without downgrade.
8. Positive, negative, concurrency, and crash-recovery tests pass.
9. Existing v1/v2 registry and promotion tests remain green.
10. The v0.2.1-to-v0.2.4 reconciliation succeeds, registry validation passes,
    and structural discovery can run without a registry error.
11. The same command can migrate any valid v1/v2/v3 registry snapshot directly
    to any strictly newer validated target version, including after skipped
    releases.
