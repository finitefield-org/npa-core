# Package Artifact Refresh Command Design

Status: implemented in the current `npa-core` package CLI. This document is
retained as the design and implementation record; package authors should use
the current workflow documented in `npa-toolchain-reference-v0.7.0.md`, which
retains the v0.6-introduced refresh contract.

## Summary

Add an explicit package refresh mode for local package artifacts:

```sh
npa package build-certs --root . --update-manifest-hashes --json
npa package build-certs --root . --update-manifest-hashes --check --json
```

Full refresh rebuilds local certificates. Targeted `--module` and `--changed`
refresh dynamically rebuild seeds and ineligible dependents, while
export-stable qualified dependents may receive a source-free strict import-pin
rebind or live-verified unchanged reuse. Both modes update local module hash
pins in `npa-package.toml`, refresh declared module `meta.json` ledgers, and
regenerate `generated/package-lock.json` as one reviewable refresh operation.

The feature exists to replace ad hoc local edits that weaken import identity
checks while refreshing artifacts. It must preserve the certificate-first trust
boundary: the command may refresh generated or pinned metadata, but proof
acceptance still depends on canonical `.npcert` bytes and checker/kernel
verification.

## Problem

`package build-certs` currently resolves package imports from the checked
manifest graph before rebuilding local certificates. For local imports, that
graph records the imported module identity from the imported module's
`expected_export_hash` and `expected_certificate_hash`. If an upstream local
module changes, its freshly rebuilt certificate has a new identity, while
downstream modules still resolve imports through stale manifest pins.

The failure appears in the direct-import context check in
`crates/npa-cli/src/package_build.rs`: the command compares the available
verified module's actual `export_hash` and `certificate_hash` with the
manifest-resolved import identity. This is a valid consistency check during
normal builds, but there is no supported command mode that says:

1. Rebuild the upstream local module.
2. Use that freshly verified identity while rebuilding downstream modules.
3. Update `npa-package.toml` to the new local module hash pins.
4. Regenerate `generated/package-lock.json` from the refreshed manifest and
   certificate artifacts.

The existing `package lock write` path is not enough because it only rewrites
`generated/package-lock.json` from the current manifest and certificate files.
It does not rebuild certificates and does not update manifest hash pins.

## Intended Implementation Outcome

Implement a new `package build-certs` mode in `npa-cli` that:

- uses the current package manifest for package shape, import names, policy,
  source paths, certificate paths, declarations, tags, and topological order;
- rebuilds all local module certificates from source in full refresh mode;
- walks the complete dependent candidate closure topologically in targeted
  refresh mode, rebuilding sources when exports or qualified baselines differ
  and otherwise live-verifying a format-owned certificate rebind or unchanged
  certificate;
- computes replacement local module hash pins from the rebuilt certificate and
  source bytes;
- compiles downstream modules against the freshly verified upstream identities
  instead of stale local manifest identities;
- keeps external package import pins strict;
- rewrites only the allowed local hash fields in `npa-package.toml`;
- regenerates every declared module metadata sidecar in the rebuild closure
  from the validated module and verified certificate identities;
- regenerates `generated/package-lock.json` from the refreshed manifest and
  certificate bytes;
- supports both write mode and no-write `--check` mode;
- leaves ordinary `build-certs`, `build-certs --check`, `check-hashes`, and
  `lock write` behavior unchanged when the flag is absent. Verification's
  independent checked/reconstructed lock modes and provenance diagnostics are
  documented in the v0.3.0 toolchain reference.

## Goals

- Provide a public, deterministic way to refresh local certificate artifacts
  and their manifest hash pins.
- Avoid weakening direct import identity checks in ordinary build and check
  modes.
- Keep external import hash pins strict in the MVP.
- Write `npa-package.toml`, local `.npcert` files, declared module metadata,
  and `generated/package-lock.json` only after the whole refresh succeeds.
- Make the refresh reviewable by keeping command output deterministic and
  reporting changed or stale targets through standard diagnostics.
- Preserve existing package validation, axiom policy checks, and source-free
  package lock validation after the refresh.
- Avoid Git LFS and avoid generating pointer files.

## Non-Goals

- Do not treat source files, replay files, metadata sidecars, generated JSON, or
  command success as proof evidence.
- Do not silently update top-level external `[[imports]]` pins.
- Do not add network or registry lookup.
- Do not update a module's `imports = [...]`, declarations, theorem lists,
  axiom lists, `meta`, `replay`, `producer_profile`, or `tags` fields.
- Do not repair malformed manifests or package graph errors.
- Do not relax package policy such as `allow_custom_axioms`.
- Do not change `package lock write`; it remains a source-free lock rewrite
  from existing manifest and certificate artifacts.
- Do not change `PackageLockManifest` schema or package lock validation rules.

## User Interface

Extend `npa package build-certs` with one flag:

```text
npa package build-certs [--root PATH] [--json] [--check]
  [--build-check-cache off|read-through]
  [--update-manifest-hashes]
```

`--update-manifest-hashes`

- Enables refresh semantics for local module hash pins.
- In write mode, writes refreshed local certificates, `npa-package.toml`, and
  declared module metadata, and `generated/package-lock.json`.
- In `--check` mode, performs the same rebuild in memory and fails if any of
  those files would change.
- Is incompatible with `--build-check-cache read-through` in the MVP, because
  refresh mode changes the key material that build-check cache entries record.

The flag name is intentionally `--update-manifest-hashes` because
`crates/npa-cli/src/args.rs` already recognizes it as a package-family flag for
unsupported-flag reporting. The new implementation should move it from
"known but unsupported" to a documented `build-certs` option.

### Parser Contract

Update `crates/npa-cli/src/args.rs`.

Extend `PackageBuildCertsOptions`:

```rust
pub struct PackageBuildCertsOptions {
    pub common: PackageCommonOptions,
    pub check: bool,
    pub build_check_cache: PackageBuildCheckCacheMode,
    pub update_manifest_hashes: bool,
}
```

Parsing rules:

- `--update-manifest-hashes` is a boolean flag.
- A duplicate flag is a usage error with `UsageReason::DuplicateFlag`.
- `--update-manifest-hashes=<value>` is not accepted. Add an explicit
  value-form parser branch that returns `UsageReason::UnsupportedFlag`,
  `command = "package build-certs"`, `flag = "--update-manifest-hashes"`, and
  `value = <value>`.
- Handle `--update-manifest-hashes` in `parse_package_build_certs_args` before
  building `common_tokens`. If it reaches `parse_common_options`, it should be
  reported as a command-specific flag error rather than an unknown positional
  argument.
- Keep `--build-check-cache read-through` valid only with `--check` and without
  `--update-manifest-hashes`.
- Reject `--update-manifest-hashes --build-check-cache read-through` with
  `UsageReason::UnsupportedFlag`, `command = "package build-certs"`,
  `flag = "--build-check-cache"`, and `value = "read-through"`.

Suggested parser branch:

```rust
let mut update_manifest_hashes = false;
// ...
"--update-manifest-hashes" => {
    if update_manifest_hashes {
        return Err(flag_error("--update-manifest-hashes", UsageReason::DuplicateFlag)
            .with_command("package build-certs"));
    }
    update_manifest_hashes = true;
    index += 1;
}
```

### Help Text

Suggested help text:

```text
Usage: npa package build-certs [--root PATH] [--json] [--check]
  [--build-check-cache off|read-through] [--update-manifest-hashes]

Rebuild package certificates. --check writes no files; write mode updates local
certificates and generated/package-lock.json. --update-manifest-hashes also
refreshes local module hash pins in npa-package.toml after a successful rebuild.
```

## Trust Boundary

Refresh mode updates metadata that names certificate identities. It does not
make metadata trusted proof evidence.

Trusted proof evidence remains:

- canonical `.npcert` bytes;
- Rust kernel / verifier verdicts;
- source-free checker verdicts;
- deterministic certificate, export, axiom-report, and import hashes.

Refresh mode must verify every rebuilt local certificate before writing it.
After rewriting the manifest in memory, it must re-parse and re-validate the
manifest and regenerate the package lock from the refreshed manifest plus the
new certificate bytes. The final lock validation must use the same
`build_package_lock_from_artifacts` and
`validate_package_lock_against_manifest_graph` behavior as ordinary package
commands.

## Fields Updated

For each local `[[modules]]` table, refresh mode may update only these fields:

```toml
expected_source_hash = "sha256:..."
expected_certificate_file_hash = "sha256:..."
expected_export_hash = "sha256:..."
expected_axiom_report_hash = "sha256:..."
expected_certificate_hash = "sha256:..."
```

Top-level `[[imports]]` entries remain strict in the MVP:

```toml
export_hash = "sha256:..."
certificate_hash = "sha256:..."
```

If an external certificate artifact does not match its top-level import pins,
refresh mode must fail with the existing `export_hash_mismatch` or
`certificate_hash_mismatch` diagnostic. A future feature may add a separate,
explicit external-import update command, but that is outside this design.

## Implementation Files

Primary implementation files:

- `crates/npa-cli/src/args.rs`: parse and render
  `--update-manifest-hashes`.
- `crates/npa-cli/src/package_build.rs`: add refresh build, check, and write
  paths.
- `crates/npa-cli/Cargo.toml`: add a direct `toml_edit` dependency for safe
  manifest rewriting.
- `crates/npa-cli/tests/package_cli_args.rs`: parser coverage.
- `crates/npa-cli/tests/package_build_certs_check.rs`: check-mode refresh
  coverage.
- `crates/npa-cli/tests/package_build_certs_write.rs`: write-mode refresh
  coverage.
- `docs/npa-toolchain-reference-v0.6.0.md`: document the current refresh and
  checked/reconstructed verification workflow while retaining the published
  v0.2.0 reference unchanged as historical documentation.

Do not change these schemas for the MVP:

- `crates/npa-package/src/manifest.rs`;
- `crates/npa-package/src/graph.rs`;
- `crates/npa-package/src/lock.rs`;
- package lock JSON schema constants.

## Runtime Data Model

Add refresh-specific structs in `package_build.rs`; keep them private to the
command implementation.

```rust
#[derive(Clone, Debug)]
struct PackageCertificateRefreshBuild {
    local_modules: Vec<LocalModuleRefreshIdentity>,
    refreshed_manifest_source: String,
    package_lock_json: String,
}
```

Use `refreshed_manifest_source` for the TOML bytes written to
`npa-package.toml`. If the implementation has an intermediate structured
manifest value, name it distinctly, for example
`refreshed_manifest: ValidatedPackageManifest`; do not use a JSON name for the
TOML manifest source.

```rust
#[derive(Clone, Debug)]
struct LocalModuleRefreshIdentity {
    module_index: usize,
    module: Name,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
    certificate_path: PackagePath,
    certificate_bytes: Vec<u8>,
}
```

For direct import context, reuse `AvailableModule` where possible. Add a
refresh variant if the code becomes clearer:

```rust
#[derive(Clone, Debug)]
struct RefreshAvailableModule {
    verified: Arc<VerifiedModule>,
    source_interface: HumanImportedSourceInterface,
    remaining_uses: usize,
    origin: RefreshImportOrigin,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RefreshImportOrigin {
    Local,
    External,
}
```

The origin is needed because external imports must still be compared against
manifest pins, while local imports use the live rebuilt identity.

## Build Algorithm

Refresh mode should reuse the existing build machinery where possible, but it
needs a different import identity source while local modules are being rebuilt.

1. Load and validate the current package root with `load_package_root`.
2. Reject forbidden certificate write targets with `check_write_mode_targets`
   before write-mode refresh. Check mode should still perform target validation
   for consistency, but must not write.
3. Compute import use counts with `package_build_import_use_counts`.
4. Verify top-level external imports exactly as ordinary `build-certs` does.
   External import mismatches are hard failures.
5. Use the validated manifest graph only for import names, import origins, and
   topological order. Do not use stale local `expected_*` hash pins as the
   effective import identity during refresh.
6. Rebuild local modules in `loaded.validated.graph().topological_order`.
7. When compiling a module, build its direct import context by walking
   `resolved_module_imports[module_index]`:
   - for `ResolvedModuleImportKind::External`, require the verified external
     identity to match `import.export_hash` and `import.certificate_hash`;
   - for `ResolvedModuleImportKind::Local`, require a live rebuilt identity for
     that module and do not compare it to stale manifest pins;
   - preserve the manifest import order in the returned verified-module and
     source-interface vectors.
8. Compile the local module using the same producer-profile branches as the
   existing write path:
   - `LEGACY_STD_PACKAGE_PRODUCER_PROFILE` uses
     `build_legacy_std_package_certificate`;
   - ordinary human-source modules use
     `compile_human_source_to_certificate_output_with_import_refs_and_axiom_policy`.
9. Encode the certificate with `npa_cert::encode_module_cert`.
10. Run `check_generated_axiom_policy`.
11. Verify that `verified.module() == module.module`.
12. Compare the generated certificate's `imports` list against the live direct
    import identities used for compilation. This check replaces the current
    stale-manifest direct-import comparison for local imports.
13. Record the module's source hash, certificate file hash, export hash,
    axiom-report hash, certificate hash, certificate bytes, verified module,
    and imported source interface.
14. Insert the verified module into the available-module map if
    `remaining_uses > 0`.
15. After every local module builds, rewrite the manifest hash pins in memory.
16. Parse and validate the refreshed manifest source with
    `parse_and_validate_manifest_str`.
17. Build the refreshed package lock with `build_package_lock_from_artifacts`
    using:
    - the refreshed validated manifest;
    - `loaded.manifest_path.clone()`;
    - `refreshed_manifest_source.as_bytes()`;
    - a single `PackageLockArtifact` iterator containing refreshed local
      certificate bytes and existing external certificate bytes.
18. Serialize the lock with `canonical_json`.
19. Compare or write target files depending on `--check`.

Refresh mode must not call `check_generated_source_hash` or
`check_generated_manifest_hashes` against the stale manifest, because refreshing
those hashes is the point of the mode. It must still compute the same values
and write them into the refreshed manifest.

Refresh mode, like ordinary full check, must freshly compile every rebuilt
local module. Source size must not permit reuse of checked certificate bytes in
place of comparing them with a certificate generated from current source.

## Direct Import Identity Check

Add a refresh-specific direct import helper instead of modifying
`take_direct_import_context` in place:

```rust
fn take_refresh_direct_import_context(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
) -> Result<DirectImportContext, Box<CommandDiagnostic>>
```

Behavior:

- Preserve the current remaining-use removal behavior.
- Return `import_identity_unavailable` if a direct import has not been built or
  loaded.
- For external imports, compare actual verified hashes against the
  `ResolvedModuleImport` hashes and return existing `export_hash_mismatch` or
  `certificate_hash_mismatch` diagnostics.
- For local imports, compare actual verified hashes only to the
  `HumanImportedSourceInterface` identity stored with the live rebuilt module.
  A mismatch here is internal refresh corruption and should return
  `refreshed_import_identity_mismatch`.

After compiling a certificate, compare its embedded imports with the direct
import identities used to compile it:

```rust
fn check_refreshed_certificate_import_identities(
    module_index: usize,
    module: &Name,
    expected: &[PackageLockImport],
    actual: &[npa_cert::ImportEntry],
) -> Option<CommandDiagnostic>
```

Rules:

- Duplicate expected direct imports must agree on hashes and are compared once.
- Certificate import module names must be unique.
- Every expected direct import must be present in the certificate import table;
  extra transitive certificate imports are allowed.
- Matching is by module name rather than import order.
- `export_hash` must match for every expected direct import.
- `certificate_hash` must be present and match for every expected direct
  import.
- Use `refreshed_import_identity_mismatch` with a path such as
  `modules[{module_index}].certificate.imports[{import_index}]` for any missing,
  duplicate, or hash-mismatched direct import.

## Manifest Rewrite

The implementation should preserve unrelated manifest formatting and comments.
Use `toml_edit` in `npa-cli` to update the exact fields in the parsed document
while preserving table order.

Helper shape:

```rust
fn refresh_manifest_hash_fields(
    manifest_source: &str,
    identities: &[LocalModuleRefreshIdentity],
) -> Result<String, Box<CommandDiagnostic>>
```

Rules:

- Parse `manifest_source` as `toml_edit::DocumentMut`.
- Locate the `modules` array of tables.
- Require the array length to match `loaded.validated.manifest().modules.len()`.
- For each module index, require the TOML table's `module` string to match the
  parsed manifest module name at the same index.
- Replace only:
  - `expected_source_hash`;
  - `expected_certificate_file_hash`;
  - `expected_export_hash`;
  - `expected_axiom_report_hash`;
  - `expected_certificate_hash`.
- Serialize hashes with `format_package_hash`.
- Preserve trailing newline behavior by emitting a trailing newline if the
  original manifest had one. If `toml_edit` changes formatting around touched
  values, keep that deterministic and covered by tests.
- Return `manifest_refresh_failed` for missing `modules`, wrong table shape,
  missing module name, module order mismatch, missing hash field, or non-string
  hash field.

If implementation review rejects a direct `toml_edit` dependency, a strict line
replacement helper is the only acceptable fallback. It must enforce these
constraints:

- every targeted `[[modules]]` table must contain each updated field exactly
  once;
- no non-targeted field may be rewritten;
- the module table order must match the parsed manifest order;
- duplicate, missing, or reordered ambiguous fields must fail instead of
  guessing;
- the rewritten manifest must parse to the expected refreshed manifest model
  before any file is written.

The command must not rewrite declarations, import lists, policy fields, or
comments as a side effect of refreshing hashes.

## Refreshed Manifest Validation

After rewrite, parse and validate the refreshed manifest:

```rust
let refreshed_validated = parse_and_validate_manifest_str(&refreshed_manifest_source)?;
```

Validation rules beyond the parser:

- `package`, `version`, package policy, module count, module order, module
  names, source paths, certificate paths, `imports`, declaration lists,
  `axioms`, `tags`, top-level `imports`, and optional package metadata must be
  unchanged from the original validated manifest.
- Only the five allowed local hash fields may differ.
- If validation fails, return `manifest_refresh_parse_failed` with the package
  manifest path.
- If unchanged-field comparison fails after a successful parse, return
  `manifest_refresh_failed`; that indicates the rewrite helper changed more
  than allowed.

## Atomic Write Plan

Write mode must stage all changed files first:

- local certificate files;
- `npa-package.toml`;
- declared module `meta.json` sidecars in the rebuild closure;
- `generated/package-lock.json`.

For each target:

1. Refuse forbidden certificate targets using the existing
   `check_write_mode_targets` behavior.
2. Write bytes to a hidden temporary path in the same directory.
3. If any temporary write fails, remove all temporary files and leave existing
   files untouched.
4. Rename all temporary files into place only after every target is staged.
5. If a rename fails, clean up remaining temporary files, roll already renamed
   targets back in reverse order, and report either the failed target or
   `artifact_rollback_failed` if recovery itself fails.

Extend `PendingWrite` or add a sibling type so manifest writes can use the same
staging and cleanup machinery as certificate and lock writes. Use
`PackagePath::new(PACKAGE_MANIFEST_PATH)` for the manifest target. The existing
`temporary_write_path` already produces a suitable suffix:

```text
.npa-package.toml.npa-build-certs.<pid>.<sequence>.tmp
```

Write order should be deterministic:

1. local certificates in manifest module order;
2. `npa-package.toml`;
3. declared module metadata in manifest module order;
4. `generated/package-lock.json`.

This order is only for deterministic behavior; no target should be renamed
until every temporary file is staged.

## Check Mode

With `--check --update-manifest-hashes`, the command writes no files. It should
fail when any target differs from the refreshed bytes.

Suggested diagnostics:

| Reason code | Path | Meaning |
| --- | --- | --- |
| `manifest_hashes_stale` | `npa-package.toml` | Refreshed local module hash pins differ from the checked manifest. |
| `build_certificate_changed` | module certificate path | Existing local certificate bytes differ from rebuilt bytes. |
| `module_metadata_missing` | module metadata path | Declared refreshed metadata is missing. |
| `module_metadata_stale` | module metadata path | Declared metadata differs from canonical refreshed bytes. |
| `package_lock_missing` | `generated/package-lock.json` | Checked package lock is missing. |
| `package_lock_stale` | `generated/package-lock.json` | Existing package lock differs from refreshed lock JSON. |

Comparison order should be deterministic and should stop at the first error,
matching current `build-certs --check` behavior:

1. manifest hash pins;
2. local certificate files in manifest module order;
3. declared module metadata in manifest module order;
4. package lock.

`manifest_hashes_stale` should use `with_hashes` and include both the refreshed
manifest hash and the current checked-in manifest hash. Keep the field ordering
consistent with the helper that performs the comparison, and cover it in the
JSON diagnostic test.

The command should not dump certificate bytes, manifest source, or large JSON
into diagnostics.

## Diagnostics

Reuse existing diagnostics wherever the meaning is unchanged:

- `source_missing`;
- `certificate_missing`;
- `external_certificate_rejected`;
- `certificate_module_mismatch`;
- `export_hash_mismatch`;
- `certificate_hash_mismatch`;
- `disallowed_axiom`;
- `certificate_rejected`;
- `certificate_encode_failed`;
- `build_certificate_changed`;
- `package_lock_missing`;
- `package_lock_stale`;
- `module_metadata_missing`;
- `module_metadata_stale`;
- `certificate_write_failed`;
- `module_metadata_write_failed`;
- `package_lock_write_failed`.

Add narrowly scoped diagnostics for refresh-specific failures:

| Reason code | Kind | Meaning |
| --- | --- | --- |
| `manifest_hashes_stale` | `HashMismatch` | Check mode found changed manifest hash pins. |
| `manifest_refresh_failed` | `PackageManifest` | Manifest rewrite changed more than allowed or could not be performed safely. |
| `manifest_refresh_parse_failed` | `PackageManifest` | Rewritten manifest did not parse or validate. |
| `manifest_write_failed` | `ArtifactIo` | Staged manifest write or rename failed. |
| `import_identity_unavailable` | `Internal` | A direct import name had no live verified identity during refresh. |
| `refreshed_import_identity_mismatch` | `HashMismatch` | Rebuilt certificate imports do not match the live identity table. |

JSON output should continue using the existing command-result schema. The
refresh command should not add `CommandArtifact` entries in the MVP.

## Interaction With Existing Commands

`package build-certs`

- Existing behavior remains unchanged unless `--update-manifest-hashes` is set.
- Existing `NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS` remains an internal escape
  hatch and should not be documented as the refresh workflow.
- Refresh mode should ignore `NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS` for local
  manifest hash comparisons because it does not perform those stale-manifest
  comparisons.

`package build-certs --check`

- Ordinary check freshly compiles every selected local target and compares its
  generated certificate with the checked bytes, regardless of source size.
- Existing read-through build-check cache behavior remains unchanged when the
  refresh flag is absent.

`package check-hashes`

- After a successful refresh, `package check-hashes` should pass for source
  hashes, certificate hashes, and package lock freshness.

`package lock write`

- No behavior change. It still reads the manifest and certificate files and
  writes only `generated/package-lock.json`.

`package verify-certs`

- Refreshed certificates still verify through the source-free verifier path.
- Core verification defaults to checked NPA package-lock input; reconstructed
  authoring is explicit. Both modes emit a separate lock-provenance/hash
  diagnostic, so output is not literally unchanged from the original refresh
  design.
- Release and audit verification must select `--package-lock checked` plus
  `--audit-cache off --verifier-memo off` explicitly.

Generated metadata commands

- `axiom-report`, `index`, `export-summary`, and `publish-plan` continue to be
  regenerated after certificate and lock refresh when release metadata is
  needed.

## Edge Cases

- Current package already fresh: write mode should be idempotent and should not
  leave new temporary files; check mode should pass.
- Source hash changed but certificate identity did not: refresh mode should
  update `expected_source_hash` and preserve other hash fields if unchanged.
- Upstream local export identity changed: refresh mode rebuilds downstream
  certificates against the new identity. If only the upstream certificate
  identity changed, targeted refresh may rebind every affected strict local
  import pin after source/baseline qualification and live verification.
- External import certificate changed without manifest pin update: refresh mode
  should fail with the existing external import hash mismatch.
- Missing existing local certificate: refresh write mode may recreate it after
  a successful build; refresh check mode should report `build_certificate_changed`
  or `certificate_missing` consistently with the chosen comparison helper.
- Missing declared metadata: refresh write mode should create it; refresh check
  mode should report `module_metadata_missing`.
- Stale declared metadata: refresh write mode should replace it while
  preserving valid extension fields; refresh check mode should report
  `module_metadata_stale`.
- Missing package lock: refresh write mode should create it; refresh check mode
  should report `package_lock_missing`.
- Malformed current manifest: fail during `load_package_root` before refresh
  starts.
- Manifest rewrite ambiguity: fail with `manifest_refresh_failed` and write
  nothing.
- Build failure after temporary files from an earlier interrupted run exist:
  ignore unrelated pre-existing temp files, but remove temp files created by
  the current run on failure.

## Tests

Add CLI parser tests in `crates/npa-cli/tests/package_cli_args.rs`:

- `build-certs --update-manifest-hashes` parses in write mode.
- `build-certs --check --update-manifest-hashes` parses in check mode.
- duplicate `--update-manifest-hashes` is a usage error.
- `--update-manifest-hashes --build-check-cache read-through` is unsupported in
  the MVP.
- help output includes the new flag.

Add package build tests with temporary fixtures. Prefer extending the existing
fixture helpers in `package_build_certs_check.rs` and
`package_build_certs_write.rs`; if duplication grows, move shared fixture
helpers to a test support module.

Write-mode tests:

- stale local upstream hash pins are refreshed and downstream certificates are
  rebuilt against the new identity.
- stale source hash only updates `expected_source_hash`.
- stale local certificate and stale manifest pins are repaired together.
- declared module metadata is refreshed from the same validated module and
  verified certificate identities while valid extension fields are preserved.
- stale package lock is regenerated from the refreshed manifest.
- idempotent refresh leaves current files unchanged.
- ordinary `build-certs` still fails on stale local direct import identity.
- external import hash mismatch still fails in refresh mode.
- malformed or ambiguous manifest rewrite input fails without writing files.
- a write failure during staged output does not partially update targets.

Check-mode tests:

- `--check --update-manifest-hashes` reports `manifest_hashes_stale` without
  writing files.
- changed certificate bytes report `build_certificate_changed` without writing
  files.
- missing metadata reports `module_metadata_missing` without writing files.
- stale metadata reports `module_metadata_stale` without writing files.
- missing package lock reports `package_lock_missing` without writing files.
- fresh package passes and writes no files.
- read-through build-check cache plus refresh flag is rejected before loading
  the package root.

Post-refresh verification tests:

- refreshed manifest plus refreshed lock passes `package check-hashes`.
- refreshed certificates pass explicit checked verification with acceleration
  disabled.
- refreshed metadata passes `package audit-artifact-ledger`.
- regenerated lock validates through `build_package_lock_from_package_root`.

Package-lock regression tests:

- no changes are needed to `lock.rs` for the MVP; lock validation should pass
  because it receives the refreshed manifest.
- keep a regression proving stale manifest inputs still fail when the refreshed
  manifest is not used.

## Acceptance Criteria

The feature is implementation-complete when:

- `npa package build-certs --update-manifest-hashes --root <pkg>` updates only
  local certificate files, `npa-package.toml`, declared module metadata in the
  rebuild closure, and `generated/package-lock.json`.
- `npa package build-certs --update-manifest-hashes --check --root <pkg>`
  writes no files and reports stale manifest, certificate, metadata, or lock
  artifacts deterministically.
- ordinary `npa package build-certs` behavior and diagnostics are unchanged
  when the new flag is absent.
- top-level external import hash mismatches remain hard failures in refresh
  mode.
- refreshed packages pass `package check-hashes` and `package verify-certs`
  with `--package-lock checked`, `--checker reference`, `--audit-cache off`,
  and `--verifier-memo off`.
- refreshed declared metadata passes `package audit-artifact-ledger`.
- parser and build tests cover the edge cases listed above.
- `cargo test -q -p npa-cli package_cli_args` passes.
- targeted package build tests for check and write refresh behavior pass.
- `git diff --check` passes.

## Rollout

1. Implement parser support and help text.
2. Implement a refresh-specific build path behind
   `--update-manifest-hashes`.
3. Implement safe manifest rewrite and staged writes.
4. Add fixture coverage for local upstream identity drift.
5. Document the workflow in the toolchain reference.
6. Update corpus/project repair scripts to use the supported flag instead of
   any local checker bypass.

## Example Workflow

After implementation, use this workflow when local source changes intentionally
alter certificate identities:

```sh
npa package build-certs --root proofs --update-manifest-hashes --json
npa package check-hashes --root proofs --json
npa package verify-certs --root proofs --package-lock checked \
  --checker reference --audit-cache off --verifier-memo off --json
npa package axiom-report --root proofs --json
npa package index --root proofs --json
npa package export-summary --root proofs --json
npa package publish-plan --root proofs --json
```

For a dry run:

```sh
npa package build-certs --root proofs --update-manifest-hashes --check --json
```

The dry run should be used in review and CI; the write mode should be used only
at explicit package artifact refresh boundaries.

The original implementation left declared module `meta.json` ledgers
unchanged. The v0.6-introduced behavior retained in current v0.7 instead
regenerates every declared ledger in the rebuild closure from the same verified
artifacts and includes it in the staged transaction. After write mode, run
`npa package audit-artifact-ledger --root proofs --json` and require clean
parity. Do not rewrite certificate bytes to match stale metadata. Neither the
refresh nor metadata alignment is proof evidence.
