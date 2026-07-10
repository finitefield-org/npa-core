# Package Artifact Refresh Command Todo

Source: `npa-core/docs/package-artifact-refresh-command-design.md`

## Scope

This task breakdown implemented the
`npa package build-certs --update-manifest-hashes` MVP from the source design.
The command mode rebuilds local certificates, refreshes only local module hash
pins in `npa-package.toml`, and regenerates `generated/package-lock.json` as
one reviewable operation.

The milestones cover CLI parsing, refresh-specific build identity handling,
safe manifest rewriting, refreshed lock generation, no-write check mode,
atomic write mode, regression coverage, and documentation handoff after the
runtime is accepted.

This task breakdown does not cover non-MVP follow-ups: external import pin
updates, network or registry lookup, package lock schema changes, package graph
schema changes, generated metadata regeneration beyond lock refresh, or any
relaxation of checker/kernel proof acceptance.

## Global Constraints

- Treat the source design as an implementation record. The current public
  workflow is documented in
  `npa-core/docs/npa-toolchain-reference-v0.2.0.md`.
- Preserve the certificate-first trust boundary. Source files, replay files,
  metadata sidecars, generated JSON, command status, and this refresh command
  are not proof evidence.
- Do not weaken ordinary `build-certs`, `build-certs --check`,
  `check-hashes`, `lock write`, or `verify-certs` behavior when
  `--update-manifest-hashes` is absent.
- Keep top-level external `[[imports]]` pins strict. Refresh mode must fail on
  external `export_hash` or `certificate_hash` drift.
- Update only local module hash fields in `npa-package.toml`:
  `expected_source_hash`, `expected_certificate_file_hash`,
  `expected_export_hash`, `expected_axiom_report_hash`, and
  `expected_certificate_hash`.
- Do not update module imports, declarations, theorem lists, axiom lists,
  `meta`, `replay`, `producer_profile`, `tags`, package policy, or optional
  package metadata.
- Do not change `crates/npa-package/src/manifest.rs`,
  `crates/npa-package/src/graph.rs`, `crates/npa-package/src/lock.rs`,
  `PackageLockManifest`, or package lock JSON schema constants for the MVP.
- Use deterministic ordering, deterministic diagnostics, and existing
  `CommandResult` JSON. Do not add `CommandArtifact` entries for refresh mode.
- Do not use Git LFS or add `.gitattributes` LFS rules.

## Milestones

### PAF-01 Parser And CLI Surface

- Status: Complete
- Depends on: None
- Inputs: design sections `User Interface`, `Parser Contract`, `Help Text`,
  `Interaction With Existing Commands`, and `Tests`; files
  `npa-core/crates/npa-cli/src/args.rs`,
  `npa-core/crates/npa-cli/src/package_build.rs`, and
  `npa-core/crates/npa-cli/tests/package_cli_args.rs`.
- Deliverables:
  - Extend `PackageBuildCertsOptions` with `update_manifest_hashes: bool`.
  - Parse `--update-manifest-hashes` in `parse_package_build_certs_args`.
  - Reject duplicate `--update-manifest-hashes` with
    `UsageReason::DuplicateFlag`.
  - Reject the `--update-manifest-hashes=VALUE` value form with
    `UsageReason::UnsupportedFlag`, command `package build-certs`, flag
    `--update-manifest-hashes`, and the provided value.
  - Reject `--update-manifest-hashes --build-check-cache read-through` with
    `UsageReason::UnsupportedFlag`, flag `--build-check-cache`, and value
    `read-through`.
  - Keep `--build-check-cache read-through` valid for ordinary
    `build-certs --check` when refresh mode is absent.
  - Update `build-certs` help text to include the new flag and current
    incompatibility.
  - Route refresh requests to explicit runtime stubs that fail with a stable
    unsupported diagnostic until later milestones replace them with working
    behavior.
- Acceptance criteria:
  - Parser defaults keep `update_manifest_hashes=false`.
  - Existing `build-certs` and `build-certs --check` parser tests keep passing.
  - The new flag parses in write mode and check mode.
  - Unsupported refresh/cache combinations fail before package-root loading.
  - Ordinary `read-through` build-check cache behavior is unchanged without the
    refresh flag.
  - No public refresh command reports success before runtime support exists.
- Verification:
  - `cargo test -q -p npa-cli package_cli_args`
  - targeted review of `npa-core/crates/npa-cli/src/args.rs`
- Notes:
  - Keep the existing `is_unsupported_clr04_flag` behavior for other commands.
  - The temporary check-mode runtime failure must be removed by PAF-05. The
    temporary write-mode runtime failure must be removed by PAF-06.

### PAF-02 Refresh Build Data Model And Runtime Skeleton

- Status: Complete
- Depends on: PAF-01
- Inputs: design sections `Implementation Files`, `Runtime Data Model`,
  `Build Algorithm`, `Trust Boundary`, and `Diagnostics`; files
  `npa-core/crates/npa-cli/src/package_build.rs`,
  `npa-core/crates/npa-cli/src/package.rs`, and
  `npa-core/crates/npa-package/src/lock.rs`.
- Deliverables:
  - Add refresh-private runtime structs such as
    `PackageCertificateRefreshBuild`, `LocalModuleRefreshIdentity`,
    `RefreshAvailableModule`, and `RefreshImportOrigin`.
  - Add `run_package_build_certs_refresh_write` and
    `run_package_build_certs_refresh_check` entry points behind the parsed
    flag.
  - Load and validate package roots through `load_package_root`.
  - Reuse `check_write_mode_targets` before write-mode refresh and apply the
    same target validation in check mode for consistency.
  - Compute import use counts with `package_build_import_use_counts`.
  - Load and verify external imports exactly as ordinary `build-certs` does.
  - Preserve existing external import mismatch diagnostics:
    `external_certificate_rejected`, `certificate_module_mismatch`,
    `export_hash_mismatch`, and `certificate_hash_mismatch`.
  - Keep refresh runtime stubs from reporting success until refreshed local
    module builds and lock generation are implemented.
- Acceptance criteria:
  - Refresh mode shares ordinary package loading, policy, target validation,
    and external import verification paths where possible.
  - External import drift is a hard failure before local manifest pins are
    rewritten.
  - No schema changes are introduced in `npa-package`.
  - Existing ordinary write and check tests remain unchanged when the flag is
    absent.
- Verification:
  - `cargo test -q -p npa-cli package_cli_args`
  - `cargo test -q -p npa-cli package_build_certs`
- Notes:
  - Keep the new structs private to `package_build.rs`.
  - Avoid broad public API changes in `npa-package`; use existing exported lock
    types such as `PackageLockArtifact`.

### PAF-03 Fresh Local Import Identity Rebuild

- Status: Complete
- Depends on: PAF-02
- Inputs: design sections `Build Algorithm`, `Direct Import Identity Check`,
  `Edge Cases`, and `Tests`; files
  `npa-core/crates/npa-cli/src/package_build.rs`,
  `npa-core/crates/npa-cli/tests/package_build_certs_check.rs`, and
  `npa-core/crates/npa-cli/tests/package_build_certs_write.rs`.
- Deliverables:
  - Implement a refresh-specific local module rebuild helper that always builds
    fresh certificate bytes in `loaded.validated.graph().topological_order`.
  - Use the same producer-profile branches as the ordinary write path,
    including `LEGACY_STD_PACKAGE_PRODUCER_PROFILE`.
  - Implement `take_refresh_direct_import_context` instead of weakening
    `take_direct_import_context`.
  - For local imports, use live rebuilt identities instead of stale manifest
    `expected_export_hash` and `expected_certificate_hash` pins.
  - For external imports, continue comparing verified identities against
    resolved manifest import hashes.
  - Preserve manifest import order in direct verified-module and source
    interface vectors.
  - Encode and verify each rebuilt certificate, run generated axiom policy
    checks, and verify `verified.module() == module.module`.
  - Implement refreshed certificate import identity checking against the live
    direct import identities used during compilation.
  - Return `import_identity_unavailable` or
    `refreshed_import_identity_mismatch` only for refresh-specific internal
    identity failures.
  - Record source hash, certificate file hash, export hash, axiom-report hash,
    certificate hash, certificate bytes, verified module, and imported source
    interface for every local module.
- Acceptance criteria:
  - A refresh build helper can rebuild downstream modules against the fresh
    upstream identity for a fixture with stale local upstream manifest pins.
  - Ordinary `build-certs` still fails on the same stale local direct-import
    identity.
  - Refresh mode does not call `check_generated_source_hash` or
    `check_generated_manifest_hashes` against the stale manifest.
  - Refresh mode does not use the terminal checked-certificate reuse
    optimization from `build_local_modules_for_check`.
  - Axiom policy and certificate module mismatch diagnostics remain enforced.
- Verification:
  - `cargo test -q -p npa-cli package_build_certs_check`
  - `cargo test -q -p npa-cli package_build_certs_write`
- Notes:
  - Prefer reusing existing build helpers before copying logic. Any copied
    logic should remain close to the ordinary build implementation and covered
    by regression tests.

### PAF-04 Safe Manifest Rewrite And Validation

- Status: Complete
- Depends on: PAF-03
- Inputs: design sections `Fields Updated`, `Manifest Rewrite`,
  `Refreshed Manifest Validation`, `Diagnostics`, and `Tests`; files
  `npa-core/crates/npa-cli/Cargo.toml`,
  `npa-core/crates/npa-cli/src/package_build.rs`,
  `npa-core/crates/npa-cli/tests/package_build_certs_check.rs`, and
  `npa-core/crates/npa-cli/tests/package_build_certs_write.rs`.
- Deliverables:
  - Add a direct `toml_edit` dependency to `npa-cli`.
  - Implement `refresh_manifest_hash_fields`.
  - Parse the manifest as `toml_edit::DocumentMut`.
  - Locate the `modules` array of tables and require its length and module
    order to match the validated manifest.
  - Replace only the five allowed local module hash fields.
  - Serialize hashes with `format_package_hash`.
  - Preserve deterministic trailing newline behavior.
  - Return `manifest_refresh_failed` for missing modules, wrong TOML shape,
    missing module names, module order mismatch, missing hash fields, duplicate
    or ambiguous hash fields, or non-string hash fields.
  - Parse and validate the rewritten manifest with
    `parse_and_validate_manifest_str`.
  - Compare the original and refreshed validated manifests and reject any
    unchanged-field drift with `manifest_refresh_failed`.
  - Return `manifest_refresh_parse_failed` when the rewritten source does not
    parse or validate.
- Acceptance criteria:
  - Only local module hash pins can change in `npa-package.toml`.
  - Package name, version, policy, module count, module order, module names,
    source paths, certificate paths, imports, declarations, axioms, tags,
    top-level imports, and optional metadata remain unchanged.
  - Formatting and comments outside touched values are preserved as far as
    `toml_edit` permits, and any deterministic formatting change is covered by
    tests.
  - Ambiguous or malformed manifest shapes fail before any target file is
    written.
  - Stale source hash with unchanged certificate identity updates only
    `expected_source_hash`.
- Verification:
  - `cargo test -q -p npa-cli package_build_certs_check`
  - `cargo test -q -p npa-cli package_build_certs_write`
  - `cargo test -q -p npa-package package_manifest`
- Notes:
  - A strict line-replacement fallback is acceptable only if implementation
    review rejects a direct `toml_edit` dependency and the fallback enforces the
    same safety rules.

### PAF-05 Refreshed Lock Generation And Check Mode

- Status: Complete
- Depends on: PAF-04
- Inputs: design sections `Build Algorithm`, `Check Mode`, `Diagnostics`,
  `Interaction With Existing Commands`, and `Tests`; files
  `npa-core/crates/npa-cli/src/package_build.rs`,
  `npa-core/crates/npa-cli/tests/package_build_certs_check.rs`, and
  `npa-core/crates/npa-package/src/lock.rs`.
- Deliverables:
  - Build the refreshed package lock with `build_package_lock_from_artifacts`.
  - Pass the refreshed validated manifest, `loaded.manifest_path.clone()`,
    refreshed manifest bytes, refreshed local certificate bytes, and existing
    external certificate bytes as one `PackageLockArtifact` iterator.
  - Serialize the refreshed lock with `canonical_json`.
  - Implement `--check --update-manifest-hashes` without writing files.
  - Compare refreshed manifest bytes, local certificate bytes, and refreshed
    lock JSON in deterministic order.
  - Return `manifest_hashes_stale` with hashes for manifest differences.
  - Reuse `build_certificate_changed`, `package_lock_missing`, and
    `package_lock_stale` where their meanings match.
  - Stop at the first stale target, matching current `build-certs --check`
    behavior.
  - Keep `NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS` undocumented and irrelevant to
    refresh-mode local manifest comparisons.
  - Keep existing read-through build-check cache behavior unchanged when the
    refresh flag is absent.
- Acceptance criteria:
  - Check mode writes no files, including no manifest, certificate, lock, or
    temporary output.
  - Fresh packages pass check mode.
  - Stale manifest pins report `manifest_hashes_stale`.
  - Changed checked-in certificate bytes report `build_certificate_changed`.
  - Missing package lock reports `package_lock_missing`.
  - Refreshed manifest plus refreshed lock validates through package lock
    builder behavior.
  - JSON output stays in the existing command-result schema with no
    `CommandArtifact` entries.
- Verification:
  - `cargo test -q -p npa-cli package_build_certs_check`
  - `cargo test -q -p npa-cli package_cli_args`
  - targeted review of JSON diagnostics for `manifest_hashes_stale`
- Notes:
  - Keep certificate bytes, manifest source, and large JSON payloads out of
    diagnostics.

### PAF-06 Atomic Write Mode

- Status: Complete
- Depends on: PAF-05
- Inputs: design sections `Atomic Write Plan`, `Diagnostics`, `Edge Cases`,
  and `Acceptance Criteria`; files
  `npa-core/crates/npa-cli/src/package_build.rs` and
  `npa-core/crates/npa-cli/tests/package_build_certs_write.rs`.
- Deliverables:
  - Extend `PendingWrite` or add a sibling staged-write type so certificate,
    manifest, and package-lock writes use one staging and cleanup path.
  - Stage local certificates in manifest module order.
  - Stage `npa-package.toml` through `PackagePath::new(PACKAGE_MANIFEST_PATH)`.
  - Stage `generated/package-lock.json`.
  - Use hidden temporary files in the target directory, including
    `.npa-package.toml.npa-build-certs.tmp` for the manifest.
  - Create parent directories only during staging, before any rename.
  - Rename no target until every temporary file is staged.
  - Rename targets in deterministic order: local certificates,
    `npa-package.toml`, then `generated/package-lock.json`.
  - Remove temporary files created by the current run on write or rename
    failure.
  - Return `manifest_write_failed`, `certificate_write_failed`, or
    `package_lock_write_failed` for the target that failed.
- Acceptance criteria:
  - Write mode updates only local certificate files, `npa-package.toml`, and
    `generated/package-lock.json`.
  - Write mode repairs stale local certificates, stale local manifest pins, and
    stale package lock together.
  - Missing local certificates and missing package lock can be recreated after a
    successful build.
  - Idempotent refresh leaves current files unchanged and leaves no new
    temporary files.
  - A staging or rename failure does not partially update target files.
  - Pre-existing unrelated temporary files are ignored.
- Verification:
  - `cargo test -q -p npa-cli package_build_certs_write`
  - targeted filesystem review of staged write tests
- Notes:
  - Keep target validation from PAF-02 active for both write and check modes.

### PAF-07 End-To-End Regression And Edge-Case Coverage

- Status: Complete
- Depends on: PAF-06
- Inputs: design sections `Edge Cases`, `Tests`, `Acceptance Criteria`,
  `Trust Boundary`, and `Non-Goals`; files
  `npa-core/crates/npa-cli/tests/package_build_certs_check.rs`,
  `npa-core/crates/npa-cli/tests/package_build_certs_write.rs`,
  `npa-core/crates/npa-cli/tests/package_cli_args.rs`, and package fixture
  helpers under `npa-core/testdata/package` or temporary test directories.
- Deliverables:
  - Add or extend fixtures for local upstream export or certificate identity
    drift and downstream rebuild.
  - Add a regression proving ordinary `build-certs` still fails on stale local
    direct-import identity when refresh mode is absent.
  - Add refresh-mode failure coverage for external import certificate drift.
  - Add source-hash-only refresh coverage.
  - Add malformed or ambiguous manifest rewrite coverage.
  - Add missing certificate and missing lock coverage for write and check modes.
  - Add post-refresh checks that `package check-hashes` passes.
  - Add post-refresh checks that `package verify-certs --checker reference`
    passes.
  - Add a regression proving stale manifest inputs still fail when the
    refreshed manifest is not used for lock generation.
  - Assert ordinary `build-certs`, `build-certs --check`, `check-hashes`,
    `lock write`, and `verify-certs` behavior remains unchanged when the flag
    is absent.
- Acceptance criteria:
  - Parser and runtime tests cover every edge case listed in the source design.
  - Tests prove external imports remain strict and local imports use live
    rebuilt identities only in refresh mode.
  - Tests prove refreshed packages pass both hash checking and source-free
    reference verification.
  - No test requires sibling NPA repository checkouts or network access.
  - No generated fixture introduces Git LFS pointer files.
- Verification:
  - `cargo test -q -p npa-cli package_cli_args`
  - `cargo test -q -p npa-cli package_build_certs_check`
  - `cargo test -q -p npa-cli package_build_certs_write`
  - `cargo test -q -p npa-cli package_verify_certs`
  - `cargo test -q -p npa-cli package_check_hashes`
- Notes:
  - Prefer compact temporary fixtures or existing package build fixture helpers
    over broad checked-in fixture churn.

### PAF-08 Documentation Handoff And Adoption Cleanup

- Status: Complete
- Depends on: PAF-07
- Inputs: design sections `Rollout`, `Example Workflow`, `Interaction With
  Existing Commands`, and `Acceptance Criteria`; files
  `npa-core/docs/package-artifact-refresh-command-design.md`,
  `npa-core/docs/package-artifact-refresh-command-design-todo.md`,
  `npa-core/docs/npa-toolchain-reference-v0.2.0.md`,
  `npa-core/docs/README.md`, `npa-core/README.md`, and any in-repository
  repair scripts or docs found by searching for local refresh bypasses.
- Deliverables:
  - Update the toolchain reference with the implemented refresh workflow only
    after PAF-07 passes.
  - Keep the current/future behavior boundary clear if the design remains
    proposed for a later release.
  - Document write mode and dry-run check mode examples.
  - State that external import pins are not updated by this command.
  - State that refresh mode is metadata and artifact refresh, not proof
    evidence.
  - Search for local scripts, docs, or suggestions that mention ad hoc hash
    bypasses or `NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS` and update them to use the
    supported flag where appropriate.
  - Keep non-MVP external import update behavior documented as future work only.
  - Run final focused tests and the fast gate unless resource limits prevent
    it.
- Acceptance criteria:
  - User-facing docs agree with implemented CLI behavior.
  - No docs tell users to bypass direct-import hash checks for artifact refresh.
  - Current stable reference examples remain accurate for the release state.
  - The design todo can be marked complete or left as an implementation record
    with all milestones satisfied.
  - Any skipped heavy validation is recorded with the focused tests that did
    pass.
- Verification:
  - `cargo fmt --all -- --check`
  - `cargo test -q -p npa-cli package_cli_args`
  - `cargo test -q -p npa-cli package_build_certs_check`
  - `cargo test -q -p npa-cli package_build_certs_write`
  - `cargo test -q -p npa-cli package_verify_certs`
  - `cargo test -q -p npa-cli package_check_hashes`
  - `./scripts/check-fast.sh`
  - `rg -n "NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS|update-manifest-hashes|bypass" npa-core docs suggestions.md`
- Notes:
  - Run expensive gates with narrower targets or lower concurrency first if
    memory pressure is plausible.
  - Keep documentation updates scoped to implemented behavior; do not advertise
    the refresh flag as current stable behavior before it ships.
