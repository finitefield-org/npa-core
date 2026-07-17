//! Package manifest metadata parsing and validation for external NPA libraries.
//!
//! `npa-package` handles the untrusted `npa.package.v0.1` metadata format used
//! by `npa-package.toml`. It helps package, CLI, and registry tooling reject
//! malformed metadata before build or verification commands run, but it is not
//! part of the trusted base. Theorem acceptance remains with canonical proof
//! certificates, the Rust kernel verdict, and independent source-free checker
//! verdicts.
//!
//! Manifest validation is deliberately lexical and metadata-only. It does not
//! read source files, read certificate files, compare artifact bytes, execute
//! checkers, contact registries, resolve latest versions, query the network, or
//! load plugins. In particular, `npa-package` does not read source or
//! certificate files for proof acceptance; later CLI commands may compare file
//! hashes or invoke checkers, but those results are separate generated
//! artifacts.
//! CLR-03 package locks are also orchestration artifacts: `npa-package` can
//! build, parse, and serialize their canonical JSON identity data from a
//! validated manifest plus certificate bytes, but proof acceptance still
//! depends on canonical certificate bytes and checker verdicts.
//!
//! CLI implementers should use the structured error API instead of parsing
//! [`std::fmt::Display`] strings. [`PackageManifestError`] exposes stable
//! [`PackageManifestErrorKind`], [`PackageManifestErrorReason`], manifest path,
//! field, expected value, and actual value fields. [`validate_manifest_source_report`]
//! wraps the same deterministic pass ordering in a report-style API for callers
//! that want to present validation diagnostics without treating display text as
//! a contract.
//!
//! # Minimal manifest example
//!
//! ```rust
//! use npa_package::{parse_and_validate_manifest_str, PACKAGE_MANIFEST_SCHEMA};
//!
//! let source = format!(
//!     r#"schema = "{PACKAGE_MANIFEST_SCHEMA}"
//! package = "fixture-minimal"
//! version = "0.1.0"
//! core_spec = "npa.core.v0.1"
//! kernel_profile = "npa.kernel.v0.1"
//! certificate_format = "npa.certificate.canonical.v0.1"
//! checker_profile = "npa.checker.reference.v0.1"
//!
//! [policy]
//! allow_custom_axioms = false
//! allowed_axioms = []
//!
//! [[modules]]
//! module = "Fixture.Minimal"
//! source = "Fixture/Minimal/source.npa"
//! certificate = "Fixture/Minimal/certificate.npcert"
//! imports = []
//! expected_source_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
//! expected_certificate_file_hash = "sha256:1111111111111111111111111111111111111111111111111111111111111111"
//! expected_export_hash = "sha256:2222222222222222222222222222222222222222222222222222222222222222"
//! expected_axiom_report_hash = "sha256:3333333333333333333333333333333333333333333333333333333333333333"
//! expected_certificate_hash = "sha256:4444444444444444444444444444444444444444444444444444444444444444"
//! definitions = []
//! theorems = ["id"]
//! axioms = []
//! "#
//! );
//!
//! let validated = parse_and_validate_manifest_str(&source)?;
//! assert_eq!(validated.manifest().package.as_str(), "fixture-minimal");
//! assert_eq!(validated.graph().topological_order, vec![0]);
//! # Ok::<(), npa_package::PackageManifestError>(())
//! ```
//!
//! # Structured errors for CLI diagnostics
//!
//! ```rust
//! use npa_package::{
//!     validate_manifest_source_report, PackageManifestErrorKind,
//!     PackageManifestErrorReason,
//! };
//!
//! let report = validate_manifest_source_report(
//!     r#"schema = "npa.package.v0.1"
//! trusted_status = "verified_by_certificate"
//! "#,
//! );
//! let error = report.first_error().unwrap();
//! assert_eq!(error.kind, PackageManifestErrorKind::Schema);
//! assert_eq!(error.reason_code, PackageManifestErrorReason::UnknownField);
//! assert_eq!(error.path, "$");
//! assert_eq!(error.field.as_deref(), Some("trusted_status"));
//! ```

#![deny(missing_docs)]

pub mod artifact_ledger;
pub mod artifacts;
pub mod audit_cache;
pub mod audit_selection;
pub mod axiom_report;
pub mod build_check_cache;
pub mod error;
pub mod export_summary;
pub mod gate_plan;
pub mod graph;
pub mod hash;
pub mod incremental_projection;
mod json;
pub mod l2_acceptance;
pub mod l2_acceptance_v2;
pub mod l2_namespace_transport;
pub mod l2_review;
pub mod lock;
pub mod manifest;
pub mod name;
pub mod path;
pub mod promotion_plan;
pub mod promotion_registry;
pub mod promotion_transaction;
pub mod proof_replay;
pub mod publish_plan;
pub mod registry;
pub mod schema;
pub mod theorem_index;
pub mod theorem_premise_report;
pub mod validate;
pub mod verified_high_trust;

pub use artifact_ledger::{
    parse_package_artifact_ledger_metadata, refresh_package_artifact_ledger_metadata,
    PackageArtifactLedgerDeclaration, PackageArtifactLedgerDeclarationKind,
    PackageArtifactLedgerMetadata, PackageArtifactLedgerMetadataError,
    PackageArtifactLedgerMetadataErrorReason, PackageArtifactLedgerMetadataRefreshInput,
    PACKAGE_ARTIFACT_LEDGER_METADATA_SCHEMA,
};
pub use artifacts::{
    PackageArtifactFileReference, PackageArtifactOrigin, PackageArtifactPolicy,
    PackageAxiomReference, PackageCheckerMode, PackageCheckerSummary, PackageGlobalRef,
    PackageGlobalRefView, PackageReleaseEvidenceKind, PackageReleaseIdentity,
    PackageReleaseVerifierIdentity,
};
pub use audit_cache::{
    package_audit_cache_key, package_audit_cache_key_material,
    package_audit_direct_imports_for_entry, package_audit_disk_memo_key,
    package_audit_disk_memo_key_input, package_audit_disk_memo_result_entry_json,
    package_audit_graph_inventory, package_audit_process_memo_key, package_audit_result_entry_json,
    package_import_context_export_cache_entry_json, package_import_context_export_cache_key,
    package_reference_summary_cache_entry_json, package_reference_summary_cache_key,
    package_reference_summary_cache_key_input, parse_package_audit_disk_memo_result_entry_json,
    parse_package_audit_result_entry_json, parse_package_import_context_export_cache_entry_json,
    parse_package_reference_summary_cache_entry_json,
    validate_package_audit_disk_memo_result_entry, validate_package_audit_result_entry,
    validate_package_import_context_export_cache_entry,
    validate_package_reference_summary_cache_entry, PackageAuditCacheKeyInput,
    PackageAuditCachedStatus, PackageAuditCheckerIdentity, PackageAuditGraphInventory,
    PackageAuditImportIdentity, PackageAuditResultEntry, PackageImportContextExportCacheEntry,
    PackageImportContextExportCacheKeyInput, PackageImportContextExportData,
    PackageReferenceSummaryCacheEntry, PACKAGE_AUDIT_CACHE_LAYOUT_DIR, PACKAGE_AUDIT_CACHE_SCHEMA,
    PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR, PACKAGE_AUDIT_DISK_MEMO_RESULT_SCHEMA,
    PACKAGE_AUDIT_DISK_MEMO_SCHEMA, PACKAGE_AUDIT_PROCESS_MEMO_SCHEMA, PACKAGE_AUDIT_RESULT_SCHEMA,
    PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_ENTRY_SCHEMA,
    PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_LAYOUT_DIR, PACKAGE_IMPORT_CONTEXT_EXPORT_CACHE_SCHEMA,
    PACKAGE_REFERENCE_SUMMARY_CACHE_ENTRY_SCHEMA, PACKAGE_REFERENCE_SUMMARY_CACHE_LAYOUT_DIR,
    PACKAGE_REFERENCE_SUMMARY_CACHE_SCHEMA, PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA,
};
pub use audit_selection::{
    package_lock_reverse_dependencies, package_lock_topological_layers,
    select_package_audit_modules, select_package_cache_aware_live_modules, PackageAuditChangeKind,
    PackageAuditChangedModule, PackageAuditSelectedModule, PackageAuditSelection,
    PackageAuditSelectionReason, PackageCacheAwareLiveModule, PackageCacheAwareLiveReason,
    PackageCacheAwareLiveSelection, PackageTopologicalLayers,
};
pub use axiom_report::{
    compute_package_axiom_report_hash, package_axiom_report_incremental_projection_plan,
    package_axiom_report_summary, parse_package_axiom_report_json, validate_package_axiom_report,
    PackageAxiomPolicyStatus, PackageAxiomPolicyStatusKind, PackageAxiomPolicyViolation,
    PackageAxiomPolicyViolationReason, PackageAxiomReport,
    PackageAxiomReportIncrementalProjectionInput, PackageAxiomReportModule,
    PackageAxiomReportSummary,
};
pub use build_check_cache::{
    package_build_check_cache_key, package_build_check_cache_key_material,
    package_build_check_result_entry_json, parse_package_build_check_result_entry_json,
    validate_package_build_check_result_entry, PackageBuildCheckCacheKeyInput,
    PackageBuildCheckCachedStatus, PackageBuildCheckImportIdentity, PackageBuildCheckResultEntry,
    PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR, PACKAGE_BUILD_CHECK_CACHE_SCHEMA,
    PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
};
pub use error::{
    PackageArtifactError, PackageArtifactErrorKind, PackageArtifactErrorReason,
    PackageArtifactResult, PackageLockError, PackageLockErrorKind, PackageLockErrorReason,
    PackageLockResult, PackageManifestError, PackageManifestErrorKind, PackageManifestErrorReason,
    PackageManifestResult,
};
pub use export_summary::{
    compute_package_verified_export_summary_hash,
    package_verified_export_summary_incremental_projection_plan,
    parse_package_verified_export_summary_json, validate_package_verified_export_summary,
    validate_package_verified_export_summary_against_lock, PackageVerifiedExportSummary,
    PackageVerifiedExportSummaryModule, PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH, PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY,
};
pub use gate_plan::{
    package_gate_plan_from_paths, PackageGateImpactClass, PackageGatePlan,
    PACKAGE_GATE_PLAN_TRUST_BOUNDARY_NOTE,
};
pub use graph::{
    package_graph_dependent_closure, package_graph_transitive_dependencies, resolve_package_graph,
    PackageGraph, ResolvedModuleImport, ResolvedModuleImportKind,
};
pub use hash::{
    format_package_hash, package_file_hash, parse_package_hash, PackageHash, PackageHashBytes,
};
pub use incremental_projection::{
    PackageIncrementalProjectionMode, PackageIncrementalProjectionModule,
    PackageIncrementalProjectionPlan, PACKAGE_INCREMENTAL_PROJECTION_TRUST_BOUNDARY,
};
pub use l2_acceptance::{
    compute_l2_review_input_hash, parse_l2_acceptance_json, parse_l2_acceptance_policy_json,
    validate_l2_acceptance, validate_l2_acceptance_policy, L2Acceptance, L2AcceptanceApproval,
    L2AcceptanceAuthority, L2AcceptanceAuthorityStatus, L2AcceptanceEntry, L2AcceptancePolicy,
    L2_ACCEPTANCE_LEVEL, L2_ACCEPTANCE_REVIEW_PROTOCOL, L2_ACCEPTANCE_REVIEW_PROTOCOL_V2,
    L2_ACCEPTANCE_VALIDATOR_PROFILE, L2_ACCEPTANCE_VALIDATOR_PROFILE_V2,
};
pub use l2_acceptance_v2::{
    merge_l2_acceptance_v2_entries, parse_l2_acceptance_v2_json, validate_l2_acceptance_v2,
    L2AcceptanceApprovalV2, L2AcceptanceEntryV2, L2AcceptanceReviewReportRef, L2AcceptanceV2,
};
pub use l2_namespace_transport::{
    l2_transport_derived_mapping_hash, l2_transport_module_declaration_names,
    l2_transport_module_projection, l2_transport_module_projection_subset,
    l2_transport_normalized_closure_hash, parse_l2_namespace_transport_attestation_json,
    parse_l2_namespace_transport_policy_json, parse_l2_namespace_transport_request_json,
    L2NamespaceTransportAttestation, L2NamespaceTransportPolicy, L2NamespaceTransportRequest,
    L2TransportAttestationChangedPath, L2TransportAttestationModulePair,
    L2TransportAttestationTheoremPair, L2TransportDeclarationRename, L2TransportEndpoint,
    L2TransportModuleMapping, L2TransportModuleRole, L2TransportPackageIdentity,
};
pub use l2_review::{
    compute_l2_review_input_v2_hash, parse_l2_review_input_json, parse_l2_review_report_json,
    validate_l2_review_input, validate_l2_review_report, L2ReviewCheckDecision,
    L2ReviewCheckResult, L2ReviewInput, L2ReviewInputImport, L2ReviewInputPolicy,
    L2ReviewInputSource, L2ReviewReport,
};
pub use lock::{
    build_package_lock_from_artifacts,
    build_package_lock_from_artifacts_allowing_local_hash_updates,
    build_package_lock_from_package_root,
    build_package_lock_from_package_root_allowing_local_hash_updates, build_package_lock_graph,
    parse_package_lock_json, validate_observed_package_lock_against_manifest_graph,
    validate_package_lock_against_manifest_graph, validate_package_lock_manifest,
    PackageLockArtifact, PackageLockEntry, PackageLockEntryOrigin, PackageLockGraph,
    PackageLockImport, PackageLockManifest, PackageLockManifestReference,
    PackageLockResolvedImport,
};
pub use manifest::{
    parse_manifest_str, PackageExternalImport, PackageManifest, PackageModule, PackagePolicy,
    PackageVersion,
};
pub use name::{
    validate_canonical_axiom_name, validate_canonical_declaration_name,
    validate_canonical_module_name, validate_package_id, PackageId,
};
pub use path::{validate_package_path, PackagePath};
pub use promotion_plan::{
    mathlib_promotion_plan_hash, mathlib_promotion_route_id, parse_mathlib_promotion_plan_json,
    validate_mathlib_promotion_plan, MathlibPromotionPlan, PromotionGovernance,
    PromotionPackageSnapshot, PromotionPlanDependencyMapping, PromotionPlanEndpoint,
    PromotionPlanExport, PromotionPlanRename, PromotionPlanSelectedModule, PromotionPlanTheorem,
    PromotionTargetSnapshot,
};
pub use promotion_registry::{
    lookup_promotion_origin, parse_promotion_origin_registry_json,
    promotion_legacy_target_reservation_id, promotion_origin_registry_hash,
    validate_promotion_origin_registry, validate_promotion_origin_registry_transition,
    PromotionAcceptanceEvidence, PromotionAuditLocation, PromotionDeclarationRename,
    PromotionEvidence, PromotionLegacyTargetReservation, PromotionLifecycle, PromotionModuleRoute,
    PromotionOriginEntry, PromotionOriginLookup, PromotionOriginRegistry, PromotionReservedTheorem,
    PromotionRouteTheorem, PromotionSourceModule, PromotionSourceOrigin, PromotionTargetRevision,
    PromotionTransportEvidence, MATHLIB_PROMOTION_REGISTRY_ID, MATHLIB_PROMOTION_REGISTRY_PATH,
};
pub use promotion_transaction::{
    parse_promotion_transaction_json, promotion_transaction_hash, promotion_transaction_path_hash,
    validate_promotion_transaction, PromotionOldFile, PromotionReplacementState,
    PromotionTransactionJournal, PromotionTransactionPhase, PromotionTransactionRow,
    PromotionTransactionState,
};
pub use proof_replay::{
    parse_package_proof_replay, PackageProofReplay, PackageProofReplayStep,
    PACKAGE_PROOF_REPLAY_PROFILE, PACKAGE_PROOF_REPLAY_SCHEMA,
};
pub use publish_plan::{
    build_package_downstream_import_bundle, build_package_publish_artifacts,
    compute_package_publish_plan_hash, package_checksum_only_signature_policy,
    package_publish_plan_incremental_projection_plan, parse_package_publish_plan_json,
    validate_package_publish_plan, PackageDownstreamImportBundle,
    PackageDownstreamImportBundleInput, PackageDownstreamImportModule, PackagePublishArtifact,
    PackagePublishArtifactListInput, PackagePublishArtifactRole, PackagePublishPlan,
    PackagePublishRelease, PackagePublishReleaseReference, PackagePublishSummary,
    PackageSignaturePolicy, PACKAGE_PUBLISH_PLAN_PATH,
};
pub use registry::{
    build_package_registry_modules, parse_registry_module_json, validate_registry_module,
    PackageRegistryArtifactHashes, PackageRegistryCheckerResult, PackageRegistryCheckerStatus,
    PackageRegistryImport, PackageRegistryModule, PackageRegistryModuleSeedInput,
};
pub use schema::{
    CERTIFICATE_FORMAT_CANONICAL_V0_1, CHECKER_PROFILE_REFERENCE_V0_1, CORE_SPEC_V0_1,
    KERNEL_PROFILE_V0_1, L2_ACCEPTANCE_POLICY_SCHEMA, L2_ACCEPTANCE_SCHEMA,
    MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA, MATHLIB_PROMOTION_PLAN_SCHEMA,
    MATHLIB_PROMOTION_TRANSACTION_SCHEMA, PACKAGE_AXIOM_REPORT_SCHEMA, PACKAGE_LOCK_SCHEMA,
    PACKAGE_MANIFEST_SCHEMA, PACKAGE_PUBLISH_PLAN_SCHEMA, PACKAGE_THEOREM_INDEX_SCHEMA,
    PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA, REGISTRY_MODULE_SCHEMA,
};
pub use theorem_index::{
    compute_package_theorem_index_hash, package_theorem_index_incremental_projection_plan,
    package_theorem_index_summary, parse_package_theorem_index_json,
    validate_package_theorem_index, PackageTheoremIndex, PackageTheoremIndexArtifact,
    PackageTheoremIndexEntry, PackageTheoremIndexKind, PackageTheoremIndexMode,
    PackageTheoremIndexSummary, PackageTheoremStatement,
    PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE,
};
pub use theorem_premise_report::*;
pub use validate::{
    parse_and_validate_manifest_str, validate_manifest, validate_manifest_report,
    validate_manifest_source_report, validate_manifest_with_options, validate_package_version,
    PackageManifestValidationOptions, PackageManifestValidationReport, ValidatedPackageManifest,
};
pub use verified_high_trust::{
    compute_package_verified_high_trust_hash, parse_package_verified_high_trust_json,
    validate_package_verified_high_trust, PackageVerifiedHighTrust,
    PackageVerifiedHighTrustAuxiliaryKind, PackageVerifiedHighTrustAuxiliaryResult,
    PackageVerifiedHighTrustCheckerIdentity, PackageVerifiedHighTrustGeneratedBy,
    PACKAGE_VERIFIED_HIGH_TRUST_PATH,
};
