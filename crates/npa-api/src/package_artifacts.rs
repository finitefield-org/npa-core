use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{
    AxiomRef, DeclPayload, ExportEntry, ExportKind, GlobalRef, Hash, Name, NameId, TermId,
    TermNode, VerifiedModule,
};
use npa_package::{
    build_package_lock_from_artifacts, format_package_hash, package_audit_direct_imports_for_entry,
    package_axiom_report_summary, package_file_hash, package_lock_reverse_dependencies,
    package_theorem_index_summary, validate_package_path, PackageArtifactError,
    PackageArtifactFileReference, PackageArtifactOrigin, PackageArtifactPolicy,
    PackageArtifactResult, PackageAxiomPolicyStatus, PackageAxiomPolicyStatusKind,
    PackageAxiomPolicyViolation, PackageAxiomPolicyViolationReason, PackageAxiomReference,
    PackageAxiomReport, PackageAxiomReportModule, PackageCheckerMode, PackageCheckerSummary,
    PackageGlobalRef, PackageGlobalRefView, PackageHash, PackageId, PackageLockArtifact,
    PackageLockEntry, PackageLockEntryOrigin, PackageLockError, PackageLockErrorKind,
    PackageLockErrorReason, PackageLockManifest, PackageLockManifestReference, PackagePath,
    PackageTheoremIndex, PackageTheoremIndexArtifact, PackageTheoremIndexEntry,
    PackageTheoremIndexKind, PackageTheoremIndexMode, PackageTheoremStatement,
    PackageVerifiedExportSummary, PackageVerifiedExportSummaryModule, PackageVersion,
    ValidatedPackageManifest, PACKAGE_AXIOM_REPORT_SCHEMA,
    PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE, PACKAGE_THEOREM_INDEX_SCHEMA,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA, PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY,
};

use crate::package_verifier::{
    verify_package_fast_source_free_with_modules, verify_package_reference_source_free,
    PackageCertificateArtifact, PackageModuleVerificationResult, PackageModuleVerificationStatus,
    PackageVerificationError, PackageVerificationErrorKind, PackageVerificationErrorReason,
    PackageVerificationMode, PackageVerificationReport, PackageVerificationResult,
    PackageVerificationStatus, PackageVerificationVerdictSource, PackageVerifiedModuleRecord,
};

/// Whether package artifact extraction should include reference-checker summaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageArtifactReferenceSummaryMode {
    /// Collect only fast-kernel summaries required to obtain verified modules.
    Omit,
    /// Also run the CLR-03 source-free reference checker and project its summary.
    Include,
}

/// Source-free input used to extract package artifact metadata.
#[derive(Clone, Debug)]
pub struct PackageArtifactExtractionInput<'a> {
    /// Validated package manifest.
    pub validated: &'a ValidatedPackageManifest,
    /// Package-relative path to the manifest bytes used by the lock.
    pub manifest_path: PackagePath,
    /// Exact manifest bytes used to check lock freshness.
    pub manifest_bytes: &'a [u8],
    /// Parsed generated package lock.
    pub package_lock: &'a PackageLockManifest,
    /// Certificate artifacts loaded by the caller.
    pub certificates: Vec<PackageCertificateArtifact<'a>>,
    /// Reference-checker summary mode.
    pub reference_summaries: PackageArtifactReferenceSummaryMode,
}

/// Stable identity key for a verified package module.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PackageArtifactVerifiedModuleKey {
    /// Module name.
    pub module: Name,
    /// Verified module export hash.
    pub export_hash: PackageHash,
    /// Verified module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Verified module payload available to later package artifact projections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageArtifactVerifiedModule {
    /// Stable identity key.
    pub key: PackageArtifactVerifiedModuleKey,
    /// Local or external package origin.
    pub origin: PackageArtifactOrigin,
    /// Certificate file identity.
    pub certificate: PackageArtifactFileReference,
    /// Verified module axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Kernel-verified module data.
    pub verified_module: VerifiedModule,
}

/// Source-free extraction output shared by CLR-05 artifact generators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageArtifactExtraction {
    /// Manifest reference checked against the package lock.
    pub manifest: PackageLockManifestReference,
    /// Verified modules keyed by module, export hash, and certificate hash.
    pub verified_modules: BTreeMap<PackageArtifactVerifiedModuleKey, PackageArtifactVerifiedModule>,
    /// Verified module keys in package-lock topological order.
    pub topological_order: Vec<PackageArtifactVerifiedModuleKey>,
    /// Checker summaries with explicit fast/reference mode labels.
    pub checker_summaries: Vec<PackageCheckerSummary>,
    /// Fast source-free verifier report used to collect verified modules.
    pub fast_verification_report: PackageVerificationReport,
    /// Optional CLR-03 source-free reference checker report.
    pub reference_verification_report: Option<PackageVerificationReport>,
}

/// Owned certificate bytes retained by a process-local package audit snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditCertificateInput {
    /// Package-relative certificate path.
    pub path: PackagePath,
    /// Exact certificate bytes at [`Self::path`].
    pub bytes: Vec<u8>,
}

/// Certificate artifact buffer retained by a process-local package audit snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditCertificateBuffer {
    /// Package-relative certificate path.
    pub path: PackagePath,
    /// Exact SHA-256 hash of [`Self::bytes`].
    pub file_hash: PackageHash,
    /// Exact certificate bytes at [`Self::path`].
    pub bytes: Vec<u8>,
}

/// Stable input hashes used to decide whether a package audit snapshot is reusable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditProjectionInputHashes {
    /// Exact manifest file hash used by the snapshot.
    pub manifest_file_hash: PackageHash,
    /// Exact package-lock file hash used by the snapshot.
    pub package_lock_file_hash: PackageHash,
    /// Deterministic package policy hash used by axiom-report projection.
    pub policy_hash: PackageHash,
    /// Exact certificate file hashes keyed by package-relative path.
    pub certificate_file_hashes: BTreeMap<PackagePath, PackageHash>,
}

/// Source-free input for building a process-local package audit snapshot.
pub struct PackageAuditSnapshotInput<'a> {
    /// Validated package manifest.
    pub validated: &'a ValidatedPackageManifest,
    /// Package-relative manifest path used by the package lock.
    pub manifest_path: PackagePath,
    /// Exact manifest bytes used to check lock freshness.
    pub manifest_bytes: &'a [u8],
    /// Parsed generated package lock.
    pub package_lock_manifest: &'a PackageLockManifest,
    /// Exact generated package-lock file identity.
    pub package_lock: PackageArtifactFileReference,
    /// Owned certificate artifacts loaded by the caller.
    pub certificates: Vec<PackageAuditCertificateInput>,
    /// Reference-checker summary mode.
    pub reference_summaries: PackageArtifactReferenceSummaryMode,
}

/// Process-local source-free package snapshot shared by projection checks.
///
/// This snapshot is an optimization boundary only. It is never serialized as
/// proof evidence, does not carry proof acceptance status, and is built solely
/// from the package manifest, package lock, certificate bytes, and package
/// policy supplied by the caller.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageAuditSnapshot {
    /// Validated package manifest used by projections.
    pub validated: ValidatedPackageManifest,
    /// Manifest identity checked against the package lock.
    pub manifest: PackageLockManifestReference,
    /// Parsed generated package lock.
    pub package_lock_manifest: PackageLockManifest,
    /// Exact generated package-lock file identity.
    pub package_lock: PackageArtifactFileReference,
    /// Package policy copied from the validated manifest.
    pub policy: PackageArtifactPolicy,
    /// Deterministic hash of [`Self::policy`].
    pub policy_hash: PackageHash,
    /// Certificate artifact buffers retained for in-process reuse.
    pub certificate_artifacts: Vec<PackageAuditCertificateBuffer>,
    /// Decoded, kernel-verified module records keyed by stable module identity.
    pub decoded_module_records:
        BTreeMap<PackageArtifactVerifiedModuleKey, PackageArtifactVerifiedModule>,
    /// Verified export summary module records projected once from decoded modules.
    pub verified_export_summary_records: Vec<PackageVerifiedExportSummaryModule>,
    /// Verified module keys in package-lock topological order.
    pub topological_order: Vec<PackageArtifactVerifiedModuleKey>,
    /// Direct reverse dependencies from the package lock.
    pub reverse_dependency_graph: BTreeMap<Name, Vec<Name>>,
    /// Input hashes used by projection reuse checks.
    pub projection_input_hashes: PackageAuditProjectionInputHashes,
    /// Checker summaries collected by the snapshot builder.
    pub checker_summaries: Vec<PackageCheckerSummary>,
    /// Fast source-free verifier report used to collect decoded modules.
    pub fast_verification_report: PackageVerificationReport,
    /// Optional CLR-03 source-free reference checker report.
    pub reference_verification_report: Option<PackageVerificationReport>,
}

/// Error produced while building a package audit snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackageAuditSnapshotBuildError {
    /// Source-free verification failed.
    Verification(PackageVerificationError),
    /// Snapshot metadata projection or reuse validation failed.
    Artifact(PackageArtifactError),
}

impl From<PackageVerificationError> for PackageAuditSnapshotBuildError {
    fn from(error: PackageVerificationError) -> Self {
        Self::Verification(error)
    }
}

impl From<PackageArtifactError> for PackageAuditSnapshotBuildError {
    fn from(error: PackageArtifactError) -> Self {
        Self::Artifact(error)
    }
}

/// Result type for package audit snapshot construction.
pub type PackageAuditSnapshotBuildResult<T> = Result<T, PackageAuditSnapshotBuildError>;

/// Build a process-local source-free package audit snapshot.
///
/// The caller supplies all bytes. This function does not read source, replay,
/// metadata, theorem index, AI traces, hidden caches, registries, network, or
/// host-local sidecars. Stale package locks, stale certificate file hashes,
/// path escapes, and projection policy mismatches are rejected before the
/// returned snapshot can be reused.
pub fn build_package_audit_snapshot_source_free(
    input: PackageAuditSnapshotInput<'_>,
) -> PackageAuditSnapshotBuildResult<PackageAuditSnapshot> {
    ensure_snapshot_path(&input.manifest_path, "manifest.path")?;
    ensure_snapshot_path(&input.package_lock.path, "package_lock.path")?;
    for (index, certificate) in input.certificates.iter().enumerate() {
        ensure_snapshot_path(&certificate.path, format!("certificates[{index}].path"))?;
    }

    let certificate_artifacts = snapshot_certificate_artifacts(input.certificates);
    let borrowed_certificates = borrowed_snapshot_certificate_artifacts(&certificate_artifacts);
    let extraction = extract_package_artifacts_source_free(PackageArtifactExtractionInput {
        validated: input.validated,
        manifest_path: input.manifest_path,
        manifest_bytes: input.manifest_bytes,
        package_lock: input.package_lock_manifest,
        certificates: borrowed_certificates,
        reference_summaries: input.reference_summaries,
    })?;

    let policy = package_policy_from_manifest(input.validated);
    let policy_hash = package_audit_policy_hash(&policy);
    let fast_extraction = fast_only_extraction_from(&extraction);
    let verified_export_summary_records = project_package_verified_export_summary_modules(
        input.package_lock_manifest,
        &fast_extraction,
    )?;
    let reverse_dependency_graph = package_lock_reverse_dependencies(input.package_lock_manifest)?;
    let projection_input_hashes = PackageAuditProjectionInputHashes {
        manifest_file_hash: package_file_hash(input.manifest_bytes),
        package_lock_file_hash: input.package_lock.file_hash,
        policy_hash,
        certificate_file_hashes: certificate_artifacts
            .iter()
            .map(|artifact| (artifact.path.clone(), artifact.file_hash))
            .collect(),
    };
    if projection_input_hashes.policy_hash != policy_hash {
        return Err(PackageArtifactError::summary_mismatch(
            "projection_input_hashes.policy_hash",
            "policy_hash",
            format_package_hash(&policy_hash),
            format_package_hash(&projection_input_hashes.policy_hash),
        )
        .into());
    }

    Ok(PackageAuditSnapshot {
        validated: input.validated.clone(),
        manifest: extraction.manifest.clone(),
        package_lock_manifest: input.package_lock_manifest.clone(),
        package_lock: input.package_lock,
        policy,
        policy_hash,
        certificate_artifacts,
        decoded_module_records: extraction.verified_modules.clone(),
        verified_export_summary_records,
        topological_order: extraction.topological_order.clone(),
        reverse_dependency_graph,
        projection_input_hashes,
        checker_summaries: extraction.checker_summaries.clone(),
        fast_verification_report: extraction.fast_verification_report.clone(),
        reference_verification_report: extraction.reference_verification_report.clone(),
    })
}

impl PackageAuditSnapshot {
    /// Return extraction data matching the snapshot's checker summary mode.
    pub fn artifact_extraction(&self) -> PackageArtifactExtraction {
        PackageArtifactExtraction {
            manifest: self.manifest.clone(),
            verified_modules: self.decoded_module_records.clone(),
            topological_order: self.topological_order.clone(),
            checker_summaries: self.checker_summaries.clone(),
            fast_verification_report: self.fast_verification_report.clone(),
            reference_verification_report: self.reference_verification_report.clone(),
        }
    }

    /// Return a fast-summary-only extraction view used by standalone projections.
    pub fn fast_projection_extraction(&self) -> PackageArtifactExtraction {
        let mut extraction = self.artifact_extraction();
        extraction
            .checker_summaries
            .retain(|summary| summary.mode == PackageCheckerMode::Fast);
        extraction.reference_verification_report = None;
        extraction
    }

    /// Project the package axiom report from this snapshot.
    pub fn project_axiom_report(&self) -> PackageArtifactResult<PackageAxiomReport> {
        let manifest = self.validated.manifest();
        let extraction = self.fast_projection_extraction();
        project_package_axiom_report_source_free(PackageAxiomReportProjectionInput {
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            policy: self.policy.clone(),
            package_lock: self.package_lock.clone(),
            extraction: &extraction,
        })
    }

    /// Project the package theorem index from this snapshot.
    pub fn project_theorem_index(&self) -> PackageArtifactResult<PackageTheoremIndex> {
        let manifest = self.validated.manifest();
        let extraction = self.fast_projection_extraction();
        project_package_theorem_index_source_free(PackageTheoremIndexProjectionInput {
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            package_lock: self.package_lock.clone(),
            extraction: &extraction,
        })
    }

    /// Project the verified export summary from this snapshot.
    pub fn project_verified_export_summary(
        &self,
    ) -> PackageArtifactResult<PackageVerifiedExportSummary> {
        let manifest = self.validated.manifest();
        PackageVerifiedExportSummary {
            schema: PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA.to_owned(),
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            core_spec: manifest.core_spec.clone(),
            certificate_format: manifest.certificate_format.clone(),
            package_lock_hash: self.package_lock.file_hash,
            module_order: PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL.to_owned(),
            trusted: false,
            trust_boundary: PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY.to_owned(),
            modules: self.verified_export_summary_records.clone(),
            summary_hash: PackageHash::new([0_u8; 32]),
        }
        .with_computed_hash()
    }
}

fn ensure_snapshot_path(
    path: &PackagePath,
    error_path: impl Into<String>,
) -> PackageArtifactResult<()> {
    validate_package_path(path, error_path.into()).map_err(|error| {
        PackageArtifactError::invalid_path(
            error.path,
            error
                .actual_value
                .unwrap_or_else(|| path.as_str().to_owned()),
        )
    })
}

fn snapshot_certificate_artifacts(
    certificates: Vec<PackageAuditCertificateInput>,
) -> Vec<PackageAuditCertificateBuffer> {
    certificates
        .into_iter()
        .map(|certificate| PackageAuditCertificateBuffer {
            file_hash: package_file_hash(&certificate.bytes),
            path: certificate.path,
            bytes: certificate.bytes,
        })
        .collect()
}

fn borrowed_snapshot_certificate_artifacts(
    certificates: &[PackageAuditCertificateBuffer],
) -> Vec<PackageCertificateArtifact<'_>> {
    certificates
        .iter()
        .map(|certificate| PackageCertificateArtifact {
            path: certificate.path.clone(),
            bytes: certificate.bytes.as_slice(),
        })
        .collect()
}

fn package_policy_from_manifest(validated: &ValidatedPackageManifest) -> PackageArtifactPolicy {
    let manifest = validated.manifest();
    PackageArtifactPolicy {
        allow_custom_axioms: manifest.policy.allow_custom_axioms,
        allowed_axioms: manifest.policy.allowed_axioms.clone(),
    }
}

fn package_audit_policy_hash(policy: &PackageArtifactPolicy) -> PackageHash {
    let mut bytes = b"npa.package.audit.snapshot.policy.v0.1\n".to_vec();
    bytes.extend(if policy.allow_custom_axioms {
        b"allow_custom_axioms=true\n".as_slice()
    } else {
        b"allow_custom_axioms=false\n".as_slice()
    });
    let mut allowed_axioms = policy.allowed_axioms.clone();
    allowed_axioms.sort();
    for axiom in allowed_axioms {
        bytes.extend(b"allowed_axiom=");
        bytes.extend(axiom.as_dotted().as_bytes());
        bytes.push(b'\n');
    }
    package_file_hash(&bytes)
}

fn fast_only_extraction_from(extraction: &PackageArtifactExtraction) -> PackageArtifactExtraction {
    let mut fast = extraction.clone();
    fast.checker_summaries
        .retain(|summary| summary.mode == PackageCheckerMode::Fast);
    fast.reference_verification_report = None;
    fast
}

/// Source-free input for projecting a package axiom report artifact.
#[derive(Clone, Debug)]
pub struct PackageAxiomReportProjectionInput<'a> {
    /// Package id copied from the validated package manifest.
    pub package: PackageId,
    /// Package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Package axiom policy copied from the validated package manifest.
    pub policy: PackageArtifactPolicy,
    /// Exact generated package lock file identity used for extraction.
    pub package_lock: PackageArtifactFileReference,
    /// Source-free verified module extraction.
    pub extraction: &'a PackageArtifactExtraction,
}

/// Source-free input for projecting a package theorem index artifact.
#[derive(Clone, Debug)]
pub struct PackageTheoremIndexProjectionInput<'a> {
    /// Package id copied from the validated package manifest.
    pub package: PackageId,
    /// Package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Exact generated package lock file identity used for extraction.
    pub package_lock: PackageArtifactFileReference,
    /// Source-free verified module extraction.
    pub extraction: &'a PackageArtifactExtraction,
}

/// Source-free input for projecting a verified export summary artifact.
#[derive(Clone, Debug)]
pub struct PackageVerifiedExportSummaryProjectionInput<'a> {
    /// Package id copied from the validated package manifest.
    pub package: PackageId,
    /// Package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Core specification profile copied from the validated package manifest.
    pub core_spec: String,
    /// Certificate format profile copied from the validated package manifest.
    pub certificate_format: String,
    /// Parsed generated package lock.
    pub package_lock_manifest: &'a PackageLockManifest,
    /// Exact generated package lock file identity used for extraction.
    pub package_lock: PackageArtifactFileReference,
    /// Source-free verified module extraction.
    pub extraction: &'a PackageArtifactExtraction,
}

/// Extract source-free package artifact metadata from manifest, lock, and certificates.
///
/// This adapter does not read files. The caller supplies manifest bytes,
/// package-lock data, and certificate bytes; source, replay, metadata, theorem
/// index, AI traces, registry data, and network state are outside this API.
pub fn extract_package_artifacts_source_free<'a>(
    input: PackageArtifactExtractionInput<'a>,
) -> PackageVerificationResult<PackageArtifactExtraction> {
    let fast = verify_package_fast_source_free_with_modules(
        input.validated,
        input.package_lock,
        input.certificates.clone(),
    )?;
    ensure_report_passed(&fast.report)?;
    ensure_package_lock_current(&input)?;

    let mut checker_summaries = checker_summaries_from_report(
        &fast.report,
        PackageCheckerMode::Fast,
        PackageVerificationVerdictSource::FastKernelCertificateVerifier.as_str(),
        PackageVerificationMode::FastKernel.as_str(),
    );
    let reference_verification_report =
        if input.reference_summaries == PackageArtifactReferenceSummaryMode::Include {
            let report = verify_package_reference_source_free(
                input.validated,
                input.package_lock,
                input.certificates,
            )?;
            ensure_report_passed(&report)?;
            checker_summaries.extend(checker_summaries_from_report(
                &report,
                PackageCheckerMode::Reference,
                PackageVerificationVerdictSource::ReferenceChecker.as_str(),
                &input.validated.manifest().checker_profile,
            ));
            Some(report)
        } else {
            None
        };

    let (verified_modules, topological_order) = verified_module_collection(fast.verified_modules)?;

    Ok(PackageArtifactExtraction {
        manifest: PackageLockManifestReference {
            path: input.manifest_path,
            file_hash: package_file_hash(input.manifest_bytes),
        },
        verified_modules,
        topological_order,
        checker_summaries,
        fast_verification_report: fast.report,
        reference_verification_report,
    })
}

/// Project `npa.package.axiom_report.v0.1` from verified package modules.
///
/// The projection reads only source-free extraction output: verified
/// certificates, package-lock identities, checker summaries, and the package
/// policy supplied by the caller. It never reads source, replay, meta, AI, or
/// theorem-search sidecars.
pub fn project_package_axiom_report_source_free(
    input: PackageAxiomReportProjectionInput<'_>,
) -> PackageArtifactResult<PackageAxiomReport> {
    let modules = project_package_axiom_report_modules(input.extraction, &input.policy)?;
    PackageAxiomReport {
        schema: PACKAGE_AXIOM_REPORT_SCHEMA.to_owned(),
        package: input.package,
        version: input.version,
        manifest: PackageArtifactFileReference {
            path: input.extraction.manifest.path.clone(),
            file_hash: input.extraction.manifest.file_hash,
        },
        package_lock: input.package_lock,
        policy: input.policy,
        summary: package_axiom_report_summary(&modules),
        modules,
        checker_summaries: input.extraction.checker_summaries.clone(),
        package_axiom_report_hash: PackageHash::new([0_u8; 32]),
    }
    .with_computed_hash()
}

/// Project `npa.package.axiom_report.v0.1` using package identity and policy
/// from a validated manifest.
pub fn project_package_axiom_report_from_extraction(
    validated: &ValidatedPackageManifest,
    extraction: &PackageArtifactExtraction,
    package_lock: PackageArtifactFileReference,
) -> PackageArtifactResult<PackageAxiomReport> {
    let manifest = validated.manifest();
    project_package_axiom_report_source_free(PackageAxiomReportProjectionInput {
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        policy: PackageArtifactPolicy {
            allow_custom_axioms: manifest.policy.allow_custom_axioms,
            allowed_axioms: manifest.policy.allowed_axioms.clone(),
        },
        package_lock,
        extraction,
    })
}

/// Project `npa.package.theorem_index.v0.1` from verified package modules.
///
/// The projection reads only source-free extraction output: verified
/// certificates, package-lock identities, and checker summaries. It does not
/// read source, replay, meta, theorem graph scores, AI traces, registry data,
/// or theorem-search sidecars.
pub fn project_package_theorem_index_source_free(
    input: PackageTheoremIndexProjectionInput<'_>,
) -> PackageArtifactResult<PackageTheoremIndex> {
    let entries = project_package_theorem_index_entries(input.extraction)?;
    PackageTheoremIndex {
        schema: PACKAGE_THEOREM_INDEX_SCHEMA.to_owned(),
        package: input.package,
        version: input.version,
        manifest: PackageArtifactFileReference {
            path: input.extraction.manifest.path.clone(),
            file_hash: input.extraction.manifest.file_hash,
        },
        package_lock: input.package_lock,
        index_profile: PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE.to_owned(),
        summary: package_theorem_index_summary(&entries),
        entries,
        checker_summaries: input.extraction.checker_summaries.clone(),
        theorem_index_hash: PackageHash::new([0_u8; 32]),
    }
    .with_computed_hash()
}

/// Project `npa.package.theorem_index.v0.1` using package identity from a
/// validated manifest.
pub fn project_package_theorem_index_from_extraction(
    validated: &ValidatedPackageManifest,
    extraction: &PackageArtifactExtraction,
    package_lock: PackageArtifactFileReference,
) -> PackageArtifactResult<PackageTheoremIndex> {
    let manifest = validated.manifest();
    project_package_theorem_index_source_free(PackageTheoremIndexProjectionInput {
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        package_lock,
        extraction,
    })
}

/// Project `npa.package.verified_export_summary.v0.1` from verified package modules.
///
/// The projection reads only package manifest identity, package lock identity,
/// and source-free certificate extraction output. It does not read source,
/// replay, meta, theorem index, AI trace, cache, registry, or network state.
pub fn project_package_verified_export_summary_source_free(
    input: PackageVerifiedExportSummaryProjectionInput<'_>,
) -> PackageArtifactResult<PackageVerifiedExportSummary> {
    let modules = project_package_verified_export_summary_modules(
        input.package_lock_manifest,
        input.extraction,
    )?;
    PackageVerifiedExportSummary {
        schema: PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA.to_owned(),
        package: input.package,
        version: input.version,
        core_spec: input.core_spec,
        certificate_format: input.certificate_format,
        package_lock_hash: input.package_lock.file_hash,
        module_order: PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL.to_owned(),
        trusted: false,
        trust_boundary: PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY.to_owned(),
        modules,
        summary_hash: PackageHash::new([0_u8; 32]),
    }
    .with_computed_hash()
}

/// Project a verified export summary using package identity from a validated manifest.
pub fn project_package_verified_export_summary_from_extraction(
    validated: &ValidatedPackageManifest,
    package_lock_manifest: &PackageLockManifest,
    package_lock: PackageArtifactFileReference,
    extraction: &PackageArtifactExtraction,
) -> PackageArtifactResult<PackageVerifiedExportSummary> {
    let manifest = validated.manifest();
    project_package_verified_export_summary_source_free(
        PackageVerifiedExportSummaryProjectionInput {
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            core_spec: manifest.core_spec.clone(),
            certificate_format: manifest.certificate_format.clone(),
            package_lock_manifest,
            package_lock,
            extraction,
        },
    )
}

fn project_package_verified_export_summary_modules(
    package_lock: &PackageLockManifest,
    extraction: &PackageArtifactExtraction,
) -> PackageArtifactResult<Vec<PackageVerifiedExportSummaryModule>> {
    let entries = package_lock
        .entries
        .iter()
        .map(|entry| (entry.module.clone(), entry))
        .collect::<BTreeMap<_, _>>();
    let mut modules = Vec::with_capacity(extraction.topological_order.len());
    for key in &extraction.topological_order {
        let module = extraction.verified_modules.get(key).ok_or_else(|| {
            projection_error(
                &key.module,
                "module",
                "verified module present in extraction",
                key.module.as_dotted(),
            )
        })?;
        let entry = entries.get(&key.module).ok_or_else(|| {
            projection_error(
                &key.module,
                "module",
                "package lock entry",
                key.module.as_dotted(),
            )
        })?;
        modules.push(project_package_verified_export_summary_module(
            extraction, module, entry,
        )?);
    }
    Ok(modules)
}

fn project_package_verified_export_summary_module(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    entry: &PackageLockEntry,
) -> PackageArtifactResult<PackageVerifiedExportSummaryModule> {
    Ok(PackageVerifiedExportSummaryModule {
        module: module.key.module.clone(),
        origin: module.origin,
        certificate: module.certificate.path.clone(),
        certificate_file_hash: module.certificate.file_hash,
        export_hash: module.key.export_hash,
        certificate_hash: module.key.certificate_hash,
        axiom_report_hash: module.axiom_report_hash,
        direct_imports: package_audit_direct_imports_for_entry(entry),
        exported_globals: project_export_summary_globals(module)?,
        module_axioms: project_export_summary_module_axioms(extraction, module)?,
        core_features: module
            .verified_module
            .axiom_report()
            .core_features
            .iter()
            .map(|feature| feature.as_str().to_owned())
            .collect(),
    })
}

fn project_export_summary_globals(
    module: &PackageArtifactVerifiedModule,
) -> PackageArtifactResult<Vec<PackageGlobalRef>> {
    let mut globals = BTreeMap::new();
    for export in module.verified_module.export_block() {
        let global = PackageGlobalRef {
            module: module.key.module.clone(),
            name: export_name(module, export.name)?,
            export_hash: module.key.export_hash,
            certificate_hash: module.key.certificate_hash,
            decl_interface_hash: PackageHash::from(export.decl_interface_hash),
        };
        globals.insert(
            (
                global.module.clone(),
                global.name.clone(),
                global.export_hash,
                global.certificate_hash,
                global.decl_interface_hash,
            ),
            global,
        );
    }
    Ok(globals.into_values().collect())
}

fn project_export_summary_module_axioms(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
) -> PackageArtifactResult<Vec<PackageGlobalRef>> {
    let mut axioms = BTreeMap::new();
    for axiom in &module.verified_module.axiom_report().module_axioms {
        let axiom = project_axiom_ref(extraction, module, axiom)?;
        let Some(provider) = module_for_axiom_reference(extraction, &axiom) else {
            return Err(axiom_projection_error(module));
        };
        let global = PackageGlobalRef {
            module: axiom.module,
            name: axiom.name,
            export_hash: axiom.export_hash,
            certificate_hash: provider.key.certificate_hash,
            decl_interface_hash: axiom.decl_interface_hash,
        };
        axioms.insert(
            (
                global.module.clone(),
                global.name.clone(),
                global.export_hash,
                global.certificate_hash,
                global.decl_interface_hash,
            ),
            global,
        );
    }
    Ok(axioms.into_values().collect())
}

fn module_for_axiom_reference<'a>(
    extraction: &'a PackageArtifactExtraction,
    axiom: &PackageAxiomReference,
) -> Option<&'a PackageArtifactVerifiedModule> {
    let mut matches = extraction.verified_modules.values().filter(|candidate| {
        candidate.key.module == axiom.module && candidate.key.export_hash == axiom.export_hash
    });
    let provider = matches.next()?;
    matches.next().is_none().then_some(provider)
}

fn ensure_report_passed(report: &PackageVerificationReport) -> PackageVerificationResult<()> {
    if report.status == PackageVerificationStatus::Passed {
        Ok(())
    } else {
        Err(report_failure_error(report))
    }
}

fn report_failure_error(report: &PackageVerificationReport) -> PackageVerificationError {
    report
        .modules
        .iter()
        .find_map(|module| module.error.clone())
        .unwrap_or_else(|| PackageVerificationError {
            kind: match report.mode {
                PackageVerificationMode::FastKernel => PackageVerificationErrorKind::Kernel,
                PackageVerificationMode::Reference => {
                    PackageVerificationErrorKind::ReferenceChecker
                }
            },
            path: "verification.status".to_owned(),
            module: None,
            field: Some(Box::new("status".to_owned())),
            reason_code: match report.mode {
                PackageVerificationMode::FastKernel => {
                    PackageVerificationErrorReason::KernelVerificationFailed
                }
                PackageVerificationMode::Reference => {
                    PackageVerificationErrorReason::ReferenceCheckerRejected
                }
            },
            expected_value: Some(PackageModuleVerificationStatus::Passed.as_str().to_owned()),
            actual_value: Some(report.status.as_str().to_owned()),
            checker_error: None,
        })
}

fn ensure_package_lock_current(
    input: &PackageArtifactExtractionInput<'_>,
) -> PackageVerificationResult<()> {
    let regenerated = build_package_lock_from_artifacts(
        input.validated,
        input.manifest_path.clone(),
        input.manifest_bytes,
        input
            .certificates
            .iter()
            .map(|artifact| PackageLockArtifact {
                path: artifact.path.clone(),
                bytes: artifact.bytes,
            }),
    )
    .map_err(package_lock_error_to_verification_error)?;
    let expected_json = regenerated
        .canonical_json()
        .map_err(package_lock_error_to_verification_error)?;
    let actual_json = input
        .package_lock
        .canonical_json()
        .map_err(package_lock_error_to_verification_error)?;

    if expected_json == actual_json {
        Ok(())
    } else {
        Err(PackageVerificationError::package_lock_stale(
            "generated/package-lock.json",
            format_package_hash(&package_file_hash(expected_json.as_bytes())),
            format_package_hash(&package_file_hash(actual_json.as_bytes())),
        ))
    }
}

fn package_lock_error_to_verification_error(error: PackageLockError) -> PackageVerificationError {
    let (kind, reason_code) = match error.kind {
        PackageLockErrorKind::ArtifactIo => (
            PackageVerificationErrorKind::Artifact,
            match error.reason_code {
                PackageLockErrorReason::CertificateMissing => {
                    PackageVerificationErrorReason::CertificateArtifactMissing
                }
                _ => PackageVerificationErrorReason::CertificateArtifactMissing,
            },
        ),
        PackageLockErrorKind::CertificateDecode => (
            PackageVerificationErrorKind::CertificateDecode,
            PackageVerificationErrorReason::CertificateDecodeFailed,
        ),
        PackageLockErrorKind::CertificateIdentity => (
            PackageVerificationErrorKind::CertificateIdentity,
            match error.reason_code {
                PackageLockErrorReason::CertificateModuleMismatch => {
                    PackageVerificationErrorReason::CertificateModuleMismatch
                }
                PackageLockErrorReason::CertificateFileHashMismatch => {
                    PackageVerificationErrorReason::CertificateFileHashMismatch
                }
                PackageLockErrorReason::ExportHashMismatch => {
                    PackageVerificationErrorReason::ExportHashMismatch
                }
                PackageLockErrorReason::AxiomReportHashMismatch => {
                    PackageVerificationErrorReason::AxiomReportHashMismatch
                }
                PackageLockErrorReason::CertificateHashMismatch => {
                    PackageVerificationErrorReason::CertificateHashMismatch
                }
                _ => PackageVerificationErrorReason::LockGraphInvalid,
            },
        ),
        PackageLockErrorKind::Graph => (
            PackageVerificationErrorKind::LockGraph,
            PackageVerificationErrorReason::LockGraphInvalid,
        ),
        _ => (
            PackageVerificationErrorKind::Input,
            PackageVerificationErrorReason::LockGraphInvalid,
        ),
    };

    PackageVerificationError {
        kind,
        path: error.path,
        module: error.module,
        field: error.field.map(Box::new),
        reason_code,
        expected_value: error.expected_value,
        actual_value: error.actual_value,
        checker_error: None,
    }
}

fn verified_module_collection(
    records: Vec<PackageVerifiedModuleRecord>,
) -> PackageVerificationResult<(
    BTreeMap<PackageArtifactVerifiedModuleKey, PackageArtifactVerifiedModule>,
    Vec<PackageArtifactVerifiedModuleKey>,
)> {
    let mut verified_modules = BTreeMap::new();
    let mut topological_order = Vec::with_capacity(records.len());
    for record in records {
        let key = PackageArtifactVerifiedModuleKey {
            module: record.module,
            export_hash: record.export_hash,
            certificate_hash: record.certificate_hash,
        };
        let verified = PackageArtifactVerifiedModule {
            key: key.clone(),
            origin: artifact_origin(record.origin),
            certificate: PackageArtifactFileReference {
                path: record.certificate,
                file_hash: record.certificate_file_hash,
            },
            axiom_report_hash: record.axiom_report_hash,
            verified_module: record.verified_module,
        };
        if verified_modules.insert(key.clone(), verified).is_some() {
            return Err(PackageVerificationError {
                kind: PackageVerificationErrorKind::LockGraph,
                path: "verified_modules".to_owned(),
                module: Some(Box::new(key.module.as_dotted())),
                field: Some(Box::new("module".to_owned())),
                reason_code: PackageVerificationErrorReason::LockGraphInvalid,
                expected_value: Some("unique module/export/certificate identity".to_owned()),
                actual_value: Some(key.module.as_dotted()),
                checker_error: None,
            });
        }
        topological_order.push(key);
    }
    Ok((verified_modules, topological_order))
}

fn artifact_origin(origin: PackageLockEntryOrigin) -> PackageArtifactOrigin {
    match origin {
        PackageLockEntryOrigin::Local => PackageArtifactOrigin::Local,
        PackageLockEntryOrigin::External => PackageArtifactOrigin::External,
    }
}

fn project_package_axiom_report_modules(
    extraction: &PackageArtifactExtraction,
    policy: &PackageArtifactPolicy,
) -> PackageArtifactResult<Vec<PackageAxiomReportModule>> {
    let mut modules = Vec::with_capacity(extraction.topological_order.len());
    for key in &extraction.topological_order {
        let module = extraction.verified_modules.get(key).ok_or_else(|| {
            projection_error(
                &key.module,
                "module",
                "verified module present in extraction",
                key.module.as_dotted(),
            )
        })?;
        let direct_axioms = project_direct_axioms(extraction, module)?;
        let transitive_axioms = project_transitive_axioms(extraction, module)?;
        let policy_status = evaluate_axiom_policy(policy, &transitive_axioms);
        modules.push(PackageAxiomReportModule {
            module: module.key.module.clone(),
            origin: module.origin,
            export_hash: module.key.export_hash,
            certificate_hash: module.key.certificate_hash,
            axiom_report_hash: module.axiom_report_hash,
            certificate_file_hash: module.certificate.file_hash,
            direct_axioms,
            transitive_axioms,
            policy_status,
        });
    }
    Ok(modules)
}

fn project_package_theorem_index_entries(
    extraction: &PackageArtifactExtraction,
) -> PackageArtifactResult<Vec<PackageTheoremIndexEntry>> {
    let mut entries = Vec::new();
    for key in &extraction.topological_order {
        let module = extraction.verified_modules.get(key).ok_or_else(|| {
            projection_error(
                &key.module,
                "module",
                "verified module present in extraction",
                key.module.as_dotted(),
            )
        })?;
        for export in module.verified_module.export_block() {
            if matches!(export.kind, ExportKind::Theorem | ExportKind::Axiom) {
                entries.push(project_package_theorem_index_entry(
                    extraction, module, export,
                )?);
            }
        }
    }
    Ok(entries)
}

fn project_package_theorem_index_entry(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    export: &ExportEntry,
) -> PackageArtifactResult<PackageTheoremIndexEntry> {
    let name = export_name(module, export.name)?;
    let kind = match export.kind {
        ExportKind::Theorem => PackageTheoremIndexKind::Theorem,
        ExportKind::Axiom => PackageTheoremIndexKind::Axiom,
        _ => {
            return Err(theorem_projection_error(
                module,
                "kind",
                "theorem or axiom export",
            ));
        }
    };
    Ok(PackageTheoremIndexEntry {
        global_ref: PackageGlobalRef {
            module: module.key.module.clone(),
            name,
            export_hash: module.key.export_hash,
            certificate_hash: module.key.certificate_hash,
            decl_interface_hash: PackageHash::from(export.decl_interface_hash),
        },
        kind,
        statement: project_theorem_statement(extraction, module, export)?,
        modes: theorem_index_modes(module, export.ty)?,
        tags: Vec::new(),
        axiom_dependencies: project_export_axiom_dependencies(extraction, module, export)?,
        module_axiom_report_hash: module.axiom_report_hash,
        artifact: PackageTheoremIndexArtifact {
            origin: module.origin,
            certificate: module.certificate.path.clone(),
        },
    })
}

fn project_theorem_statement(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    export: &ExportEntry,
) -> PackageArtifactResult<PackageTheoremStatement> {
    Ok(PackageTheoremStatement {
        core_hash: PackageHash::from(export.type_hash),
        head: theorem_statement_head(extraction, module, export.ty)?,
        constants: theorem_statement_constants(extraction, module, export.ty)?,
    })
}

fn theorem_statement_head(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    ty: TermId,
) -> PackageArtifactResult<Option<PackageGlobalRefView>> {
    let mut conclusion = ty;
    while let TermNode::Pi { body, .. } = term_node(module, conclusion)? {
        conclusion = *body;
    }
    let Some(global_ref) = syntactic_term_head(module, conclusion)? else {
        return Ok(None);
    };
    project_global_ref_view(extraction, module, &global_ref).map(Some)
}

fn syntactic_term_head(
    module: &PackageArtifactVerifiedModule,
    term: TermId,
) -> PackageArtifactResult<Option<GlobalRef>> {
    let mut current = term;
    while let TermNode::App(func, _) = term_node(module, current)? {
        current = *func;
    }
    Ok(match term_node(module, current)? {
        TermNode::Const { global_ref, .. } => Some(global_ref.clone()),
        _ => None,
    })
}

fn theorem_statement_constants(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    ty: TermId,
) -> PackageArtifactResult<Vec<PackageGlobalRefView>> {
    let mut constants = BTreeMap::new();
    let mut visited = BTreeSet::new();
    collect_term_constants(extraction, module, ty, &mut visited, &mut constants)?;
    Ok(constants.into_values().collect())
}

fn collect_term_constants(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    term: TermId,
    visited: &mut BTreeSet<TermId>,
    constants: &mut BTreeMap<(Name, Name, PackageHash, PackageHash), PackageGlobalRefView>,
) -> PackageArtifactResult<()> {
    if !visited.insert(term) {
        return Ok(());
    }
    match term_node(module, term)? {
        TermNode::Sort(_) | TermNode::BVar(_) => Ok(()),
        TermNode::Const { global_ref, .. } => {
            let view = project_global_ref_view(extraction, module, global_ref)?;
            constants.insert(global_ref_view_key(&view), view);
            Ok(())
        }
        TermNode::App(func, arg) => {
            collect_term_constants(extraction, module, *func, visited, constants)?;
            collect_term_constants(extraction, module, *arg, visited, constants)
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_term_constants(extraction, module, *ty, visited, constants)?;
            collect_term_constants(extraction, module, *body, visited, constants)
        }
        TermNode::Let { ty, value, body } => {
            collect_term_constants(extraction, module, *ty, visited, constants)?;
            collect_term_constants(extraction, module, *value, visited, constants)?;
            collect_term_constants(extraction, module, *body, visited, constants)
        }
    }
}

fn theorem_index_modes(
    module: &PackageArtifactVerifiedModule,
    ty: TermId,
) -> PackageArtifactResult<Vec<PackageTheoremIndexMode>> {
    let mut modes = vec![PackageTheoremIndexMode::Exact];
    if matches!(term_node(module, ty)?, TermNode::Pi { .. }) {
        modes.push(PackageTheoremIndexMode::Apply);
    }
    Ok(modes)
}

fn project_export_axiom_dependencies(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
    export: &ExportEntry,
) -> PackageArtifactResult<Vec<PackageAxiomReference>> {
    let mut projected = BTreeMap::new();
    for axiom in &export.axiom_dependencies {
        insert_projected_axiom(&mut projected, extraction, module, axiom)?;
    }
    Ok(projected.into_values().collect())
}

fn project_global_ref_view(
    extraction: &PackageArtifactExtraction,
    owner: &PackageArtifactVerifiedModule,
    global_ref: &GlobalRef,
) -> PackageArtifactResult<PackageGlobalRefView> {
    match global_ref {
        GlobalRef::Builtin { .. } => Err(theorem_projection_error(
            owner,
            "global_ref",
            "package-exported declaration reference",
        )),
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let imported = imported_module_for_global_ref(extraction, owner, *import_index)?;
            let name = export_name(owner, *name)?;
            unique_export_by_name_and_hash(imported, &name, *decl_interface_hash).ok_or_else(
                || theorem_projection_error(owner, "global_ref", "imported public export"),
            )?;
            Ok(PackageGlobalRefView {
                module: imported.key.module.clone(),
                name,
                export_hash: imported.key.export_hash,
                decl_interface_hash: PackageHash::from(*decl_interface_hash),
            })
        }
        GlobalRef::Local { decl_index } => {
            let decl = owner
                .verified_module
                .declarations()
                .get(*decl_index)
                .ok_or_else(|| {
                    theorem_projection_error(owner, "global_ref", "local declaration")
                })?;
            let name = decl_payload_name(owner, &decl.decl)?;
            unique_export_by_name_and_hash(owner, &name, decl.hashes.decl_interface_hash)
                .ok_or_else(|| {
                    theorem_projection_error(owner, "global_ref", "local public export")
                })?;
            Ok(PackageGlobalRefView {
                module: owner.key.module.clone(),
                name,
                export_hash: owner.key.export_hash,
                decl_interface_hash: PackageHash::from(decl.hashes.decl_interface_hash),
            })
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            let decl = owner
                .verified_module
                .declarations()
                .get(*decl_index)
                .ok_or_else(|| {
                    theorem_projection_error(owner, "global_ref", "local generated source")
                })?;
            let name = export_name(owner, *name)?;
            if !decl_contains_generated_name(owner, &decl.decl, &name)? {
                return Err(theorem_projection_error(
                    owner,
                    "global_ref",
                    "generated declaration owned by referenced source declaration",
                ));
            }
            let export =
                unique_export_by_name_and_hash(owner, &name, decl.hashes.decl_interface_hash)
                    .ok_or_else(|| {
                        theorem_projection_error(
                            owner,
                            "global_ref",
                            "local generated public export",
                        )
                    })?;
            if !matches!(export.kind, ExportKind::Constructor | ExportKind::Recursor) {
                return Err(theorem_projection_error(
                    owner,
                    "global_ref",
                    "constructor or recursor export",
                ));
            }
            Ok(PackageGlobalRefView {
                module: owner.key.module.clone(),
                name,
                export_hash: owner.key.export_hash,
                decl_interface_hash: PackageHash::from(export.decl_interface_hash),
            })
        }
    }
}

fn unique_export_by_name_and_hash<'a>(
    module: &'a PackageArtifactVerifiedModule,
    name: &Name,
    decl_interface_hash: Hash,
) -> Option<&'a ExportEntry> {
    let mut matches = module
        .verified_module
        .export_block()
        .iter()
        .filter(|entry| {
            entry.decl_interface_hash == decl_interface_hash
                && module
                    .verified_module
                    .name_table()
                    .get(entry.name)
                    .is_some_and(|entry_name| entry_name == name)
        });
    let first = matches.next()?;
    if matches.next().is_none() {
        Some(first)
    } else {
        None
    }
}

fn decl_contains_generated_name(
    module: &PackageArtifactVerifiedModule,
    decl: &DeclPayload,
    generated_name: &Name,
) -> PackageArtifactResult<bool> {
    match decl {
        DeclPayload::Inductive {
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            constructors,
            recursor,
            ..
        } => generated_specs_contain_name(module, constructors, recursor.as_ref(), generated_name),
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                if generated_specs_contain_name(
                    module,
                    &inductive.constructors,
                    inductive.recursor.as_ref(),
                    generated_name,
                )? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Ok(false),
    }
}

fn generated_specs_contain_name(
    module: &PackageArtifactVerifiedModule,
    constructors: &[npa_cert::ConstructorSpec],
    recursor: Option<&npa_cert::RecursorSpec>,
    generated_name: &Name,
) -> PackageArtifactResult<bool> {
    for constructor in constructors {
        if export_name(module, constructor.name)? == *generated_name {
            return Ok(true);
        }
    }
    if let Some(recursor) = recursor {
        if export_name(module, recursor.name)? == *generated_name {
            return Ok(true);
        }
    }
    Ok(false)
}

fn term_node(
    module: &PackageArtifactVerifiedModule,
    term: TermId,
) -> PackageArtifactResult<&TermNode> {
    module
        .verified_module
        .term_table()
        .get(term)
        .ok_or_else(|| {
            theorem_projection_error(module, "statement", "valid certificate term reference")
        })
}

fn export_name(
    module: &PackageArtifactVerifiedModule,
    name_id: NameId,
) -> PackageArtifactResult<Name> {
    module
        .verified_module
        .name_table()
        .get(name_id)
        .cloned()
        .ok_or_else(|| theorem_projection_error(module, "name", "valid certificate name"))
}

fn decl_payload_name(
    module: &PackageArtifactVerifiedModule,
    decl: &DeclPayload,
) -> PackageArtifactResult<Name> {
    export_name(module, decl_payload_name_id(decl))
}

fn decl_payload_name_id(decl: &DeclPayload) -> NameId {
    match decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

fn global_ref_view_key(view: &PackageGlobalRefView) -> (Name, Name, PackageHash, PackageHash) {
    (
        view.module.clone(),
        view.name.clone(),
        view.export_hash,
        view.decl_interface_hash,
    )
}

fn project_direct_axioms(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
) -> PackageArtifactResult<Vec<PackageAxiomReference>> {
    let mut projected = BTreeMap::new();
    for report in &module.verified_module.axiom_report().per_declaration {
        for axiom in &report.direct_axioms {
            insert_projected_axiom(&mut projected, extraction, module, axiom)?;
        }
    }
    Ok(projected.into_values().collect())
}

fn project_transitive_axioms(
    extraction: &PackageArtifactExtraction,
    module: &PackageArtifactVerifiedModule,
) -> PackageArtifactResult<Vec<PackageAxiomReference>> {
    let mut projected = BTreeMap::new();
    for axiom in &module.verified_module.axiom_report().module_axioms {
        insert_projected_axiom(&mut projected, extraction, module, axiom)?;
    }
    Ok(projected.into_values().collect())
}

fn insert_projected_axiom(
    projected: &mut BTreeMap<(Name, Name, PackageHash, PackageHash), PackageAxiomReference>,
    extraction: &PackageArtifactExtraction,
    owner: &PackageArtifactVerifiedModule,
    axiom: &AxiomRef,
) -> PackageArtifactResult<()> {
    let axiom = project_axiom_ref(extraction, owner, axiom)?;
    projected.insert(
        (
            axiom.module.clone(),
            axiom.name.clone(),
            axiom.export_hash,
            axiom.decl_interface_hash,
        ),
        axiom,
    );
    Ok(())
}

fn project_axiom_ref(
    extraction: &PackageArtifactExtraction,
    owner: &PackageArtifactVerifiedModule,
    axiom: &AxiomRef,
) -> PackageArtifactResult<PackageAxiomReference> {
    match &axiom.global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            if axiom.decl_interface_hash != *decl_interface_hash {
                return Err(axiom_projection_error(owner));
            }
            let Some(axiom_name) = owner.verified_module.name_table().get(*name) else {
                return Err(axiom_projection_error(owner));
            };
            let Some(report_name) = owner.verified_module.name_table().get(axiom.name) else {
                return Err(axiom_projection_error(owner));
            };
            if report_name != axiom_name {
                return Err(axiom_projection_error(owner));
            }
            Ok(PackageAxiomReference {
                module: owner.key.module.clone(),
                name: axiom_name.clone(),
                export_hash: owner.key.export_hash,
                decl_interface_hash: PackageHash::from(*decl_interface_hash),
            })
        }
        GlobalRef::Local { decl_index } => {
            let Some(decl) = owner.verified_module.declarations().get(*decl_index) else {
                return Err(axiom_projection_error(owner));
            };
            if !matches!(
                decl.decl,
                DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. }
            ) {
                return Err(axiom_projection_error(owner));
            }
            let Some(name) = owner.verified_module.name_table().get(axiom.name) else {
                return Err(axiom_projection_error(owner));
            };
            Ok(PackageAxiomReference {
                module: owner.key.module.clone(),
                name: name.clone(),
                export_hash: owner.key.export_hash,
                decl_interface_hash: PackageHash::from(axiom.decl_interface_hash),
            })
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let imported = imported_module_for_axiom(extraction, owner, *import_index)?;
            let Some(axiom_name) = owner.verified_module.name_table().get(*name) else {
                return Err(axiom_projection_error(owner));
            };
            if axiom.decl_interface_hash != *decl_interface_hash
                || !module_exports_declared_axiom(imported, axiom_name, *decl_interface_hash)
            {
                return Err(axiom_projection_error(owner));
            }
            Ok(PackageAxiomReference {
                module: imported.key.module.clone(),
                name: axiom_name.clone(),
                export_hash: imported.key.export_hash,
                decl_interface_hash: PackageHash::from(*decl_interface_hash),
            })
        }
        GlobalRef::LocalGenerated { .. } => Err(axiom_projection_error(owner)),
    }
}

fn module_exports_declared_axiom(
    module: &PackageArtifactVerifiedModule,
    axiom_name: &Name,
    decl_interface_hash: npa_cert::Hash,
) -> bool {
    module.verified_module.export_block().iter().any(|entry| {
        module
            .verified_module
            .name_table()
            .get(entry.name)
            .is_some_and(|entry_name| {
                entry.kind == ExportKind::Axiom
                    && entry_name == axiom_name
                    && entry.decl_interface_hash == decl_interface_hash
            })
    })
}

fn imported_module_for_global_ref<'a>(
    extraction: &'a PackageArtifactExtraction,
    owner: &PackageArtifactVerifiedModule,
    import_index: usize,
) -> PackageArtifactResult<&'a PackageArtifactVerifiedModule> {
    let Some(import) = owner.verified_module.imports().get(import_index) else {
        return Err(theorem_projection_error(
            owner,
            "global_ref",
            "valid import binding",
        ));
    };
    let mut matches = extraction.verified_modules.values().filter(|candidate| {
        candidate.key.module == import.module
            && candidate.key.export_hash == PackageHash::from(import.export_hash)
            && import
                .certificate_hash
                .is_none_or(|hash| candidate.key.certificate_hash == PackageHash::from(hash))
    });
    let Some(imported) = matches.next() else {
        return Err(theorem_projection_error(
            owner,
            "global_ref",
            "verified imported module",
        ));
    };
    if matches.next().is_some() {
        return Err(theorem_projection_error(
            owner,
            "global_ref",
            "unique verified imported module",
        ));
    }
    Ok(imported)
}

fn imported_module_for_axiom<'a>(
    extraction: &'a PackageArtifactExtraction,
    owner: &PackageArtifactVerifiedModule,
    import_index: usize,
) -> PackageArtifactResult<&'a PackageArtifactVerifiedModule> {
    let Some(import) = owner.verified_module.imports().get(import_index) else {
        return Err(axiom_projection_error(owner));
    };
    let mut matches = extraction.verified_modules.values().filter(|candidate| {
        candidate.key.module == import.module
            && candidate.key.export_hash == PackageHash::from(import.export_hash)
            && import
                .certificate_hash
                .is_none_or(|hash| candidate.key.certificate_hash == PackageHash::from(hash))
    });
    let Some(imported) = matches.next() else {
        return Err(axiom_projection_error(owner));
    };
    if matches.next().is_some() {
        return Err(axiom_projection_error(owner));
    }
    Ok(imported)
}

fn evaluate_axiom_policy(
    policy: &PackageArtifactPolicy,
    transitive_axioms: &[PackageAxiomReference],
) -> PackageAxiomPolicyStatus {
    let allowed_axioms = policy
        .allowed_axioms
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut violations = BTreeMap::new();
    for axiom in transitive_axioms {
        let reason_code = if axiom.name.as_dotted().contains("sorry") {
            Some(PackageAxiomPolicyViolationReason::SorryDisallowed)
        } else if !policy.allow_custom_axioms && !allowed_axioms.contains(&axiom.name) {
            Some(PackageAxiomPolicyViolationReason::AxiomNotAllowlisted)
        } else {
            None
        };
        if let Some(reason_code) = reason_code {
            violations.insert(
                (
                    axiom.module.clone(),
                    axiom.name.clone(),
                    axiom.export_hash,
                    axiom.decl_interface_hash,
                    reason_code,
                ),
                PackageAxiomPolicyViolation {
                    axiom: axiom.clone(),
                    reason_code,
                },
            );
        }
    }
    let violations = violations.into_values().collect::<Vec<_>>();
    PackageAxiomPolicyStatus {
        status: if violations.is_empty() {
            PackageAxiomPolicyStatusKind::Ok
        } else {
            PackageAxiomPolicyStatusKind::Violation
        },
        violations,
    }
}

fn axiom_projection_error(module: &PackageArtifactVerifiedModule) -> PackageArtifactError {
    projection_error(
        &module.key.module,
        "axiom_ref",
        "package-projectable builtin, local, or imported axiom reference",
        module.key.module.as_dotted(),
    )
}

fn theorem_projection_error(
    module: &PackageArtifactVerifiedModule,
    field: &str,
    expected: impl Into<String>,
) -> PackageArtifactError {
    projection_error(
        &module.key.module,
        field,
        expected,
        module.key.module.as_dotted(),
    )
}

fn projection_error(
    module: &Name,
    field: &str,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> PackageArtifactError {
    PackageArtifactError::summary_mismatch(
        format!("modules[{}].{field}", module.as_dotted()),
        field,
        expected,
        actual,
    )
}

fn checker_summaries_from_report(
    report: &PackageVerificationReport,
    mode: PackageCheckerMode,
    checker: &str,
    profile: &str,
) -> Vec<PackageCheckerSummary> {
    report
        .modules
        .iter()
        .map(|module| checker_summary_from_module(module, mode, checker, profile))
        .collect()
}

fn checker_summary_from_module(
    module: &PackageModuleVerificationResult,
    mode: PackageCheckerMode,
    checker: &str,
    profile: &str,
) -> PackageCheckerSummary {
    PackageCheckerSummary {
        module: module.module.clone(),
        checker: checker.to_owned(),
        profile: profile.to_owned(),
        mode,
        status: module.status.as_str().to_owned(),
        export_hash: module.export_hash,
        certificate_hash: module.certificate_hash,
        axiom_report_hash: module.axiom_report_hash,
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
    };

    use npa_package::{
        build_package_lock_from_artifacts, parse_and_validate_manifest_str,
        parse_package_axiom_report_json, parse_package_lock_json, parse_package_theorem_index_json,
        PackageLockError, PackageLockImport, PackageTheoremIndexMode, PACKAGE_THEOREM_INDEX_SCHEMA,
    };

    use super::*;

    const BASIC_CERTIFICATE_PATH: &str = "Proofs/Ai/Basic/certificate.npcert";
    const EQ_CERTIFICATE_PATH: &str = "vendor/npa-std/Std/Logic/Eq/certificate.npcert";
    const EQ_REASONING_CERTIFICATE_PATH: &str = "Proofs/Ai/EqReasoning/certificate.npcert";

    #[derive(Clone, Debug)]
    struct CertificateBuffer {
        path: PackagePath,
        bytes: Vec<u8>,
    }

    #[test]
    fn package_lock_error_conversion_preserves_module_context() {
        let error = PackageLockError::manifest_import_missing(
            "entries[263].imports[24].module",
            "Std.Logic.Eq",
        )
        .with_module("Proofs.Ai.Foundation");

        let converted = package_lock_error_to_verification_error(error);

        assert_eq!(converted.kind, PackageVerificationErrorKind::LockGraph);
        assert_eq!(
            converted.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
        assert_eq!(converted.path, "entries[263].imports[24].module");
        assert_eq!(
            converted.module.as_ref().map(|module| module.as_str()),
            Some("Proofs.Ai.Foundation")
        );
        assert_eq!(
            converted.field.as_ref().map(|field| field.as_str()),
            Some("module")
        );
    }

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("npa-api crate lives under crates/")
            .to_path_buf()
    }

    fn basic_certificate_bytes() -> Vec<u8> {
        fs::read(
            repo_root()
                .join("testdata/package/proofs")
                .join(BASIC_CERTIFICATE_PATH),
        )
        .unwrap()
    }

    fn proof_certificate_buffer(root: &Path, path: &str) -> CertificateBuffer {
        CertificateBuffer {
            path: PackagePath::new(path),
            bytes: fs::read(root.join(path)).unwrap(),
        }
    }

    fn certificate_artifacts(buffers: &[CertificateBuffer]) -> Vec<PackageCertificateArtifact<'_>> {
        buffers
            .iter()
            .map(|buffer| PackageCertificateArtifact {
                path: buffer.path.clone(),
                bytes: buffer.bytes.as_slice(),
            })
            .collect()
    }

    fn package_lock_file_reference(lock_json: &str) -> PackageArtifactFileReference {
        PackageArtifactFileReference {
            path: PackagePath::new("generated/package-lock.json"),
            file_hash: package_file_hash(lock_json.as_bytes()),
        }
    }

    fn basic_manifest_source() -> String {
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]

[[modules]]
module = "Proofs.Ai.Basic"
source = "missing/source/Proofs/Ai/Basic.npa"
certificate = "Proofs/Ai/Basic/certificate.npcert"
meta = "missing/meta/Proofs/Ai/Basic.json"
replay = "missing/replay/Proofs/Ai/Basic.json"
producer_profile = "human-surface-explicit-term"
expected_source_hash = "sha256:2176be7570deae66754789868aa373ab01434512b4f50b992089886d2c655387"
expected_certificate_file_hash = "sha256:448a3de71485d4f38e45ac7bf3b637b0e9e38d7ce215dd4847a2a2188099ee21"
expected_export_hash = "sha256:6cbf881b56f61d413c2584eb9b1cdd6fb09e504f6ff6c855fa73ee55d763b839"
expected_axiom_report_hash = "sha256:fed11e73accfbfb0dfc28b4f510e151fa33d8af82d58fdb23b92567e04e59e40"
expected_certificate_hash = "sha256:7a50b381af353fe15c0b602fad60f4b9d5f70613dfe6f47832da2d8c11b391dd"
imports = []
definitions = []
theorems = ["id"]
axioms = []
"#
        .to_owned()
    }

    fn eq_reasoning_manifest_source() -> String {
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]

[[imports]]
module = "Std.Logic.Eq"
package = "npa-std"
version = "0.1.0"
certificate = "vendor/npa-std/Std/Logic/Eq/certificate.npcert"
export_hash = "sha256:1f203117abf6f3417d663138bbf5b95f2a155b73502be59678b8a57f31bd9eb1"
certificate_hash = "sha256:0308e48e6f6353e601fe14c737a0e0882e37657fd864cabbdb3a7250a90b82ab"

[[modules]]
module = "Proofs.Ai.EqReasoning"
source = "missing/source/Proofs/Ai/EqReasoning.npa"
certificate = "Proofs/Ai/EqReasoning/certificate.npcert"
meta = "missing/meta/Proofs/Ai/EqReasoning.json"
replay = "missing/replay/Proofs/Ai/EqReasoning.json"
producer_profile = "human-surface-explicit-term"
expected_source_hash = "sha256:676d15f72088b4f107773ad566920c02a5e29d8773a4c5c24ccb0a1b19de930f"
expected_certificate_file_hash = "sha256:ffc6f428215aca3b28761989ba03160821e2c4aa76dea44e5d5a3af7d2858b2c"
expected_export_hash = "sha256:4727d19030aece233f2fc0e44ea6a0bff83bf8347fabb0232ea2b52cfc1d10d7"
expected_axiom_report_hash = "sha256:5283e4bbd120c3ffa60356b600be06364c3739f9c1992538f75aa4c7df947968"
expected_certificate_hash = "sha256:b73e42bf01fc55ebd79309367d9b3661697b7b11bf97955742fb036711121aba"
imports = ["Std.Logic.Eq"]
definitions = []
theorems = ["eq_symm", "eq_trans", "eq_congr_arg", "eq_congr_fun", "eq_congr2", "eq_subst", "eq_transport_const", "eq_rewrite_left", "eq_rewrite_right", "eq_cast_trans", "eq_calc3"]
axioms = ["Eq.rec"]
"#
        .to_owned()
    }

    fn basic_lock(
        validated: &ValidatedPackageManifest,
        manifest_source: &str,
        certificate_bytes: &[u8],
    ) -> PackageLockManifest {
        build_package_lock_from_artifacts(
            validated,
            PackagePath::new("npa-package.toml"),
            manifest_source.as_bytes(),
            [PackageLockArtifact {
                path: PackagePath::new(BASIC_CERTIFICATE_PATH),
                bytes: certificate_bytes,
            }],
        )
        .unwrap()
    }

    fn extraction_input<'a>(
        validated: &'a ValidatedPackageManifest,
        lock: &'a PackageLockManifest,
        manifest_source: &'a str,
        certificate_bytes: &'a [u8],
        reference_summaries: PackageArtifactReferenceSummaryMode,
    ) -> PackageArtifactExtractionInput<'a> {
        PackageArtifactExtractionInput {
            validated,
            manifest_path: PackagePath::new("npa-package.toml"),
            manifest_bytes: manifest_source.as_bytes(),
            package_lock: lock,
            certificates: vec![PackageCertificateArtifact {
                path: PackagePath::new(BASIC_CERTIFICATE_PATH),
                bytes: certificate_bytes,
            }],
            reference_summaries,
        }
    }

    fn eq_reasoning_projection_fixture() -> (
        ValidatedPackageManifest,
        PackageArtifactExtraction,
        PackageArtifactFileReference,
    ) {
        let root = repo_root().join("testdata/package/proofs");
        let manifest_source = eq_reasoning_manifest_source();
        let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let buffers = vec![
            proof_certificate_buffer(&root, EQ_CERTIFICATE_PATH),
            proof_certificate_buffer(&root, EQ_REASONING_CERTIFICATE_PATH),
        ];
        let lock = build_package_lock_from_artifacts(
            &validated,
            PackagePath::new("npa-package.toml"),
            manifest_source.as_bytes(),
            buffers.iter().map(|buffer| PackageLockArtifact {
                path: buffer.path.clone(),
                bytes: buffer.bytes.as_slice(),
            }),
        )
        .unwrap();
        let lock_json = lock.canonical_json().unwrap();
        let package_lock = package_lock_file_reference(&lock_json);
        let extraction = extract_package_artifacts_source_free(PackageArtifactExtractionInput {
            validated: &validated,
            manifest_path: PackagePath::new("npa-package.toml"),
            manifest_bytes: manifest_source.as_bytes(),
            package_lock: &lock,
            certificates: certificate_artifacts(&buffers),
            reference_summaries: PackageArtifactReferenceSummaryMode::Omit,
        })
        .unwrap();

        (validated, extraction, package_lock)
    }

    fn proof_corpus_certificate_buffers(
        validated: &ValidatedPackageManifest,
    ) -> Vec<CertificateBuffer> {
        let root = repo_root().join("testdata/package/proofs");
        let mut buffers = Vec::new();
        if let Some(imports) = &validated.manifest().imports {
            for import in imports {
                buffers.push(proof_certificate_buffer(&root, import.certificate.as_str()));
            }
        }
        for module in &validated.manifest().modules {
            buffers.push(proof_certificate_buffer(&root, module.certificate.as_str()));
        }
        buffers
    }

    fn verified_module<'a>(
        extraction: &'a PackageArtifactExtraction,
        module: &str,
    ) -> &'a PackageArtifactVerifiedModule {
        extraction
            .verified_modules
            .values()
            .find(|verified| verified.key.module.as_dotted() == module)
            .unwrap()
    }

    fn export_by_name<'a>(
        module: &'a PackageArtifactVerifiedModule,
        declaration: &str,
    ) -> &'a ExportEntry {
        module
            .verified_module
            .export_block()
            .iter()
            .find(|export| {
                module
                    .verified_module
                    .name_table()
                    .get(export.name)
                    .is_some_and(|name| name.as_dotted() == declaration)
            })
            .unwrap()
    }

    fn theorem_entry_sort_key(entry: &PackageTheoremIndexEntry) -> String {
        format!(
            "{{\"module\":\"{}\",\"name\":\"{}\",\"export_hash\":\"{}\",\"certificate_hash\":\"{}\",\"decl_interface_hash\":\"{}\"}}",
            entry.global_ref.module.as_dotted(),
            entry.global_ref.name.as_dotted(),
            format_package_hash(&entry.global_ref.export_hash),
            format_package_hash(&entry.global_ref.certificate_hash),
            format_package_hash(&entry.global_ref.decl_interface_hash),
        )
    }

    #[test]
    fn package_artifact_extraction_collects_verified_modules_and_fast_summaries_source_free() {
        let manifest_source = basic_manifest_source();
        let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let certificate_bytes = basic_certificate_bytes();
        let lock = basic_lock(&validated, &manifest_source, &certificate_bytes);

        let extraction = extract_package_artifacts_source_free(extraction_input(
            &validated,
            &lock,
            &manifest_source,
            &certificate_bytes,
            PackageArtifactReferenceSummaryMode::Omit,
        ))
        .unwrap();

        assert_eq!(extraction.topological_order.len(), 1);
        let key = &extraction.topological_order[0];
        assert_eq!(key.module.as_dotted(), "Proofs.Ai.Basic");
        let module = extraction.verified_modules.get(key).unwrap();
        assert_eq!(module.origin, PackageArtifactOrigin::Local);
        assert_eq!(
            module.verified_module.module().as_dotted(),
            "Proofs.Ai.Basic"
        );
        assert_eq!(
            module.verified_module.export_hash(),
            key.export_hash.into_bytes()
        );
        assert_eq!(
            module.verified_module.certificate_hash(),
            key.certificate_hash.into_bytes()
        );
        assert_eq!(extraction.checker_summaries.len(), 1);
        let summary = &extraction.checker_summaries[0];
        assert_eq!(summary.mode, PackageCheckerMode::Fast);
        assert_eq!(summary.checker, "fast-kernel-certificate-verifier");
        assert_eq!(summary.profile, "fast-kernel");
        assert_ne!(summary.checker, "npa-checker-ref");
        assert_eq!(summary.status, "passed");
        assert!(
            !extraction
                .fast_verification_report
                .reference_checker_verdict
        );
        assert!(extraction.reference_verification_report.is_none());
    }

    #[test]
    fn package_artifact_extraction_reference_summary_uses_source_free_reference_verifier() {
        let manifest_source = basic_manifest_source();
        let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let certificate_bytes = basic_certificate_bytes();
        let lock = basic_lock(&validated, &manifest_source, &certificate_bytes);

        let extraction = extract_package_artifacts_source_free(extraction_input(
            &validated,
            &lock,
            &manifest_source,
            &certificate_bytes,
            PackageArtifactReferenceSummaryMode::Include,
        ))
        .unwrap();

        assert_eq!(extraction.checker_summaries.len(), 2);
        let reference = extraction
            .checker_summaries
            .iter()
            .find(|summary| summary.mode == PackageCheckerMode::Reference)
            .expect("reference summary is included");
        assert_eq!(reference.checker, "npa-checker-ref");
        assert_eq!(reference.profile, "npa.checker.reference.v0.1");
        assert_eq!(reference.status, "passed");
        assert!(
            extraction
                .reference_verification_report
                .as_ref()
                .unwrap()
                .reference_checker_verdict
        );
    }

    #[test]
    fn package_axiom_report_projection_projects_axioms_policy_summary_and_ordering() {
        let (validated, extraction, package_lock) = eq_reasoning_projection_fixture();

        let report =
            project_package_axiom_report_from_extraction(&validated, &extraction, package_lock)
                .unwrap();

        assert_eq!(report.modules.len(), 2);
        assert_eq!(
            report
                .modules
                .iter()
                .map(|module| module.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Proofs.Ai.EqReasoning", "Std.Logic.Eq"]
        );
        let eq_reasoning = report
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == "Proofs.Ai.EqReasoning")
            .unwrap();
        assert_eq!(eq_reasoning.origin, PackageArtifactOrigin::Local);
        assert_eq!(eq_reasoning.direct_axioms.len(), 1);
        assert_eq!(eq_reasoning.transitive_axioms.len(), 1);
        assert_eq!(
            eq_reasoning.direct_axioms[0].module.as_dotted(),
            "Proofs.Ai.EqReasoning"
        );
        assert_eq!(eq_reasoning.direct_axioms[0].name.as_dotted(), "Eq.rec");

        let std_eq = report
            .modules
            .iter()
            .find(|module| module.module.as_dotted() == "Std.Logic.Eq")
            .unwrap();
        assert_eq!(std_eq.origin, PackageArtifactOrigin::External);
        assert!(std_eq.direct_axioms.is_empty());
        assert!(std_eq.transitive_axioms.is_empty());
        assert!(report
            .modules
            .iter()
            .all(|module| module.policy_status.status == PackageAxiomPolicyStatusKind::Ok));
        assert_eq!(report.summary.module_count, 2);
        assert_eq!(report.summary.local_module_count, 1);
        assert_eq!(report.summary.external_module_count, 1);
        assert_eq!(report.summary.direct_axiom_count, 1);
        assert_eq!(report.summary.transitive_axiom_count, 1);
        assert_eq!(report.summary.policy_violation_count, 0);
        assert_eq!(
            report
                .checker_summaries
                .iter()
                .map(|summary| summary.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Proofs.Ai.EqReasoning", "Std.Logic.Eq"]
        );

        let json = report.canonical_json().unwrap();
        assert_eq!(parse_package_axiom_report_json(&json).unwrap(), report);
    }

    #[test]
    fn package_theorem_index_projection_projects_public_theorems_axioms_statement_and_ordering() {
        let (validated, extraction, package_lock) = eq_reasoning_projection_fixture();

        let index =
            project_package_theorem_index_from_extraction(&validated, &extraction, package_lock)
                .unwrap();

        assert_eq!(index.schema, PACKAGE_THEOREM_INDEX_SCHEMA);
        assert_eq!(index.package, validated.manifest().package.clone());
        assert_eq!(index.version, validated.manifest().version.clone());
        assert_eq!(index.summary.entry_count as usize, index.entries.len());
        assert_eq!(
            index.summary.entry_count,
            index.summary.theorem_count + index.summary.axiom_count
        );
        let expected_theorem_count = extraction
            .verified_modules
            .values()
            .flat_map(|module| module.verified_module.export_block())
            .filter(|export| export.kind == ExportKind::Theorem)
            .count() as u64;
        let expected_axiom_count = extraction
            .verified_modules
            .values()
            .flat_map(|module| module.verified_module.export_block())
            .filter(|export| export.kind == ExportKind::Axiom)
            .count() as u64;
        assert_eq!(index.summary.theorem_count, expected_theorem_count);
        assert_eq!(index.summary.axiom_count, expected_axiom_count);
        assert!(index
            .entries
            .iter()
            .all(|entry| entry.modes.contains(&PackageTheoremIndexMode::Exact)));
        assert!(index
            .entries
            .iter()
            .any(|entry| entry.modes.contains(&PackageTheoremIndexMode::Apply)));
        assert!(!index
            .entries
            .iter()
            .any(|entry| entry.modes.iter().any(|mode| matches!(
                mode,
                PackageTheoremIndexMode::Rw | PackageTheoremIndexMode::Simp
            ))));
        assert!(index.entries.iter().all(|entry| entry.tags.is_empty()));

        let mut sorted = index.entries.clone();
        sorted.sort_by_key(theorem_entry_sort_key);
        assert_eq!(index.entries, sorted);

        let eq_reasoning = verified_module(&extraction, "Proofs.Ai.EqReasoning");
        let eq_symm_export = export_by_name(eq_reasoning, "eq_symm");
        let eq_symm = index
            .entries
            .iter()
            .find(|entry| {
                entry.global_ref.module.as_dotted() == "Proofs.Ai.EqReasoning"
                    && entry.global_ref.name.as_dotted() == "eq_symm"
            })
            .unwrap();
        assert_eq!(eq_symm.kind, PackageTheoremIndexKind::Theorem);
        assert_eq!(eq_symm.global_ref.export_hash, eq_reasoning.key.export_hash);
        assert_eq!(
            eq_symm.global_ref.certificate_hash,
            eq_reasoning.key.certificate_hash
        );
        assert_eq!(
            eq_symm.global_ref.decl_interface_hash,
            PackageHash::from(eq_symm_export.decl_interface_hash)
        );
        assert_eq!(
            eq_symm.statement.core_hash,
            PackageHash::from(eq_symm_export.type_hash)
        );
        assert!(eq_symm.statement.head.is_some());
        assert!(!eq_symm.statement.constants.is_empty());
        assert_eq!(
            eq_symm.module_axiom_report_hash,
            eq_reasoning.axiom_report_hash
        );
        assert_eq!(
            eq_symm.artifact.certificate.as_str(),
            EQ_REASONING_CERTIFICATE_PATH
        );

        assert!(index.entries.iter().any(|entry| {
            entry
                .axiom_dependencies
                .iter()
                .any(|axiom| axiom.name.as_dotted() == "Eq.rec")
        }));

        let json = index.canonical_json().unwrap();
        assert_eq!(parse_package_theorem_index_json(&json).unwrap(), index);
    }

    #[test]
    fn package_axiom_report_projection_reports_non_allowlisted_axiom_without_mutating_policy() {
        let (validated, extraction, package_lock) = eq_reasoning_projection_fixture();
        let manifest = validated.manifest();

        let report = project_package_axiom_report_source_free(PackageAxiomReportProjectionInput {
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            policy: PackageArtifactPolicy {
                allow_custom_axioms: false,
                allowed_axioms: vec![Name::from_dotted("Other.allowed")],
            },
            package_lock,
            extraction: &extraction,
        })
        .unwrap();

        assert_eq!(
            report
                .policy
                .allowed_axioms
                .iter()
                .map(Name::as_dotted)
                .collect::<Vec<_>>(),
            vec!["Other.allowed"]
        );
        assert!(report.summary.policy_violation_count >= 1);
        assert!(report.modules.iter().any(|module| {
            module.policy_status.violations.iter().any(|violation| {
                violation.axiom.name.as_dotted() == "Eq.rec"
                    && violation.reason_code
                        == PackageAxiomPolicyViolationReason::AxiomNotAllowlisted
            })
        }));
    }

    #[test]
    fn package_axiom_report_projection_proof_corpus_fixture_passes_eq_rec_policy() {
        std::thread::Builder::new()
            .name(
                "package_axiom_report_projection_proof_corpus_fixture_passes_eq_rec_policy".into(),
            )
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let root = repo_root().join("testdata/package/proofs");
                let manifest_source = fs::read_to_string(root.join("npa-package.toml")).unwrap();
                let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
                let lock_source =
                    fs::read_to_string(root.join("generated/package-lock.json")).unwrap();
                let lock = parse_package_lock_json(&lock_source).unwrap();
                let buffers = proof_corpus_certificate_buffers(&validated);

                let extraction =
                    extract_package_artifacts_source_free(PackageArtifactExtractionInput {
                        validated: &validated,
                        manifest_path: PackagePath::new("npa-package.toml"),
                        manifest_bytes: manifest_source.as_bytes(),
                        package_lock: &lock,
                        certificates: certificate_artifacts(&buffers),
                        reference_summaries: PackageArtifactReferenceSummaryMode::Omit,
                    })
                    .unwrap();
                let report = project_package_axiom_report_from_extraction(
                    &validated,
                    &extraction,
                    package_lock_file_reference(&lock_source),
                )
                .unwrap();

                assert_eq!(
                    report.policy.allowed_axioms,
                    vec![Name::from_dotted("Eq.rec")]
                );
                assert!(report
                    .modules
                    .iter()
                    .all(|module| module.policy_status.status == PackageAxiomPolicyStatusKind::Ok));
                assert_eq!(
                    report.summary.local_module_count,
                    validated.manifest().modules.len() as u64
                );
                assert_eq!(
                    report.summary.external_module_count,
                    validated.manifest().imports.as_ref().map_or(0, Vec::len) as u64
                );
                let axiom_names = report
                    .modules
                    .iter()
                    .flat_map(|module| {
                        module
                            .direct_axioms
                            .iter()
                            .chain(module.transitive_axioms.iter())
                    })
                    .map(|axiom| axiom.name.as_dotted())
                    .collect::<BTreeSet<_>>();
                assert_eq!(axiom_names, BTreeSet::from(["Eq.rec".to_owned()]));
                assert!(report.summary.direct_axiom_count > 0);
                assert!(report.summary.transitive_axiom_count >= report.summary.direct_axiom_count);
                assert_eq!(report.summary.policy_violation_count, 0);
                let json = report.canonical_json().unwrap();
                assert_eq!(parse_package_axiom_report_json(&json).unwrap(), report);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn package_artifact_extraction_rejects_stale_lock_missing_artifacts_and_imports() {
        let manifest_source = basic_manifest_source();
        let validated = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let certificate_bytes = basic_certificate_bytes();
        let lock = basic_lock(&validated, &manifest_source, &certificate_bytes);

        let mut missing_input = extraction_input(
            &validated,
            &lock,
            &manifest_source,
            &certificate_bytes,
            PackageArtifactReferenceSummaryMode::Omit,
        );
        missing_input.certificates.clear();
        let missing = extract_package_artifacts_source_free(missing_input).unwrap_err();
        assert_eq!(
            missing.reason_code,
            PackageVerificationErrorReason::CertificateArtifactMissing
        );

        let mut stale_lock = lock.clone();
        stale_lock.manifest.file_hash = PackageHash::new([0x77; 32]);
        let stale = extract_package_artifacts_source_free(extraction_input(
            &validated,
            &stale_lock,
            &manifest_source,
            &certificate_bytes,
            PackageArtifactReferenceSummaryMode::Omit,
        ))
        .unwrap_err();
        assert_eq!(
            stale.reason_code,
            PackageVerificationErrorReason::PackageLockStale
        );

        let mut stale_certificate = certificate_bytes.clone();
        stale_certificate[0] ^= 0x01;
        let stale_certificate_error = extract_package_artifacts_source_free(extraction_input(
            &validated,
            &lock,
            &manifest_source,
            &stale_certificate,
            PackageArtifactReferenceSummaryMode::Omit,
        ))
        .unwrap_err();
        assert_eq!(
            stale_certificate_error.reason_code,
            PackageVerificationErrorReason::CertificateFileHashMismatch
        );

        let mut missing_import_lock = lock.clone();
        missing_import_lock.entries[0]
            .imports
            .push(PackageLockImport {
                module: Name(vec!["Missing".to_owned(), "Import".to_owned()]),
                export_hash: PackageHash::new([0x11; 32]),
                certificate_hash: PackageHash::new([0x22; 32]),
            });
        let missing_import = extract_package_artifacts_source_free(extraction_input(
            &validated,
            &missing_import_lock,
            &manifest_source,
            &certificate_bytes,
            PackageArtifactReferenceSummaryMode::Omit,
        ))
        .unwrap_err();
        assert_eq!(
            missing_import.reason_code,
            PackageVerificationErrorReason::LockGraphInvalid
        );
    }
}
