//! Live, source-free package artifact observations for ledger auditing.
//!
//! This module accepts only a validated manifest, an observed in-memory lock,
//! and caller-owned certificate buffers. It performs no filesystem access and
//! cannot consume source or metadata bytes.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;
use npa_checker_ref::{
    reference_checker_build_hash, REFERENCE_CHECKER_ID, REFERENCE_CHECKER_VERSION,
};
use npa_package::{
    package_file_hash, PackageHash, PackageLockArtifact, PackageLockManifest,
    ValidatedPackageManifest,
};

use crate::package_verifier::{
    verify_package_reference_source_free_execution_with_validation, PackageCertificateArtifact,
    PackageModuleVerificationStatus, PackageVerificationError, PackageVerificationExecutionOptions,
    PackageVerificationInputValidationMode, PackageVerificationMemoMode,
};

/// Built-in reference-checker identity used for one audit observation.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerCheckerIdentity {
    /// Stable checker id.
    pub checker_id: String,
    /// Reference-checker crate version.
    pub checker_version: String,
    /// Deterministic logical checker build identity.
    pub checker_build_hash: PackageHash,
}

/// Live checker status for one observed module.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageArtifactLedgerCheckerStatus {
    /// The live reference checker accepted the module.
    Checked,
    /// The module was attempted and rejected.
    Rejected,
    /// Verification was skipped after an earlier executed module failed.
    Blocked,
    /// A command-level prerequisite prevented the verifier loop from starting.
    NotRun,
}

/// One package module's live checker observation.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerCheckerModuleObservation {
    /// Canonical module name.
    pub module: Name,
    /// Whether the module was explicitly selected for ledger reporting.
    pub selected_for_ledger: bool,
    /// Exact hash of the supplied certificate buffer.
    pub certificate_file_hash: PackageHash,
    /// Checker-accepted export hash, available only for checked modules.
    pub export_hash: Option<PackageHash>,
    /// Checker-accepted axiom-report hash, available only for checked modules.
    pub axiom_report_hash: Option<PackageHash>,
    /// Checker-accepted certificate hash, available only for checked modules.
    pub certificate_hash: Option<PackageHash>,
    /// Live execution status.
    pub status: PackageArtifactLedgerCheckerStatus,
    /// Original typed verifier error for rejected or blocked modules.
    pub error: Option<PackageVerificationError>,
}

/// Source-free live checker report for the selected ledger closure.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerCheckerReport {
    /// Built-in checker identity.
    pub checker: PackageArtifactLedgerCheckerIdentity,
    /// Executed closure results in package-lock topological order.
    pub modules: Vec<PackageArtifactLedgerCheckerModuleObservation>,
}

/// Observe selected package artifacts with the live in-process reference checker.
///
/// Local manifest hash pins are comparison inputs and may drift. External pins,
/// module/import accountability, policy, decoding, and checker acceptance remain
/// strict. No cache or memoized verdict can satisfy this operation.
pub fn observe_package_artifacts_with_reference_checker<'a>(
    validated: &ValidatedPackageManifest,
    observed_lock: &PackageLockManifest,
    certificate_artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
    selected_modules: &BTreeSet<Name>,
) -> Result<PackageArtifactLedgerCheckerReport, PackageVerificationError> {
    let artifacts = certificate_artifacts.into_iter().collect::<Vec<_>>();
    let bytes_by_path = artifacts
        .iter()
        .map(|artifact| (artifact.path.clone(), artifact.bytes))
        .collect::<BTreeMap<_, _>>();
    let verifier_artifacts = artifacts.iter().map(|artifact| PackageCertificateArtifact {
        path: artifact.path.clone(),
        bytes: artifact.bytes,
    });
    let report = verify_package_reference_source_free_execution_with_validation(
        validated,
        observed_lock,
        verifier_artifacts,
        PackageVerificationExecutionOptions {
            jobs: 1,
            selected_modules: Some(selected_modules.clone()),
            memoization: PackageVerificationMemoMode::Disabled,
            collect_decode_cache_counters: false,
            ..PackageVerificationExecutionOptions::default()
        },
        PackageVerificationInputValidationMode::ObserveLocalArtifacts,
    )?;
    let mut canonical_entries = observed_lock.entries.iter().collect::<Vec<_>>();
    canonical_entries.sort_by(|left, right| left.module.cmp(&right.module));
    let entries = canonical_entries
        .into_iter()
        .enumerate()
        .map(|(index, entry)| (entry.module.clone(), (index, entry)))
        .collect::<BTreeMap<_, _>>();

    let modules = report
        .modules
        .into_iter()
        .map(|result| -> Result<_, PackageVerificationError> {
            let (entry_index, entry) = entries
                .get(&result.module)
                .expect("verifier report module must have observed-lock entry");
            let bytes = bytes_by_path.get(&entry.certificate).ok_or_else(|| {
                PackageVerificationError::certificate_artifact_missing(
                    format!("entries[{entry_index}].certificate"),
                    entry.certificate.as_str(),
                )
            })?;
            let (status, accepted) = match result.status {
                PackageModuleVerificationStatus::Passed => {
                    (PackageArtifactLedgerCheckerStatus::Checked, true)
                }
                PackageModuleVerificationStatus::Failed => {
                    (PackageArtifactLedgerCheckerStatus::Rejected, false)
                }
                PackageModuleVerificationStatus::Skipped => {
                    (PackageArtifactLedgerCheckerStatus::Blocked, false)
                }
            };
            Ok(PackageArtifactLedgerCheckerModuleObservation {
                module: result.module.clone(),
                selected_for_ledger: selected_modules.contains(&result.module),
                certificate_file_hash: package_file_hash(bytes),
                export_hash: accepted.then_some(result.export_hash),
                axiom_report_hash: accepted.then_some(result.axiom_report_hash),
                certificate_hash: accepted.then_some(result.certificate_hash),
                status,
                error: result.error,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(PackageArtifactLedgerCheckerReport {
        checker: PackageArtifactLedgerCheckerIdentity {
            checker_id: REFERENCE_CHECKER_ID.to_owned(),
            checker_version: REFERENCE_CHECKER_VERSION.to_owned(),
            checker_build_hash: PackageHash::from(reference_checker_build_hash()),
        },
        modules,
    })
}
