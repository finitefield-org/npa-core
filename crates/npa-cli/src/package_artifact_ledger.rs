//! Implementation of the non-mutating package artifact-ledger audit.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;

use npa_api::{
    observe_package_artifacts_with_reference_checker,
    PackageArtifactLedgerCheckerModuleObservation, PackageArtifactLedgerCheckerStatus,
    PackageVerificationError, PackageVerificationErrorKind, PackageVerificationErrorReason,
};
use npa_cert::Name;
use npa_checker_ref::{
    reference_checker_build_hash, REFERENCE_CHECKER_ID, REFERENCE_CHECKER_VERSION,
};
use npa_package::{
    build_package_lock_from_artifacts_allowing_local_hash_updates, format_package_hash,
    package_file_hash, parse_package_artifact_ledger_metadata, PackageArtifactLedgerMetadata,
    PackageArtifactLedgerMetadataError, PackageHash, PackageLockArtifact, PackageModule,
    PackagePath,
};

use crate::args::PackageArtifactLedgerAuditOptions;
use crate::diagnostic::{
    CommandDiagnostic, CommandResult, CommandStatus, DiagnosticKind, DiagnosticSeverity,
};
use crate::fs::{join_package_path, render_package_path};
use crate::package::{load_package_root, LoadedPackageRoot, PACKAGE_MANIFEST_PATH};

const COMMAND: &str = "package audit-artifact-ledger";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HashDriftClass {
    Consistent,
    MetadataOnlyDrift,
    ManifestOnlyDrift,
    BothLedgersSameStaleIdentity,
    BothLedgersDiverge,
    Unavailable,
}

impl HashDriftClass {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Consistent => "consistent",
            Self::MetadataOnlyDrift => "metadata_only_drift",
            Self::ManifestOnlyDrift => "manifest_only_drift",
            Self::BothLedgersSameStaleIdentity => "both_ledgers_same_stale_identity",
            Self::BothLedgersDiverge => "both_ledgers_diverge",
            Self::Unavailable => "unavailable",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IdentityParity {
    Matches,
    Drift,
    Incomplete,
}

impl IdentityParity {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Matches => "matches",
            Self::Drift => "drift",
            Self::Incomplete => "incomplete",
        }
    }
}

#[derive(Clone, Debug)]
struct ReadFailure {
    not_found: bool,
}

type SnapshotCache = BTreeMap<PackagePath, Result<Vec<u8>, ReadFailure>>;

#[derive(Default)]
struct Summary {
    local_modules: usize,
    eligible: usize,
    selected: usize,
    unselected_eligible: usize,
    skipped_without_meta: usize,
    hash_consistent: usize,
    hash_metadata_only_drift: usize,
    hash_manifest_only_drift: usize,
    hash_both_ledgers_same_stale_identity: usize,
    hash_both_ledgers_diverge: usize,
    hash_unavailable: usize,
    identity_matches: usize,
    identity_drift: usize,
    identity_incomplete: usize,
    checker_checked: usize,
    checker_rejected: usize,
    checker_blocked: usize,
    checker_not_run: usize,
    checker_support_failures: usize,
}

impl Summary {
    fn record(
        &mut self,
        hash: HashDriftClass,
        identity: IdentityParity,
        checker: PackageArtifactLedgerCheckerStatus,
    ) {
        match hash {
            HashDriftClass::Consistent => self.hash_consistent += 1,
            HashDriftClass::MetadataOnlyDrift => self.hash_metadata_only_drift += 1,
            HashDriftClass::ManifestOnlyDrift => self.hash_manifest_only_drift += 1,
            HashDriftClass::BothLedgersSameStaleIdentity => {
                self.hash_both_ledgers_same_stale_identity += 1;
            }
            HashDriftClass::BothLedgersDiverge => self.hash_both_ledgers_diverge += 1,
            HashDriftClass::Unavailable => self.hash_unavailable += 1,
        }
        match identity {
            IdentityParity::Matches => self.identity_matches += 1,
            IdentityParity::Drift => self.identity_drift += 1,
            IdentityParity::Incomplete => self.identity_incomplete += 1,
        }
        match checker {
            PackageArtifactLedgerCheckerStatus::Checked => self.checker_checked += 1,
            PackageArtifactLedgerCheckerStatus::Rejected => self.checker_rejected += 1,
            PackageArtifactLedgerCheckerStatus::Blocked => self.checker_blocked += 1,
            PackageArtifactLedgerCheckerStatus::NotRun => self.checker_not_run += 1,
            _ => self.checker_not_run += 1,
        }
    }

    fn encode(&self) -> String {
        format!(
            "local_modules={},eligible={},selected={},unselected_eligible={},skipped_without_meta={},hash_consistent={},hash_metadata_only_drift={},hash_manifest_only_drift={},hash_both_ledgers_same_stale_identity={},hash_both_ledgers_diverge={},hash_unavailable={},identity_matches={},identity_drift={},identity_incomplete={},checker_checked={},checker_rejected={},checker_blocked={},checker_not_run={},checker_support_failures={}",
            self.local_modules,
            self.eligible,
            self.selected,
            self.unselected_eligible,
            self.skipped_without_meta,
            self.hash_consistent,
            self.hash_metadata_only_drift,
            self.hash_manifest_only_drift,
            self.hash_both_ledgers_same_stale_identity,
            self.hash_both_ledgers_diverge,
            self.hash_unavailable,
            self.identity_matches,
            self.identity_drift,
            self.identity_incomplete,
            self.checker_checked,
            self.checker_rejected,
            self.checker_blocked,
            self.checker_not_run,
            self.checker_support_failures,
        )
    }
}

/// Run the package artifact-ledger audit without writing package files.
pub fn run_package_artifact_ledger_audit(
    options: PackageArtifactLedgerAuditOptions,
) -> CommandResult {
    let loaded = match load_package_root(&options.common.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let manifest = loaded.validated.manifest();
    let mut diagnostics = Vec::new();
    let selected_indices = select_modules(&loaded, &options.modules, &mut diagnostics);
    if selected_indices.is_empty() {
        return CommandResult::failed(COMMAND, loaded.root_display, diagnostics);
    }

    diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "artifact_ledger_checker_id",
        )
        .with_field("checker.id")
        .with_actual_value(REFERENCE_CHECKER_ID)
        .with_checker(REFERENCE_CHECKER_ID),
    );
    diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "artifact_ledger_checker_version",
        )
        .with_field("checker.version")
        .with_actual_value(REFERENCE_CHECKER_VERSION)
        .with_checker(REFERENCE_CHECKER_ID),
    );
    let mut build_identity = CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "artifact_ledger_checker_build_hash",
    )
    .with_field("checker.build_hash")
    .with_checker(REFERENCE_CHECKER_ID);
    build_identity.actual_hash = Some(format_package_hash(&PackageHash::from(
        reference_checker_build_hash(),
    )));
    diagnostics.push(build_identity);

    let selected_names = selected_indices
        .iter()
        .map(|index| manifest.modules[*index].module.clone())
        .collect::<BTreeSet<_>>();
    let mut cache = SnapshotCache::new();
    let mut certificate_paths = Vec::new();
    let mut seen_certificate_paths = BTreeSet::new();
    for module in &manifest.modules {
        capture_path(&loaded, &module.certificate, &mut cache);
        if seen_certificate_paths.insert(module.certificate.clone()) {
            certificate_paths.push(module.certificate.clone());
        }
    }
    for import in manifest.imports.as_deref().unwrap_or(&[]) {
        capture_path(&loaded, &import.certificate, &mut cache);
        if seen_certificate_paths.insert(import.certificate.clone()) {
            certificate_paths.push(import.certificate.clone());
        }
    }
    for index in &selected_indices {
        let module = &manifest.modules[*index];
        capture_path(&loaded, &module.source, &mut cache);
        capture_path(
            &loaded,
            module.meta.as_ref().expect("selected module has metadata"),
            &mut cache,
        );
    }

    let selected_certificate_owners = selected_indices
        .iter()
        .map(|index| {
            (
                manifest.modules[*index].certificate.clone(),
                manifest.modules[*index].module.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut first_certificate_failure = None::<String>;
    for path in &certificate_paths {
        if cache.get(path).is_some_and(Result::is_err) {
            first_certificate_failure.get_or_insert_with(|| "certificate_missing".to_owned());
            if !selected_certificate_owners.contains_key(path) {
                diagnostics.push(
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                        .with_path(render_package_path(path)),
                );
            }
        }
    }

    let mut checker_cause = first_certificate_failure;
    let mut checker_observations =
        BTreeMap::<Name, PackageArtifactLedgerCheckerModuleObservation>::new();
    let mut support_failures = 0usize;
    if checker_cause.is_none() {
        let lock_artifacts = certificate_paths.iter().map(|path| PackageLockArtifact {
            path: path.clone(),
            bytes: cache
                .get(path)
                .and_then(|result| result.as_ref().ok())
                .expect("certificate prerequisite checked")
                .as_slice(),
        });
        match build_package_lock_from_artifacts_allowing_local_hash_updates(
            &loaded.validated,
            loaded.manifest_path.clone(),
            loaded.manifest_source.as_bytes(),
            lock_artifacts,
        ) {
            Ok(observed_lock) => {
                let observer_artifacts = certificate_paths.iter().map(|path| PackageLockArtifact {
                    path: path.clone(),
                    bytes: cache
                        .get(path)
                        .and_then(|result| result.as_ref().ok())
                        .expect("certificate prerequisite checked")
                        .as_slice(),
                });
                match observe_package_artifacts_with_reference_checker(
                    &loaded.validated,
                    &observed_lock,
                    observer_artifacts,
                    &selected_names,
                ) {
                    Ok(report) => {
                        debug_assert_eq!(report.checker.checker_id, REFERENCE_CHECKER_ID);
                        for observation in report.modules {
                            if is_support_rejection(
                                observation.selected_for_ledger,
                                observation.status,
                            ) {
                                support_failures += 1;
                                diagnostics.push(checker_failure_diagnostic(&observation));
                            }
                            checker_observations.insert(observation.module.clone(), observation);
                        }
                    }
                    Err(error) => {
                        checker_cause = Some(error.reason_code.as_str().to_owned());
                        diagnostics.push(package_verification_diagnostic(&error, None));
                    }
                }
            }
            Err(error) => {
                checker_cause = Some(error.reason_code.as_str().to_owned());
                diagnostics.push(CommandDiagnostic::from_package_lock_error(&error));
            }
        }
    }

    let mut summary = Summary {
        local_modules: manifest.modules.len(),
        eligible: manifest
            .modules
            .iter()
            .filter(|module| module.meta.is_some())
            .count(),
        selected: selected_indices.len(),
        unselected_eligible: manifest
            .modules
            .iter()
            .filter(|module| module.meta.is_some())
            .count()
            .saturating_sub(selected_indices.len()),
        skipped_without_meta: manifest
            .modules
            .iter()
            .filter(|module| module.meta.is_none())
            .count(),
        checker_support_failures: support_failures,
        ..Summary::default()
    };
    let mut emitted_source_failures = BTreeSet::new();
    let mut emitted_certificate_failures = BTreeSet::new();
    let mut emitted_metadata_failures = BTreeSet::new();

    for index in selected_indices {
        let module = &manifest.modules[index];
        let meta_path = module.meta.as_ref().expect("selected module has metadata");
        let module_name = module.module.as_dotted();
        let source_result = cache.get(&module.source).expect("selected source captured");
        if source_result.is_err() && emitted_source_failures.insert(module.source.clone()) {
            diagnostics.push(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "source_missing")
                    .with_module(&module_name)
                    .with_path(render_package_path(&module.source)),
            );
        }
        let certificate_result = cache
            .get(&module.certificate)
            .expect("selected certificate captured");
        if certificate_result.is_err()
            && emitted_certificate_failures.insert(module.certificate.clone())
        {
            diagnostics.push(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                    .with_module(&module_name)
                    .with_path(render_package_path(&module.certificate)),
            );
        }

        let (metadata, metadata_cause) = parse_metadata_for_module(
            module,
            meta_path,
            cache.get(meta_path).expect("selected metadata captured"),
            &mut diagnostics,
            &mut emitted_metadata_failures,
        );

        emit_producer_identity(module, meta_path, metadata.as_ref(), &mut diagnostics);
        let identity =
            emit_identity_comparisons(module, meta_path, metadata.as_ref(), &mut diagnostics);

        let raw_source_hash = source_result
            .as_ref()
            .ok()
            .map(|bytes| package_file_hash(bytes));
        let raw_certificate_hash = certificate_result
            .as_ref()
            .ok()
            .map(|bytes| package_file_hash(bytes));
        let checker_observation = checker_observations.get(&module.module);
        let checker_status = checker_observation
            .map(|observation| observation.status)
            .unwrap_or(PackageArtifactLedgerCheckerStatus::NotRun);
        let module_checker_cause = checker_observation
            .and_then(|observation| observation.error.as_ref())
            .map(|error| {
                if checker_status == PackageArtifactLedgerCheckerStatus::Blocked {
                    "artifact_ledger_checker_blocked".to_owned()
                } else {
                    error.reason_code.as_str().to_owned()
                }
            })
            .or_else(|| checker_cause.clone())
            .unwrap_or_else(|| "artifact_ledger_checker_blocked".to_owned());

        let meta_ref = metadata.as_ref();
        emit_hash_slot(
            &mut diagnostics,
            &module_name,
            PACKAGE_MANIFEST_PATH,
            "manifest.expected_source_hash",
            Some(module.expected_source_hash),
            raw_source_hash,
            "artifact_ledger_manifest_source_hash_mismatch",
            "raw_source_file_hash",
            source_result
                .as_ref()
                .err()
                .map(|_| "source_missing")
                .unwrap_or("source_missing"),
            false,
        );
        emit_hash_slot(
            &mut diagnostics,
            &module_name,
            meta_path.as_str(),
            "metadata.source_sha256",
            meta_ref.map(|meta| meta.source_sha256),
            raw_source_hash,
            "artifact_ledger_metadata_source_hash_mismatch",
            "raw_source_file_hash",
            metadata_cause.as_deref().unwrap_or("source_missing"),
            false,
        );
        emit_hash_slot(
            &mut diagnostics,
            &module_name,
            PACKAGE_MANIFEST_PATH,
            "manifest.expected_certificate_file_hash",
            Some(module.expected_certificate_file_hash),
            raw_certificate_hash,
            "artifact_ledger_manifest_certificate_file_hash_mismatch",
            "raw_certificate_file_hash",
            "certificate_missing",
            false,
        );
        emit_hash_slot(
            &mut diagnostics,
            &module_name,
            meta_path.as_str(),
            "metadata.certificate_file_sha256",
            meta_ref.map(|meta| meta.certificate_file_sha256),
            raw_certificate_hash,
            "artifact_ledger_metadata_certificate_file_hash_mismatch",
            "raw_certificate_file_hash",
            metadata_cause.as_deref().unwrap_or("certificate_missing"),
            false,
        );
        emit_checker_hash_pair(
            module,
            meta_path,
            checker_observation.and_then(|value| value.export_hash),
            "manifest.expected_export_hash",
            "metadata.export_hash",
            module.expected_export_hash,
            meta_ref.map(|meta| meta.export_hash),
            "artifact_ledger_manifest_export_hash_mismatch",
            "artifact_ledger_metadata_export_hash_mismatch",
            "checker_export_hash",
            &module_checker_cause,
            metadata_cause.as_deref(),
            &mut diagnostics,
        );
        emit_checker_hash_pair(
            module,
            meta_path,
            checker_observation.and_then(|value| value.axiom_report_hash),
            "manifest.expected_axiom_report_hash",
            "metadata.axiom_report_hash",
            module.expected_axiom_report_hash,
            meta_ref.map(|meta| meta.axiom_report_hash),
            "artifact_ledger_manifest_axiom_report_hash_mismatch",
            "artifact_ledger_metadata_axiom_report_hash_mismatch",
            "checker_axiom_report_hash",
            &module_checker_cause,
            metadata_cause.as_deref(),
            &mut diagnostics,
        );
        emit_checker_hash_pair(
            module,
            meta_path,
            checker_observation.and_then(|value| value.certificate_hash),
            "manifest.expected_certificate_hash",
            "metadata.certificate_hash",
            module.expected_certificate_hash,
            meta_ref.map(|meta| meta.certificate_hash),
            "artifact_ledger_manifest_certificate_hash_mismatch",
            "artifact_ledger_metadata_certificate_hash_mismatch",
            "checker_certificate_hash",
            &module_checker_cause,
            metadata_cause.as_deref(),
            &mut diagnostics,
        );

        if let Some(observation) = checker_observation {
            if observation.status != PackageArtifactLedgerCheckerStatus::Checked {
                diagnostics.push(checker_failure_diagnostic(observation));
            }
        }

        let hash_class = classify_hashes(
            module,
            metadata.as_ref(),
            raw_source_hash,
            raw_certificate_hash,
            checker_observation,
        );
        diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::GeneratedArtifact,
                "artifact_ledger_module_classified",
            )
            .with_module(&module_name)
            .with_field("module_state")
            .with_actual_value(format!(
                "hash_drift_class={},identity_parity={},checker_status={}",
                hash_class.as_str(),
                identity.as_str(),
                checker_status_as_str(checker_status),
            )),
        );
        summary.record(hash_class, identity, checker_status);
    }

    diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "artifact_ledger_audit_summary",
        )
        .with_field("summary")
        .with_actual_value(summary.encode()),
    );

    let failed = diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error);
    let mut result = CommandResult::passed(COMMAND, loaded.root_display);
    result.diagnostics = diagnostics;
    if failed {
        result.status = CommandStatus::Failed;
    }
    result
}

fn is_support_rejection(
    selected_for_ledger: bool,
    status: PackageArtifactLedgerCheckerStatus,
) -> bool {
    !selected_for_ledger && status == PackageArtifactLedgerCheckerStatus::Rejected
}

fn select_modules(
    loaded: &LoadedPackageRoot,
    requested: &[Name],
    diagnostics: &mut Vec<CommandDiagnostic>,
) -> Vec<usize> {
    let modules = &loaded.validated.manifest().modules;
    if requested.is_empty() {
        let selected = modules
            .iter()
            .enumerate()
            .filter_map(|(index, module)| module.meta.as_ref().map(|_| index))
            .collect::<Vec<_>>();
        if selected.is_empty() {
            diagnostics.push(CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "artifact_ledger_no_metadata_declared",
            ));
        }
        return selected;
    }

    let requested = requested.iter().cloned().collect::<BTreeSet<_>>();
    let local_by_name = modules
        .iter()
        .enumerate()
        .map(|(index, module)| (module.module.clone(), (index, module)))
        .collect::<BTreeMap<_, _>>();
    for name in &requested {
        match local_by_name.get(name) {
            None => diagnostics.push(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "artifact_ledger_module_not_found",
                )
                .with_module(name.as_dotted()),
            ),
            Some((_, module)) if module.meta.is_none() => diagnostics.push(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "artifact_ledger_meta_not_declared",
                )
                .with_module(name.as_dotted()),
            ),
            Some(_) => {}
        }
    }
    modules
        .iter()
        .enumerate()
        .filter_map(|(index, module)| {
            (requested.contains(&module.module) && module.meta.is_some()).then_some(index)
        })
        .collect()
}

fn capture_path(loaded: &LoadedPackageRoot, path: &PackagePath, cache: &mut SnapshotCache) {
    if cache.contains_key(path) {
        return;
    }
    let full_path = join_package_path(&loaded.root, path, "artifact_ledger.path")
        .expect("validated manifest paths remain package-relative");
    let result = fs::read(full_path).map_err(|error| ReadFailure {
        not_found: error.kind() == io::ErrorKind::NotFound,
    });
    cache.insert(path.clone(), result);
}

fn parse_metadata_for_module(
    module: &PackageModule,
    path: &PackagePath,
    bytes: &Result<Vec<u8>, ReadFailure>,
    diagnostics: &mut Vec<CommandDiagnostic>,
    emitted: &mut BTreeSet<PackagePath>,
) -> (Option<PackageArtifactLedgerMetadata>, Option<String>) {
    let module_name = module.module.as_dotted();
    let source = match bytes {
        Ok(bytes) => match std::str::from_utf8(bytes) {
            Ok(source) => source,
            Err(_) => {
                let reason = "artifact_ledger_meta_invalid_json";
                if emitted.insert(path.clone()) {
                    diagnostics.push(
                        CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                            .with_module(module_name)
                            .with_path(path.as_str()),
                    );
                }
                return (None, Some(reason.to_owned()));
            }
        },
        Err(error) => {
            let reason = if error.not_found {
                "artifact_ledger_meta_missing"
            } else {
                "artifact_ledger_meta_read_failed"
            };
            if emitted.insert(path.clone()) {
                diagnostics.push(
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason)
                        .with_module(module_name)
                        .with_path(path.as_str()),
                );
            }
            return (None, Some(reason.to_owned()));
        }
    };
    match parse_package_artifact_ledger_metadata(source) {
        Ok(metadata) => (Some(metadata), None),
        Err(error) => {
            let reason = error.reason_code.as_str().to_owned();
            if emitted.insert(path.clone()) {
                diagnostics.push(metadata_error_diagnostic(module, path, &error));
            }
            (None, Some(reason))
        }
    }
}

fn metadata_error_diagnostic(
    module: &PackageModule,
    path: &PackagePath,
    error: &PackageArtifactLedgerMetadataError,
) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        error.reason_code.as_str(),
    )
    .with_module(module.module.as_dotted())
    .with_path(path.as_str());
    if let Some(field) = &error.field {
        diagnostic = diagnostic.with_field(field);
    }
    if let Some(expected) = &error.expected_value {
        diagnostic = diagnostic.with_expected_value(expected);
    }
    if let Some(actual) = &error.actual_value {
        diagnostic = diagnostic.with_actual_value(actual);
    }
    diagnostic
}

fn emit_producer_identity(
    module: &PackageModule,
    meta_path: &PackagePath,
    metadata: Option<&PackageArtifactLedgerMetadata>,
    diagnostics: &mut Vec<CommandDiagnostic>,
) {
    let module_name = module.module.as_dotted();
    if let Some(profile) = &module.producer_profile {
        diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::GeneratedArtifact,
                "artifact_ledger_manifest_producer_profile",
            )
            .with_module(&module_name)
            .with_path(PACKAGE_MANIFEST_PATH)
            .with_field("manifest.producer_profile")
            .with_actual_value(profile),
        );
    } else {
        diagnostics.push(incomplete_identity(
            &module_name,
            PACKAGE_MANIFEST_PATH,
            "manifest.producer_profile",
        ));
    }
    if let Some(metadata) = metadata {
        diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::GeneratedArtifact,
                "artifact_ledger_metadata_producer_profile",
            )
            .with_module(&module_name)
            .with_path(meta_path.as_str())
            .with_field("metadata.producer_profile")
            .with_actual_value(&metadata.producer_profile),
        );
    }
    diagnostics.push(incomplete_identity(
        &module_name,
        meta_path.as_str(),
        "producer.version",
    ));
    diagnostics.push(incomplete_identity(
        &module_name,
        meta_path.as_str(),
        "producer.build_hash",
    ));
}

fn incomplete_identity(module: &str, path: &str, field: &str) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "artifact_ledger_producer_identity_incomplete",
    )
    .with_module(module)
    .with_path(path)
    .with_field(field)
    .with_actual_value("unavailable")
}

fn emit_identity_comparisons(
    module: &PackageModule,
    meta_path: &PackagePath,
    metadata: Option<&PackageArtifactLedgerMetadata>,
    diagnostics: &mut Vec<CommandDiagnostic>,
) -> IdentityParity {
    let Some(metadata) = metadata else {
        return IdentityParity::Incomplete;
    };
    let expected_imports = format_name_set(&module.imports);
    let expected_axioms = format_name_set(module.axioms.as_deref().unwrap_or(&[]));
    let comparisons = [
        (
            "metadata.module",
            module.module.as_dotted(),
            metadata.module.as_dotted(),
        ),
        (
            "metadata.source",
            module.source.as_str().to_owned(),
            metadata.source.as_str().to_owned(),
        ),
        (
            "metadata.certificate",
            module.certificate.as_str().to_owned(),
            metadata.certificate.as_str().to_owned(),
        ),
        (
            "metadata.imports",
            expected_imports,
            format_name_set(&metadata.imports),
        ),
        (
            "metadata.axioms",
            expected_axioms,
            format_name_set(&metadata.axioms),
        ),
    ];
    let mut drift = false;
    for (field, expected, actual) in comparisons {
        drift |= emit_value_comparison(
            diagnostics,
            &module.module,
            meta_path,
            field,
            &expected,
            &actual,
        );
    }
    if let Some(expected) = &module.producer_profile {
        drift |= emit_value_comparison(
            diagnostics,
            &module.module,
            meta_path,
            "metadata.producer_profile",
            expected,
            &metadata.producer_profile,
        );
    }
    if drift {
        IdentityParity::Drift
    } else {
        IdentityParity::Matches
    }
}

fn emit_value_comparison(
    diagnostics: &mut Vec<CommandDiagnostic>,
    module: &Name,
    path: &PackagePath,
    field: &str,
    expected: &str,
    actual: &str,
) -> bool {
    let mismatch = expected != actual;
    let diagnostic = if mismatch {
        CommandDiagnostic::error(
            DiagnosticKind::GeneratedArtifact,
            "artifact_ledger_value_mismatch",
        )
    } else {
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "artifact_ledger_value_match",
        )
    };
    diagnostics.push(
        diagnostic
            .with_module(module.as_dotted())
            .with_path(path.as_str())
            .with_field(field)
            .with_expected_value(expected)
            .with_actual_value(actual),
    );
    mismatch
}

#[allow(clippy::too_many_arguments)]
fn emit_hash_slot(
    diagnostics: &mut Vec<CommandDiagnostic>,
    module: &str,
    path: &str,
    field: &str,
    expected: Option<PackageHash>,
    actual: Option<PackageHash>,
    mismatch_reason: &str,
    observation: &str,
    cause: &str,
    checker: bool,
) {
    let mut diagnostic = match (expected, actual) {
        (Some(expected), Some(actual)) if expected == actual => CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "artifact_ledger_hash_match",
        )
        .with_hashes(format_package_hash(&expected), format_package_hash(&actual)),
        (Some(expected), Some(actual)) => {
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, mismatch_reason)
                .with_hashes(format_package_hash(&expected), format_package_hash(&actual))
        }
        (expected, _) => {
            let mut unavailable = CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "artifact_ledger_comparison_unavailable",
            )
            .with_actual_value(format!(
                "observation={observation},status=unavailable,cause={cause}"
            ));
            unavailable.expected_hash = expected.map(|hash| format_package_hash(&hash));
            unavailable
        }
    }
    .with_module(module)
    .with_path(path)
    .with_field(field);
    if checker {
        diagnostic = diagnostic.with_checker(REFERENCE_CHECKER_ID);
    }
    diagnostics.push(diagnostic);
}

#[allow(clippy::too_many_arguments)]
fn emit_checker_hash_pair(
    module: &PackageModule,
    meta_path: &PackagePath,
    observation: Option<PackageHash>,
    manifest_field: &str,
    metadata_field: &str,
    manifest_hash: PackageHash,
    metadata_hash: Option<PackageHash>,
    manifest_mismatch: &str,
    metadata_mismatch: &str,
    observation_name: &str,
    checker_cause: &str,
    metadata_cause: Option<&str>,
    diagnostics: &mut Vec<CommandDiagnostic>,
) {
    let module_name = module.module.as_dotted();
    emit_hash_slot(
        diagnostics,
        &module_name,
        PACKAGE_MANIFEST_PATH,
        manifest_field,
        Some(manifest_hash),
        observation,
        manifest_mismatch,
        observation_name,
        checker_cause,
        true,
    );
    emit_hash_slot(
        diagnostics,
        &module_name,
        meta_path.as_str(),
        metadata_field,
        metadata_hash,
        observation,
        metadata_mismatch,
        observation_name,
        metadata_cause.unwrap_or(checker_cause),
        true,
    );
}

fn classify_hashes(
    module: &PackageModule,
    metadata: Option<&PackageArtifactLedgerMetadata>,
    source: Option<PackageHash>,
    certificate_file: Option<PackageHash>,
    checker: Option<&PackageArtifactLedgerCheckerModuleObservation>,
) -> HashDriftClass {
    let Some(metadata) = metadata else {
        return HashDriftClass::Unavailable;
    };
    let Some(source) = source else {
        return HashDriftClass::Unavailable;
    };
    let Some(certificate_file) = certificate_file else {
        return HashDriftClass::Unavailable;
    };
    let Some(checker) = checker.filter(|value| {
        value.status == PackageArtifactLedgerCheckerStatus::Checked
            && value.export_hash.is_some()
            && value.axiom_report_hash.is_some()
            && value.certificate_hash.is_some()
    }) else {
        return HashDriftClass::Unavailable;
    };
    let observations = [
        source,
        certificate_file,
        checker.export_hash.expect("checked export"),
        checker.axiom_report_hash.expect("checked axiom report"),
        checker.certificate_hash.expect("checked certificate"),
    ];
    let manifest_hashes = [
        module.expected_source_hash,
        module.expected_certificate_file_hash,
        module.expected_export_hash,
        module.expected_axiom_report_hash,
        module.expected_certificate_hash,
    ];
    let metadata_hashes = [
        metadata.source_sha256,
        metadata.certificate_file_sha256,
        metadata.export_hash,
        metadata.axiom_report_hash,
        metadata.certificate_hash,
    ];
    let manifest_parity = manifest_hashes == observations;
    let metadata_parity = metadata_hashes == observations;
    match (
        manifest_parity,
        metadata_parity,
        manifest_hashes == metadata_hashes,
    ) {
        (true, true, _) => HashDriftClass::Consistent,
        (true, false, _) => HashDriftClass::MetadataOnlyDrift,
        (false, true, _) => HashDriftClass::ManifestOnlyDrift,
        (false, false, true) => HashDriftClass::BothLedgersSameStaleIdentity,
        (false, false, false) => HashDriftClass::BothLedgersDiverge,
    }
}

fn checker_failure_diagnostic(
    observation: &PackageArtifactLedgerCheckerModuleObservation,
) -> CommandDiagnostic {
    match observation.status {
        PackageArtifactLedgerCheckerStatus::Blocked => {
            let earlier = observation
                .error
                .as_ref()
                .and_then(|error| error.actual_value.as_deref())
                .unwrap_or("unavailable");
            CommandDiagnostic::error(
                DiagnosticKind::ReferenceVerifier,
                "artifact_ledger_checker_blocked",
            )
            .with_module(observation.module.as_dotted())
            .with_field("checker_status")
            .with_actual_value(earlier)
            .with_checker(REFERENCE_CHECKER_ID)
        }
        PackageArtifactLedgerCheckerStatus::Rejected => observation
            .error
            .as_ref()
            .map(|error| package_verification_diagnostic(error, Some(&observation.module)))
            .unwrap_or_else(|| {
                CommandDiagnostic::error(
                    DiagnosticKind::ReferenceVerifier,
                    "reference_checker_rejected",
                )
                .with_module(observation.module.as_dotted())
                .with_checker(REFERENCE_CHECKER_ID)
            }),
        PackageArtifactLedgerCheckerStatus::Checked
        | PackageArtifactLedgerCheckerStatus::NotRun => CommandDiagnostic::error(
            DiagnosticKind::ReferenceVerifier,
            "artifact_ledger_checker_blocked",
        )
        .with_module(observation.module.as_dotted())
        .with_checker(REFERENCE_CHECKER_ID),
        _ => CommandDiagnostic::error(
            DiagnosticKind::ReferenceVerifier,
            "artifact_ledger_checker_blocked",
        )
        .with_module(observation.module.as_dotted())
        .with_checker(REFERENCE_CHECKER_ID),
    }
}

fn package_verification_diagnostic(
    error: &PackageVerificationError,
    module: Option<&Name>,
) -> CommandDiagnostic {
    let kind = if error.reason_code == PackageVerificationErrorReason::AxiomPolicyRejected {
        DiagnosticKind::PackagePolicy
    } else {
        match error.kind {
            PackageVerificationErrorKind::Input => DiagnosticKind::PackageLock,
            PackageVerificationErrorKind::LockGraph => DiagnosticKind::PackageGraph,
            PackageVerificationErrorKind::Artifact => DiagnosticKind::ArtifactIo,
            PackageVerificationErrorKind::CertificateDecode => DiagnosticKind::SourceFreeBoundary,
            PackageVerificationErrorKind::CertificateIdentity => DiagnosticKind::HashMismatch,
            PackageVerificationErrorKind::Kernel => DiagnosticKind::FastVerifier,
            PackageVerificationErrorKind::ReferenceChecker => DiagnosticKind::ReferenceVerifier,
            PackageVerificationErrorKind::Phase8Adapter => DiagnosticKind::SourceFreeBoundary,
            PackageVerificationErrorKind::Dependency => DiagnosticKind::ReferenceVerifier,
        }
    };
    let mut diagnostic = CommandDiagnostic::error(kind, error.reason_code.as_str())
        .with_path(&error.path)
        .with_checker(REFERENCE_CHECKER_ID);
    if let Some(module) = error.module.as_deref() {
        diagnostic = diagnostic.with_module(module.as_str());
    } else if let Some(module) = module {
        diagnostic = diagnostic.with_module(module.as_dotted());
    }
    if let Some(checker_error) = error.checker_error.as_deref() {
        diagnostic = diagnostic
            .with_field("checker_error")
            .with_actual_value(format!(
                "kind={},reason={},section={},offset={}",
                checker_error.kind,
                checker_error
                    .reason_code
                    .as_deref()
                    .unwrap_or("unavailable"),
                checker_error.section.as_deref().unwrap_or("unavailable"),
                checker_error
                    .offset
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "unavailable".to_owned()),
            ));
    } else {
        if let Some(field) = error.field.as_deref() {
            diagnostic = diagnostic.with_field(field.as_str());
        }
        if is_verifier_hash_mismatch(error.reason_code) {
            if let (Some(expected), Some(actual)) = (&error.expected_value, &error.actual_value) {
                diagnostic = diagnostic.with_hashes(expected, actual);
            }
        } else {
            if let Some(expected) = &error.expected_value {
                diagnostic = diagnostic.with_expected_value(expected);
            }
            if let Some(actual) = &error.actual_value {
                diagnostic = diagnostic.with_actual_value(actual);
            }
        }
    }
    diagnostic
}

fn is_verifier_hash_mismatch(reason: PackageVerificationErrorReason) -> bool {
    matches!(
        reason,
        PackageVerificationErrorReason::PackageLockStale
            | PackageVerificationErrorReason::CertificateFileHashMismatch
            | PackageVerificationErrorReason::ExportHashMismatch
            | PackageVerificationErrorReason::AxiomReportHashMismatch
            | PackageVerificationErrorReason::CertificateHashMismatch
    )
}

fn checker_status_as_str(status: PackageArtifactLedgerCheckerStatus) -> &'static str {
    match status {
        PackageArtifactLedgerCheckerStatus::Checked => "checked",
        PackageArtifactLedgerCheckerStatus::Rejected => "rejected",
        PackageArtifactLedgerCheckerStatus::Blocked => "blocked",
        PackageArtifactLedgerCheckerStatus::NotRun => "not_run",
        _ => "not_run",
    }
}

fn format_name_set(names: &[Name]) -> String {
    let mut values = names.iter().map(Name::as_dotted).collect::<Vec<_>>();
    values.sort();
    values.dedup();
    format!("[{}]", values.join(","))
}

#[cfg(test)]
mod tests {
    use super::{is_support_rejection, PackageArtifactLedgerCheckerStatus};

    #[test]
    fn only_unselected_rejections_are_support_failures() {
        assert!(is_support_rejection(
            false,
            PackageArtifactLedgerCheckerStatus::Rejected
        ));
        assert!(!is_support_rejection(
            true,
            PackageArtifactLedgerCheckerStatus::Rejected
        ));
        for status in [
            PackageArtifactLedgerCheckerStatus::Checked,
            PackageArtifactLedgerCheckerStatus::Blocked,
            PackageArtifactLedgerCheckerStatus::NotRun,
        ] {
            assert!(!is_support_rejection(false, status));
        }
    }
}
