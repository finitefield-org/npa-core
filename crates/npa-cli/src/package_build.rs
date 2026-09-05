//! Implementation of `npa package build-certs`.
//!
//! The ordinary package-check result is deliberately not a public promotion
//! target for local-authoring or cached contexts.
//!
//! ```compile_fail
//! use npa_cli::package_build::PackageCertificateCheckBuild;
//! use npa_cert::LocalAuthoringModuleBuild;
//!
//! fn promote(build: LocalAuthoringModuleBuild<'_>) -> PackageCertificateCheckBuild {
//!     build.into()
//! }
//! ```

use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    io,
    io::{Read as _, Write as _},
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    time::Instant,
};

use npa_api::{
    build_std_package_module_cert, PerformanceAcceptedKernelMeasurement,
    PerformanceDeclarationMeasurement, PerformanceMeasurementLabel, PerformanceMeasurementRecorder,
    PerformancePackageSelectionObservation, LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
    STD_PACKAGE_PRODUCER_PROFILE,
};
use npa_cert::{
    AxiomPolicy, ModuleCert, ModuleCertImportRebindError, ModuleCertImportRebindOutcome,
    ModuleCertRebindExpectedIdentity, ModuleCertRebindImport, ModuleCertRebindImportOrigin, Name,
    VerifiedModule, VerifierSession,
};
use npa_frontend::{
    compile_human_source_to_observed_built_certificate_only_with_available_import_refs,
    compile_human_source_to_observed_built_certificate_output_with_available_import_refs,
    compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy,
    parse_human_module, parse_human_module_with_source_interfaces,
    resolve_human_module_with_source_interfaces, source_interface_with_certificate_hashes,
    validate_human_source_lexical_structure, FileId, HumanAuthoringImport,
    HumanCompilationObservations, HumanCompileOptions, HumanImportedSourceInterface, HumanItem,
    HumanName, HumanSourceDeclarationKind, HumanSourceDeclarationMetadata, HumanSourceInterface,
    HumanUniverseParam, Span, VerifiedImport,
};
use npa_kernel::KernelWorkCounterSink;
use npa_package::{
    build_package_lock_from_artifacts,
    build_package_lock_from_artifacts_allowing_local_hash_updates, format_package_hash,
    package_file_hash, package_graph_dependent_closure, package_graph_transitive_dependencies,
    parse_and_validate_manifest_str, parse_package_lock_json,
    refresh_package_artifact_ledger_metadata, validate_package_lock_against_manifest_graph,
    PackageArtifactLedgerDeclaration, PackageArtifactLedgerDeclarationKind,
    PackageArtifactLedgerMetadataRefreshInput, PackageBuildCheckCachedStatus,
    PackageExternalImport, PackageHash, PackageLockArtifact, PackageLockEntry,
    PackageLockEntryOrigin, PackageLockError, PackageLockImport, PackageLockManifest,
    PackageLockManifestReference, PackageManifest, PackageModule, PackagePath,
    ResolvedModuleImportKind, TargetedAuthoringCertificateImportIdentity,
    TargetedAuthoringExternalModuleInput, TargetedAuthoringLocalModuleInput,
    ValidatedPackageManifest, PACKAGE_LOCK_SCHEMA,
};
use toml_edit::{DocumentMut, InlineTable, Table, Value};

use crate::args::{
    validate_package_build_certs_options, KernelFuelReportMode, PackageBuildCertsOptions,
    PackageBuildCheckCacheMode, PackageBuildOptionsValidationError, PackageBuildSelection,
    PackageCommonOptions, PackageTimingMode,
};
use crate::diagnostic::{
    CommandDiagnostic, CommandDiagnosticConversionContext, CommandDiagnosticSourceContext,
    CommandKernelFuelDiagnostic, CommandResult, DiagnosticKind,
};
use crate::fs::render_package_path;
use crate::package::{load_package_root, LoadedPackageRoot, PACKAGE_MANIFEST_PATH};
use crate::package_build_cache::{
    coalesced_build_check_cache_unavailable_diagnostic, finalize_package_build_check_cache_run,
    finalize_package_build_check_cache_run_outcomes,
    prepare_package_build_check_and_support_cache_sessions_observed,
    prepare_package_build_check_cache_run, prepare_package_build_check_cache_session_observed,
    PackageBuildCacheToolIdentityObservation, PackageBuildCheckCacheOutcomeCounts,
    PackageBuildCheckCacheRun, PackageBuildCheckCacheSession, PackageBuildCheckCertificateIdentity,
    TargetedAuthoringSupportCacheSession, TARGETED_EXTERNAL_CERTIFICATE_BYTES_LIMIT,
    TARGETED_EXTERNAL_DEPENDENCY_EDGE_LIMIT, TARGETED_EXTERNAL_IMPORT_LIMIT,
};
use crate::package_promotion_transaction::TargetLock;
use crate::package_verify::changed_package_paths_observed;
use crate::source_diagnostic::{command_delimiter_context, command_source_context};
use crate::targeted_authoring_build::{
    build_targeted_authoring_execution_plan, checked_current_module_file_id,
    run_targeted_authoring_local_hit, TargetedAuthoringBuildSession, TargetedAuthoringCheckPlan,
    TargetedAuthoringCheckRun, TargetedAuthoringCurrentSnapshot, TargetedAuthoringExecutionOutcome,
    TargetedAuthoringExecutionPlan, TargetedAuthoringImportContext,
    TargetedAuthoringMeasurementSnapshot, TargetedAuthoringModuleAcceptance,
    TargetedAuthoringPlannerInput, TargetedAuthoringPublicationOrigin,
    TargetedAuthoringSupportPublicationPlanner,
};
use crate::timing::{
    PackageTimingCollector, TIMING_CACHE_LOOKUP_MS, TIMING_COMPLETION_BUILD_MS,
    TIMING_PRIORITY_BUILD_MS, TIMING_SELECTION_MS, TIMING_SOURCE_PREFLIGHT_MS,
};
use crate::{
    fs::no_follow_directory::{regular_file_identity, Directory, Identity},
    generated_artifact_writer::{
        open_package_parent_no_follow, open_package_regular_file_no_follow,
        read_package_regular_file_no_follow,
    },
};

const COMMAND: &str = "package build-certs";
const PACKAGE_LOCK_PATH: &str = "generated/package-lock.json";

fn is_std_core_builder_profile(profile: Option<&str>) -> bool {
    matches!(
        profile,
        Some(STD_PACKAGE_PRODUCER_PROFILE | LEGACY_STD_PACKAGE_PRODUCER_PROFILE)
    )
}
static NEXT_TEMPORARY_WRITE: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
#[derive(Debug, Default)]
struct CertificateReadVerifyTestCounts {
    reads_by_path: BTreeMap<String, usize>,
    verifies_by_path: BTreeMap<String, usize>,
}

#[cfg(test)]
thread_local! {
    static CERTIFICATE_READ_VERIFY_TEST_COUNTS: std::cell::RefCell<Option<CertificateReadVerifyTestCounts>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
fn observe_certificate_read_for_test(path: &PackagePath) {
    CERTIFICATE_READ_VERIFY_TEST_COUNTS.with(|counts| {
        if let Some(counts) = counts.borrow_mut().as_mut() {
            *counts
                .reads_by_path
                .entry(path.as_str().to_owned())
                .or_default() += 1;
        }
    });
}

#[cfg(not(test))]
fn observe_certificate_read_for_test(_path: &PackagePath) {}

#[cfg(test)]
fn observe_certificate_verify_for_test(path: &PackagePath) {
    CERTIFICATE_READ_VERIFY_TEST_COUNTS.with(|counts| {
        if let Some(counts) = counts.borrow_mut().as_mut() {
            *counts
                .verifies_by_path
                .entry(path.as_str().to_owned())
                .or_default() += 1;
        }
    });
}

#[cfg(not(test))]
fn observe_certificate_verify_for_test(_path: &PackagePath) {}

#[cfg(test)]
thread_local! {
    static TARGETED_REFRESH_AFTER_PREFLIGHT_TEST_HOOK: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        std::cell::RefCell::new(None);
}

#[cfg(test)]
fn run_targeted_refresh_after_preflight_test_hook() {
    TARGETED_REFRESH_AFTER_PREFLIGHT_TEST_HOOK.with(|hook| {
        if let Some(run) = hook.borrow_mut().take() {
            run();
        }
    });
}

#[cfg(not(test))]
fn run_targeted_refresh_after_preflight_test_hook() {}

/// Operation-scoped observation state shared by every package-build path.
///
/// The coordinator is intentionally finalized only by `run_package_build_certs`
/// so validation failures, cache/no-rebuild successes, and every build mode all
/// attach timing observations through the same command-result boundary.
struct PackageBuildObservationCoordinator {
    kernel_fuel_report: KernelFuelReportMode,
    timings: PackageTimingCollector,
    measurements: Option<PerformanceMeasurementRecorder>,
    kernel_work_counter_sink: Option<KernelWorkCounterSink>,
}

impl PackageBuildObservationCoordinator {
    fn new(kernel_fuel_report: KernelFuelReportMode, timing_mode: PackageTimingMode) -> Self {
        let timings = PackageTimingCollector::new(timing_mode);
        let measurement_mode = timings.measurement_mode();
        let timing_enabled = timings.is_enabled();
        Self {
            kernel_fuel_report,
            timings,
            measurements: timing_enabled
                .then(|| PerformanceMeasurementRecorder::new(measurement_mode)),
            kernel_work_counter_sink: timing_enabled.then(KernelWorkCounterSink::default),
        }
    }

    fn compile_options(&self) -> HumanCompileOptions {
        HumanCompileOptions {
            kernel_fuel_report: self.kernel_fuel_report.into(),
            ..HumanCompileOptions::default()
        }
    }

    fn kernel_work_counter_sink(&self) -> Option<&KernelWorkCounterSink> {
        self.kernel_work_counter_sink.as_ref()
    }

    fn collect_declaration_details(&self) -> bool {
        self.timings.is_detailed()
    }

    fn measurement_enabled(&self) -> bool {
        self.measurements.is_some()
    }

    fn measurements_enabled(&self) -> bool {
        self.timings.is_enabled()
    }

    fn time_selection<T>(&mut self, run: impl FnOnce() -> T) -> T {
        self.timings.time_phase(TIMING_SELECTION_MS, run)
    }

    fn initialize_refresh_timings(&mut self, targeted: bool) {
        self.timings
            .observe_elapsed_ms(TIMING_SOURCE_PREFLIGHT_MS, 0);
        if targeted {
            self.timings.observe_elapsed_ms(TIMING_PRIORITY_BUILD_MS, 0);
        }
        self.timings
            .observe_elapsed_ms(TIMING_COMPLETION_BUILD_MS, 0);
    }

    fn time_source_preflight<T>(&mut self, run: impl FnOnce(&mut Self) -> T) -> T {
        self.time_refresh_phase(TIMING_SOURCE_PREFLIGHT_MS, run)
    }

    fn time_priority_build<T>(&mut self, run: impl FnOnce(&mut Self) -> T) -> T {
        self.time_refresh_phase(TIMING_PRIORITY_BUILD_MS, run)
    }

    fn time_completion_build<T>(&mut self, run: impl FnOnce(&mut Self) -> T) -> T {
        self.time_refresh_phase(TIMING_COMPLETION_BUILD_MS, run)
    }

    fn time_refresh_phase<T>(
        &mut self,
        field: &'static str,
        run: impl FnOnce(&mut Self) -> T,
    ) -> T {
        if !self.timings.is_enabled() {
            return run(self);
        }
        let started = Instant::now();
        let value = run(self);
        self.timings.observe_elapsed_ms(
            field,
            u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX),
        );
        value
    }

    fn observe_package_selection(&mut self, observation: &PerformancePackageSelectionObservation) {
        if let Some(measurements) = self.measurements.as_mut() {
            measurements.observe_package_selection(observation);
        }
    }

    fn record_targeted_authoring_measurements(
        &mut self,
        measurements: TargetedAuthoringMeasurementSnapshot,
    ) {
        self.timings
            .observe_elapsed_ms(TIMING_CACHE_LOOKUP_MS, measurements.cache_lookup_ms());
        if let Some(recorder) = self.measurements.as_mut() {
            measurements.record(recorder);
        }
    }

    fn record_cache_tool_identity(
        &mut self,
        observation: PackageBuildCacheToolIdentityObservation,
    ) {
        if !observation.attempted {
            return;
        }
        if let Some(recorder) = self.measurements.as_mut() {
            recorder.add_counter(
                PerformanceMeasurementLabel::CacheToolIdentityBytes,
                observation.bytes,
            );
            recorder.add_counter(
                PerformanceMeasurementLabel::CacheToolIdentityElapsed,
                observation.elapsed_ns,
            );
        }
    }

    fn record_cache_entry_bytes(&mut self, bytes_loaded: usize, bytes_written: usize) {
        if let Some(recorder) = self.measurements.as_mut() {
            recorder.add_counter(
                PerformanceMeasurementLabel::CacheBytesLoaded,
                u64::try_from(bytes_loaded).unwrap_or(u64::MAX),
            );
            recorder.add_counter(
                PerformanceMeasurementLabel::CacheBytesWritten,
                u64::try_from(bytes_written).unwrap_or(u64::MAX),
            );
        }
    }

    fn record_cache_lookup_ms(&mut self, elapsed_ms: u64) {
        self.timings
            .observe_elapsed_ms(TIMING_CACHE_LOOKUP_MS, elapsed_ms);
    }

    fn record_declaration_batch(
        &mut self,
        module: &Name,
        observations: HumanCompilationObservations,
    ) {
        let include_kernel =
            self.timings.is_detailed() && self.kernel_fuel_report == KernelFuelReportMode::Detailed;
        let declarations = observations
            .declarations
            .into_iter()
            .map(|observation| PerformanceDeclarationMeasurement {
                module: module.as_dotted(),
                declaration_index: observation.declaration_index,
                declaration: observation.declaration,
                term_nodes: observation.term_nodes,
                elaboration_elapsed_ns: observation.elaboration_elapsed_ns,
                kernel: include_kernel
                    .then_some(observation.kernel.as_ref())
                    .flatten()
                    .and_then(PerformanceAcceptedKernelMeasurement::from_frontend),
            })
            .collect();
        if let Some(measurements) = self.measurements.as_mut() {
            measurements.record_declaration_batch(
                observations.attempted,
                observations.overflowed,
                declarations,
            );
        }
    }

    fn finish(mut self, result: CommandResult) -> CommandResult {
        if let Some(mut measurements) = self.measurements.take() {
            if let Some(sink) = &self.kernel_work_counter_sink {
                measurements.observe_kernel_work_counters(sink.snapshot());
            }
            self.timings.observe_measurements(measurements.report());
        }
        self.timings.finish_result(result)
    }
}

#[derive(Clone, Debug)]
struct CertificateArtifactBuffer {
    path: PackagePath,
    bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
struct LocalCertificateBuild {
    module_index: usize,
    module: Name,
    path: PackagePath,
    bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
struct PackageCertificateBuild {
    local_certificates: Vec<LocalCertificateBuild>,
    package_lock_json: String,
}

#[derive(Clone, Debug)]
struct PackageCertificateCheckBuild {
    local_certificates: Vec<PackageBuildCheckCertificateIdentity>,
    package_lock_json: String,
    diagnostic: Option<CommandDiagnostic>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct PackageCertificateRefreshBuild {
    local_modules: Vec<LocalModuleRefreshIdentity>,
    unchanged_artifacts: Vec<CertificateArtifactBuffer>,
    refreshed_manifest_source: String,
    package_lock_json: String,
    targeted_refresh_stats: Option<TargetedRefreshStats>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct LocalModuleRefreshIdentity {
    module_index: usize,
    module: Name,
    source_hash: PackageHash,
    source_imports: Option<Vec<Name>>,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
    certificate_path: PackagePath,
    certificate_bytes: Vec<u8>,
    metadata_path: Option<PackagePath>,
    metadata_bytes: Option<Vec<u8>>,
}

#[derive(Clone, Debug)]
struct ManifestHashRefreshIdentity {
    module_index: usize,
    module: Name,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct RefreshAvailableModule {
    verified: Arc<VerifiedModule>,
    source_interface: HumanImportedSourceInterface,
    remaining_uses: usize,
    origin: RefreshImportOrigin,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RefreshImportOrigin {
    Local,
    External,
}

#[derive(Clone, Debug)]
struct AvailableModule {
    verified: Arc<VerifiedModule>,
    source_interface: HumanImportedSourceInterface,
    remaining_uses: usize,
}

type DirectImportContext = (Vec<Arc<VerifiedModule>>, Vec<HumanImportedSourceInterface>);
type RefreshedModuleMetadata = (Option<PackagePath>, Option<Vec<u8>>);

#[derive(Debug)]
enum LocalModuleCheckBuild {
    Verified {
        certificate: ModuleCert,
        generated_bytes: Vec<u8>,
        verified: Box<VerifiedModule>,
        source_interface: Box<HumanSourceInterface>,
    },
    Unverified {
        certificate: ModuleCert,
        generated_bytes: Vec<u8>,
        source_interface: Option<Box<HumanSourceInterface>>,
    },
}

impl LocalModuleCheckBuild {
    fn certificate(&self) -> &ModuleCert {
        match self {
            Self::Verified { certificate, .. } | Self::Unverified { certificate, .. } => {
                certificate
            }
        }
    }

    fn generated_bytes(&self) -> &[u8] {
        match self {
            Self::Verified {
                generated_bytes, ..
            }
            | Self::Unverified {
                generated_bytes, ..
            } => generated_bytes,
        }
    }
}

#[derive(Debug)]
struct PendingWrite {
    path: PackagePath,
    directory: Directory,
    leaf: OsString,
    temp: OsString,
    temp_identity: Identity,
    reason_code: &'static str,
    module: Option<Name>,
    previous_bytes: Option<Vec<u8>>,
    replacement_bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
struct PackageBuildSelectionPlan {
    mode: &'static str,
    promotion: PackageBuildSelectionPromotion,
    seeds: BTreeSet<usize>,
    rebuild: Vec<usize>,
    support_local: BTreeSet<usize>,
    support_external: BTreeSet<usize>,
    changed_external: BTreeSet<usize>,
    lock_selected: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PackageBuildSelectionPromotion {
    None,
    ManifestChanged,
}

impl PackageBuildSelectionPromotion {
    const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::ManifestChanged => "manifest_changed",
        }
    }
}

#[derive(Clone, Debug)]
struct TargetedRefreshLocalPlan {
    structural_seed_order: Vec<usize>,
    priority_local_order: Vec<usize>,
    priority_rebuild: BTreeSet<usize>,
    priority_support: BTreeSet<usize>,
    priority_external_roots: BTreeSet<usize>,
    completion_local_order: Vec<usize>,
    completion_rebuild: BTreeSet<usize>,
    completion_support: BTreeSet<usize>,
    completion_snapshot: BTreeSet<usize>,
}

impl TargetedRefreshLocalPlan {
    fn diagnostic(&self, declared_external: usize) -> CommandDiagnostic {
        CommandDiagnostic::info(DiagnosticKind::Build, "package_build_refresh_schedule")
            .with_field("refresh_schedule")
            .with_actual_value(format!(
                "priority_rebuild={},priority_support_local={},priority_external_roots={},declared_external={},deferred_rebuild={},deferred_support_local={},snapshot_unrelated_local={}",
                self.priority_rebuild.len(),
                self.priority_support.len(),
                self.priority_external_roots.len(),
                declared_external,
                self.completion_rebuild.len(),
                self.completion_support.len(),
                self.completion_snapshot.len(),
            ))
    }
}

#[derive(Clone, Debug)]
struct TargetedRefreshExternalPlan {
    priority_external_order: Vec<usize>,
    completion_external_order: Vec<usize>,
}

#[derive(Debug)]
struct ExternalImportDependencyDiscovery {
    order: Vec<usize>,
    certificate_bytes_by_index: BTreeMap<usize, Vec<u8>>,
    dependencies_by_index: BTreeMap<usize, Vec<usize>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RefreshModuleRole {
    CheckedSupport,
    Rebuild,
    UnrelatedSnapshot,
}

#[derive(Debug)]
struct PendingPriorityMetadata {
    verified: Arc<VerifiedModule>,
    source_interface: HumanSourceInterface,
}

#[derive(Debug)]
struct TargetedRefreshExecutionState {
    external_verifier_session: VerifierSession,
    discovered_external_bytes_by_index: BTreeMap<usize, Vec<u8>>,
    loaded_external: BTreeSet<usize>,
    processed_local: BTreeSet<usize>,
    available_modules: BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts_by_path: BTreeMap<PackagePath, CertificateArtifactBuffer>,
    pending_priority_metadata_by_index: BTreeMap<usize, PendingPriorityMetadata>,
    refreshed_modules_by_index: BTreeMap<usize, LocalModuleRefreshIdentity>,
    stats: TargetedRefreshStats,
}

impl TargetedRefreshExecutionState {
    fn new(candidate_count: usize) -> Self {
        Self {
            external_verifier_session: VerifierSession::new(),
            discovered_external_bytes_by_index: BTreeMap::new(),
            loaded_external: BTreeSet::new(),
            processed_local: BTreeSet::new(),
            available_modules: BTreeMap::new(),
            verified_modules_by_module: BTreeMap::new(),
            artifacts_by_path: BTreeMap::new(),
            pending_priority_metadata_by_index: BTreeMap::new(),
            refreshed_modules_by_index: BTreeMap::new(),
            stats: TargetedRefreshStats {
                candidates: candidate_count,
                ..TargetedRefreshStats::default()
            },
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum TargetedExternalImportSelection<'selection> {
    Seeds(&'selection BTreeSet<usize>),
    Ordered(&'selection [usize]),
}

#[derive(Clone, Debug, Default)]
struct TargetedRefreshStats {
    candidates: usize,
    source_rebuilds: usize,
    certificate_rebinds: usize,
    unchanged: usize,
    source_scans: usize,
    source_interface_reconstructions: usize,
    fallbacks: BTreeMap<&'static str, usize>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct TargetedBuildCheckStats {
    support_selected: usize,
    targets_selected: usize,
    support_live_checked: usize,
    targets_live_built: usize,
    live_support_elapsed_ns: u64,
    source_interface_resolution_elapsed_ns: u64,
    fresh_target_elapsed_ns: u64,
}

impl TargetedBuildCheckStats {
    fn new(plan: &PackageBuildSelectionPlan) -> Self {
        Self {
            support_selected: plan.support_local.len(),
            targets_selected: plan.rebuild.len(),
            ..Self::default()
        }
    }
}

#[derive(Debug)]
struct TargetedBuildCheckCacheState {
    session: PackageBuildCheckCacheSession,
    support_session: Option<TargetedAuthoringSupportCacheSession>,
    support_publication: Option<TargetedAuthoringSupportPublicationPlanner>,
    support_publication_closed: bool,
    stats: TargetedBuildCheckStats,
    certificates: Vec<PackageBuildCheckCertificateIdentity>,
    unavailable_diagnostic: Option<CommandDiagnostic>,
}

#[derive(Debug)]
struct FullReadThroughSupportWarming {
    session: TargetedAuthoringSupportCacheSession,
    publication: Option<TargetedAuthoringSupportPublicationPlanner>,
    detailed_diagnostics: bool,
}

impl FullReadThroughSupportWarming {
    fn new(session: TargetedAuthoringSupportCacheSession, detailed_diagnostics: bool) -> Self {
        Self {
            session,
            publication: None,
            detailed_diagnostics,
        }
    }

    fn prepare(
        &mut self,
        loaded: &LoadedPackageRoot,
        policy: &AxiomPolicy,
        lock_entries: &[PackageLockEntry],
        verified_modules_by_module: &BTreeMap<Name, Arc<VerifiedModule>>,
    ) {
        let external_count = loaded
            .validated
            .manifest()
            .imports
            .as_deref()
            .unwrap_or(&[])
            .len();
        if lock_entries.len() != external_count {
            self.publication = Some(TargetedAuthoringSupportPublicationPlanner::disabled(
                "external_entry_count_mismatch",
                self.detailed_diagnostics,
            ));
            return;
        }
        let mut external_inputs = Vec::with_capacity(external_count);
        for entry in lock_entries {
            let Some(verified) = verified_modules_by_module.get(&entry.module) else {
                self.publication = Some(TargetedAuthoringSupportPublicationPlanner::disabled(
                    "external_verified_module_missing",
                    self.detailed_diagnostics,
                ));
                return;
            };
            external_inputs.push(TargetedAuthoringExternalModuleInput {
                module: entry.module.clone(),
                current_certificate_file_hash: entry.certificate_file_hash,
                actual_export_hash: PackageHash::from(verified.export_hash()),
                actual_certificate_hash: PackageHash::from(verified.certificate_hash()),
            });
        }
        self.publication = Some(TargetedAuthoringSupportPublicationPlanner::new(
            self.session.namespace().cloned(),
            self.session.toolchain().cloned(),
            external_inputs,
            policy,
            self.detailed_diagnostics,
        ));
    }

    #[allow(clippy::too_many_arguments)]
    fn publish_retained_module(
        &mut self,
        loaded: &LoadedPackageRoot,
        module_index: usize,
        artifact: TargetedAuthoringLocalModuleInput,
        source: &str,
        interface: &HumanImportedSourceInterface,
        verified: &VerifiedModule,
    ) {
        let Some(publication) = self.publication.as_mut() else {
            return;
        };
        let entry = publication.observe_local(
            loaded,
            module_index,
            artifact,
            source,
            interface,
            verified,
            TargetedAuthoringPublicationOrigin::FullReadThroughRetainedModule,
            false,
            TargetedAuthoringModuleAcceptance::full_source_complete(),
        );
        if let Some(entry) = entry {
            let outcome = self.session.publish(&entry, publication.budget_mut());
            publication.record_publish_outcome(module_index, outcome);
        }
    }

    fn take_diagnostics(&mut self) -> Vec<CommandDiagnostic> {
        self.publication.as_mut().map_or_else(
            Vec::new,
            TargetedAuthoringSupportPublicationPlanner::take_diagnostics,
        )
    }

    fn observed_cache_bytes(&self) -> (usize, usize) {
        self.publication
            .as_ref()
            .map_or((0, 0), |publication| publication.observed_cache_bytes())
    }
}

impl TargetedRefreshStats {
    fn record_fallback(&mut self, reason: &'static str) {
        *self.fallbacks.entry(reason).or_default() += 1;
    }

    fn diagnostic(&self, seeds: usize) -> CommandDiagnostic {
        let fallbacks = if self.fallbacks.is_empty() {
            "none".to_owned()
        } else {
            self.fallbacks
                .iter()
                .map(|(reason, count)| format!("{reason}:{count}"))
                .collect::<Vec<_>>()
                .join("|")
        };
        CommandDiagnostic::info(DiagnosticKind::Build, "package_build_refresh_plan")
            .with_field("refresh_plan")
            .with_actual_value(format!(
                "seeds={seeds},candidates={},source_rebuild={},certificate_rebind={},unchanged={},source_scans={},source_interfaces={},fallbacks={fallbacks}",
                self.candidates,
                self.source_rebuilds,
                self.certificate_rebinds,
                self.unchanged,
                self.source_scans,
                self.source_interface_reconstructions,
            ))
    }
}

#[derive(Debug)]
enum QualifiedDependentRefresh {
    Fallback(&'static str),
    Unchanged {
        certificate: ModuleCert,
        bytes: Vec<u8>,
        verified: VerifiedModule,
        source_interface: HumanSourceInterface,
        source_imports: Vec<Name>,
    },
    Rebound {
        certificate: ModuleCert,
        bytes: Vec<u8>,
        verified: VerifiedModule,
        source_interface: HumanSourceInterface,
        source_imports: Vec<Name>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExternalImportVisitState {
    Unvisited,
    Visiting,
    Visited,
}

#[derive(Debug)]
struct ExternalImportVisitFrame {
    index: usize,
    dependencies: Vec<usize>,
    next_dependency: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExternalImportDependencyLimits {
    max_imports: usize,
    max_dependency_edges: usize,
    max_certificate_bytes: usize,
}

const TARGETED_EXTERNAL_DEPENDENCY_LIMITS: ExternalImportDependencyLimits =
    ExternalImportDependencyLimits {
        max_imports: TARGETED_EXTERNAL_IMPORT_LIMIT,
        max_dependency_edges: TARGETED_EXTERNAL_DEPENDENCY_EDGE_LIMIT,
        max_certificate_bytes: TARGETED_EXTERNAL_CERTIFICATE_BYTES_LIMIT,
    };

impl PackageBuildSelectionPlan {
    fn diagnostic(&self) -> CommandDiagnostic {
        CommandDiagnostic::info(DiagnosticKind::Build, "package_build_selection")
            .with_field("selection")
            .with_actual_value(format!(
                "mode={},seeds={},rebuild={},support_local={},support_external={},changed_external={},promotion={}",
                self.mode,
                self.seeds.len(),
                self.rebuild.len(),
                self.support_local.len(),
                self.support_external.len(),
                self.changed_external.len(),
                self.promotion.as_str(),
            ))
    }
}

/// Run `package build-certs`.
pub fn run_package_build_certs(options: PackageBuildCertsOptions) -> CommandResult {
    let mut observations =
        PackageBuildObservationCoordinator::new(options.kernel_fuel_report, options.timings);
    let result = run_package_build_certs_with_observations(options, &mut observations);
    observations.finish(result)
}

fn run_package_build_certs_with_observations(
    options: PackageBuildCertsOptions,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    if let Err(error) = validate_package_build_certs_options(&options) {
        return CommandResult::failed(
            COMMAND,
            crate::fs::render_package_root(&options.common.root),
            vec![package_build_validation_diagnostic(&options, error)],
        );
    }
    if !matches!(options.selection, PackageBuildSelection::Full) {
        return run_targeted_package_build_certs(options, observations);
    }
    if options.update_manifest_hashes {
        if options.check {
            return run_package_build_certs_refresh_check_with_observations(
                options.common,
                observations,
            );
        }
        return run_package_build_certs_refresh_write_with_observations(
            options.common,
            observations,
        );
    }
    if options.check {
        return run_package_build_certs_check_with_cache_and_observations(
            options.common,
            options.build_check_cache,
            options.build_check_cache_root,
            observations,
        );
    }
    run_package_build_certs_write_with_observations(options.common, observations)
}

fn package_build_validation_diagnostic(
    options: &PackageBuildCertsOptions,
    error: PackageBuildOptionsValidationError,
) -> CommandDiagnostic {
    match error {
        PackageBuildOptionsValidationError::BuildCheckCacheWithRefresh
        | PackageBuildOptionsValidationError::BuildCheckCacheWithoutCheck => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "unsupported_flag")
                .with_field("--build-check-cache")
                .with_actual_value(options.build_check_cache.as_str())
        }
        PackageBuildOptionsValidationError::TargetedBuildCheckCache => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "package_build_selection_invalid")
                .with_field("--build-check-cache")
                .with_actual_value(options.build_check_cache.as_str())
        }
        PackageBuildOptionsValidationError::LocalHitRequiresTargetedCheck => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "package_build_selection_invalid")
                .with_field("--build-check-cache")
                .with_actual_value(options.build_check_cache.as_str())
        }
        PackageBuildOptionsValidationError::TargetedWriteRequiresRefresh => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "targeted_write_requires_refresh")
                .with_field("selection")
                .with_expected_value("--check or --update-manifest-hashes")
        }
        PackageBuildOptionsValidationError::EmptyModuleSelection
        | PackageBuildOptionsValidationError::DuplicateModuleSelection => {
            CommandDiagnostic::error(DiagnosticKind::Usage, "package_build_selection_invalid")
                .with_field("--module")
        }
    }
}

fn run_targeted_package_build_certs(
    options: PackageBuildCertsOptions,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let loaded = match load_package_root(&options.common.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let selection_is_changed = matches!(&options.selection, PackageBuildSelection::Changed);
    let mut selection_observation = (observations.measurements_enabled() && selection_is_changed)
        .then(PerformancePackageSelectionObservation::default);
    let selection_result = observations.time_selection(|| {
        resolve_package_build_selection(
            &loaded,
            &options.selection,
            options.update_manifest_hashes,
            selection_observation.as_mut(),
        )
    });
    if let Some(observation) = selection_observation.as_ref() {
        observations.observe_package_selection(observation);
    }
    let plan = match selection_result {
        Ok(plan) => plan,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };
    let selection_diagnostic = plan.diagnostic();
    if options.build_check_cache == PackageBuildCheckCacheMode::LocalHit {
        let selected_external = plan
            .support_external
            .union(&plan.changed_external)
            .copied()
            .collect::<BTreeSet<_>>();
        let authoring_plan =
            TargetedAuthoringCheckPlan::new(plan.rebuild.len(), plan.support_local.len(), 0);
        let output = run_targeted_authoring_local_hit(
            COMMAND,
            loaded.root_display.clone(),
            selection_diagnostic,
            authoring_plan,
            observations.measurement_enabled(),
            observations.collect_declaration_details(),
            || {
                let external_order = external_import_dependency_plan(&loaded, &selected_external)
                    .map_err(|diagnostic| *diagnostic)?;
                let manifest = loaded.validated.manifest();
                let planner_input = TargetedAuthoringPlannerInput::from_package_graph(
                    &manifest.modules,
                    loaded.validated.graph(),
                    &plan.rebuild,
                    &plan.support_local,
                    external_order,
                    manifest.imports.as_deref().unwrap_or(&[]).len(),
                )?;
                build_targeted_authoring_execution_plan(planner_input)
            },
            |authoring_plan, run| {
                execute_targeted_authoring_local_hit_live(
                    &loaded,
                    &plan,
                    authoring_plan,
                    run,
                    options.build_check_cache_root.as_deref(),
                    observations,
                )
            },
        );
        let (result, measurements) = output.into_parts();
        observations.record_targeted_authoring_measurements(measurements);
        return result;
    }
    let refresh_plan_diagnostic;
    let refresh_schedule_diagnostic;
    let mut cache_state = if options.build_check_cache.uses_local_store() {
        let (session, support_session) = if plan.support_local.is_empty() {
            (
                prepare_package_build_check_cache_session_observed(
                    &loaded,
                    options.build_check_cache_root.as_deref(),
                    observations.measurement_enabled(),
                ),
                None,
            )
        } else {
            let (result, support) = prepare_package_build_check_and_support_cache_sessions_observed(
                &loaded,
                options.build_check_cache_root.as_deref(),
                observations.measurement_enabled(),
            );
            (result, Some(support))
        };
        observations.record_cache_tool_identity(session.tool_identity_observation());
        let mut session = session;
        let unavailable_diagnostic = coalesced_build_check_cache_unavailable_diagnostic(
            "read-through",
            &mut session,
            support_session.as_ref(),
        );
        Some(TargetedBuildCheckCacheState {
            session,
            support_session,
            support_publication: None,
            support_publication_closed: false,
            stats: TargetedBuildCheckStats::new(&plan),
            certificates: Vec::new(),
            unavailable_diagnostic,
        })
    } else {
        None
    };

    if plan.rebuild.is_empty() && (!options.update_manifest_hashes || !plan.lock_selected) {
        let selected_external = plan.changed_external.clone();
        if let Err(diagnostic) = build_targeted_refresh_inputs(
            &loaded,
            &plan,
            false,
            false,
            false,
            Some(TargetedExternalImportSelection::Seeds(&selected_external)),
            cache_state.as_mut(),
            None,
            None,
            None,
            observations,
        ) {
            return targeted_build_check_result_with_optional_cache(
                &loaded,
                selection_diagnostic,
                cache_state,
                Some(*diagnostic),
                false,
                observations,
            );
        }
        return targeted_build_check_result_with_optional_cache(
            &loaded,
            selection_diagnostic,
            cache_state,
            None,
            true,
            observations,
        );
    }

    if options.update_manifest_hashes {
        if let Some(diagnostic) = check_targeted_refresh_mode_targets(&loaded, &plan) {
            return targeted_failed(&loaded, selection_diagnostic, diagnostic);
        }
        let local_plan = match build_targeted_refresh_local_plan(&loaded, &plan) {
            Ok(local_plan) => local_plan,
            Err(diagnostic) => {
                return targeted_failed(&loaded, selection_diagnostic, *diagnostic);
            }
        };
        let declared_external = loaded
            .validated
            .manifest()
            .imports
            .as_deref()
            .unwrap_or(&[])
            .len();
        let schedule_diagnostic = local_plan.diagnostic(declared_external);
        observations.initialize_refresh_timings(true);
        let preflight = observations.time_source_preflight(|_| {
            preflight_human_sources(&loaded, &local_plan.structural_seed_order)
        });
        if let Err(diagnostic) = preflight {
            return targeted_failed_after_schedule(
                &loaded,
                selection_diagnostic,
                schedule_diagnostic,
                *diagnostic,
            );
        }
        run_targeted_refresh_after_preflight_test_hook();
        refresh_schedule_diagnostic = schedule_diagnostic;
        let build = match build_package_certificates_targeted_refresh(
            &loaded,
            &plan,
            &local_plan,
            observations,
        ) {
            Ok(build) => build,
            Err(diagnostic) => {
                return targeted_failed_after_schedule(
                    &loaded,
                    selection_diagnostic,
                    refresh_schedule_diagnostic,
                    *diagnostic,
                );
            }
        };
        refresh_plan_diagnostic = build
            .targeted_refresh_stats
            .as_ref()
            .map(|stats| stats.diagnostic(plan.seeds.len()));
        let diagnostic = if options.check {
            check_refreshed_package_build(&loaded, &build)
        } else {
            write_refreshed_package_build(&loaded, &build)
        };
        if let Some(diagnostic) = diagnostic {
            return targeted_failed_after_plan(
                &loaded,
                selection_diagnostic,
                refresh_schedule_diagnostic,
                refresh_plan_diagnostic,
                diagnostic,
            );
        }
    } else {
        let build = match build_package_certificates_targeted_check(
            &loaded,
            &plan,
            cache_state.as_mut(),
            None,
            None,
            None,
            observations,
        ) {
            Ok(build) => build,
            Err(diagnostic) => {
                return targeted_build_check_result_with_optional_cache(
                    &loaded,
                    selection_diagnostic,
                    cache_state,
                    Some(*diagnostic),
                    false,
                    observations,
                );
            }
        };
        return targeted_build_check_result_with_optional_cache(
            &loaded,
            selection_diagnostic,
            cache_state,
            build.diagnostic,
            true,
            observations,
        );
    }

    let mut result = CommandResult::passed(COMMAND, loaded.root_display);
    result.diagnostics.push(selection_diagnostic);
    result.diagnostics.push(refresh_schedule_diagnostic);
    if let Some(diagnostic) = refresh_plan_diagnostic {
        result.diagnostics.push(diagnostic);
    }
    result
}

fn execute_targeted_authoring_local_hit_live(
    loaded: &LoadedPackageRoot,
    plan: &PackageBuildSelectionPlan,
    authoring_plan: &TargetedAuthoringExecutionPlan,
    run: &mut TargetedAuthoringCheckRun,
    cache_root: Option<&Path>,
    observations: &mut PackageBuildObservationCoordinator,
) -> TargetedAuthoringExecutionOutcome {
    if plan.rebuild.is_empty() {
        return match build_targeted_refresh_inputs(
            loaded,
            plan,
            false,
            false,
            false,
            Some(TargetedExternalImportSelection::Ordered(
                authoring_plan.external_order(),
            )),
            None,
            Some(run),
            Some(authoring_plan),
            cache_root,
            observations,
        ) {
            Ok(_) => {
                run.record_completed_external_visits();
                TargetedAuthoringExecutionOutcome::completed(None)
            }
            Err(diagnostic) => TargetedAuthoringExecutionOutcome::stopped(*diagnostic),
        };
    }

    match build_package_certificates_targeted_check(
        loaded,
        plan,
        None,
        Some(authoring_plan),
        Some(run),
        cache_root,
        observations,
    ) {
        Ok(build) => {
            run.record_completed_external_visits();
            TargetedAuthoringExecutionOutcome::completed(build.diagnostic)
        }
        Err(diagnostic) => TargetedAuthoringExecutionOutcome::stopped(*diagnostic),
    }
}

fn targeted_build_check_result_with_optional_cache(
    loaded: &LoadedPackageRoot,
    selection: CommandDiagnostic,
    cache_state: Option<TargetedBuildCheckCacheState>,
    diagnostic: Option<CommandDiagnostic>,
    completed: bool,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let status = if diagnostic.is_some() {
        PackageBuildCheckCachedStatus::Rejected
    } else {
        PackageBuildCheckCachedStatus::Accepted
    };
    let reason = diagnostic
        .as_ref()
        .map(|diagnostic| diagnostic.reason_code.clone());
    let mut diagnostics = vec![selection];
    if let Some(diagnostic) = diagnostic {
        diagnostics.push(diagnostic);
    }
    if let Some(cache_state) = cache_state {
        let TargetedBuildCheckCacheState {
            session,
            support_session: _,
            mut support_publication,
            support_publication_closed: _,
            stats,
            certificates,
            unavailable_diagnostic,
        } = cache_state;
        let run = prepare_package_build_check_cache_run(
            session,
            loaded,
            &certificates,
            observations.measurement_enabled(),
        );
        observations.record_cache_lookup_ms(run.lookup_ms());
        if let Some(unavailable) = run.unavailable_diagnostic() {
            diagnostics.push(unavailable);
        }
        if let Some(unavailable) = unavailable_diagnostic {
            diagnostics.push(unavailable);
        }
        let outcomes =
            finalize_package_build_check_cache_run_outcomes(run, status, reason.as_deref());
        let support_context_entries_written = support_publication.as_ref().map_or(
            0,
            TargetedAuthoringSupportPublicationPlanner::entries_written,
        );
        let (support_context_bytes_loaded, support_context_bytes_written) = support_publication
            .as_ref()
            .map_or((0, 0), |publication| publication.observed_cache_bytes());
        if let Some(publication) = support_publication.as_mut() {
            diagnostics.extend(publication.take_diagnostics());
        }
        let bytes_loaded = support_context_bytes_loaded.saturating_add(outcomes.bytes_loaded);
        let bytes_written = support_context_bytes_written.saturating_add(outcomes.bytes_written);
        diagnostics.push(targeted_authoring_read_through_summary_diagnostic(
            stats,
            completed,
            support_context_entries_written,
            bytes_loaded,
            bytes_written,
        ));
        observations.record_targeted_authoring_measurements(
            TargetedAuthoringMeasurementSnapshot::read_through(
                stats.support_selected,
                stats.support_live_checked,
                stats.targets_live_built,
                stats.live_support_elapsed_ns,
                stats.source_interface_resolution_elapsed_ns,
                stats.fresh_target_elapsed_ns,
                bytes_loaded,
                bytes_written,
            ),
        );
        diagnostics.push(targeted_build_check_cache_summary_diagnostic(
            stats,
            outcomes,
            support_context_entries_written,
        ));
    }

    if status == PackageBuildCheckCachedStatus::Rejected {
        CommandResult::failed(COMMAND, loaded.root_display.clone(), diagnostics)
    } else {
        let mut result = CommandResult::passed(COMMAND, loaded.root_display.clone());
        result.diagnostics = diagnostics;
        result
    }
}

fn targeted_authoring_read_through_summary_diagnostic(
    stats: TargetedBuildCheckStats,
    complete: bool,
    entries_written: usize,
    bytes_loaded: usize,
    bytes_written: usize,
) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "targeted_authoring_cache_summary",
    )
    .with_field("targeted_authoring_cache")
    .with_actual_value(format!(
        "mode=read-through;complete={complete};support_selected={};targets_selected={};support_live_checked={};targets_live_built={};support_context_entries_written={entries_written};support_checks_avoided=0;avoided_source_interface_resolutions=0;bytes_loaded={bytes_loaded};bytes_written={bytes_written};trusted=false;build_evidence=false;proof_evidence=false",
        stats.support_selected,
        stats.targets_selected,
        stats.support_live_checked,
        stats.targets_live_built,
    ))
}

fn targeted_build_check_cache_summary_diagnostic(
    stats: TargetedBuildCheckStats,
    outcomes: PackageBuildCheckCacheOutcomeCounts,
    support_context_entries_written: usize,
) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "build_check_cache_summary",
    )
    .with_field("build_check_cache")
    .with_actual_value(format!(
        "mode=read-through;support_live_checked={};targets_live_built={};target_result_cache_hits={};target_result_cache_misses={};target_result_cache_stale={};target_result_cache_schema_misses={};target_result_entries_written={};support_context_cache_hits=0;support_context_entries_written={};support_checks_avoided=0;avoided_source_interface_resolutions=0;trusted=false;build_evidence=false",
        stats.support_live_checked,
        stats.targets_live_built,
        outcomes.hits,
        outcomes.misses,
        outcomes.stale,
        outcomes.schema_misses,
        outcomes.written,
        support_context_entries_written,
    ))
}

fn targeted_failed(
    loaded: &LoadedPackageRoot,
    selection: CommandDiagnostic,
    diagnostic: CommandDiagnostic,
) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        loaded.root_display.clone(),
        vec![selection, diagnostic],
    )
}

fn targeted_failed_after_plan(
    loaded: &LoadedPackageRoot,
    selection: CommandDiagnostic,
    refresh_schedule: CommandDiagnostic,
    refresh_plan: Option<CommandDiagnostic>,
    diagnostic: CommandDiagnostic,
) -> CommandResult {
    let mut diagnostics = vec![selection, refresh_schedule];
    if let Some(refresh_plan) = refresh_plan {
        diagnostics.push(refresh_plan);
    }
    diagnostics.push(diagnostic);
    CommandResult::failed(COMMAND, loaded.root_display.clone(), diagnostics)
}

fn targeted_failed_after_schedule(
    loaded: &LoadedPackageRoot,
    selection: CommandDiagnostic,
    refresh_schedule: CommandDiagnostic,
    diagnostic: CommandDiagnostic,
) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        loaded.root_display.clone(),
        vec![selection, refresh_schedule, diagnostic],
    )
}

fn resolve_package_build_selection(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelection,
    refresh: bool,
    observation: Option<&mut PerformancePackageSelectionObservation>,
) -> Result<PackageBuildSelectionPlan, Box<CommandDiagnostic>> {
    let manifest = loaded.validated.manifest();
    let module_by_name = manifest
        .modules
        .iter()
        .enumerate()
        .map(|(index, module)| (module.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut seeds = BTreeSet::new();
    let mut changed_external = BTreeSet::new();
    let mut lock_selected = false;
    let mut promote_full = false;
    let mode = match selection {
        PackageBuildSelection::Full => "full",
        PackageBuildSelection::Modules(modules) => {
            for module in modules {
                let Some(&module_index) = module_by_name.get(module) else {
                    return Err(Box::new(
                        CommandDiagnostic::error(
                            DiagnosticKind::PackageManifest,
                            "package_build_module_unknown",
                        )
                        .with_module(module.as_dotted())
                        .with_field("--module"),
                    ));
                };
                seeds.insert(module_index);
            }
            "modules"
        }
        PackageBuildSelection::Changed => {
            let mut selected_paths = BTreeSet::from([
                PACKAGE_MANIFEST_PATH.to_owned(),
                PACKAGE_LOCK_PATH.to_owned(),
            ]);
            for module in &manifest.modules {
                selected_paths.insert(module.source.as_str().to_owned());
                selected_paths.insert(module.certificate.as_str().to_owned());
                if let Some(meta) = &module.meta {
                    selected_paths.insert(meta.as_str().to_owned());
                }
            }
            for import in manifest.imports.as_deref().unwrap_or(&[]) {
                selected_paths.insert(import.certificate.as_str().to_owned());
            }
            let paths = changed_package_paths_observed(&loaded.root, &selected_paths, observation)
                .map_err(|error| {
                    Box::new(
                        CommandDiagnostic::error(DiagnosticKind::Internal, "git_status_failed")
                            .with_field("--changed")
                            .with_actual_value(error),
                    )
                })?;
            for path in paths {
                if path == PACKAGE_MANIFEST_PATH {
                    promote_full = true;
                    continue;
                }
                if path == PACKAGE_LOCK_PATH {
                    lock_selected = true;
                    continue;
                }
                for (module_index, module) in manifest.modules.iter().enumerate() {
                    if path == module.source.as_str()
                        || path == module.certificate.as_str()
                        || module
                            .meta
                            .as_ref()
                            .is_some_and(|meta| path == meta.as_str())
                    {
                        seeds.insert(module_index);
                    }
                }
                for (import_index, import) in manifest
                    .imports
                    .as_deref()
                    .unwrap_or(&[])
                    .iter()
                    .enumerate()
                {
                    if path == import.certificate.as_str() {
                        changed_external.insert(import_index);
                    }
                }
            }
            "changed"
        }
    };
    let promotion = if promote_full {
        seeds.extend(0..manifest.modules.len());
        PackageBuildSelectionPromotion::ManifestChanged
    } else {
        PackageBuildSelectionPromotion::None
    };
    let rebuild = if refresh {
        package_graph_dependent_closure(loaded.validated.graph(), &seeds)
    } else {
        loaded
            .validated
            .graph()
            .topological_order
            .iter()
            .copied()
            .filter(|index| seeds.contains(index))
            .collect()
    };
    let rebuild_set = rebuild.iter().copied().collect::<BTreeSet<_>>();
    let mut support_local =
        package_graph_transitive_dependencies(loaded.validated.graph(), &rebuild_set)
            .into_iter()
            .collect::<BTreeSet<_>>();
    support_local.retain(|index| !rebuild_set.contains(index));
    let mut support_external = BTreeSet::new();
    for &module_index in rebuild_set.iter().chain(support_local.iter()) {
        for import in &loaded.validated.graph().resolved_module_imports[module_index] {
            if let ResolvedModuleImportKind::External { import_index } = import.kind {
                support_external.insert(import_index);
            }
        }
    }
    Ok(PackageBuildSelectionPlan {
        mode,
        promotion,
        seeds,
        rebuild,
        support_local,
        support_external,
        changed_external,
        lock_selected,
    })
}

fn build_targeted_refresh_local_plan(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelectionPlan,
) -> Result<TargetedRefreshLocalPlan, Box<CommandDiagnostic>> {
    let graph = loaded.validated.graph();
    let module_count = loaded.validated.manifest().modules.len();
    if selection
        .seeds
        .iter()
        .chain(selection.rebuild.iter())
        .chain(selection.support_local.iter())
        .any(|index| *index >= module_count)
    {
        return Err(targeted_refresh_plan_invalid("local_index_out_of_range"));
    }

    let rebuild = selection.rebuild.iter().copied().collect::<BTreeSet<_>>();
    let mut priority = selection.seeds.clone();
    priority.extend(package_graph_transitive_dependencies(
        graph,
        &selection.seeds,
    ));
    let priority_rebuild = priority
        .intersection(&rebuild)
        .copied()
        .collect::<BTreeSet<_>>();
    let priority_support = priority
        .difference(&rebuild)
        .copied()
        .collect::<BTreeSet<_>>();
    let completion_rebuild = rebuild
        .difference(&priority_rebuild)
        .copied()
        .collect::<BTreeSet<_>>();
    let completion_support = selection
        .support_local
        .difference(&priority_support)
        .copied()
        .collect::<BTreeSet<_>>();
    let semantic = rebuild
        .union(&selection.support_local)
        .copied()
        .collect::<BTreeSet<_>>();
    let completion_snapshot = (0..module_count)
        .filter(|index| !semantic.contains(index))
        .collect::<BTreeSet<_>>();

    let structural_seed_order = graph
        .topological_order
        .iter()
        .copied()
        .filter(|index| selection.seeds.contains(index))
        .collect::<Vec<_>>();
    let priority_local_order = graph
        .topological_order
        .iter()
        .copied()
        .filter(|index| priority.contains(index))
        .collect::<Vec<_>>();
    let completion_local_order = graph
        .topological_order
        .iter()
        .copied()
        .filter(|index| !priority.contains(index))
        .collect::<Vec<_>>();
    let mut priority_external_roots = BTreeSet::new();
    for &module_index in &priority {
        let Some(imports) = graph.resolved_module_imports.get(module_index) else {
            return Err(targeted_refresh_plan_invalid("local_import_row_missing"));
        };
        for import in imports {
            if let ResolvedModuleImportKind::External { import_index } = import.kind {
                priority_external_roots.insert(import_index);
            }
        }
    }

    let plan = TargetedRefreshLocalPlan {
        structural_seed_order,
        priority_local_order,
        priority_rebuild,
        priority_support,
        priority_external_roots,
        completion_local_order,
        completion_rebuild,
        completion_support,
        completion_snapshot,
    };
    validate_targeted_refresh_local_plan(loaded, selection, &plan)?;
    Ok(plan)
}

fn validate_targeted_refresh_local_plan(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelectionPlan,
    plan: &TargetedRefreshLocalPlan,
) -> Result<(), Box<CommandDiagnostic>> {
    let graph = loaded.validated.graph();
    let module_count = loaded.validated.manifest().modules.len();
    if graph.topological_order.len() != module_count {
        return Err(targeted_refresh_plan_invalid("missing_local"));
    }
    let expected_structural = graph
        .topological_order
        .iter()
        .copied()
        .filter(|index| selection.seeds.contains(index))
        .collect::<Vec<_>>();
    if plan.structural_seed_order != expected_structural {
        return Err(targeted_refresh_plan_invalid("structural_seed_order"));
    }

    let roles = [
        &plan.priority_rebuild,
        &plan.priority_support,
        &plan.completion_rebuild,
        &plan.completion_support,
        &plan.completion_snapshot,
    ];
    let mut role_count = vec![0_u8; module_count];
    for role in roles {
        for &index in role {
            let Some(count) = role_count.get_mut(index) else {
                return Err(targeted_refresh_plan_invalid("local_index_out_of_range"));
            };
            *count = count.saturating_add(1);
            if *count > 1 {
                return Err(targeted_refresh_plan_invalid("duplicate_local"));
            }
        }
    }
    if role_count.iter().any(|count| *count != 1) {
        return Err(targeted_refresh_plan_invalid("missing_local"));
    }

    let rebuild = selection.rebuild.iter().copied().collect::<BTreeSet<_>>();
    let planned_rebuild = plan
        .priority_rebuild
        .union(&plan.completion_rebuild)
        .copied()
        .collect::<BTreeSet<_>>();
    if planned_rebuild != rebuild {
        return Err(targeted_refresh_plan_invalid("rebuild_partition_invalid"));
    }
    let planned_support = plan
        .priority_support
        .union(&plan.completion_support)
        .copied()
        .collect::<BTreeSet<_>>();
    if planned_support != selection.support_local {
        return Err(targeted_refresh_plan_invalid("support_partition_invalid"));
    }
    let priority = plan
        .priority_rebuild
        .union(&plan.priority_support)
        .copied()
        .collect::<BTreeSet<_>>();
    let completion = plan
        .completion_rebuild
        .union(&plan.completion_support)
        .copied()
        .chain(plan.completion_snapshot.iter().copied())
        .collect::<BTreeSet<_>>();
    let expected_priority_order = graph
        .topological_order
        .iter()
        .copied()
        .filter(|index| priority.contains(index))
        .collect::<Vec<_>>();
    let expected_completion_order = graph
        .topological_order
        .iter()
        .copied()
        .filter(|index| completion.contains(index))
        .collect::<Vec<_>>();
    if plan.priority_local_order != expected_priority_order {
        return Err(targeted_refresh_plan_invalid("priority_local_order"));
    }
    if plan.completion_local_order != expected_completion_order {
        return Err(targeted_refresh_plan_invalid("completion_local_order"));
    }

    let mut execution_order = plan.priority_local_order.clone();
    execution_order.extend(&plan.completion_local_order);
    if execution_order.len() != module_count {
        return Err(targeted_refresh_plan_invalid("missing_local"));
    }
    let mut positions = vec![usize::MAX; module_count];
    for (position, &index) in execution_order.iter().enumerate() {
        let Some(slot) = positions.get_mut(index) else {
            return Err(targeted_refresh_plan_invalid("local_index_out_of_range"));
        };
        if *slot != usize::MAX {
            return Err(targeted_refresh_plan_invalid("duplicate_local"));
        }
        *slot = position;
    }
    for (consumer, imports) in graph.resolved_module_imports.iter().enumerate() {
        for import in imports {
            let ResolvedModuleImportKind::Local {
                module_index: dependency,
            } = import.kind
            else {
                continue;
            };
            if positions.get(dependency).copied().unwrap_or(usize::MAX)
                >= positions.get(consumer).copied().unwrap_or(usize::MAX)
            {
                return Err(targeted_refresh_plan_invalid(
                    "local_dependency_after_consumer",
                ));
            }
        }
    }

    let external_count = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .len();
    if plan
        .priority_external_roots
        .iter()
        .any(|index| *index >= external_count)
    {
        return Err(targeted_refresh_plan_invalid("external_root_out_of_range"));
    }
    let mut expected_external_roots = BTreeSet::new();
    for &module_index in &priority {
        for import in &graph.resolved_module_imports[module_index] {
            if let ResolvedModuleImportKind::External { import_index } = import.kind {
                expected_external_roots.insert(import_index);
            }
        }
    }
    if plan.priority_external_roots != expected_external_roots {
        return Err(targeted_refresh_plan_invalid("external_roots_invalid"));
    }
    Ok(())
}

fn targeted_refresh_plan_invalid(actual: &'static str) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(DiagnosticKind::Internal, "targeted_refresh_plan_invalid")
            .with_field("refresh_schedule")
            .with_actual_value(actual),
    )
}

fn check_targeted_refresh_mode_targets(
    loaded: &LoadedPackageRoot,
    plan: &PackageBuildSelectionPlan,
) -> Option<CommandDiagnostic> {
    for &module_index in &plan.rebuild {
        let module = &loaded.validated.manifest().modules[module_index];
        if let Some(reason) = forbidden_local_certificate_write_reason(loaded, &module.certificate)
        {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::ArtifactIo,
                    "certificate_write_target_forbidden",
                )
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&module.certificate))
                .with_actual_value(reason),
            );
        }
    }
    for &module_index in &plan.rebuild {
        let module = &loaded.validated.manifest().modules[module_index];
        if let Some(metadata_path) = &module.meta {
            if let Some(reason) = forbidden_module_metadata_write_reason(loaded, metadata_path) {
                return Some(module_metadata_write_target_diagnostic(
                    module_index,
                    module,
                    metadata_path,
                    reason,
                ));
            }
        }
    }
    None
}

fn run_package_build_certs_refresh_check_with_observations(
    options: PackageCommonOptions,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_refresh_mode_targets(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    observations.initialize_refresh_timings(false);
    let structural_order = loaded.validated.graph().topological_order.clone();
    let preflight =
        observations.time_source_preflight(|_| preflight_human_sources(&loaded, &structural_order));
    if let Err(diagnostic) = preflight {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
    }

    let build = match observations.time_completion_build(|observations| {
        build_package_certificates_refresh(&loaded, observations)
    }) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    if let Some(diagnostic) = check_refreshed_package_build(&loaded, &build) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn build_package_certificates_targeted_check(
    loaded: &LoadedPackageRoot,
    plan: &PackageBuildSelectionPlan,
    cache_state: Option<&mut TargetedBuildCheckCacheState>,
    authoring_plan: Option<&TargetedAuthoringExecutionPlan>,
    authoring_run: Option<&mut TargetedAuthoringCheckRun>,
    targeted_authoring_cache_root: Option<&Path>,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<PackageCertificateCheckBuild, Box<CommandDiagnostic>> {
    let selected_external = plan
        .support_external
        .union(&plan.changed_external)
        .copied()
        .collect::<BTreeSet<_>>();
    let external_selection = authoring_plan.map_or_else(
        || TargetedExternalImportSelection::Seeds(&selected_external),
        |plan| TargetedExternalImportSelection::Ordered(plan.external_order()),
    );
    let (local_modules, _artifacts, _stats) = build_targeted_refresh_inputs(
        loaded,
        plan,
        false,
        false,
        false,
        Some(external_selection),
        cache_state,
        authoring_run,
        authoring_plan,
        targeted_authoring_cache_root,
        observations,
    )?;
    let mut local_certificates = Vec::new();
    for identity in &local_modules {
        let module = &loaded.validated.manifest().modules[identity.module_index];
        if identity.source_hash != module.expected_source_hash {
            return Ok(PackageCertificateCheckBuild {
                local_certificates,
                package_lock_json: String::new(),
                diagnostic: Some(
                    hash_mismatch(
                        "source_hash_mismatch",
                        format!("modules[{}].expected_source_hash", identity.module_index),
                        "expected_source_hash",
                        module.expected_source_hash,
                        identity.source_hash,
                    )
                    .with_module(module.module.as_dotted()),
                ),
            });
        }
        let certificate =
            npa_cert::decode_module_cert(&identity.certificate_bytes).map_err(|error| {
                Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Build, "certificate_decode_failed")
                        .with_module(module.module.as_dotted())
                        .with_path(render_package_path(&module.certificate))
                        .with_actual_value(format!("{error:?}")),
                )
            })?;
        if let Some(diagnostic) = check_generated_manifest_hashes(
            identity.module_index,
            module,
            &certificate,
            &identity.certificate_bytes,
        ) {
            return Ok(PackageCertificateCheckBuild {
                local_certificates,
                package_lock_json: String::new(),
                diagnostic: Some(diagnostic),
            });
        }
        if let Some(diagnostic) = check_local_certificate_file(
            loaded,
            identity.module_index,
            module,
            &identity.certificate_bytes,
        ) {
            let diagnostic = identity
                .source_imports
                .as_deref()
                .and_then(|source_imports| {
                    check_existing_certificate_import_drift(
                        loaded,
                        identity.module_index,
                        module,
                        source_imports,
                    )
                })
                .unwrap_or(diagnostic);
            local_certificates.push(PackageBuildCheckCertificateIdentity {
                module_index: identity.module_index,
                source_hash: identity.source_hash,
                output_certificate_format: certificate.header().format.clone(),
                output_core_spec: certificate.header().core_spec.clone(),
            });
            return Ok(PackageCertificateCheckBuild {
                local_certificates,
                package_lock_json: String::new(),
                diagnostic: Some(diagnostic),
            });
        }
        local_certificates.push(PackageBuildCheckCertificateIdentity {
            module_index: identity.module_index,
            source_hash: identity.source_hash,
            output_certificate_format: certificate.header().format.clone(),
            output_core_spec: certificate.header().core_spec.clone(),
        });
    }
    Ok(PackageCertificateCheckBuild {
        local_certificates,
        package_lock_json: String::new(),
        diagnostic: None,
    })
}

fn build_package_certificates_targeted_refresh(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelectionPlan,
    local_plan: &TargetedRefreshLocalPlan,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<PackageCertificateRefreshBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut state = TargetedRefreshExecutionState::new(selection.rebuild.len());
    let priority_empty =
        local_plan.priority_local_order.is_empty() && local_plan.priority_external_roots.is_empty();
    let external_plan = if priority_empty {
        run_targeted_refresh_priority_phase(
            loaded,
            selection,
            local_plan,
            &policy,
            &import_use_counts,
            &mut state,
            observations,
        )?
    } else {
        observations.time_priority_build(|observations| {
            run_targeted_refresh_priority_phase(
                loaded,
                selection,
                local_plan,
                &policy,
                &import_use_counts,
                &mut state,
                observations,
            )
        })?
    };

    observations.time_completion_build(|observations| {
        load_external_imports_for_targeted_refresh(
            loaded,
            &policy,
            &import_use_counts,
            &external_plan.completion_external_order,
            false,
            &mut state,
        )?;
        process_targeted_refresh_local_order(
            loaded,
            selection,
            local_plan,
            &local_plan.completion_local_order,
            false,
            &policy,
            &import_use_counts,
            &mut state,
            observations,
        )
    })?;

    let local_count = loaded.validated.manifest().modules.len();
    let external_count = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .len();
    if state.processed_local.len() != local_count {
        return Err(targeted_refresh_plan_invalid("missing_local"));
    }
    if state.loaded_external.len() != external_count {
        return Err(targeted_refresh_plan_invalid("external_partition_invalid"));
    }
    if state.refreshed_modules_by_index.len() != selection.rebuild.len() {
        return Err(targeted_refresh_plan_invalid("refreshed_local_missing"));
    }
    let (local_modules, unchanged_artifacts) =
        materialize_targeted_refresh_outputs(loaded, &mut state)?;
    let targeted_refresh_stats = state.stats;
    let refreshed_manifest_source =
        refresh_manifest_hash_fields(&loaded.manifest_source, &local_modules)?;
    let refreshed_validated = parse_and_validate_refreshed_manifest(&refreshed_manifest_source)?;
    validate_refreshed_manifest_unchanged_fields(&loaded.validated, &refreshed_validated)?;
    let package_lock_json = build_refreshed_package_lock(
        loaded,
        &refreshed_validated,
        &refreshed_manifest_source,
        &local_modules,
        &unchanged_artifacts,
    )?;
    Ok(PackageCertificateRefreshBuild {
        local_modules,
        unchanged_artifacts,
        refreshed_manifest_source,
        package_lock_json,
        targeted_refresh_stats: Some(targeted_refresh_stats),
    })
}

fn materialize_targeted_refresh_outputs(
    loaded: &LoadedPackageRoot,
    state: &mut TargetedRefreshExecutionState,
) -> Result<
    (
        Vec<LocalModuleRefreshIdentity>,
        Vec<CertificateArtifactBuffer>,
    ),
    Box<CommandDiagnostic>,
> {
    let manifest = loaded.validated.manifest();
    let topological_order = &loaded.validated.graph().topological_order;
    let mut local_modules = Vec::with_capacity(state.refreshed_modules_by_index.len());
    for &module_index in topological_order {
        if let Some(identity) = state.refreshed_modules_by_index.remove(&module_index) {
            local_modules.push(identity);
        }
    }
    if !state.refreshed_modules_by_index.is_empty() {
        return Err(targeted_refresh_plan_invalid(
            "refreshed_local_order_invalid",
        ));
    }

    let mut artifacts = Vec::with_capacity(state.artifacts_by_path.len());
    for import in manifest.imports.as_deref().unwrap_or(&[]) {
        let artifact = state
            .artifacts_by_path
            .remove(&import.certificate)
            .ok_or_else(|| targeted_refresh_plan_invalid("external_artifact_missing"))?;
        artifacts.push(artifact);
    }
    for &module_index in topological_order {
        let module = manifest
            .modules
            .get(module_index)
            .ok_or_else(|| targeted_refresh_plan_invalid("local_index_out_of_range"))?;
        if let Some(artifact) = state.artifacts_by_path.remove(&module.certificate) {
            artifacts.push(artifact);
        }
    }
    if !state.artifacts_by_path.is_empty() {
        return Err(targeted_refresh_plan_invalid("artifact_order_invalid"));
    }
    Ok((local_modules, artifacts))
}

#[allow(clippy::too_many_arguments)]
fn run_targeted_refresh_priority_phase(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelectionPlan,
    local_plan: &TargetedRefreshLocalPlan,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    state: &mut TargetedRefreshExecutionState,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<TargetedRefreshExternalPlan, Box<CommandDiagnostic>> {
    let discovery =
        external_import_dependency_discovery(loaded, &local_plan.priority_external_roots)?;
    let external_plan = build_targeted_refresh_external_plan(
        loaded,
        &local_plan.priority_external_roots,
        &discovery,
    )?;
    state.discovered_external_bytes_by_index = discovery.certificate_bytes_by_index;
    load_external_imports_for_targeted_refresh(
        loaded,
        policy,
        import_use_counts,
        &external_plan.priority_external_order,
        true,
        state,
    )?;
    if !state.discovered_external_bytes_by_index.is_empty() {
        return Err(targeted_refresh_plan_invalid(
            "external_discovery_bytes_not_consumed",
        ));
    }
    process_targeted_refresh_local_order(
        loaded,
        selection,
        local_plan,
        &local_plan.priority_local_order,
        true,
        policy,
        import_use_counts,
        state,
        observations,
    )?;
    finalize_targeted_refresh_priority_metadata(loaded, local_plan, state)?;
    Ok(external_plan)
}

#[allow(clippy::too_many_arguments)]
fn build_targeted_refresh_inputs(
    loaded: &LoadedPackageRoot,
    plan: &PackageBuildSelectionPlan,
    snapshot_unrelated: bool,
    refresh_metadata: bool,
    interface_aware: bool,
    selected_external: Option<TargetedExternalImportSelection<'_>>,
    mut targeted_check_cache: Option<&mut TargetedBuildCheckCacheState>,
    mut targeted_authoring_run: Option<&mut TargetedAuthoringCheckRun>,
    targeted_authoring_plan: Option<&TargetedAuthoringExecutionPlan>,
    targeted_authoring_cache_root: Option<&Path>,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<
    (
        Vec<LocalModuleRefreshIdentity>,
        Vec<CertificateArtifactBuffer>,
        TargetedRefreshStats,
    ),
    Box<CommandDiagnostic>,
> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut verified_modules_by_module = BTreeMap::new();
    let mut artifacts = Vec::new();
    let selected_external = match selected_external {
        Some(TargetedExternalImportSelection::Seeds(seeds)) => {
            Some(Cow::Owned(external_import_dependency_plan(loaded, seeds)?))
        }
        Some(TargetedExternalImportSelection::Ordered(order)) => Some(Cow::Borrowed(order)),
        None => None,
    };
    if let Some(diagnostic) = load_external_imports(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut verified_modules_by_module,
        &mut artifacts,
        selected_external.as_deref(),
    ) {
        return Err(Box::new(diagnostic));
    }
    if let Some(cache) = targeted_check_cache.as_deref_mut() {
        let external_inputs = targeted_authoring_external_inputs(
            loaded,
            selected_external.as_deref().unwrap_or(&[]),
            &artifacts,
            &verified_modules_by_module,
        );
        if let Some(session) = cache.support_session.as_ref() {
            cache.support_publication = Some(match external_inputs {
                Ok(external_inputs) => TargetedAuthoringSupportPublicationPlanner::new(
                    session.namespace().cloned(),
                    session.toolchain().cloned(),
                    external_inputs,
                    &policy,
                    observations.collect_declaration_details(),
                ),
                Err(_) => TargetedAuthoringSupportPublicationPlanner::disabled(
                    "external_identity_unavailable",
                    observations.collect_declaration_details(),
                ),
            });
        }
    }
    if let Some(run) = targeted_authoring_run.as_deref_mut() {
        let external_inputs = targeted_authoring_external_inputs(
            loaded,
            selected_external.as_deref().unwrap_or(&[]),
            &artifacts,
            &verified_modules_by_module,
        )?;
        run.prepare_support_lookup(
            loaded,
            targeted_authoring_cache_root,
            external_inputs,
            &policy,
        )
        .map_err(Box::new)?;
    }
    let mut refresh_available_modules = available_modules
        .into_iter()
        .map(|(module, available)| {
            (
                module,
                RefreshAvailableModule {
                    verified: available.verified,
                    source_interface: available.source_interface,
                    remaining_uses: available.remaining_uses,
                    origin: RefreshImportOrigin::External,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let rebuild = plan.rebuild.iter().copied().collect::<BTreeSet<_>>();
    let mut local_modules = Vec::new();
    let mut targeted_refresh_stats = TargetedRefreshStats {
        candidates: plan.rebuild.len(),
        ..TargetedRefreshStats::default()
    };
    if let Some(authoring_plan) = targeted_authoring_plan {
        let Some(run) = targeted_authoring_run else {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::Internal,
                    "targeted_authoring_plan_invalid",
                )
                .with_actual_value("execution_plan_without_run"),
            ));
        };
        if let Some(diagnostic) = build_local_modules_for_targeted_authoring_check(
            loaded,
            &policy,
            &import_use_counts,
            &mut refresh_available_modules,
            &mut verified_modules_by_module,
            &mut local_modules,
            &mut artifacts,
            authoring_plan,
            run,
            observations,
        ) {
            return Err(Box::new(diagnostic));
        }
        return Ok((local_modules, artifacts, targeted_refresh_stats));
    }
    if targeted_authoring_run.is_some() {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Internal, "targeted_authoring_plan_invalid")
                .with_actual_value("run_without_execution_plan"),
        ));
    }
    if let Some(diagnostic) = build_local_modules_for_refresh(
        loaded,
        &policy,
        &import_use_counts,
        &mut refresh_available_modules,
        &mut verified_modules_by_module,
        &mut local_modules,
        Some(&rebuild),
        &plan.support_local,
        snapshot_unrelated,
        refresh_metadata,
        &mut artifacts,
        Some(&plan.seeds),
        interface_aware,
        &mut targeted_refresh_stats,
        targeted_check_cache,
        targeted_authoring_run,
        observations,
    ) {
        return Err(Box::new(diagnostic));
    }
    Ok((local_modules, artifacts, targeted_refresh_stats))
}

fn run_package_build_certs_refresh_write_with_observations(
    options: PackageCommonOptions,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_refresh_mode_targets(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    observations.initialize_refresh_timings(false);
    let structural_order = loaded.validated.graph().topological_order.clone();
    let preflight =
        observations.time_source_preflight(|_| preflight_human_sources(&loaded, &structural_order));
    if let Err(diagnostic) = preflight {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
    }

    let build = match observations.time_completion_build(|observations| {
        build_package_certificates_refresh(&loaded, observations)
    }) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    if let Some(diagnostic) = write_refreshed_package_build(&loaded, &build) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn build_package_certificates_refresh(
    loaded: &LoadedPackageRoot,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<PackageCertificateRefreshBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut verified_modules_by_module = BTreeMap::new();
    let mut artifacts = Vec::new();

    if let Some(diagnostic) = load_external_imports(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut verified_modules_by_module,
        &mut artifacts,
        None,
    ) {
        return Err(Box::new(diagnostic));
    }

    let refresh_available_modules = available_modules
        .into_iter()
        .map(|(module, available)| {
            (
                module,
                RefreshAvailableModule {
                    verified: available.verified,
                    source_interface: available.source_interface,
                    remaining_uses: available.remaining_uses,
                    origin: RefreshImportOrigin::External,
                },
            )
        })
        .collect();
    let mut refresh_available_modules = refresh_available_modules;
    let mut local_modules = Vec::new();
    let mut ignored_targeted_stats = TargetedRefreshStats::default();
    if let Some(diagnostic) = build_local_modules_for_refresh(
        loaded,
        &policy,
        &import_use_counts,
        &mut refresh_available_modules,
        &mut verified_modules_by_module,
        &mut local_modules,
        None,
        &BTreeSet::new(),
        false,
        true,
        &mut artifacts,
        None,
        false,
        &mut ignored_targeted_stats,
        None,
        None,
        observations,
    ) {
        return Err(Box::new(diagnostic));
    }

    let refreshed_manifest_source =
        refresh_manifest_hash_fields(&loaded.manifest_source, &local_modules)?;
    let refreshed_validated = parse_and_validate_refreshed_manifest(&refreshed_manifest_source)?;
    validate_refreshed_manifest_unchanged_fields(&loaded.validated, &refreshed_validated)?;
    let package_lock_json = build_refreshed_package_lock(
        loaded,
        &refreshed_validated,
        &refreshed_manifest_source,
        &local_modules,
        &artifacts,
    )?;

    Ok(PackageCertificateRefreshBuild {
        local_modules,
        unchanged_artifacts: artifacts,
        refreshed_manifest_source,
        package_lock_json,
        targeted_refresh_stats: None,
    })
}

fn build_refreshed_package_lock(
    loaded: &LoadedPackageRoot,
    refreshed_validated: &ValidatedPackageManifest,
    refreshed_manifest_source: &str,
    local_modules: &[LocalModuleRefreshIdentity],
    unchanged_artifacts: &[CertificateArtifactBuffer],
) -> Result<String, Box<CommandDiagnostic>> {
    let local_artifacts = local_modules.iter().map(|module| PackageLockArtifact {
        path: module.certificate_path.clone(),
        bytes: module.certificate_bytes.as_slice(),
    });
    let unchanged_artifacts = unchanged_artifacts
        .iter()
        .map(|artifact| PackageLockArtifact {
            path: artifact.path.clone(),
            bytes: artifact.bytes.as_slice(),
        });
    let refreshed_lock = build_package_lock_from_artifacts(
        refreshed_validated,
        loaded.manifest_path.clone(),
        refreshed_manifest_source.as_bytes(),
        local_artifacts.chain(unchanged_artifacts),
    )
    .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    refreshed_lock
        .canonical_json()
        .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))
}

fn check_refreshed_package_build(
    loaded: &LoadedPackageRoot,
    build: &PackageCertificateRefreshBuild,
) -> Option<CommandDiagnostic> {
    if loaded.manifest_source.as_bytes() != build.refreshed_manifest_source.as_bytes() {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "manifest_hashes_stale")
                .with_path(PACKAGE_MANIFEST_PATH)
                .with_hashes(
                    format_package_hash(&package_file_hash(
                        build.refreshed_manifest_source.as_bytes(),
                    )),
                    format_package_hash(&package_file_hash(loaded.manifest_source.as_bytes())),
                ),
        );
    }

    let local_modules = match refresh_modules_by_manifest_order(
        &build.local_modules,
        loaded.validated.manifest().modules.len(),
    ) {
        Ok(local_modules) => local_modules,
        Err(diagnostic) => return Some(*diagnostic),
    };
    for module in local_modules {
        let manifest_module = &loaded.validated.manifest().modules[module.module_index];
        if let Some(diagnostic) = check_local_certificate_file(
            loaded,
            module.module_index,
            manifest_module,
            &module.certificate_bytes,
        ) {
            return Some(diagnostic);
        }
    }

    let local_modules = match refresh_modules_by_manifest_order(
        &build.local_modules,
        loaded.validated.manifest().modules.len(),
    ) {
        Ok(local_modules) => local_modules,
        Err(diagnostic) => return Some(*diagnostic),
    };
    for module in local_modules {
        let (Some(metadata_path), Some(expected_bytes)) =
            (&module.metadata_path, &module.metadata_bytes)
        else {
            continue;
        };
        let actual_bytes = match read_package_regular_file_no_follow(&loaded.root, metadata_path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "module_metadata_missing")
                        .with_module(module.module.as_dotted())
                        .with_path(render_package_path(metadata_path)),
                );
            }
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(
                        DiagnosticKind::ArtifactIo,
                        "module_metadata_refresh_failed",
                    )
                    .with_module(module.module.as_dotted())
                    .with_path(render_package_path(metadata_path)),
                );
            }
        };
        if actual_bytes != *expected_bytes {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::HashMismatch, "module_metadata_stale")
                    .with_module(module.module.as_dotted())
                    .with_path(render_package_path(metadata_path))
                    .with_hashes(
                        format_package_hash(&package_file_hash(expected_bytes)),
                        format_package_hash(&package_file_hash(&actual_bytes)),
                    ),
            );
        }
    }

    check_package_lock(loaded, &build.package_lock_json)
}

fn refresh_modules_by_manifest_order(
    local_modules: &[LocalModuleRefreshIdentity],
    module_count: usize,
) -> Result<Vec<&LocalModuleRefreshIdentity>, Box<CommandDiagnostic>> {
    let mut modules_by_index = vec![None; module_count];
    for module in local_modules {
        if module.module_index >= module_count {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                    .with_module(module.module.as_dotted())
                    .with_actual_value(module.module_index.to_string()),
            ));
        }
        if modules_by_index[module.module_index].is_some() {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "duplicate_module_index")
                    .with_module(module.module.as_dotted())
                    .with_actual_value(module.module_index.to_string()),
            ));
        }
        modules_by_index[module.module_index] = Some(module);
    }
    modules_by_index.into_iter().flatten().map(Ok).collect()
}

fn refresh_manifest_hash_fields(
    manifest_source: &str,
    identities: &[LocalModuleRefreshIdentity],
) -> Result<String, Box<CommandDiagnostic>> {
    let identities = identities
        .iter()
        .map(ManifestHashRefreshIdentity::from)
        .collect::<Vec<_>>();
    refresh_manifest_hash_fields_for_modules(manifest_source, &identities)
}

fn refresh_manifest_hash_fields_for_modules(
    manifest_source: &str,
    identities: &[ManifestHashRefreshIdentity],
) -> Result<String, Box<CommandDiagnostic>> {
    let mut document = manifest_source.parse::<DocumentMut>().map_err(|error| {
        manifest_refresh_failed(
            PACKAGE_MANIFEST_PATH,
            "toml",
            "valid TOML manifest",
            error.to_string(),
        )
    })?;
    let modules_item = document.get_mut("modules").ok_or_else(|| {
        manifest_refresh_failed("$.modules", "modules", "array of module tables", "missing")
    })?;
    if let Some(modules) = modules_item.as_array_of_tables_mut() {
        let identities_by_index = manifest_refresh_identities_by_index(identities, modules.len())?;
        refresh_manifest_array_of_tables_hash_fields(&identities_by_index, modules)?;
    } else if let Some(modules) = modules_item.as_array_mut() {
        let identities_by_index = manifest_refresh_identities_by_index(identities, modules.len())?;
        refresh_manifest_inline_array_hash_fields(&identities_by_index, modules)?;
    } else {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            "array of module tables",
            modules_item.type_name(),
        ));
    }

    Ok(preserve_manifest_source_layout(
        manifest_source,
        document.to_string(),
    ))
}

fn refresh_manifest_array_of_tables_hash_fields(
    identities_by_index: &[Option<&ManifestHashRefreshIdentity>],
    modules: &mut toml_edit::ArrayOfTables,
) -> Result<(), Box<CommandDiagnostic>> {
    if modules.len() != identities_by_index.len() {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            identities_by_index.len().to_string(),
            modules.len().to_string(),
        ));
    }

    for (module_index, identity) in identities_by_index.iter().copied().enumerate() {
        let path = format!("modules[{module_index}]");
        let table = modules.get_mut(module_index).ok_or_else(|| {
            manifest_refresh_failed(
                path.as_str(),
                "modules",
                "module table",
                "non-table array item",
            )
        })?;
        if let Some(identity) = identity {
            refresh_manifest_module_table_hash_fields(table, module_index, identity)?;
        }
    }

    Ok(())
}

fn refresh_manifest_inline_array_hash_fields(
    identities_by_index: &[Option<&ManifestHashRefreshIdentity>],
    modules: &mut toml_edit::Array,
) -> Result<(), Box<CommandDiagnostic>> {
    if modules.len() != identities_by_index.len() {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            identities_by_index.len().to_string(),
            modules.len().to_string(),
        ));
    }

    for (module_index, identity) in identities_by_index.iter().copied().enumerate() {
        let path = format!("modules[{module_index}]");
        let value = modules.get_mut(module_index).ok_or_else(|| {
            manifest_refresh_failed(path.as_str(), "modules", "inline module table", "missing")
        })?;
        let Some(table) = value.as_inline_table_mut() else {
            return Err(manifest_refresh_failed(
                path.as_str(),
                "modules",
                "inline module table",
                value.type_name(),
            ));
        };
        if let Some(identity) = identity {
            refresh_manifest_inline_module_hash_fields(table, module_index, identity)?;
        }
    }

    Ok(())
}

fn refresh_manifest_module_table_hash_fields(
    table: &mut Table,
    module_index: usize,
    identity: &ManifestHashRefreshIdentity,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}]");
    let module_item = table.get("module").ok_or_else(|| {
        manifest_refresh_failed(format!("{path}.module"), "module", "module name", "missing")
    })?;
    let Some(actual_module) = module_item.as_str() else {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            "string",
            module_item.type_name(),
        ));
    };
    let expected_module = identity.module.as_dotted();
    if actual_module != expected_module {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            expected_module,
            actual_module,
        ));
    }

    refresh_module_hash_field(
        table,
        module_index,
        "expected_source_hash",
        identity.source_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_certificate_file_hash",
        identity.certificate_file_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_export_hash",
        identity.export_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_axiom_report_hash",
        identity.axiom_report_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_certificate_hash",
        identity.certificate_hash,
    )?;
    Ok(())
}

fn refresh_manifest_inline_module_hash_fields(
    table: &mut InlineTable,
    module_index: usize,
    identity: &ManifestHashRefreshIdentity,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}]");
    let module_value = table.get("module").ok_or_else(|| {
        manifest_refresh_failed(format!("{path}.module"), "module", "module name", "missing")
    })?;
    let Some(actual_module) = module_value.as_str() else {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            "string",
            module_value.type_name(),
        ));
    };
    let expected_module = identity.module.as_dotted();
    if actual_module != expected_module {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            expected_module,
            actual_module,
        ));
    }

    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_source_hash",
        identity.source_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_certificate_file_hash",
        identity.certificate_file_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_export_hash",
        identity.export_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_axiom_report_hash",
        identity.axiom_report_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_certificate_hash",
        identity.certificate_hash,
    )?;
    Ok(())
}

fn manifest_refresh_identities_by_index(
    identities: &[ManifestHashRefreshIdentity],
    module_count: usize,
) -> Result<Vec<Option<&ManifestHashRefreshIdentity>>, Box<CommandDiagnostic>> {
    let mut identities_by_index = vec![None; module_count];
    for identity in identities {
        if identity.module_index >= module_count {
            return Err(manifest_refresh_failed(
                "$.modules",
                "module_index",
                format!("0..{module_count}"),
                identity.module_index.to_string(),
            ));
        }
        if identities_by_index[identity.module_index].is_some() {
            return Err(manifest_refresh_failed(
                "$.modules",
                "module_index",
                "unique module index",
                identity.module_index.to_string(),
            ));
        }
        identities_by_index[identity.module_index] = Some(identity);
    }
    Ok(identities_by_index)
}

fn refresh_module_hash_field(
    table: &mut Table,
    module_index: usize,
    field: &'static str,
    hash: PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}].{field}");
    let item = table.get_mut(field).ok_or_else(|| {
        manifest_refresh_failed(
            path.as_str(),
            field,
            "existing string hash field",
            "missing",
        )
    })?;
    let item_type = item.type_name();
    let Some(value) = item.as_value_mut() else {
        return Err(manifest_refresh_failed(
            path.as_str(),
            field,
            "string",
            item_type,
        ));
    };
    if !value.is_str() {
        return Err(manifest_refresh_failed(
            path.as_str(),
            field,
            "string",
            value.type_name(),
        ));
    }
    let refreshed_hash = format_package_hash(&hash);
    if value.as_str() == Some(refreshed_hash.as_str()) {
        return Ok(());
    }
    let decor = value.decor().clone();
    let mut replacement = Value::from(refreshed_hash);
    *replacement.decor_mut() = decor;
    *value = replacement;
    Ok(())
}

fn refresh_inline_module_hash_field(
    table: &mut InlineTable,
    module_index: usize,
    field: &'static str,
    hash: PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}].{field}");
    let value = table.get_mut(field).ok_or_else(|| {
        manifest_refresh_failed(
            path.as_str(),
            field,
            "existing string hash field",
            "missing",
        )
    })?;
    if !value.is_str() {
        return Err(manifest_refresh_failed(
            path.as_str(),
            field,
            "string",
            value.type_name(),
        ));
    }
    let refreshed_hash = format_package_hash(&hash);
    if value.as_str() == Some(refreshed_hash.as_str()) {
        return Ok(());
    }
    let decor = value.decor().clone();
    let mut replacement = Value::from(refreshed_hash);
    *replacement.decor_mut() = decor;
    *value = replacement;
    Ok(())
}

fn preserve_manifest_source_layout(original: &str, refreshed: String) -> String {
    let refreshed = preserve_manifest_trailing_newline(original, refreshed);
    match first_manifest_line_ending(original) {
        Some(ManifestLineEnding::Crlf) => normalize_manifest_line_endings_to_crlf(&refreshed),
        Some(ManifestLineEnding::Lf) | None => refreshed,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ManifestLineEnding {
    Lf,
    Crlf,
}

fn first_manifest_line_ending(source: &str) -> Option<ManifestLineEnding> {
    let bytes = source.as_bytes();
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'\n' {
            return Some(if index > 0 && bytes[index - 1] == b'\r' {
                ManifestLineEnding::Crlf
            } else {
                ManifestLineEnding::Lf
            });
        }
    }
    None
}

fn normalize_manifest_line_endings_to_crlf(source: &str) -> String {
    source.replace("\r\n", "\n").replace('\n', "\r\n")
}

fn preserve_manifest_trailing_newline(original: &str, mut refreshed: String) -> String {
    if original.ends_with('\n') {
        if !refreshed.ends_with('\n') {
            refreshed.push('\n');
        }
    } else {
        while refreshed.ends_with('\n') {
            refreshed.pop();
        }
    }
    refreshed
}

fn parse_and_validate_refreshed_manifest(
    refreshed_manifest_source: &str,
) -> Result<ValidatedPackageManifest, Box<CommandDiagnostic>> {
    parse_and_validate_manifest_str(refreshed_manifest_source).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::PackageManifest,
                "manifest_refresh_parse_failed",
            )
            .with_path(PACKAGE_MANIFEST_PATH)
            .with_actual_value(format!("{error:?}")),
        )
    })
}

fn validate_refreshed_manifest_unchanged_fields(
    original: &ValidatedPackageManifest,
    refreshed: &ValidatedPackageManifest,
) -> Result<(), Box<CommandDiagnostic>> {
    let original_manifest = original.manifest();
    let refreshed_manifest = refreshed.manifest();
    let mut normalized_refreshed = refreshed_manifest.clone();
    normalize_allowed_refresh_hash_fields(original_manifest, &mut normalized_refreshed)?;
    if &normalized_refreshed != original_manifest {
        return Err(manifest_refresh_failed(
            PACKAGE_MANIFEST_PATH,
            "unchanged_fields",
            "only local module hash pins changed",
            "refreshed manifest changed a non-refresh field",
        ));
    }
    Ok(())
}

fn normalize_allowed_refresh_hash_fields(
    original: &PackageManifest,
    refreshed: &mut PackageManifest,
) -> Result<(), Box<CommandDiagnostic>> {
    if refreshed.modules.len() != original.modules.len() {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            original.modules.len().to_string(),
            refreshed.modules.len().to_string(),
        ));
    }
    for (module_index, original_module) in original.modules.iter().enumerate() {
        let refreshed_module = &mut refreshed.modules[module_index];
        if refreshed_module.module != original_module.module {
            return Err(manifest_refresh_failed(
                format!("modules[{module_index}].module"),
                "module",
                original_module.module.as_dotted(),
                refreshed_module.module.as_dotted(),
            ));
        }
        refreshed_module.expected_source_hash = original_module.expected_source_hash;
        refreshed_module.expected_certificate_file_hash =
            original_module.expected_certificate_file_hash;
        refreshed_module.expected_export_hash = original_module.expected_export_hash;
        refreshed_module.expected_axiom_report_hash = original_module.expected_axiom_report_hash;
        refreshed_module.expected_certificate_hash = original_module.expected_certificate_hash;
    }
    Ok(())
}

impl From<&LocalModuleRefreshIdentity> for ManifestHashRefreshIdentity {
    fn from(identity: &LocalModuleRefreshIdentity) -> Self {
        Self {
            module_index: identity.module_index,
            module: identity.module.clone(),
            source_hash: identity.source_hash,
            certificate_file_hash: identity.certificate_file_hash,
            export_hash: identity.export_hash,
            axiom_report_hash: identity.axiom_report_hash,
            certificate_hash: identity.certificate_hash,
        }
    }
}

fn manifest_refresh_failed(
    path: impl Into<String>,
    field: impl Into<String>,
    expected_value: impl Into<String>,
    actual_value: impl Into<String>,
) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(DiagnosticKind::PackageManifest, "manifest_refresh_failed")
            .with_path(path)
            .with_field(field)
            .with_expected_value(expected_value)
            .with_actual_value(actual_value),
    )
}

/// Run no-write certificate rebuild checking.
///
/// This command reads package source files, local certificate files, external
/// pinned certificate artifacts, and `generated/package-lock.json`. It builds
/// local certificates in memory through the untrusted frontend, verifies the
/// generated canonical certificate bytes through `npa-cert`, and compares the
/// results to the manifest and checked-in artifacts. It does not write files.
pub fn run_package_build_certs_check(options: PackageCommonOptions) -> CommandResult {
    run_package_build_certs(crate::package_api::v1::build_certs_check(options))
}

/// Run no-write certificate rebuild checking with optional read-through cache metadata.
pub fn run_package_build_certs_check_with_cache(
    options: PackageCommonOptions,
    build_check_cache: PackageBuildCheckCacheMode,
) -> CommandResult {
    run_package_build_certs(
        crate::package_api::v1::build_certs_check(options)
            .with_build_check_cache(build_check_cache),
    )
}

fn run_package_build_certs_check_with_cache_and_observations(
    options: PackageCommonOptions,
    build_check_cache: PackageBuildCheckCacheMode,
    build_check_cache_root: Option<PathBuf>,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    let has_retained_local_module = loaded
        .validated
        .graph()
        .resolved_module_imports
        .iter()
        .flatten()
        .any(|import| matches!(import.kind, ResolvedModuleImportKind::Local { .. }));
    let (cache_session, mut support_warming, cache_unavailable_diagnostic) =
        if build_check_cache.uses_local_store() {
            if has_retained_local_module {
                let (mut result, support) =
                    prepare_package_build_check_and_support_cache_sessions_observed(
                        &loaded,
                        build_check_cache_root.as_deref(),
                        observations.measurement_enabled(),
                    );
                let unavailable = coalesced_build_check_cache_unavailable_diagnostic(
                    "read-through",
                    &mut result,
                    Some(&support),
                );
                (
                    Some(result),
                    Some(FullReadThroughSupportWarming::new(
                        support,
                        observations.collect_declaration_details(),
                    )),
                    unavailable,
                )
            } else {
                (
                    Some(prepare_package_build_check_cache_session_observed(
                        &loaded,
                        build_check_cache_root.as_deref(),
                        observations.measurement_enabled(),
                    )),
                    None,
                    None,
                )
            }
        } else {
            (None, None, None)
        };
    if let Some(session) = cache_session.as_ref() {
        observations.record_cache_tool_identity(session.tool_identity_observation());
    }

    let build =
        match build_package_certificates_check(&loaded, support_warming.as_mut(), observations) {
            Ok(build) => build,
            Err(diagnostic) => {
                let mut diagnostics = vec![*diagnostic];
                if let Some(unavailable) = cache_session
                    .as_ref()
                    .and_then(PackageBuildCheckCacheSession::unavailable_diagnostic)
                {
                    diagnostics.push(unavailable);
                }
                if let Some(unavailable) = cache_unavailable_diagnostic {
                    diagnostics.push(unavailable);
                }
                if let Some(warming) = support_warming.as_mut() {
                    let (bytes_loaded, bytes_written) = warming.observed_cache_bytes();
                    observations.record_cache_entry_bytes(bytes_loaded, bytes_written);
                    diagnostics.extend(warming.take_diagnostics());
                }
                return CommandResult::failed(COMMAND, loaded.root_display, diagnostics);
            }
        };

    if let Some(warming) = support_warming.as_ref() {
        let (bytes_loaded, bytes_written) = warming.observed_cache_bytes();
        observations.record_cache_entry_bytes(bytes_loaded, bytes_written);
    }

    let cache_run = cache_session.map(|session| {
        let run = prepare_package_build_check_cache_run(
            session,
            &loaded,
            &build.local_certificates,
            observations.measurement_enabled(),
        );
        observations.record_cache_lookup_ms(run.lookup_ms());
        run
    });

    if build.diagnostic.is_some() {
        let mut result = build_check_result_with_optional_cache(
            loaded.root_display,
            cache_run,
            build.diagnostic,
            cache_unavailable_diagnostic,
            observations,
        );
        if let Some(warming) = support_warming.as_mut() {
            result.diagnostics.extend(warming.take_diagnostics());
        }
        return result;
    }

    if let Some(diagnostic) = check_package_lock(&loaded, &build.package_lock_json) {
        let mut result = build_check_result_with_optional_cache(
            loaded.root_display,
            cache_run,
            Some(diagnostic),
            cache_unavailable_diagnostic,
            observations,
        );
        if let Some(warming) = support_warming.as_mut() {
            result.diagnostics.extend(warming.take_diagnostics());
        }
        return result;
    }

    let mut result = build_check_result_with_optional_cache(
        loaded.root_display,
        cache_run,
        None,
        cache_unavailable_diagnostic,
        observations,
    );
    if let Some(warming) = support_warming.as_mut() {
        result.diagnostics.extend(warming.take_diagnostics());
    }
    result
}

/// Run certificate rebuild write mode.
///
/// This mode uses the same complete in-memory build as `--check`, then writes
/// only command-owned certificate artifacts and the generated package lock. No
/// target file is touched until every module has built successfully.
pub fn run_package_build_certs_write(options: PackageCommonOptions) -> CommandResult {
    run_package_build_certs(crate::package_api::v1::build_certs_write(options))
}

fn run_package_build_certs_write_with_observations(
    options: PackageCommonOptions,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_write_mode_targets(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    let build = match build_package_certificates(&loaded, observations) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    if let Some(diagnostic) = write_package_build(&loaded, &build) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn check_write_mode_targets(loaded: &LoadedPackageRoot) -> Option<CommandDiagnostic> {
    for (module_index, module) in loaded.validated.manifest().modules.iter().enumerate() {
        let Some(forbidden_reason) =
            forbidden_local_certificate_write_reason(loaded, &module.certificate)
        else {
            continue;
        };
        return Some(
            CommandDiagnostic::error(
                DiagnosticKind::ArtifactIo,
                "certificate_write_target_forbidden",
            )
            .with_module(module.module.as_dotted())
            .with_path(render_package_path(&module.certificate))
            .with_field(format!("modules[{module_index}].certificate"))
            .with_expected_value("local module .npcert certificate artifact")
            .with_actual_value(forbidden_reason),
        );
    }
    None
}

fn check_refresh_mode_targets(loaded: &LoadedPackageRoot) -> Option<CommandDiagnostic> {
    if let Some(diagnostic) = check_write_mode_targets(loaded) {
        return Some(diagnostic);
    }
    for (module_index, module) in loaded.validated.manifest().modules.iter().enumerate() {
        let Some(metadata_path) = &module.meta else {
            continue;
        };
        let Some(reason) = forbidden_module_metadata_write_reason(loaded, metadata_path) else {
            continue;
        };
        return Some(module_metadata_write_target_diagnostic(
            module_index,
            module,
            metadata_path,
            reason,
        ));
    }
    None
}

fn module_metadata_write_target_diagnostic(
    module_index: usize,
    module: &PackageModule,
    path: &PackagePath,
    reason: &'static str,
) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::ArtifactIo,
        "module_metadata_write_target_forbidden",
    )
    .with_module(module.module.as_dotted())
    .with_path(render_package_path(path))
    .with_field(format!("modules[{module_index}].meta"))
    .with_expected_value("module metadata sidecar distinct from command-owned artifacts")
    .with_actual_value(reason)
}

fn forbidden_module_metadata_write_reason(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
) -> Option<&'static str> {
    if path == &loaded.manifest_path {
        return Some("package_manifest");
    }
    if path.as_str() == PACKAGE_LOCK_PATH {
        return Some("package_lock");
    }
    if loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .any(|import| import.certificate == *path)
    {
        return Some("external_import_certificate");
    }
    None
}

fn forbidden_local_certificate_write_reason(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
) -> Option<&'static str> {
    if path == &loaded.manifest_path {
        return Some("package_manifest");
    }
    if path.as_str() == PACKAGE_LOCK_PATH {
        return Some("package_lock");
    }
    if loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .any(|import| import.certificate == *path)
    {
        return Some("external_import_certificate");
    }
    for module in &loaded.validated.manifest().modules {
        if module.source == *path {
            return Some("source_file");
        }
        if module.meta.as_ref() == Some(path) || module.replay.as_ref() == Some(path) {
            return Some("untrusted_sidecar");
        }
    }
    if !path.as_str().ends_with(".npcert") {
        return Some("non_npcert_certificate_path");
    }
    None
}

fn build_package_certificates(
    loaded: &LoadedPackageRoot,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<PackageCertificateBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut verified_modules_by_module = BTreeMap::new();
    let mut artifacts = Vec::new();
    let mut local_certificates = Vec::new();

    if let Some(diagnostic) = load_external_imports(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut verified_modules_by_module,
        &mut artifacts,
        None,
    ) {
        return Err(Box::new(diagnostic));
    }

    if let Some(diagnostic) = build_local_modules(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut verified_modules_by_module,
        &mut artifacts,
        &mut local_certificates,
        observations,
    ) {
        return Err(Box::new(diagnostic));
    }

    let regenerated_lock = match build_package_lock_from_artifacts_allowing_local_hash_updates(
        &loaded.validated,
        loaded.manifest_path.clone(),
        loaded.manifest_source.as_bytes(),
        artifacts.iter().map(|artifact| PackageLockArtifact {
            path: artifact.path.clone(),
            bytes: artifact.bytes.as_slice(),
        }),
    ) {
        Ok(lock) => lock,
        Err(error) => {
            return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
        }
    };

    let regenerated_lock_json = match regenerated_lock.canonical_json() {
        Ok(json) => json,
        Err(error) => {
            return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
        }
    };

    Ok(PackageCertificateBuild {
        local_certificates,
        package_lock_json: regenerated_lock_json,
    })
}

fn axiom_policy_for_package(loaded: &LoadedPackageRoot) -> AxiomPolicy {
    let mut policy = AxiomPolicy::normal();
    if !loaded.validated.manifest().policy.allow_custom_axioms {
        policy.allowlisted_axioms = loaded
            .validated
            .manifest()
            .policy
            .allowed_axioms
            .iter()
            .cloned()
            .collect();
    }
    policy
}

fn build_package_certificates_check(
    loaded: &LoadedPackageRoot,
    mut support_warming: Option<&mut FullReadThroughSupportWarming>,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<PackageCertificateCheckBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut verified_modules_by_module = BTreeMap::new();
    let mut lock_entries = Vec::new();
    let mut local_certificates = Vec::new();

    if let Some(diagnostic) = load_external_imports_for_check(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut verified_modules_by_module,
        &mut lock_entries,
    ) {
        return Err(Box::new(diagnostic));
    }
    if let Some(warming) = support_warming.as_deref_mut() {
        warming.prepare(loaded, &policy, &lock_entries, &verified_modules_by_module);
    }

    if let Some(diagnostic) = build_local_modules_for_check(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut verified_modules_by_module,
        &mut lock_entries,
        &mut local_certificates,
        support_warming,
        observations,
    ) {
        return Ok(PackageCertificateCheckBuild {
            local_certificates,
            package_lock_json: String::new(),
            diagnostic: Some(diagnostic),
        });
    }

    let lock = PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: loaded.validated.manifest().package.clone(),
        version: loaded.validated.manifest().version.clone(),
        manifest: PackageLockManifestReference {
            path: loaded.manifest_path.clone(),
            file_hash: package_file_hash(loaded.manifest_source.as_bytes()),
        },
        entries: lock_entries,
    };
    if let Err(error) = validate_package_lock_against_manifest_graph(&loaded.validated, &lock) {
        return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
    }
    let package_lock_json = match lock.canonical_json() {
        Ok(json) => json,
        Err(error) => {
            return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
        }
    };

    Ok(PackageCertificateCheckBuild {
        local_certificates,
        package_lock_json,
        diagnostic: None,
    })
}

fn package_build_import_use_counts(loaded: &LoadedPackageRoot) -> BTreeMap<Name, usize> {
    let mut counts = BTreeMap::new();
    for imports in &loaded.validated.graph().resolved_module_imports {
        for import in imports {
            *counts.entry(import.module.clone()).or_insert(0) += 1;
        }
    }
    counts
}

fn external_import_dependency_plan(
    loaded: &LoadedPackageRoot,
    seeds: &BTreeSet<usize>,
) -> Result<Vec<usize>, Box<CommandDiagnostic>> {
    Ok(external_import_dependency_discovery(loaded, seeds)?.order)
}

fn external_import_dependency_discovery(
    loaded: &LoadedPackageRoot,
    seeds: &BTreeSet<usize>,
) -> Result<ExternalImportDependencyDiscovery, Box<CommandDiagnostic>> {
    if seeds.is_empty() {
        return Ok(ExternalImportDependencyDiscovery {
            order: Vec::new(),
            certificate_bytes_by_index: BTreeMap::new(),
            dependencies_by_index: BTreeMap::new(),
        });
    }
    let limits = TARGETED_EXTERNAL_DEPENDENCY_LIMITS;
    let imports = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[]);
    check_external_import_count_limit(imports.len(), limits.max_imports)?;
    let import_indices = imports
        .iter()
        .enumerate()
        .map(|(index, import)| (import.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let import_modules = imports
        .iter()
        .map(|import| import.module.clone())
        .collect::<Vec<_>>();
    let mut certificate_bytes = 0;
    let mut certificate_bytes_by_index = BTreeMap::new();
    let mut dependencies_by_index = BTreeMap::new();
    let order = external_import_dependency_order(
        &import_modules,
        seeds,
        limits,
        |index, remaining_edges| {
            let import = &imports[index];
            let remaining_bytes = limits.max_certificate_bytes - certificate_bytes;
            let bytes = read_certificate_bytes_for_external_dependency_discovery(
                loaded,
                import,
                index,
                remaining_bytes,
                limits.max_certificate_bytes,
            )?;
            certificate_bytes += bytes.len();
            let decoded = npa_cert::decode_module_cert(&bytes)
                .map_err(|error| Box::new(external_certificate_rejected(import, &error)))?;
            let mut dependencies = BTreeSet::new();
            for dependency in decoded.imports() {
                let Some(dependency) = import_indices.get(&dependency.module).copied() else {
                    continue;
                };
                if dependencies.insert(dependency) && dependencies.len() > remaining_edges {
                    return Err(Box::new(external_import_closure_limit_exceeded(
                        Some(&import.module),
                        Some(index),
                        "dependency_edges",
                        limits.max_dependency_edges,
                        limits.max_dependency_edges.saturating_add(1),
                    )));
                }
            }
            let dependencies = dependencies.into_iter().collect::<Vec<_>>();
            if certificate_bytes_by_index.insert(index, bytes).is_some()
                || dependencies_by_index
                    .insert(index, dependencies.clone())
                    .is_some()
            {
                return Err(targeted_refresh_plan_invalid(
                    "external_dependency_duplicate",
                ));
            }
            Ok(dependencies)
        },
    )?;
    Ok(ExternalImportDependencyDiscovery {
        order,
        certificate_bytes_by_index,
        dependencies_by_index,
    })
}

fn external_import_dependency_order(
    import_modules: &[Name],
    seeds: &BTreeSet<usize>,
    limits: ExternalImportDependencyLimits,
    mut dependencies_for: impl FnMut(usize, usize) -> Result<Vec<usize>, Box<CommandDiagnostic>>,
) -> Result<Vec<usize>, Box<CommandDiagnostic>> {
    if seeds.is_empty() {
        return Ok(Vec::new());
    }
    check_external_import_count_limit(import_modules.len(), limits.max_imports)?;
    let mut states = vec![ExternalImportVisitState::Unvisited; import_modules.len()];
    let mut path = Vec::new();
    let mut frames = Vec::<ExternalImportVisitFrame>::new();
    let mut order = Vec::new();
    let mut dependency_edges = 0;

    for &seed in seeds {
        if seed >= import_modules.len() {
            return Err(Box::new(external_import_index_out_of_range(
                seed,
                import_modules.len(),
            )));
        }
        if states[seed] == ExternalImportVisitState::Visited {
            continue;
        }

        states[seed] = ExternalImportVisitState::Visiting;
        path.push(seed);
        frames.push(external_import_visit_frame(
            import_modules,
            limits,
            &mut dependency_edges,
            &mut dependencies_for,
            seed,
        )?);

        while !frames.is_empty() {
            let dependency = {
                let frame = frames.last_mut().expect("external import frame");
                let dependency = frame.dependencies.get(frame.next_dependency).copied();
                if dependency.is_some() {
                    frame.next_dependency += 1;
                }
                dependency
            };
            let Some(dependency) = dependency else {
                let completed = frames.pop().expect("external import frame").index;
                let popped = path.pop();
                debug_assert_eq!(popped, Some(completed));
                states[completed] = ExternalImportVisitState::Visited;
                order.push(completed);
                continue;
            };
            if dependency >= import_modules.len() {
                return Err(Box::new(external_import_index_out_of_range(
                    dependency,
                    import_modules.len(),
                )));
            }

            match states[dependency] {
                ExternalImportVisitState::Unvisited => {
                    states[dependency] = ExternalImportVisitState::Visiting;
                    path.push(dependency);
                    frames.push(external_import_visit_frame(
                        import_modules,
                        limits,
                        &mut dependency_edges,
                        &mut dependencies_for,
                        dependency,
                    )?);
                }
                ExternalImportVisitState::Visiting => {
                    return Err(Box::new(external_import_cycle_diagnostic(
                        import_modules,
                        &path,
                        dependency,
                    )));
                }
                ExternalImportVisitState::Visited => {}
            }
        }
    }

    Ok(order)
}

fn external_import_visit_frame(
    import_modules: &[Name],
    limits: ExternalImportDependencyLimits,
    dependency_edges: &mut usize,
    dependencies_for: &mut impl FnMut(usize, usize) -> Result<Vec<usize>, Box<CommandDiagnostic>>,
    index: usize,
) -> Result<ExternalImportVisitFrame, Box<CommandDiagnostic>> {
    let remaining_edges = limits.max_dependency_edges - *dependency_edges;
    let dependencies = dependencies_for(index, remaining_edges)?;
    let actual_edges = (*dependency_edges).saturating_add(dependencies.len());
    if actual_edges > limits.max_dependency_edges {
        return Err(Box::new(external_import_closure_limit_exceeded(
            import_modules.get(index),
            Some(index),
            "dependency_edges",
            limits.max_dependency_edges,
            actual_edges,
        )));
    }
    *dependency_edges = actual_edges;
    Ok(ExternalImportVisitFrame {
        index,
        dependencies,
        next_dependency: 0,
    })
}

fn check_external_import_count_limit(
    import_count: usize,
    limit: usize,
) -> Result<(), Box<CommandDiagnostic>> {
    if import_count > limit {
        return Err(Box::new(external_import_closure_limit_exceeded(
            None,
            None,
            "imports",
            limit,
            import_count,
        )));
    }
    Ok(())
}

fn external_import_closure_limit_exceeded(
    module: Option<&Name>,
    index: Option<usize>,
    field: &'static str,
    limit: usize,
    actual: usize,
) -> CommandDiagnostic {
    let path = match (index, field) {
        (Some(index), "certificate_bytes") => format!("imports[{index}].certificate"),
        (Some(index), _) => format!("imports[{index}].certificate.imports"),
        (None, _) => "imports".to_owned(),
    };
    let mut diagnostic = CommandDiagnostic::error(
        DiagnosticKind::Build,
        "external_import_closure_limit_exceeded",
    )
    .with_path(path)
    .with_field(field)
    .with_expected_value(format!("at most {limit}"))
    .with_actual_value(actual.to_string());
    if let Some(module) = module {
        diagnostic = diagnostic.with_module(module.as_dotted());
    }
    diagnostic
}

fn external_import_cycle_diagnostic(
    import_modules: &[Name],
    stack: &[usize],
    repeated: usize,
) -> CommandDiagnostic {
    let owner_index = stack.last().copied().unwrap_or(repeated);
    let start = stack
        .iter()
        .position(|index| *index == repeated)
        .unwrap_or(0);
    let mut cycle = stack[start..]
        .iter()
        .map(|index| import_modules[*index].as_dotted())
        .collect::<Vec<_>>();
    cycle.push(import_modules[repeated].as_dotted());
    let error = PackageLockError::lock_import_cycle(
        format!("imports[{owner_index}].certificate.imports"),
        cycle.join(" -> "),
    )
    .with_module(import_modules[owner_index].as_dotted());
    CommandDiagnostic::from_package_lock_error(&error)
}

fn external_import_index_out_of_range(index: usize, import_count: usize) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::Internal,
        "external_import_index_out_of_range",
    )
    .with_path("imports")
    .with_field("index")
    .with_expected_value(format!("index below {import_count}"))
    .with_actual_value(index.to_string())
}

fn build_targeted_refresh_external_plan(
    loaded: &LoadedPackageRoot,
    roots: &BTreeSet<usize>,
    discovery: &ExternalImportDependencyDiscovery,
) -> Result<TargetedRefreshExternalPlan, Box<CommandDiagnostic>> {
    let import_count = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .len();
    let priority_set = discovery.order.iter().copied().collect::<BTreeSet<_>>();
    if priority_set.len() != discovery.order.len()
        || priority_set.iter().any(|index| *index >= import_count)
    {
        return Err(targeted_refresh_plan_invalid("external_partition_invalid"));
    }
    if !roots.is_subset(&priority_set) {
        return Err(targeted_refresh_plan_invalid("external_root_missing"));
    }
    if discovery
        .certificate_bytes_by_index
        .keys()
        .copied()
        .collect::<BTreeSet<_>>()
        != priority_set
        || discovery
            .dependencies_by_index
            .keys()
            .copied()
            .collect::<BTreeSet<_>>()
            != priority_set
    {
        return Err(targeted_refresh_plan_invalid("external_partition_invalid"));
    }

    let mut positions = BTreeMap::new();
    for (position, &index) in discovery.order.iter().enumerate() {
        positions.insert(index, position);
    }
    for (&consumer, dependencies) in &discovery.dependencies_by_index {
        let Some(&consumer_position) = positions.get(&consumer) else {
            return Err(targeted_refresh_plan_invalid("external_partition_invalid"));
        };
        for dependency in dependencies {
            if positions.get(dependency).copied().unwrap_or(usize::MAX) >= consumer_position {
                return Err(targeted_refresh_plan_invalid(
                    "external_dependency_after_consumer",
                ));
            }
        }
    }

    let completion_external_order = (0..import_count)
        .filter(|index| !priority_set.contains(index))
        .collect::<Vec<_>>();
    if discovery.order.len() + completion_external_order.len() != import_count {
        return Err(targeted_refresh_plan_invalid("external_partition_invalid"));
    }
    Ok(TargetedRefreshExternalPlan {
        priority_external_order: discovery.order.clone(),
        completion_external_order,
    })
}

fn load_external_imports_for_targeted_refresh(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    import_order: &[usize],
    require_discovered_bytes: bool,
    state: &mut TargetedRefreshExecutionState,
) -> Result<(), Box<CommandDiagnostic>> {
    let imports = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[]);
    for &index in import_order {
        let Some(import) = imports.get(index) else {
            return Err(Box::new(external_import_index_out_of_range(
                index,
                imports.len(),
            )));
        };
        if state.loaded_external.contains(&index) {
            return Err(targeted_refresh_plan_invalid("external_loaded_twice"));
        }
        if state.artifacts_by_path.contains_key(&import.certificate)
            || state
                .refreshed_modules_by_index
                .values()
                .any(|identity| identity.certificate_path == import.certificate)
        {
            return Err(duplicate_refresh_artifact_path(&import.certificate));
        }
        let bytes = if require_discovered_bytes {
            state
                .discovered_external_bytes_by_index
                .remove(&index)
                .ok_or_else(|| targeted_refresh_plan_invalid("external_discovery_bytes_missing"))?
        } else {
            read_certificate_bytes(
                loaded,
                &import.certificate,
                format!("imports[{index}].certificate"),
            )?
        };
        observe_certificate_verify_for_test(&import.certificate);
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut state.external_verifier_session, policy)
                .map_err(|error| Box::new(external_certificate_rejected(import, &error)))?;
        if verified.module() != &import.module {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_field("module")
                    .with_expected_value(import.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            ));
        }
        let actual_export_hash = PackageHash::from(verified.export_hash());
        if actual_export_hash != import.export_hash {
            return Err(Box::new(hash_mismatch(
                "export_hash_mismatch",
                format!("imports[{index}].export_hash"),
                "export_hash",
                import.export_hash,
                actual_export_hash,
            )));
        }
        let actual_certificate_hash = PackageHash::from(verified.certificate_hash());
        if actual_certificate_hash != import.certificate_hash {
            return Err(Box::new(hash_mismatch(
                "certificate_hash_mismatch",
                format!("imports[{index}].certificate_hash"),
                "certificate_hash",
                import.certificate_hash,
                actual_certificate_hash,
            )));
        }

        let verified = Arc::new(verified);
        if state
            .verified_modules_by_module
            .insert(import.module.clone(), Arc::clone(&verified))
            .is_some()
        {
            return Err(targeted_refresh_plan_invalid(
                "external_verified_module_duplicate",
            ));
        }
        let remaining_uses = import_use_counts
            .get(&import.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0
            && state
                .available_modules
                .insert(
                    import.module.clone(),
                    RefreshAvailableModule {
                        source_interface: fallback_imported_source_interface(&verified),
                        verified,
                        remaining_uses,
                        origin: RefreshImportOrigin::External,
                    },
                )
                .is_some()
        {
            return Err(targeted_refresh_plan_invalid(
                "external_available_module_duplicate",
            ));
        }
        state.artifacts_by_path.insert(
            import.certificate.clone(),
            CertificateArtifactBuffer {
                path: import.certificate.clone(),
                bytes,
            },
        );
        state.loaded_external.insert(index);
    }
    Ok(())
}

fn external_certificate_rejected(
    import: &PackageExternalImport,
    error: &impl std::fmt::Debug,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::Build, "external_certificate_rejected")
        .with_module(import.module.as_dotted())
        .with_path(render_package_path(&import.certificate))
        .with_actual_value(format!("{error:?}"))
}

fn load_external_imports_for_check(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    lock_entries: &mut Vec<PackageLockEntry>,
) -> Option<CommandDiagnostic> {
    let mut session = VerifierSession::new();
    for (index, import) in loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let bytes = match read_certificate_bytes(
            loaded,
            &import.certificate,
            format!("imports[{index}].certificate"),
        ) {
            Ok(bytes) => bytes,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let verified = match npa_cert::verify_module_cert(&bytes, &mut session, policy) {
            Ok(verified) => verified,
            Err(error) => return Some(external_certificate_rejected(import, &error)),
        };

        if verified.module() != &import.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_field("module")
                    .with_expected_value(import.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }
        let actual_export_hash = PackageHash::from(verified.export_hash());
        if actual_export_hash != import.export_hash {
            return Some(hash_mismatch(
                "export_hash_mismatch",
                format!("imports[{index}].export_hash"),
                "export_hash",
                import.export_hash,
                actual_export_hash,
            ));
        }
        let actual_certificate_hash = PackageHash::from(verified.certificate_hash());
        if actual_certificate_hash != import.certificate_hash {
            return Some(hash_mismatch(
                "certificate_hash_mismatch",
                format!("imports[{index}].certificate_hash"),
                "certificate_hash",
                import.certificate_hash,
                actual_certificate_hash,
            ));
        }

        let decoded = match npa_cert::decode_module_cert(&bytes) {
            Ok(certificate) => certificate,
            Err(error) => {
                return Some(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackageLock,
                        "certificate_decode_failed",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_actual_value(format!("{error:?}")),
                );
            }
        };
        let imports = match package_lock_imports_for_certificate(
            decoded.imports(),
            &format!("imports[{index}].certificate.imports"),
            &import.module,
        ) {
            Ok(imports) => imports,
            Err(diagnostic) => return Some(*diagnostic),
        };
        lock_entries.push(PackageLockEntry {
            module: import.module.clone(),
            origin: PackageLockEntryOrigin::External,
            certificate: import.certificate.clone(),
            certificate_file_hash: package_file_hash(&bytes),
            export_hash: PackageHash::from(decoded.hashes().export_hash),
            axiom_report_hash: PackageHash::from(decoded.hashes().axiom_report_hash),
            certificate_hash: PackageHash::from(decoded.hashes().certificate_hash),
            imports,
            package: Some(import.package.clone()),
            version: Some(import.version.clone()),
        });

        let verified = Arc::new(verified);
        verified_modules_by_module.insert(import.module.clone(), Arc::clone(&verified));

        let remaining_uses = import_use_counts
            .get(&import.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0 {
            available_modules.insert(
                import.module.clone(),
                AvailableModule {
                    source_interface: fallback_imported_source_interface(&verified),
                    verified,
                    remaining_uses,
                },
            );
        }
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn build_local_modules_for_check(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    lock_entries: &mut Vec<PackageLockEntry>,
    local_certificates: &mut Vec<PackageBuildCheckCertificateIdentity>,
    mut support_warming: Option<&mut FullReadThroughSupportWarming>,
    observations: &mut PackageBuildObservationCoordinator,
) -> Option<CommandDiagnostic> {
    let compile_options = observations.compile_options();
    let progress_filter = std::env::var("NPA_PACKAGE_BUILD_CERTS_PROGRESS").ok();
    let check_hashes = std::env::var_os("NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS").is_none();
    for &module_index in &loaded.validated.graph().topological_order {
        let module = &loaded.validated.manifest().modules[module_index];
        let remaining_uses = import_use_counts
            .get(&module.module)
            .copied()
            .unwrap_or_default();
        let progress_started_at = Instant::now();
        let module_progress_name = module.module.as_dotted();
        let progress = match progress_filter.as_deref() {
            Some("1") => true,
            Some(filter) => module_progress_name.contains(filter),
            None => false,
        };
        if progress {
            eprintln!(
                "package build-certs check: start {}/{} {}",
                module_index + 1,
                loaded.validated.manifest().modules.len(),
                module_progress_name
            );
        }
        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let source_hash = package_file_hash(source.as_bytes());
        if check_hashes {
            if let Some(diagnostic) = check_generated_source_hash(module_index, module, source_hash)
            {
                return Some(diagnostic);
            }
        }
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                        .with_module(module.module.as_dotted()),
                );
            }
        };
        let (direct_verified_modules, direct_source_interfaces) =
            match take_direct_import_context(loaded, module_index, available_modules, check_hashes)
            {
                Ok(imports) => imports,
                Err(diagnostic) => return Some(*diagnostic),
            };
        let direct_verified_module_refs = direct_verified_modules
            .iter()
            .map(Arc::as_ref)
            .collect::<Vec<_>>();
        let available_verified_module_refs = available_verified_module_refs_for_direct_imports(
            &direct_verified_modules,
            verified_modules_by_module,
        );

        let built = if is_std_core_builder_profile(module.producer_profile.as_deref()) {
            let (certificate, generated_bytes, verified, source_interface, _) =
                match build_std_core_builder_package_certificate(
                    module_index,
                    module,
                    &source,
                    &direct_verified_module_refs,
                    policy,
                    false,
                ) {
                    Ok(output) => output,
                    Err(diagnostic) => return Some(*diagnostic),
                };
            LocalModuleCheckBuild::Verified {
                certificate,
                generated_bytes,
                verified: Box::new(verified),
                source_interface: Box::new(source_interface),
            }
        } else if remaining_uses == 0 {
            if progress {
                eprintln!(
                    "package build-certs check: compile certificate-only {}",
                    module_progress_name
                );
            }
            let observed =
                    match compile_human_source_to_observed_built_certificate_only_with_available_import_refs(
                        file_id,
                        module.module.clone(),
                        &source,
                        &direct_verified_module_refs,
                        &available_verified_module_refs,
                        &direct_source_interfaces,
                        &compile_options,
                        observations.kernel_work_counter_sink(),
                        observations.collect_declaration_details(),
                    ) {
                        Ok(output) => output,
                        Err(error) => {
                            return Some(frontend_build_failed(
                                module_index,
                                module,
                                file_id,
                                &source,
                                &direct_source_interfaces,
                                error,
                            ));
                        }
                    };
            observations.record_declaration_batch(&module.module, observed.observations);
            let output = observed.output;
            if progress {
                eprintln!(
                    "package build-certs check: encode certificate-only {} after {:.3}s",
                    module_progress_name,
                    progress_started_at.elapsed().as_secs_f64()
                );
            }
            let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return Some(
                        CommandDiagnostic::error(
                            DiagnosticKind::Build,
                            "certificate_encode_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_actual_value(format!("{error:?}")),
                    );
                }
            };
            LocalModuleCheckBuild::Unverified {
                certificate: output.certificate,
                generated_bytes,
                source_interface: None,
            }
        } else {
            if progress {
                eprintln!(
                    "package build-certs check: compile with interface {}",
                    module_progress_name
                );
            }
            let observed =
                match compile_human_source_to_observed_built_certificate_output_with_available_import_refs(
                    file_id,
                    module.module.clone(),
                    &source,
                    &direct_verified_module_refs,
                    &available_verified_module_refs,
                    &direct_source_interfaces,
                    &compile_options,
                    observations.kernel_work_counter_sink(),
                    observations.collect_declaration_details(),
                ) {
                    Ok(output) => output,
                    Err(error) => {
                        return Some(frontend_build_failed(
                            module_index,
                            module,
                            file_id,
                            &source,
                            &direct_source_interfaces,
                            error,
                        ));
                    }
                };
            observations.record_declaration_batch(&module.module, observed.observations);
            let output = observed.output;
            if progress {
                eprintln!(
                    "package build-certs check: encode with interface {} after {:.3}s",
                    module_progress_name,
                    progress_started_at.elapsed().as_secs_f64()
                );
            }
            let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return Some(
                        CommandDiagnostic::error(
                            DiagnosticKind::Build,
                            "certificate_encode_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_actual_value(format!("{error:?}")),
                    );
                }
            };
            LocalModuleCheckBuild::Unverified {
                certificate: output.certificate,
                generated_bytes,
                source_interface: Some(Box::new(output.source_interface)),
            }
        };
        let certificate = built.certificate();
        let generated_bytes = built.generated_bytes();
        let output_certificate_format = certificate.header().format.clone();
        let output_core_spec = certificate.header().core_spec.clone();

        if let Some(diagnostic) =
            check_generated_axiom_policy(loaded, module_index, module, certificate)
        {
            return Some(diagnostic);
        }

        let source_imports = human_source_imports(file_id, &source, &direct_source_interfaces);
        if let Some(source_imports) = source_imports.as_deref() {
            if let Some(diagnostic) = check_observable_import_drift(
                module_index,
                module,
                source_imports,
                certificate,
                &direct_source_interfaces,
            ) {
                return Some(diagnostic);
            }
        }
        if check_hashes {
            if let Some(diagnostic) =
                check_generated_manifest_hashes(module_index, module, certificate, generated_bytes)
            {
                return Some(diagnostic);
            }
        }

        if let Some(diagnostic) =
            check_local_certificate_file(loaded, module_index, module, generated_bytes)
        {
            let source_imports = source_imports
                .or_else(|| human_source_imports(file_id, &source, &direct_source_interfaces));
            let diagnostic = source_imports
                .as_deref()
                .and_then(|source_imports| {
                    check_existing_certificate_import_drift(
                        loaded,
                        module_index,
                        module,
                        source_imports,
                    )
                })
                .unwrap_or(diagnostic);
            local_certificates.push(PackageBuildCheckCertificateIdentity {
                module_index,
                source_hash,
                output_certificate_format: certificate.header().format.clone(),
                output_core_spec: certificate.header().core_spec.clone(),
            });
            return Some(diagnostic);
        }
        let warming_artifact = (support_warming.is_some() && remaining_uses > 0).then(|| {
            targeted_authoring_local_input_from_accepted_certificate(
                module,
                source_hash,
                certificate,
                generated_bytes,
            )
        });

        let imports = match package_lock_imports_for_certificate(
            certificate.imports(),
            &format!("modules[{module_index}].certificate.imports"),
            &module.module,
        ) {
            Ok(imports) => imports,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let lock_entry = PackageLockEntry {
            module: module.module.clone(),
            origin: PackageLockEntryOrigin::Local,
            certificate: module.certificate.clone(),
            certificate_file_hash: package_file_hash(generated_bytes),
            export_hash: PackageHash::from(certificate.hashes().export_hash),
            axiom_report_hash: PackageHash::from(certificate.hashes().axiom_report_hash),
            certificate_hash: PackageHash::from(certificate.hashes().certificate_hash),
            imports,
            package: None,
            version: None,
        };
        if certificate.header().module != module.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_field("module")
                    .with_expected_value(module.module.as_dotted())
                    .with_actual_value(certificate.header().module.as_dotted()),
            );
        }
        let (export_hash, certificate_hash, verified, source_interface) = match built {
            LocalModuleCheckBuild::Verified {
                certificate,
                generated_bytes,
                verified,
                source_interface,
            } => {
                let export_hash = certificate.hashes().export_hash;
                let certificate_hash = certificate.hashes().certificate_hash;
                drop(generated_bytes);
                (
                    export_hash,
                    certificate_hash,
                    Some(*verified),
                    Some(*source_interface),
                )
            }
            LocalModuleCheckBuild::Unverified {
                certificate,
                generated_bytes,
                source_interface,
            } => {
                let export_hash = certificate.hashes().export_hash;
                let certificate_hash = certificate.hashes().certificate_hash;
                if remaining_uses > 0 {
                    let Some(source_interface) = source_interface else {
                        return Some(
                            CommandDiagnostic::error(
                                DiagnosticKind::Internal,
                                "source_interface_missing",
                            )
                            .with_module(module.module.as_dotted()),
                        );
                    };
                    if progress {
                        eprintln!(
                            "package build-certs check: verify {} remaining_uses={}",
                            module.module.as_dotted(),
                            remaining_uses
                        );
                    }
                    drop(certificate);
                    let verified = match npa_cert::verify_module_cert_with_import_refs(
                        &generated_bytes,
                        &available_verified_module_refs,
                        policy,
                    ) {
                        Ok(verified) => verified,
                        Err(error) => {
                            return Some(
                                CommandDiagnostic::error(
                                    DiagnosticKind::Build,
                                    "certificate_rejected",
                                )
                                .with_module(module.module.as_dotted())
                                .with_path(format!("modules[{module_index}].certificate"))
                                .with_actual_value(format!("{error:?}")),
                            );
                        }
                    };
                    drop(generated_bytes);
                    (
                        export_hash,
                        certificate_hash,
                        Some(verified),
                        Some(*source_interface),
                    )
                } else {
                    drop(certificate);
                    drop(generated_bytes);
                    (export_hash, certificate_hash, None, None)
                }
            }
        };
        if progress {
            eprintln!(
                "package build-certs check: finish {} in {:.3}s",
                module.module.as_dotted(),
                progress_started_at.elapsed().as_secs_f64()
            );
        }

        drop(direct_verified_module_refs);
        drop(direct_verified_modules);
        drop(direct_source_interfaces);
        trim_package_build_heap();

        if let Some(verified) = verified.as_ref() {
            if verified.module() != &module.module {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_field("module")
                        .with_expected_value(module.module.as_dotted())
                        .with_actual_value(verified.module().as_dotted()),
                );
            }
        }

        lock_entries.push(lock_entry);

        if remaining_uses > 0 {
            let Some(verified) = verified else {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "verified_module_missing")
                        .with_module(module.module.as_dotted()),
                );
            };
            let verified = Arc::new(verified);
            verified_modules_by_module.insert(module.module.clone(), Arc::clone(&verified));
            let Some(source_interface) = source_interface else {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "source_interface_missing")
                        .with_module(module.module.as_dotted()),
                );
            };
            let imported_source_interface = HumanImportedSourceInterface {
                module: module.module.clone(),
                export_hash,
                certificate_hash: Some(certificate_hash),
                source_interface,
            };
            if let (Some(warming), Some(artifact)) =
                (support_warming.as_deref_mut(), warming_artifact)
            {
                warming.publish_retained_module(
                    loaded,
                    module_index,
                    artifact,
                    &source,
                    &imported_source_interface,
                    &verified,
                );
            }
            available_modules.insert(
                module.module.clone(),
                AvailableModule {
                    verified,
                    source_interface: imported_source_interface,
                    remaining_uses,
                },
            );
        }
        local_certificates.push(PackageBuildCheckCertificateIdentity {
            module_index,
            source_hash,
            output_certificate_format,
            output_core_spec,
        });
        drop(source);
    }
    None
}

fn targeted_authoring_external_inputs(
    loaded: &LoadedPackageRoot,
    external_order: &[usize],
    artifacts: &[CertificateArtifactBuffer],
    verified_modules_by_module: &BTreeMap<Name, Arc<VerifiedModule>>,
) -> Result<Vec<TargetedAuthoringExternalModuleInput>, Box<CommandDiagnostic>> {
    if external_order.len() != artifacts.len() {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Internal, "targeted_authoring_plan_invalid")
                .with_field("external_artifacts")
                .with_actual_value("external_artifact_count_mismatch"),
        ));
    }
    let imports = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[]);
    external_order
        .iter()
        .copied()
        .zip(artifacts)
        .map(|(index, artifact)| {
            let import = imports.get(index).ok_or_else(|| {
                Box::new(external_import_index_out_of_range(index, imports.len()))
            })?;
            if artifact.path != import.certificate {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "targeted_authoring_plan_invalid",
                    )
                    .with_module(import.module.as_dotted())
                    .with_field("external_artifacts")
                    .with_actual_value("external_artifact_order_mismatch"),
                ));
            }
            let verified = verified_modules_by_module
                .get(&import.module)
                .ok_or_else(|| {
                    Box::new(
                        CommandDiagnostic::error(
                            DiagnosticKind::Internal,
                            "targeted_authoring_plan_invalid",
                        )
                        .with_module(import.module.as_dotted())
                        .with_field("external_artifacts")
                        .with_actual_value("external_verified_module_missing"),
                    )
                })?;
            Ok(TargetedAuthoringExternalModuleInput {
                module: import.module.clone(),
                current_certificate_file_hash: package_file_hash(&artifact.bytes),
                actual_export_hash: PackageHash::from(verified.export_hash()),
                actual_certificate_hash: PackageHash::from(verified.certificate_hash()),
            })
        })
        .collect()
}

fn load_external_imports(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    selected_imports: Option<&[usize]>,
) -> Option<CommandDiagnostic> {
    let mut session = VerifierSession::new();
    let imports = loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[]);
    let all_import_indices;
    let import_indices = match selected_imports {
        Some(indices) => indices,
        None => {
            all_import_indices = (0..imports.len()).collect::<Vec<_>>();
            &all_import_indices
        }
    };
    for &index in import_indices {
        let Some(import) = imports.get(index) else {
            return Some(external_import_index_out_of_range(index, imports.len()));
        };
        let bytes = match read_certificate_bytes(
            loaded,
            &import.certificate,
            format!("imports[{index}].certificate"),
        ) {
            Ok(bytes) => bytes,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let verified = match npa_cert::verify_module_cert(&bytes, &mut session, policy) {
            Ok(verified) => verified,
            Err(error) => return Some(external_certificate_rejected(import, &error)),
        };

        if verified.module() != &import.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_field("module")
                    .with_expected_value(import.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }
        let actual_export_hash = PackageHash::from(verified.export_hash());
        if actual_export_hash != import.export_hash {
            return Some(hash_mismatch(
                "export_hash_mismatch",
                format!("imports[{index}].export_hash"),
                "export_hash",
                import.export_hash,
                actual_export_hash,
            ));
        }
        let actual_certificate_hash = PackageHash::from(verified.certificate_hash());
        if actual_certificate_hash != import.certificate_hash {
            return Some(hash_mismatch(
                "certificate_hash_mismatch",
                format!("imports[{index}].certificate_hash"),
                "certificate_hash",
                import.certificate_hash,
                actual_certificate_hash,
            ));
        }

        let verified = Arc::new(verified);
        verified_modules_by_module.insert(import.module.clone(), Arc::clone(&verified));

        let remaining_uses = import_use_counts
            .get(&import.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0 {
            available_modules.insert(
                import.module.clone(),
                AvailableModule {
                    source_interface: fallback_imported_source_interface(&verified),
                    verified,
                    remaining_uses,
                },
            );
        }
        artifacts.push(CertificateArtifactBuffer {
            path: import.certificate.clone(),
            bytes,
        });
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn load_checked_local_module_for_refresh(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    module_index: usize,
    require_current_source: bool,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    compile_options: &HumanCompileOptions,
) -> Option<CommandDiagnostic> {
    let mut source_interface_elapsed_ns = 0;
    load_checked_local_module_for_refresh_with_snapshot(
        loaded,
        policy,
        import_use_counts,
        module_index,
        require_current_source,
        available_modules,
        verified_modules_by_module,
        artifacts,
        compile_options,
        None,
        false,
        &mut source_interface_elapsed_ns,
    )
}

#[allow(clippy::too_many_arguments)]
fn load_checked_local_module_for_refresh_observed(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    module_index: usize,
    require_current_source: bool,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    compile_options: &HumanCompileOptions,
) -> (Option<CommandDiagnostic>, u64) {
    let mut source_interface_elapsed_ns = 0;
    let diagnostic = load_checked_local_module_for_refresh_with_snapshot(
        loaded,
        policy,
        import_use_counts,
        module_index,
        require_current_source,
        available_modules,
        verified_modules_by_module,
        artifacts,
        compile_options,
        None,
        true,
        &mut source_interface_elapsed_ns,
    );
    (diagnostic, source_interface_elapsed_ns)
}

#[allow(clippy::too_many_arguments)]
fn load_checked_local_module_for_refresh_from_snapshot(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    compile_options: &HumanCompileOptions,
    snapshot: TargetedAuthoringCurrentSnapshot,
) -> Option<CommandDiagnostic> {
    let mut source_interface_elapsed_ns = 0;
    load_checked_local_module_for_refresh_with_snapshot(
        loaded,
        policy,
        import_use_counts,
        module_index,
        true,
        available_modules,
        verified_modules_by_module,
        artifacts,
        compile_options,
        Some(snapshot),
        false,
        &mut source_interface_elapsed_ns,
    )
}

#[allow(clippy::too_many_arguments)]
fn load_checked_local_module_for_refresh_from_snapshot_observed(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    compile_options: &HumanCompileOptions,
    snapshot: TargetedAuthoringCurrentSnapshot,
) -> (Option<CommandDiagnostic>, u64) {
    let mut source_interface_elapsed_ns = 0;
    let diagnostic = load_checked_local_module_for_refresh_with_snapshot(
        loaded,
        policy,
        import_use_counts,
        module_index,
        true,
        available_modules,
        verified_modules_by_module,
        artifacts,
        compile_options,
        Some(snapshot),
        true,
        &mut source_interface_elapsed_ns,
    );
    (diagnostic, source_interface_elapsed_ns)
}

#[allow(clippy::too_many_arguments)]
fn load_checked_local_module_for_refresh_with_snapshot(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    module_index: usize,
    require_current_source: bool,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    compile_options: &HumanCompileOptions,
    snapshot: Option<TargetedAuthoringCurrentSnapshot>,
    observe_source_interface: bool,
    source_interface_elapsed_ns: &mut u64,
) -> Option<CommandDiagnostic> {
    let module = &loaded.validated.manifest().modules[module_index];
    let (snapshot_source, snapshot_certificate_bytes) = snapshot
        .map(TargetedAuthoringCurrentSnapshot::into_parts)
        .map_or((None, None), |(source, bytes)| (Some(source), Some(bytes)));
    let support_source = if require_current_source {
        let source = match snapshot_source {
            Some(source) => source,
            None => match read_source(loaded, module_index, module) {
                Ok(source) => source,
                Err(diagnostic) => return Some(*diagnostic),
            },
        };
        let actual = package_file_hash(source.as_bytes());
        if actual != module.expected_source_hash {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "selection_dependency_source_stale",
                )
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&module.source))
                .with_field(format!("modules[{module_index}].expected_source_hash"))
                .with_hashes(
                    format_package_hash(&module.expected_source_hash),
                    format_package_hash(&actual),
                ),
            );
        }
        Some(source)
    } else {
        None
    };

    let bytes = match snapshot_certificate_bytes {
        Some(bytes) => bytes,
        None => match read_certificate_bytes(
            loaded,
            &module.certificate,
            format!("modules[{module_index}].certificate"),
        ) {
            Ok(bytes) => bytes,
            Err(diagnostic) => return Some(*diagnostic),
        },
    };
    let certificate = match npa_cert::decode_module_cert(&bytes) {
        Ok(certificate) => certificate,
        Err(error) => {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_decode_failed")
                    .with_module(module.module.as_dotted())
                    .with_path(render_package_path(&module.certificate))
                    .with_actual_value(format!("{error:?}")),
            );
        }
    };
    if let Some(diagnostic) =
        check_generated_axiom_policy(loaded, module_index, module, &certificate)
    {
        return Some(diagnostic);
    }
    let available_refs = verified_modules_by_module
        .values()
        .map(Arc::as_ref)
        .collect::<Vec<_>>();
    let verified =
        match npa_cert::verify_module_cert_with_import_refs(&bytes, &available_refs, policy) {
            Ok(verified) => verified,
            Err(error) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Build, "certificate_rejected")
                        .with_module(module.module.as_dotted())
                        .with_path(render_package_path(&module.certificate))
                        .with_actual_value(format!("{error:?}")),
                );
            }
        };
    if verified.module() != &module.module {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_expected_value(module.module.as_dotted())
                .with_actual_value(verified.module().as_dotted()),
        );
    }
    let source_interface_started = observe_source_interface.then(Instant::now);
    let source_interface = checked_local_source_interface_for_refresh(
        loaded,
        module_index,
        module,
        support_source.as_deref(),
        available_modules,
        &certificate,
        &verified,
        compile_options,
    );
    if let Some(started) = source_interface_started {
        *source_interface_elapsed_ns = source_interface_elapsed_ns
            .saturating_add(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
    }
    let source_interface = match source_interface {
        Ok(source_interface) => source_interface,
        Err(diagnostic) => return Some(*diagnostic),
    };
    if let Some(diagnostic) =
        check_generated_manifest_hashes(module_index, module, &certificate, &bytes)
    {
        return Some(diagnostic);
    }
    let verified = Arc::new(verified);
    verified_modules_by_module.insert(module.module.clone(), Arc::clone(&verified));
    if import_use_counts
        .get(&module.module)
        .copied()
        .unwrap_or_default()
        > 0
    {
        available_modules.insert(
            module.module.clone(),
            RefreshAvailableModule {
                source_interface,
                verified,
                remaining_uses: import_use_counts
                    .get(&module.module)
                    .copied()
                    .unwrap_or_default(),
                origin: RefreshImportOrigin::Local,
            },
        );
    }
    artifacts.push(CertificateArtifactBuffer {
        path: module.certificate.clone(),
        bytes,
    });
    None
}

#[allow(clippy::too_many_arguments)]
fn checked_local_source_interface_for_refresh(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    support_source: Option<&str>,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    certificate: &ModuleCert,
    verified: &VerifiedModule,
    compile_options: &HumanCompileOptions,
) -> Result<HumanImportedSourceInterface, Box<CommandDiagnostic>> {
    match support_source {
        Some(source) if is_std_core_builder_profile(module.producer_profile.as_deref()) => {
            checked_local_std_core_builder_support_source_interface(
                loaded,
                module_index,
                module,
                source,
                available_modules,
                certificate,
                verified,
            )
        }
        Some(source) => checked_local_support_source_interface(
            loaded,
            module_index,
            module,
            source,
            available_modules,
            certificate,
            verified,
            compile_options,
        ),
        None => Ok(fallback_imported_source_interface(verified)),
    }
}

#[allow(clippy::too_many_arguments)]
fn checked_local_support_source_interface(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    source: &str,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    certificate: &ModuleCert,
    verified: &VerifiedModule,
    compile_options: &HumanCompileOptions,
) -> Result<HumanImportedSourceInterface, Box<CommandDiagnostic>> {
    let file_id = checked_current_module_file_id(module_index).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Internal, error.reason_code())
                .with_module(module.module.as_dotted()),
        )
    })?;
    let (direct_verified_modules, direct_source_interfaces) =
        take_refresh_direct_import_context(loaded, module_index, available_modules)?;
    let verified_imports = direct_verified_modules
        .iter()
        .map(|verified| VerifiedImport::from(verified.as_ref()))
        .collect::<Vec<_>>();
    let parsed =
        parse_human_module_with_source_interfaces(file_id, source, &direct_source_interfaces)
            .map_err(|error| {
                Box::new(frontend_build_failed(
                    module_index,
                    module,
                    file_id,
                    source,
                    &direct_source_interfaces,
                    error,
                ))
            })?;
    let source_imports = parsed
        .items
        .iter()
        .filter_map(|item| match item {
            HumanItem::Import { module, .. } => Some(Name::from_dotted(module.as_dotted())),
            _ => None,
        })
        .collect::<Vec<_>>();
    let resolved = resolve_human_module_with_source_interfaces(
        module.module.clone(),
        parsed,
        &verified_imports,
        &direct_source_interfaces,
        compile_options,
    )
    .map_err(|error| {
        Box::new(frontend_build_failed(
            module_index,
            module,
            file_id,
            source,
            &direct_source_interfaces,
            error,
        ))
    })?;
    if let Some(diagnostic) = check_observable_import_drift(
        module_index,
        module,
        &source_imports,
        certificate,
        &direct_source_interfaces,
    ) {
        return Err(Box::new(diagnostic));
    }
    Ok(HumanImportedSourceInterface {
        module: module.module.clone(),
        export_hash: verified.export_hash(),
        certificate_hash: Some(verified.certificate_hash()),
        source_interface: source_interface_with_certificate_hashes(
            resolved.state.source_interfaces.current,
            certificate,
        ),
    })
}

fn checked_local_std_core_builder_support_source_interface(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    source: &str,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    certificate: &ModuleCert,
    verified: &VerifiedModule,
) -> Result<HumanImportedSourceInterface, Box<CommandDiagnostic>> {
    let source_imports = std_core_builder_source_skeleton_imports(module_index, module, source)?;
    let (_direct_verified_modules, direct_source_interfaces) =
        take_refresh_direct_import_context(loaded, module_index, available_modules)?;
    if let Some(diagnostic) = check_observable_import_drift(
        module_index,
        module,
        &source_imports,
        certificate,
        &direct_source_interfaces,
    ) {
        return Err(Box::new(diagnostic));
    }
    Ok(fallback_imported_source_interface(verified))
}

type RefreshModuleBuildOutput = (
    ModuleCert,
    Vec<u8>,
    VerifiedModule,
    HumanSourceInterface,
    Option<Vec<Name>>,
    u64,
);

#[allow(clippy::too_many_arguments)]
fn build_refresh_module_from_source(
    module_index: usize,
    module: &PackageModule,
    source: &str,
    file_id: FileId,
    direct_verified_module_refs: &[&VerifiedModule],
    available_verified_module_refs: &[&VerifiedModule],
    direct_source_interfaces: &[HumanImportedSourceInterface],
    policy: &AxiomPolicy,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<RefreshModuleBuildOutput, Box<CommandDiagnostic>> {
    let (certificate, generated_bytes, verified, source_interface, verification_elapsed_ns) =
        if is_std_core_builder_profile(module.producer_profile.as_deref()) {
            build_std_core_builder_package_certificate(
                module_index,
                module,
                source,
                direct_verified_module_refs,
                policy,
                observations.measurement_enabled(),
            )?
        } else {
            let compile_options = observations.compile_options();
            let observed =
            compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy(
                file_id,
                module.module.clone(),
                source,
                direct_verified_module_refs,
                available_verified_module_refs,
                direct_source_interfaces,
                &compile_options,
                policy,
                observations.kernel_work_counter_sink(),
                observations.collect_declaration_details(),
            )
            .map_err(|error| {
                Box::new(frontend_build_failed(
                    module_index,
                    module,
                    file_id,
                    source,
                    direct_source_interfaces,
                    error,
                ))
            })?;
            let verification_elapsed_ns = observed.observations.source_free_verification_elapsed_ns;
            let output = observed.output;
            observations.record_declaration_batch(&module.module, observed.observations);
            let generated_bytes =
                npa_cert::encode_module_cert(&output.certificate).map_err(|error| {
                    Box::new(
                        CommandDiagnostic::error(
                            DiagnosticKind::Build,
                            "certificate_encode_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_actual_value(format!("{error:?}")),
                    )
                })?;
            (
                output.certificate,
                generated_bytes,
                output.verified_module,
                output.source_interface,
                verification_elapsed_ns,
            )
        };
    let source_imports = human_source_imports(file_id, source, direct_source_interfaces);
    Ok((
        certificate,
        generated_bytes,
        verified,
        source_interface,
        source_imports,
        verification_elapsed_ns,
    ))
}

fn transitive_module_dependency_names(
    roots: impl IntoIterator<Item = Name>,
    mut imports_for: impl FnMut(&Name) -> Option<Vec<Name>>,
) -> BTreeSet<Name> {
    let mut required = BTreeSet::new();
    let mut pending = roots.into_iter().collect::<Vec<_>>();
    while let Some(module) = pending.pop() {
        if !required.insert(module.clone()) {
            continue;
        }
        if let Some(imports) = imports_for(&module) {
            pending.extend(imports);
        }
    }
    required
}

/// Keep the Human kernel environment scoped to the selected module's verified
/// import closure. Unrelated package modules may legitimately export the same
/// unqualified declaration name; exposing every previously built module would
/// make those unrelated exports participate in transitive dependency lookup.
fn available_verified_module_refs_for_direct_imports<'a>(
    direct: &'a [Arc<VerifiedModule>],
    available: &'a BTreeMap<Name, Arc<VerifiedModule>>,
) -> Vec<&'a VerifiedModule> {
    let direct_by_module = direct
        .iter()
        .map(|module| (module.module().clone(), module.as_ref()))
        .collect::<BTreeMap<_, _>>();
    let roots = direct_by_module.keys().cloned().collect::<Vec<_>>();
    let required = transitive_module_dependency_names(roots, |module| {
        direct_by_module
            .get(module)
            .copied()
            .or_else(|| available.get(module).map(Arc::as_ref))
            .map(|verified| {
                verified
                    .imports()
                    .iter()
                    .map(|import| import.module.clone())
                    .collect()
            })
    });

    required
        .iter()
        .filter_map(|module| {
            direct_by_module
                .get(module)
                .copied()
                .or_else(|| available.get(module).map(Arc::as_ref))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn qualify_dependent_refresh(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    module_index: usize,
    module: &PackageModule,
    source: &str,
    source_hash: PackageHash,
    file_id: FileId,
    direct_verified_modules: &[Arc<VerifiedModule>],
    direct_source_interfaces: &[HumanImportedSourceInterface],
    verified_modules_by_module: &BTreeMap<Name, Arc<VerifiedModule>>,
    local_module_names: &BTreeSet<Name>,
    stats: &mut TargetedRefreshStats,
    compile_options: &HumanCompileOptions,
) -> Result<QualifiedDependentRefresh, Box<CommandDiagnostic>> {
    if source_hash != module.expected_source_hash {
        return Ok(QualifiedDependentRefresh::Fallback("source_hash"));
    }
    let previous_bytes = match read_certificate_bytes(
        loaded,
        &module.certificate,
        format!("modules[{module_index}].certificate"),
    ) {
        Ok(bytes) => bytes,
        Err(_) => {
            return Ok(QualifiedDependentRefresh::Fallback(
                "certificate_unavailable",
            ))
        }
    };
    if package_file_hash(&previous_bytes) != module.expected_certificate_file_hash {
        return Ok(QualifiedDependentRefresh::Fallback("certificate_file_hash"));
    }
    let previous = match npa_cert::verify_module_cert_hashes(&previous_bytes) {
        Ok(certificate) => certificate,
        Err(_) => return Ok(QualifiedDependentRefresh::Fallback("certificate_structure")),
    };
    if previous.header().module != module.module
        || PackageHash::from(previous.hashes().export_hash) != module.expected_export_hash
        || PackageHash::from(previous.hashes().axiom_report_hash)
            != module.expected_axiom_report_hash
        || PackageHash::from(previous.hashes().certificate_hash) != module.expected_certificate_hash
    {
        return Ok(QualifiedDependentRefresh::Fallback("certificate_identity"));
    }
    if check_generated_axiom_policy(loaded, module_index, module, &previous).is_some() {
        return Ok(QualifiedDependentRefresh::Fallback("axiom_policy"));
    }
    let Some((source_imports, source_interface)) = reconstruct_qualified_source_interface(
        module,
        source,
        file_id,
        direct_verified_modules,
        direct_source_interfaces,
        &previous,
        compile_options,
    ) else {
        return Ok(QualifiedDependentRefresh::Fallback("source_interface"));
    };
    stats.source_interface_reconstructions += 1;

    let mut mapped_imports = Vec::with_capacity(previous.imports().len());
    for import in previous.imports() {
        let Some(verified) = verified_modules_by_module.get(&import.module) else {
            return Ok(QualifiedDependentRefresh::Fallback("certificate_imports"));
        };
        mapped_imports.push(ModuleCertRebindImport {
            verified: verified.as_ref(),
            origin: if local_module_names.contains(&import.module) {
                ModuleCertRebindImportOrigin::Local
            } else {
                ModuleCertRebindImportOrigin::External
            },
        });
    }
    let expected = ModuleCertRebindExpectedIdentity {
        module: module.module.clone(),
        export_hash: module.expected_export_hash.into_bytes(),
        axiom_report_hash: module.expected_axiom_report_hash.into_bytes(),
        certificate_hash: module.expected_certificate_hash.into_bytes(),
    };
    let outcome = match npa_cert::rebind_module_cert_import_certificate_hashes(
        &previous_bytes,
        &expected,
        &mapped_imports,
        policy,
    ) {
        Ok(outcome) => outcome,
        Err(
            ModuleCertImportRebindError::DuplicateCertificateImport { .. }
            | ModuleCertImportRebindError::MissingMappedImport { .. }
            | ModuleCertImportRebindError::MissingStrictCertificateHash { .. }
            | ModuleCertImportRebindError::ModuleMismatch { .. }
            | ModuleCertImportRebindError::IdentityHashMismatch { .. },
        ) => return Ok(QualifiedDependentRefresh::Fallback("certificate_imports")),
        Err(error) => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_rebind_failed")
                    .with_module(module.module.as_dotted())
                    .with_path(render_package_path(&module.certificate))
                    .with_actual_value(format!("{error:?}")),
            ));
        }
    };
    match outcome {
        ModuleCertImportRebindOutcome::IneligibleFormat { .. } => {
            Ok(QualifiedDependentRefresh::Fallback("certificate_format"))
        }
        ModuleCertImportRebindOutcome::ExportChanged { .. } => {
            Ok(QualifiedDependentRefresh::Fallback("import_export_changed"))
        }
        ModuleCertImportRebindOutcome::Unchanged {
            certificate,
            verified,
        } => Ok(QualifiedDependentRefresh::Unchanged {
            certificate,
            bytes: previous_bytes,
            verified,
            source_interface,
            source_imports,
        }),
        ModuleCertImportRebindOutcome::Rebound {
            certificate,
            bytes,
            verified,
            ..
        } => Ok(QualifiedDependentRefresh::Rebound {
            certificate,
            bytes,
            verified,
            source_interface,
            source_imports,
        }),
    }
}

fn reconstruct_qualified_source_interface(
    module: &PackageModule,
    source: &str,
    file_id: FileId,
    direct_verified_modules: &[Arc<VerifiedModule>],
    direct_source_interfaces: &[HumanImportedSourceInterface],
    certificate: &ModuleCert,
    compile_options: &HumanCompileOptions,
) -> Option<(Vec<Name>, HumanSourceInterface)> {
    let parsed =
        parse_human_module_with_source_interfaces(file_id, source, direct_source_interfaces)
            .ok()?;
    let source_imports = parsed
        .items
        .iter()
        .filter_map(|item| match item {
            HumanItem::Import { module, .. } => Some(Name::from_dotted(module.as_dotted())),
            _ => None,
        })
        .collect::<Vec<_>>();
    if module.imports.iter().cloned().collect::<BTreeSet<_>>()
        != source_imports.iter().cloned().collect::<BTreeSet<_>>()
    {
        return None;
    }
    let certificate_imports = certificate
        .imports()
        .iter()
        .map(|import| (&import.module, import))
        .collect::<BTreeMap<_, _>>();
    if module.imports.iter().any(|module| {
        certificate_imports
            .get(module)
            .is_none_or(|import| import.certificate_hash.is_none())
    }) {
        return None;
    }
    let verified_imports = direct_verified_modules
        .iter()
        .map(|verified| VerifiedImport::from(verified.as_ref()))
        .collect::<Vec<_>>();
    let resolved = resolve_human_module_with_source_interfaces(
        module.module.clone(),
        parsed,
        &verified_imports,
        direct_source_interfaces,
        compile_options,
    )
    .ok()?;
    Some((source_imports, resolved.state.source_interfaces.current))
}

type TargetedAuthoringContextMap<'session> =
    BTreeMap<Name, TargetedAuthoringImportContext<'session>>;

#[allow(clippy::too_many_arguments)]
fn build_local_modules_for_targeted_authoring_check(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    local_modules: &mut Vec<LocalModuleRefreshIdentity>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    execution_plan: &TargetedAuthoringExecutionPlan,
    run: &mut TargetedAuthoringCheckRun,
    observations: &mut PackageBuildObservationCoordinator,
) -> Option<CommandDiagnostic> {
    let compile_options = observations.compile_options();
    let authoring_session = TargetedAuthoringBuildSession::new();
    let mut authoring_contexts = TargetedAuthoringContextMap::new();
    let mut authoring_source_interfaces = BTreeMap::new();

    for (module, available) in available_modules.iter() {
        authoring_contexts.insert(
            module.clone(),
            authoring_session.register_shared_live_support(Arc::clone(&available.verified)),
        );
        authoring_source_interfaces.insert(module.clone(), available.source_interface.clone());
    }

    let mut pending_contexts_adopted = false;
    for &module_index in execution_plan.combined_local_order() {
        let module = &loaded.validated.manifest().modules[module_index];
        if !execution_plan.is_explicit_target(module_index) {
            run.record_live_support_visit(module_index);
            if run.should_capture_pre_target_snapshot(module_index) {
                let snapshot = run.time_current_byte_validation_for(module_index, || {
                    read_targeted_authoring_local_snapshot(loaded, module_index, module)
                });
                let (artifact, snapshot) = match snapshot {
                    Ok(snapshot) => snapshot,
                    Err(diagnostic) => return Some(*diagnostic),
                };
                if let Err(diagnostic) = run.lookup_pre_target_support(
                    loaded,
                    module_index,
                    artifact,
                    snapshot,
                    verified_modules_by_module,
                    policy,
                ) {
                    return Some(diagnostic);
                }
                let promoted = match run.resolve_reached_pre_target_support(module_index) {
                    Ok(promoted) => promoted,
                    Err(diagnostic) => return Some(diagnostic),
                };
                for promoted_index in promoted {
                    let snapshot = match run.take_retained_snapshot(promoted_index) {
                        Ok(snapshot) => snapshot,
                        Err(diagnostic) => return Some(diagnostic),
                    };
                    let publication_source = snapshot.source().to_owned();
                    let live_started = run.measurement_enabled().then(Instant::now);
                    let (diagnostic, source_interface_elapsed_ns) = if run.measurement_enabled() {
                        load_checked_local_module_for_refresh_from_snapshot_observed(
                            loaded,
                            policy,
                            import_use_counts,
                            promoted_index,
                            available_modules,
                            verified_modules_by_module,
                            artifacts,
                            &compile_options,
                            snapshot,
                        )
                    } else {
                        (
                            load_checked_local_module_for_refresh_from_snapshot(
                                loaded,
                                policy,
                                import_use_counts,
                                promoted_index,
                                available_modules,
                                verified_modules_by_module,
                                artifacts,
                                &compile_options,
                                snapshot,
                            ),
                            0,
                        )
                    };
                    if let Some(started) = live_started {
                        run.record_live_support_elapsed(
                            u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX),
                        );
                        run.record_source_interface_resolution_elapsed(source_interface_elapsed_ns);
                    }
                    if let Some(diagnostic) = diagnostic {
                        return Some(diagnostic);
                    }
                    let closure_used_cached_context =
                        match targeted_direct_closure_used_cached_context(
                            loaded,
                            promoted_index,
                            &authoring_contexts,
                        ) {
                            Ok(value) => value,
                            Err(diagnostic) => return Some(diagnostic),
                        };
                    if let Err(diagnostic) = retain_targeted_live_authoring_context(
                        loaded,
                        promoted_index,
                        &authoring_session,
                        available_modules,
                        verified_modules_by_module,
                        &mut authoring_contexts,
                        &mut authoring_source_interfaces,
                    ) {
                        return Some(*diagnostic);
                    }
                    if let Err(diagnostic) = run.record_live_support_completion(promoted_index) {
                        return Some(diagnostic);
                    }
                    let promoted_module =
                        &loaded.validated.manifest().modules[promoted_index].module;
                    let Some(available) = available_modules.get(promoted_module) else {
                        return Some(targeted_authoring_execution_invalid(
                            "published_support_interface_missing",
                        ));
                    };
                    let Some(verified) = verified_modules_by_module.get(promoted_module) else {
                        return Some(targeted_authoring_execution_invalid(
                            "published_support_verified_module_missing",
                        ));
                    };
                    run.publish_accepted_live_support(
                        loaded,
                        promoted_index,
                        &publication_source,
                        &available.source_interface,
                        verified,
                        closure_used_cached_context,
                    );
                    if let Err(diagnostic) = consume_and_release_targeted_local_producers(
                        loaded,
                        promoted_index,
                        run,
                        available_modules,
                        verified_modules_by_module,
                        &mut authoring_contexts,
                        &mut authoring_source_interfaces,
                    ) {
                        return Some(diagnostic);
                    }
                }
                continue;
            }

            let live_started = run.measurement_enabled().then(Instant::now);
            let (diagnostic, source_interface_elapsed_ns) = if run.measurement_enabled() {
                load_checked_local_module_for_refresh_observed(
                    loaded,
                    policy,
                    import_use_counts,
                    module_index,
                    true,
                    available_modules,
                    verified_modules_by_module,
                    artifacts,
                    &compile_options,
                )
            } else {
                (
                    load_checked_local_module_for_refresh(
                        loaded,
                        policy,
                        import_use_counts,
                        module_index,
                        true,
                        available_modules,
                        verified_modules_by_module,
                        artifacts,
                        &compile_options,
                    ),
                    0,
                )
            };
            if let Some(started) = live_started {
                run.record_live_support_elapsed(
                    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX),
                );
                run.record_source_interface_resolution_elapsed(source_interface_elapsed_ns);
            }
            if let Some(diagnostic) = diagnostic {
                return Some(diagnostic);
            }
            if let Err(diagnostic) = retain_targeted_live_authoring_context(
                loaded,
                module_index,
                &authoring_session,
                available_modules,
                verified_modules_by_module,
                &mut authoring_contexts,
                &mut authoring_source_interfaces,
            ) {
                return Some(*diagnostic);
            }
            if let Err(diagnostic) = run.record_live_support_completion(module_index) {
                return Some(diagnostic);
            }
            if let Err(diagnostic) = consume_and_release_targeted_local_producers(
                loaded,
                module_index,
                run,
                available_modules,
                verified_modules_by_module,
                &mut authoring_contexts,
                &mut authoring_source_interfaces,
            ) {
                return Some(diagnostic);
            }
            continue;
        }

        let forced_live = execution_plan.is_forced_live(module_index);
        if let Err(diagnostic) = run.record_target_attempt(module_index, forced_live) {
            return Some(diagnostic);
        }
        if !forced_live && !pending_contexts_adopted {
            let adopted = match run.adopt_remaining_cached_support(&authoring_session) {
                Ok(adopted) => adopted,
                Err(diagnostic) => return Some(diagnostic),
            };
            for cached in adopted {
                let (cached_index, context, source_interface) = cached.into_parts();
                let cached_module = source_interface.module.clone();
                if authoring_contexts
                    .insert(cached_module.clone(), context)
                    .is_some()
                    || authoring_source_interfaces
                        .insert(cached_module, source_interface)
                        .is_some()
                {
                    return Some(targeted_authoring_execution_invalid(
                        "cached_authoring_context_duplicate",
                    ));
                }
                if let Err(diagnostic) = consume_and_release_targeted_local_producers(
                    loaded,
                    cached_index,
                    run,
                    available_modules,
                    verified_modules_by_module,
                    &mut authoring_contexts,
                    &mut authoring_source_interfaces,
                ) {
                    return Some(diagnostic);
                }
            }
            pending_contexts_adopted = true;
        }

        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let source_hash = package_file_hash(source.as_bytes());
        let file_id = match checked_current_module_file_id(module_index) {
            Ok(file_id) => file_id,
            Err(error) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, error.reason_code())
                        .with_module(module.module.as_dotted()),
                )
            }
        };

        if forced_live {
            let (direct_verified_modules, direct_source_interfaces) =
                match take_refresh_direct_import_context(loaded, module_index, available_modules) {
                    Ok(imports) => imports,
                    Err(diagnostic) => return Some(*diagnostic),
                };
            let direct_verified_module_refs = direct_verified_modules
                .iter()
                .map(Arc::as_ref)
                .collect::<Vec<_>>();
            let available_verified_module_refs = available_verified_module_refs_for_direct_imports(
                &direct_verified_modules,
                verified_modules_by_module,
            );
            let (
                certificate,
                generated_bytes,
                verified,
                source_interface,
                source_imports,
                verification_elapsed_ns,
            ) = match build_refresh_module_from_source(
                module_index,
                module,
                &source,
                file_id,
                &direct_verified_module_refs,
                &available_verified_module_refs,
                &direct_source_interfaces,
                policy,
                observations,
            ) {
                Ok(output) => output,
                Err(diagnostic) => return Some(*diagnostic),
            };
            run.record_fresh_target_verification_elapsed(verification_elapsed_ns);
            if let Some(diagnostic) = validate_targeted_authoring_target_output(
                loaded,
                module_index,
                module,
                source_imports.as_deref(),
                &direct_source_interfaces,
                &certificate,
            ) {
                return Some(diagnostic);
            }
            let imported_source_interface = HumanImportedSourceInterface {
                module: module.module.clone(),
                export_hash: certificate.hashes().export_hash,
                certificate_hash: Some(certificate.hashes().certificate_hash),
                source_interface,
            };
            let verified = Arc::new(verified);
            let retain = match run.register_target_lifetime(module_index, true) {
                Ok(retain) => retain,
                Err(diagnostic) => return Some(diagnostic),
            };
            if retain {
                verified_modules_by_module.insert(module.module.clone(), Arc::clone(&verified));
                available_modules.insert(
                    module.module.clone(),
                    RefreshAvailableModule {
                        verified: Arc::clone(&verified),
                        source_interface: imported_source_interface.clone(),
                        remaining_uses: import_use_counts
                            .get(&module.module)
                            .copied()
                            .unwrap_or_default(),
                        origin: RefreshImportOrigin::Local,
                    },
                );
                authoring_contexts.insert(
                    module.module.clone(),
                    authoring_session.register_shared_fresh_target(verified),
                );
                authoring_source_interfaces
                    .insert(module.module.clone(), imported_source_interface);
            }
            push_targeted_authoring_local_identity(
                local_modules,
                module_index,
                module,
                source_hash,
                source_imports,
                &certificate,
                generated_bytes,
            );
        } else {
            let (direct_authoring_imports, available_authoring_imports, direct_source_interfaces) =
                match targeted_authoring_import_context(
                    loaded,
                    module_index,
                    &authoring_contexts,
                    &authoring_source_interfaces,
                ) {
                    Ok(imports) => imports,
                    Err(diagnostic) => return Some(*diagnostic),
                };
            let build = match authoring_session.compile_human_target(
                file_id,
                module.module.clone(),
                &source,
                &direct_authoring_imports,
                &available_authoring_imports,
                &direct_source_interfaces,
                &compile_options,
                policy,
                observations.kernel_work_counter_sink(),
                observations.collect_declaration_details(),
            ) {
                Ok(build) => build,
                Err(error) => {
                    return Some(frontend_build_failed(
                        module_index,
                        module,
                        file_id,
                        &source,
                        &direct_source_interfaces,
                        error,
                    ))
                }
            };
            run.record_fresh_target_verification_elapsed(
                build
                    .compilation_observations()
                    .source_free_verification_elapsed_ns,
            );
            observations
                .record_declaration_batch(&module.module, build.compilation_observations().clone());
            let generated_bytes = build.certificate_bytes().to_vec();
            let certificate = match npa_cert::decode_module_cert(&generated_bytes) {
                Ok(certificate) => certificate,
                Err(error) => {
                    return Some(
                        CommandDiagnostic::error(
                            DiagnosticKind::Build,
                            "certificate_decode_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(render_package_path(&module.certificate))
                        .with_actual_value(format!("{error:?}")),
                    )
                }
            };
            let source_imports = human_source_imports(file_id, &source, &direct_source_interfaces);
            if let Some(diagnostic) = validate_targeted_authoring_target_output(
                loaded,
                module_index,
                module,
                source_imports.as_deref(),
                &direct_source_interfaces,
                &certificate,
            ) {
                return Some(diagnostic);
            }
            let retain = match run.register_target_lifetime(module_index, false) {
                Ok(retain) => retain,
                Err(diagnostic) => return Some(diagnostic),
            };
            if retain {
                authoring_contexts.insert(module.module.clone(), build.fresh_import_context());
                authoring_source_interfaces
                    .insert(module.module.clone(), build.imported_source_interface());
            }
            push_targeted_authoring_local_identity(
                local_modules,
                module_index,
                module,
                source_hash,
                source_imports,
                &certificate,
                generated_bytes,
            );
        }

        if let Err(diagnostic) = consume_and_release_targeted_local_producers(
            loaded,
            module_index,
            run,
            available_modules,
            verified_modules_by_module,
            &mut authoring_contexts,
            &mut authoring_source_interfaces,
        ) {
            return Some(diagnostic);
        }
        run.record_target_completion();
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn retain_targeted_live_authoring_context<'session>(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    session: &'session TargetedAuthoringBuildSession,
    available_modules: &BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &BTreeMap<Name, Arc<VerifiedModule>>,
    authoring_contexts: &mut TargetedAuthoringContextMap<'session>,
    authoring_source_interfaces: &mut BTreeMap<Name, HumanImportedSourceInterface>,
) -> Result<(), Box<CommandDiagnostic>> {
    let module = &loaded.validated.manifest().modules[module_index];
    let verified = verified_modules_by_module
        .get(&module.module)
        .ok_or_else(|| {
            Box::new(targeted_authoring_execution_invalid(
                "live_verified_module_missing",
            ))
        })?;
    let source_interface = available_modules
        .get(&module.module)
        .map(|available| available.source_interface.clone())
        .ok_or_else(|| {
            Box::new(targeted_authoring_execution_invalid(
                "live_source_interface_missing",
            ))
        })?;
    if authoring_contexts
        .insert(
            module.module.clone(),
            session.register_shared_live_support(Arc::clone(verified)),
        )
        .is_some()
        || authoring_source_interfaces
            .insert(module.module.clone(), source_interface)
            .is_some()
    {
        return Err(Box::new(targeted_authoring_execution_invalid(
            "live_authoring_context_duplicate",
        )));
    }
    Ok(())
}

type TargetedAuthoringImportSet<'session> = (
    Vec<HumanAuthoringImport<'session>>,
    Vec<HumanAuthoringImport<'session>>,
    Vec<HumanImportedSourceInterface>,
);

fn targeted_authoring_import_context<'session>(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    authoring_contexts: &TargetedAuthoringContextMap<'session>,
    authoring_source_interfaces: &BTreeMap<Name, HumanImportedSourceInterface>,
) -> Result<TargetedAuthoringImportSet<'session>, Box<CommandDiagnostic>> {
    let mut direct_imports = Vec::new();
    let mut direct_source_interfaces = Vec::new();
    for (import_index, import) in loaded.validated.graph().resolved_module_imports[module_index]
        .iter()
        .enumerate()
    {
        let path = format!("modules[{module_index}].imports[{import_index}]");
        let context = authoring_contexts.get(&import.module).ok_or_else(|| {
            Box::new(
                targeted_authoring_execution_invalid("authoring_import_unavailable")
                    .with_module(import.module.as_dotted())
                    .with_path(path.clone()),
            )
        })?;
        let authoring_import = context.authoring_import().map_err(|error| {
            Box::new(
                targeted_authoring_execution_invalid("authoring_import_projection_failed")
                    .with_module(import.module.as_dotted())
                    .with_path(path.clone())
                    .with_actual_value(format!("{error:?}")),
            )
        })?;
        let actual_export_hash = PackageHash::from(authoring_import.export_hash());
        if actual_export_hash != import.export_hash {
            return Err(Box::new(hash_mismatch(
                "export_hash_mismatch",
                format!("{path}.export_hash"),
                "export_hash",
                import.export_hash,
                actual_export_hash,
            )));
        }
        let actual_certificate_hash = authoring_import
            .certificate_hash()
            .map(PackageHash::from)
            .ok_or_else(|| {
                Box::new(
                    targeted_authoring_execution_invalid("authoring_certificate_hash_missing")
                        .with_module(import.module.as_dotted())
                        .with_path(format!("{path}.certificate_hash")),
                )
            })?;
        if actual_certificate_hash != import.certificate_hash {
            return Err(Box::new(hash_mismatch(
                "certificate_hash_mismatch",
                format!("{path}.certificate_hash"),
                "certificate_hash",
                import.certificate_hash,
                actual_certificate_hash,
            )));
        }
        let source_interface = authoring_source_interfaces
            .get(&import.module)
            .cloned()
            .ok_or_else(|| {
                Box::new(
                    targeted_authoring_execution_invalid("authoring_source_interface_missing")
                        .with_module(import.module.as_dotted())
                        .with_path(path),
                )
            })?;
        direct_imports.push(authoring_import);
        direct_source_interfaces.push(source_interface);
    }
    let available_imports = authoring_contexts
        .values()
        .map(TargetedAuthoringImportContext::authoring_import)
        .collect::<npa_cert::Result<Vec<_>>>()
        .map_err(|error| {
            Box::new(
                targeted_authoring_execution_invalid("available_authoring_projection_failed")
                    .with_actual_value(format!("{error:?}")),
            )
        })?;
    Ok((direct_imports, available_imports, direct_source_interfaces))
}

#[allow(clippy::too_many_arguments)]
fn consume_and_release_targeted_local_producers(
    loaded: &LoadedPackageRoot,
    consumer_index: usize,
    run: &mut TargetedAuthoringCheckRun,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    authoring_contexts: &mut TargetedAuthoringContextMap<'_>,
    authoring_source_interfaces: &mut BTreeMap<Name, HumanImportedSourceInterface>,
) -> Result<(), CommandDiagnostic> {
    for released_index in run.consume_local_consumer(consumer_index)? {
        let module = &loaded.validated.manifest().modules[released_index].module;
        available_modules.remove(module);
        verified_modules_by_module.remove(module);
        authoring_contexts.remove(module);
        authoring_source_interfaces.remove(module);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_targeted_authoring_target_output(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    source_imports: Option<&[Name]>,
    direct_source_interfaces: &[HumanImportedSourceInterface],
    certificate: &ModuleCert,
) -> Option<CommandDiagnostic> {
    if let Some(diagnostic) =
        check_generated_axiom_policy(loaded, module_index, module, certificate)
    {
        return Some(diagnostic);
    }
    if certificate.header().module != module.module {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_field("module")
                .with_expected_value(module.module.as_dotted())
                .with_actual_value(certificate.header().module.as_dotted()),
        );
    }
    if let Some(source_imports) = source_imports {
        if let Some(diagnostic) = check_observable_import_drift(
            module_index,
            module,
            source_imports,
            certificate,
            direct_source_interfaces,
        ) {
            return Some(diagnostic);
        }
    }
    let expected_imports = match package_lock_imports_for_source_interfaces(
        direct_source_interfaces,
        &format!("modules[{module_index}].imports"),
        &module.module,
    ) {
        Ok(imports) => imports,
        Err(diagnostic) => return Some(*diagnostic),
    };
    if let Some(diagnostic) = check_refreshed_certificate_import_identities(
        module_index,
        &module.module,
        &expected_imports,
        certificate.imports(),
    ) {
        return Some(diagnostic);
    }
    None
}

fn targeted_direct_closure_used_cached_context(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    authoring_contexts: &TargetedAuthoringContextMap<'_>,
) -> Result<bool, CommandDiagnostic> {
    let imports = loaded
        .validated
        .graph()
        .resolved_module_imports
        .get(module_index)
        .ok_or_else(|| targeted_authoring_execution_invalid("publication_import_row_missing"))?;
    for import in imports {
        if !matches!(import.kind, ResolvedModuleImportKind::Local { .. }) {
            continue;
        }
        let context = authoring_contexts.get(&import.module).ok_or_else(|| {
            targeted_authoring_execution_invalid("publication_import_context_missing")
        })?;
        if context.closure_used_cached_context() {
            return Ok(true);
        }
    }
    Ok(false)
}

fn push_targeted_authoring_local_identity(
    local_modules: &mut Vec<LocalModuleRefreshIdentity>,
    module_index: usize,
    module: &PackageModule,
    source_hash: PackageHash,
    source_imports: Option<Vec<Name>>,
    certificate: &ModuleCert,
    generated_bytes: Vec<u8>,
) {
    local_modules.push(LocalModuleRefreshIdentity {
        module_index,
        module: module.module.clone(),
        source_hash,
        source_imports,
        certificate_file_hash: package_file_hash(&generated_bytes),
        export_hash: PackageHash::from(certificate.hashes().export_hash),
        axiom_report_hash: PackageHash::from(certificate.hashes().axiom_report_hash),
        certificate_hash: PackageHash::from(certificate.hashes().certificate_hash),
        certificate_path: module.certificate.clone(),
        certificate_bytes: generated_bytes,
        metadata_path: None,
        metadata_bytes: None,
    });
}

fn targeted_authoring_execution_invalid(reason: &'static str) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::Internal, "targeted_authoring_plan_invalid")
        .with_actual_value(reason)
}

#[allow(clippy::too_many_arguments)]
fn process_targeted_refresh_local_order(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelectionPlan,
    local_plan: &TargetedRefreshLocalPlan,
    order: &[usize],
    priority_phase: bool,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    state: &mut TargetedRefreshExecutionState,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<(), Box<CommandDiagnostic>> {
    let compile_options = observations.compile_options();
    let local_module_names = loaded
        .validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    for &module_index in order {
        if !state.processed_local.insert(module_index) {
            return Err(targeted_refresh_plan_invalid("local_processed_twice"));
        }
        let role = targeted_refresh_module_role(local_plan, module_index, priority_phase)?;
        match role {
            RefreshModuleRole::CheckedSupport | RefreshModuleRole::UnrelatedSnapshot => {
                let module = loaded
                    .validated
                    .manifest()
                    .modules
                    .get(module_index)
                    .ok_or_else(|| targeted_refresh_plan_invalid("local_index_out_of_range"))?;
                if state
                    .verified_modules_by_module
                    .contains_key(&module.module)
                {
                    return Err(targeted_refresh_plan_invalid(
                        "local_verified_module_duplicate",
                    ));
                }
                let mut artifacts = Vec::new();
                if let Some(diagnostic) = load_checked_local_module_for_refresh(
                    loaded,
                    policy,
                    import_use_counts,
                    module_index,
                    role == RefreshModuleRole::CheckedSupport,
                    &mut state.available_modules,
                    &mut state.verified_modules_by_module,
                    &mut artifacts,
                    &compile_options,
                ) {
                    return Err(Box::new(diagnostic));
                }
                for artifact in artifacts {
                    insert_targeted_refresh_artifact(state, artifact)?;
                }
            }
            RefreshModuleRole::Rebuild => process_targeted_refresh_rebuild_module(
                loaded,
                selection,
                module_index,
                priority_phase,
                policy,
                import_use_counts,
                &local_module_names,
                &compile_options,
                state,
                observations,
            )?,
        }
    }
    Ok(())
}

fn targeted_refresh_module_role(
    plan: &TargetedRefreshLocalPlan,
    module_index: usize,
    priority_phase: bool,
) -> Result<RefreshModuleRole, Box<CommandDiagnostic>> {
    let role = if priority_phase {
        if plan.priority_rebuild.contains(&module_index) {
            Some(RefreshModuleRole::Rebuild)
        } else if plan.priority_support.contains(&module_index) {
            Some(RefreshModuleRole::CheckedSupport)
        } else {
            None
        }
    } else if plan.completion_rebuild.contains(&module_index) {
        Some(RefreshModuleRole::Rebuild)
    } else if plan.completion_support.contains(&module_index) {
        Some(RefreshModuleRole::CheckedSupport)
    } else if plan.completion_snapshot.contains(&module_index) {
        Some(RefreshModuleRole::UnrelatedSnapshot)
    } else {
        None
    };
    role.ok_or_else(|| targeted_refresh_plan_invalid("local_role_missing"))
}

#[allow(clippy::too_many_arguments)]
fn process_targeted_refresh_rebuild_module(
    loaded: &LoadedPackageRoot,
    selection: &PackageBuildSelectionPlan,
    module_index: usize,
    defer_metadata: bool,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    local_module_names: &BTreeSet<Name>,
    compile_options: &HumanCompileOptions,
    state: &mut TargetedRefreshExecutionState,
    observations: &mut PackageBuildObservationCoordinator,
) -> Result<(), Box<CommandDiagnostic>> {
    let module = loaded
        .validated
        .manifest()
        .modules
        .get(module_index)
        .ok_or_else(|| targeted_refresh_plan_invalid("local_index_out_of_range"))?;
    if state.artifacts_by_path.contains_key(&module.certificate)
        || state
            .refreshed_modules_by_index
            .values()
            .any(|identity| identity.certificate_path == module.certificate)
    {
        return Err(duplicate_refresh_artifact_path(&module.certificate));
    }
    let source = read_source(loaded, module_index, module)?;
    state.stats.source_scans = state.stats.source_scans.saturating_add(1);
    let source_hash = package_file_hash(source.as_bytes());
    let file_id = u32::try_from(module_index).map(FileId).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                .with_module(module.module.as_dotted()),
        )
    })?;
    let (direct_verified_modules, direct_source_interfaces) =
        take_refresh_direct_import_context(loaded, module_index, &mut state.available_modules)?;
    let expected_imports = package_lock_imports_for_source_interfaces(
        &direct_source_interfaces,
        &format!("modules[{module_index}].imports"),
        &module.module,
    )?;
    let direct_verified_module_refs = direct_verified_modules
        .iter()
        .map(Arc::as_ref)
        .collect::<Vec<_>>();
    let available_verified_module_refs = available_verified_module_refs_for_direct_imports(
        &direct_verified_modules,
        &state.verified_modules_by_module,
    );
    let is_nonseed = !selection.seeds.contains(&module_index);
    let may_reuse = is_nonseed && !is_std_core_builder_profile(module.producer_profile.as_deref());
    let qualified = if may_reuse {
        Some(qualify_dependent_refresh(
            loaded,
            policy,
            module_index,
            module,
            &source,
            source_hash,
            file_id,
            &direct_verified_modules,
            &direct_source_interfaces,
            &state.verified_modules_by_module,
            local_module_names,
            &mut state.stats,
            compile_options,
        )?)
    } else if is_nonseed {
        Some(QualifiedDependentRefresh::Fallback("producer_profile"))
    } else {
        None
    };
    let (certificate, generated_bytes, verified, source_interface, source_imports, _) =
        match qualified {
            Some(QualifiedDependentRefresh::Unchanged {
                certificate,
                bytes,
                verified,
                source_interface,
                source_imports,
            }) => {
                state.stats.unchanged = state.stats.unchanged.saturating_add(1);
                (
                    certificate,
                    bytes,
                    verified,
                    source_interface,
                    Some(source_imports),
                    0,
                )
            }
            Some(QualifiedDependentRefresh::Rebound {
                certificate,
                bytes,
                verified,
                source_interface,
                source_imports,
            }) => {
                state.stats.certificate_rebinds = state.stats.certificate_rebinds.saturating_add(1);
                (
                    certificate,
                    bytes,
                    verified,
                    source_interface,
                    Some(source_imports),
                    0,
                )
            }
            fallback => {
                state.stats.source_rebuilds = state.stats.source_rebuilds.saturating_add(1);
                if let Some(QualifiedDependentRefresh::Fallback(reason)) = fallback {
                    state.stats.record_fallback(reason);
                }
                build_refresh_module_from_source(
                    module_index,
                    module,
                    &source,
                    file_id,
                    &direct_verified_module_refs,
                    &available_verified_module_refs,
                    &direct_source_interfaces,
                    policy,
                    observations,
                )?
            }
        };
    if let Some(diagnostic) =
        check_generated_axiom_policy(loaded, module_index, module, &certificate)
    {
        return Err(Box::new(diagnostic));
    }
    if verified.module() != &module.module {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_field("module")
                .with_expected_value(module.module.as_dotted())
                .with_actual_value(verified.module().as_dotted()),
        ));
    }
    if let Some(source_imports) = source_imports.as_deref() {
        if let Some(diagnostic) = check_observable_import_drift(
            module_index,
            module,
            source_imports,
            &certificate,
            &direct_source_interfaces,
        ) {
            return Err(Box::new(diagnostic));
        }
    }
    if let Some(diagnostic) = check_refreshed_certificate_import_identities(
        module_index,
        &module.module,
        &expected_imports,
        certificate.imports(),
    ) {
        return Err(Box::new(diagnostic));
    }

    let certificate_file_hash = package_file_hash(&generated_bytes);
    let export_hash = PackageHash::from(certificate.hashes().export_hash);
    let axiom_report_hash = PackageHash::from(certificate.hashes().axiom_report_hash);
    let certificate_hash = PackageHash::from(certificate.hashes().certificate_hash);
    let pending_source_interface =
        (defer_metadata && module.meta.is_some()).then(|| source_interface.clone());
    let (metadata_path, metadata_bytes) = if defer_metadata {
        (None, None)
    } else {
        refreshed_module_metadata(
            loaded,
            module_index,
            module,
            &verified,
            &source_interface,
            source_hash,
            certificate_file_hash,
            axiom_report_hash,
        )?
    };
    drop(source);
    let remaining_uses = import_use_counts
        .get(&module.module)
        .copied()
        .unwrap_or_default();
    let verified = Arc::new(verified);
    if state
        .verified_modules_by_module
        .insert(module.module.clone(), Arc::clone(&verified))
        .is_some()
    {
        return Err(targeted_refresh_plan_invalid(
            "local_verified_module_duplicate",
        ));
    }
    if remaining_uses > 0
        && state
            .available_modules
            .insert(
                module.module.clone(),
                RefreshAvailableModule {
                    verified: Arc::clone(&verified),
                    source_interface: HumanImportedSourceInterface {
                        module: module.module.clone(),
                        export_hash: certificate.hashes().export_hash,
                        certificate_hash: Some(certificate.hashes().certificate_hash),
                        source_interface,
                    },
                    remaining_uses,
                    origin: RefreshImportOrigin::Local,
                },
            )
            .is_some()
    {
        return Err(targeted_refresh_plan_invalid(
            "local_available_module_duplicate",
        ));
    }
    let identity = LocalModuleRefreshIdentity {
        module_index,
        module: module.module.clone(),
        source_hash,
        source_imports,
        certificate_file_hash,
        export_hash,
        axiom_report_hash,
        certificate_hash,
        certificate_path: module.certificate.clone(),
        certificate_bytes: generated_bytes,
        metadata_path,
        metadata_bytes,
    };
    if state
        .refreshed_modules_by_index
        .insert(module_index, identity)
        .is_some()
    {
        return Err(targeted_refresh_plan_invalid("local_refreshed_twice"));
    }
    if let Some(source_interface) = pending_source_interface {
        if state
            .pending_priority_metadata_by_index
            .insert(
                module_index,
                PendingPriorityMetadata {
                    verified,
                    source_interface,
                },
            )
            .is_some()
        {
            return Err(targeted_refresh_plan_invalid("priority_metadata_duplicate"));
        }
    }
    Ok(())
}

fn finalize_targeted_refresh_priority_metadata(
    loaded: &LoadedPackageRoot,
    local_plan: &TargetedRefreshLocalPlan,
    state: &mut TargetedRefreshExecutionState,
) -> Result<(), Box<CommandDiagnostic>> {
    for &module_index in &local_plan.priority_local_order {
        let Some(pending) = state
            .pending_priority_metadata_by_index
            .remove(&module_index)
        else {
            continue;
        };
        let module = loaded
            .validated
            .manifest()
            .modules
            .get(module_index)
            .ok_or_else(|| targeted_refresh_plan_invalid("local_index_out_of_range"))?;
        let identity = state
            .refreshed_modules_by_index
            .get_mut(&module_index)
            .ok_or_else(|| targeted_refresh_plan_invalid("priority_identity_missing"))?;
        if identity.metadata_path.is_some() || identity.metadata_bytes.is_some() {
            return Err(targeted_refresh_plan_invalid(
                "priority_metadata_already_finalized",
            ));
        }
        let (metadata_path, metadata_bytes) = refreshed_module_metadata(
            loaded,
            module_index,
            module,
            &pending.verified,
            &pending.source_interface,
            identity.source_hash,
            identity.certificate_file_hash,
            identity.axiom_report_hash,
        )?;
        identity.metadata_path = metadata_path;
        identity.metadata_bytes = metadata_bytes;
    }
    if !state.pending_priority_metadata_by_index.is_empty() {
        return Err(targeted_refresh_plan_invalid(
            "priority_metadata_not_finalized",
        ));
    }
    Ok(())
}

fn insert_targeted_refresh_artifact(
    state: &mut TargetedRefreshExecutionState,
    artifact: CertificateArtifactBuffer,
) -> Result<(), Box<CommandDiagnostic>> {
    if state.artifacts_by_path.contains_key(&artifact.path)
        || state
            .refreshed_modules_by_index
            .values()
            .any(|identity| identity.certificate_path == artifact.path)
    {
        return Err(duplicate_refresh_artifact_path(&artifact.path));
    }
    state
        .artifacts_by_path
        .insert(artifact.path.clone(), artifact);
    Ok(())
}

fn duplicate_refresh_artifact_path(path: &PackagePath) -> Box<CommandDiagnostic> {
    Box::new(CommandDiagnostic::from_package_lock_error(
        &PackageLockError::duplicate_certificate_path("artifacts", path.as_str()),
    ))
}

#[allow(clippy::too_many_arguments)]
fn build_local_modules_for_refresh(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    local_modules: &mut Vec<LocalModuleRefreshIdentity>,
    rebuild: Option<&BTreeSet<usize>>,
    support_local: &BTreeSet<usize>,
    snapshot_unrelated: bool,
    refresh_metadata: bool,
    unchanged_artifacts: &mut Vec<CertificateArtifactBuffer>,
    targeted_seeds: Option<&BTreeSet<usize>>,
    interface_aware: bool,
    targeted_stats: &mut TargetedRefreshStats,
    mut targeted_check_cache: Option<&mut TargetedBuildCheckCacheState>,
    mut targeted_authoring_run: Option<&mut TargetedAuthoringCheckRun>,
    observations: &mut PackageBuildObservationCoordinator,
) -> Option<CommandDiagnostic> {
    let compile_options = observations.compile_options();
    let local_module_names = loaded
        .validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    for &module_index in &loaded.validated.graph().topological_order {
        let module = &loaded.validated.manifest().modules[module_index];
        if rebuild.is_some_and(|rebuild| !rebuild.contains(&module_index)) {
            let is_support = support_local.contains(&module_index);
            if !is_support && !snapshot_unrelated {
                continue;
            }
            if is_support {
                if let Some(cache) = targeted_check_cache.as_deref_mut() {
                    cache.stats.support_live_checked =
                        cache.stats.support_live_checked.saturating_add(1);
                }
                if let Some(run) = targeted_authoring_run.as_deref_mut() {
                    run.record_live_support_visit(module_index);
                    let captured_pre_target = run.should_capture_pre_target_snapshot(module_index);
                    if captured_pre_target {
                        let snapshot = run.time_current_byte_validation_for(module_index, || {
                            read_targeted_authoring_local_snapshot(loaded, module_index, module)
                        });
                        let (artifact, snapshot) = match snapshot {
                            Ok(snapshot) => snapshot,
                            Err(diagnostic) => return Some(*diagnostic),
                        };
                        if let Err(diagnostic) = run.lookup_pre_target_support(
                            loaded,
                            module_index,
                            artifact,
                            snapshot,
                            verified_modules_by_module,
                            policy,
                        ) {
                            return Some(diagnostic);
                        }
                    }
                    if captured_pre_target {
                        let promoted = match run.resolve_reached_pre_target_support(module_index) {
                            Ok(promoted) => promoted,
                            Err(diagnostic) => return Some(diagnostic),
                        };
                        for promoted_index in promoted {
                            let snapshot = match run.take_retained_snapshot(promoted_index) {
                                Ok(snapshot) => snapshot,
                                Err(diagnostic) => return Some(diagnostic),
                            };
                            let live_started = run.measurement_enabled().then(Instant::now);
                            let (diagnostic, source_interface_elapsed_ns) =
                                if run.measurement_enabled() {
                                    load_checked_local_module_for_refresh_from_snapshot_observed(
                                        loaded,
                                        policy,
                                        import_use_counts,
                                        promoted_index,
                                        available_modules,
                                        verified_modules_by_module,
                                        unchanged_artifacts,
                                        &compile_options,
                                        snapshot,
                                    )
                                } else {
                                    (
                                        load_checked_local_module_for_refresh_from_snapshot(
                                            loaded,
                                            policy,
                                            import_use_counts,
                                            promoted_index,
                                            available_modules,
                                            verified_modules_by_module,
                                            unchanged_artifacts,
                                            &compile_options,
                                            snapshot,
                                        ),
                                        0,
                                    )
                                };
                            if let Some(started) = live_started {
                                run.record_live_support_elapsed(
                                    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX),
                                );
                                run.record_source_interface_resolution_elapsed(
                                    source_interface_elapsed_ns,
                                );
                            }
                            if let Some(diagnostic) = diagnostic {
                                return Some(diagnostic);
                            }
                            if let Err(diagnostic) =
                                run.record_live_support_completion(promoted_index)
                            {
                                return Some(diagnostic);
                            }
                        }
                        continue;
                    }
                }
            }
            let warming_snapshot = if is_support
                && targeted_check_cache
                    .as_deref()
                    .is_some_and(|cache| !cache.support_publication_closed)
            {
                let (artifact, snapshot) =
                    match read_targeted_authoring_local_snapshot(loaded, module_index, module) {
                        Ok(snapshot) => snapshot,
                        Err(diagnostic) => return Some(*diagnostic),
                    };
                Some((artifact, snapshot.source().to_owned(), snapshot))
            } else {
                None
            };
            let mut warming_publication = None;
            let observe_authoring_live = targeted_authoring_run
                .as_deref()
                .is_some_and(TargetedAuthoringCheckRun::measurement_enabled);
            let observe_read_through_live =
                is_support && targeted_check_cache.is_some() && observations.measurement_enabled();
            let observe_live = observe_authoring_live || observe_read_through_live;
            let live_started = observe_live.then(Instant::now);
            let (load_diagnostic, source_interface_elapsed_ns) = match warming_snapshot {
                Some((artifact, source, snapshot)) => {
                    warming_publication = Some((artifact, source));
                    if observe_live {
                        load_checked_local_module_for_refresh_from_snapshot_observed(
                            loaded,
                            policy,
                            import_use_counts,
                            module_index,
                            available_modules,
                            verified_modules_by_module,
                            unchanged_artifacts,
                            &compile_options,
                            snapshot,
                        )
                    } else {
                        (
                            load_checked_local_module_for_refresh_from_snapshot(
                                loaded,
                                policy,
                                import_use_counts,
                                module_index,
                                available_modules,
                                verified_modules_by_module,
                                unchanged_artifacts,
                                &compile_options,
                                snapshot,
                            ),
                            0,
                        )
                    }
                }
                None => {
                    if observe_live {
                        load_checked_local_module_for_refresh_observed(
                            loaded,
                            policy,
                            import_use_counts,
                            module_index,
                            is_support,
                            available_modules,
                            verified_modules_by_module,
                            unchanged_artifacts,
                            &compile_options,
                        )
                    } else {
                        (
                            load_checked_local_module_for_refresh(
                                loaded,
                                policy,
                                import_use_counts,
                                module_index,
                                is_support,
                                available_modules,
                                verified_modules_by_module,
                                unchanged_artifacts,
                                &compile_options,
                            ),
                            0,
                        )
                    }
                }
            };
            if let (Some(run), Some(started)) =
                (targeted_authoring_run.as_deref_mut(), live_started)
            {
                run.record_live_support_elapsed(
                    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX),
                );
                run.record_source_interface_resolution_elapsed(source_interface_elapsed_ns);
            }
            if observe_read_through_live {
                if let (Some(cache), Some(started)) =
                    (targeted_check_cache.as_deref_mut(), live_started)
                {
                    cache.stats.live_support_elapsed_ns =
                        cache.stats.live_support_elapsed_ns.saturating_add(
                            u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX),
                        );
                    cache.stats.source_interface_resolution_elapsed_ns = cache
                        .stats
                        .source_interface_resolution_elapsed_ns
                        .saturating_add(source_interface_elapsed_ns);
                }
            }
            if let Some(diagnostic) = load_diagnostic {
                return Some(diagnostic);
            }
            if let (Some((artifact, source)), Some(cache)) =
                (warming_publication, targeted_check_cache.as_deref_mut())
            {
                let accepted = available_modules
                    .get(&module.module)
                    .zip(verified_modules_by_module.get(&module.module));
                if let Some((available, verified)) = accepted {
                    if let Some(publication) = cache.support_publication.as_mut() {
                        let entry = publication.observe_local(
                            loaded,
                            module_index,
                            artifact,
                            &source,
                            &available.source_interface,
                            verified,
                            TargetedAuthoringPublicationOrigin::TargetedReadThroughSupport,
                            false,
                            TargetedAuthoringModuleAcceptance::checked_certificate_complete(),
                        );
                        if let Some(entry) = entry {
                            if let Some(session) = cache.support_session.as_mut() {
                                let outcome = session.publish(&entry, publication.budget_mut());
                                publication.record_publish_outcome(module_index, outcome);
                            }
                        }
                    }
                } else {
                    cache.support_publication =
                        Some(TargetedAuthoringSupportPublicationPlanner::disabled(
                            "accepted_interface_unavailable",
                            observations.collect_declaration_details(),
                        ));
                }
            }
            if is_support {
                if let Some(run) = targeted_authoring_run.as_deref_mut() {
                    if let Err(diagnostic) = run.record_live_support_completion(module_index) {
                        return Some(diagnostic);
                    }
                }
            }
            continue;
        }
        if let Some(cache) = targeted_check_cache.as_deref_mut() {
            cache.support_publication_closed = true;
        }
        if let Some(cache) = targeted_check_cache.as_deref_mut() {
            cache.stats.targets_live_built = cache.stats.targets_live_built.saturating_add(1);
        }
        if let Some(run) = targeted_authoring_run.as_deref_mut() {
            if let Err(diagnostic) = run.record_target_attempt(module_index, false) {
                return Some(diagnostic);
            }
        }
        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        if interface_aware {
            targeted_stats.source_scans += 1;
        }
        let source_hash = package_file_hash(source.as_bytes());
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                        .with_module(module.module.as_dotted()),
                );
            }
        };
        let (direct_verified_modules, direct_source_interfaces) =
            match take_refresh_direct_import_context(loaded, module_index, available_modules) {
                Ok(imports) => imports,
                Err(diagnostic) => return Some(*diagnostic),
            };
        let expected_imports = match package_lock_imports_for_source_interfaces(
            &direct_source_interfaces,
            &format!("modules[{module_index}].imports"),
            &module.module,
        ) {
            Ok(imports) => imports,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let direct_verified_module_refs = direct_verified_modules
            .iter()
            .map(Arc::as_ref)
            .collect::<Vec<_>>();
        let available_verified_module_refs = available_verified_module_refs_for_direct_imports(
            &direct_verified_modules,
            verified_modules_by_module,
        );
        let is_nonseed = targeted_seeds.is_some_and(|seeds| !seeds.contains(&module_index));
        let may_reuse = interface_aware
            && is_nonseed
            && !is_std_core_builder_profile(module.producer_profile.as_deref());
        let qualified = if may_reuse {
            match qualify_dependent_refresh(
                loaded,
                policy,
                module_index,
                module,
                &source,
                source_hash,
                file_id,
                &direct_verified_modules,
                &direct_source_interfaces,
                verified_modules_by_module,
                &local_module_names,
                targeted_stats,
                &compile_options,
            ) {
                Ok(qualified) => Some(qualified),
                Err(diagnostic) => return Some(*diagnostic),
            }
        } else if interface_aware && is_nonseed {
            Some(QualifiedDependentRefresh::Fallback("producer_profile"))
        } else {
            None
        };
        let (
            certificate,
            generated_bytes,
            verified,
            source_interface,
            source_imports,
            verification_elapsed_ns,
        ) = match qualified {
            Some(QualifiedDependentRefresh::Unchanged {
                certificate,
                bytes,
                verified,
                source_interface,
                source_imports,
            }) => {
                targeted_stats.unchanged += 1;
                (
                    certificate,
                    bytes,
                    verified,
                    source_interface,
                    Some(source_imports),
                    0,
                )
            }
            Some(QualifiedDependentRefresh::Rebound {
                certificate,
                bytes,
                verified,
                source_interface,
                source_imports,
            }) => {
                targeted_stats.certificate_rebinds += 1;
                (
                    certificate,
                    bytes,
                    verified,
                    source_interface,
                    Some(source_imports),
                    0,
                )
            }
            fallback => {
                if interface_aware {
                    targeted_stats.source_rebuilds += 1;
                }
                if let Some(QualifiedDependentRefresh::Fallback(reason)) = fallback {
                    targeted_stats.record_fallback(reason);
                }
                match build_refresh_module_from_source(
                    module_index,
                    module,
                    &source,
                    file_id,
                    &direct_verified_module_refs,
                    &available_verified_module_refs,
                    &direct_source_interfaces,
                    policy,
                    observations,
                ) {
                    Ok(output) => output,
                    Err(diagnostic) => return Some(*diagnostic),
                }
            }
        };
        if let Some(cache) = targeted_check_cache.as_deref_mut() {
            cache.stats.fresh_target_elapsed_ns = cache
                .stats
                .fresh_target_elapsed_ns
                .saturating_add(verification_elapsed_ns);
        }
        if let Some(run) = targeted_authoring_run.as_deref_mut() {
            run.record_fresh_target_verification_elapsed(verification_elapsed_ns);
        }
        if let Some(diagnostic) =
            check_generated_axiom_policy(loaded, module_index, module, &certificate)
        {
            return Some(diagnostic);
        }
        if verified.module() != &module.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_field("module")
                    .with_expected_value(module.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }
        if let Some(source_imports) = source_imports.as_deref() {
            if let Some(diagnostic) = check_observable_import_drift(
                module_index,
                module,
                source_imports,
                &certificate,
                &direct_source_interfaces,
            ) {
                return Some(diagnostic);
            }
        }
        if let Some(diagnostic) = check_refreshed_certificate_import_identities(
            module_index,
            &module.module,
            &expected_imports,
            certificate.imports(),
        ) {
            return Some(diagnostic);
        }

        let certificate_file_hash = package_file_hash(&generated_bytes);
        let export_hash = PackageHash::from(certificate.hashes().export_hash);
        let axiom_report_hash = PackageHash::from(certificate.hashes().axiom_report_hash);
        let certificate_hash = PackageHash::from(certificate.hashes().certificate_hash);
        let (metadata_path, metadata_bytes) = if refresh_metadata {
            match refreshed_module_metadata(
                loaded,
                module_index,
                module,
                &verified,
                &source_interface,
                source_hash,
                certificate_file_hash,
                axiom_report_hash,
            ) {
                Ok(metadata) => metadata,
                Err(diagnostic) => return Some(*diagnostic),
            }
        } else {
            (None, None)
        };
        drop(source);
        let remaining_uses = import_use_counts
            .get(&module.module)
            .copied()
            .unwrap_or_default();
        let verified = Arc::new(verified);
        verified_modules_by_module.insert(module.module.clone(), Arc::clone(&verified));
        if remaining_uses > 0 {
            let imported_source_interface = HumanImportedSourceInterface {
                module: module.module.clone(),
                export_hash: certificate.hashes().export_hash,
                certificate_hash: Some(certificate.hashes().certificate_hash),
                source_interface,
            };
            available_modules.insert(
                module.module.clone(),
                RefreshAvailableModule {
                    verified,
                    source_interface: imported_source_interface,
                    remaining_uses,
                    origin: RefreshImportOrigin::Local,
                },
            );
        }
        if let Some(cache) = targeted_check_cache.as_deref_mut() {
            cache
                .certificates
                .push(PackageBuildCheckCertificateIdentity {
                    module_index,
                    source_hash,
                    output_certificate_format: certificate.header().format.clone(),
                    output_core_spec: certificate.header().core_spec.clone(),
                });
        }
        local_modules.push(LocalModuleRefreshIdentity {
            module_index,
            module: module.module.clone(),
            source_hash,
            source_imports,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
            certificate_path: module.certificate.clone(),
            certificate_bytes: generated_bytes,
            metadata_path,
            metadata_bytes,
        });
        if let Some(run) = targeted_authoring_run.as_deref_mut() {
            run.record_target_completion();
        }
    }
    None
}

fn read_targeted_authoring_local_snapshot(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
) -> Result<
    (
        TargetedAuthoringLocalModuleInput,
        TargetedAuthoringCurrentSnapshot,
    ),
    Box<CommandDiagnostic>,
> {
    let source = read_source(loaded, module_index, module)?;
    let current_source_hash = package_file_hash(source.as_bytes());
    if current_source_hash != module.expected_source_hash {
        return Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::HashMismatch,
                "selection_dependency_source_stale",
            )
            .with_module(module.module.as_dotted())
            .with_path(render_package_path(&module.source))
            .with_field(format!("modules[{module_index}].expected_source_hash"))
            .with_hashes(
                format_package_hash(&module.expected_source_hash),
                format_package_hash(&current_source_hash),
            ),
        ));
    }
    let certificate_bytes = read_certificate_bytes(
        loaded,
        &module.certificate,
        format!("modules[{module_index}].certificate"),
    )?;
    let certificate = npa_cert::decode_module_cert(&certificate_bytes).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_decode_failed")
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&module.certificate))
                .with_actual_value(format!("{error:?}")),
        )
    })?;
    let artifact = TargetedAuthoringLocalModuleInput {
        module: module.module.clone(),
        current_source_hash,
        current_certificate_file_hash: package_file_hash(&certificate_bytes),
        actual_export_hash: PackageHash::from(certificate.hashes().export_hash),
        actual_axiom_report_hash: PackageHash::from(certificate.hashes().axiom_report_hash),
        actual_certificate_hash: PackageHash::from(certificate.hashes().certificate_hash),
        certificate_imports: certificate
            .imports()
            .iter()
            .map(|import| TargetedAuthoringCertificateImportIdentity {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: import.certificate_hash.map(PackageHash::from),
            })
            .collect(),
    };
    Ok((
        artifact,
        TargetedAuthoringCurrentSnapshot::new(source, certificate_bytes),
    ))
}

fn targeted_authoring_local_input_from_accepted_certificate(
    module: &PackageModule,
    current_source_hash: PackageHash,
    certificate: &ModuleCert,
    certificate_bytes: &[u8],
) -> TargetedAuthoringLocalModuleInput {
    TargetedAuthoringLocalModuleInput {
        module: module.module.clone(),
        current_source_hash,
        current_certificate_file_hash: package_file_hash(certificate_bytes),
        actual_export_hash: PackageHash::from(certificate.hashes().export_hash),
        actual_axiom_report_hash: PackageHash::from(certificate.hashes().axiom_report_hash),
        actual_certificate_hash: PackageHash::from(certificate.hashes().certificate_hash),
        certificate_imports: certificate
            .imports()
            .iter()
            .map(|import| TargetedAuthoringCertificateImportIdentity {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: import.certificate_hash.map(PackageHash::from),
            })
            .collect(),
    }
}

#[allow(clippy::too_many_arguments)]
fn refreshed_module_metadata(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    verified: &VerifiedModule,
    source_interface: &HumanSourceInterface,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    axiom_report_hash: PackageHash,
) -> Result<RefreshedModuleMetadata, Box<CommandDiagnostic>> {
    let Some(metadata_path) = module.meta.clone() else {
        return Ok((None, None));
    };
    let producer_profile = module.producer_profile.clone().ok_or_else(|| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "module_metadata_refresh_failed",
            )
            .with_module(module.module.as_dotted())
            .with_path(render_package_path(&metadata_path))
            .with_field(format!("modules[{module_index}].producer_profile"))
            .with_expected_value("non-empty producer profile"),
        )
    })?;
    let declarations = refreshed_metadata_declarations(
        module_index,
        module,
        source_interface,
        verified,
        &metadata_path,
    )?;
    let axioms = verified
        .axiom_report()
        .module_axioms
        .iter()
        .map(|axiom| {
            verified
                .name_table()
                .get(axiom.name)
                .cloned()
                .ok_or_else(|| {
                    Box::new(
                        CommandDiagnostic::error(
                            DiagnosticKind::GeneratedArtifact,
                            "module_metadata_refresh_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(render_package_path(&metadata_path))
                        .with_actual_value("verified axiom name index out of range"),
                    )
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let input = PackageArtifactLedgerMetadataRefreshInput::new(
        module.module.clone(),
        module.source.clone(),
        module.certificate.clone(),
        producer_profile,
        source_hash,
        certificate_file_hash,
        PackageHash::from(verified.export_hash()),
        axiom_report_hash,
        PackageHash::from(verified.certificate_hash()),
        module.imports.clone(),
        axioms,
        declarations,
    );
    let existing = match read_package_regular_file_no_follow(&loaded.root, &metadata_path) {
        Ok(existing) => Some(String::from_utf8(existing).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "module_metadata_refresh_failed",
                )
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&metadata_path))
                .with_actual_value("metadata is not readable UTF-8"),
            )
        })?),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(_) => {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "module_metadata_refresh_failed",
                )
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&metadata_path))
                .with_actual_value("metadata is not readable UTF-8"),
            ));
        }
    };
    let rendered =
        refresh_package_artifact_ledger_metadata(existing.as_deref(), &input).map_err(|error| {
            let mut diagnostic = CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "module_metadata_refresh_failed",
            )
            .with_module(module.module.as_dotted())
            .with_path(render_package_path(&metadata_path))
            .with_actual_value(error.reason_code.as_str());
            if let Some(field) = error.field {
                diagnostic = diagnostic.with_field(field);
            }
            Box::new(diagnostic)
        })?;
    Ok((Some(metadata_path), Some(rendered.into_bytes())))
}

fn refreshed_metadata_declarations(
    module_index: usize,
    module: &PackageModule,
    source_interface: &HumanSourceInterface,
    verified: &VerifiedModule,
    metadata_path: &PackagePath,
) -> Result<Vec<PackageArtifactLedgerDeclaration>, Box<CommandDiagnostic>> {
    let mut declarations = Vec::new();
    for declaration in &source_interface.declarations {
        let kind = match declaration.kind {
            HumanSourceDeclarationKind::Axiom => PackageArtifactLedgerDeclarationKind::Axiom,
            HumanSourceDeclarationKind::Def => PackageArtifactLedgerDeclarationKind::Definition,
            HumanSourceDeclarationKind::Theorem => PackageArtifactLedgerDeclarationKind::Theorem,
            HumanSourceDeclarationKind::Inductive | HumanSourceDeclarationKind::Class => {
                PackageArtifactLedgerDeclarationKind::Inductive
            }
            HumanSourceDeclarationKind::Instance => {
                PackageArtifactLedgerDeclarationKind::Definition
            }
            HumanSourceDeclarationKind::ClassField | HumanSourceDeclarationKind::Imported => {
                continue;
            }
        };
        let name = Name::from_dotted(declaration.name.as_dotted());
        if verified_declaration_kind(verified, &name) != Some(kind) {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "module_metadata_refresh_failed",
                )
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(metadata_path))
                .with_field(format!("modules[{module_index}].meta.declarations"))
                .with_expected_value(format!("{}:{}", name.as_dotted(), kind.as_str()))
                .with_actual_value("verified declaration missing or incompatible"),
            ));
        }
        declarations.push(PackageArtifactLedgerDeclaration::new(name, kind));
    }
    Ok(declarations)
}

fn verified_declaration_kind(
    verified: &VerifiedModule,
    expected_name: &Name,
) -> Option<PackageArtifactLedgerDeclarationKind> {
    verified.declarations().iter().find_map(|declaration| {
        let (name_id, kind) = match &declaration.decl {
            npa_cert::DeclPayload::Axiom { name, .. }
            | npa_cert::DeclPayload::AxiomConstrained { name, .. } => {
                (*name, PackageArtifactLedgerDeclarationKind::Axiom)
            }
            npa_cert::DeclPayload::Def { name, .. }
            | npa_cert::DeclPayload::DefConstrained { name, .. } => {
                (*name, PackageArtifactLedgerDeclarationKind::Definition)
            }
            npa_cert::DeclPayload::Theorem { name, .. }
            | npa_cert::DeclPayload::TheoremConstrained { name, .. } => {
                (*name, PackageArtifactLedgerDeclarationKind::Theorem)
            }
            npa_cert::DeclPayload::Inductive { name, .. }
            | npa_cert::DeclPayload::InductiveConstrained { name, .. }
            | npa_cert::DeclPayload::MutualInductiveBlock { name, .. } => {
                (*name, PackageArtifactLedgerDeclarationKind::Inductive)
            }
        };
        (verified.name_table().get(name_id) == Some(expected_name)).then_some(kind)
    })
}

#[allow(clippy::too_many_arguments)]
fn build_local_modules(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    verified_modules_by_module: &mut BTreeMap<Name, Arc<VerifiedModule>>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    local_certificates: &mut Vec<LocalCertificateBuild>,
    observations: &mut PackageBuildObservationCoordinator,
) -> Option<CommandDiagnostic> {
    let compile_options = observations.compile_options();
    for &module_index in &loaded.validated.graph().topological_order {
        let module = &loaded.validated.manifest().modules[module_index];
        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                        .with_module(module.module.as_dotted()),
                );
            }
        };
        let (direct_verified_modules, direct_source_interfaces) =
            match take_direct_import_context(loaded, module_index, available_modules, false) {
                Ok(imports) => imports,
                Err(diagnostic) => return Some(*diagnostic),
            };
        let direct_verified_module_refs = direct_verified_modules
            .iter()
            .map(Arc::as_ref)
            .collect::<Vec<_>>();
        let available_verified_module_refs = available_verified_module_refs_for_direct_imports(
            &direct_verified_modules,
            verified_modules_by_module,
        );

        let (certificate, generated_bytes, verified, source_interface) =
            if is_std_core_builder_profile(module.producer_profile.as_deref()) {
                match build_std_core_builder_package_certificate(
                    module_index,
                    module,
                    &source,
                    &direct_verified_module_refs,
                    policy,
                    false,
                ) {
                    Ok((certificate, bytes, verified, interface, _)) => {
                        (certificate, bytes, verified, interface)
                    }
                    Err(diagnostic) => return Some(*diagnostic),
                }
            } else {
                let observed =
                match compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy(
                    file_id,
                    module.module.clone(),
                    &source,
                    &direct_verified_module_refs,
                    &available_verified_module_refs,
                    &direct_source_interfaces,
                    &compile_options,
                    policy,
                    observations.kernel_work_counter_sink(),
                    observations.collect_declaration_details(),
                ) {
                    Ok(output) => output,
                    Err(error) => {
                        return Some(frontend_build_failed(
                            module_index,
                            module,
                            file_id,
                            &source,
                            &direct_source_interfaces,
                            error,
                        ));
                    }
                };
                observations.record_declaration_batch(&module.module, observed.observations);
                let output = observed.output;
                let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        return Some(
                            CommandDiagnostic::error(
                                DiagnosticKind::Build,
                                "certificate_encode_failed",
                            )
                            .with_module(module.module.as_dotted())
                            .with_path(format!("modules[{module_index}].certificate"))
                            .with_actual_value(format!("{error:?}")),
                        );
                    }
                };
                (
                    output.certificate,
                    generated_bytes,
                    output.verified_module,
                    output.source_interface,
                )
            };

        if let Some(diagnostic) =
            check_generated_axiom_policy(loaded, module_index, module, &certificate)
        {
            return Some(diagnostic);
        }

        if let Some(source_imports) =
            human_source_imports(file_id, &source, &direct_source_interfaces)
        {
            if let Some(diagnostic) = check_observable_import_drift(
                module_index,
                module,
                &source_imports,
                &certificate,
                &direct_source_interfaces,
            ) {
                return Some(diagnostic);
            }
        }

        if verified.module() != &module.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_field("module")
                    .with_expected_value(module.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }

        let imported_source_interface = HumanImportedSourceInterface {
            module: module.module.clone(),
            export_hash: certificate.hashes().export_hash,
            certificate_hash: Some(certificate.hashes().certificate_hash),
            source_interface,
        };
        let remaining_uses = import_use_counts
            .get(&module.module)
            .copied()
            .unwrap_or_default();
        let verified = Arc::new(verified);
        verified_modules_by_module.insert(module.module.clone(), Arc::clone(&verified));
        if remaining_uses > 0 {
            available_modules.insert(
                module.module.clone(),
                AvailableModule {
                    verified,
                    source_interface: imported_source_interface,
                    remaining_uses,
                },
            );
        }
        local_certificates.push(LocalCertificateBuild {
            module_index,
            module: module.module.clone(),
            path: module.certificate.clone(),
            bytes: generated_bytes.clone(),
        });
        artifacts.push(CertificateArtifactBuffer {
            path: module.certificate.clone(),
            bytes: generated_bytes,
        });
    }
    None
}

fn check_local_certificate_file(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    generated_bytes: &[u8],
) -> Option<CommandDiagnostic> {
    let checked_in_bytes = match read_certificate_bytes(
        loaded,
        &module.certificate,
        format!("modules[{module_index}].certificate"),
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return Some(*diagnostic),
    };
    if checked_in_bytes != generated_bytes {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "build_certificate_changed")
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&module.certificate))
                .with_hashes(
                    format_package_hash(&package_file_hash(&checked_in_bytes)),
                    format_package_hash(&package_file_hash(generated_bytes)),
                ),
        );
    }
    None
}

fn package_lock_imports_for_certificate(
    imports: &[npa_cert::ImportEntry],
    path: &str,
    owner_module: &Name,
) -> Result<Vec<PackageLockImport>, Box<CommandDiagnostic>> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            let certificate_hash = import.certificate_hash.ok_or_else(|| {
                Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackageLock,
                        "import_certificate_hash_missing",
                    )
                    .with_module(owner_module.as_dotted())
                    .with_path(format!("{path}[{index}].certificate_hash")),
                )
            })?;
            Ok(PackageLockImport {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: PackageHash::from(certificate_hash),
            })
        })
        .collect()
}

fn package_lock_imports_for_source_interfaces(
    imports: &[HumanImportedSourceInterface],
    path: &str,
    owner_module: &Name,
) -> Result<Vec<PackageLockImport>, Box<CommandDiagnostic>> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            let certificate_hash = import.certificate_hash.ok_or_else(|| {
                Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::HashMismatch,
                        "refreshed_import_identity_mismatch",
                    )
                    .with_module(owner_module.as_dotted())
                    .with_path(format!("{path}[{index}].certificate_hash"))
                    .with_field("certificate_hash")
                    .with_expected_value("live import certificate hash")
                    .with_actual_value("<missing>"),
                )
            })?;
            Ok(PackageLockImport {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: PackageHash::from(certificate_hash),
            })
        })
        .collect()
}

fn take_refresh_direct_import_context(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
) -> Result<DirectImportContext, Box<CommandDiagnostic>> {
    let mut direct_verified_modules = Vec::new();
    let mut direct_source_interfaces = Vec::new();

    for (import_index, import) in loaded.validated.graph().resolved_module_imports[module_index]
        .iter()
        .enumerate()
    {
        let path = format!("modules[{module_index}].imports[{import_index}]");
        let is_last_use = {
            let Some(available) = available_modules.get_mut(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "import_identity_unavailable",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(path),
                ));
            };

            check_refresh_available_module_identity(import, available, &path)?;
            if available.remaining_uses <= 1 {
                true
            } else {
                available.remaining_uses -= 1;
                direct_verified_modules.push(Arc::clone(&available.verified));
                direct_source_interfaces.push(available.source_interface.clone());
                false
            }
        };

        if is_last_use {
            let Some(available) = available_modules.remove(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "import_identity_unavailable",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(path),
                ));
            };
            direct_verified_modules.push(available.verified);
            direct_source_interfaces.push(available.source_interface);
        }
    }

    Ok((direct_verified_modules, direct_source_interfaces))
}

fn check_refresh_available_module_identity(
    import: &npa_package::ResolvedModuleImport,
    available: &RefreshAvailableModule,
    path: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    match import.kind {
        ResolvedModuleImportKind::External { .. } => {
            if available.origin != RefreshImportOrigin::External {
                return Err(Box::new(refresh_import_origin_mismatch(
                    path,
                    &import.module,
                    "external",
                    available.origin,
                )));
            }
            let actual_export_hash = PackageHash::from(available.verified.export_hash());
            if actual_export_hash != import.export_hash {
                return Err(Box::new(hash_mismatch(
                    "export_hash_mismatch",
                    format!("{path}.export_hash"),
                    "export_hash",
                    import.export_hash,
                    actual_export_hash,
                )));
            }
            let actual_certificate_hash = PackageHash::from(available.verified.certificate_hash());
            if actual_certificate_hash != import.certificate_hash {
                return Err(Box::new(hash_mismatch(
                    "certificate_hash_mismatch",
                    format!("{path}.certificate_hash"),
                    "certificate_hash",
                    import.certificate_hash,
                    actual_certificate_hash,
                )));
            }
        }
        ResolvedModuleImportKind::Local { .. } => {
            if available.origin != RefreshImportOrigin::Local {
                return Err(Box::new(refresh_import_origin_mismatch(
                    path,
                    &import.module,
                    "local",
                    available.origin,
                )));
            }
            let verified_export_hash = PackageHash::from(available.verified.export_hash());
            let interface_export_hash = PackageHash::from(available.source_interface.export_hash);
            if verified_export_hash != interface_export_hash {
                return Err(Box::new(refreshed_import_identity_hash_mismatch(
                    format!("{path}.export_hash"),
                    "export_hash",
                    verified_export_hash,
                    interface_export_hash,
                )));
            }
            let Some(interface_certificate_hash) = available.source_interface.certificate_hash
            else {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::HashMismatch,
                        "refreshed_import_identity_mismatch",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(format!("{path}.certificate_hash"))
                    .with_field("certificate_hash")
                    .with_expected_value("live verified certificate hash")
                    .with_actual_value("<missing>"),
                ));
            };
            let verified_certificate_hash =
                PackageHash::from(available.verified.certificate_hash());
            let interface_certificate_hash = PackageHash::from(interface_certificate_hash);
            if verified_certificate_hash != interface_certificate_hash {
                return Err(Box::new(refreshed_import_identity_hash_mismatch(
                    format!("{path}.certificate_hash"),
                    "certificate_hash",
                    verified_certificate_hash,
                    interface_certificate_hash,
                )));
            }
        }
    }
    Ok(())
}

fn check_refreshed_certificate_import_identities(
    module_index: usize,
    module: &Name,
    expected: &[PackageLockImport],
    actual: &[npa_cert::ImportEntry],
) -> Option<CommandDiagnostic> {
    let mut expected_by_module: BTreeMap<Name, (usize, &PackageLockImport)> = BTreeMap::new();
    for (import_index, expected) in expected.iter().enumerate() {
        if let Some((_, existing)) = expected_by_module.get(&expected.module).copied() {
            if existing.export_hash != expected.export_hash {
                return Some(refreshed_import_identity_hash_mismatch(
                    format!("modules[{module_index}].imports[{import_index}].export_hash"),
                    "export_hash",
                    existing.export_hash,
                    expected.export_hash,
                ));
            }
            if existing.certificate_hash != expected.certificate_hash {
                return Some(refreshed_import_identity_hash_mismatch(
                    format!("modules[{module_index}].imports[{import_index}].certificate_hash"),
                    "certificate_hash",
                    existing.certificate_hash,
                    expected.certificate_hash,
                ));
            }
            continue;
        }
        expected_by_module.insert(expected.module.clone(), (import_index, expected));
    }

    let mut actual_by_module = BTreeMap::new();
    for (import_index, actual) in actual.iter().enumerate() {
        if actual_by_module
            .insert(actual.module.clone(), (import_index, actual))
            .is_some()
        {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "refreshed_import_identity_mismatch",
                )
                .with_module(module.as_dotted())
                .with_path(format!(
                    "modules[{module_index}].certificate.imports[{import_index}].module"
                ))
                .with_field("module")
                .with_expected_value("unique import module")
                .with_actual_value(actual.module.as_dotted()),
            );
        }
    }

    for (expected_import_index, expected) in expected_by_module.values().copied() {
        let Some((actual_import_index, actual)) = actual_by_module.get(&expected.module).copied()
        else {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "refreshed_import_identity_mismatch",
                )
                .with_module(module.as_dotted())
                .with_path(format!(
                    "modules[{module_index}].certificate.imports[{expected_import_index}].module"
                ))
                .with_field("module")
                .with_expected_value(expected.module.as_dotted())
                .with_actual_value("<missing>"),
            );
        };
        let path = format!("modules[{module_index}].certificate.imports[{actual_import_index}]");
        let actual_export_hash = PackageHash::from(actual.export_hash);
        if expected.export_hash != actual_export_hash {
            return Some(refreshed_import_identity_hash_mismatch(
                format!("{path}.export_hash"),
                "export_hash",
                expected.export_hash,
                actual_export_hash,
            ));
        }
        let Some(actual_certificate_hash) = actual.certificate_hash else {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "refreshed_import_identity_mismatch",
                )
                .with_module(module.as_dotted())
                .with_path(format!("{path}.certificate_hash"))
                .with_field("certificate_hash")
                .with_expected_value(format_package_hash(&expected.certificate_hash))
                .with_actual_value("<missing>"),
            );
        };
        let actual_certificate_hash = PackageHash::from(actual_certificate_hash);
        if expected.certificate_hash != actual_certificate_hash {
            return Some(refreshed_import_identity_hash_mismatch(
                format!("{path}.certificate_hash"),
                "certificate_hash",
                expected.certificate_hash,
                actual_certificate_hash,
            ));
        }
    }

    None
}

fn refreshed_import_identity_hash_mismatch(
    path: String,
    field: &'static str,
    expected: PackageHash,
    actual: PackageHash,
) -> CommandDiagnostic {
    hash_mismatch(
        "refreshed_import_identity_mismatch",
        path,
        field,
        expected,
        actual,
    )
}

fn refresh_import_origin_mismatch(
    path: &str,
    module: &Name,
    expected_origin: &'static str,
    actual_origin: RefreshImportOrigin,
) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::HashMismatch,
        "refreshed_import_identity_mismatch",
    )
    .with_module(module.as_dotted())
    .with_path(format!("{path}.origin"))
    .with_field("origin")
    .with_expected_value(expected_origin)
    .with_actual_value(actual_origin.as_str())
}

impl RefreshImportOrigin {
    fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::External => "external",
        }
    }
}

fn take_direct_import_context(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    check_hashes: bool,
) -> Result<DirectImportContext, Box<CommandDiagnostic>> {
    let mut direct_verified_modules = Vec::new();
    let mut direct_source_interfaces = Vec::new();

    for (import_index, import) in loaded.validated.graph().resolved_module_imports[module_index]
        .iter()
        .enumerate()
    {
        let path = format!("modules[{module_index}].imports[{import_index}]");
        let is_last_use = {
            let Some(available) = available_modules.get_mut(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "import_not_built")
                        .with_module(import.module.as_dotted())
                        .with_path(path),
                ));
            };

            if check_hashes {
                let actual_export_hash = PackageHash::from(available.verified.export_hash());
                if actual_export_hash != import.export_hash {
                    return Err(Box::new(hash_mismatch(
                        "export_hash_mismatch",
                        format!("{path}.export_hash"),
                        "export_hash",
                        import.export_hash,
                        actual_export_hash,
                    )));
                }
                let actual_certificate_hash =
                    PackageHash::from(available.verified.certificate_hash());
                if actual_certificate_hash != import.certificate_hash {
                    return Err(Box::new(hash_mismatch(
                        "certificate_hash_mismatch",
                        format!("{path}.certificate_hash"),
                        "certificate_hash",
                        import.certificate_hash,
                        actual_certificate_hash,
                    )));
                }
            }

            if available.remaining_uses <= 1 {
                true
            } else {
                available.remaining_uses -= 1;
                direct_verified_modules.push(Arc::clone(&available.verified));
                direct_source_interfaces.push(available.source_interface.clone());
                false
            }
        };

        if is_last_use {
            let Some(available) = available_modules.remove(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "import_not_built")
                        .with_module(import.module.as_dotted())
                        .with_path(path),
                ));
            };
            direct_verified_modules.push(available.verified);
            direct_source_interfaces.push(available.source_interface);
        }
    }

    Ok((direct_verified_modules, direct_source_interfaces))
}

type StdCoreBuilderPackageCertificateBuild = (
    ModuleCert,
    Vec<u8>,
    VerifiedModule,
    HumanSourceInterface,
    u64,
);

fn build_std_core_builder_package_certificate(
    module_index: usize,
    module: &PackageModule,
    source: &str,
    direct_verified_modules: &[&VerifiedModule],
    policy: &AxiomPolicy,
    observe_verification: bool,
) -> Result<StdCoreBuilderPackageCertificateBuild, Box<CommandDiagnostic>> {
    validate_std_core_builder_source_skeleton(module_index, module, source)?;
    let direct_verified_module_values = direct_verified_modules
        .iter()
        .map(|module| (*module).clone())
        .collect::<Vec<_>>();
    let certificate =
        match build_std_package_module_cert(&module.module, &direct_verified_module_values) {
            Some(Ok(certificate)) => certificate,
            Some(Err(error)) => {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Build, "certificate_build_failed")
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_actual_value(format!("{error:?}")),
                ));
            }
            None => {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::Build,
                        "unsupported_std_core_builder_module",
                    )
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].module"))
                    .with_field("module")
                    .with_expected_value("Std.Logic.Eq|Std.Nat.Basic")
                    .with_actual_value(module.module.as_dotted()),
                ));
            }
        };
    let verification_started = observe_verification.then(Instant::now);
    let verified = npa_cert::verify_built_module_cert_with_import_refs(
        &certificate,
        direct_verified_modules,
        policy,
    )
    .map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_rejected")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_actual_value(format!("{error:?}")),
        )
    })?;
    let verification_elapsed_ns = verification_started.map_or(0, |started| {
        u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
    });
    let generated_bytes = npa_cert::encode_module_cert(&certificate).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_encode_failed")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_actual_value(format!("{error:?}")),
        )
    })?;
    let source_interface = fallback_imported_source_interface(&verified).source_interface;
    Ok((
        certificate,
        generated_bytes,
        verified,
        source_interface,
        verification_elapsed_ns,
    ))
}

fn validate_std_core_builder_source_skeleton(
    module_index: usize,
    module: &PackageModule,
    source: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    let actual_imports = std_core_builder_source_skeleton_imports(module_index, module, source)?;
    if actual_imports != module.imports {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "source_imports_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].source"))
                .with_field("imports")
                .with_expected_value(format!("{:?}", module.imports))
                .with_actual_value(format!("{actual_imports:?}")),
        ));
    }
    Ok(())
}

fn std_core_builder_source_skeleton_imports(
    module_index: usize,
    module: &PackageModule,
    source: &str,
) -> Result<Vec<Name>, Box<CommandDiagnostic>> {
    let file_id = match u32::try_from(module_index) {
        Ok(index) => FileId(index),
        Err(_) => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                    .with_module(module.module.as_dotted()),
            ));
        }
    };
    let parsed = parse_human_module(file_id, source).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "source_skeleton_parse_failed")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].source"))
                .with_field("source_skeleton")
                .with_actual_value(error.message),
        )
    })?;
    let mut actual_imports = Vec::new();
    for item in parsed.items {
        match item {
            HumanItem::Import { module, .. } => {
                actual_imports.push(Name::from_dotted(module.as_dotted()));
            }
            other => {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Build, "source_skeleton_has_items")
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].source"))
                        .with_field("source_skeleton")
                        .with_expected_value("imports and comments only")
                        .with_actual_value(format!("{:?}", other.span())),
                ));
            }
        }
    }
    Ok(actual_imports)
}

fn read_source(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
) -> Result<String, Box<CommandDiagnostic>> {
    let _ = module_index;
    read_package_regular_file_no_follow(&loaded.root, &module.source)
        .and_then(|bytes| String::from_utf8(bytes).map_err(io::Error::other))
        .map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "source_missing")
                    .with_module(module.module.as_dotted())
                    .with_path(render_package_path(&module.source)),
            )
        })
}

fn preflight_human_sources(
    loaded: &LoadedPackageRoot,
    module_order: &[usize],
) -> Result<(), Box<CommandDiagnostic>> {
    let modules = &loaded.validated.manifest().modules;
    for &module_index in module_order {
        let module = modules
            .get(module_index)
            .ok_or_else(|| targeted_refresh_plan_invalid("local_index_out_of_range"))?;
        let source = read_source(loaded, module_index, module)?;
        let file_id = u32::try_from(module_index).map(FileId).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                    .with_module(module.module.as_dotted()),
            )
        })?;
        validate_human_source_lexical_structure(file_id, &source).map_err(|error| {
            Box::new(frontend_preflight_failed(
                module_index,
                module,
                file_id,
                &source,
                error,
            ))
        })?;
    }
    Ok(())
}

fn read_certificate_bytes(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
    manifest_field_path: impl Into<String>,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let _ = manifest_field_path.into();
    observe_certificate_read_for_test(path);
    read_package_regular_file_no_follow(&loaded.root, path).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                .with_path(render_package_path(path)),
        )
    })
}

fn read_certificate_bytes_for_external_dependency_discovery(
    loaded: &LoadedPackageRoot,
    import: &PackageExternalImport,
    index: usize,
    remaining_bytes: usize,
    total_limit: usize,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    observe_certificate_read_for_test(&import.certificate);
    let file =
        open_package_regular_file_no_follow(&loaded.root, &import.certificate).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                    .with_path(render_package_path(&import.certificate)),
            )
        })?;
    let bytes = read_bytes_through_limit(file, remaining_bytes).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                .with_path(render_package_path(&import.certificate)),
        )
    })?;
    if bytes.len() > remaining_bytes {
        return Err(Box::new(external_import_closure_limit_exceeded(
            Some(&import.module),
            Some(index),
            "certificate_bytes",
            total_limit,
            total_limit.saturating_add(1),
        )));
    }
    Ok(bytes)
}

fn read_bytes_through_limit(reader: impl io::Read, remaining_bytes: usize) -> io::Result<Vec<u8>> {
    let read_limit = u64::try_from(remaining_bytes.saturating_add(1)).unwrap_or(u64::MAX);
    let mut bytes = Vec::new();
    reader.take(read_limit).read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn check_generated_axiom_policy(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    certificate: &ModuleCert,
) -> Option<CommandDiagnostic> {
    let package_policy = &loaded.validated.manifest().policy;
    if package_policy.allow_custom_axioms {
        return None;
    }

    let allowed_axioms = package_policy
        .allowed_axioms
        .iter()
        .collect::<BTreeSet<&Name>>();
    for axiom in &certificate.axiom_report().module_axioms {
        let Some(name) = certificate.name_table().get(axiom.name) else {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_axiom_name_missing")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate")),
            );
        };
        if name.as_dotted().contains("sorry") || !allowed_axioms.contains(name) {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "disallowed_axiom")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].axioms"))
                    .with_field("axioms")
                    .with_expected_value("allowed axiom or allow_custom_axioms = true")
                    .with_actual_value(name.as_dotted()),
            );
        }
    }
    None
}

fn check_generated_manifest_hashes(
    module_index: usize,
    module: &PackageModule,
    certificate: &ModuleCert,
    certificate_bytes: &[u8],
) -> Option<CommandDiagnostic> {
    let actual_file_hash = package_file_hash(certificate_bytes);
    if actual_file_hash != module.expected_certificate_file_hash {
        return Some(hash_mismatch(
            "certificate_file_hash_mismatch",
            format!("modules[{module_index}].expected_certificate_file_hash"),
            "expected_certificate_file_hash",
            module.expected_certificate_file_hash,
            actual_file_hash,
        ));
    }

    let actual_export_hash = PackageHash::from(certificate.hashes().export_hash);
    if actual_export_hash != module.expected_export_hash {
        return Some(hash_mismatch(
            "export_hash_mismatch",
            format!("modules[{module_index}].expected_export_hash"),
            "expected_export_hash",
            module.expected_export_hash,
            actual_export_hash,
        ));
    }

    let actual_axiom_report_hash = PackageHash::from(certificate.hashes().axiom_report_hash);
    if actual_axiom_report_hash != module.expected_axiom_report_hash {
        return Some(hash_mismatch(
            "axiom_report_hash_mismatch",
            format!("modules[{module_index}].expected_axiom_report_hash"),
            "expected_axiom_report_hash",
            module.expected_axiom_report_hash,
            actual_axiom_report_hash,
        ));
    }

    let actual_certificate_hash = PackageHash::from(certificate.hashes().certificate_hash);
    if actual_certificate_hash != module.expected_certificate_hash {
        return Some(hash_mismatch(
            "certificate_hash_mismatch",
            format!("modules[{module_index}].expected_certificate_hash"),
            "expected_certificate_hash",
            module.expected_certificate_hash,
            actual_certificate_hash,
        ));
    }

    None
}

fn human_source_imports(
    file_id: FileId,
    source: &str,
    direct_source_interfaces: &[HumanImportedSourceInterface],
) -> Option<Vec<Name>> {
    let parsed =
        parse_human_module_with_source_interfaces(file_id, source, direct_source_interfaces)
            .ok()?;
    Some(
        parsed
            .items
            .iter()
            .filter_map(|item| match item {
                HumanItem::Import { module, .. } => Some(Name::from_dotted(module.as_dotted())),
                _ => None,
            })
            .collect(),
    )
}

fn check_observable_import_drift(
    module_index: usize,
    module: &PackageModule,
    source_imports: &[Name],
    certificate: &ModuleCert,
    direct_source_interfaces: &[HumanImportedSourceInterface],
) -> Option<CommandDiagnostic> {
    let certificate_imports = certificate
        .imports()
        .iter()
        .map(|import| import.module.clone())
        .collect::<Vec<_>>();
    let manifest_set = module.imports.iter().cloned().collect::<BTreeSet<_>>();
    let source_set = source_imports.iter().cloned().collect::<BTreeSet<_>>();
    if manifest_set != source_set {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "manifest_source_imports_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].imports"))
                .with_field("imports")
                .with_expected_value(format!("manifest=[{}]", dotted_name_list(&module.imports)))
                .with_actual_value(format!("source=[{}]", dotted_name_list(source_imports))),
        );
    }
    let certificate_set = certificate_imports.iter().cloned().collect::<BTreeSet<_>>();
    if !manifest_set.is_subset(&certificate_set) {
        return Some(
            CommandDiagnostic::error(
                DiagnosticKind::HashMismatch,
                "manifest_certificate_imports_mismatch",
            )
            .with_module(module.module.as_dotted())
            .with_path(format!("modules[{module_index}].imports"))
            .with_field("imports")
            .with_expected_value(format!("manifest=[{}]", dotted_name_list(&module.imports)))
            .with_actual_value(format!(
                "certificate=[{}]",
                dotted_name_list(&certificate_imports)
            )),
        );
    }
    let certificate_by_module = certificate
        .imports()
        .iter()
        .map(|import| (&import.module, import))
        .collect::<BTreeMap<_, _>>();
    let expected_by_module = direct_source_interfaces
        .iter()
        .map(|interface| (&interface.module, interface))
        .collect::<BTreeMap<_, _>>();
    for (import_index, import_module) in module.imports.iter().enumerate() {
        let Some(expected) = expected_by_module.get(import_module) else {
            continue;
        };
        let Some(actual) = certificate_by_module.get(import_module) else {
            continue;
        };
        let actual_export = PackageHash::from(actual.export_hash);
        let expected_export = PackageHash::from(expected.export_hash);
        if actual_export != expected_export {
            return Some(
                hash_mismatch(
                    "certificate_import_identity_mismatch",
                    format!("modules[{module_index}].imports[{import_index}]"),
                    "export_hash",
                    expected_export,
                    actual_export,
                )
                .with_module(module.module.as_dotted()),
            );
        }
        if let (Some(expected_certificate), Some(actual_certificate)) =
            (expected.certificate_hash, actual.certificate_hash)
        {
            let expected_certificate = PackageHash::from(expected_certificate);
            let actual_certificate = PackageHash::from(actual_certificate);
            if actual_certificate != expected_certificate {
                return Some(
                    hash_mismatch(
                        "certificate_import_identity_mismatch",
                        format!("modules[{module_index}].imports[{import_index}]"),
                        "certificate_hash",
                        expected_certificate,
                        actual_certificate,
                    )
                    .with_module(module.module.as_dotted()),
                );
            }
        }
    }
    None
}

fn check_existing_certificate_import_drift(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    source_imports: &[Name],
) -> Option<CommandDiagnostic> {
    let bytes = read_certificate_bytes(
        loaded,
        &module.certificate,
        format!("modules[{module_index}].certificate"),
    )
    .ok()?;
    let certificate = npa_cert::decode_module_cert(&bytes).ok()?;
    let certificate_imports = certificate
        .imports()
        .iter()
        .map(|import| import.module.clone())
        .collect::<Vec<_>>();
    let manifest_set = module.imports.iter().cloned().collect::<BTreeSet<_>>();
    let source_set = source_imports.iter().cloned().collect::<BTreeSet<_>>();
    if manifest_set != source_set {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "manifest_source_imports_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].imports"))
                .with_field("imports")
                .with_expected_value(format!("manifest=[{}]", dotted_name_list(&module.imports)))
                .with_actual_value(format!("source=[{}]", dotted_name_list(source_imports))),
        );
    }
    let certificate_set = certificate_imports.iter().cloned().collect::<BTreeSet<_>>();
    if !manifest_set.is_subset(&certificate_set) {
        return Some(
            CommandDiagnostic::error(
                DiagnosticKind::HashMismatch,
                "manifest_certificate_imports_mismatch",
            )
            .with_module(module.module.as_dotted())
            .with_path(format!("modules[{module_index}].imports"))
            .with_field("imports")
            .with_expected_value(format!("manifest=[{}]", dotted_name_list(&module.imports)))
            .with_actual_value(format!(
                "certificate=[{}]",
                dotted_name_list(&certificate_imports)
            )),
        );
    }
    let certificate_by_module = certificate
        .imports()
        .iter()
        .map(|import| (&import.module, import))
        .collect::<BTreeMap<_, _>>();
    for (import_index, expected) in loaded.validated.graph().resolved_module_imports[module_index]
        .iter()
        .enumerate()
    {
        let Some(actual) = certificate_by_module.get(&expected.module) else {
            continue;
        };
        let actual_export = PackageHash::from(actual.export_hash);
        if actual_export != expected.export_hash {
            return Some(
                hash_mismatch(
                    "certificate_import_identity_mismatch",
                    format!("modules[{module_index}].imports[{import_index}]"),
                    "export_hash",
                    expected.export_hash,
                    actual_export,
                )
                .with_module(module.module.as_dotted()),
            );
        }
        if let Some(actual_certificate) = actual.certificate_hash {
            let actual_certificate = PackageHash::from(actual_certificate);
            if actual_certificate != expected.certificate_hash {
                return Some(
                    hash_mismatch(
                        "certificate_import_identity_mismatch",
                        format!("modules[{module_index}].imports[{import_index}]"),
                        "certificate_hash",
                        expected.certificate_hash,
                        actual_certificate,
                    )
                    .with_module(module.module.as_dotted()),
                );
            }
        }
    }
    None
}

fn dotted_name_list(names: &[Name]) -> String {
    names
        .iter()
        .map(Name::as_dotted)
        .collect::<Vec<_>>()
        .join(",")
}

fn check_generated_source_hash(
    module_index: usize,
    module: &PackageModule,
    source_hash: PackageHash,
) -> Option<CommandDiagnostic> {
    if source_hash != module.expected_source_hash {
        return Some(hash_mismatch(
            "source_hash_mismatch",
            format!("modules[{module_index}].expected_source_hash"),
            "expected_source_hash",
            module.expected_source_hash,
            source_hash,
        ));
    }
    None
}

fn check_package_lock(
    loaded: &LoadedPackageRoot,
    regenerated_lock_json: &str,
) -> Option<CommandDiagnostic> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let lock_source = match read_package_regular_file_no_follow(&loaded.root, &lock_path)
        .and_then(|bytes| String::from_utf8(bytes).map_err(io::Error::other))
    {
        Ok(source) => source,
        Err(_) => {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::PackageLock, "package_lock_missing")
                    .with_path(PACKAGE_LOCK_PATH),
            );
        }
    };
    if let Err(error) = parse_package_lock_json(&lock_source) {
        return Some(
            CommandDiagnostic::from_package_lock_error(&error).with_path(PACKAGE_LOCK_PATH),
        );
    }
    if lock_source != regenerated_lock_json {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "package_lock_stale")
                .with_path(PACKAGE_LOCK_PATH)
                .with_hashes(
                    format_package_hash(&package_file_hash(regenerated_lock_json.as_bytes())),
                    format_package_hash(&package_file_hash(lock_source.as_bytes())),
                ),
        );
    }
    None
}

fn build_check_result_with_optional_cache(
    root_display: String,
    cache_run: Option<PackageBuildCheckCacheRun>,
    diagnostic: Option<CommandDiagnostic>,
    cache_unavailable_diagnostic: Option<CommandDiagnostic>,
    observations: &mut PackageBuildObservationCoordinator,
) -> CommandResult {
    let status = if diagnostic.is_some() {
        PackageBuildCheckCachedStatus::Rejected
    } else {
        PackageBuildCheckCachedStatus::Accepted
    };
    let reason = diagnostic
        .as_ref()
        .map(|diagnostic| diagnostic.reason_code.clone());

    let mut diagnostics = Vec::new();
    if let Some(diagnostic) = diagnostic {
        diagnostics.push(diagnostic);
    }
    if let Some(unavailable) = cache_unavailable_diagnostic {
        diagnostics.push(unavailable);
    }
    if let Some(run) = cache_run {
        if let Some(unavailable) = run.unavailable_diagnostic() {
            diagnostics.push(unavailable);
        }
        let (summary, outcomes) =
            finalize_package_build_check_cache_run(run, status, reason.as_deref());
        observations.record_cache_entry_bytes(outcomes.bytes_loaded, outcomes.bytes_written);
        diagnostics.push(summary);
    }

    if status == PackageBuildCheckCachedStatus::Rejected {
        CommandResult::failed(COMMAND, root_display, diagnostics)
    } else {
        let mut result = CommandResult::passed(COMMAND, root_display);
        result.diagnostics = diagnostics;
        result
    }
}

fn write_package_build(
    loaded: &LoadedPackageRoot,
    build: &PackageCertificateBuild,
) -> Option<CommandDiagnostic> {
    let mutation_lock = match TargetLock::acquire(&loaded.root) {
        Ok(lock) => lock,
        Err(_) => {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::ArtifactIo,
                    "package_build_concurrent_update",
                )
                .with_path(PACKAGE_MANIFEST_PATH),
            )
        }
    };
    let mut pending = Vec::new();
    for certificate in &build.local_certificates {
        match prepare_pending_write(
            &mutation_lock,
            &loaded.root,
            &certificate.path,
            format!("modules[{}].certificate", certificate.module_index),
            &certificate.bytes,
            "certificate_write_failed",
            Some(certificate.module.clone()),
        ) {
            Ok(Some(write)) => pending.push(write),
            Ok(None) => {}
            Err(diagnostic) => {
                cleanup_pending_writes(&mutation_lock, &pending);
                return Some(*diagnostic);
            }
        }
    }

    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    match prepare_pending_write(
        &mutation_lock,
        &loaded.root,
        &lock_path,
        "package_lock.path",
        build.package_lock_json.as_bytes(),
        "package_lock_write_failed",
        None,
    ) {
        Ok(Some(write)) => pending.push(write),
        Ok(None) => {}
        Err(diagnostic) => {
            cleanup_pending_writes(&mutation_lock, &pending);
            return Some(*diagnostic);
        }
    }

    commit_pending_writes(&mutation_lock, &pending)
}

fn write_refreshed_package_build(
    loaded: &LoadedPackageRoot,
    build: &PackageCertificateRefreshBuild,
) -> Option<CommandDiagnostic> {
    let mutation_lock = match TargetLock::acquire(&loaded.root) {
        Ok(lock) => lock,
        Err(_) => {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::ArtifactIo,
                    "package_build_concurrent_update",
                )
                .with_path(PACKAGE_MANIFEST_PATH),
            )
        }
    };
    let mut pending = Vec::new();
    let local_modules = match refresh_modules_by_manifest_order(
        &build.local_modules,
        loaded.validated.manifest().modules.len(),
    ) {
        Ok(local_modules) => local_modules,
        Err(diagnostic) => return Some(*diagnostic),
    };

    for module in local_modules {
        match prepare_pending_write(
            &mutation_lock,
            &loaded.root,
            &module.certificate_path,
            format!("modules[{}].certificate", module.module_index),
            &module.certificate_bytes,
            "certificate_write_failed",
            Some(module.module.clone()),
        ) {
            Ok(Some(write)) => pending.push(write),
            Ok(None) => {}
            Err(diagnostic) => {
                cleanup_pending_writes(&mutation_lock, &pending);
                return Some(*diagnostic);
            }
        }
    }

    let manifest_path = PackagePath::new(PACKAGE_MANIFEST_PATH);
    match prepare_pending_write(
        &mutation_lock,
        &loaded.root,
        &manifest_path,
        "$.manifest",
        build.refreshed_manifest_source.as_bytes(),
        "manifest_write_failed",
        None,
    ) {
        Ok(Some(write)) => pending.push(write),
        Ok(None) => {}
        Err(diagnostic) => {
            cleanup_pending_writes(&mutation_lock, &pending);
            return Some(*diagnostic);
        }
    }

    let local_modules = match refresh_modules_by_manifest_order(
        &build.local_modules,
        loaded.validated.manifest().modules.len(),
    ) {
        Ok(local_modules) => local_modules,
        Err(diagnostic) => {
            cleanup_pending_writes(&mutation_lock, &pending);
            return Some(*diagnostic);
        }
    };
    for module in local_modules {
        let (Some(metadata_path), Some(metadata_bytes)) =
            (&module.metadata_path, &module.metadata_bytes)
        else {
            continue;
        };
        match prepare_pending_write(
            &mutation_lock,
            &loaded.root,
            metadata_path,
            format!("modules[{}].meta", module.module_index),
            metadata_bytes,
            "module_metadata_write_failed",
            Some(module.module.clone()),
        ) {
            Ok(Some(write)) => pending.push(write),
            Ok(None) => {}
            Err(diagnostic) => {
                cleanup_pending_writes(&mutation_lock, &pending);
                return Some(*diagnostic);
            }
        }
    }

    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    match prepare_pending_write(
        &mutation_lock,
        &loaded.root,
        &lock_path,
        "package_lock.path",
        build.package_lock_json.as_bytes(),
        "package_lock_write_failed",
        None,
    ) {
        Ok(Some(write)) => pending.push(write),
        Ok(None) => {}
        Err(diagnostic) => {
            cleanup_pending_writes(&mutation_lock, &pending);
            return Some(*diagnostic);
        }
    }

    commit_pending_writes(&mutation_lock, &pending)
}

fn prepare_pending_write(
    mutation_lock: &TargetLock,
    root: &Path,
    package_path: &PackagePath,
    manifest_field_path: impl Into<String>,
    bytes: &[u8],
    reason_code: &'static str,
    module: Option<Name>,
) -> Result<Option<PendingWrite>, Box<CommandDiagnostic>> {
    // Retain the exact parent directory capability for the transaction's
    // complete lifetime. Commit, rollback, and cleanup never re-resolve it.
    let _ = manifest_field_path.into();
    let (directory, leaf) =
        open_package_parent_no_follow(root, package_path, true).map_err(|_| {
            Box::new(write_artifact_diagnostic(
                reason_code,
                package_path,
                module.as_ref(),
            ))
        })?;
    let previous_bytes = match read_directory_entry(&directory, &leaf) {
        Ok(Some(existing)) if existing == bytes => return Ok(None),
        Ok(existing) => existing,
        Err(_) => {
            return Err(Box::new(write_artifact_diagnostic(
                reason_code,
                package_path,
                module.as_ref(),
            )));
        }
    };

    let (temp, temp_identity) =
        match write_unique_temporary_file(mutation_lock, &directory, &leaf, bytes) {
            Ok(value) => value,
            Err(_) => {
                return Err(Box::new(write_artifact_diagnostic(
                    reason_code,
                    package_path,
                    module.as_ref(),
                )));
            }
        };
    Ok(Some(PendingWrite {
        path: package_path.clone(),
        directory,
        leaf,
        temp,
        temp_identity,
        reason_code,
        module,
        previous_bytes,
        replacement_bytes: bytes.to_vec(),
    }))
}

fn commit_pending_writes(
    mutation_lock: &TargetLock,
    pending: &[PendingWrite],
) -> Option<CommandDiagnostic> {
    let mut committed = Vec::new();
    for write in pending {
        let unchanged = mutation_lock.ensure_target_identity().is_ok()
            && read_directory_entry(&write.directory, &write.leaf)
                .map(|current| current == write.previous_bytes)
                .unwrap_or(false);
        if !unchanged
            || mutation_lock
                .replace_file_under_lock(&write.directory, &write.temp, &write.leaf)
                .and_then(|_| write.directory.sync_all())
                .and_then(|_| mutation_lock.ensure_target_identity())
                .and_then(|_| {
                    if read_directory_entry(&write.directory, &write.leaf)?.as_deref()
                        == Some(write.replacement_bytes.as_slice())
                    {
                        Ok(())
                    } else {
                        Err(io::Error::other(
                            "package build destination bytes changed after publication",
                        ))
                    }
                })
                .is_err()
        {
            cleanup_pending_writes(mutation_lock, pending);
            if let Some(diagnostic) = rollback_pending_writes(mutation_lock, &committed) {
                return Some(diagnostic);
            }
            return Some(write_artifact_diagnostic(
                write.reason_code,
                &write.path,
                write.module.as_ref(),
            ));
        }
        committed.push(write);
    }
    None
}

fn cleanup_pending_writes(mutation_lock: &TargetLock, pending: &[PendingWrite]) {
    for write in pending {
        let Ok(Some(file)) = write.directory.open_regular_file(&write.temp) else {
            continue;
        };
        let Ok(identity) = regular_file_identity(&file) else {
            continue;
        };
        if identity == write.temp_identity {
            let _ = mutation_lock.remove_regular_file_under_lock(
                &write.directory,
                &write.temp,
                identity,
            );
        }
    }
}

fn rollback_pending_writes(
    mutation_lock: &TargetLock,
    committed: &[&PendingWrite],
) -> Option<CommandDiagnostic> {
    for write in committed.iter().rev() {
        if mutation_lock.ensure_target_identity().is_err()
            || read_directory_entry(&write.directory, &write.leaf)
                .ok()
                .flatten()
                .as_deref()
                != Some(write.replacement_bytes.as_slice())
        {
            return Some(rollback_diagnostic(write));
        }
        let restored = match &write.previous_bytes {
            Some(bytes) => {
                write_unique_temporary_file(mutation_lock, &write.directory, &write.leaf, bytes)
                    .and_then(|(temporary, temporary_identity)| {
                        let result = mutation_lock.replace_file_under_lock(
                            &write.directory,
                            &temporary,
                            &write.leaf,
                        );
                        if result.is_err() {
                            let _ = mutation_lock.remove_regular_file_under_lock(
                                &write.directory,
                                &temporary,
                                temporary_identity,
                            );
                        }
                        result
                            .and_then(|_| write.directory.sync_all())
                            .and_then(|_| mutation_lock.ensure_target_identity())
                    })
            }
            None => write
                .directory
                .open_regular_file(&write.leaf)
                .and_then(|file| {
                    let file = file.ok_or_else(|| {
                        io::Error::other("published package build artifact disappeared")
                    })?;
                    let identity = regular_file_identity(&file)?;
                    mutation_lock
                        .remove_regular_file_under_lock(&write.directory, &write.leaf, identity)
                        .and_then(|_| write.directory.sync_all())
                }),
        };
        if restored.is_err() {
            return Some(rollback_diagnostic(write));
        }
    }
    None
}

fn temporary_write_name(leaf: &std::ffi::OsStr, sequence: usize) -> OsString {
    OsString::from(format!(
        ".{file_name}.npa-build-certs.{}.{}.tmp",
        std::process::id(),
        sequence,
        file_name = leaf.to_string_lossy(),
    ))
}

fn write_unique_temporary_file(
    mutation_lock: &TargetLock,
    directory: &Directory,
    leaf: &std::ffi::OsStr,
    bytes: &[u8],
) -> io::Result<(OsString, Identity)> {
    mutation_lock.ensure_target_identity()?;
    for _ in 0..1024 {
        let sequence = NEXT_TEMPORARY_WRITE.fetch_add(1, Ordering::Relaxed);
        let temp = temporary_write_name(leaf, sequence);
        match directory.create_new_regular_file(&temp) {
            Ok(mut file) => {
                let identity = regular_file_identity(&file)?;
                if let Err(error) = file.write_all(bytes).and_then(|_| file.sync_all()) {
                    drop(file);
                    let _ =
                        mutation_lock.remove_regular_file_under_lock(directory, &temp, identity);
                    return Err(error);
                }
                mutation_lock.ensure_target_identity()?;
                return Ok((temp, identity));
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "unable to allocate unique package build temporary file",
    ))
}

fn read_directory_entry(
    directory: &Directory,
    leaf: &std::ffi::OsStr,
) -> io::Result<Option<Vec<u8>>> {
    let Some(mut file) = directory.open_regular_file(leaf)? else {
        return Ok(None);
    };
    const MAX_TRANSACTION_ARTIFACT_BYTES: u64 = 134_217_728;
    let metadata = file.metadata()?;
    if metadata.len() > MAX_TRANSACTION_ARTIFACT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "package build artifact exceeds the transaction byte limit",
        ));
    }
    let mut bytes = Vec::new();
    std::io::Read::by_ref(&mut file)
        .take(MAX_TRANSACTION_ARTIFACT_BYTES + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_TRANSACTION_ARTIFACT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "package build artifact exceeds the transaction byte limit",
        ));
    }
    Ok(Some(bytes))
}

fn rollback_diagnostic(write: &PendingWrite) -> CommandDiagnostic {
    let diagnostic =
        CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "artifact_rollback_failed")
            .with_path(render_package_path(&write.path));
    if let Some(module) = &write.module {
        diagnostic.with_module(module.as_dotted())
    } else {
        diagnostic
    }
}

fn write_artifact_diagnostic(
    reason_code: &'static str,
    path: &PackagePath,
    module: Option<&Name>,
) -> CommandDiagnostic {
    let diagnostic =
        CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason_code).with_path(path.as_str());
    if let Some(module) = module {
        diagnostic.with_module(module.as_dotted())
    } else {
        diagnostic
    }
}

pub(crate) fn fallback_imported_source_interface(
    verified: &VerifiedModule,
) -> HumanImportedSourceInterface {
    let import = VerifiedImport::from(verified);
    let empty_span = Span::empty(FileId(0));
    let mut source_interface = HumanSourceInterface::new(import.module.clone());
    source_interface.declarations = import
        .exports
        .iter()
        .map(|export| HumanSourceDeclarationMetadata {
            kind: HumanSourceDeclarationKind::Imported,
            definition_reducibility: export
                .reducibility
                .map(npa_frontend::DefinitionReducibility::from_cert),
            name: HumanName::new(export.name.0.clone(), empty_span),
            universe_params: export
                .universe_params
                .iter()
                .cloned()
                .map(|name| HumanUniverseParam {
                    name,
                    span: empty_span,
                })
                .collect(),
            binders: Vec::new(),
            decl_interface_hash: Some(export.decl_interface_hash),
            span: empty_span,
        })
        .collect();

    HumanImportedSourceInterface {
        module: import.module,
        export_hash: import.export_hash,
        certificate_hash: import.certificate_hash,
        source_interface,
    }
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn trim_package_build_heap() {
    // SAFETY: `malloc_trim(0)` asks glibc's allocator to return free heap pages
    // to the OS. It does not inspect or mutate Rust-owned live objects, and this
    // CLI-only call is a memory-pressure mitigation after large temporary proof
    // verification structures have been dropped.
    unsafe {
        libc::malloc_trim(0);
    }
}

#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
fn trim_package_build_heap() {}

fn frontend_build_failed(
    module_index: usize,
    module: &PackageModule,
    file_id: FileId,
    source: &str,
    direct_source_interfaces: &[HumanImportedSourceInterface],
    error: npa_frontend::HumanDiagnostic,
) -> CommandDiagnostic {
    frontend_build_failed_with_context(
        module_index,
        module,
        file_id,
        source,
        direct_source_interfaces,
        error,
        true,
    )
}

fn frontend_preflight_failed(
    module_index: usize,
    module: &PackageModule,
    file_id: FileId,
    source: &str,
    error: npa_frontend::HumanDiagnostic,
) -> CommandDiagnostic {
    frontend_build_failed_with_context(module_index, module, file_id, source, &[], error, false)
}

#[allow(clippy::too_many_arguments)]
fn frontend_build_failed_with_context(
    module_index: usize,
    module: &PackageModule,
    file_id: FileId,
    source: &str,
    direct_source_interfaces: &[HumanImportedSourceInterface],
    error: npa_frontend::HumanDiagnostic,
    include_declaration: bool,
) -> CommandDiagnostic {
    let primary_span = error.primary_span;
    let phase = error
        .payload
        .as_ref()
        .and_then(|payload| payload.phase)
        .map(|phase| phase.as_str())
        .unwrap_or("human_frontend");
    let conversion = error.payload.as_ref().and_then(|payload| {
        payload.conversion.as_ref().and_then(|conversion| {
            CommandDiagnosticConversionContext::new(
                conversion.phase(),
                conversion.outcome(),
                conversion.lhs_head(),
                conversion.rhs_head(),
                conversion.depth(),
            )
        })
    });
    let kernel_fuel = error
        .payload
        .as_ref()
        .and_then(|payload| payload.kernel_fuel.as_ref())
        .map(CommandKernelFuelDiagnostic::from_frontend);
    let universe_mismatch = error.payload.as_ref().and_then(|payload| {
        payload.universe_mismatch.as_ref().map(|mismatch| {
            (
                mismatch.declared_level().to_owned(),
                format!(
                    "declaration={};inferred_level={};type_path={}",
                    mismatch.declaration_name(),
                    mismatch.inferred_level(),
                    mismatch.type_path(),
                ),
            )
        })
    });
    let delimiter = error
        .payload
        .as_ref()
        .and_then(|payload| payload.delimiter.as_ref())
        .and_then(|delimiter| {
            command_delimiter_context(&module.source, file_id, source, delimiter)
        });
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
        .with_module(module.module.as_dotted())
        .with_path(format!("modules[{module_index}].source"))
        .with_field(phase)
        .with_actual_value(error.message);
    if let Some((declared_level, inferred_context)) = universe_mismatch {
        diagnostic = diagnostic
            .with_expected_value(declared_level)
            .with_actual_value(inferred_context);
    }
    if let Some(conversion) = conversion {
        diagnostic = diagnostic.with_conversion(conversion);
    }
    if let Some(kernel_fuel) = kernel_fuel {
        diagnostic = diagnostic.with_kernel_fuel(kernel_fuel);
    }
    if let Some(delimiter) = delimiter {
        diagnostic = diagnostic.with_delimiter(delimiter);
    }

    match frontend_source_context_with_declaration(
        &module.source,
        file_id,
        source,
        direct_source_interfaces,
        primary_span,
        include_declaration,
    ) {
        Some(context) => diagnostic.with_source(context),
        None => diagnostic,
    }
}

#[cfg(test)]
fn frontend_source_context(
    source_path: &PackagePath,
    file_id: FileId,
    source: &str,
    direct_source_interfaces: &[HumanImportedSourceInterface],
    span: Span,
) -> Option<CommandDiagnosticSourceContext> {
    frontend_source_context_with_declaration(
        source_path,
        file_id,
        source,
        direct_source_interfaces,
        span,
        true,
    )
}

fn frontend_source_context_with_declaration(
    source_path: &PackagePath,
    file_id: FileId,
    source: &str,
    direct_source_interfaces: &[HumanImportedSourceInterface],
    span: Span,
    include_declaration: bool,
) -> Option<CommandDiagnosticSourceContext> {
    let context = command_source_context(source_path, file_id, source, span)?;
    let declaration = include_declaration
        .then(|| frontend_containing_declaration(file_id, source, direct_source_interfaces, span))
        .flatten();

    Some(match declaration {
        Some(declaration) => context.with_declaration(declaration),
        None => context,
    })
}

fn frontend_containing_declaration(
    file_id: FileId,
    source: &str,
    direct_source_interfaces: &[HumanImportedSourceInterface],
    span: Span,
) -> Option<String> {
    let parsed =
        parse_human_module_with_source_interfaces(file_id, source, direct_source_interfaces)
            .ok()?;
    let last_named_item = parsed
        .items
        .iter()
        .rposition(|item| named_human_item(item).is_some());
    let mut namespace_stack: Vec<HumanName> = Vec::new();

    for (item_index, item) in parsed.items.iter().enumerate() {
        if let Some((name, item_span)) = named_human_item(item) {
            if human_item_contains_span(
                item_span,
                span,
                source.len(),
                Some(item_index) == last_named_item,
            ) {
                let mut parts = namespace_stack
                    .iter()
                    .flat_map(|namespace| namespace.parts.iter().cloned())
                    .collect::<Vec<_>>();
                parts.extend(name.parts.iter().cloned());
                return Some(parts.join("."));
            }
        }

        match item {
            HumanItem::NamespaceStart { name, .. } => namespace_stack.push(name.clone()),
            HumanItem::NamespaceEnd { .. } => {
                namespace_stack.pop();
            }
            _ => {}
        }
    }

    None
}

fn named_human_item(item: &HumanItem) -> Option<(&HumanName, Span)> {
    match item {
        HumanItem::Def(definition) => {
            Some((&definition.declaration.name, definition.declaration.span))
        }
        HumanItem::Theorem(decl) => Some((&decl.name, decl.span)),
        HumanItem::EquationDef(decl) => Some((&decl.name, decl.span)),
        HumanItem::Axiom(decl) => Some((&decl.name, decl.span)),
        HumanItem::Inductive(decl) => Some((&decl.name, decl.span)),
        HumanItem::Class(decl) => Some((&decl.name, decl.span)),
        HumanItem::Instance(decl) => Some((&decl.name, decl.span)),
        HumanItem::Import { .. }
        | HumanItem::Open { .. }
        | HumanItem::NamespaceStart { .. }
        | HumanItem::NamespaceEnd { .. }
        | HumanItem::Notation(_) => None,
    }
}

fn human_item_contains_span(
    item_span: Span,
    diagnostic_span: Span,
    source_len: usize,
    is_last_named_item: bool,
) -> bool {
    if item_span.file_id != diagnostic_span.file_id {
        return false;
    }

    if diagnostic_span.start.0 < diagnostic_span.end.0 {
        return item_span.start.0 <= diagnostic_span.start.0
            && diagnostic_span.end.0 <= item_span.end.0;
    }

    let offset = diagnostic_span.start.0;
    item_span.start.0 <= offset
        && (offset < item_span.end.0
            || (is_last_named_item
                && item_span.end.0 == offset
                && usize::try_from(offset).ok() == Some(source_len)))
}

fn hash_mismatch(
    reason_code: &'static str,
    path: String,
    field: &'static str,
    expected: PackageHash,
    actual: PackageHash,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::HashMismatch, reason_code)
        .with_path(path)
        .with_field(field)
        .with_hashes(format_package_hash(&expected), format_package_hash(&actual))
}

#[cfg(test)]
mod tests {
    use super::{
        check_refreshed_certificate_import_identities, external_import_dependency_order,
        format_package_hash, frontend_source_context, normalize_allowed_refresh_hash_fields,
        parse_and_validate_manifest_str, read_bytes_through_limit,
        refresh_manifest_hash_fields_for_modules, transitive_module_dependency_names,
        CertificateReadVerifyTestCounts, CommandResult, DiagnosticKind,
        ExternalImportDependencyLimits, FileId, HumanImportedSourceInterface, HumanName,
        HumanSourceInterface, KernelFuelReportMode, ManifestHashRefreshIdentity, Name,
        PackageBuildObservationCoordinator, PackageHash, PackageLockImport, PackagePath,
        PackageTimingMode, PerformancePackageSelectionObservation, Span,
        CERTIFICATE_READ_VERIFY_TEST_COUNTS, TARGETED_EXTERNAL_DEPENDENCY_LIMITS,
        TARGETED_REFRESH_AFTER_PREFLIGHT_TEST_HOOK, TIMING_SELECTION_MS,
    };
    use crate::package_api::v1::{common_options, refresh_artifacts_check};
    use npa_api::{PerformanceMeasurementLabel, PerformancePackageSelectionBatchPolicy};
    use npa_frontend::{
        HumanNotationAssociativity, HumanNotationKind, HumanSourceNotationMetadata,
    };
    use std::{
        collections::BTreeSet,
        fs,
        io::Cursor,
        path::{Path, PathBuf},
    };

    const FRONTEND_SOURCE_PATH: &str = "Proofs/Ai/ExplicitFinite/source.npa";

    #[test]
    fn available_import_dependency_closure_excludes_unrelated_modules() {
        let dependencies = [
            ("Fixture.Direct", vec!["Fixture.Base"]),
            ("Fixture.Base", vec!["Fixture.Foundation"]),
            ("Fixture.Foundation", vec![]),
            ("Fixture.UnrelatedDuplicate", vec!["Fixture.Other"]),
            ("Fixture.Other", vec![]),
        ]
        .into_iter()
        .map(|(module, imports)| {
            (
                Name::from_dotted(module),
                imports
                    .into_iter()
                    .map(Name::from_dotted)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();

        let closure =
            transitive_module_dependency_names([Name::from_dotted("Fixture.Direct")], |module| {
                dependencies.get(module).cloned()
            });

        assert_eq!(
            closure,
            ["Fixture.Base", "Fixture.Direct", "Fixture.Foundation"]
                .into_iter()
                .map(Name::from_dotted)
                .collect()
        );
        assert!(!closure.contains(&Name::from_dotted("Fixture.UnrelatedDuplicate")));
    }

    struct CopiedPackageFixture {
        path: PathBuf,
    }

    impl CopiedPackageFixture {
        fn proofs(label: &str) -> Self {
            let source =
                Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package/proofs");
            let path = std::env::temp_dir().join(format!(
                "npa-cli-package-build-unit-{}-{label}",
                std::process::id()
            ));
            if path.exists() {
                fs::remove_dir_all(&path).unwrap();
            }
            copy_test_tree(&source, &path);
            Self { path }
        }
    }

    impl Drop for CopiedPackageFixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    fn copy_test_tree(source: &Path, destination: &Path) {
        fs::create_dir_all(destination).unwrap();
        for entry in fs::read_dir(source).unwrap() {
            let entry = entry.unwrap();
            let source_path = entry.path();
            let destination_path = destination.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copy_test_tree(&source_path, &destination_path);
            } else {
                fs::copy(source_path, destination_path).unwrap();
            }
        }
    }

    #[test]
    fn targeted_refresh_rereads_selected_source_after_structural_preflight() {
        let fixture = CopiedPackageFixture::proofs("post-preflight-source-replacement");
        let selected_source = fixture.path.join("Proofs/Ai/Basic/source.npa");
        TARGETED_REFRESH_AFTER_PREFLIGHT_TEST_HOOK.with(|hook| {
            *hook.borrow_mut() = Some(Box::new(move || {
                fs::write(selected_source, "def replaced_bad : Type := (\n").unwrap();
            }));
        });

        let result = super::run_package_build_certs(
            refresh_artifacts_check(common_options(&fixture.path, true))
                .with_modules(vec![Name::from_dotted("Proofs.Ai.Basic")]),
        );
        TARGETED_REFRESH_AFTER_PREFLIGHT_TEST_HOOK.with(|hook| {
            hook.borrow_mut().take();
        });

        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::PackageFailure
        );
        assert_eq!(result.diagnostics.len(), 3);
        assert_eq!(result.diagnostics[0].reason_code, "package_build_selection");
        assert_eq!(
            result.diagnostics[1].reason_code,
            "package_build_refresh_schedule"
        );
        assert_eq!(result.diagnostics[2].reason_code, "build_failed");
        assert_eq!(
            result.diagnostics[2].module.as_deref(),
            Some("Proofs.Ai.Basic")
        );
        assert_eq!(result.diagnostics[2].field.as_deref(), Some("parser"));
    }

    #[test]
    fn targeted_refresh_reads_and_verifies_each_declared_external_once() {
        let fixture = CopiedPackageFixture::proofs("priority-external-single-read");
        CERTIFICATE_READ_VERIFY_TEST_COUNTS.with(|counts| {
            *counts.borrow_mut() = Some(CertificateReadVerifyTestCounts::default());
        });

        let result = super::run_package_build_certs(
            refresh_artifacts_check(common_options(&fixture.path, true))
                .with_modules(vec![Name::from_dotted("Proofs.Ai.EqReasoning")]),
        );
        let counts = CERTIFICATE_READ_VERIFY_TEST_COUNTS.with(|counts| {
            counts
                .borrow_mut()
                .take()
                .expect("certificate observer was installed")
        });

        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::Success,
            "{:?}",
            result.diagnostics
        );
        for path in [
            "vendor/npa-std/Std/Logic/Eq/certificate.npcert",
            "vendor/npa-std/Std/Nat/Basic/certificate.npcert",
        ] {
            assert_eq!(counts.reads_by_path.get(path), Some(&1), "read {path}");
            assert_eq!(counts.verifies_by_path.get(path), Some(&1), "verify {path}");
        }
    }

    fn assert_changed_selection_observation_coordinator_contract() {
        let observation = PerformancePackageSelectionObservation {
            batch_policy: PerformancePackageSelectionBatchPolicy::ExecBudget,
            candidate_paths: 3,
            pathspec_batches: 1,
            tracked_queries: 1,
            untracked_queries: 1,
            selected_paths: 2,
            ..PerformancePackageSelectionObservation::default()
        };

        let mut off = PackageBuildObservationCoordinator::new(
            KernelFuelReportMode::Off,
            PackageTimingMode::Off,
        );
        assert!(!off.measurement_enabled());
        assert!(!off.measurements_enabled());
        let mut off_called = false;
        assert_eq!(
            off.time_selection(|| {
                off_called = true;
                7
            }),
            7
        );
        assert!(off_called);
        off.observe_package_selection(&observation);
        assert!(off
            .finish(CommandResult::passed("test", "root"))
            .timings
            .is_none());

        let mut summary = PackageBuildObservationCoordinator::new(
            KernelFuelReportMode::Off,
            PackageTimingMode::Summary,
        );
        assert!(summary.measurement_enabled());
        assert!(summary.measurements_enabled());
        assert_eq!(summary.time_selection(|| 11), 11);
        summary.observe_package_selection(&observation);
        let result = summary.finish(CommandResult::passed("test", "root"));
        let timings = result.timings.expect("summary timing envelope");
        assert!(timings
            .metrics
            .iter()
            .any(|metric| metric.field == TIMING_SELECTION_MS));
        let measurements = timings.measurements.expect("selection measurements");
        assert!(measurements.counters.iter().any(|counter| {
            counter.label == PerformanceMeasurementLabel::PackageSelectionCandidatePaths
                && counter.value == 3
        }));
        assert!(measurements.counters.iter().any(|counter| {
            counter.label == PerformanceMeasurementLabel::PackageSelectionChangedPaths
                && counter.value == 2
        }));

        let source = include_str!("package_build.rs");
        let allocate = source
            .find("(observations.measurements_enabled() && selection_is_changed)")
            .expect("changed selection observation is enablement-gated");
        let time = source[allocate..]
            .find("observations.time_selection(||")
            .map(|index| allocate + index)
            .expect("complete selection is timed");
        let thread = source[time..]
            .find("selection_observation.as_mut()")
            .map(|index| time + index)
            .expect("operation observation is threaded into selection");
        let project = source[thread..]
            .find("observations.observe_package_selection(observation)")
            .map(|index| thread + index)
            .expect("selection observation is projected");
        let propagate = source[project..]
            .find("let plan = match selection_result")
            .map(|index| project + index)
            .expect("selection result is propagated after projection");
        assert!(allocate < time && time < thread && thread < project && project < propagate);
    }

    macro_rules! changed_selection_exact_test {
        ($name:ident) => {
            #[test]
            fn $name() {
                assert_changed_selection_observation_coordinator_contract();
            }
        };
    }

    changed_selection_exact_test!(observation_coordinator_reports_measurement_enablement);
    changed_selection_exact_test!(observation_coordinator_times_selection_only_when_enabled);
    changed_selection_exact_test!(observation_coordinator_projects_selection);
    changed_selection_exact_test!(changed_selection_threads_operation_observation);
    changed_selection_exact_test!(changed_build_allocates_selection_observation_only_when_enabled);
    changed_selection_exact_test!(changed_build_times_complete_selection);
    changed_selection_exact_test!(changed_build_projects_selection_observation);
    changed_selection_exact_test!(changed_build_projects_selection_before_result_propagation);

    #[test]
    fn package_build_certs_external_import_dependency_order_handles_deep_chains_iteratively() {
        const IMPORT_COUNT: usize = 32_768;
        let import_modules = vec![Name::from_dotted("Fixture.External.Module"); IMPORT_COUNT];
        let seeds = BTreeSet::from([0]);

        let order = external_import_dependency_order(
            &import_modules,
            &seeds,
            TARGETED_EXTERNAL_DEPENDENCY_LIMITS,
            |index, _remaining_edges| {
                Ok((index + 1 < IMPORT_COUNT)
                    .then_some(vec![index + 1])
                    .unwrap_or_default())
            },
        )
        .expect("deep external chain should not consume call-stack depth");

        assert_eq!(order.len(), IMPORT_COUNT);
        assert_eq!(order.first(), Some(&(IMPORT_COUNT - 1)));
        assert_eq!(order.last(), Some(&0));
        assert!(order.windows(2).all(|pair| pair[0] == pair[1] + 1));
    }

    #[test]
    fn package_build_certs_external_import_dependency_order_prunes_completed_cycle_path_nodes() {
        let import_modules = ["Fixture.A", "Fixture.B", "Fixture.C"]
            .into_iter()
            .map(Name::from_dotted)
            .collect::<Vec<_>>();
        let seeds = BTreeSet::from([0]);
        let dependencies = [vec![1, 2], vec![], vec![0]];

        let diagnostic = external_import_dependency_order(
            &import_modules,
            &seeds,
            TARGETED_EXTERNAL_DEPENDENCY_LIMITS,
            |index, _remaining_edges| Ok(dependencies[index].clone()),
        )
        .expect_err("A -> C -> A should be rejected as a cycle");

        assert_eq!(diagnostic.reason_code, "lock_import_cycle");
        assert_eq!(diagnostic.module.as_deref(), Some("Fixture.C"));
        assert_eq!(
            diagnostic.path.as_deref(),
            Some("imports[2].certificate.imports")
        );
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some("Fixture.A -> Fixture.C -> Fixture.A")
        );
    }

    #[test]
    fn package_build_certs_external_import_dependency_order_bounds_cumulative_edges() {
        let import_modules = ["Fixture.A", "Fixture.B", "Fixture.C", "Fixture.D"]
            .into_iter()
            .map(Name::from_dotted)
            .collect::<Vec<_>>();
        let seeds = BTreeSet::from([0]);
        let dependencies = [vec![1, 2, 3], vec![2], vec![], vec![]];
        let limits = ExternalImportDependencyLimits {
            max_imports: import_modules.len(),
            max_dependency_edges: 3,
            max_certificate_bytes: 16,
        };

        let diagnostic =
            external_import_dependency_order(&import_modules, &seeds, limits, |index, _| {
                Ok(dependencies[index].clone())
            })
            .expect_err("the fourth retained dependency edge should exceed the limit");

        assert_eq!(
            diagnostic.reason_code,
            "external_import_closure_limit_exceeded"
        );
        assert_eq!(diagnostic.module.as_deref(), Some("Fixture.B"));
        assert_eq!(
            diagnostic.path.as_deref(),
            Some("imports[1].certificate.imports")
        );
        assert_eq!(diagnostic.field.as_deref(), Some("dependency_edges"));
        assert_eq!(diagnostic.expected_value.as_deref(), Some("at most 3"));
        assert_eq!(diagnostic.actual_value.as_deref(), Some("4"));
    }

    #[test]
    fn package_build_certs_external_import_dependency_order_bounds_import_count() {
        let import_modules = ["Fixture.A", "Fixture.B", "Fixture.C"]
            .into_iter()
            .map(Name::from_dotted)
            .collect::<Vec<_>>();
        let limits = ExternalImportDependencyLimits {
            max_imports: 2,
            max_dependency_edges: 3,
            max_certificate_bytes: 16,
        };

        let diagnostic = external_import_dependency_order(
            &import_modules,
            &BTreeSet::from([0]),
            limits,
            |_, _| panic!("dependency discovery must not start above the import limit"),
        )
        .expect_err("the third manifest import should exceed the limit");

        assert_eq!(
            diagnostic.reason_code,
            "external_import_closure_limit_exceeded"
        );
        assert_eq!(diagnostic.module, None);
        assert_eq!(diagnostic.path.as_deref(), Some("imports"));
        assert_eq!(diagnostic.field.as_deref(), Some("imports"));
        assert_eq!(diagnostic.expected_value.as_deref(), Some("at most 2"));
        assert_eq!(diagnostic.actual_value.as_deref(), Some("3"));
    }

    #[test]
    fn package_build_certs_empty_external_selection_skips_discovery_limits() {
        let import_modules = ["Fixture.A", "Fixture.B", "Fixture.C"]
            .into_iter()
            .map(Name::from_dotted)
            .collect::<Vec<_>>();
        let limits = ExternalImportDependencyLimits {
            max_imports: 2,
            max_dependency_edges: 0,
            max_certificate_bytes: 0,
        };

        let order =
            external_import_dependency_order(&import_modules, &BTreeSet::new(), limits, |_, _| {
                panic!("empty external selection must not discover dependencies")
            })
            .expect("unrelated manifest imports should not affect an empty selection");

        assert!(order.is_empty());
    }

    #[test]
    fn package_build_certs_external_import_dependency_read_is_bounded() {
        let exact = read_bytes_through_limit(Cursor::new(vec![0_u8; 4]), 4)
            .expect("exact-limit read should succeed");
        assert_eq!(exact.len(), 4);

        let oversized = read_bytes_through_limit(Cursor::new(vec![0_u8; 8]), 4)
            .expect("bounded oversized read should succeed");
        assert_eq!(oversized.len(), 5);
    }

    #[test]
    fn package_build_certs_frontend_source_context_validates_file_and_range_without_slicing() {
        let file_id = FileId(7);
        let source = "def value : Type := Type\n-- λ";
        let ascii_start = source.find("value").expect("value token") as u32;
        let ascii_end = ascii_start + "value".len() as u32;
        let path = PackagePath::new(FRONTEND_SOURCE_PATH);

        let current = frontend_source_context(
            &path,
            file_id,
            source,
            &[],
            Span::new(file_id, ascii_start, ascii_end),
        )
        .expect("current-source span should project");
        assert_eq!(current.path(), FRONTEND_SOURCE_PATH);
        assert_eq!(current.start_byte(), ascii_start);
        assert_eq!(current.end_byte(), ascii_end);
        assert_eq!(current.declaration(), Some("value"));
        assert_eq!(current.line(), Some(1));
        assert_eq!(current.column(), Some(5));
        assert_eq!(current.token(), Some("value"));

        for span in [
            Span::new(FileId(8), ascii_start, ascii_end),
            Span::new(file_id, ascii_end, ascii_start),
            Span::new(file_id, ascii_start, source.len() as u32 + 1),
        ] {
            assert!(frontend_source_context(&path, file_id, source, &[], span).is_none());
        }

        let lambda_start = source.find('λ').expect("lambda token") as u32;
        let inside_multibyte_scalar = Span::new(file_id, lambda_start + 1, lambda_start + 1);
        let unicode_context =
            frontend_source_context(&path, file_id, source, &[], inside_multibyte_scalar)
                .expect("byte offsets need not be UTF-8 scalar boundaries");
        assert_eq!(unicode_context.start_byte(), lambda_start + 1);
        assert_eq!(unicode_context.end_byte(), lambda_start + 1);
        assert_eq!(unicode_context.line(), None);
        assert_eq!(unicode_context.column(), None);
        assert_eq!(unicode_context.token(), None);

        let unicode_source = "αβ value";
        let value_start = unicode_source.find("value").unwrap() as u32;
        let unicode_scalar_column = frontend_source_context(
            &path,
            file_id,
            unicode_source,
            &[],
            Span::new(file_id, value_start, value_start + 5),
        )
        .unwrap();
        assert_eq!(unicode_scalar_column.line(), Some(1));
        assert_eq!(unicode_scalar_column.column(), Some(4));
        assert_eq!(unicode_scalar_column.token(), Some("value"));
    }

    #[test]
    fn package_build_certs_frontend_source_context_distinguishes_repeated_binders() {
        let file_id = FileId(3);
        let source = "def first : Type := fun x => x\ndef second : Type := fun x => x";
        let binders = source
            .match_indices("fun x")
            .map(|(start, _)| start as u32 + 4)
            .collect::<Vec<_>>();
        assert_eq!(binders.len(), 2);

        let first =
            test_frontend_source_context(source, Span::new(file_id, binders[0], binders[0] + 1));
        let second =
            test_frontend_source_context(source, Span::new(file_id, binders[1], binders[1] + 1));
        assert_eq!(first.declaration(), Some("first"));
        assert_eq!(second.declaration(), Some("second"));
        assert_ne!(first.start_byte(), second.start_byte());
    }

    #[test]
    fn package_build_certs_frontend_source_context_uses_half_open_empty_boundaries_and_eof() {
        let file_id = FileId(3);
        let source = "def first : Type := Type\ndef second : Type := Type";
        let second_start = source.find("def second").expect("second declaration") as u32;

        let at_second_start =
            test_frontend_source_context(source, Span::new(file_id, second_start, second_start));
        assert_eq!(at_second_start.declaration(), Some("second"));

        let at_start = test_frontend_source_context(source, Span::new(file_id, 0, 0));
        assert_eq!(at_start.declaration(), Some("first"));

        let eof = source.len() as u32;
        let at_eof = test_frontend_source_context(source, Span::new(file_id, eof, eof));
        assert_eq!(at_eof.declaration(), Some("second"));
    }

    #[test]
    fn package_build_certs_frontend_source_context_reports_every_named_owning_item() {
        let file_id = FileId(3);
        let source = "\
def plain : Type := Type
def equations (n : Nat) : Nat where
| default => n
theorem result : Type := Type
axiom assumed : Type
inductive Choice : Type where
| pick : Choice
class Wrapper (A : Type) where
  unwrap : A
instance wrapper_type : Wrapper Type where
  unwrap := Type";
        for (token, expected) in [
            ("plain", "plain"),
            ("equations", "equations"),
            ("result", "result"),
            ("assumed", "assumed"),
            ("pick", "Choice"),
            ("unwrap : A", "Wrapper"),
            ("unwrap := Type", "wrapper_type"),
        ] {
            let start = source
                .find(token)
                .unwrap_or_else(|| panic!("missing token {token}")) as u32;
            let context = test_frontend_source_context(
                source,
                Span::new(file_id, start, start + token.len() as u32),
            );
            assert_eq!(context.declaration(), Some(expected), "token {token}");
        }
    }

    #[test]
    fn package_build_certs_frontend_source_context_flattens_nested_namespaces() {
        let file_id = FileId(3);
        let source = "\
namespace Enumeration
namespace Product.Tools
theorem product_intro : Type := Type
end Product.Tools
end Enumeration";
        let parsed = npa_frontend::parse_human_module(file_id, source)
            .expect("nested namespace source should parse");
        assert_eq!(parsed.items.len(), 5);
        let start = source.find("product_intro").expect("theorem name") as u32;
        let context = test_frontend_source_context(
            source,
            Span::new(file_id, start, start + "product_intro".len() as u32),
        );
        assert_eq!(
            context.declaration(),
            Some("Enumeration.Product.Tools.product_intro")
        );
    }

    #[test]
    fn package_build_certs_frontend_source_context_ignores_unnamed_items_and_parser_failure() {
        let file_id = FileId(3);
        let unnamed_source = "notation \"unit\" => Unit.value";
        let start = unnamed_source.find("unit").expect("notation token") as u32;
        let unnamed = test_frontend_source_context(
            unnamed_source,
            Span::new(file_id, start, start + "unit".len() as u32),
        );
        assert_eq!(unnamed.declaration(), None);

        let incomplete_source = "theorem incomplete : Type :=";
        let eof = incomplete_source.len() as u32;
        let incomplete =
            test_frontend_source_context(incomplete_source, Span::new(file_id, eof, eof));
        assert_eq!(incomplete.path(), FRONTEND_SOURCE_PATH);
        assert_eq!(incomplete.start_byte(), eof);
        assert_eq!(incomplete.end_byte(), eof);
        assert_eq!(incomplete.declaration(), None);
    }

    #[test]
    fn package_build_certs_frontend_source_context_reparses_with_imported_notation() {
        let file_id = FileId(3);
        let imported_module = Name::from_dotted("Fixture.Operators");
        let mut source_interface = HumanSourceInterface::new(imported_module.clone());
        source_interface
            .notations
            .push(HumanSourceNotationMetadata {
                kind: HumanNotationKind::Infixl,
                associativity: HumanNotationAssociativity::Left,
                precedence: 65,
                token: "+".to_owned(),
                target: HumanName::new(
                    vec![
                        "Fixture".to_owned(),
                        "Operators".to_owned(),
                        "add".to_owned(),
                    ],
                    Span::empty(FileId(1)),
                ),
                namespace: Vec::new(),
                span: Span::empty(FileId(1)),
            });
        let imported = HumanImportedSourceInterface {
            module: imported_module,
            export_hash: [1; 32],
            certificate_hash: Some([2; 32]),
            source_interface,
        };
        let source = "\
import Fixture.Operators
def using_imported_notation (n : Nat) : Nat := n + n";
        let start = source.find("n + n").expect("notation application") as u32 + 2;
        let context = frontend_source_context(
            &PackagePath::new(FRONTEND_SOURCE_PATH),
            file_id,
            source,
            &[imported],
            Span::new(file_id, start, start + 1),
        )
        .expect("source span should project");
        assert_eq!(context.declaration(), Some("using_imported_notation"));
    }

    fn test_frontend_source_context(
        source: &str,
        span: Span,
    ) -> super::CommandDiagnosticSourceContext {
        frontend_source_context(
            &PackagePath::new(FRONTEND_SOURCE_PATH),
            FileId(3),
            source,
            &[],
            span,
        )
        .expect("test span should project")
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_updates_only_source_hash() {
        let old_source_hash = hash(1);
        let refreshed_source_hash = hash(2);
        let certificate_file_hash = hash(3);
        let export_hash = hash(4);
        let axiom_report_hash = hash(5);
        let certificate_hash = hash(6);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            refreshed_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            old_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );

        let refreshed_source = refresh_manifest_hash_fields_for_modules(
            &manifest_source,
            std::slice::from_ref(&identity),
        )
        .unwrap();

        assert!(refreshed_source.ends_with('\n'));
        assert!(refreshed_source.contains("# package comment"));
        assert!(refreshed_source.contains("# source pin"));
        assert!(refreshed_source.contains(&format!(
            "expected_source_hash = \"{}\"",
            format_package_hash(&refreshed_source_hash)
        )));
        assert!(!refreshed_source.contains(&format_package_hash(&old_source_hash)));
        let no_newline_source = manifest_source.trim_end_matches('\n').to_owned();
        let no_newline_refreshed = refresh_manifest_hash_fields_for_modules(
            &no_newline_source,
            std::slice::from_ref(&identity),
        )
        .unwrap();
        assert!(!no_newline_refreshed.ends_with('\n'));

        let crlf_source = manifest_source.replace('\n', "\r\n");
        let crlf_refreshed =
            refresh_manifest_hash_fields_for_modules(&crlf_source, std::slice::from_ref(&identity))
                .unwrap();
        assert!(crlf_refreshed.ends_with("\r\n"));
        assert!(!crlf_refreshed.replace("\r\n", "").contains('\n'));
        assert!(crlf_refreshed.contains(&format!(
            "expected_source_hash = \"{}\"",
            format_package_hash(&refreshed_source_hash)
        )));

        let original = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let refreshed = parse_and_validate_manifest_str(&refreshed_source).unwrap();
        assert_eq!(
            refreshed.manifest().modules[0].expected_source_hash,
            refreshed_source_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_certificate_file_hash,
            certificate_file_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_export_hash,
            export_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_axiom_report_hash,
            axiom_report_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_certificate_hash,
            certificate_hash
        );
        let mut normalized_refreshed = refreshed.manifest().clone();
        normalize_allowed_refresh_hash_fields(original.manifest(), &mut normalized_refreshed)
            .unwrap();
        assert_eq!(&normalized_refreshed, original.manifest());
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_rejects_non_string_hash_field() {
        let identity = refresh_identity(
            0,
            "Fixture.A",
            hash(11),
            hash(12),
            hash(13),
            hash(14),
            hash(15),
        );
        let manifest_source =
            fixture_manifest_source("Fixture.A", hash(1), hash(12), hash(13), hash(14), hash(15));
        let malformed_source = manifest_source.replace(
            &format!(
                "expected_source_hash = \"{}\" # source pin",
                format_package_hash(&hash(1))
            ),
            "expected_source_hash = 1 # source pin",
        );

        let error =
            refresh_manifest_hash_fields_for_modules(&malformed_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(
            error.path.as_deref(),
            Some("modules[0].expected_source_hash")
        );
        assert_eq!(error.field.as_deref(), Some("expected_source_hash"));
        assert_eq!(error.expected_value.as_deref(), Some("string"));
        assert_eq!(error.actual_value.as_deref(), Some("integer"));
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_rejects_missing_hash_field() {
        let identity = refresh_identity(
            0,
            "Fixture.A",
            hash(16),
            hash(17),
            hash(18),
            hash(19),
            hash(20),
        );
        let missing_line = format!(
            "expected_certificate_hash = \"{}\"\n",
            format_package_hash(&hash(20))
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            hash(16),
            hash(17),
            hash(18),
            hash(19),
            hash(20),
        );
        let malformed_source = manifest_source.replace(&missing_line, "");

        let error =
            refresh_manifest_hash_fields_for_modules(&malformed_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(
            error.path.as_deref(),
            Some("modules[0].expected_certificate_hash")
        );
        assert_eq!(error.field.as_deref(), Some("expected_certificate_hash"));
        assert_eq!(
            error.expected_value.as_deref(),
            Some("existing string hash field")
        );
        assert_eq!(error.actual_value.as_deref(), Some("missing"));
    }

    #[test]
    fn package_build_certs_write_refresh_manifest_rewrite_rejects_duplicate_hash_field() {
        let source_hash = hash(21);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            hash(22),
            hash(23),
            hash(24),
            hash(25),
            hash(26),
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            source_hash,
            hash(23),
            hash(24),
            hash(25),
            hash(26),
        );
        let duplicate_source = manifest_source.replace(
            &format!(
                "expected_source_hash = \"{}\" # source pin",
                format_package_hash(&source_hash)
            ),
            &format!(
                "expected_source_hash = \"{}\" # source pin\nexpected_source_hash = \"{}\"",
                format_package_hash(&source_hash),
                format_package_hash(&source_hash)
            ),
        );

        let error =
            refresh_manifest_hash_fields_for_modules(&duplicate_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(error.path.as_deref(), Some("npa-package.toml"));
        assert_eq!(error.field.as_deref(), Some("toml"));
    }

    #[test]
    fn package_build_certs_write_refresh_manifest_rewrite_rejects_module_order_mismatch() {
        let identity = refresh_identity(
            0,
            "Fixture.B",
            hash(31),
            hash(32),
            hash(33),
            hash(34),
            hash(35),
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            hash(30),
            hash(32),
            hash(33),
            hash(34),
            hash(35),
        );

        let error =
            refresh_manifest_hash_fields_for_modules(&manifest_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(error.path.as_deref(), Some("modules[0].module"));
        assert_eq!(error.field.as_deref(), Some("module"));
        assert_eq!(error.expected_value.as_deref(), Some("Fixture.B"));
        assert_eq!(error.actual_value.as_deref(), Some("Fixture.A"));
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_preserves_fresh_crlf_manifest() {
        let source_hash = hash(41);
        let certificate_file_hash = hash(42);
        let export_hash = hash(43);
        let axiom_report_hash = hash(44);
        let certificate_hash = hash(45);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        )
        .replace('\n', "\r\n");

        let refreshed_source = refresh_manifest_hash_fields_for_modules(
            &manifest_source,
            std::slice::from_ref(&identity),
        )
        .unwrap();

        assert_eq!(refreshed_source, manifest_source);
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_accepts_empty_modules_array() {
        let manifest_source = empty_modules_array_manifest_source();

        let refreshed_source = refresh_manifest_hash_fields_for_modules(&manifest_source, &[])
            .expect("empty modules array should refresh");

        assert_eq!(refreshed_source, manifest_source);
        let parsed = parse_and_validate_manifest_str(&refreshed_source).unwrap();
        assert!(parsed.manifest().modules.is_empty());
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_updates_inline_module_array() {
        let old_source_hash = hash(46);
        let refreshed_source_hash = hash(47);
        let certificate_file_hash = hash(48);
        let export_hash = hash(49);
        let axiom_report_hash = hash(50);
        let certificate_hash = hash(51);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            refreshed_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );
        let manifest_source = inline_module_array_manifest_source(
            "Fixture.A",
            old_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );

        let refreshed_source = refresh_manifest_hash_fields_for_modules(
            &manifest_source,
            std::slice::from_ref(&identity),
        )
        .expect("inline module array should refresh");

        assert!(refreshed_source.contains("modules = ["));
        assert!(refreshed_source.contains("{ module = \"Fixture.A\""));
        assert!(!refreshed_source.contains("[[modules]]"));
        assert!(refreshed_source.contains(&format!(
            "expected_source_hash = \"{}\"",
            format_package_hash(&refreshed_source_hash)
        )));
        assert!(!refreshed_source.contains(&format_package_hash(&old_source_hash)));
        let parsed = parse_and_validate_manifest_str(&refreshed_source).unwrap();
        assert_eq!(
            parsed.manifest().modules[0].expected_source_hash,
            refreshed_source_hash
        );
    }

    #[test]
    fn package_build_certs_check_refresh_import_identity_allows_certificate_import_order() {
        let owner = Name::from_dotted("Fixture.C");
        let expected = vec![
            lock_import("Fixture.A", 51, 52),
            lock_import("Fixture.B", 53, 54),
        ];
        let actual = vec![
            certificate_import("Fixture.B", 53, 54),
            certificate_import("Fixture.A", 51, 52),
        ];

        let diagnostic =
            check_refreshed_certificate_import_identities(2, &owner, &expected, &actual);

        assert!(diagnostic.is_none());
    }

    #[test]
    fn package_build_certs_check_refresh_import_identity_deduplicates_expected_imports() {
        let owner = Name::from_dotted("Fixture.C");
        let expected = vec![
            lock_import("Fixture.A", 55, 56),
            lock_import("Fixture.A", 55, 56),
        ];
        let actual = vec![certificate_import("Fixture.A", 55, 56)];

        let diagnostic =
            check_refreshed_certificate_import_identities(2, &owner, &expected, &actual);

        assert!(diagnostic.is_none());
    }

    #[test]
    fn package_build_certs_check_refresh_import_identity_allows_transitive_imports() {
        let owner = Name::from_dotted("Fixture.C");
        let expected = vec![lock_import("Fixture.B", 53, 54)];
        let actual = vec![
            certificate_import("Fixture.A", 51, 52),
            certificate_import("Fixture.B", 53, 54),
        ];

        let diagnostic =
            check_refreshed_certificate_import_identities(2, &owner, &expected, &actual);

        assert!(diagnostic.is_none());
    }

    fn fixture_manifest_source(
        module: &str,
        source_hash: PackageHash,
        certificate_file_hash: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
    ) -> String {
        format!(
            r#"schema = "npa.package.v0.1" # package comment
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []

[[modules]]
module = "{module}"
source = "Fixture/A/source.npa"
certificate = "Fixture/A/certificate.npcert"
imports = []
expected_source_hash = "{}" # source pin
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
"#,
            format_package_hash(&source_hash),
            format_package_hash(&certificate_file_hash),
            format_package_hash(&export_hash),
            format_package_hash(&axiom_report_hash),
            format_package_hash(&certificate_hash),
        )
    }

    fn inline_module_array_manifest_source(
        module: &str,
        source_hash: PackageHash,
        certificate_file_hash: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
    ) -> String {
        format!(
            r#"schema = "npa.package.v0.1" # package comment
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = [{{ module = "{module}", source = "Fixture/A/source.npa", certificate = "Fixture/A/certificate.npcert", imports = [], expected_source_hash = "{}", expected_certificate_file_hash = "{}", expected_export_hash = "{}", expected_axiom_report_hash = "{}", expected_certificate_hash = "{}" }}]

[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
            format_package_hash(&source_hash),
            format_package_hash(&certificate_file_hash),
            format_package_hash(&export_hash),
            format_package_hash(&axiom_report_hash),
            format_package_hash(&certificate_hash),
        )
    }

    fn empty_modules_array_manifest_source() -> String {
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = []

[policy]
allow_custom_axioms = false
allowed_axioms = []
"#
        .to_owned()
    }

    fn refresh_identity(
        module_index: usize,
        module: &str,
        source_hash: PackageHash,
        certificate_file_hash: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
    ) -> ManifestHashRefreshIdentity {
        ManifestHashRefreshIdentity {
            module_index,
            module: Name::from_dotted(module),
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        }
    }

    fn hash(byte: u8) -> PackageHash {
        PackageHash::new([byte; 32])
    }

    fn lock_import(
        module: &str,
        export_hash_seed: u8,
        certificate_hash_seed: u8,
    ) -> PackageLockImport {
        PackageLockImport {
            module: Name::from_dotted(module),
            export_hash: hash(export_hash_seed),
            certificate_hash: hash(certificate_hash_seed),
        }
    }

    fn certificate_import(
        module: &str,
        export_hash_seed: u8,
        certificate_hash_seed: u8,
    ) -> npa_cert::ImportEntry {
        npa_cert::ImportEntry {
            module: Name::from_dotted(module),
            export_hash: hash(export_hash_seed).into_bytes(),
            certificate_hash: Some(hash(certificate_hash_seed).into_bytes()),
        }
    }
}
