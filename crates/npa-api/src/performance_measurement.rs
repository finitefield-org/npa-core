//! Bounded, diagnostic-only performance measurements shared by authoring and
//! package verification.
//!
//! Measurements are deliberately excluded from semantic requests, hashes,
//! certificates, verifier policy, and proof evidence.

use std::collections::BTreeMap;
use std::time::Instant;

use npa_kernel::KernelWorkCounters;

/// Stable schema for the common cross-subsystem measurement block.
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1: &str = "npa.performance.measurements.v0.1";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2: &str = "npa.performance.measurements.v0.2";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA: &str = PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2;
/// Maximum retained module detail records.
pub const PERFORMANCE_MODULE_DETAIL_LIMIT: usize = 1_024;
/// Maximum retained declaration detail records.
pub const PERFORMANCE_DECLARATION_DETAIL_LIMIT: usize = 2_048;
/// Maximum retained candidate detail records.
pub const PERFORMANCE_CANDIDATE_DETAIL_LIMIT: usize = 256;
/// Maximum retained worker or shard detail records.
pub const PERFORMANCE_WORKER_DETAIL_LIMIT: usize = 64;

/// Operation-scoped measurement mode.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum PerformanceMeasurementMode {
    /// Do not read the clock, update counters, or allocate detail storage.
    #[default]
    Off,
    /// Retain aggregate deterministic counters and coarse elapsed stages.
    Summary,
    /// Retain aggregates plus bounded, canonically ordered detail records.
    Detailed,
}

impl PerformanceMeasurementMode {
    /// Stable JSON and CLI spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Summary => "summary",
            Self::Detailed => "detailed",
        }
    }

    /// Return whether any measurements are enabled.
    pub const fn is_enabled(self) -> bool {
        !matches!(self, Self::Off)
    }

    /// Return whether bounded keyed details are enabled.
    pub const fn is_detailed(self) -> bool {
        matches!(self, Self::Detailed)
    }
}

/// Stable unit for one measurement counter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PerformanceMeasurementUnit {
    Count,
    Bytes,
    Nanoseconds,
}

impl PerformanceMeasurementUnit {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Count => "count",
            Self::Bytes => "bytes",
            Self::Nanoseconds => "nanoseconds",
        }
    }
}

macro_rules! performance_labels {
    ($( $variant:ident => ($identifier:literal, $unit:ident) ),+ $(,)?) => {
        /// Closed vocabulary for performance counters.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum PerformanceMeasurementLabel {
            $( $variant, )+
        }

        impl PerformanceMeasurementLabel {
            /// Exhaustive label table. JSON projection sorts by identifier.
            pub const ALL: &'static [Self] = &[
                $( Self::$variant, )+
            ];

            /// Stable lower-case group-qualified identifier.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $( Self::$variant => $identifier, )+
                }
            }

            /// Stable counter unit.
            pub const fn unit(self) -> PerformanceMeasurementUnit {
                match self {
                    $( Self::$variant => PerformanceMeasurementUnit::$unit, )+
                }
            }
        }
    };
}

performance_labels! {
    ModuleSourceBytes => ("module.source_bytes", Bytes),
    ModuleSourceLines => ("module.source_lines", Count),
    ModuleSourceTokens => ("module.source_tokens", Count),
    ModuleDeclarationsElaborated => ("module.declarations_elaborated", Count),
    ModuleDeclarationsReused => ("module.declarations_reused", Count),
    ModuleBuildElapsed => ("module.build_elapsed", Nanoseconds),
    ModuleImportsLive => ("module.imports_live", Count),
    ModuleImportsCached => ("module.imports_cached", Count),
    ModuleOutputCertificateBytes => ("module.output_certificate_bytes", Bytes),
    ModuleSourceIdentityChanges => ("module.source_identity_changes", Count),
    ModuleExportIdentityChanges => ("module.export_identity_changes", Count),
    ModuleCertificateIdentityChanges => ("module.certificate_identity_changes", Count),
    CandidateSubmitted => ("candidate.submitted", Count),
    CandidateEvaluated => ("candidate.evaluated", Count),
    CandidateAccepted => ("candidate.accepted", Count),
    CandidateRejected => ("candidate.rejected", Count),
    CandidateDelayedPayloadsParsed => ("candidate.delayed_payloads_parsed", Count),
    CandidateDelayedPayloadsSkipped => ("candidate.delayed_payloads_skipped", Count),
    CandidateBatchPreparations => ("candidate.batch_preparations", Count),
    CandidateInputValidations => ("candidate.input_validations", Count),
    CandidateBaseValidations => ("candidate.base_validations", Count),
    CandidateBaseValidationsReused => ("candidate.base_validations_reused", Count),
    CandidateLocalValidations => ("candidate.local_validations", Count),
    CandidateOutputValidations => ("candidate.output_validations", Count),
    CandidateSnapshotProjections => ("candidate.snapshot_projections", Count),
    CandidateGoalProjections => ("candidate.goal_projections", Count),
    CandidateContextProjections => ("candidate.context_projections", Count),
    CandidateSnapshotProjectionsReused => ("candidate.snapshot_projections_reused", Count),
    CandidateGoalProjectionsReused => ("candidate.goal_projections_reused", Count),
    CandidateContextProjectionsReused => ("candidate.context_projections_reused", Count),
    CandidateGoalHashComputations => ("candidate.goal_hash_computations", Count),
    CandidateContextHashComputations => ("candidate.context_hash_computations", Count),
    CandidateCanonicalBytesHashed => ("candidate.canonical_bytes_hashed", Bytes),
    CandidateExecutableBaseStateClones => ("candidate.executable_base_state_clones", Count),
    CandidateOutputStateClones => ("candidate.output_state_clones", Count),
    CandidateCopiedElements => ("candidate.copied_elements", Count),
    CandidateCopiedBytes => ("candidate.copied_bytes", Bytes),
    CandidateCopiedPrefixElements => ("candidate.copied_prefix_elements", Count),
    CandidateNameIndexRebuilds => ("candidate.name_index_rebuilds", Count),
    CandidateEnvironmentClones => ("candidate.environment_clones", Count),
    CandidatePreparationElapsed => ("candidate.preparation_elapsed", Nanoseconds),
    CandidateValidationElapsed => ("candidate.validation_elapsed", Nanoseconds),
    CandidateExecutionElapsed => ("candidate.execution_elapsed", Nanoseconds),
    CandidateDeltaBuildElapsed => ("candidate.delta_build_elapsed", Nanoseconds),
    CandidateEvaluatedPrefix => ("candidate.evaluated_prefix", Count),
    CandidateSchedulerTimeoutStops => ("candidate.scheduler_timeout_stops", Count),
    CandidateSchedulerResourceLimitStops => ("candidate.scheduler_resource_limit_stops", Count),
    KernelCheckCalls => ("kernel.check_calls", Count),
    KernelInferCalls => ("kernel.infer_calls", Count),
    KernelWhnfCalls => ("kernel.whnf_calls", Count),
    KernelDefeqCalls => ("kernel.defeq_calls", Count),
    KernelQuickEqualityHits => ("kernel.quick_equality_hits", Count),
    KernelBetaSteps => ("kernel.beta_steps", Count),
    KernelDeltaSteps => ("kernel.delta_steps", Count),
    KernelIotaSteps => ("kernel.iota_steps", Count),
    KernelZetaSteps => ("kernel.zeta_steps", Count),
    KernelLogicalFuel => ("kernel.logical_fuel", Count),
    KernelSuccessfulFuel => ("kernel.successful_fuel", Count),
    KernelExhaustedFuel => ("kernel.exhausted_fuel", Count),
    KernelPhysicalReductions => ("kernel.physical_reductions", Count),
    KernelContextLookups => ("kernel.context_lookups", Count),
    KernelContextShifts => ("kernel.context_shifts", Count),
    KernelMemoHits => ("kernel.memo_hits", Count),
    KernelMemoMisses => ("kernel.memo_misses", Count),
    KernelMemoInserts => ("kernel.memo_inserts", Count),
    KernelMemoCapacity => ("kernel.memo_capacity", Count),
    KernelMemoRetainedBytes => ("kernel.memo_retained_bytes", Bytes),
    KernelMemoInsertionStops => ("kernel.memo_insertion_stops", Count),
    KernelMemoEligibleCalls => ("kernel.memo_eligible_calls", Count),
    KernelMemoIneligibleBorrowed => ("kernel.memo_ineligible_borrowed", Count),
    KernelMemoIneligibleFresh => ("kernel.memo_ineligible_fresh", Count),
    KernelMemoIneligibleDiagnosed => ("kernel.memo_ineligible_diagnosed", Count),
    KernelMemoIdentityCapacityStops => ("kernel.memo_identity_capacity_stops", Count),
    KernelMemoLogicalFuelReplayed => ("kernel.memo_logical_fuel_replayed", Count),
    KernelMemoBypassedCallBodies => ("kernel.memo_bypassed_call_bodies", Count),
    KernelMemoProbeLookups => ("kernel.memo_probe_lookups", Count),
    KernelMemoProbeRepetitions => ("kernel.memo_probe_repetitions", Count),
    KernelMemoProbeInserts => ("kernel.memo_probe_inserts", Count),
    KernelMemoProbeCapacityStops => ("kernel.memo_probe_capacity_stops", Count),
    KernelMemoProbeTruncated => ("kernel.memo_probe_truncated", Count),
    CacheContextOff => ("cache.context_off", Count),
    CacheContextHits => ("cache.context_hits", Count),
    CacheContextMisses => ("cache.context_misses", Count),
    CacheLivePrerequisiteChecks => ("cache.live_prerequisite_checks", Count),
    CacheAvoidedRecursiveChecks => ("cache.avoided_recursive_checks", Count),
    CacheAvoidedDependencyChecks => ("cache.avoided_dependency_checks", Count),
    CacheAvoidedKernelChecks => ("cache.avoided_kernel_checks", Count),
    CacheReconstructionElapsed => ("cache.reconstruction_elapsed", Nanoseconds),
    CacheFreshTargetElapsed => ("cache.fresh_target_elapsed", Nanoseconds),
    PackageModulesDecoded => ("package.modules_decoded", Count),
    PackageModulesChecked => ("package.modules_checked", Count),
    PackageCertificateBytes => ("package.certificate_bytes", Bytes),
    PackageDeclarations => ("package.declarations", Count),
    PackageImports => ("package.imports", Count),
    PackageLiveResults => ("package.live_results", Count),
    PackageCacheResults => ("package.cache_results", Count),
    PackageMemoResults => ("package.memo_results", Count),
    PackageDecodeCacheHits => ("package.decode_cache_hits", Count),
    PackageDecodeCacheMisses => ("package.decode_cache_misses", Count),
    PackageRequestedJobs => ("package.requested_jobs", Count),
    PackageEffectiveJobs => ("package.effective_jobs", Count),
    PackageSharedBaseContextBytes => ("package.shared_base_context_bytes", Bytes),
    PackageAvoidedBaseContextClones => ("package.avoided_base_context_clones", Count),
    PackageAvoidedBaseContextCloneBytes => ("package.avoided_base_context_clone_bytes", Bytes),
    PackageWorkerActiveElapsed => ("package.worker_active_elapsed", Nanoseconds),
    PackageWorkerIdleElapsed => ("package.worker_idle_elapsed", Nanoseconds),
    PackageCoordinatorMergeElapsed => ("package.coordinator_merge_elapsed", Nanoseconds),
    PackageRefreshCandidates => ("package.refresh_candidates", Count),
    PackageSourceRebuilds => ("package.source_rebuilds", Count),
    PackageCertificateRebinds => ("package.certificate_rebinds", Count),
    PackageUnchangedModules => ("package.unchanged_modules", Count),
    PackageFallbacks => ("package.fallbacks", Count),
    PackageSourceHashScans => ("package.source_hash_scans", Count),
    PackageInterfaceReconstructions => ("package.interface_reconstructions", Count),
    PackageShardEstimatedCost => ("package.shard_estimated_cost", Count),
    PackageShardElapsed => ("package.shard_elapsed", Nanoseconds),
    PackageShardModules => ("package.shard_modules", Count),
    PackageShardBytes => ("package.shard_bytes", Bytes),
    PackageDagCriticalPathLayers => ("package.dag_critical_path_layers", Count),
    PackageDagLayerWidth => ("package.dag_layer_width", Count),
    PackageDagLayerElapsed => ("package.dag_layer_elapsed", Nanoseconds),
}

/// One aggregate counter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceMeasurementCounter {
    pub label: PerformanceMeasurementLabel,
    pub unit: PerformanceMeasurementUnit,
    pub value: u64,
}

/// Bounded detail accounting for one record family.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PerformanceDetailCounts {
    pub attempted: u64,
    pub retained: u64,
    pub omitted: u64,
}

/// Detailed module measurement. No source or proof text is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceModuleMeasurement {
    pub module: String,
    pub certificate_bytes: u64,
    pub declaration_count: u64,
    pub import_count: u64,
    pub checker_elapsed_ns: u64,
    pub package_sharding: Option<PerformancePackageModuleShardingMeasurement>,
}

/// Cost-model and shard assignment detail for one package module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PerformancePackageShardCostModel {
    FastShardCostV1,
}

impl PerformancePackageShardCostModel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastShardCostV1 => "npa.fast-shard-cost.v1",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PerformancePackageShardMemoryModel {
    FastShardMemoryV1,
}

impl PerformancePackageShardMemoryModel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastShardMemoryV1 => "npa.fast-shard-memory.v1",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PerformancePackageShardReductionReason {
    None,
    RequestedOne,
    RunnableWidth,
    MemoryBudget,
    EstimateOverflow,
}

impl PerformancePackageShardReductionReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::RequestedOne => "requested_one",
            Self::RunnableWidth => "runnable_width",
            Self::MemoryBudget => "memory_budget",
            Self::EstimateOverflow => "estimate_overflow",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PerformancePackageModuleShardingMeasurement {
    pub cost_model: PerformancePackageShardCostModel,
    pub artifact_bytes: u64,
    pub direct_import_count: u64,
    pub estimated_cost: u64,
    pub layer_index: Option<u64>,
    pub shard_index: Option<u64>,
    pub cost_overflowed: bool,
    pub critical_path: bool,
}

/// Detailed declaration measurement. Proof terms and source text are never
/// retained; the canonical key is module, declaration index, then name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceDeclarationMeasurement {
    pub module: String,
    pub declaration_index: u64,
    pub declaration: String,
    pub term_nodes: u64,
    pub elaboration_elapsed_ns: u64,
}

/// Stable outcome for a measured candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PerformanceCandidateOutcome {
    Accepted,
    Rejected,
    NotEvaluated,
}

impl PerformanceCandidateOutcome {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::NotEvaluated => "not_evaluated",
        }
    }
}

/// Detailed candidate measurement keyed by batch and input index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceCandidateMeasurement {
    pub batch_index: u64,
    pub candidate_index: u64,
    pub validation_elapsed_ns: u64,
    pub execution_elapsed_ns: u64,
    pub outcome: PerformanceCandidateOutcome,
}

/// Detailed worker or shard measurement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceWorkerMeasurement {
    pub worker_index: u64,
    pub module_count: u64,
    pub certificate_bytes: u64,
    pub active_elapsed_ns: u64,
    pub idle_elapsed_ns: u64,
}

/// Detailed deterministic package DAG layer measurement.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PerformancePackageLayerMeasurement {
    pub layer_index: u64,
    pub runnable_width: u64,
    pub estimated_total_cost: u64,
    pub estimated_max_shard_cost: u64,
    pub requested_jobs: u64,
    pub effective_jobs: u64,
    pub reduction_reason: PerformancePackageShardReductionReason,
    pub shared_base_context_bytes: u64,
    pub per_worker_bytes: u64,
    pub memory_budget_bytes: u64,
    pub estimate_overflowed: bool,
    pub elapsed_ns: u64,
}

/// Detailed deterministic package shard measurement.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PerformancePackageShardMeasurement {
    pub layer_index: u64,
    pub shard_index: u64,
    pub estimated_cost: u64,
    pub artifact_bytes: u64,
    pub member_count: u64,
    pub active_elapsed_ns: u64,
    pub estimate_overflowed: bool,
}

/// Operation-wide package sharding model and critical-path summary.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PerformancePackageShardingMeasurement {
    pub cost_model: PerformancePackageShardCostModel,
    pub memory_model: PerformancePackageShardMemoryModel,
    pub import_weight: u64,
    pub memory_budget_bytes: u64,
    pub fixed_worker_bytes: u64,
    pub scratch_multiplier: u64,
    pub requested_jobs: u64,
    pub effective_jobs: u64,
    pub reduction_reason: PerformancePackageShardReductionReason,
    pub shared_base_context_bytes: u64,
    pub per_worker_bytes: u64,
    pub avoided_base_context_clone_bytes: u64,
    pub estimate_overflowed: bool,
    pub critical_path_cost: u64,
    pub critical_path_module_count: u64,
    pub critical_path_identity: String,
    pub critical_path_checker_elapsed_ns: u64,
    pub barrier_elapsed_ns: u64,
}

/// Clock metadata for elapsed measurements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PerformanceClockMetadata {
    pub source: &'static str,
    pub resolution_ns: u64,
    pub coarse_stage_reads: u64,
}

/// Common diagnostic-only report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceMeasurementReport {
    pub schema: &'static str,
    pub trusted: bool,
    pub proof_evidence: bool,
    pub mode: PerformanceMeasurementMode,
    pub input_identity: Option<String>,
    pub counters: Vec<PerformanceMeasurementCounter>,
    pub modules: Vec<PerformanceModuleMeasurement>,
    pub module_details: PerformanceDetailCounts,
    pub declarations: Vec<PerformanceDeclarationMeasurement>,
    pub declaration_details: PerformanceDetailCounts,
    pub candidates: Vec<PerformanceCandidateMeasurement>,
    pub candidate_details: PerformanceDetailCounts,
    pub workers: Vec<PerformanceWorkerMeasurement>,
    pub worker_details: PerformanceDetailCounts,
    pub package_sharding: Option<PerformancePackageShardingMeasurement>,
    pub package_layers: Vec<PerformancePackageLayerMeasurement>,
    pub package_layer_details: PerformanceDetailCounts,
    pub package_shards: Vec<PerformancePackageShardMeasurement>,
    pub package_shard_details: PerformanceDetailCounts,
    pub detail_truncated: bool,
    pub overflowed: bool,
    pub clock: PerformanceClockMetadata,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PerformanceMeasurementState {
    counters: BTreeMap<PerformanceMeasurementLabel, u64>,
    modules: Option<BTreeMap<String, PerformanceModuleMeasurement>>,
    module_attempted: u64,
    declarations: Option<BTreeMap<(String, u64, String), PerformanceDeclarationMeasurement>>,
    declaration_attempted: u64,
    candidates: Option<BTreeMap<(u64, u64), PerformanceCandidateMeasurement>>,
    candidate_attempted: u64,
    workers: Option<BTreeMap<u64, PerformanceWorkerMeasurement>>,
    worker_attempted: u64,
    package_sharding: Option<PerformancePackageShardingMeasurement>,
    package_layers: Option<BTreeMap<u64, PerformancePackageLayerMeasurement>>,
    package_layer_attempted: u64,
    package_shards: Option<BTreeMap<(u64, u64), PerformancePackageShardMeasurement>>,
    package_shard_attempted: u64,
    overflowed: bool,
    coarse_stage_reads: u64,
}

/// Operation-scoped bounded recorder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceMeasurementRecorder {
    mode: PerformanceMeasurementMode,
    input_identity: Option<String>,
    state: Option<PerformanceMeasurementState>,
}

impl PerformanceMeasurementRecorder {
    pub fn new(mode: PerformanceMeasurementMode) -> Self {
        let state = mode.is_enabled().then(|| PerformanceMeasurementState {
            modules: mode.is_detailed().then(BTreeMap::new),
            declarations: mode.is_detailed().then(BTreeMap::new),
            candidates: mode.is_detailed().then(BTreeMap::new),
            workers: mode.is_detailed().then(BTreeMap::new),
            package_layers: mode.is_detailed().then(BTreeMap::new),
            package_shards: mode.is_detailed().then(BTreeMap::new),
            ..PerformanceMeasurementState::default()
        });
        Self {
            mode,
            input_identity: None,
            state,
        }
    }

    pub fn with_input_identity(mut self, identity: impl Into<String>) -> Self {
        if self.mode.is_enabled() {
            self.input_identity = Some(identity.into());
        }
        self
    }

    pub const fn mode(&self) -> PerformanceMeasurementMode {
        self.mode
    }

    pub const fn is_enabled(&self) -> bool {
        self.mode.is_enabled()
    }

    /// Read the monotonic clock only when measurement is enabled.
    pub fn start_timer(&mut self) -> Option<Instant> {
        let state = self.state.as_mut()?;
        saturating_increment(&mut state.coarse_stage_reads, &mut state.overflowed);
        Some(Instant::now())
    }

    pub fn elapsed_ns(started: Option<Instant>) -> u64 {
        started
            .map(|started| u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX))
            .unwrap_or(0)
    }

    /// Account for coarse clocks read by a lower-level crate-local meter.
    pub fn observe_coarse_stage_clock_reads(&mut self, reads: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        saturating_add(&mut state.coarse_stage_reads, reads, &mut state.overflowed);
    }

    pub fn add_counter(&mut self, label: PerformanceMeasurementLabel, value: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        let counter = state.counters.entry(label).or_default();
        let (next, overflowed) = counter.overflowing_add(value);
        if overflowed {
            *counter = u64::MAX;
            state.overflowed = true;
        } else {
            *counter = next;
        }
    }

    pub(crate) fn mark_overflowed(&mut self) {
        if let Some(state) = self.state.as_mut() {
            state.overflowed = true;
        }
    }

    /// Adapt lower-level kernel counters without making the kernel depend on
    /// this reporting schema.
    pub fn observe_kernel_work_counters(&mut self, counters: KernelWorkCounters) {
        for (label, value) in [
            (
                PerformanceMeasurementLabel::KernelCheckCalls,
                counters.check_calls,
            ),
            (
                PerformanceMeasurementLabel::KernelInferCalls,
                counters.infer_calls,
            ),
            (
                PerformanceMeasurementLabel::KernelWhnfCalls,
                counters.whnf_calls,
            ),
            (
                PerformanceMeasurementLabel::KernelDefeqCalls,
                counters.defeq_calls,
            ),
            (
                PerformanceMeasurementLabel::KernelQuickEqualityHits,
                counters.quick_equality_hits,
            ),
            (
                PerformanceMeasurementLabel::KernelBetaSteps,
                counters.beta_steps,
            ),
            (
                PerformanceMeasurementLabel::KernelDeltaSteps,
                counters.delta_steps,
            ),
            (
                PerformanceMeasurementLabel::KernelIotaSteps,
                counters.iota_steps,
            ),
            (
                PerformanceMeasurementLabel::KernelZetaSteps,
                counters.zeta_steps,
            ),
            (
                PerformanceMeasurementLabel::KernelLogicalFuel,
                counters.logical_fuel,
            ),
            (
                PerformanceMeasurementLabel::KernelSuccessfulFuel,
                counters.successful_fuel,
            ),
            (
                PerformanceMeasurementLabel::KernelExhaustedFuel,
                counters.exhausted_fuel,
            ),
            (
                PerformanceMeasurementLabel::KernelPhysicalReductions,
                counters.physical_reductions,
            ),
            (
                PerformanceMeasurementLabel::KernelContextLookups,
                counters.context_lookups,
            ),
            (
                PerformanceMeasurementLabel::KernelContextShifts,
                counters.context_shifts,
            ),
        ] {
            self.add_counter(label, value);
        }
        let observed_memo_or_probe = counters.memo_entry_capacity != 0
            || counters.memo_eligible_calls != 0
            || counters.memo_ineligible_borrowed != 0
            || counters.memo_ineligible_fresh != 0
            || counters.memo_ineligible_diagnosed != 0
            || counters.memo_identity_capacity_stops != 0
            || counters.memo_probe_lookups != 0
            || counters.memo_probe_capacity_stops != 0
            || counters.memo_probe_truncated;
        if observed_memo_or_probe {
            let (memo_hits, hits_overflowed) =
                saturating_sum([counters.whnf_memo_hits, counters.defeq_memo_hits]);
            let (memo_misses, misses_overflowed) =
                saturating_sum([counters.whnf_memo_misses, counters.defeq_memo_misses]);
            let (memo_inserts, inserts_overflowed) =
                saturating_sum([counters.whnf_memo_inserts, counters.defeq_memo_inserts]);
            let (memo_stops, stops_overflowed) = saturating_sum([
                counters.memo_identity_capacity_stops,
                counters.whnf_memo_capacity_stops,
                counters.defeq_memo_capacity_stops,
            ]);
            let aggregation_overflowed =
                hits_overflowed || misses_overflowed || inserts_overflowed || stops_overflowed;
            for (label, value) in [
                (PerformanceMeasurementLabel::KernelMemoHits, memo_hits),
                (PerformanceMeasurementLabel::KernelMemoMisses, memo_misses),
                (PerformanceMeasurementLabel::KernelMemoInserts, memo_inserts),
                (
                    PerformanceMeasurementLabel::KernelMemoCapacity,
                    counters.memo_entry_capacity,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoRetainedBytes,
                    counters.memo_retained_bytes,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoInsertionStops,
                    memo_stops,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoEligibleCalls,
                    counters.memo_eligible_calls,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoIneligibleBorrowed,
                    counters.memo_ineligible_borrowed,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoIneligibleFresh,
                    counters.memo_ineligible_fresh,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoIneligibleDiagnosed,
                    counters.memo_ineligible_diagnosed,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoIdentityCapacityStops,
                    counters.memo_identity_capacity_stops,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoLogicalFuelReplayed,
                    counters.memo_logical_fuel_replayed,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoBypassedCallBodies,
                    counters.memo_bypassed_call_bodies,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoProbeLookups,
                    counters.memo_probe_lookups,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoProbeRepetitions,
                    counters.memo_probe_repetitions,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoProbeInserts,
                    counters.memo_probe_inserts,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoProbeCapacityStops,
                    counters.memo_probe_capacity_stops,
                ),
                (
                    PerformanceMeasurementLabel::KernelMemoProbeTruncated,
                    u64::from(counters.memo_probe_truncated),
                ),
            ] {
                self.add_counter(label, value);
            }
            if aggregation_overflowed {
                self.mark_overflowed();
            }
        }
        if counters.overflowed {
            if let Some(state) = self.state.as_mut() {
                state.overflowed = true;
            }
        }
    }

    pub fn record_module(&mut self, measurement: PerformanceModuleMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.modules.is_none() {
            return;
        }
        saturating_increment(&mut state.module_attempted, &mut state.overflowed);
        let modules = state
            .modules
            .as_mut()
            .expect("detailed module storage exists");
        modules.insert(measurement.module.clone(), measurement);
        truncate_last(modules, PERFORMANCE_MODULE_DETAIL_LIMIT);
    }

    pub fn record_declaration(&mut self, measurement: PerformanceDeclarationMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.declarations.is_none() {
            return;
        }
        saturating_increment(&mut state.declaration_attempted, &mut state.overflowed);
        let declarations = state
            .declarations
            .as_mut()
            .expect("detailed declaration storage exists");
        declarations.insert(
            (
                measurement.module.clone(),
                measurement.declaration_index,
                measurement.declaration.clone(),
            ),
            measurement,
        );
        truncate_last(declarations, PERFORMANCE_DECLARATION_DETAIL_LIMIT);
    }

    pub(crate) fn observe_declaration_attempts(&mut self, count: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.declarations.is_none() {
            return;
        }
        saturating_add(
            &mut state.declaration_attempted,
            count,
            &mut state.overflowed,
        );
    }

    pub fn record_candidate(&mut self, measurement: PerformanceCandidateMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.candidates.is_none() {
            return;
        }
        saturating_increment(&mut state.candidate_attempted, &mut state.overflowed);
        self.update_candidate(measurement);
    }

    pub(crate) fn observe_candidate_attempts(&mut self, count: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.candidates.is_none() {
            return;
        }
        saturating_add(&mut state.candidate_attempted, count, &mut state.overflowed);
    }

    pub(crate) fn update_candidate(&mut self, measurement: PerformanceCandidateMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        let Some(candidates) = state.candidates.as_mut() else {
            return;
        };
        let key = (measurement.batch_index, measurement.candidate_index);
        if let Some(existing) = candidates.get_mut(&key) {
            if measurement.validation_elapsed_ns != 0 {
                existing.validation_elapsed_ns = measurement.validation_elapsed_ns;
            }
            if measurement.execution_elapsed_ns != 0 {
                existing.execution_elapsed_ns = measurement.execution_elapsed_ns;
            }
            if measurement.outcome != PerformanceCandidateOutcome::NotEvaluated {
                existing.outcome = measurement.outcome;
            }
        } else {
            candidates.insert(key, measurement);
        }
        truncate_last(candidates, PERFORMANCE_CANDIDATE_DETAIL_LIMIT);
    }

    pub fn record_worker(&mut self, measurement: PerformanceWorkerMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.workers.is_none() {
            return;
        }
        saturating_increment(&mut state.worker_attempted, &mut state.overflowed);
        let workers = state
            .workers
            .as_mut()
            .expect("detailed worker storage exists");
        workers.insert(measurement.worker_index, measurement);
        truncate_last(workers, PERFORMANCE_WORKER_DETAIL_LIMIT);
    }

    pub(crate) fn observe_worker_attempts(&mut self, count: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.workers.is_none() {
            return;
        }
        saturating_add(&mut state.worker_attempted, count, &mut state.overflowed);
    }

    pub fn set_package_sharding(&mut self, measurement: PerformancePackageShardingMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        match state.package_sharding.as_mut() {
            Some(existing) if existing != &measurement => {
                state.overflowed = true;
                if measurement < *existing {
                    *existing = measurement;
                }
            }
            Some(_) => {}
            None => state.package_sharding = Some(measurement),
        }
    }

    pub fn record_package_layer(&mut self, measurement: PerformancePackageLayerMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        let Some(layers) = state.package_layers.as_mut() else {
            return;
        };
        saturating_increment(&mut state.package_layer_attempted, &mut state.overflowed);
        layers.insert(measurement.layer_index, measurement);
        truncate_last(layers, PERFORMANCE_MODULE_DETAIL_LIMIT);
    }

    pub(crate) fn observe_package_layer_attempts(&mut self, count: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.package_layers.is_none() {
            return;
        }
        saturating_add(
            &mut state.package_layer_attempted,
            count,
            &mut state.overflowed,
        );
    }

    pub fn record_package_shard(&mut self, measurement: PerformancePackageShardMeasurement) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        let Some(shards) = state.package_shards.as_mut() else {
            return;
        };
        saturating_increment(&mut state.package_shard_attempted, &mut state.overflowed);
        shards.insert(
            (measurement.layer_index, measurement.shard_index),
            measurement,
        );
        truncate_last(shards, PERFORMANCE_WORKER_DETAIL_LIMIT);
    }

    pub(crate) fn observe_package_shard_attempts(&mut self, count: u64) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        if state.package_shards.is_none() {
            return;
        }
        saturating_add(
            &mut state.package_shard_attempted,
            count,
            &mut state.overflowed,
        );
    }

    /// Merge a completed report. Canonical first-N retention is independent of
    /// worker completion order.
    pub fn merge(&mut self, report: &PerformanceMeasurementReport) {
        if !self.mode.is_enabled() {
            return;
        }
        if let Some(state) = self.state.as_mut() {
            saturating_add(
                &mut state.coarse_stage_reads,
                report.clock.coarse_stage_reads,
                &mut state.overflowed,
            );
        }
        for counter in &report.counters {
            self.add_counter(counter.label, counter.value);
        }
        for module in &report.modules {
            self.record_module(module.clone());
        }
        for declaration in &report.declarations {
            self.record_declaration(declaration.clone());
        }
        for candidate in &report.candidates {
            self.record_candidate(candidate.clone());
        }
        for worker in &report.workers {
            self.record_worker(worker.clone());
        }
        if let Some(package_sharding) = &report.package_sharding {
            self.set_package_sharding(package_sharding.clone());
        }
        for layer in &report.package_layers {
            self.record_package_layer(layer.clone());
        }
        for shard in &report.package_shards {
            self.record_package_shard(shard.clone());
        }
        if report.overflowed {
            if let Some(state) = self.state.as_mut() {
                state.overflowed = true;
            }
        }
        if let Some(state) = self.state.as_mut().filter(|state| state.modules.is_some()) {
            saturating_add(
                &mut state.module_attempted,
                report.module_details.omitted,
                &mut state.overflowed,
            );
            saturating_add(
                &mut state.declaration_attempted,
                report.declaration_details.omitted,
                &mut state.overflowed,
            );
            saturating_add(
                &mut state.candidate_attempted,
                report.candidate_details.omitted,
                &mut state.overflowed,
            );
            saturating_add(
                &mut state.worker_attempted,
                report.worker_details.omitted,
                &mut state.overflowed,
            );
            saturating_add(
                &mut state.package_layer_attempted,
                report.package_layer_details.omitted,
                &mut state.overflowed,
            );
            saturating_add(
                &mut state.package_shard_attempted,
                report.package_shard_details.omitted,
                &mut state.overflowed,
            );
        }
    }

    pub fn report(&self) -> Option<PerformanceMeasurementReport> {
        let state = self.state.as_ref()?;
        let mut counters = state
            .counters
            .iter()
            .map(|(label, value)| PerformanceMeasurementCounter {
                label: *label,
                unit: label.unit(),
                value: *value,
            })
            .collect::<Vec<_>>();
        counters.sort_by_key(|counter| counter.label.as_str());
        let modules: Vec<PerformanceModuleMeasurement> = state
            .modules
            .as_ref()
            .map(|records| records.values().cloned().collect())
            .unwrap_or_default();
        let declarations: Vec<PerformanceDeclarationMeasurement> = state
            .declarations
            .as_ref()
            .map(|records| records.values().cloned().collect())
            .unwrap_or_default();
        let candidates: Vec<PerformanceCandidateMeasurement> = state
            .candidates
            .as_ref()
            .map(|records| records.values().cloned().collect())
            .unwrap_or_default();
        let workers: Vec<PerformanceWorkerMeasurement> = state
            .workers
            .as_ref()
            .map(|records| records.values().cloned().collect())
            .unwrap_or_default();
        let package_layers: Vec<PerformancePackageLayerMeasurement> = state
            .package_layers
            .as_ref()
            .map(|records| records.values().cloned().collect())
            .unwrap_or_default();
        let package_shards: Vec<PerformancePackageShardMeasurement> = state
            .package_shards
            .as_ref()
            .map(|records| records.values().cloned().collect())
            .unwrap_or_default();
        let module_details = detail_counts(state.module_attempted, modules.len());
        let declaration_details = detail_counts(state.declaration_attempted, declarations.len());
        let candidate_details = detail_counts(state.candidate_attempted, candidates.len());
        let worker_details = detail_counts(state.worker_attempted, workers.len());
        let package_layer_details =
            detail_counts(state.package_layer_attempted, package_layers.len());
        let package_shard_details =
            detail_counts(state.package_shard_attempted, package_shards.len());
        Some(PerformanceMeasurementReport {
            schema: PERFORMANCE_MEASUREMENTS_SCHEMA,
            trusted: false,
            proof_evidence: false,
            mode: self.mode,
            input_identity: self.input_identity.clone(),
            counters,
            modules,
            module_details,
            declarations,
            declaration_details,
            candidates,
            candidate_details,
            workers,
            worker_details,
            package_sharding: state.package_sharding.clone(),
            package_layers,
            package_layer_details,
            package_shards,
            package_shard_details,
            detail_truncated: module_details.omitted > 0
                || declaration_details.omitted > 0
                || candidate_details.omitted > 0
                || worker_details.omitted > 0
                || package_layer_details.omitted > 0
                || package_shard_details.omitted > 0,
            overflowed: state.overflowed,
            clock: PerformanceClockMetadata {
                source: "std.monotonic.instant",
                resolution_ns: 1,
                coarse_stage_reads: state.coarse_stage_reads,
            },
        })
    }
}

fn saturating_increment(value: &mut u64, overflowed: &mut bool) {
    if *value == u64::MAX {
        *overflowed = true;
    } else {
        *value += 1;
    }
}

fn saturating_add(value: &mut u64, amount: u64, overflowed: &mut bool) {
    let (next, did_overflow) = value.overflowing_add(amount);
    if did_overflow {
        *value = u64::MAX;
        *overflowed = true;
    } else {
        *value = next;
    }
}

fn saturating_sum(values: impl IntoIterator<Item = u64>) -> (u64, bool) {
    let mut value = 0;
    let mut overflowed = false;
    for amount in values {
        saturating_add(&mut value, amount, &mut overflowed);
    }
    (value, overflowed)
}

fn truncate_last<K: Ord + Clone, V>(records: &mut BTreeMap<K, V>, limit: usize) {
    while records.len() > limit {
        let key = records
            .last_key_value()
            .map(|(key, _)| key.clone())
            .expect("over-limit detail map is nonempty");
        records.remove(&key);
    }
}

fn detail_counts(attempted: u64, retained: usize) -> PerformanceDetailCounts {
    let retained = u64::try_from(retained).unwrap_or(u64::MAX);
    PerformanceDetailCounts {
        attempted,
        retained,
        omitted: attempted.saturating_sub(retained),
    }
}

/// Render canonical JSON for the common measurement block.
pub fn performance_measurement_report_json(report: &PerformanceMeasurementReport) -> String {
    let counters = report
        .counters
        .iter()
        .map(|counter| {
            format!(
                "{{\"label\":\"{}\",\"unit\":\"{}\",\"value\":{}}}",
                counter.label.as_str(),
                counter.unit.as_str(),
                counter.value
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let modules = report
        .modules
        .iter()
        .map(|module| {
            format!(
                "{{\"module\":\"{}\",\"certificate_bytes\":{},\"declaration_count\":{},\"import_count\":{},\"checker_elapsed_ns\":{},\"package_sharding\":{}}}",
                json_escape(&module.module), module.certificate_bytes, module.declaration_count,
                module.import_count, module.checker_elapsed_ns,
                package_module_sharding_json(module.package_sharding.as_ref())
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let declarations = report
        .declarations
        .iter()
        .map(|declaration| {
            format!(
                "{{\"module\":\"{}\",\"declaration_index\":{},\"declaration\":\"{}\",\"term_nodes\":{},\"elaboration_elapsed_ns\":{}}}",
                json_escape(&declaration.module),
                declaration.declaration_index,
                json_escape(&declaration.declaration),
                declaration.term_nodes,
                declaration.elaboration_elapsed_ns
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let candidates = report
        .candidates
        .iter()
        .map(|candidate| {
            format!(
                "{{\"batch_index\":{},\"candidate_index\":{},\"validation_elapsed_ns\":{},\"execution_elapsed_ns\":{},\"outcome\":\"{}\"}}",
                candidate.batch_index, candidate.candidate_index,
                candidate.validation_elapsed_ns, candidate.execution_elapsed_ns,
                candidate.outcome.as_str()
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let workers = report
        .workers
        .iter()
        .map(|worker| {
            format!(
                "{{\"worker_index\":{},\"module_count\":{},\"certificate_bytes\":{},\"active_elapsed_ns\":{},\"idle_elapsed_ns\":{}}}",
                worker.worker_index, worker.module_count, worker.certificate_bytes,
                worker.active_elapsed_ns, worker.idle_elapsed_ns
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let package_sharding = report
        .package_sharding
        .as_ref()
        .map(package_sharding_json)
        .unwrap_or_else(|| "null".to_owned());
    let package_layers = report
        .package_layers
        .iter()
        .map(|layer| {
            format!(
                "{{\"layer_index\":{},\"runnable_width\":{},\"estimated_total_cost\":{},\"estimated_max_shard_cost\":{},\"requested_jobs\":{},\"effective_jobs\":{},\"reduction_reason\":\"{}\",\"shared_base_context_bytes\":{},\"per_worker_bytes\":{},\"memory_budget_bytes\":{},\"estimate_overflowed\":{},\"elapsed_ns\":{}}}",
                layer.layer_index,
                layer.runnable_width,
                layer.estimated_total_cost,
                layer.estimated_max_shard_cost,
                layer.requested_jobs,
                layer.effective_jobs,
                layer.reduction_reason.as_str(),
                layer.shared_base_context_bytes,
                layer.per_worker_bytes,
                layer.memory_budget_bytes,
                layer.estimate_overflowed,
                layer.elapsed_ns,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let package_shards = report
        .package_shards
        .iter()
        .map(|shard| {
            format!(
                "{{\"layer_index\":{},\"shard_index\":{},\"estimated_cost\":{},\"artifact_bytes\":{},\"member_count\":{},\"active_elapsed_ns\":{},\"estimate_overflowed\":{}}}",
                shard.layer_index,
                shard.shard_index,
                shard.estimated_cost,
                shard.artifact_bytes,
                shard.member_count,
                shard.active_elapsed_ns,
                shard.estimate_overflowed,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let identity = report
        .input_identity
        .as_ref()
        .map(|identity| format!("\"{}\"", json_escape(identity)))
        .unwrap_or_else(|| "null".to_owned());
    format!(
        "{{\"schema\":\"{}\",\"trusted\":false,\"proof_evidence\":false,\"mode\":\"{}\",\"input_identity\":{},\"counters\":[{}],\"modules\":[{}],\"module_details\":{},\"declarations\":[{}],\"declaration_details\":{},\"candidates\":[{}],\"candidate_details\":{},\"workers\":[{}],\"worker_details\":{},\"package_sharding\":{},\"package_layers\":[{}],\"package_layer_details\":{},\"package_shards\":[{}],\"package_shard_details\":{},\"detail_truncated\":{},\"overflowed\":{},\"clock\":{{\"source\":\"{}\",\"resolution_ns\":{},\"coarse_stage_reads\":{}}}}}",
        report.schema,
        report.mode.as_str(),
        identity,
        counters,
        modules,
        detail_counts_json(report.module_details),
        declarations,
        detail_counts_json(report.declaration_details),
        candidates,
        detail_counts_json(report.candidate_details),
        workers,
        detail_counts_json(report.worker_details),
        package_sharding,
        package_layers,
        detail_counts_json(report.package_layer_details),
        package_shards,
        detail_counts_json(report.package_shard_details),
        report.detail_truncated,
        report.overflowed,
        report.clock.source,
        report.clock.resolution_ns,
        report.clock.coarse_stage_reads,
    )
}

fn package_module_sharding_json(
    measurement: Option<&PerformancePackageModuleShardingMeasurement>,
) -> String {
    measurement.map_or_else(
        || "null".to_owned(),
        |measurement| {
            format!(
                "{{\"cost_model\":\"{}\",\"artifact_bytes\":{},\"direct_import_count\":{},\"estimated_cost\":{},\"layer_index\":{},\"shard_index\":{},\"cost_overflowed\":{},\"critical_path\":{}}}",
                measurement.cost_model.as_str(),
                measurement.artifact_bytes,
                measurement.direct_import_count,
                measurement.estimated_cost,
                optional_u64_json(measurement.layer_index),
                optional_u64_json(measurement.shard_index),
                measurement.cost_overflowed,
                measurement.critical_path,
            )
        },
    )
}

fn package_sharding_json(measurement: &PerformancePackageShardingMeasurement) -> String {
    format!(
        "{{\"cost_model\":\"{}\",\"memory_model\":\"{}\",\"import_weight\":{},\"memory_budget_bytes\":{},\"fixed_worker_bytes\":{},\"scratch_multiplier\":{},\"requested_jobs\":{},\"effective_jobs\":{},\"reduction_reason\":\"{}\",\"shared_base_context_bytes\":{},\"per_worker_bytes\":{},\"avoided_base_context_clone_bytes\":{},\"estimate_overflowed\":{},\"critical_path_cost\":{},\"critical_path_module_count\":{},\"critical_path_identity\":\"{}\",\"critical_path_checker_elapsed_ns\":{},\"barrier_elapsed_ns\":{}}}",
        measurement.cost_model.as_str(),
        measurement.memory_model.as_str(),
        measurement.import_weight,
        measurement.memory_budget_bytes,
        measurement.fixed_worker_bytes,
        measurement.scratch_multiplier,
        measurement.requested_jobs,
        measurement.effective_jobs,
        measurement.reduction_reason.as_str(),
        measurement.shared_base_context_bytes,
        measurement.per_worker_bytes,
        measurement.avoided_base_context_clone_bytes,
        measurement.estimate_overflowed,
        measurement.critical_path_cost,
        measurement.critical_path_module_count,
        json_escape(&measurement.critical_path_identity),
        measurement.critical_path_checker_elapsed_ns,
        measurement.barrier_elapsed_ns,
    )
}

fn optional_u64_json(value: Option<u64>) -> String {
    value.map_or_else(|| "null".to_owned(), |value| value.to_string())
}

fn detail_counts_json(counts: PerformanceDetailCounts) -> String {
    format!(
        "{{\"attempted\":{},\"retained\":{},\"omitted\":{}}}",
        counts.attempted, counts.retained, counts.omitted
    )
}

fn json_escape(value: &str) -> String {
    let mut out = String::new();
    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            control if control.is_control() => {
                out.push_str(&format!("\\u{:04x}", control as u32));
            }
            other => out.push(other),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};

    #[test]
    fn label_table_is_exhaustive_unique_and_canonical() {
        let mut identifiers = PerformanceMeasurementLabel::ALL
            .iter()
            .map(|label| label.as_str())
            .collect::<Vec<_>>();
        identifiers.sort_unstable();
        assert!(identifiers.windows(2).all(|pair| pair[0] != pair[1]));
        assert!(identifiers.iter().all(|identifier| {
            identifier.contains('.')
                && identifier
                    .bytes()
                    .all(|byte| byte.is_ascii_lowercase() || byte == b'.' || byte == b'_')
        }));
        let snapshot = PerformanceMeasurementLabel::ALL
            .iter()
            .map(|label| format!("{}:{}", label.as_str(), label.unit().as_str()))
            .collect::<Vec<_>>()
            .join("\n");
        let snapshot_hash = format!("{:x}", Sha256::digest(snapshot.as_bytes()));
        assert_eq!(
            snapshot_hash,
            "990ced2b480dd75275e3a10dddda7f01171cd6527aaa1b84117ca503f36c3400"
        );
    }

    #[test]
    fn disabled_mode_has_no_state_clock_reads_or_report() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Off);
        assert!(recorder.start_timer().is_none());
        recorder.add_counter(PerformanceMeasurementLabel::CandidateSubmitted, 1);
        recorder.record_module(module("B"));
        assert!(recorder.state.is_none());
        assert!(recorder.report().is_none());
    }

    #[test]
    fn summary_mode_does_not_allocate_or_report_omitted_details() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.record_module(module("A"));
        recorder.record_candidate(PerformanceCandidateMeasurement {
            batch_index: 0,
            candidate_index: 0,
            validation_elapsed_ns: 1,
            execution_elapsed_ns: 1,
            outcome: PerformanceCandidateOutcome::Accepted,
        });
        let report = recorder.report().unwrap();
        assert!(report.modules.is_empty());
        assert!(report.candidates.is_empty());
        assert_eq!(report.module_details, PerformanceDetailCounts::default());
        assert_eq!(report.candidate_details, PerformanceDetailCounts::default());
        assert!(!report.detail_truncated);
    }

    #[test]
    fn detailed_retention_keeps_canonical_first_keys() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        for index in (0..PERFORMANCE_CANDIDATE_DETAIL_LIMIT + 4).rev() {
            recorder.record_candidate(PerformanceCandidateMeasurement {
                batch_index: 0,
                candidate_index: index as u64,
                validation_elapsed_ns: index as u64,
                execution_elapsed_ns: 0,
                outcome: PerformanceCandidateOutcome::Rejected,
            });
        }
        let report = recorder.report().unwrap();
        assert_eq!(report.candidates.len(), PERFORMANCE_CANDIDATE_DETAIL_LIMIT);
        assert_eq!(report.candidates.first().unwrap().candidate_index, 0);
        assert_eq!(
            report.candidates.last().unwrap().candidate_index,
            PERFORMANCE_CANDIDATE_DETAIL_LIMIT as u64 - 1
        );
        assert_eq!(report.candidate_details.omitted, 4);
        assert!(report.detail_truncated);
    }

    #[test]
    fn merge_is_independent_of_completion_order() {
        fn worker(modules: &[&str]) -> PerformanceMeasurementReport {
            let mut recorder =
                PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
            recorder.observe_coarse_stage_clock_reads(modules.len() as u64);
            for name in modules {
                recorder.record_module(module(name));
            }
            recorder.report().unwrap()
        }
        let first = worker(&["C", "A"]);
        let second = worker(&["D", "B"]);
        let mut left = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        left.merge(&first);
        left.merge(&second);
        let mut right = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        right.merge(&second);
        right.merge(&first);
        let left = left.report().unwrap();
        let right = right.report().unwrap();
        assert_eq!(left, right);
        assert_eq!(left.clock.coarse_stage_reads, 4);
    }

    #[test]
    fn conflicting_package_sharding_summaries_merge_canonically() {
        fn report(barrier_elapsed_ns: u64) -> PerformanceMeasurementReport {
            let mut recorder =
                PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
            recorder.set_package_sharding(package_sharding(barrier_elapsed_ns));
            recorder.report().unwrap()
        }

        let first = report(10);
        let second = report(20);
        let mut left = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        left.merge(&first);
        left.merge(&second);
        let mut right = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        right.merge(&second);
        right.merge(&first);

        let left = left.report().unwrap();
        let right = right.report().unwrap();
        assert_eq!(left, right);
        assert!(left.overflowed);
        assert_eq!(left.package_sharding, Some(package_sharding(10)));
    }

    #[test]
    fn saturation_is_explicit_and_json_is_canonical() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.add_counter(PerformanceMeasurementLabel::KernelLogicalFuel, u64::MAX);
        recorder.add_counter(PerformanceMeasurementLabel::KernelLogicalFuel, 1);
        let report = recorder.report().unwrap();
        assert!(report.overflowed);
        assert_eq!(report.counters[0].value, u64::MAX);
        let json = performance_measurement_report_json(&report);
        assert!(json.starts_with("{\"schema\":\"npa.performance.measurements.v0.2\""));
        assert!(json.contains("\"trusted\":false,\"proof_evidence\":false"));
        assert!(json.contains("\"overflowed\":true"));
    }

    #[test]
    fn kernel_memo_counters_project_only_for_explicit_reuse_operations() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_kernel_work_counters(KernelWorkCounters::default());
        let report = recorder.report().unwrap();
        assert!(report
            .counters
            .iter()
            .all(|counter| counter.label != PerformanceMeasurementLabel::KernelMemoCapacity));

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_kernel_work_counters(KernelWorkCounters {
            memo_ineligible_diagnosed: 1,
            ..KernelWorkCounters::default()
        });
        let report = recorder.report().unwrap();
        assert_eq!(
            report
                .counters
                .iter()
                .find(|counter| {
                    counter.label == PerformanceMeasurementLabel::KernelMemoIneligibleDiagnosed
                })
                .map(|counter| counter.value),
            Some(1)
        );

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_kernel_work_counters(KernelWorkCounters {
            whnf_memo_hits: 2,
            defeq_memo_hits: 3,
            whnf_memo_misses: 4,
            defeq_memo_misses: 5,
            whnf_memo_inserts: 6,
            defeq_memo_inserts: 7,
            memo_entry_capacity: 12_288,
            memo_retained_bytes: 512,
            memo_identity_capacity_stops: 1,
            whnf_memo_capacity_stops: 2,
            defeq_memo_capacity_stops: 3,
            memo_eligible_calls: 17,
            memo_ineligible_borrowed: 18,
            memo_ineligible_fresh: 19,
            memo_ineligible_diagnosed: 20,
            memo_logical_fuel_replayed: 21,
            memo_bypassed_call_bodies: 22,
            memo_probe_lookups: 23,
            memo_probe_repetitions: 24,
            memo_probe_inserts: 25,
            memo_probe_capacity_stops: 4,
            memo_probe_truncated: true,
            ..KernelWorkCounters::default()
        });
        let report = recorder.report().unwrap();
        let value = |label| {
            report
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
        };
        assert_eq!(value(PerformanceMeasurementLabel::KernelMemoHits), Some(5));
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoMisses),
            Some(9)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoInserts),
            Some(13)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoCapacity),
            Some(12_288)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoRetainedBytes),
            Some(512)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoInsertionStops),
            Some(6)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoEligibleCalls),
            Some(17)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoIneligibleBorrowed),
            Some(18)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoIneligibleFresh),
            Some(19)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoIneligibleDiagnosed),
            Some(20)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoIdentityCapacityStops),
            Some(1)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoLogicalFuelReplayed),
            Some(21)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoBypassedCallBodies),
            Some(22)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoProbeLookups),
            Some(23)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoProbeRepetitions),
            Some(24)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoProbeInserts),
            Some(25)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoProbeCapacityStops),
            Some(4)
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::KernelMemoProbeTruncated),
            Some(1)
        );

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_kernel_work_counters(KernelWorkCounters {
            whnf_memo_hits: u64::MAX,
            defeq_memo_hits: 1,
            memo_entry_capacity: 1,
            ..KernelWorkCounters::default()
        });
        let report = recorder.report().unwrap();
        assert!(report.overflowed);
        assert_eq!(
            report
                .counters
                .iter()
                .find(|counter| counter.label == PerformanceMeasurementLabel::KernelMemoHits)
                .map(|counter| counter.value),
            Some(u64::MAX),
        );
    }

    #[test]
    fn real_certificate_verifier_counters_reach_the_common_projection() {
        let level = npa_kernel::Level::param("u");
        let cert = npa_cert::build_module_cert(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.ObservedKernelMemo"),
                declarations: vec![npa_kernel::Decl::Def {
                    name: "Observed.id".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: npa_kernel::Expr::pi(
                        "A",
                        npa_kernel::Expr::sort(level.clone()),
                        npa_kernel::Expr::pi(
                            "x",
                            npa_kernel::Expr::bvar(0),
                            npa_kernel::Expr::bvar(1),
                        ),
                    ),
                    value: npa_kernel::Expr::lam(
                        "A",
                        npa_kernel::Expr::sort(level),
                        npa_kernel::Expr::lam(
                            "x",
                            npa_kernel::Expr::bvar(0),
                            npa_kernel::Expr::bvar(0),
                        ),
                    ),
                    reducibility: npa_kernel::Reducibility::Reducible,
                }],
            },
            &[],
        )
        .unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();
        let mut counters = KernelWorkCounters::default();
        npa_cert::verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
            &bytes,
            &[],
            &npa_cert::AxiomPolicy::normal(),
            npa_kernel::KernelExecutionOptions::repetition_probe(),
            &mut counters,
        )
        .unwrap();
        assert!(counters.check_calls > 0);

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_kernel_work_counters(counters);
        let report = recorder.report().unwrap();
        assert!(report.counters.iter().any(|counter| {
            counter.label == PerformanceMeasurementLabel::KernelMemoCapacity
                && counter.value == 12_288
        }));
        assert!(report.counters.iter().any(|counter| {
            counter.label == PerformanceMeasurementLabel::KernelMemoProbeLookups
        }));
    }

    fn module(name: &str) -> PerformanceModuleMeasurement {
        PerformanceModuleMeasurement {
            module: name.to_owned(),
            certificate_bytes: 1,
            declaration_count: 1,
            import_count: 0,
            checker_elapsed_ns: 1,
            package_sharding: None,
        }
    }

    fn package_sharding(barrier_elapsed_ns: u64) -> PerformancePackageShardingMeasurement {
        PerformancePackageShardingMeasurement {
            cost_model: PerformancePackageShardCostModel::FastShardCostV1,
            memory_model: PerformancePackageShardMemoryModel::FastShardMemoryV1,
            import_weight: 4_096,
            memory_budget_bytes: 1_073_741_824,
            fixed_worker_bytes: 8_388_608,
            scratch_multiplier: 4,
            requested_jobs: 4,
            effective_jobs: 2,
            reduction_reason: PerformancePackageShardReductionReason::RunnableWidth,
            shared_base_context_bytes: 10,
            per_worker_bytes: 20,
            avoided_base_context_clone_bytes: 20,
            estimate_overflowed: false,
            critical_path_cost: 30,
            critical_path_module_count: 2,
            critical_path_identity: format!("sha256:{}", "00".repeat(32)),
            critical_path_checker_elapsed_ns: 40,
            barrier_elapsed_ns,
        }
    }
}
