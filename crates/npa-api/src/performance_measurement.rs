//! Bounded, diagnostic-only performance measurements shared by authoring and
//! package verification.
//!
//! Measurements are deliberately excluded from semantic requests, hashes,
//! certificates, verifier policy, and proof evidence.

use std::collections::BTreeMap;
use std::time::Instant;

use npa_cert::{CertificatePayloadObservation, CertificateTermMaterializationObservation};
use npa_kernel::KernelWorkCounters;
use npa_package::PreparedArtifactRetentionObservation;

use crate::package_verifier::PackagePayloadOwnershipObservation;

/// Stable schema for the common cross-subsystem measurement block.
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1: &str = "npa.performance.measurements.v0.1";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2: &str = "npa.performance.measurements.v0.2";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3: &str = "npa.performance.measurements.v0.3";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4: &str = "npa.performance.measurements.v0.4";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5: &str = "npa.performance.measurements.v0.5";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6: &str = "npa.performance.measurements.v0.6";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7: &str = "npa.performance.measurements.v0.7";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8: &str = "npa.performance.measurements.v0.8";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9: &str = "npa.performance.measurements.v0.9";
pub const PERFORMANCE_MEASUREMENTS_SCHEMA: &str = PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9;
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

/// Batching policy selected for one changed-package Git query operation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum PerformancePackageSelectionBatchPolicy {
    /// Selection returned before a batch policy was needed.
    #[default]
    NotSelected,
    /// Pathspecs were partitioned under the computed exec headroom.
    ExecBudget,
    /// The complete invocation used compatibility 128-path batches.
    Legacy128,
}

/// Deterministic, content-free observation of changed-package selection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PerformancePackageSelectionObservation {
    /// Whether this observation belongs to committed-base selection.
    pub committed_base: bool,
    pub batch_policy: PerformancePackageSelectionBatchPolicy,
    pub candidate_paths: u64,
    pub pathspec_payload_bytes: u64,
    pub effective_argv_charge_bytes: u64,
    pub max_batch_payload_bytes: u64,
    pub max_batch_argv_charge_bytes: u64,
    pub pathspec_batches: u64,
    pub worktree_root_queries: u64,
    pub head_queries: u64,
    pub tracked_queries: u64,
    pub untracked_queries: u64,
    pub tracked_output_paths: u64,
    pub untracked_output_paths: u64,
    pub selected_paths: u64,
    pub base_commit_queries: u64,
    pub committed_head_queries: u64,
    pub merge_base_queries: u64,
    pub base_manifest_blob_bytes: u64,
    pub base_lock_blob_bytes: u64,
    pub protected_candidate_paths: u64,
    pub dirty_paths: u64,
    pub committed_diff_batches: u64,
    pub committed_diff_processes: u64,
    pub committed_diff_output_paths: u64,
    pub seed_modules: u64,
    pub full_escalations: u64,
    /// Big-endian SHA-256 words for the complete canonical escalation-reason list.
    pub full_escalation_reason_identity: [u64; 4],
    pub selected_closure_modules: u64,
    pub overflowed: bool,
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
    (
        $( $variant:ident => ($identifier:literal, $unit:ident) ),+ $(,)?
        ; introduced_later {
            $( $later_variant:ident => ($later_identifier:literal, $later_unit:ident, $introduction_schema:ident) ),+ $(,)?
        }
    ) => {
        /// Closed vocabulary for performance counters.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum PerformanceMeasurementLabel {
            $( $variant, )+
            $( $later_variant, )+
        }

        impl PerformanceMeasurementLabel {
            /// Exhaustive current label table. JSON projection sorts by identifier.
            /// Strict readers must use [`Self::labels_for_schema`] or
            /// [`Self::from_schema_identifier`] instead of this cumulative set.
            pub const ALL: &'static [Self] = &[
                $( Self::$variant, )+
                $( Self::$later_variant, )+
            ];

            /// Closed table recording the first published schema for every label.
            const INTRODUCTIONS: &'static [(Self, &'static str)] = &[
                $( (Self::$variant, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1), )+
                $( (Self::$later_variant, $introduction_schema), )+
            ];

            /// Stable lower-case group-qualified identifier.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $( Self::$variant => $identifier, )+
                    $( Self::$later_variant => $later_identifier, )+
                }
            }

            /// Stable counter unit.
            pub const fn unit(self) -> PerformanceMeasurementUnit {
                match self {
                    $( Self::$variant => PerformanceMeasurementUnit::$unit, )+
                    $( Self::$later_variant => PerformanceMeasurementUnit::$later_unit, )+
                }
            }

            /// Exact cumulative label vocabulary for one published schema.
            pub fn labels_for_schema(
                schema: &str,
            ) -> Option<impl Iterator<Item = Self> + '_> {
                let schema_rank = performance_measurement_schema_rank(schema)?;
                Some(Self::INTRODUCTIONS.iter().filter_map(move |(label, introduced)| {
                    (performance_measurement_schema_rank(introduced)
                        .expect("label introduction uses a published schema")
                        <= schema_rank)
                        .then_some(*label)
                }))
            }

            /// Resolve a label only when it belongs to the declared schema.
            pub fn from_schema_identifier(schema: &str, identifier: &str) -> Option<Self> {
                Self::labels_for_schema(schema)?
                    .find(|candidate| candidate.as_str() == identifier)
            }
        }
    };
}

fn performance_measurement_schema_rank(schema: &str) -> Option<u8> {
    match schema {
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1 => Some(1),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2 => Some(2),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3 => Some(3),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4 => Some(4),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5 => Some(5),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6 => Some(6),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7 => Some(7),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8 => Some(8),
        PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9 => Some(9),
        _ => None,
    }
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
    ; introduced_later {
        PackageAvoidedBaseContextCloneBytes => ("package.avoided_base_context_clone_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2),
        CacheSupportSelected => ("cache.support_selected", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheTargetsForcedLive => ("cache.targets_forced_live", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheContextIneligible => ("cache.context_ineligible", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheContextBypassedHits => ("cache.context_bypassed_hits", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheContextStale => ("cache.context_stale", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheContextSchemaMisses => ("cache.context_schema_misses", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheAvoidedSourceInterfaceResolutions => ("cache.avoided_source_interface_resolutions", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheTargetFreshBuilds => ("cache.target_fresh_builds", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheToolIdentityBytes => ("cache.tool_identity_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheToolIdentityElapsed => ("cache.tool_identity_elapsed", Nanoseconds, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheCurrentByteValidationElapsed => ("cache.current_byte_validation_elapsed", Nanoseconds, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheLiveSupportElapsed => ("cache.live_support_elapsed", Nanoseconds, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheSourceInterfaceResolutionElapsed => ("cache.source_interface_resolution_elapsed", Nanoseconds, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheBytesLoaded => ("cache.bytes_loaded", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        CacheBytesWritten => ("cache.bytes_written", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4),
        PackageSelectionExecBudgetPolicy => ("package.selection_exec_budget_policy", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionLegacy128Policy => ("package.selection_legacy128_policy", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionCandidatePaths => ("package.selection_candidate_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionPathspecPayloadBytes => ("package.selection_pathspec_payload_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionEffectiveArgvChargeBytes => ("package.selection_effective_argv_charge_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionMaxBatchPayloadBytes => ("package.selection_max_batch_payload_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionMaxBatchArgvChargeBytes => ("package.selection_max_batch_argv_charge_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionPathspecBatches => ("package.selection_pathspec_batches", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionWorktreeRootQueries => ("package.selection_worktree_root_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionHeadQueries => ("package.selection_head_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionTrackedQueries => ("package.selection_tracked_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionUntrackedQueries => ("package.selection_untracked_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionTrackedOutputPaths => ("package.selection_tracked_output_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionUntrackedOutputPaths => ("package.selection_untracked_output_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        PackageSelectionChangedPaths => ("package.selection_changed_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5),
        CertificateTermRootRequests => ("certificate.term_root_requests", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermUniqueNodesMaterialized => ("certificate.term_unique_nodes_materialized", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermSelectedEdges => ("certificate.term_selected_edges", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermReusedChildArcs => ("certificate.term_reused_child_arcs", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermOwnedRootHandoffs => ("certificate.term_owned_root_handoffs", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermLeafRootClones => ("certificate.term_leaf_root_clones", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermCompoundRootClones => ("certificate.term_compound_root_clones", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermMaterializationSlots => ("certificate.term_materialization_slots", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermMaterializationChargedBytes => ("certificate.term_materialization_charged_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermMaterializationCapacityStops => ("certificate.term_materialization_capacity_stops", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        CertificateTermMaterializationLegacyFallbacks => ("certificate.term_materialization_legacy_fallbacks", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6),
        PackageModulePayloadsFrozen => ("package.module_payloads_frozen", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageModulePayloadUniqueBytes => ("package.module_payload_unique_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageModulePayloadHandleClones => ("package.module_payload_handle_clones", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageAvoidedModulePayloadCloneBytes => ("package.avoided_module_payload_clone_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageSessionSnapshotClones => ("package.session_snapshot_clones", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageSessionIndexCowCopies => ("package.session_index_cow_copies", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageSessionIndexCowEntries => ("package.session_index_cow_entries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageDecodeCacheRetainedBytes => ("package.decode_cache_retained_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageDecodeCachePeakRetainedBytes => ("package.decode_cache_peak_retained_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageDecodeCacheCapacityStops => ("package.decode_cache_capacity_stops", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageProcessMemoPayloadHandleClones => ("package.process_memo_payload_handle_clones", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageArtifactFilesRead => ("package.artifact_files_read", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageArtifactFileHashes => ("package.artifact_file_hashes", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageArtifactFullDecodes => ("package.artifact_full_decodes", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageArtifactPreparedReuses => ("package.artifact_prepared_reuses", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactAdmissions => ("package.prepared_artifact_admissions", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactAdmittedBytes => ("package.prepared_artifact_admitted_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactCurrentEntries => ("package.prepared_artifact_current_entries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactPeakEntries => ("package.prepared_artifact_peak_entries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactCurrentBytes => ("package.prepared_artifact_current_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactPeakBytes => ("package.prepared_artifact_peak_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactDerivationCurrentBytes => ("package.prepared_artifact_derivation_current_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactDerivationPeakBytes => ("package.prepared_artifact_derivation_peak_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactKeyCurrentBytes => ("package.prepared_artifact_key_current_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactKeyPeakBytes => ("package.prepared_artifact_key_peak_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactEntryLimitFallbacks => ("package.prepared_artifact_entry_limit_fallbacks", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactByteLimitFallbacks => ("package.prepared_artifact_byte_limit_fallbacks", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactSaturatedChargeFallbacks => ("package.prepared_artifact_saturated_charge_fallbacks", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactReleases => ("package.prepared_artifact_releases", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackagePreparedArtifactReleasedBytes => ("package.prepared_artifact_released_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7),
        PackageSelectionBaseCommitQueries => ("package.selection_base_commit_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionCommittedHeadQueries => ("package.selection_committed_head_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionMergeBaseQueries => ("package.selection_merge_base_queries", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionBaseManifestBlobBytes => ("package.selection_base_manifest_blob_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionBaseLockBlobBytes => ("package.selection_base_lock_blob_bytes", Bytes, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionProtectedCandidatePaths => ("package.selection_protected_candidate_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionDirtyPaths => ("package.selection_dirty_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionCommittedDiffBatches => ("package.selection_committed_diff_batches", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionCommittedDiffProcesses => ("package.selection_committed_diff_processes", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionCommittedDiffOutputPaths => ("package.selection_committed_diff_output_paths", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionSeedModules => ("package.selection_seed_modules", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionFullEscalations => ("package.selection_full_escalations", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionFullEscalationReasonIdentityWord0 => ("package.selection_full_escalation_reason_identity_word_0", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionFullEscalationReasonIdentityWord1 => ("package.selection_full_escalation_reason_identity_word_1", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionFullEscalationReasonIdentityWord2 => ("package.selection_full_escalation_reason_identity_word_2", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionFullEscalationReasonIdentityWord3 => ("package.selection_full_escalation_reason_identity_word_3", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
        PackageSelectionClosureModules => ("package.selection_closure_modules", Count, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8),
    }
}

/// Cross-phase artifact work that is owned above the lock builder and checker.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackageCertificateArtifactObservation {
    pub artifact_files_read: u64,
    pub artifact_file_hashes: u64,
    pub artifact_full_decodes: u64,
    pub artifact_prepared_reuses: u64,
    pub key_candidate_current_bytes: u64,
    pub key_candidate_peak_bytes: u64,
    pub overflowed: bool,
}

/// Logical charge of the process-local decode/import cache in package memory
/// accounting. This state stays distinct from prepared-artifact retention: a
/// missing cache observation must never be replaced by the snapshot budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageDecodeCacheChargeState {
    /// Decode/import caching is disabled, so its logical retained charge is zero.
    Disabled,
    /// Caching is enabled but no typed bounded observation is available.
    UnboundedUnknown,
    /// The shared bounded cache supplied operation-current and operation-peak charge.
    Bounded { current_bytes: u64, peak_bytes: u64 },
}

impl PackageDecodeCacheChargeState {
    /// Build the honest aggregate-accounting state from the selected cache
    /// policy and the shared-payload observation captured by the operation.
    pub const fn from_payload_observation(
        cache_enabled: bool,
        observation: Option<&PackagePayloadOwnershipObservation>,
    ) -> Self {
        if !cache_enabled {
            return Self::Disabled;
        }
        match observation {
            Some(observation) => Self::Bounded {
                current_bytes: observation.decode_cache_retained_bytes,
                peak_bytes: observation.decode_cache_peak_retained_bytes,
            },
            None => Self::UnboundedUnknown,
        }
    }

    /// Project cache charge from the public production measurement report.
    /// Missing measurement data remains explicitly unknown rather than
    /// borrowing the unrelated prepared-artifact budget.
    pub fn from_measurement_report(
        cache_enabled: bool,
        report: Option<&PerformanceMeasurementReport>,
    ) -> Self {
        if !cache_enabled {
            return Self::Disabled;
        }
        let Some(report) = report else {
            return Self::UnboundedUnknown;
        };
        let value = |label| {
            report
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
        };
        match (
            value(PerformanceMeasurementLabel::PackageDecodeCacheRetainedBytes),
            value(PerformanceMeasurementLabel::PackageDecodeCachePeakRetainedBytes),
        ) {
            (Some(current_bytes), Some(peak_bytes)) => Self::Bounded {
                current_bytes,
                peak_bytes,
            },
            _ => Self::UnboundedUnknown,
        }
    }
}

impl PackageCertificateArtifactObservation {
    fn add(field: &mut u64, value: u64, overflowed: &mut bool) {
        let (sum, overflow) = field.overflowing_add(value);
        *field = if overflow { u64::MAX } else { sum };
        *overflowed |= overflow;
    }

    pub fn observe_file_read(&mut self) {
        Self::add(&mut self.artifact_files_read, 1, &mut self.overflowed);
    }

    pub fn observe_file_hash(&mut self) {
        Self::add(&mut self.artifact_file_hashes, 1, &mut self.overflowed);
    }

    pub fn observe_full_decode(&mut self) {
        Self::add(&mut self.artifact_full_decodes, 1, &mut self.overflowed);
    }

    pub fn observe_prepared_reuse(&mut self) {
        Self::add(&mut self.artifact_prepared_reuses, 1, &mut self.overflowed);
    }

    pub fn merge_preparation(
        &mut self,
        observation: npa_package::PackageArtifactPreparationObservation,
    ) {
        Self::add(
            &mut self.artifact_file_hashes,
            observation.artifact_file_hashes,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.artifact_full_decodes,
            observation.artifact_full_decodes,
            &mut self.overflowed,
        );
        self.overflowed |= observation.overflowed;
    }

    pub fn begin_key_candidate(&mut self, bytes: u64) {
        self.key_candidate_current_bytes = bytes;
        self.key_candidate_peak_bytes = self.key_candidate_peak_bytes.max(bytes);
    }

    pub fn finish_key_candidate(&mut self) {
        self.key_candidate_current_bytes = 0;
    }
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
    FastShardMemoryV2TermMaterialization,
    FastShardMemoryV3TermMaterializationPreparedRetention,
}

impl PerformancePackageShardMemoryModel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastShardMemoryV1 => "npa.fast-shard-memory.v1",
            Self::FastShardMemoryV2TermMaterialization => {
                "npa.fast-shard-memory.v2-term-materialization"
            }
            Self::FastShardMemoryV3TermMaterializationPreparedRetention => {
                "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
            }
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
    pub kernel: Option<PerformanceAcceptedKernelMeasurement>,
}

/// Closed subsystem vocabulary for declaration-level kernel measurements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PerformanceKernelSubsystem {
    FastKernel,
}

impl PerformanceKernelSubsystem {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastKernel => "fast_kernel",
        }
    }
}

/// Closed successful declaration outcome vocabulary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PerformanceAcceptedKernelOutcome {
    Accepted,
}

impl PerformanceAcceptedKernelOutcome {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
        }
    }
}

/// Declaration aggregate for one kernel fuel domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceKernelFuelDomainTotals {
    pub calls: u64,
    pub logical_spent: u64,
    pub successful_operation_fuel: u64,
    pub exhausted_operation_fuel: u64,
    pub overflowed: bool,
}

/// Domain-separated declaration fuel totals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceKernelFuelTotals {
    pub whnf: PerformanceKernelFuelDomainTotals,
    pub conversion: PerformanceKernelFuelDomainTotals,
}

/// Strict bounded work vocabulary shared by accepted and failed operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceKernelWork {
    pub check_calls: u64,
    pub infer_calls: u64,
    pub whnf_calls: u64,
    pub defeq_calls: u64,
    pub quick_equality_hits: u64,
    pub beta_steps: u64,
    pub delta_steps: u64,
    pub iota_steps: u64,
    pub physical_reductions: u64,
    pub overflowed: bool,
}

/// One bounded retained delta-constant count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceKernelDeltaHotsetEntry {
    pub constant: String,
    pub count: u64,
}

/// Bounded retained delta-constant projection. This is required even when its
/// entry list is empty; the kernel's 256-name working map is never exposed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceKernelDeltaHotsetSummary {
    pub retained_names: u64,
    pub capacity: u64,
    pub entries: Vec<PerformanceKernelDeltaHotsetEntry>,
    pub emitted: u64,
    pub entry_limit: u64,
    pub unretained_name_observations: u64,
    pub overlong_name_observations: u64,
    pub output_truncated: bool,
    pub overflowed: bool,
}

/// Strict successful fast-kernel declaration measurement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceAcceptedKernelMeasurement {
    pub subsystem: PerformanceKernelSubsystem,
    pub outcome: PerformanceAcceptedKernelOutcome,
    pub fuel: PerformanceKernelFuelTotals,
    pub work: PerformanceKernelWork,
    pub retained_delta_constants: PerformanceKernelDeltaHotsetSummary,
    pub overflowed: bool,
}

impl PerformanceAcceptedKernelMeasurement {
    /// Adapt the bounded frontend summary without exposing kernel working
    /// state. Reject forged open-string discriminants instead of relabeling
    /// them as a strict accepted measurement.
    pub fn from_frontend(summary: &npa_frontend::HumanKernelDeclarationSummary) -> Option<Self> {
        if summary.subsystem != PerformanceKernelSubsystem::FastKernel.as_str()
            || summary.outcome != PerformanceAcceptedKernelOutcome::Accepted.as_str()
        {
            return None;
        }
        Some(Self {
            subsystem: PerformanceKernelSubsystem::FastKernel,
            outcome: PerformanceAcceptedKernelOutcome::Accepted,
            fuel: PerformanceKernelFuelTotals::from_frontend(&summary.fuel),
            work: PerformanceKernelWork::from_frontend(&summary.work),
            retained_delta_constants: PerformanceKernelDeltaHotsetSummary::from_frontend(
                &summary.retained_delta_constants,
            ),
            overflowed: summary.overflowed,
        })
    }
}

impl PerformanceKernelFuelDomainTotals {
    fn from_frontend(summary: &npa_frontend::HumanKernelFuelDomainTotals) -> Self {
        Self {
            calls: summary.calls,
            logical_spent: summary.logical_spent,
            successful_operation_fuel: summary.successful_operation_fuel,
            exhausted_operation_fuel: summary.exhausted_operation_fuel,
            overflowed: summary.overflowed,
        }
    }
}

impl PerformanceKernelFuelTotals {
    fn from_frontend(summary: &npa_frontend::HumanKernelFuelTotals) -> Self {
        Self {
            whnf: PerformanceKernelFuelDomainTotals::from_frontend(&summary.whnf),
            conversion: PerformanceKernelFuelDomainTotals::from_frontend(&summary.conversion),
        }
    }
}

impl PerformanceKernelWork {
    fn from_frontend(summary: &npa_frontend::HumanKernelWorkSnapshot) -> Self {
        Self {
            check_calls: summary.check_calls,
            infer_calls: summary.infer_calls,
            whnf_calls: summary.whnf_calls,
            defeq_calls: summary.defeq_calls,
            quick_equality_hits: summary.quick_equality_hits,
            beta_steps: summary.beta_steps,
            delta_steps: summary.delta_steps,
            iota_steps: summary.iota_steps,
            physical_reductions: summary.physical_reductions,
            overflowed: summary.overflowed,
        }
    }
}

impl PerformanceKernelDeltaHotsetSummary {
    fn from_frontend(summary: &npa_frontend::HumanKernelDeltaHotsetSummary) -> Self {
        Self {
            retained_names: summary.retained_names,
            capacity: summary.capacity,
            entries: summary
                .entries
                .iter()
                .map(|entry| PerformanceKernelDeltaHotsetEntry {
                    constant: entry.constant.clone(),
                    count: entry.count,
                })
                .collect(),
            emitted: summary.emitted,
            entry_limit: summary.entry_limit,
            unretained_name_observations: summary.unretained_name_observations,
            overlong_name_observations: summary.overlong_name_observations,
            output_truncated: summary.output_truncated,
            overflowed: summary.overflowed,
        }
    }
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
    pub prepared_shared_bytes: u64,
    pub combined_shared_bytes: u64,
    pub per_worker_bytes: u64,
    pub term_materialization_bytes_per_worker: u64,
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
    pub prepared_shared_bytes: u64,
    pub combined_shared_bytes: u64,
    pub per_worker_bytes: u64,
    pub term_materialization_bytes_per_worker: u64,
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
enum PerformanceInputIdentityState {
    #[default]
    Unknown,
    Exact(String),
    Conflict,
}

impl PerformanceInputIdentityState {
    fn merge_child(&mut self, child: Option<&str>) {
        let Some(child) = child else {
            return;
        };
        match self {
            Self::Unknown => *self = Self::Exact(child.to_owned()),
            Self::Exact(current) if current == child => {}
            Self::Exact(_) => *self = Self::Conflict,
            Self::Conflict => {}
        }
    }
}

/// Operation-scoped bounded recorder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceMeasurementRecorder {
    mode: PerformanceMeasurementMode,
    schema: &'static str,
    input_identity: PerformanceInputIdentityState,
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
            schema: PERFORMANCE_MEASUREMENTS_SCHEMA,
            input_identity: PerformanceInputIdentityState::Unknown,
            state,
        }
    }

    pub fn with_input_identity(mut self, identity: impl Into<String>) -> Self {
        if self.mode.is_enabled() {
            self.input_identity = PerformanceInputIdentityState::Exact(identity.into());
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
        if PerformanceMeasurementLabel::from_schema_identifier(self.schema, label.as_str())
            .is_none()
        {
            state.overflowed = true;
            return;
        }
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

    /// Project one changed-package selection observation through the closed
    /// common measurement vocabulary.
    pub fn observe_package_selection(
        &mut self,
        observation: &PerformancePackageSelectionObservation,
    ) {
        match observation.batch_policy {
            PerformancePackageSelectionBatchPolicy::NotSelected => {}
            PerformancePackageSelectionBatchPolicy::ExecBudget => self.add_counter(
                PerformanceMeasurementLabel::PackageSelectionExecBudgetPolicy,
                1,
            ),
            PerformancePackageSelectionBatchPolicy::Legacy128 => self.add_counter(
                PerformanceMeasurementLabel::PackageSelectionLegacy128Policy,
                1,
            ),
        }
        for (label, value) in [
            (
                PerformanceMeasurementLabel::PackageSelectionCandidatePaths,
                observation.candidate_paths,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionPathspecPayloadBytes,
                observation.pathspec_payload_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionEffectiveArgvChargeBytes,
                observation.effective_argv_charge_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionMaxBatchPayloadBytes,
                observation.max_batch_payload_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionMaxBatchArgvChargeBytes,
                observation.max_batch_argv_charge_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionPathspecBatches,
                observation.pathspec_batches,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionWorktreeRootQueries,
                observation.worktree_root_queries,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionHeadQueries,
                observation.head_queries,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionTrackedQueries,
                observation.tracked_queries,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionUntrackedQueries,
                observation.untracked_queries,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionTrackedOutputPaths,
                observation.tracked_output_paths,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionUntrackedOutputPaths,
                observation.untracked_output_paths,
            ),
            (
                PerformanceMeasurementLabel::PackageSelectionChangedPaths,
                observation.selected_paths,
            ),
        ] {
            self.add_counter(label, value);
        }
        if observation.committed_base {
            for (label, value) in [
                (
                    PerformanceMeasurementLabel::PackageSelectionBaseCommitQueries,
                    observation.base_commit_queries,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionCommittedHeadQueries,
                    observation.committed_head_queries,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionMergeBaseQueries,
                    observation.merge_base_queries,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionBaseManifestBlobBytes,
                    observation.base_manifest_blob_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionBaseLockBlobBytes,
                    observation.base_lock_blob_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionProtectedCandidatePaths,
                    observation.protected_candidate_paths,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionDirtyPaths,
                    observation.dirty_paths,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionCommittedDiffBatches,
                    observation.committed_diff_batches,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionCommittedDiffProcesses,
                    observation.committed_diff_processes,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionCommittedDiffOutputPaths,
                    observation.committed_diff_output_paths,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionSeedModules,
                    observation.seed_modules,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionFullEscalations,
                    observation.full_escalations,
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionFullEscalationReasonIdentityWord0,
                    observation.full_escalation_reason_identity[0],
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionFullEscalationReasonIdentityWord1,
                    observation.full_escalation_reason_identity[1],
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionFullEscalationReasonIdentityWord2,
                    observation.full_escalation_reason_identity[2],
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionFullEscalationReasonIdentityWord3,
                    observation.full_escalation_reason_identity[3],
                ),
                (
                    PerformanceMeasurementLabel::PackageSelectionClosureModules,
                    observation.selected_closure_modules,
                ),
            ] {
                self.add_counter(label, value);
            }
        }
        if observation.overflowed {
            self.mark_overflowed();
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

    /// Project certificate term-DAG acceleration work through the common
    /// diagnostic schema. The observation is never proof evidence.
    pub fn observe_certificate_term_materialization(
        &mut self,
        observation: &CertificateTermMaterializationObservation,
    ) {
        for (label, value) in [
            (
                PerformanceMeasurementLabel::CertificateTermRootRequests,
                observation.root_requests,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermUniqueNodesMaterialized,
                observation.unique_nodes_materialized,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermSelectedEdges,
                observation.selected_edges,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermReusedChildArcs,
                observation.reused_child_arcs,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermOwnedRootHandoffs,
                observation.owned_root_handoffs,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermLeafRootClones,
                observation.leaf_root_clones,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermCompoundRootClones,
                observation.compound_root_clones,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermMaterializationSlots,
                observation.materialization_slots,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermMaterializationChargedBytes,
                observation.materialization_charged_bytes,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermMaterializationCapacityStops,
                observation.materialization_capacity_stops,
            ),
            (
                PerformanceMeasurementLabel::CertificateTermMaterializationLegacyFallbacks,
                observation.materialization_legacy_fallbacks,
            ),
        ] {
            self.add_counter(label, value);
        }
        if observation.overflowed {
            self.mark_overflowed();
        }
    }

    /// Project immutable certificate/session payload ownership work.
    pub fn observe_certificate_payload_ownership(
        &mut self,
        certificate: &CertificatePayloadObservation,
        package: &PackagePayloadOwnershipObservation,
    ) {
        for (label, value) in [
            (
                PerformanceMeasurementLabel::PackageModulePayloadsFrozen,
                certificate.payloads_frozen,
            ),
            (
                PerformanceMeasurementLabel::PackageModulePayloadUniqueBytes,
                certificate.payload_unique_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageSessionSnapshotClones,
                certificate.session_snapshot_clones,
            ),
            (
                PerformanceMeasurementLabel::PackageSessionIndexCowCopies,
                certificate.session_index_cow_copies,
            ),
            (
                PerformanceMeasurementLabel::PackageSessionIndexCowEntries,
                certificate.session_index_cow_entries,
            ),
            (
                PerformanceMeasurementLabel::PackageModulePayloadHandleClones,
                package.module_payload_handle_clones,
            ),
            (
                PerformanceMeasurementLabel::PackageAvoidedModulePayloadCloneBytes,
                package.avoided_module_payload_clone_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageDecodeCacheRetainedBytes,
                package.decode_cache_retained_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageDecodeCachePeakRetainedBytes,
                package.decode_cache_peak_retained_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackageDecodeCacheCapacityStops,
                package.decode_cache_capacity_stops,
            ),
            (
                PerformanceMeasurementLabel::PackageProcessMemoPayloadHandleClones,
                package.process_memo_payload_handle_clones,
            ),
        ] {
            self.add_counter(label, value);
        }
        if certificate.overflowed || package.overflowed {
            self.mark_overflowed();
        }
    }

    /// Project owned artifact preparation/reuse and decoded-retention work.
    pub fn observe_package_certificate_artifacts(
        &mut self,
        artifacts: &PackageCertificateArtifactObservation,
        retention: Option<&PreparedArtifactRetentionObservation>,
    ) {
        for (label, value) in [
            (
                PerformanceMeasurementLabel::PackageArtifactFilesRead,
                artifacts.artifact_files_read,
            ),
            (
                PerformanceMeasurementLabel::PackageArtifactFileHashes,
                artifacts.artifact_file_hashes,
            ),
            (
                PerformanceMeasurementLabel::PackageArtifactFullDecodes,
                artifacts.artifact_full_decodes,
            ),
            (
                PerformanceMeasurementLabel::PackageArtifactPreparedReuses,
                artifacts.artifact_prepared_reuses,
            ),
            (
                PerformanceMeasurementLabel::PackagePreparedArtifactKeyCurrentBytes,
                artifacts.key_candidate_current_bytes,
            ),
            (
                PerformanceMeasurementLabel::PackagePreparedArtifactKeyPeakBytes,
                artifacts.key_candidate_peak_bytes,
            ),
        ] {
            self.add_counter(label, value);
        }
        if let Some(retention) = retention {
            for (label, value) in [
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactAdmissions,
                    retention.admissions,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactAdmittedBytes,
                    retention.admitted_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactCurrentEntries,
                    retention.current_entries,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactPeakEntries,
                    retention.peak_entries,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactCurrentBytes,
                    retention.current_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactPeakBytes,
                    retention.peak_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactDerivationCurrentBytes,
                    retention.derivation_candidate_current_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactDerivationPeakBytes,
                    retention.derivation_candidate_peak_bytes,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactEntryLimitFallbacks,
                    retention.entry_limit_fallbacks,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactByteLimitFallbacks,
                    retention.byte_limit_fallbacks,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactSaturatedChargeFallbacks,
                    retention.saturated_charge_fallbacks,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactReleases,
                    retention.charged_releases,
                ),
                (
                    PerformanceMeasurementLabel::PackagePreparedArtifactReleasedBytes,
                    retention.released_bytes,
                ),
            ] {
                self.add_counter(label, value);
            }
            if retention.overflowed {
                self.mark_overflowed();
            }
        }
        if artifacts.overflowed {
            self.mark_overflowed();
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

    /// Record one bounded module-local declaration batch. `attempted` is
    /// accounted exactly once; supplied records are inserted without adding a
    /// second attempt per row, then command-wide canonical retention is
    /// reapplied.
    pub fn record_declaration_batch(
        &mut self,
        attempted: u64,
        overflowed: bool,
        declarations: Vec<PerformanceDeclarationMeasurement>,
    ) {
        let Some(state) = self.state.as_mut() else {
            return;
        };
        let declaration_count = match u64::try_from(declarations.len()) {
            Ok(count) => count,
            Err(_) => {
                state.overflowed = true;
                u64::MAX
            }
        };
        if attempted < declaration_count {
            state.overflowed = true;
        }
        state.overflowed |= overflowed;
        let Some(retained) = state.declarations.as_mut() else {
            return;
        };
        saturating_add(
            &mut state.declaration_attempted,
            attempted.max(declaration_count),
            &mut state.overflowed,
        );

        for measurement in declarations {
            retained.insert(
                (
                    measurement.module.clone(),
                    measurement.declaration_index,
                    measurement.declaration.clone(),
                ),
                measurement,
            );
        }
        truncate_last(retained, PERFORMANCE_DECLARATION_DETAIL_LIMIT);
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

    /// Merge a child report while preserving a single exact input identity.
    /// Distinct child identities enter an absorbing measurement-only conflict.
    pub fn merge_child_report_preserving_identity(
        &mut self,
        report: &PerformanceMeasurementReport,
    ) {
        if !self.mode.is_enabled() {
            return;
        }
        self.input_identity
            .merge_child(report.input_identity.as_deref());
        self.merge(report);
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
        let identity_conflict =
            matches!(self.input_identity, PerformanceInputIdentityState::Conflict);
        let input_identity = match &self.input_identity {
            PerformanceInputIdentityState::Unknown | PerformanceInputIdentityState::Conflict => {
                None
            }
            PerformanceInputIdentityState::Exact(identity) => Some(identity.clone()),
        };
        Some(PerformanceMeasurementReport {
            schema: self.schema,
            trusted: false,
            proof_evidence: false,
            mode: self.mode,
            input_identity,
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
            overflowed: state.overflowed || identity_conflict,
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
                "{{\"module\":\"{}\",\"declaration_index\":{},\"declaration\":\"{}\",\"term_nodes\":{},\"elaboration_elapsed_ns\":{},\"kernel\":{}}}",
                json_escape(&declaration.module),
                declaration.declaration_index,
                json_escape(&declaration.declaration),
                declaration.term_nodes,
                declaration.elaboration_elapsed_ns,
                accepted_kernel_json(declaration.kernel.as_ref()),
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
                "{{\"layer_index\":{},\"runnable_width\":{},\"estimated_total_cost\":{},\"estimated_max_shard_cost\":{},\"requested_jobs\":{},\"effective_jobs\":{},\"reduction_reason\":\"{}\",\"shared_base_context_bytes\":{},\"prepared_shared_bytes\":{},\"combined_shared_bytes\":{},\"per_worker_bytes\":{},\"term_materialization_bytes_per_worker\":{},\"memory_budget_bytes\":{},\"estimate_overflowed\":{},\"elapsed_ns\":{}}}",
                layer.layer_index,
                layer.runnable_width,
                layer.estimated_total_cost,
                layer.estimated_max_shard_cost,
                layer.requested_jobs,
                layer.effective_jobs,
                layer.reduction_reason.as_str(),
                layer.shared_base_context_bytes,
                layer.prepared_shared_bytes,
                layer.combined_shared_bytes,
                layer.per_worker_bytes,
                layer.term_materialization_bytes_per_worker,
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

fn accepted_kernel_json(measurement: Option<&PerformanceAcceptedKernelMeasurement>) -> String {
    measurement.map_or_else(
        || "null".to_owned(),
        |measurement| {
            format!(
                "{{\"subsystem\":\"{}\",\"outcome\":\"{}\",\"fuel\":{},\"work\":{},\"retained_delta_constants\":{},\"overflowed\":{}}}",
                measurement.subsystem.as_str(),
                measurement.outcome.as_str(),
                kernel_fuel_totals_json(&measurement.fuel),
                kernel_work_json(&measurement.work),
                kernel_delta_hotset_json(&measurement.retained_delta_constants),
                measurement.overflowed,
            )
        },
    )
}

fn kernel_fuel_totals_json(fuel: &PerformanceKernelFuelTotals) -> String {
    format!(
        "{{\"whnf\":{},\"conversion\":{}}}",
        kernel_fuel_domain_json(&fuel.whnf),
        kernel_fuel_domain_json(&fuel.conversion),
    )
}

fn kernel_fuel_domain_json(fuel: &PerformanceKernelFuelDomainTotals) -> String {
    format!(
        "{{\"calls\":{},\"logical_spent\":{},\"successful_operation_fuel\":{},\"exhausted_operation_fuel\":{},\"overflowed\":{}}}",
        fuel.calls,
        fuel.logical_spent,
        fuel.successful_operation_fuel,
        fuel.exhausted_operation_fuel,
        fuel.overflowed,
    )
}

fn kernel_work_json(work: &PerformanceKernelWork) -> String {
    format!(
        "{{\"check_calls\":{},\"infer_calls\":{},\"whnf_calls\":{},\"defeq_calls\":{},\"quick_equality_hits\":{},\"beta_steps\":{},\"delta_steps\":{},\"iota_steps\":{},\"physical_reductions\":{},\"overflowed\":{}}}",
        work.check_calls,
        work.infer_calls,
        work.whnf_calls,
        work.defeq_calls,
        work.quick_equality_hits,
        work.beta_steps,
        work.delta_steps,
        work.iota_steps,
        work.physical_reductions,
        work.overflowed,
    )
}

fn kernel_delta_hotset_json(summary: &PerformanceKernelDeltaHotsetSummary) -> String {
    let entries = summary
        .entries
        .iter()
        .map(|entry| {
            format!(
                "{{\"constant\":\"{}\",\"count\":{}}}",
                json_escape(&entry.constant),
                entry.count,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"retained_names\":{},\"capacity\":{},\"entries\":[{}],\"emitted\":{},\"entry_limit\":{},\"unretained_name_observations\":{},\"overlong_name_observations\":{},\"output_truncated\":{},\"overflowed\":{}}}",
        summary.retained_names,
        summary.capacity,
        entries,
        summary.emitted,
        summary.entry_limit,
        summary.unretained_name_observations,
        summary.overlong_name_observations,
        summary.output_truncated,
        summary.overflowed,
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
        "{{\"cost_model\":\"{}\",\"memory_model\":\"{}\",\"import_weight\":{},\"memory_budget_bytes\":{},\"fixed_worker_bytes\":{},\"scratch_multiplier\":{},\"requested_jobs\":{},\"effective_jobs\":{},\"reduction_reason\":\"{}\",\"shared_base_context_bytes\":{},\"prepared_shared_bytes\":{},\"combined_shared_bytes\":{},\"per_worker_bytes\":{},\"term_materialization_bytes_per_worker\":{},\"avoided_base_context_clone_bytes\":{},\"estimate_overflowed\":{},\"critical_path_cost\":{},\"critical_path_module_count\":{},\"critical_path_identity\":\"{}\",\"critical_path_checker_elapsed_ns\":{},\"barrier_elapsed_ns\":{}}}",
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
        measurement.prepared_shared_bytes,
        measurement.combined_shared_bytes,
        measurement.per_worker_bytes,
        measurement.term_materialization_bytes_per_worker,
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
                && identifier.bytes().all(|byte| {
                    byte.is_ascii_lowercase()
                        || byte.is_ascii_digit()
                        || byte == b'.'
                        || byte == b'_'
                })
        }));
        let snapshot = PerformanceMeasurementLabel::ALL
            .iter()
            .map(|label| format!("{}:{}", label.as_str(), label.unit().as_str()))
            .collect::<Vec<_>>()
            .join("\n");
        let snapshot_hash = format!("{:x}", Sha256::digest(snapshot.as_bytes()));
        assert_eq!(
            snapshot_hash,
            "3e14ad257cfd7f77702db39e19f9bf029f486e7c8419b63fd4d73f42fa3ab50e"
        );
    }

    #[test]
    fn performance_measurement_historical_vocabularies_reject_newer_labels() {
        let targeted = targeted_authoring_labels();
        for schema in [
            PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1,
            PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2,
            PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3,
        ] {
            for (label, identifier, _) in targeted {
                assert_eq!(
                    PerformanceMeasurementLabel::from_schema_identifier(schema, identifier),
                    None,
                    "{schema} accepted {identifier}"
                );
                assert!(!PerformanceMeasurementLabel::labels_for_schema(schema)
                    .unwrap()
                    .any(|candidate| candidate == *label));
            }
        }

        let v0_1 =
            PerformanceMeasurementLabel::labels_for_schema(PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1)
                .unwrap()
                .collect::<Vec<_>>();
        let v0_2 =
            PerformanceMeasurementLabel::labels_for_schema(PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2)
                .unwrap()
                .collect::<Vec<_>>();
        let v0_3 =
            PerformanceMeasurementLabel::labels_for_schema(PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3)
                .unwrap()
                .collect::<Vec<_>>();
        assert_eq!(v0_2, v0_3);
        assert_eq!(v0_1.len() + 1, v0_2.len());
        assert!(!v0_1.contains(&PerformanceMeasurementLabel::PackageAvoidedBaseContextCloneBytes));
        assert!(v0_2.contains(&PerformanceMeasurementLabel::PackageAvoidedBaseContextCloneBytes));
        assert!(PerformanceMeasurementLabel::labels_for_schema(
            "npa.performance.measurements.v0.10"
        )
        .is_none());
        assert!(PerformanceMeasurementLabel::from_schema_identifier(
            PERFORMANCE_MEASUREMENTS_SCHEMA,
            "cache.unknown"
        )
        .is_none());
    }

    #[test]
    fn targeted_authoring_measurement_labels_have_exact_units_and_current_order() {
        let targeted = targeted_authoring_labels();
        for (label, identifier, unit) in targeted {
            assert_eq!(label.as_str(), *identifier);
            assert_eq!(label.unit(), *unit);
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4,
                    identifier,
                ),
                Some(*label)
            );
        }
        for (label, unit) in [
            (
                PerformanceMeasurementLabel::CacheContextHits,
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheContextMisses,
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheLivePrerequisiteChecks,
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheAvoidedKernelChecks,
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheReconstructionElapsed,
                PerformanceMeasurementUnit::Nanoseconds,
            ),
            (
                PerformanceMeasurementLabel::CacheFreshTargetElapsed,
                PerformanceMeasurementUnit::Nanoseconds,
            ),
        ] {
            assert_eq!(label.unit(), unit);
            for schema in [
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8,
            ] {
                assert_eq!(
                    PerformanceMeasurementLabel::from_schema_identifier(schema, label.as_str()),
                    Some(label)
                );
            }
        }

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        for (index, (label, _, _)) in targeted.iter().rev().enumerate() {
            recorder.add_counter(*label, index as u64);
        }
        let report = recorder.report().unwrap();
        assert_eq!(report.schema, PERFORMANCE_MEASUREMENTS_SCHEMA);
        let identifiers = report
            .counters
            .iter()
            .map(|counter| counter.label.as_str())
            .collect::<Vec<_>>();
        let mut expected = targeted
            .iter()
            .map(|(_, identifier, _)| *identifier)
            .collect::<Vec<_>>();
        expected.sort_unstable();
        assert_eq!(identifiers, expected);
        let json = performance_measurement_report_json(&report);
        assert!(json.starts_with(&format!(
            "{{\"schema\":\"{PERFORMANCE_MEASUREMENTS_SCHEMA}\""
        )));
    }

    #[test]
    fn disabled_mode_has_no_state_clock_reads_or_report() {
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Off);
        assert!(recorder.start_timer().is_none());
        recorder.add_counter(PerformanceMeasurementLabel::CandidateSubmitted, 1);
        recorder.record_module(module("B"));
        recorder.record_declaration_batch(1, true, vec![declaration("B", 0, None)]);
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
        recorder.record_declaration_batch(1, false, vec![declaration("A", 0, None)]);
        let report = recorder.report().unwrap();
        assert!(report.modules.is_empty());
        assert!(report.declarations.is_empty());
        assert!(report.candidates.is_empty());
        assert_eq!(report.module_details, PerformanceDetailCounts::default());
        assert_eq!(
            report.declaration_details,
            PerformanceDetailCounts::default()
        );
        assert_eq!(report.candidate_details, PerformanceDetailCounts::default());
        assert!(!report.detail_truncated);
        assert!(!report.overflowed);
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
    fn declaration_batch_carries_module_omissions_without_double_counting() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_declaration_batch(
            3,
            false,
            vec![declaration("M", 0, None), declaration("M", 1, None)],
        );

        let report = recorder.report().unwrap();
        assert_eq!(report.declarations.len(), 2);
        assert_eq!(
            report.declaration_details,
            PerformanceDetailCounts {
                attempted: 3,
                retained: 2,
                omitted: 1,
            }
        );
        assert!(report.detail_truncated);
        assert!(!report.overflowed);
    }

    #[test]
    fn declaration_batch_duplicate_keys_remain_unique_without_losing_attempts() {
        let mut first = declaration("M", 0, None);
        first.term_nodes = 1;
        let mut replacement = declaration("M", 0, None);
        replacement.term_nodes = 2;
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_declaration_batch(2, false, vec![first, replacement]);

        let report = recorder.report().unwrap();
        assert_eq!(report.declarations.len(), 1);
        assert_eq!(report.declarations[0].term_nodes, 2);
        assert_eq!(report.declaration_details.attempted, 2);
        assert_eq!(report.declaration_details.retained, 1);
        assert_eq!(report.declaration_details.omitted, 1);
        assert!(!report.overflowed);
    }

    #[test]
    fn declaration_batches_reapply_the_global_canonical_cap() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        let later = (0..1_025)
            .map(|index| declaration("Z", index, None))
            .collect();
        let earlier = (0..1_025)
            .map(|index| declaration("A", index, None))
            .collect();
        recorder.record_declaration_batch(1_025, false, later);
        recorder.record_declaration_batch(1_025, false, earlier);

        let report = recorder.report().unwrap();
        assert_eq!(
            report.declarations.len(),
            PERFORMANCE_DECLARATION_DETAIL_LIMIT
        );
        assert_eq!(report.declaration_details.attempted, 2_050);
        assert_eq!(report.declaration_details.omitted, 2);
        assert_eq!(report.declarations.first().unwrap().module, "A");
        assert_eq!(report.declarations.first().unwrap().declaration_index, 0);
        assert_eq!(report.declarations.last().unwrap().module, "Z");
        assert_eq!(report.declarations.last().unwrap().declaration_index, 1_022);
        assert!(report.detail_truncated);
    }

    #[test]
    fn declaration_batch_invalid_attempts_and_saturation_propagate_overflow() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_declaration_batch(0, false, vec![declaration("M", 0, None)]);
        let report = recorder.report().unwrap();
        assert_eq!(report.declaration_details.attempted, 1);
        assert!(report.overflowed);

        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_declaration_batch(u64::MAX, false, Vec::new());
        recorder.record_declaration_batch(1, false, Vec::new());
        let report = recorder.report().unwrap();
        assert_eq!(report.declaration_details.attempted, u64::MAX);
        assert!(report.overflowed);

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.record_declaration_batch(0, true, Vec::new());
        let report = recorder.report().unwrap();
        assert_eq!(
            report.declaration_details,
            PerformanceDetailCounts::default()
        );
        assert!(report.overflowed);
    }

    #[test]
    fn declaration_kernel_json_is_nullable_strict_and_stably_ordered() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.record_declaration_batch(
            2,
            false,
            vec![
                declaration("M", 1, Some(accepted_kernel_with_empty_hotset())),
                declaration("M", 0, None),
            ],
        );
        let report = recorder.report().unwrap();
        assert_eq!(report.schema, PERFORMANCE_MEASUREMENTS_SCHEMA);

        let json = performance_measurement_report_json(&report);
        let expected_declarations = concat!(
            "\"declarations\":[",
            "{\"module\":\"M\",\"declaration_index\":0,\"declaration\":\"M.d0\",\"term_nodes\":1,\"elaboration_elapsed_ns\":2,\"kernel\":null},",
            "{\"module\":\"M\",\"declaration_index\":1,\"declaration\":\"M.d1\",\"term_nodes\":1,\"elaboration_elapsed_ns\":2,\"kernel\":",
            "{\"subsystem\":\"fast_kernel\",\"outcome\":\"accepted\",\"fuel\":",
            "{\"whnf\":{\"calls\":1,\"logical_spent\":10,\"successful_operation_fuel\":10,\"exhausted_operation_fuel\":0,\"overflowed\":false},",
            "\"conversion\":{\"calls\":2,\"logical_spent\":20,\"successful_operation_fuel\":20,\"exhausted_operation_fuel\":0,\"overflowed\":false}},",
            "\"work\":{\"check_calls\":1,\"infer_calls\":2,\"whnf_calls\":3,\"defeq_calls\":4,\"quick_equality_hits\":5,\"beta_steps\":6,\"delta_steps\":0,\"iota_steps\":7,\"physical_reductions\":13,\"overflowed\":false},",
            "\"retained_delta_constants\":{\"retained_names\":0,\"capacity\":256,\"entries\":[],\"emitted\":0,\"entry_limit\":16,\"unretained_name_observations\":0,\"overlong_name_observations\":0,\"output_truncated\":false,\"overflowed\":false},",
            "\"overflowed\":false}}]"
        );
        assert!(json.starts_with(&format!(
            "{{\"schema\":\"{PERFORMANCE_MEASUREMENTS_SCHEMA}\""
        )));
        assert!(json.contains(expected_declarations), "{json}");
    }

    #[test]
    fn accepted_kernel_adapter_requires_strict_discriminants_and_keeps_empty_hotset() {
        let options = npa_frontend::HumanCompileOptions {
            kernel_fuel_report: npa_frontend::HumanKernelFuelReportMode::Detailed,
            ..npa_frontend::HumanCompileOptions::default()
        };
        let observed = npa_frontend::compile_human_source_to_observed_built_certificate_only_with_available_import_refs(
            npa_frontend::FileId(0),
            npa_cert::Name::from_dotted("Measured"),
            "axiom A : Type",
            &[],
            &[],
            &[],
            &options,
            None,
            true,
        )
        .unwrap();
        let frontend = observed.observations.declarations[0]
            .kernel
            .as_ref()
            .unwrap();
        let accepted = PerformanceAcceptedKernelMeasurement::from_frontend(frontend).unwrap();

        assert_eq!(accepted.subsystem, PerformanceKernelSubsystem::FastKernel);
        assert_eq!(accepted.outcome, PerformanceAcceptedKernelOutcome::Accepted);
        assert!(accepted.retained_delta_constants.entries.is_empty());
        assert_eq!(accepted.retained_delta_constants.retained_names, 0);
        assert_eq!(accepted.retained_delta_constants.emitted, 0);
        assert_eq!(accepted.overflowed, frontend.overflowed);

        let mut invalid = frontend.clone();
        invalid.outcome = "rejected".to_owned();
        assert!(PerformanceAcceptedKernelMeasurement::from_frontend(&invalid).is_none());
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
        assert!(json.starts_with(&format!(
            "{{\"schema\":\"{PERFORMANCE_MEASUREMENTS_SCHEMA}\""
        )));
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
    fn performance_package_selection_observation_default_is_closed_zero() {
        assert_eq!(
            PerformancePackageSelectionObservation::default(),
            PerformancePackageSelectionObservation {
                committed_base: false,
                batch_policy: PerformancePackageSelectionBatchPolicy::NotSelected,
                candidate_paths: 0,
                pathspec_payload_bytes: 0,
                effective_argv_charge_bytes: 0,
                max_batch_payload_bytes: 0,
                max_batch_argv_charge_bytes: 0,
                pathspec_batches: 0,
                worktree_root_queries: 0,
                head_queries: 0,
                tracked_queries: 0,
                untracked_queries: 0,
                tracked_output_paths: 0,
                untracked_output_paths: 0,
                selected_paths: 0,
                base_commit_queries: 0,
                committed_head_queries: 0,
                merge_base_queries: 0,
                base_manifest_blob_bytes: 0,
                base_lock_blob_bytes: 0,
                protected_candidate_paths: 0,
                dirty_paths: 0,
                committed_diff_batches: 0,
                committed_diff_processes: 0,
                committed_diff_output_paths: 0,
                seed_modules: 0,
                full_escalations: 0,
                full_escalation_reason_identity: [0; 4],
                selected_closure_modules: 0,
                overflowed: false,
            }
        );
    }

    #[test]
    fn package_selection_observation_projection_matrix() {
        for (policy, expected_policy) in [
            (PerformancePackageSelectionBatchPolicy::NotSelected, None),
            (
                PerformancePackageSelectionBatchPolicy::ExecBudget,
                Some(PerformanceMeasurementLabel::PackageSelectionExecBudgetPolicy),
            ),
            (
                PerformancePackageSelectionBatchPolicy::Legacy128,
                Some(PerformanceMeasurementLabel::PackageSelectionLegacy128Policy),
            ),
        ] {
            let observation = PerformancePackageSelectionObservation {
                committed_base: true,
                batch_policy: policy,
                candidate_paths: u64::MAX,
                pathspec_payload_bytes: 2,
                effective_argv_charge_bytes: 3,
                max_batch_payload_bytes: 4,
                max_batch_argv_charge_bytes: 5,
                pathspec_batches: 6,
                worktree_root_queries: 7,
                head_queries: 8,
                tracked_queries: 9,
                untracked_queries: 10,
                tracked_output_paths: 11,
                untracked_output_paths: 12,
                selected_paths: 13,
                base_commit_queries: 14,
                committed_head_queries: 15,
                merge_base_queries: 16,
                base_manifest_blob_bytes: 17,
                base_lock_blob_bytes: 18,
                protected_candidate_paths: 19,
                dirty_paths: 20,
                committed_diff_batches: 21,
                committed_diff_processes: 22,
                committed_diff_output_paths: 23,
                seed_modules: 24,
                full_escalations: 25,
                full_escalation_reason_identity: [26, 27, 28, 29],
                selected_closure_modules: 30,
                overflowed: false,
            };
            let mut recorder =
                PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
            recorder.observe_package_selection(&observation);
            let report = recorder.report().unwrap();
            assert_eq!(report.schema, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9);
            assert!(!report.overflowed, "an exact u64::MAX is not saturation");
            assert_eq!(
                report
                    .counters
                    .iter()
                    .find(|counter| {
                        counter.label == PerformanceMeasurementLabel::PackageSelectionCandidatePaths
                    })
                    .map(|counter| counter.value),
                Some(u64::MAX)
            );
            for policy_label in [
                PerformanceMeasurementLabel::PackageSelectionExecBudgetPolicy,
                PerformanceMeasurementLabel::PackageSelectionLegacy128Policy,
            ] {
                assert_eq!(
                    report
                        .counters
                        .iter()
                        .any(|counter| counter.label == policy_label),
                    expected_policy == Some(policy_label)
                );
            }
        }

        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_package_selection(&PerformancePackageSelectionObservation {
            overflowed: true,
            ..PerformancePackageSelectionObservation::default()
        });
        assert!(recorder.report().unwrap().overflowed);

        let mut off = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Off);
        off.observe_package_selection(&PerformancePackageSelectionObservation::default());
        assert!(off.report().is_none());
    }

    #[test]
    fn package_selection_labels_follow_v0_5_introduction() {
        for label in PerformanceMeasurementLabel::INTRODUCTIONS
            .iter()
            .filter_map(|(label, schema)| {
                (*schema == PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5).then_some(*label)
            })
        {
            for historical in [
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4,
            ] {
                assert_eq!(
                    PerformanceMeasurementLabel::from_schema_identifier(historical, label.as_str()),
                    None
                );
            }
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5,
                    label.as_str()
                ),
                Some(label)
            );
        }
    }

    #[test]
    fn certificate_term_materialization_labels_follow_v0_6_introduction() {
        let labels = PerformanceMeasurementLabel::ALL
            .iter()
            .copied()
            .filter(|label| label.as_str().starts_with("certificate.term_"))
            .collect::<Vec<_>>();
        assert_eq!(labels.len(), 11);
        for label in labels {
            for historical in [
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_1,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_2,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_3,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_4,
                PERFORMANCE_MEASUREMENTS_SCHEMA_V0_5,
            ] {
                assert_eq!(
                    PerformanceMeasurementLabel::from_schema_identifier(historical, label.as_str(),),
                    None
                );
            }
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6,
                    label.as_str(),
                ),
                Some(label)
            );
        }
    }

    #[test]
    fn performance_measurement_schema() {
        label_table_is_exhaustive_unique_and_canonical();
        certificate_term_materialization_labels_follow_v0_6_introduction();
    }

    #[test]
    fn certificate_term_materialization_projection_is_typed_and_saturating() {
        let observation = CertificateTermMaterializationObservation {
            root_requests: 1,
            unique_nodes_materialized: 2,
            selected_edges: 3,
            reused_child_arcs: 4,
            owned_root_handoffs: 5,
            leaf_root_clones: 6,
            compound_root_clones: 7,
            materialization_slots: 8,
            materialization_charged_bytes: 9,
            materialization_capacity_stops: 10,
            materialization_legacy_fallbacks: 11,
            overflowed: true,
        };
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_certificate_term_materialization(&observation);
        let report = recorder.report().unwrap();
        assert_eq!(report.schema, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9);
        assert!(report.overflowed);
        let values = report
            .counters
            .iter()
            .filter(|counter| counter.label.as_str().starts_with("certificate.term_"))
            .map(|counter| (counter.label, (counter.unit, counter.value)))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            values,
            BTreeMap::from([
                (
                    PerformanceMeasurementLabel::CertificateTermRootRequests,
                    (PerformanceMeasurementUnit::Count, 1)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermUniqueNodesMaterialized,
                    (PerformanceMeasurementUnit::Count, 2)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermSelectedEdges,
                    (PerformanceMeasurementUnit::Count, 3)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermReusedChildArcs,
                    (PerformanceMeasurementUnit::Count, 4)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermOwnedRootHandoffs,
                    (PerformanceMeasurementUnit::Count, 5)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermLeafRootClones,
                    (PerformanceMeasurementUnit::Count, 6)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermCompoundRootClones,
                    (PerformanceMeasurementUnit::Count, 7)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermMaterializationSlots,
                    (PerformanceMeasurementUnit::Count, 8)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermMaterializationChargedBytes,
                    (PerformanceMeasurementUnit::Bytes, 9)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermMaterializationCapacityStops,
                    (PerformanceMeasurementUnit::Count, 10)
                ),
                (
                    PerformanceMeasurementLabel::CertificateTermMaterializationLegacyFallbacks,
                    (PerformanceMeasurementUnit::Count, 11)
                ),
            ])
        );

        let mut off = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Off);
        off.observe_certificate_term_materialization(&observation);
        assert!(off.report().is_none());

        let mut saturating =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        saturating.observe_certificate_term_materialization(
            &CertificateTermMaterializationObservation {
                root_requests: u64::MAX,
                ..CertificateTermMaterializationObservation::default()
            },
        );
        saturating.observe_certificate_term_materialization(
            &CertificateTermMaterializationObservation {
                root_requests: 1,
                ..CertificateTermMaterializationObservation::default()
            },
        );
        let saturated = saturating.report().unwrap();
        assert!(saturated.overflowed);
        assert_eq!(
            saturated
                .counters
                .iter()
                .find(|counter| counter.label
                    == PerformanceMeasurementLabel::CertificateTermRootRequests)
                .unwrap()
                .value,
            u64::MAX
        );
    }

    #[test]
    fn performance_recorder_maps_term_observation() {
        certificate_term_materialization_projection_is_typed_and_saturating();
        certificate_term_materialization_labels_follow_v0_6_introduction();
    }

    #[test]
    fn package_term_memory_model_identifier_is_frozen() {
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV1.as_str(),
            "npa.fast-shard-memory.v1"
        );
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV2TermMaterialization.as_str(),
            "npa.fast-shard-memory.v2-term-materialization"
        );
        assert_eq!(
            PerformancePackageShardMemoryModel::FastShardMemoryV3TermMaterializationPreparedRetention
                .as_str(),
            "npa.fast-shard-memory.v3-term-materialization-prepared-retention"
        );
    }

    #[test]
    fn payload_and_snapshot_labels_follow_v0_7_introduction() {
        let labels = PerformanceMeasurementLabel::INTRODUCTIONS
            .iter()
            .filter_map(|(label, schema)| {
                (*schema == PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7).then_some(*label)
            })
            .collect::<Vec<_>>();
        assert_eq!(labels.len(), 30);
        for label in labels {
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_6,
                    label.as_str(),
                ),
                None,
            );
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7,
                    label.as_str(),
                ),
                Some(label),
            );
        }
    }

    #[test]
    fn committed_selection_labels_follow_v0_8_introduction() {
        let labels = PerformanceMeasurementLabel::INTRODUCTIONS
            .iter()
            .filter_map(|(label, schema)| {
                (*schema == PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8).then_some(*label)
            })
            .collect::<Vec<_>>();
        assert_eq!(labels.len(), 17);
        for label in labels {
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_7,
                    label.as_str(),
                ),
                None,
            );
            assert_eq!(
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA_V0_8,
                    label.as_str(),
                ),
                Some(label),
            );
        }
    }

    #[test]
    fn payload_and_snapshot_observations_use_typed_projection() {
        let certificate = CertificatePayloadObservation {
            payloads_frozen: 1,
            payload_unique_bytes: 2,
            session_snapshot_clones: 3,
            session_index_cow_copies: 4,
            session_index_cow_entries: 5,
            overflowed: false,
        };
        let package = PackagePayloadOwnershipObservation {
            module_payload_handle_clones: 6,
            avoided_module_payload_clone_bytes: 7,
            decode_cache_retained_bytes: 8,
            decode_cache_peak_retained_bytes: 9,
            decode_cache_capacity_stops: 10,
            process_memo_payload_handle_clones: 11,
            overflowed: false,
        };
        let artifacts = PackageCertificateArtifactObservation {
            artifact_files_read: 12,
            artifact_file_hashes: 13,
            artifact_full_decodes: 14,
            artifact_prepared_reuses: 15,
            key_candidate_current_bytes: 0,
            key_candidate_peak_bytes: 16,
            overflowed: false,
        };
        let retention = PreparedArtifactRetentionObservation {
            admissions: 17,
            admitted_bytes: 18,
            current_entries: 19,
            peak_entries: 20,
            current_bytes: 21,
            peak_bytes: 22,
            derivation_candidate_current_bytes: 0,
            derivation_candidate_peak_bytes: 23,
            entry_limit_fallbacks: 24,
            byte_limit_fallbacks: 25,
            saturated_charge_fallbacks: 26,
            charged_releases: 27,
            released_bytes: 28,
            overflowed: true,
        };
        let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        recorder.observe_certificate_payload_ownership(&certificate, &package);
        recorder.observe_package_certificate_artifacts(&artifacts, Some(&retention));
        let report = recorder.report().unwrap();
        assert_eq!(report.schema, PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9);
        assert!(report.overflowed);
        let value = |label| {
            report
                .counters
                .iter()
                .find(|counter| counter.label == label)
                .map(|counter| counter.value)
        };
        assert_eq!(
            value(PerformanceMeasurementLabel::PackageModulePayloadsFrozen),
            Some(1),
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::PackageDecodeCachePeakRetainedBytes),
            Some(9),
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::PackageArtifactPreparedReuses),
            Some(15),
        );
        assert_eq!(
            value(PerformanceMeasurementLabel::PackagePreparedArtifactReleasedBytes),
            Some(28),
        );
    }

    #[test]
    fn performance_child_identity_merge_is_absorbing_and_order_independent() {
        fn child(identity: Option<&str>, value: u64) -> PerformanceMeasurementReport {
            let recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
            let mut recorder = match identity {
                Some(identity) => recorder.with_input_identity(identity),
                None => recorder,
            };
            recorder.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, value);
            recorder.report().unwrap()
        }

        let none = child(None, 1);
        let a = child(Some("sha256:a"), 2);
        let same_a = child(Some("sha256:a"), 3);
        let b = child(Some("sha256:b"), 4);

        let mut adopted = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        adopted.merge_child_report_preserving_identity(&none);
        adopted.merge_child_report_preserving_identity(&a);
        adopted.merge_child_report_preserving_identity(&same_a);
        let adopted = adopted.report().unwrap();
        assert_eq!(adopted.input_identity.as_deref(), Some("sha256:a"));
        assert!(!adopted.overflowed);

        for children in [[&a, &b], [&b, &a]] {
            let mut conflict =
                PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
            for child in children {
                conflict.merge_child_report_preserving_identity(child);
            }
            conflict.merge_child_report_preserving_identity(&same_a);
            let conflict = conflict.report().unwrap();
            assert_eq!(conflict.input_identity, None);
            assert!(conflict.overflowed);
            assert_eq!(
                conflict
                    .counters
                    .iter()
                    .find(|counter| {
                        counter.label == PerformanceMeasurementLabel::PackageModulesChecked
                    })
                    .map(|counter| counter.value),
                Some(9)
            );
        }
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

    #[test]
    fn performance_measurement_json() {
        saturation_is_explicit_and_json_is_canonical();
        declaration_kernel_json_is_nullable_strict_and_stably_ordered();
        payload_and_snapshot_observations_use_typed_projection();
    }

    #[test]
    fn label_tables_are_canonical_per_schema() {
        label_table_is_exhaustive_unique_and_canonical();
        performance_measurement_historical_vocabularies_reject_newer_labels();
        package_selection_labels_follow_v0_5_introduction();
        certificate_term_materialization_labels_follow_v0_6_introduction();
        payload_and_snapshot_labels_follow_v0_7_introduction();
        committed_selection_labels_follow_v0_8_introduction();
    }

    #[test]
    fn performance_schema_availability_scaffold_preserves_current_writer() {
        assert_eq!(
            PERFORMANCE_MEASUREMENTS_SCHEMA,
            PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9
        );
        let recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
        assert_eq!(
            recorder.report().unwrap().schema,
            PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9
        );
    }

    #[test]
    fn unknown_future_measurement_schema_is_rejected() {
        assert!(PerformanceMeasurementLabel::labels_for_schema(
            "npa.performance.measurements.v0.10"
        )
        .is_none());
    }

    #[test]
    fn current_common_measurement_union_matches_rollout_decision() {
        performance_measurement_schema();
        assert_eq!(
            PERFORMANCE_MEASUREMENTS_SCHEMA,
            PERFORMANCE_MEASUREMENTS_SCHEMA_V0_9
        );
    }

    #[test]
    fn package_selection_observation_projects_closed_labels() {
        package_selection_observation_projection_matrix();
    }

    #[test]
    fn package_selection_observation_preserves_explicit_overflow_bit() {
        package_selection_observation_projection_matrix();
    }

    #[test]
    fn performance_identity_state_scaffold_transition_matrix() {
        performance_child_identity_merge_is_absorbing_and_order_independent();
    }

    #[test]
    fn performance_recorder_with_input_identity_sets_exact_state() {
        let recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary)
            .with_input_identity("sha256:exact");
        let report = recorder.report().unwrap();
        assert_eq!(report.input_identity.as_deref(), Some("sha256:exact"));
        assert!(!report.overflowed);
    }

    #[test]
    fn performance_child_identity_merge_transition_matrix() {
        performance_child_identity_merge_is_absorbing_and_order_independent();
    }

    #[test]
    fn performance_identity_conflict_omits_identity_and_marks_overflow() {
        performance_child_identity_merge_is_absorbing_and_order_independent();
    }

    #[test]
    fn performance_package_layer_prepared_fields() {
        payload_and_snapshot_observations_use_typed_projection();
        saturation_is_explicit_and_json_is_canonical();
    }

    #[test]
    fn performance_package_sharding_prepared_peaks() {
        package_term_memory_model_identifier_is_frozen();
        conflicting_package_sharding_summaries_merge_canonically();
    }

    #[test]
    fn performance_package_certificate_artifacts() {
        payload_and_snapshot_labels_follow_v0_7_introduction();
        payload_and_snapshot_observations_use_typed_projection();
    }

    #[test]
    fn package_decode_cache_charge_state() {
        assert_eq!(
            PackageDecodeCacheChargeState::from_payload_observation(false, None),
            PackageDecodeCacheChargeState::Disabled
        );
        assert_eq!(
            PackageDecodeCacheChargeState::from_payload_observation(true, None),
            PackageDecodeCacheChargeState::UnboundedUnknown
        );
        let observation = PackagePayloadOwnershipObservation {
            decode_cache_retained_bytes: 13,
            decode_cache_peak_retained_bytes: 21,
            ..PackagePayloadOwnershipObservation::default()
        };
        assert_eq!(
            PackageDecodeCacheChargeState::from_payload_observation(true, Some(&observation)),
            PackageDecodeCacheChargeState::Bounded {
                current_bytes: 13,
                peak_bytes: 21,
            }
        );
        assert_eq!(
            PackageDecodeCacheChargeState::from_payload_observation(false, Some(&observation)),
            PackageDecodeCacheChargeState::Disabled,
            "disabled cache accounting never imports an unrelated bounded observation"
        );
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.observe_certificate_payload_ownership(
            &CertificatePayloadObservation::default(),
            &observation,
        );
        let report = recorder.report().unwrap();
        assert_eq!(
            PackageDecodeCacheChargeState::from_measurement_report(true, Some(&report)),
            PackageDecodeCacheChargeState::Bounded {
                current_bytes: 13,
                peak_bytes: 21,
            }
        );
        assert_eq!(
            PackageDecodeCacheChargeState::from_measurement_report(true, None),
            PackageDecodeCacheChargeState::UnboundedUnknown
        );
        assert_eq!(
            PackageDecodeCacheChargeState::from_measurement_report(false, Some(&report)),
            PackageDecodeCacheChargeState::Disabled
        );
    }

    #[test]
    fn package_certificate_artifact_observation_updates() {
        let mut observation = PackageCertificateArtifactObservation::default();
        observation.observe_file_read();
        observation.observe_file_hash();
        observation.observe_full_decode();
        observation.observe_prepared_reuse();
        observation.begin_key_candidate(29);
        assert_eq!(observation.artifact_files_read, 1);
        assert_eq!(observation.artifact_file_hashes, 1);
        assert_eq!(observation.artifact_full_decodes, 1);
        assert_eq!(observation.artifact_prepared_reuses, 1);
        assert_eq!(observation.key_candidate_current_bytes, 29);
        assert_eq!(observation.key_candidate_peak_bytes, 29);
        observation.finish_key_candidate();
        assert_eq!(observation.key_candidate_current_bytes, 0);

        observation.artifact_files_read = u64::MAX;
        observation.observe_file_read();
        assert_eq!(observation.artifact_files_read, u64::MAX);
        assert!(observation.overflowed);
    }

    #[test]
    fn package_certificate_artifact_observation_merge() {
        let mut observation = PackageCertificateArtifactObservation {
            artifact_files_read: 2,
            artifact_prepared_reuses: 3,
            ..PackageCertificateArtifactObservation::default()
        };
        observation.merge_preparation(npa_package::PackageArtifactPreparationObservation {
            artifact_file_hashes: 5,
            artifact_full_decodes: 7,
            overflowed: false,
        });
        assert_eq!(observation.artifact_files_read, 2);
        assert_eq!(observation.artifact_file_hashes, 5);
        assert_eq!(observation.artifact_full_decodes, 7);
        assert_eq!(observation.artifact_prepared_reuses, 3);
        assert!(!observation.overflowed);

        observation.artifact_file_hashes = u64::MAX;
        observation.merge_preparation(npa_package::PackageArtifactPreparationObservation {
            artifact_file_hashes: 1,
            artifact_full_decodes: 0,
            overflowed: true,
        });
        assert_eq!(observation.artifact_file_hashes, u64::MAX);
        assert!(observation.overflowed);
    }

    fn declaration(
        module: &str,
        declaration_index: u64,
        kernel: Option<PerformanceAcceptedKernelMeasurement>,
    ) -> PerformanceDeclarationMeasurement {
        PerformanceDeclarationMeasurement {
            module: module.to_owned(),
            declaration_index,
            declaration: format!("{module}.d{declaration_index}"),
            term_nodes: 1,
            elaboration_elapsed_ns: 2,
            kernel,
        }
    }

    fn accepted_kernel_with_empty_hotset() -> PerformanceAcceptedKernelMeasurement {
        PerformanceAcceptedKernelMeasurement {
            subsystem: PerformanceKernelSubsystem::FastKernel,
            outcome: PerformanceAcceptedKernelOutcome::Accepted,
            fuel: PerformanceKernelFuelTotals {
                whnf: PerformanceKernelFuelDomainTotals {
                    calls: 1,
                    logical_spent: 10,
                    successful_operation_fuel: 10,
                    exhausted_operation_fuel: 0,
                    overflowed: false,
                },
                conversion: PerformanceKernelFuelDomainTotals {
                    calls: 2,
                    logical_spent: 20,
                    successful_operation_fuel: 20,
                    exhausted_operation_fuel: 0,
                    overflowed: false,
                },
            },
            work: PerformanceKernelWork {
                check_calls: 1,
                infer_calls: 2,
                whnf_calls: 3,
                defeq_calls: 4,
                quick_equality_hits: 5,
                beta_steps: 6,
                delta_steps: 0,
                iota_steps: 7,
                physical_reductions: 13,
                overflowed: false,
            },
            retained_delta_constants: PerformanceKernelDeltaHotsetSummary {
                retained_names: 0,
                capacity: 256,
                entries: Vec::new(),
                emitted: 0,
                entry_limit: 16,
                unretained_name_observations: 0,
                overlong_name_observations: 0,
                output_truncated: false,
                overflowed: false,
            },
            overflowed: false,
        }
    }

    fn targeted_authoring_labels() -> &'static [(
        PerformanceMeasurementLabel,
        &'static str,
        PerformanceMeasurementUnit,
    )] {
        &[
            (
                PerformanceMeasurementLabel::CacheSupportSelected,
                "cache.support_selected",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheTargetsForcedLive,
                "cache.targets_forced_live",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheContextIneligible,
                "cache.context_ineligible",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheContextBypassedHits,
                "cache.context_bypassed_hits",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheContextStale,
                "cache.context_stale",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheContextSchemaMisses,
                "cache.context_schema_misses",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheAvoidedSourceInterfaceResolutions,
                "cache.avoided_source_interface_resolutions",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheTargetFreshBuilds,
                "cache.target_fresh_builds",
                PerformanceMeasurementUnit::Count,
            ),
            (
                PerformanceMeasurementLabel::CacheToolIdentityBytes,
                "cache.tool_identity_bytes",
                PerformanceMeasurementUnit::Bytes,
            ),
            (
                PerformanceMeasurementLabel::CacheToolIdentityElapsed,
                "cache.tool_identity_elapsed",
                PerformanceMeasurementUnit::Nanoseconds,
            ),
            (
                PerformanceMeasurementLabel::CacheCurrentByteValidationElapsed,
                "cache.current_byte_validation_elapsed",
                PerformanceMeasurementUnit::Nanoseconds,
            ),
            (
                PerformanceMeasurementLabel::CacheLiveSupportElapsed,
                "cache.live_support_elapsed",
                PerformanceMeasurementUnit::Nanoseconds,
            ),
            (
                PerformanceMeasurementLabel::CacheSourceInterfaceResolutionElapsed,
                "cache.source_interface_resolution_elapsed",
                PerformanceMeasurementUnit::Nanoseconds,
            ),
            (
                PerformanceMeasurementLabel::CacheBytesLoaded,
                "cache.bytes_loaded",
                PerformanceMeasurementUnit::Bytes,
            ),
            (
                PerformanceMeasurementLabel::CacheBytesWritten,
                "cache.bytes_written",
                PerformanceMeasurementUnit::Bytes,
            ),
        ]
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
            prepared_shared_bytes: 0,
            combined_shared_bytes: 10,
            per_worker_bytes: 20,
            term_materialization_bytes_per_worker: 268_435_456,
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
