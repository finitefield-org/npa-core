//! Argument model and parser for the `npa` binary.

use std::collections::BTreeSet;
use std::fmt;
use std::path::PathBuf;

use npa_cert::Name;

/// Parsed top-level CLI action.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliAction {
    /// Execute a parsed command.
    Run(CliCommand),
    /// Render deterministic help for the selected topic.
    Help(HelpTopic),
    /// Print the `npa` CLI package version.
    Version,
}

/// Parsed top-level command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliCommand {
    /// `npa package ...`.
    Package(PackageCommand),
}

impl CliCommand {
    /// Stable command name used in diagnostics.
    pub fn command_name(&self) -> &'static str {
        match self {
            Self::Package(command) => command.command_name(),
        }
    }
}

/// Parsed `npa package` subcommand.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageCommand {
    /// `npa package check`.
    Check(PackageCommonOptions),
    /// `npa package build-certs`.
    BuildCerts(PackageBuildCertsOptions),
    /// `npa package axiom-report`.
    AxiomReport(PackageAxiomReportOptions),
    /// `npa package index`.
    Index(PackageIndexOptions),
    /// `npa package theorem-premise-report`.
    TheoremPremiseReport(PackageTheoremPremiseReportOptions),
    /// `npa package export-summary`.
    ExportSummary(PackageExportSummaryOptions),
    /// `npa package export-candidate-metadata`.
    ExportCandidateMetadata(PackageCandidateMetadataOptions),
    /// `npa package validate-l2-acceptance`.
    ValidateL2Acceptance(PackageL2AcceptanceOptions),
    /// `npa package prepare-l2-review-input`.
    PrepareL2ReviewInput(PackageL2ReviewInputOptions),
    /// `npa package aggregate-l2-acceptance`.
    AggregateL2Acceptance(Box<PackageL2AcceptanceAggregateOptions>),
    /// `npa package validate-l2-namespace-transport`.
    ValidateL2NamespaceTransport(Box<PackageL2NamespaceTransportOptions>),
    /// `npa package prepare-promotion`.
    PreparePromotion(Box<PackagePreparePromotionOptions>),
    /// `npa package materialize-promotion`.
    MaterializePromotion(Box<PackageMaterializePromotionOptions>),
    /// `npa package validate-promotion-materialization`.
    ValidatePromotionMaterialization(Box<PackageValidatePromotionMaterializationOptions>),
    /// `npa package validate-promotion-origin-registry`.
    ValidatePromotionOriginRegistry(PackageValidatePromotionOriginRegistryOptions),
    /// `npa package register-equivalent-promotion-origin`.
    RegisterEquivalentPromotionOrigin(PackageRegisterEquivalentPromotionOriginOptions),
    /// `npa package verify-certs`.
    VerifyCerts(PackageVerifyCertsOptions),
    /// `npa package check-hashes`.
    CheckHashes(PackageCommonOptions),
    /// `npa package audit-artifact-ledger`.
    AuditArtifactLedger(PackageArtifactLedgerAuditOptions),
    /// `npa package lock ...`.
    Lock(PackageLockCommand),
    /// `npa package publish-plan`.
    PublishPlan(PackagePublishPlanOptions),
    /// `npa package check-generated`.
    CheckGenerated(PackageCheckGeneratedOptions),
    /// `npa package high-trust`.
    HighTrust(Box<PackageHighTrustOptions>),
    /// `npa package gate-plan`.
    GatePlan(PackageGatePlanOptions),
    /// `npa package refactor-plan`.
    RefactorPlan(PackageRefactorPlanOptions),
}

impl PackageCommand {
    /// Stable command name used in diagnostics.
    pub fn command_name(&self) -> &'static str {
        match self {
            Self::Check(_) => "package check",
            Self::BuildCerts(_) => "package build-certs",
            Self::AxiomReport(_) => "package axiom-report",
            Self::Index(_) => "package index",
            Self::TheoremPremiseReport(_) => "package theorem-premise-report",
            Self::ExportSummary(_) => "package export-summary",
            Self::ExportCandidateMetadata(_) => "package export-candidate-metadata",
            Self::ValidateL2Acceptance(_) => "package validate-l2-acceptance",
            Self::PrepareL2ReviewInput(_) => "package prepare-l2-review-input",
            Self::AggregateL2Acceptance(_) => "package aggregate-l2-acceptance",
            Self::ValidateL2NamespaceTransport(_) => "package validate-l2-namespace-transport",
            Self::PreparePromotion(_) => "package prepare-promotion",
            Self::MaterializePromotion(_) => "package materialize-promotion",
            Self::ValidatePromotionMaterialization(_) => {
                "package validate-promotion-materialization"
            }
            Self::ValidatePromotionOriginRegistry(_) => {
                "package validate-promotion-origin-registry"
            }
            Self::RegisterEquivalentPromotionOrigin(_) => {
                "package register-equivalent-promotion-origin"
            }
            Self::VerifyCerts(_) => "package verify-certs",
            Self::CheckHashes(_) => "package check-hashes",
            Self::AuditArtifactLedger(_) => "package audit-artifact-ledger",
            Self::Lock(command) => command.command_name(),
            Self::PublishPlan(_) => "package publish-plan",
            Self::CheckGenerated(_) => "package check-generated",
            Self::HighTrust(_) => "package high-trust",
            Self::GatePlan(_) => "package gate-plan",
            Self::RefactorPlan(_) => "package refactor-plan",
        }
    }

    /// Common options for the package subcommand.
    pub fn common_options(&self) -> &PackageCommonOptions {
        match self {
            Self::Check(options) | Self::CheckHashes(options) => options,
            Self::AuditArtifactLedger(options) => &options.common,
            Self::Lock(command) => command.common_options(),
            Self::BuildCerts(options) => &options.common,
            Self::AxiomReport(options) => &options.common,
            Self::Index(options) => &options.common,
            Self::TheoremPremiseReport(options) => &options.common,
            Self::ExportSummary(options) => &options.common,
            Self::ExportCandidateMetadata(options) => &options.common,
            Self::ValidateL2Acceptance(options) => &options.common,
            Self::PrepareL2ReviewInput(options) => &options.common,
            Self::AggregateL2Acceptance(options) => &options.common,
            Self::ValidateL2NamespaceTransport(options) => &options.common,
            Self::PreparePromotion(options) => &options.common,
            Self::MaterializePromotion(options) => &options.common,
            Self::ValidatePromotionMaterialization(options) => &options.common,
            Self::ValidatePromotionOriginRegistry(options) => &options.common,
            Self::RegisterEquivalentPromotionOrigin(options) => &options.common,
            Self::VerifyCerts(options) => &options.common,
            Self::PublishPlan(options) => &options.common,
            Self::CheckGenerated(options) => &options.common,
            Self::HighTrust(options) => &options.common,
            Self::GatePlan(options) => &options.common,
            Self::RefactorPlan(options) => &options.common,
        }
    }
}

/// Parsed `npa package lock` subcommand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageLockCommand {
    /// `npa package lock check`.
    Check(PackageCommonOptions),
    /// `npa package lock write`.
    Write(PackageCommonOptions),
}

impl PackageLockCommand {
    /// Stable command name used in diagnostics.
    pub fn command_name(&self) -> &'static str {
        match self {
            Self::Check(_) => "package lock check",
            Self::Write(_) => "package lock write",
        }
    }

    /// Common options for the package lock subcommand.
    pub fn common_options(&self) -> &PackageCommonOptions {
        match self {
            Self::Check(options) | Self::Write(options) => options,
        }
    }
}

/// Common options accepted by each package subcommand.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageCommonOptions {
    /// Package root path. Defaults to `.` without parent search.
    pub root: PathBuf,
    /// Whether deterministic JSON output was requested.
    pub json: bool,
}

impl Default for PackageCommonOptions {
    fn default() -> Self {
        Self {
            root: PathBuf::from("."),
            json: false,
        }
    }
}

/// Options for the non-mutating package artifact-ledger audit.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageArtifactLedgerAuditOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Optional explicit local modules to audit.
    pub modules: Vec<Name>,
}

/// Scope selected for `package refactor-plan`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageRefactorPlanScope {
    /// Rank module refactor candidates.
    Modules,
    /// Rank theorem-family refactor candidates.
    Theorems,
    /// Rank both module and theorem-family refactor candidates.
    Both,
}

/// Options for `package refactor-plan`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageRefactorPlanOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Candidate scope to emit.
    pub scope: PackageRefactorPlanScope,
    /// Optional local module filter.
    pub module: Option<Name>,
    /// Maximum number of sorted candidates to emit.
    pub top: usize,
    /// Reserved source-reading metrics flag. Rejected by the MVP parser.
    pub include_source_metrics: bool,
}

/// Options for `package gate-plan`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageGatePlanOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Git merge-base comparison base for `git diff --name-only <base>...HEAD`.
    pub base: String,
}

/// Options for `package build-certs`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageBuildCertsOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: rebuild in memory without writing files.
    pub check: bool,
    /// Local build-check cache mode for check mode.
    pub build_check_cache: PackageBuildCheckCacheMode,
    /// Refresh local module hash pins in npa-package.toml after rebuilding certificates.
    pub update_manifest_hashes: bool,
    /// Local-module build selection.
    pub selection: PackageBuildSelection,
}

/// Local-module selection for `package build-certs`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageBuildSelection {
    /// Rebuild every local module.
    Full,
    /// Rebuild explicitly named local modules.
    Modules(Vec<Name>),
    /// Derive the selection from changed package authoring paths in Git.
    Changed,
}

/// Local package build-check cache mode for `package build-certs --check`.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageBuildCheckCacheMode {
    /// Do not read or write package build-check cache entries.
    Off,
    /// Read cache entries for diagnostics, but still run live build comparison.
    ReadThrough,
}

impl PackageBuildCheckCacheMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::ReadThrough => "read-through",
        }
    }

    /// Return whether this mode reads or writes the local build-check cache store.
    pub fn uses_local_store(self) -> bool {
        match self {
            Self::Off => false,
            Self::ReadThrough => true,
        }
    }
}

/// Options for `package axiom-report`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageAxiomReportOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package index`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageIndexOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package theorem-premise-report`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageTheoremPremiseReportOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package export-summary`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageExportSummaryOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Optional package-relative output path.
    pub out: Option<PathBuf>,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package export-candidate-metadata`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageCandidateMetadataOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Module containing the candidate theorem.
    pub module: String,
    /// Theorem declaration to export.
    pub declaration: String,
    /// Package-relative output path.
    pub out: PathBuf,
}

/// Options for `package validate-l2-acceptance`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageL2AcceptanceOptions {
    /// Common package command options for the source proof package.
    pub common: PackageCommonOptions,
    /// Workspace-relative canonical authority policy path.
    pub policy: PathBuf,
    /// Workspace-relative source acceptance record path.
    pub acceptance: PathBuf,
    /// Optional local modules whose complete public theorem inventory is required.
    pub modules: Vec<Name>,
}

/// Options for `package prepare-l2-review-input`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageL2ReviewInputOptions {
    /// Common source package options.
    pub common: PackageCommonOptions,
    /// Canonical L2 policy path.
    pub policy: PathBuf,
    /// Selected local module.
    pub module: String,
    /// Selected theorem declaration.
    pub declaration: String,
    /// Package-relative immutable output path.
    pub out: PathBuf,
    /// Compare with an existing output without writing.
    pub check: bool,
}

/// Options for `package aggregate-l2-acceptance`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageL2AcceptanceAggregateOptions {
    /// Common source package options.
    pub common: PackageCommonOptions,
    /// Canonical current L2 policy path.
    pub policy: PathBuf,
    /// Package-relative review input paths.
    pub review_inputs: Vec<PathBuf>,
    /// Package-relative review report paths.
    pub reviews: Vec<PathBuf>,
    /// Explicit package-relative existing v2 ledger.
    pub existing: Option<PathBuf>,
    /// Existing theorem keys explicitly authorized for replacement.
    pub replacements: Vec<(Name, Name)>,
    /// Package-relative output path.
    pub out: PathBuf,
    /// Compare with an existing output without writing.
    pub check: bool,
}

/// Options for `package validate-l2-namespace-transport`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageL2NamespaceTransportOptions {
    /// Common output options; its root is the source package root.
    pub common: PackageCommonOptions,
    /// Clean target baseline package root.
    pub target_baseline_root: PathBuf,
    /// Materialized target package root.
    pub target_root: PathBuf,
    /// Canonical source acceptance policy path.
    pub acceptance_policy: PathBuf,
    /// Source-root-relative v2 acceptance path.
    pub source_acceptance: PathBuf,
    /// Canonical namespace transport policy path.
    pub transport_policy: PathBuf,
    /// Source-root-relative transport request path.
    pub mapping: PathBuf,
    /// Optional source-root-relative attestation path.
    pub out: Option<PathBuf>,
    /// Compare with an existing attestation without writing.
    pub check: bool,
}

/// Options for `package prepare-promotion`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackagePreparePromotionOptions {
    /// Common options; the root is the source package root.
    pub common: PackageCommonOptions,
    /// Clean target package baseline.
    pub target_baseline_root: PathBuf,
    /// Canonical current L2 policy.
    pub acceptance_policy: Option<PathBuf>,
    /// Source-root-relative v2 acceptance ledger.
    pub source_acceptance: Option<PathBuf>,
    /// Canonical namespace-transport policy.
    pub transport_policy: Option<PathBuf>,
    /// Source-root-relative mapping request.
    pub mapping: Option<PathBuf>,
    /// Source-root-relative declaration selection request for plan v2.
    pub declaration_request: Option<PathBuf>,
    /// Optional artifact-identical source package roots.
    pub equivalent_origin_roots: Vec<PathBuf>,
    /// Source-root-relative canonical plan output.
    pub out: PathBuf,
    /// Compare the existing plan without writing.
    pub check: bool,
}

/// Safety phase selected for `package materialize-promotion`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackagePromotionPhase {
    /// Materialize into a disposable package copy without changing the registry.
    Temporary,
    /// Materialize into the tracked target and update the registry.
    Tracked,
}

impl PackagePromotionPhase {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Temporary => "temporary",
            Self::Tracked => "tracked",
        }
    }
}

/// Options for `package materialize-promotion` normal or recovery mode.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageMaterializePromotionOptions {
    /// Common options; root is meaningful only in normal mode.
    pub common: PackageCommonOptions,
    /// Clean target package baseline in normal mode.
    pub target_baseline_root: Option<PathBuf>,
    /// Candidate or tracked target root.
    pub target_root: PathBuf,
    /// Source-root-relative promotion plan in normal mode.
    pub plan: Option<PathBuf>,
    /// Artifact-identical source roots bound by the plan in normal mode.
    pub equivalent_origin_roots: Vec<PathBuf>,
    /// Source-root-relative transport attestation for tracked mode.
    pub transport_attestation: Option<PathBuf>,
    /// Source-root-relative verified materialization attestation for plan v2 tracked mode.
    pub verification_attestation: Option<PathBuf>,
    /// Explicit safety phase in normal mode.
    pub phase: Option<PackagePromotionPhase>,
    /// Whether the validated change set may be written.
    pub apply: bool,
    /// Recovery journal path; when present all normal-mode options are absent.
    pub recover: Option<PathBuf>,
}

/// Options for `package validate-promotion-materialization`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageValidatePromotionMaterializationOptions {
    /// Common options; root is the source package root.
    pub common: PackageCommonOptions,
    /// Clean target package baseline.
    pub target_baseline_root: PathBuf,
    /// Already materialized disposable target copy.
    pub target_root: PathBuf,
    /// Source-root-relative declaration promotion plan v2.
    pub plan: PathBuf,
    /// Source-root-relative canonical attestation output.
    pub out: PathBuf,
    /// Compare an existing attestation without writing.
    pub check: bool,
}

/// Options for `package validate-promotion-origin-registry`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageValidatePromotionOriginRegistryOptions {
    /// Common options; root is the target package root.
    pub common: PackageCommonOptions,
    /// Optional source roots used for source-identity validation.
    pub source_roots: Vec<PathBuf>,
    /// Optional previous registry used for append-only transition validation.
    pub previous_registry: Option<PathBuf>,
}

/// Options for `package register-equivalent-promotion-origin`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageRegisterEquivalentPromotionOriginOptions {
    /// Common options; root is the new equivalent source package.
    pub common: PackageCommonOptions,
    /// Target package containing the canonical registry.
    pub target_root: PathBuf,
    /// Existing promotion route to extend.
    pub promotion_id: String,
    /// Whether the validated registry replacement may be written.
    pub apply: bool,
}

/// Options for `package publish-plan`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackagePublishPlanOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package check-generated`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageCheckGeneratedOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package high-trust`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageHighTrustOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Workspace-relative release policy path.
    pub release_policy: PathBuf,
    /// Expected canonical release policy hash.
    pub release_policy_hash: String,
    /// Workspace-relative high-trust runner policy path.
    pub runner_policy: PathBuf,
    /// Expected canonical runner policy hash.
    pub runner_policy_hash: String,
    /// Workspace-relative high-trust challenge runner policy path.
    pub challenge_runner_policy: PathBuf,
    /// Expected canonical challenge runner policy hash.
    pub challenge_runner_policy_hash: String,
    /// Workspace-relative checker binary registry path.
    pub checker_registry: PathBuf,
    /// Optional workspace-relative output path. Defaults under package root.
    pub out: Option<PathBuf>,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
}

/// Options for `package verify-certs`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageVerifyCertsOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Checker mode selected for source-free verification.
    pub checker: PackageChecker,
    /// Verify only package modules whose certificate files are changed in Git.
    pub changed: bool,
    /// Local package audit cache mode.
    pub audit_cache: PackageAuditCacheMode,
    /// Local verifier memo mode.
    pub verifier_memo: PackageVerifierMemoMode,
    /// Maximum verifier worker count.
    pub jobs: usize,
    /// Required external checker runner inputs when `checker = external`.
    pub external: Option<PackageExternalCheckerOptions>,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
    /// Package-lock input selected for certificate verification.
    pub package_lock_mode: PackageLockInputMode,
}

/// Optional package audit timing telemetry mode.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageTimingMode {
    /// Do not collect or render timing telemetry.
    Off,
    /// Collect stable command phase totals.
    Summary,
    /// Collect stable command phase totals with the detailed mode label.
    Detailed,
}

impl PackageTimingMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Summary => "summary",
            Self::Detailed => "detailed",
        }
    }

    /// Return whether this mode emits timing telemetry.
    pub const fn is_enabled(self) -> bool {
        match self {
            Self::Off => false,
            Self::Summary | Self::Detailed => true,
        }
    }
}

/// Options required by `package verify-certs --checker external`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageExternalCheckerOptions {
    /// Package-relative runner policy path.
    pub runner_policy: PathBuf,
    /// Expected canonical runner policy hash.
    pub runner_policy_hash: String,
    /// Package-relative checker binary registry path.
    pub checker_registry: PathBuf,
}

/// Supported package certificate checker modes.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageChecker {
    /// CLR-03 source-free reference checker path.
    Reference,
    /// CLR-03 fast kernel verifier path for local development.
    Fast,
    /// CLR-08 external checker runner path.
    External,
}

impl PackageChecker {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Reference => "reference",
            Self::Fast => "fast",
            Self::External => "external",
        }
    }
}

/// Local package audit cache mode for `package verify-certs`.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageAuditCacheMode {
    /// Do not read or write package audit cache entries.
    Off,
    /// Read cache entries for diagnostics, but still run live verification.
    ReadThrough,
    /// Use exact accepted local cache hits for local-only audit acceleration.
    LocalHit,
}

impl PackageAuditCacheMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::ReadThrough => "read-through",
            Self::LocalHit => "local-hit",
        }
    }

    /// Return whether this mode reads the local audit cache store.
    pub fn uses_local_store(self) -> bool {
        match self {
            Self::Off => false,
            Self::ReadThrough | Self::LocalHit => true,
        }
    }
}

/// Local verifier memo mode for `package verify-certs`.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageVerifierMemoMode {
    /// Do not read or write disk-backed verifier memo entries.
    Off,
    /// Read and write disk-backed verifier memo entries, but still run live verification.
    ReadThrough,
    /// Use exact accepted disk-backed verifier memo hits for local-only audit acceleration.
    Disk,
}

/// Package-lock input used for `package verify-certs`.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageLockInputMode {
    /// Read and validate the checked `generated/package-lock.json` artifact.
    CheckedFile,
    /// Reconstruct and validate the package lock in memory.
    ReconstructedInMemory,
}

impl PackageLockInputMode {
    /// Return the stable public spelling of this package-lock input mode.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CheckedFile => "checked",
            Self::ReconstructedInMemory => "reconstructed",
        }
    }
}

impl PackageVerifierMemoMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::ReadThrough => "read-through",
            Self::Disk => "disk",
        }
    }

    /// Return whether this mode reads or writes the local disk memo store.
    pub fn uses_local_store(self) -> bool {
        match self {
            Self::Off => false,
            Self::ReadThrough | Self::Disk => true,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PackageBuildOptionsValidationError {
    BuildCheckCacheWithRefresh,
    BuildCheckCacheWithoutCheck,
    TargetedBuildCheckCache,
    TargetedWriteRequiresRefresh,
    EmptyModuleSelection,
    DuplicateModuleSelection,
}

pub(crate) fn validate_package_build_certs_options(
    options: &PackageBuildCertsOptions,
) -> Result<(), PackageBuildOptionsValidationError> {
    if let PackageBuildSelection::Modules(modules) = &options.selection {
        if modules.is_empty() {
            return Err(PackageBuildOptionsValidationError::EmptyModuleSelection);
        }
        let mut seen = BTreeSet::new();
        if modules.iter().any(|module| !seen.insert(module)) {
            return Err(PackageBuildOptionsValidationError::DuplicateModuleSelection);
        }
    }
    if !matches!(options.selection, PackageBuildSelection::Full)
        && options.build_check_cache.uses_local_store()
    {
        return Err(PackageBuildOptionsValidationError::TargetedBuildCheckCache);
    }
    if !matches!(options.selection, PackageBuildSelection::Full)
        && !options.check
        && !options.update_manifest_hashes
    {
        return Err(PackageBuildOptionsValidationError::TargetedWriteRequiresRefresh);
    }
    if options.update_manifest_hashes && options.build_check_cache.uses_local_store() {
        return Err(PackageBuildOptionsValidationError::BuildCheckCacheWithRefresh);
    }
    if options.build_check_cache.uses_local_store() && !options.check {
        return Err(PackageBuildOptionsValidationError::BuildCheckCacheWithoutCheck);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PackageExternalCheckerOptionsState {
    Absent,
    Partial,
    Complete,
}

impl PackageExternalCheckerOptionsState {
    fn from_flags(runner_policy: bool, runner_policy_hash: bool, checker_registry: bool) -> Self {
        match (runner_policy, runner_policy_hash, checker_registry) {
            (false, false, false) => Self::Absent,
            (true, true, true) => Self::Complete,
            _ => Self::Partial,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PackageVerifyOptionsValidationInput {
    checker: PackageChecker,
    changed: bool,
    audit_cache: PackageAuditCacheMode,
    verifier_memo: PackageVerifierMemoMode,
    jobs: usize,
    external_options: PackageExternalCheckerOptionsState,
    package_lock_mode: PackageLockInputMode,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PackageVerifyOptionsValidationError {
    JobsZero,
    ChangedWithExternalChecker,
    ChangedWithAuditCache,
    ChangedWithVerifierMemo,
    ExternalCheckerWithParallelJobs,
    ExternalCheckerWithAuditCache,
    ExternalCheckerWithVerifierMemo,
    ExternalCheckerWithReconstructedLock,
    AuditCacheWithParallelJobs,
    AuditCacheWithVerifierMemo,
    MissingExternalCheckerOptions,
    UnexpectedExternalCheckerOptions,
}

pub(crate) fn validate_package_verify_certs_options(
    options: &PackageVerifyCertsOptions,
) -> Result<(), PackageVerifyOptionsValidationError> {
    validate_package_verify_options(PackageVerifyOptionsValidationInput {
        checker: options.checker,
        changed: options.changed,
        audit_cache: options.audit_cache,
        verifier_memo: options.verifier_memo,
        jobs: options.jobs,
        external_options: if options.external.is_some() {
            PackageExternalCheckerOptionsState::Complete
        } else {
            PackageExternalCheckerOptionsState::Absent
        },
        package_lock_mode: options.package_lock_mode,
    })
}

fn validate_package_verify_options(
    options: PackageVerifyOptionsValidationInput,
) -> Result<(), PackageVerifyOptionsValidationError> {
    if !package_verify_jobs_are_valid(options.jobs) {
        return Err(PackageVerifyOptionsValidationError::JobsZero);
    }
    if options.changed && options.checker == PackageChecker::External {
        return Err(PackageVerifyOptionsValidationError::ChangedWithExternalChecker);
    }
    if options.changed && options.audit_cache.uses_local_store() {
        return Err(PackageVerifyOptionsValidationError::ChangedWithAuditCache);
    }
    if options.changed && options.verifier_memo.uses_local_store() {
        return Err(PackageVerifyOptionsValidationError::ChangedWithVerifierMemo);
    }
    if options.checker == PackageChecker::External && options.jobs > 1 {
        return Err(PackageVerifyOptionsValidationError::ExternalCheckerWithParallelJobs);
    }
    if options.checker == PackageChecker::External && options.audit_cache.uses_local_store() {
        return Err(PackageVerifyOptionsValidationError::ExternalCheckerWithAuditCache);
    }
    if options.checker == PackageChecker::External && options.verifier_memo.uses_local_store() {
        return Err(PackageVerifyOptionsValidationError::ExternalCheckerWithVerifierMemo);
    }
    if options.checker == PackageChecker::External
        && options.package_lock_mode == PackageLockInputMode::ReconstructedInMemory
    {
        return Err(PackageVerifyOptionsValidationError::ExternalCheckerWithReconstructedLock);
    }
    if options.audit_cache.uses_local_store() && options.jobs > 1 {
        return Err(PackageVerifyOptionsValidationError::AuditCacheWithParallelJobs);
    }
    if options.audit_cache.uses_local_store() && options.verifier_memo.uses_local_store() {
        return Err(PackageVerifyOptionsValidationError::AuditCacheWithVerifierMemo);
    }
    match (options.checker, options.external_options) {
        (PackageChecker::External, PackageExternalCheckerOptionsState::Complete)
        | (
            PackageChecker::Reference | PackageChecker::Fast,
            PackageExternalCheckerOptionsState::Absent,
        ) => Ok(()),
        (PackageChecker::External, _) => {
            Err(PackageVerifyOptionsValidationError::MissingExternalCheckerOptions)
        }
        (PackageChecker::Reference | PackageChecker::Fast, _) => {
            Err(PackageVerifyOptionsValidationError::UnexpectedExternalCheckerOptions)
        }
    }
}

const fn package_verify_jobs_are_valid(jobs: usize) -> bool {
    jobs > 0
}

/// Help topic selected by `--help`.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HelpTopic {
    /// Top-level `npa` help.
    Root,
    /// `npa package` help.
    Package,
    /// `npa package check --help`.
    PackageCheck,
    /// `npa package build-certs --help`.
    PackageBuildCerts,
    /// `npa package axiom-report --help`.
    PackageAxiomReport,
    /// `npa package index --help`.
    PackageIndex,
    /// `npa package theorem-premise-report --help`.
    PackageTheoremPremiseReport,
    /// `npa package export-summary --help`.
    PackageExportSummary,
    /// `npa package export-candidate-metadata --help`.
    PackageExportCandidateMetadata,
    /// `npa package validate-l2-acceptance --help`.
    PackageValidateL2Acceptance,
    /// `npa package prepare-l2-review-input --help`.
    PackagePrepareL2ReviewInput,
    /// `npa package aggregate-l2-acceptance --help`.
    PackageAggregateL2Acceptance,
    /// `npa package validate-l2-namespace-transport --help`.
    PackageValidateL2NamespaceTransport,
    /// `npa package prepare-promotion --help`.
    PackagePreparePromotion,
    /// `npa package materialize-promotion --help`.
    PackageMaterializePromotion,
    /// `npa package validate-promotion-materialization --help`.
    PackageValidatePromotionMaterialization,
    /// `npa package validate-promotion-origin-registry --help`.
    PackageValidatePromotionOriginRegistry,
    /// `npa package register-equivalent-promotion-origin --help`.
    PackageRegisterEquivalentPromotionOrigin,
    /// `npa package verify-certs --help`.
    PackageVerifyCerts,
    /// `npa package check-hashes --help`.
    PackageCheckHashes,
    /// `npa package audit-artifact-ledger --help`.
    PackageAuditArtifactLedger,
    /// `npa package lock --help`.
    PackageLock,
    /// `npa package lock check --help`.
    PackageLockCheck,
    /// `npa package lock write --help`.
    PackageLockWrite,
    /// `npa package publish-plan --help`.
    PackagePublishPlan,
    /// `npa package check-generated --help`.
    PackageCheckGenerated,
    /// `npa package high-trust --help`.
    PackageHighTrust,
    /// `npa package gate-plan --help`.
    PackageGatePlan,
    /// `npa package refactor-plan --help`.
    PackageRefactorPlan,
}

/// Stable usage error produced by the argument parser.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CliUsageError {
    /// Machine-readable reason code.
    pub reason: UsageReason,
    /// Command context, when known.
    pub command: Option<String>,
    /// Flag involved in the error, when applicable.
    pub flag: Option<String>,
    /// Value involved in the error, when applicable.
    pub value: Option<String>,
}

impl CliUsageError {
    fn new(reason: UsageReason) -> Self {
        Self {
            reason,
            command: None,
            flag: None,
            value: None,
        }
    }

    fn with_command(mut self, command: impl Into<String>) -> Self {
        self.command = Some(command.into());
        self
    }

    fn with_flag(mut self, flag: impl Into<String>) -> Self {
        self.flag = Some(flag.into());
        self
    }

    fn with_value(mut self, value: impl Into<String>) -> Self {
        self.value = Some(value.into());
        self
    }

    /// Deterministic human-readable usage diagnostic.
    pub fn render_human(&self) -> String {
        let mut message = format!("error: {}", self.reason.reason_code());
        if let Some(command) = &self.command {
            message.push_str(&format!(" command={command}"));
        }
        if let Some(flag) = &self.flag {
            message.push_str(&format!(" flag={flag}"));
        }
        if let Some(value) = &self.value {
            message.push_str(&format!(" value={value}"));
        }
        message
    }
}

impl fmt::Display for CliUsageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render_human())
    }
}

impl std::error::Error for CliUsageError {}

/// Stable usage reason codes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UsageReason {
    /// Unknown command or subcommand.
    UnknownCommand,
    /// Unknown flag.
    UnknownFlag,
    /// Flag requires a value but none was provided.
    MissingFlagValue,
    /// Flag was provided more than once.
    DuplicateFlag,
    /// A selected mode requires a flag that was not provided.
    MissingRequiredFlag,
    /// Known flag is outside CLR-04 scope or the selected command.
    UnsupportedFlag,
    /// Flag value has the wrong deterministic shape.
    InvalidFlagValue,
    /// Module name is not a canonical dotted NPA name.
    InvalidModuleName,
    /// Checker mode is outside CLR-04 scope.
    UnsupportedChecker,
    /// Package audit cache mode is unsupported.
    UnsupportedAuditCacheMode,
    /// Package verifier memo mode is unsupported.
    UnsupportedVerifierMemoMode,
    /// Package build-check cache mode is unsupported.
    UnsupportedBuildCheckCacheMode,
    /// Package timing telemetry mode is unsupported.
    UnsupportedTimingMode,
}

impl UsageReason {
    /// Stable reason code used by later structured diagnostics.
    pub fn reason_code(self) -> &'static str {
        match self {
            Self::UnknownCommand => "unknown_command",
            Self::UnknownFlag => "unknown_flag",
            Self::MissingFlagValue => "missing_flag_value",
            Self::DuplicateFlag => "duplicate_flag",
            Self::MissingRequiredFlag => "missing_required_flag",
            Self::UnsupportedFlag => "unsupported_flag",
            Self::InvalidFlagValue => "invalid_flag_value",
            Self::InvalidModuleName => "invalid_module_name",
            Self::UnsupportedChecker => "unsupported_checker",
            Self::UnsupportedAuditCacheMode => "unsupported_audit_cache_mode",
            Self::UnsupportedVerifierMemoMode => "unsupported_verifier_memo_mode",
            Self::UnsupportedBuildCheckCacheMode => "unsupported_build_check_cache_mode",
            Self::UnsupportedTimingMode => "unsupported_timing_mode",
        }
    }
}

/// Parse `npa` arguments, excluding the binary name.
pub fn parse_cli_args<I, S>(args: I) -> Result<CliAction, CliUsageError>
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
    if args.is_empty() {
        return Ok(CliAction::Help(HelpTopic::Root));
    }

    match args[0].as_str() {
        "--help" | "-h" => Ok(CliAction::Help(HelpTopic::Root)),
        "--version" | "-V" | "version" => Ok(CliAction::Version),
        "package" => parse_package_args(&args[1..]),
        command => Err(CliUsageError::new(UsageReason::UnknownCommand).with_command(command)),
    }
}

fn parse_package_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if args.is_empty() {
        return Ok(CliAction::Help(HelpTopic::Package));
    }
    match args[0].as_str() {
        "--help" | "-h" => Ok(CliAction::Help(HelpTopic::Package)),
        "check" => parse_package_check_args(&args[1..]),
        "build-certs" => parse_package_build_certs_args(&args[1..]),
        "axiom-report" => parse_package_axiom_report_args(&args[1..]),
        "index" => parse_package_index_args(&args[1..]),
        "theorem-premise-report" => parse_package_theorem_premise_report_args(&args[1..]),
        "export-summary" => parse_package_export_summary_args(&args[1..]),
        "export-candidate-metadata" => parse_package_export_candidate_metadata_args(&args[1..]),
        "validate-l2-acceptance" => parse_package_validate_l2_acceptance_args(&args[1..]),
        "prepare-l2-review-input" => parse_package_prepare_l2_review_input_args(&args[1..]),
        "aggregate-l2-acceptance" => parse_package_aggregate_l2_acceptance_args(&args[1..]),
        "validate-l2-namespace-transport" => {
            parse_package_validate_l2_namespace_transport_args(&args[1..])
        }
        "prepare-promotion" => parse_package_prepare_promotion_args(&args[1..]),
        "materialize-promotion" => parse_package_materialize_promotion_args(&args[1..]),
        "validate-promotion-materialization" => {
            parse_package_validate_promotion_materialization_args(&args[1..])
        }
        "validate-promotion-origin-registry" => {
            parse_package_validate_promotion_origin_registry_args(&args[1..])
        }
        "register-equivalent-promotion-origin" => {
            parse_package_register_equivalent_promotion_origin_args(&args[1..])
        }
        "verify-certs" => parse_package_verify_certs_args(&args[1..]),
        "check-hashes" => parse_package_check_hashes_args(&args[1..]),
        "audit-artifact-ledger" => parse_package_audit_artifact_ledger_args(&args[1..]),
        "lock" => parse_package_lock_args(&args[1..]),
        "publish-plan" => parse_package_publish_plan_args(&args[1..]),
        "check-generated" => parse_package_check_generated_args(&args[1..]),
        "high-trust" => parse_package_high_trust_args(&args[1..]),
        "gate-plan" => parse_package_gate_plan_args(&args[1..]),
        "refactor-plan" => parse_package_refactor_plan_args(&args[1..]),
        command if command.starts_with('-') => {
            Err(flag_error(command, UsageReason::UnknownFlag).with_command("package"))
        }
        command => Err(CliUsageError::new(UsageReason::UnknownCommand)
            .with_command(format!("package {command}"))),
    }
}

fn parse_package_lock_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if args.is_empty() {
        return Err(CliUsageError::new(UsageReason::UnknownCommand).with_command("package lock"));
    }
    match args[0].as_str() {
        "--help" | "-h" => Ok(CliAction::Help(HelpTopic::PackageLock)),
        "check" => parse_package_lock_check_args(&args[1..]),
        "write" => parse_package_lock_write_args(&args[1..]),
        command if command.starts_with('-') => {
            Err(flag_error(command, UsageReason::UnknownFlag).with_command("package lock"))
        }
        command => Err(CliUsageError::new(UsageReason::UnknownCommand)
            .with_command(format!("package lock {command}"))),
    }
}

fn parse_package_lock_check_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageLockCheck));
    }
    let common = parse_common_options(args, "package lock check", &[])?;
    Ok(CliAction::Run(CliCommand::Package(PackageCommand::Lock(
        PackageLockCommand::Check(common),
    ))))
}

fn parse_package_lock_write_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageLockWrite));
    }
    let common = parse_common_options(args, "package lock write", &[])?;
    Ok(CliAction::Run(CliCommand::Package(PackageCommand::Lock(
        PackageLockCommand::Write(common),
    ))))
}

fn parse_package_check_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageCheck));
    }
    let common = parse_common_options(args, "package check", &[])?;
    Ok(CliAction::Run(CliCommand::Package(PackageCommand::Check(
        common,
    ))))
}

fn parse_package_check_hashes_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageCheckHashes));
    }
    let common = parse_common_options(args, "package check-hashes", &[])?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::CheckHashes(common),
    )))
}

fn parse_package_audit_artifact_ledger_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package audit-artifact-ledger";
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageAuditArtifactLedger));
    }

    let mut common_tokens = Vec::new();
    let mut module_values = Vec::new();
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--module" => {
                module_values.push(flag_value(args, index, "--module", COMMAND)?.to_owned());
                index += 2;
            }
            token if token.starts_with("--module=") => {
                let value = token.trim_start_matches("--module=");
                if value.is_empty() {
                    return Err(
                        flag_error("--module", UsageReason::MissingFlagValue).with_command(COMMAND)
                    );
                }
                module_values.push(value.to_owned());
                index += 1;
            }
            _ => {
                common_tokens.push(args[index].clone());
                index += 1;
            }
        }
    }

    let common = parse_common_options(&common_tokens, COMMAND, &[])?;
    let mut seen = BTreeSet::new();
    let mut modules = Vec::new();
    for value in module_values {
        let module = Name::from_dotted(&value);
        if npa_package::validate_canonical_module_name(&module, "--module").is_err() {
            return Err(CliUsageError::new(UsageReason::InvalidModuleName)
                .with_command(COMMAND)
                .with_flag("--module")
                .with_value(value));
        }
        if seen.insert(module.clone()) {
            modules.push(module);
        }
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::AuditArtifactLedger(PackageArtifactLedgerAuditOptions { common, modules }),
    )))
}

fn parse_package_refactor_plan_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package refactor-plan";

    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageRefactorPlan));
    }

    let mut common_tokens = Vec::new();
    let mut scope = None::<String>;
    let mut module = None::<String>;
    let mut top = None::<String>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--scope" => {
                parse_string_flag(args, &mut index, "--scope", COMMAND, &mut scope)?;
            }
            token if token.starts_with("--scope=") => {
                parse_string_equals_flag(token, "--scope", COMMAND, &mut scope)?;
                index += 1;
            }
            "--module" => {
                parse_string_flag(args, &mut index, "--module", COMMAND, &mut module)?;
            }
            token if token.starts_with("--module=") => {
                parse_string_equals_flag(token, "--module", COMMAND, &mut module)?;
                index += 1;
            }
            "--top" => {
                parse_string_flag(args, &mut index, "--top", COMMAND, &mut top)?;
            }
            token if token.starts_with("--top=") => {
                parse_string_equals_flag(token, "--top", COMMAND, &mut top)?;
                index += 1;
            }
            "--include-source-metrics" => {
                return Err(
                    flag_error("--include-source-metrics", UsageReason::UnsupportedFlag)
                        .with_command(COMMAND),
                );
            }
            token if token.starts_with("--include-source-metrics=") => {
                return Err(
                    flag_error("--include-source-metrics", UsageReason::UnsupportedFlag)
                        .with_command(COMMAND),
                );
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        COMMAND,
        &["--scope", "--module", "--top", "--include-source-metrics"],
    )?;
    let scope = match scope {
        Some(value) => parse_refactor_plan_scope(&value)?,
        None => PackageRefactorPlanScope::Modules,
    };
    let module = match module {
        Some(value) => Some(parse_refactor_plan_module(&value)?),
        None => None,
    };
    let top = match top {
        Some(value) => parse_refactor_plan_top(&value)?,
        None => 20,
    };

    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::RefactorPlan(PackageRefactorPlanOptions {
            common,
            scope,
            module,
            top,
            include_source_metrics: false,
        }),
    )))
}

fn parse_package_gate_plan_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageGatePlan));
    }

    let mut common_tokens = Vec::new();
    let mut base = None::<String>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--base" => {
                parse_string_flag(args, &mut index, "--base", "package gate-plan", &mut base)?;
            }
            token if token.starts_with("--base=") => {
                parse_string_equals_flag(token, "--base", "package gate-plan", &mut base)?;
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(&common_tokens, "package gate-plan", &["--base"])?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::GatePlan(PackageGatePlanOptions {
            common,
            base: base.ok_or_else(|| {
                flag_error("--base", UsageReason::MissingRequiredFlag)
                    .with_command("package gate-plan")
            })?,
        }),
    )))
}

fn parse_package_build_certs_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageBuildCerts));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut build_check_cache = None::<PackageBuildCheckCacheMode>;
    let mut update_manifest_hashes = false;
    let mut module_values = Vec::new();
    let mut changed = false;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package build-certs"));
                }
                check = true;
                index += 1;
            }
            "--build-check-cache" => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                let value = flag_value(args, index, "--build-check-cache", "package build-certs")?;
                build_check_cache = Some(parse_build_check_cache_mode(value)?);
                index += 2;
            }
            "--build-check-cache=off" => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                build_check_cache = Some(PackageBuildCheckCacheMode::Off);
                index += 1;
            }
            "--build-check-cache=read-through" => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                build_check_cache = Some(PackageBuildCheckCacheMode::ReadThrough);
                index += 1;
            }
            token if token.starts_with("--build-check-cache=") => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                let value = token.trim_start_matches("--build-check-cache=");
                if value.is_empty() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::MissingFlagValue)
                            .with_command("package build-certs"),
                    );
                }
                build_check_cache = Some(parse_build_check_cache_mode(value)?);
                index += 1;
            }
            "--update-manifest-hashes" => {
                if update_manifest_hashes {
                    return Err(
                        flag_error("--update-manifest-hashes", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                update_manifest_hashes = true;
                index += 1;
            }
            "--module" => {
                module_values
                    .push(flag_value(args, index, "--module", "package build-certs")?.to_owned());
                index += 2;
            }
            token if token.starts_with("--module=") => {
                let value = token.trim_start_matches("--module=");
                if value.is_empty() {
                    return Err(flag_error("--module", UsageReason::MissingFlagValue)
                        .with_command("package build-certs"));
                }
                module_values.push(value.to_owned());
                index += 1;
            }
            "--changed" => {
                if changed {
                    return Err(flag_error("--changed", UsageReason::DuplicateFlag)
                        .with_command("package build-certs"));
                }
                changed = true;
                index += 1;
            }
            token if token.starts_with("--changed=") => {
                return Err(flag_error("--changed", UsageReason::UnsupportedFlag)
                    .with_command("package build-certs")
                    .with_value(token.trim_start_matches("--changed=")));
            }
            token if token.starts_with("--update-manifest-hashes=") => {
                let value = token.trim_start_matches("--update-manifest-hashes=");
                return Err(CliUsageError::new(UsageReason::UnsupportedFlag)
                    .with_command("package build-certs")
                    .with_flag("--update-manifest-hashes")
                    .with_value(value));
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package build-certs",
        &[
            "--check",
            "--build-check-cache",
            "--update-manifest-hashes",
            "--module",
            "--changed",
        ],
    )?;
    if changed && !module_values.is_empty() {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package build-certs")
            .with_flag("--module")
            .with_value("conflicts with --changed"));
    }
    let selection = if changed {
        PackageBuildSelection::Changed
    } else if module_values.is_empty() {
        PackageBuildSelection::Full
    } else {
        let mut seen = BTreeSet::new();
        let mut modules = Vec::with_capacity(module_values.len());
        for value in module_values {
            let module = Name::from_dotted(&value);
            if !module.is_canonical() {
                return Err(CliUsageError::new(UsageReason::InvalidModuleName)
                    .with_command("package build-certs")
                    .with_flag("--module")
                    .with_value(value));
            }
            if !seen.insert(module.clone()) {
                return Err(flag_error("--module", UsageReason::DuplicateFlag)
                    .with_command("package build-certs")
                    .with_value(module.as_dotted()));
            }
            modules.push(module);
        }
        PackageBuildSelection::Modules(modules)
    };
    let build_check_cache = build_check_cache.unwrap_or(PackageBuildCheckCacheMode::Off);
    let options = PackageBuildCertsOptions {
        common,
        check,
        build_check_cache,
        update_manifest_hashes,
        selection,
    };
    if let Err(error) = validate_package_build_certs_options(&options) {
        return Err(package_build_validation_cli_error(&options, error));
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::BuildCerts(options),
    )))
}

fn package_build_validation_cli_error(
    options: &PackageBuildCertsOptions,
    error: PackageBuildOptionsValidationError,
) -> CliUsageError {
    match error {
        PackageBuildOptionsValidationError::BuildCheckCacheWithRefresh
        | PackageBuildOptionsValidationError::BuildCheckCacheWithoutCheck => {
            CliUsageError::new(UsageReason::UnsupportedFlag)
                .with_command("package build-certs")
                .with_flag("--build-check-cache")
                .with_value(options.build_check_cache.as_str())
        }
        PackageBuildOptionsValidationError::TargetedBuildCheckCache => {
            CliUsageError::new(UsageReason::UnsupportedFlag)
                .with_command("package build-certs")
                .with_flag("--build-check-cache")
                .with_value(options.build_check_cache.as_str())
        }
        PackageBuildOptionsValidationError::TargetedWriteRequiresRefresh => {
            CliUsageError::new(UsageReason::UnsupportedFlag)
                .with_command("package build-certs")
                .with_flag("--module")
                .with_value("targeted_write_requires_refresh")
        }
        PackageBuildOptionsValidationError::EmptyModuleSelection
        | PackageBuildOptionsValidationError::DuplicateModuleSelection => {
            CliUsageError::new(UsageReason::InvalidFlagValue)
                .with_command("package build-certs")
                .with_flag("--module")
                .with_value("package_build_selection_invalid")
        }
    }
}

fn parse_package_axiom_report_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageAxiomReport));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package axiom-report"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package axiom-report"));
                }
                let value = flag_value(args, index, "--timings", "package axiom-report")?;
                timings = Some(parse_timing_mode(value, "package axiom-report")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package axiom-report"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package axiom-report"));
                }
                timings = Some(parse_timing_mode(value, "package axiom-report")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package axiom-report",
        &["--check", "--checker", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::AxiomReport(PackageAxiomReportOptions {
            common,
            check,
            timings,
        }),
    )))
}

fn parse_package_index_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageIndex));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package index"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package index"));
                }
                let value = flag_value(args, index, "--timings", "package index")?;
                timings = Some(parse_timing_mode(value, "package index")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package index"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package index"));
                }
                timings = Some(parse_timing_mode(value, "package index")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package index",
        &["--check", "--checker", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(PackageCommand::Index(
        PackageIndexOptions {
            common,
            check,
            timings,
        },
    ))))
}

fn parse_package_theorem_premise_report_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageTheoremPremiseReport));
    }

    let command = "package theorem-premise-report";
    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(
                        flag_error("--check", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(
                        flag_error("--timings", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                let value = flag_value(args, index, "--timings", command)?;
                timings = Some(parse_timing_mode(value, command)?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(
                        flag_error("--timings", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command(command));
                }
                timings = Some(parse_timing_mode(value, command)?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        command,
        &["--check", "--checker", "--timings"],
    )?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::TheoremPremiseReport(PackageTheoremPremiseReportOptions {
            common,
            check,
            timings: timings.unwrap_or(PackageTimingMode::Off),
        }),
    )))
}

fn parse_package_export_summary_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageExportSummary));
    }

    let mut common_tokens = Vec::new();
    let mut out = None::<PathBuf>;
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--out" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--out",
                    "package export-summary",
                    &mut out,
                )?;
            }
            token if token.starts_with("--out=") => {
                parse_path_equals_flag(token, "--out", "package export-summary", &mut out)?;
                index += 1;
            }
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package export-summary"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package export-summary"));
                }
                let value = flag_value(args, index, "--timings", "package export-summary")?;
                timings = Some(parse_timing_mode(value, "package export-summary")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package export-summary"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package export-summary"));
                }
                timings = Some(parse_timing_mode(value, "package export-summary")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package export-summary",
        &["--check", "--out", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ExportSummary(PackageExportSummaryOptions {
            common,
            out,
            check,
            timings,
        }),
    )))
}

fn parse_package_export_candidate_metadata_args(
    args: &[String],
) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageExportCandidateMetadata));
    }

    let mut common_tokens = Vec::new();
    let mut module = None::<String>;
    let mut declaration = None::<String>;
    let mut out = None::<PathBuf>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--module" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--module",
                    "package export-candidate-metadata",
                    &mut module,
                )?;
            }
            token if token.starts_with("--module=") => {
                parse_string_equals_flag(
                    token,
                    "--module",
                    "package export-candidate-metadata",
                    &mut module,
                )?;
                index += 1;
            }
            "--declaration" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--declaration",
                    "package export-candidate-metadata",
                    &mut declaration,
                )?;
            }
            token if token.starts_with("--declaration=") => {
                parse_string_equals_flag(
                    token,
                    "--declaration",
                    "package export-candidate-metadata",
                    &mut declaration,
                )?;
                index += 1;
            }
            "--out" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--out",
                    "package export-candidate-metadata",
                    &mut out,
                )?;
            }
            token if token.starts_with("--out=") => {
                parse_path_equals_flag(
                    token,
                    "--out",
                    "package export-candidate-metadata",
                    &mut out,
                )?;
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package export-candidate-metadata",
        &["--module", "--declaration", "--out"],
    )?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ExportCandidateMetadata(PackageCandidateMetadataOptions {
            common,
            module: module.ok_or_else(|| {
                flag_error("--module", UsageReason::MissingRequiredFlag)
                    .with_command("package export-candidate-metadata")
            })?,
            declaration: declaration.ok_or_else(|| {
                flag_error("--declaration", UsageReason::MissingRequiredFlag)
                    .with_command("package export-candidate-metadata")
            })?,
            out: out.ok_or_else(|| {
                flag_error("--out", UsageReason::MissingRequiredFlag)
                    .with_command("package export-candidate-metadata")
            })?,
        }),
    )))
}

fn parse_package_validate_l2_acceptance_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package validate-l2-acceptance";
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageValidateL2Acceptance));
    }

    let mut common_tokens = Vec::new();
    let mut policy = None::<PathBuf>;
    let mut acceptance = None::<PathBuf>;
    let mut module_values = Vec::new();
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--policy" => parse_path_flag(args, &mut index, "--policy", COMMAND, &mut policy)?,
            token if token.starts_with("--policy=") => {
                parse_path_equals_flag(token, "--policy", COMMAND, &mut policy)?;
                index += 1;
            }
            "--acceptance" => {
                parse_path_flag(args, &mut index, "--acceptance", COMMAND, &mut acceptance)?;
            }
            token if token.starts_with("--acceptance=") => {
                parse_path_equals_flag(token, "--acceptance", COMMAND, &mut acceptance)?;
                index += 1;
            }
            "--module" => {
                module_values.push(flag_value(args, index, "--module", COMMAND)?.to_owned());
                index += 2;
            }
            token if token.starts_with("--module=") => {
                let value = token.trim_start_matches("--module=");
                if value.is_empty() {
                    return Err(
                        flag_error("--module", UsageReason::MissingFlagValue).with_command(COMMAND)
                    );
                }
                module_values.push(value.to_owned());
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        COMMAND,
        &["--policy", "--acceptance", "--module"],
    )?;
    let mut seen = BTreeSet::new();
    let mut modules = Vec::new();
    for value in module_values {
        let module = Name::from_dotted(&value);
        if npa_package::validate_canonical_module_name(&module, "--module").is_err() {
            return Err(CliUsageError::new(UsageReason::InvalidModuleName)
                .with_command(COMMAND)
                .with_flag("--module")
                .with_value(value));
        }
        if seen.insert(module.clone()) {
            modules.push(module);
        }
    }

    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ValidateL2Acceptance(PackageL2AcceptanceOptions {
            common,
            policy: policy.ok_or_else(|| {
                flag_error("--policy", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            })?,
            acceptance: acceptance.ok_or_else(|| {
                flag_error("--acceptance", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            })?,
            modules,
        }),
    )))
}

fn parse_package_prepare_l2_review_input_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package prepare-l2-review-input";
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackagePrepareL2ReviewInput));
    }
    let mut common_tokens = Vec::new();
    let mut policy = None;
    let mut module = None;
    let mut declaration = None;
    let mut out = None;
    let mut check = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        match token {
            "--policy" => parse_path_flag(args, &mut index, "--policy", COMMAND, &mut policy)?,
            "--module" => parse_string_flag(args, &mut index, "--module", COMMAND, &mut module)?,
            "--declaration" => {
                parse_string_flag(args, &mut index, "--declaration", COMMAND, &mut declaration)?
            }
            "--out" => parse_path_flag(args, &mut index, "--out", COMMAND, &mut out)?,
            "--check" if !check => {
                check = true;
                index += 1;
            }
            "--check" => {
                return Err(flag_error("--check", UsageReason::DuplicateFlag).with_command(COMMAND))
            }
            _ if token.starts_with("--policy=") => {
                parse_path_equals_flag(token, "--policy", COMMAND, &mut policy)?;
                index += 1;
            }
            _ if token.starts_with("--module=") => {
                parse_string_equals_flag(token, "--module", COMMAND, &mut module)?;
                index += 1;
            }
            _ if token.starts_with("--declaration=") => {
                parse_string_equals_flag(token, "--declaration", COMMAND, &mut declaration)?;
                index += 1;
            }
            _ if token.starts_with("--out=") => {
                parse_path_equals_flag(token, "--out", COMMAND, &mut out)?;
                index += 1;
            }
            _ => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }
    let common = parse_common_options(&common_tokens, COMMAND, &[])?;
    let module = module.ok_or_else(|| {
        flag_error("--module", UsageReason::MissingRequiredFlag).with_command(COMMAND)
    })?;
    let declaration = declaration.ok_or_else(|| {
        flag_error("--declaration", UsageReason::MissingRequiredFlag).with_command(COMMAND)
    })?;
    for (flag, value) in [("--module", &module), ("--declaration", &declaration)] {
        let name = Name::from_dotted(value);
        if npa_package::validate_canonical_module_name(&name, flag).is_err() {
            return Err(CliUsageError::new(UsageReason::InvalidModuleName)
                .with_command(COMMAND)
                .with_flag(flag)
                .with_value(value));
        }
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::PrepareL2ReviewInput(PackageL2ReviewInputOptions {
            common,
            policy: policy.ok_or_else(|| {
                flag_error("--policy", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            })?,
            module,
            declaration,
            out: out.ok_or_else(|| {
                flag_error("--out", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            })?,
            check,
        }),
    )))
}

fn parse_package_aggregate_l2_acceptance_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package aggregate-l2-acceptance";
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageAggregateL2Acceptance));
    }
    let mut common_tokens = Vec::new();
    let mut policy = None;
    let mut inputs = Vec::new();
    let mut reviews = Vec::new();
    let mut existing = None;
    let mut replacements = Vec::new();
    let mut out = None;
    let mut check = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        match token {
            "--policy" => parse_path_flag(args, &mut index, "--policy", COMMAND, &mut policy)?,
            "--review-input" => {
                inputs.push(PathBuf::from(flag_value(
                    args,
                    index,
                    "--review-input",
                    COMMAND,
                )?));
                index += 2;
            }
            "--review" => {
                reviews.push(PathBuf::from(flag_value(args, index, "--review", COMMAND)?));
                index += 2;
            }
            "--existing" => {
                parse_path_flag(args, &mut index, "--existing", COMMAND, &mut existing)?
            }
            "--replace" => {
                replacements.push(parse_l2_replace_selector(
                    flag_value(args, index, "--replace", COMMAND)?,
                    COMMAND,
                )?);
                index += 2;
            }
            "--out" => parse_path_flag(args, &mut index, "--out", COMMAND, &mut out)?,
            "--check" if !check => {
                check = true;
                index += 1;
            }
            "--check" => {
                return Err(flag_error("--check", UsageReason::DuplicateFlag).with_command(COMMAND))
            }
            _ if token.starts_with("--policy=") => {
                parse_path_equals_flag(token, "--policy", COMMAND, &mut policy)?;
                index += 1;
            }
            _ if token.starts_with("--review-input=") => {
                inputs.push(PathBuf::from(flag_equals_value(
                    token,
                    "--review-input",
                    COMMAND,
                )?));
                index += 1;
            }
            _ if token.starts_with("--review=") => {
                reviews.push(PathBuf::from(flag_equals_value(
                    token, "--review", COMMAND,
                )?));
                index += 1;
            }
            _ if token.starts_with("--existing=") => {
                parse_path_equals_flag(token, "--existing", COMMAND, &mut existing)?;
                index += 1;
            }
            _ if token.starts_with("--replace=") => {
                replacements.push(parse_l2_replace_selector(
                    flag_equals_value(token, "--replace", COMMAND)?,
                    COMMAND,
                )?);
                index += 1;
            }
            _ if token.starts_with("--out=") => {
                parse_path_equals_flag(token, "--out", COMMAND, &mut out)?;
                index += 1;
            }
            _ => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }
    if inputs.is_empty() {
        return Err(
            flag_error("--review-input", UsageReason::MissingRequiredFlag).with_command(COMMAND),
        );
    }
    if reviews.is_empty() {
        return Err(flag_error("--review", UsageReason::MissingRequiredFlag).with_command(COMMAND));
    }
    let mut seen = BTreeSet::new();
    if inputs
        .iter()
        .chain(reviews.iter())
        .any(|path| !seen.insert(path.clone()))
    {
        return Err(CliUsageError::new(UsageReason::DuplicateFlag).with_command(COMMAND));
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::AggregateL2Acceptance(Box::new(PackageL2AcceptanceAggregateOptions {
            common: parse_common_options(&common_tokens, COMMAND, &[])?,
            policy: policy.ok_or_else(|| {
                flag_error("--policy", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            })?,
            review_inputs: inputs,
            reviews,
            existing,
            replacements,
            out: out.ok_or_else(|| {
                flag_error("--out", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            })?,
            check,
        })),
    )))
}

fn parse_l2_replace_selector(value: &str, command: &str) -> Result<(Name, Name), CliUsageError> {
    let Some((module, declaration)) = value.split_once("::") else {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command(command)
            .with_flag("--replace")
            .with_value(value));
    };
    if module.is_empty() || declaration.is_empty() || declaration.contains("::") {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command(command)
            .with_flag("--replace")
            .with_value(value));
    }
    let pair = (Name::from_dotted(module), Name::from_dotted(declaration));
    if npa_package::validate_canonical_module_name(&pair.0, "--replace").is_err()
        || npa_package::validate_canonical_module_name(&pair.1, "--replace").is_err()
    {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command(command)
            .with_flag("--replace")
            .with_value(value));
    }
    Ok(pair)
}

fn parse_package_validate_l2_namespace_transport_args(
    args: &[String],
) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package validate-l2-namespace-transport";
    if contains_help(args) {
        return Ok(CliAction::Help(
            HelpTopic::PackageValidateL2NamespaceTransport,
        ));
    }
    let mut source_root = None;
    let mut baseline = None;
    let mut target = None;
    let mut acceptance_policy = None;
    let mut source_acceptance = None;
    let mut transport_policy = None;
    let mut mapping = None;
    let mut out = None;
    let mut check = false;
    let mut json = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        let (flag, slot) = match token {
            "--source-root" => ("--source-root", &mut source_root),
            "--target-baseline-root" => ("--target-baseline-root", &mut baseline),
            "--target-root" => ("--target-root", &mut target),
            "--acceptance-policy" => ("--acceptance-policy", &mut acceptance_policy),
            "--source-acceptance" => ("--source-acceptance", &mut source_acceptance),
            "--transport-policy" => ("--transport-policy", &mut transport_policy),
            "--mapping" => ("--mapping", &mut mapping),
            "--out" => ("--out", &mut out),
            "--check" if !check => {
                check = true;
                index += 1;
                continue;
            }
            "--json" if !json => {
                json = true;
                index += 1;
                continue;
            }
            "--check" | "--json" => {
                return Err(flag_error(token, UsageReason::DuplicateFlag).with_command(COMMAND))
            }
            _ => {
                let mut handled = false;
                for (flag, slot) in [
                    ("--source-root", &mut source_root),
                    ("--target-baseline-root", &mut baseline),
                    ("--target-root", &mut target),
                    ("--acceptance-policy", &mut acceptance_policy),
                    ("--source-acceptance", &mut source_acceptance),
                    ("--transport-policy", &mut transport_policy),
                    ("--mapping", &mut mapping),
                    ("--out", &mut out),
                ] {
                    if token.starts_with(&format!("{flag}=")) {
                        parse_path_equals_flag(token, flag, COMMAND, slot)?;
                        handled = true;
                        break;
                    }
                }
                if handled {
                    index += 1;
                    continue;
                }
                return Err(flag_error(token, UsageReason::UnknownFlag).with_command(COMMAND));
            }
        };
        parse_path_flag(args, &mut index, flag, COMMAND, slot)?;
    }
    if check && out.is_none() {
        return Err(flag_error("--out", UsageReason::MissingRequiredFlag).with_command(COMMAND));
    }
    let required = |value: Option<PathBuf>, flag: &'static str| {
        value
            .ok_or_else(|| flag_error(flag, UsageReason::MissingRequiredFlag).with_command(COMMAND))
    };
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ValidateL2NamespaceTransport(Box::new(
            PackageL2NamespaceTransportOptions {
                common: PackageCommonOptions {
                    root: required(source_root, "--source-root")?,
                    json,
                },
                target_baseline_root: required(baseline, "--target-baseline-root")?,
                target_root: required(target, "--target-root")?,
                acceptance_policy: required(acceptance_policy, "--acceptance-policy")?,
                source_acceptance: required(source_acceptance, "--source-acceptance")?,
                transport_policy: required(transport_policy, "--transport-policy")?,
                mapping: required(mapping, "--mapping")?,
                out,
                check,
            },
        )),
    )))
}

fn parse_package_prepare_promotion_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package prepare-promotion";
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackagePreparePromotion));
    }
    let root_explicit = args
        .iter()
        .any(|token| token == "--root" || token.starts_with("--root="));
    let mut common_tokens = Vec::new();
    let mut baseline = None;
    let mut acceptance_policy = None;
    let mut source_acceptance = None;
    let mut transport_policy = None;
    let mut mapping = None;
    let mut declaration_request = None;
    let mut equivalent_origin_roots = Vec::new();
    let mut out = None;
    let mut check = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        let slot = match token {
            "--target-baseline-root" => Some(("--target-baseline-root", &mut baseline)),
            "--acceptance-policy" => Some(("--acceptance-policy", &mut acceptance_policy)),
            "--source-acceptance" => Some(("--source-acceptance", &mut source_acceptance)),
            "--transport-policy" => Some(("--transport-policy", &mut transport_policy)),
            "--mapping" => Some(("--mapping", &mut mapping)),
            "--declaration-request" => Some(("--declaration-request", &mut declaration_request)),
            "--out" => Some(("--out", &mut out)),
            "--equivalent-origin-root" => {
                equivalent_origin_roots.push(PathBuf::from(flag_value(
                    args,
                    index,
                    "--equivalent-origin-root",
                    COMMAND,
                )?));
                index += 2;
                continue;
            }
            "--check" if !check => {
                check = true;
                index += 1;
                continue;
            }
            "--check" => {
                return Err(flag_error("--check", UsageReason::DuplicateFlag).with_command(COMMAND));
            }
            _ => None,
        };
        if let Some((flag, slot)) = slot {
            parse_path_flag(args, &mut index, flag, COMMAND, slot)?;
            continue;
        }
        if token.starts_with("--equivalent-origin-root=") {
            equivalent_origin_roots.push(PathBuf::from(flag_equals_value(
                token,
                "--equivalent-origin-root",
                COMMAND,
            )?));
            index += 1;
            continue;
        }
        let mut handled = false;
        for (flag, slot) in [
            ("--target-baseline-root", &mut baseline),
            ("--acceptance-policy", &mut acceptance_policy),
            ("--source-acceptance", &mut source_acceptance),
            ("--transport-policy", &mut transport_policy),
            ("--mapping", &mut mapping),
            ("--declaration-request", &mut declaration_request),
            ("--out", &mut out),
        ] {
            if token.starts_with(&format!("{flag}=")) {
                parse_path_equals_flag(token, flag, COMMAND, slot)?;
                handled = true;
                break;
            }
        }
        if handled {
            index += 1;
        } else {
            common_tokens.push(token.to_owned());
            index += 1;
        }
    }
    let required = |value: Option<PathBuf>, flag: &'static str| {
        value
            .ok_or_else(|| flag_error(flag, UsageReason::MissingRequiredFlag).with_command(COMMAND))
    };
    if !root_explicit {
        return Err(flag_error("--root", UsageReason::MissingRequiredFlag).with_command(COMMAND));
    }
    let l2_count = [
        acceptance_policy.is_some(),
        source_acceptance.is_some(),
        transport_policy.is_some(),
        mapping.is_some(),
    ]
    .into_iter()
    .filter(|present| *present)
    .count();
    if declaration_request.is_some() {
        if l2_count != 0 {
            return Err(
                flag_error("--declaration-request", UsageReason::InvalidFlagValue)
                    .with_command(COMMAND),
            );
        }
    } else if l2_count != 4 {
        let flag = if acceptance_policy.is_none() {
            "--acceptance-policy"
        } else if source_acceptance.is_none() {
            "--source-acceptance"
        } else if transport_policy.is_none() {
            "--transport-policy"
        } else {
            "--mapping"
        };
        return Err(flag_error(flag, UsageReason::MissingRequiredFlag).with_command(COMMAND));
    }
    let mut seen_origins = BTreeSet::new();
    if equivalent_origin_roots
        .iter()
        .any(|path| !seen_origins.insert(path.clone()))
    {
        return Err(
            flag_error("--equivalent-origin-root", UsageReason::DuplicateFlag)
                .with_command(COMMAND),
        );
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::PreparePromotion(Box::new(PackagePreparePromotionOptions {
            common: parse_common_options(&common_tokens, COMMAND, &[])?,
            target_baseline_root: required(baseline, "--target-baseline-root")?,
            acceptance_policy,
            source_acceptance,
            transport_policy,
            mapping,
            declaration_request,
            equivalent_origin_roots,
            out: required(out, "--out")?,
            check,
        })),
    )))
}

fn parse_package_materialize_promotion_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package materialize-promotion";
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageMaterializePromotion));
    }
    let root_explicit = args
        .iter()
        .any(|token| token == "--root" || token.starts_with("--root="));
    let mut common_tokens = Vec::new();
    let mut baseline = None;
    let mut target = None;
    let mut plan = None;
    let mut equivalent_origin_roots = Vec::new();
    let mut attestation = None;
    let mut verification_attestation = None;
    let mut phase = None;
    let mut recover = None;
    let mut apply = false;
    let mut dry_run = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        let slot = match token {
            "--target-baseline-root" => Some(("--target-baseline-root", &mut baseline)),
            "--target-root" => Some(("--target-root", &mut target)),
            "--plan" => Some(("--plan", &mut plan)),
            "--transport-attestation" => Some(("--transport-attestation", &mut attestation)),
            "--verification-attestation" => {
                Some(("--verification-attestation", &mut verification_attestation))
            }
            "--recover" => Some(("--recover", &mut recover)),
            "--equivalent-origin-root" => {
                equivalent_origin_roots.push(PathBuf::from(flag_value(
                    args,
                    index,
                    "--equivalent-origin-root",
                    COMMAND,
                )?));
                index += 2;
                continue;
            }
            "--phase" => {
                let value = flag_value(args, index, "--phase", COMMAND)?;
                if phase.is_some() {
                    return Err(
                        flag_error("--phase", UsageReason::DuplicateFlag).with_command(COMMAND)
                    );
                }
                phase = Some(parse_promotion_phase(value, COMMAND)?);
                index += 2;
                continue;
            }
            "--apply" if !apply => {
                apply = true;
                index += 1;
                continue;
            }
            "--dry-run" if !dry_run => {
                dry_run = true;
                index += 1;
                continue;
            }
            "--apply" | "--dry-run" => {
                return Err(flag_error(token, UsageReason::DuplicateFlag).with_command(COMMAND));
            }
            _ => None,
        };
        if let Some((flag, slot)) = slot {
            parse_path_flag(args, &mut index, flag, COMMAND, slot)?;
            continue;
        }
        if token.starts_with("--phase=") {
            if phase.is_some() {
                return Err(flag_error("--phase", UsageReason::DuplicateFlag).with_command(COMMAND));
            }
            phase = Some(parse_promotion_phase(
                flag_equals_value(token, "--phase", COMMAND)?,
                COMMAND,
            )?);
            index += 1;
            continue;
        }
        if token.starts_with("--equivalent-origin-root=") {
            equivalent_origin_roots.push(PathBuf::from(flag_equals_value(
                token,
                "--equivalent-origin-root",
                COMMAND,
            )?));
            index += 1;
            continue;
        }
        let mut handled = false;
        for (flag, slot) in [
            ("--target-baseline-root", &mut baseline),
            ("--target-root", &mut target),
            ("--plan", &mut plan),
            ("--transport-attestation", &mut attestation),
            ("--verification-attestation", &mut verification_attestation),
            ("--recover", &mut recover),
        ] {
            if token.starts_with(&format!("{flag}=")) {
                parse_path_equals_flag(token, flag, COMMAND, slot)?;
                handled = true;
                break;
            }
        }
        if handled {
            index += 1;
        } else {
            common_tokens.push(token.to_owned());
            index += 1;
        }
    }
    if apply && dry_run {
        return Err(flag_error("--apply", UsageReason::InvalidFlagValue).with_command(COMMAND));
    }
    let target_root = target.ok_or_else(|| {
        flag_error("--target-root", UsageReason::MissingRequiredFlag).with_command(COMMAND)
    })?;
    if recover.is_some() {
        if root_explicit
            || baseline.is_some()
            || plan.is_some()
            || !equivalent_origin_roots.is_empty()
            || attestation.is_some()
            || verification_attestation.is_some()
            || phase.is_some()
            || apply
            || dry_run
            || common_tokens.iter().any(|token| token != "--json")
        {
            return Err(
                flag_error("--recover", UsageReason::InvalidFlagValue).with_command(COMMAND)
            );
        }
    } else {
        if !root_explicit {
            return Err(
                flag_error("--root", UsageReason::MissingRequiredFlag).with_command(COMMAND)
            );
        }
        if baseline.is_none() || plan.is_none() || phase.is_none() {
            let flag = if baseline.is_none() {
                "--target-baseline-root"
            } else if plan.is_none() {
                "--plan"
            } else {
                "--phase"
            };
            return Err(flag_error(flag, UsageReason::MissingRequiredFlag).with_command(COMMAND));
        }
        let attestation_count =
            usize::from(attestation.is_some()) + usize::from(verification_attestation.is_some());
        match (phase, attestation_count) {
            (Some(PackagePromotionPhase::Tracked), 0) => {
                return Err(flag_error(
                    "--transport-attestation",
                    UsageReason::MissingRequiredFlag,
                )
                .with_command(COMMAND));
            }
            (Some(PackagePromotionPhase::Tracked), 2) => {
                return Err(flag_error(
                    "--verification-attestation",
                    UsageReason::InvalidFlagValue,
                )
                .with_command(COMMAND));
            }
            (Some(PackagePromotionPhase::Temporary), 1 | 2) => {
                return Err(flag_error(
                    "--verification-attestation",
                    UsageReason::InvalidFlagValue,
                )
                .with_command(COMMAND));
            }
            _ => {}
        }
        let mut seen_origins = BTreeSet::new();
        if equivalent_origin_roots
            .iter()
            .any(|path| !seen_origins.insert(path.clone()))
        {
            return Err(
                flag_error("--equivalent-origin-root", UsageReason::DuplicateFlag)
                    .with_command(COMMAND),
            );
        }
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::MaterializePromotion(Box::new(PackageMaterializePromotionOptions {
            common: parse_common_options(&common_tokens, COMMAND, &[])?,
            target_baseline_root: baseline,
            target_root,
            plan,
            equivalent_origin_roots,
            transport_attestation: attestation,
            verification_attestation,
            phase,
            apply,
            recover,
        })),
    )))
}

fn parse_promotion_phase(
    value: &str,
    command: &str,
) -> Result<PackagePromotionPhase, CliUsageError> {
    match value {
        "temporary" => Ok(PackagePromotionPhase::Temporary),
        "tracked" => Ok(PackagePromotionPhase::Tracked),
        _ => Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command(command)
            .with_flag("--phase")
            .with_value(value)),
    }
}

fn parse_package_validate_promotion_materialization_args(
    args: &[String],
) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package validate-promotion-materialization";
    if contains_help(args) {
        return Ok(CliAction::Help(
            HelpTopic::PackageValidatePromotionMaterialization,
        ));
    }
    let root_explicit = args
        .iter()
        .any(|token| token == "--root" || token.starts_with("--root="));
    let mut common_tokens = Vec::new();
    let mut baseline = None;
    let mut target = None;
    let mut plan = None;
    let mut out = None;
    let mut check = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        let slot = match token {
            "--target-baseline-root" => Some(("--target-baseline-root", &mut baseline)),
            "--target-root" => Some(("--target-root", &mut target)),
            "--plan" => Some(("--plan", &mut plan)),
            "--out" => Some(("--out", &mut out)),
            "--check" if !check => {
                check = true;
                index += 1;
                continue;
            }
            "--check" => {
                return Err(flag_error("--check", UsageReason::DuplicateFlag).with_command(COMMAND));
            }
            _ => None,
        };
        if let Some((flag, slot)) = slot {
            parse_path_flag(args, &mut index, flag, COMMAND, slot)?;
            continue;
        }
        let mut handled = false;
        for (flag, slot) in [
            ("--target-baseline-root", &mut baseline),
            ("--target-root", &mut target),
            ("--plan", &mut plan),
            ("--out", &mut out),
        ] {
            if token.starts_with(&format!("{flag}=")) {
                parse_path_equals_flag(token, flag, COMMAND, slot)?;
                handled = true;
                break;
            }
        }
        if handled {
            index += 1;
        } else {
            common_tokens.push(token.to_owned());
            index += 1;
        }
    }
    if !root_explicit {
        return Err(flag_error("--root", UsageReason::MissingRequiredFlag).with_command(COMMAND));
    }
    let required = |value: Option<PathBuf>, flag: &'static str| {
        value
            .ok_or_else(|| flag_error(flag, UsageReason::MissingRequiredFlag).with_command(COMMAND))
    };
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ValidatePromotionMaterialization(Box::new(
            PackageValidatePromotionMaterializationOptions {
                common: parse_common_options(&common_tokens, COMMAND, &[])?,
                target_baseline_root: required(baseline, "--target-baseline-root")?,
                target_root: required(target, "--target-root")?,
                plan: required(plan, "--plan")?,
                out: required(out, "--out")?,
                check,
            },
        )),
    )))
}

fn parse_package_validate_promotion_origin_registry_args(
    args: &[String],
) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package validate-promotion-origin-registry";
    if contains_help(args) {
        return Ok(CliAction::Help(
            HelpTopic::PackageValidatePromotionOriginRegistry,
        ));
    }
    let mut common_tokens = Vec::new();
    let mut source_roots = Vec::new();
    let mut previous_registry = None;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        match token {
            "--source-root" => {
                source_roots.push(PathBuf::from(flag_value(
                    args,
                    index,
                    "--source-root",
                    COMMAND,
                )?));
                index += 2;
            }
            "--previous-registry" => parse_path_flag(
                args,
                &mut index,
                "--previous-registry",
                COMMAND,
                &mut previous_registry,
            )?,
            _ if token.starts_with("--source-root=") => {
                source_roots.push(PathBuf::from(flag_equals_value(
                    token,
                    "--source-root",
                    COMMAND,
                )?));
                index += 1;
            }
            _ if token.starts_with("--previous-registry=") => {
                parse_path_equals_flag(
                    token,
                    "--previous-registry",
                    COMMAND,
                    &mut previous_registry,
                )?;
                index += 1;
            }
            _ => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ValidatePromotionOriginRegistry(
            PackageValidatePromotionOriginRegistryOptions {
                common: parse_common_options(&common_tokens, COMMAND, &[])?,
                source_roots,
                previous_registry,
            },
        ),
    )))
}

fn parse_package_register_equivalent_promotion_origin_args(
    args: &[String],
) -> Result<CliAction, CliUsageError> {
    const COMMAND: &str = "package register-equivalent-promotion-origin";
    if contains_help(args) {
        return Ok(CliAction::Help(
            HelpTopic::PackageRegisterEquivalentPromotionOrigin,
        ));
    }
    let root_explicit = args
        .iter()
        .any(|token| token == "--root" || token.starts_with("--root="));
    let mut common_tokens = Vec::new();
    let mut target_root = None;
    let mut promotion_id = None;
    let mut apply = false;
    let mut dry_run = false;
    let mut index = 0;
    while index < args.len() {
        let token = args[index].as_str();
        match token {
            "--target-root" => {
                parse_path_flag(args, &mut index, "--target-root", COMMAND, &mut target_root)?
            }
            "--promotion-id" => parse_string_flag(
                args,
                &mut index,
                "--promotion-id",
                COMMAND,
                &mut promotion_id,
            )?,
            "--apply" if !apply => {
                apply = true;
                index += 1;
            }
            "--dry-run" if !dry_run => {
                dry_run = true;
                index += 1;
            }
            "--apply" | "--dry-run" => {
                return Err(flag_error(token, UsageReason::DuplicateFlag).with_command(COMMAND));
            }
            _ if token.starts_with("--target-root=") => {
                parse_path_equals_flag(token, "--target-root", COMMAND, &mut target_root)?;
                index += 1;
            }
            _ if token.starts_with("--promotion-id=") => {
                parse_string_equals_flag(token, "--promotion-id", COMMAND, &mut promotion_id)?;
                index += 1;
            }
            _ => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }
    if apply && dry_run {
        return Err(flag_error("--apply", UsageReason::InvalidFlagValue).with_command(COMMAND));
    }
    if !root_explicit {
        return Err(flag_error("--root", UsageReason::MissingRequiredFlag).with_command(COMMAND));
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::RegisterEquivalentPromotionOrigin(
            PackageRegisterEquivalentPromotionOriginOptions {
                common: parse_common_options(&common_tokens, COMMAND, &[])?,
                target_root: target_root.ok_or_else(|| {
                    flag_error("--target-root", UsageReason::MissingRequiredFlag)
                        .with_command(COMMAND)
                })?,
                promotion_id: promotion_id.ok_or_else(|| {
                    flag_error("--promotion-id", UsageReason::MissingRequiredFlag)
                        .with_command(COMMAND)
                })?,
                apply,
            },
        ),
    )))
}

fn parse_package_publish_plan_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackagePublishPlan));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package publish-plan"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package publish-plan"));
                }
                let value = flag_value(args, index, "--timings", "package publish-plan")?;
                timings = Some(parse_timing_mode(value, "package publish-plan")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package publish-plan"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package publish-plan"));
                }
                timings = Some(parse_timing_mode(value, "package publish-plan")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package publish-plan",
        &["--check", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::PublishPlan(PackagePublishPlanOptions {
            common,
            check,
            timings,
        }),
    )))
}

fn parse_package_check_generated_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageCheckGenerated));
    }

    let mut common_tokens = Vec::new();
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package check-generated"));
                }
                let value = flag_value(args, index, "--timings", "package check-generated")?;
                timings = Some(parse_timing_mode(value, "package check-generated")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package check-generated"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package check-generated"));
                }
                timings = Some(parse_timing_mode(value, "package check-generated")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(&common_tokens, "package check-generated", &["--timings"])?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::CheckGenerated(PackageCheckGeneratedOptions { common, timings }),
    )))
}

fn parse_package_high_trust_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageHighTrust));
    }

    let mut common_tokens = Vec::new();
    let mut release_policy = None::<PathBuf>;
    let mut release_policy_hash = None::<String>;
    let mut runner_policy = None::<PathBuf>;
    let mut runner_policy_hash = None::<String>;
    let mut challenge_runner_policy = None::<PathBuf>;
    let mut challenge_runner_policy_hash = None::<String>;
    let mut checker_registry = None::<PathBuf>;
    let mut out = None::<PathBuf>;
    let mut check = false;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--release-policy" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--release-policy",
                    "package high-trust",
                    &mut release_policy,
                )?;
            }
            token if token.starts_with("--release-policy=") => {
                parse_path_equals_flag(
                    token,
                    "--release-policy",
                    "package high-trust",
                    &mut release_policy,
                )?;
                index += 1;
            }
            "--release-policy-hash" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--release-policy-hash",
                    "package high-trust",
                    &mut release_policy_hash,
                )?;
            }
            token if token.starts_with("--release-policy-hash=") => {
                parse_string_equals_flag(
                    token,
                    "--release-policy-hash",
                    "package high-trust",
                    &mut release_policy_hash,
                )?;
                index += 1;
            }
            "--runner-policy" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--runner-policy",
                    "package high-trust",
                    &mut runner_policy,
                )?;
            }
            token if token.starts_with("--runner-policy=") => {
                parse_path_equals_flag(
                    token,
                    "--runner-policy",
                    "package high-trust",
                    &mut runner_policy,
                )?;
                index += 1;
            }
            "--runner-policy-hash" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--runner-policy-hash",
                    "package high-trust",
                    &mut runner_policy_hash,
                )?;
            }
            token if token.starts_with("--runner-policy-hash=") => {
                parse_string_equals_flag(
                    token,
                    "--runner-policy-hash",
                    "package high-trust",
                    &mut runner_policy_hash,
                )?;
                index += 1;
            }
            "--challenge-runner-policy" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--challenge-runner-policy",
                    "package high-trust",
                    &mut challenge_runner_policy,
                )?;
            }
            token if token.starts_with("--challenge-runner-policy=") => {
                parse_path_equals_flag(
                    token,
                    "--challenge-runner-policy",
                    "package high-trust",
                    &mut challenge_runner_policy,
                )?;
                index += 1;
            }
            "--challenge-runner-policy-hash" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--challenge-runner-policy-hash",
                    "package high-trust",
                    &mut challenge_runner_policy_hash,
                )?;
            }
            token if token.starts_with("--challenge-runner-policy-hash=") => {
                parse_string_equals_flag(
                    token,
                    "--challenge-runner-policy-hash",
                    "package high-trust",
                    &mut challenge_runner_policy_hash,
                )?;
                index += 1;
            }
            "--checker-registry" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--checker-registry",
                    "package high-trust",
                    &mut checker_registry,
                )?;
            }
            token if token.starts_with("--checker-registry=") => {
                parse_path_equals_flag(
                    token,
                    "--checker-registry",
                    "package high-trust",
                    &mut checker_registry,
                )?;
                index += 1;
            }
            "--out" => {
                parse_path_flag(args, &mut index, "--out", "package high-trust", &mut out)?;
            }
            token if token.starts_with("--out=") => {
                parse_path_equals_flag(token, "--out", "package high-trust", &mut out)?;
                index += 1;
            }
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package high-trust"));
                }
                check = true;
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package high-trust",
        &[
            "--release-policy",
            "--release-policy-hash",
            "--runner-policy",
            "--runner-policy-hash",
            "--challenge-runner-policy",
            "--challenge-runner-policy-hash",
            "--checker-registry",
            "--out",
            "--check",
        ],
    )?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::HighTrust(Box::new(PackageHighTrustOptions {
            common,
            release_policy: release_policy.ok_or_else(|| {
                flag_error("--release-policy", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            release_policy_hash: release_policy_hash.ok_or_else(|| {
                flag_error("--release-policy-hash", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            runner_policy: runner_policy.ok_or_else(|| {
                flag_error("--runner-policy", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            runner_policy_hash: runner_policy_hash.ok_or_else(|| {
                flag_error("--runner-policy-hash", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            challenge_runner_policy: challenge_runner_policy.ok_or_else(|| {
                flag_error(
                    "--challenge-runner-policy",
                    UsageReason::MissingRequiredFlag,
                )
                .with_command("package high-trust")
            })?,
            challenge_runner_policy_hash: challenge_runner_policy_hash.ok_or_else(|| {
                flag_error(
                    "--challenge-runner-policy-hash",
                    UsageReason::MissingRequiredFlag,
                )
                .with_command("package high-trust")
            })?,
            checker_registry: checker_registry.ok_or_else(|| {
                flag_error("--checker-registry", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            out,
            check,
        })),
    )))
}

fn parse_package_verify_certs_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageVerifyCerts));
    }

    let mut common_tokens = Vec::new();
    let mut checker = None::<PackageChecker>;
    let mut package_lock_mode = None::<PackageLockInputMode>;
    let mut changed = false;
    let mut audit_cache = None::<PackageAuditCacheMode>;
    let mut verifier_memo = None::<PackageVerifierMemoMode>;
    let mut jobs = None::<usize>;
    let mut runner_policy = None::<PathBuf>;
    let mut runner_policy_hash = None::<String>;
    let mut checker_registry = None::<PathBuf>;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--changed" => {
                if changed {
                    return Err(flag_error("--changed", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                changed = true;
                index += 1;
            }
            "--checker" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--checker", "package verify-certs")?;
                checker = Some(parse_checker(value)?);
                index += 2;
            }
            "--checker=reference" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                checker = Some(PackageChecker::Reference);
                index += 1;
            }
            "--checker=fast" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                checker = Some(PackageChecker::Fast);
                index += 1;
            }
            "--checker=external" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                checker = Some(PackageChecker::External);
                index += 1;
            }
            token if token.starts_with("--checker=") => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--checker=");
                if value.is_empty() {
                    return Err(flag_error("--checker", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                checker = Some(parse_checker(value)?);
                index += 1;
            }
            "--package-lock" => {
                if package_lock_mode.is_some() {
                    return Err(flag_error("--package-lock", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--package-lock", "package verify-certs")?;
                package_lock_mode = Some(parse_package_lock_mode(value)?);
                index += 2;
            }
            token if token.starts_with("--package-lock=") => {
                if package_lock_mode.is_some() {
                    return Err(flag_error("--package-lock", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--package-lock=");
                if value.is_empty() {
                    return Err(flag_error("--package-lock", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                package_lock_mode = Some(parse_package_lock_mode(value)?);
                index += 1;
            }
            "--audit-cache" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--audit-cache", "package verify-certs")?;
                audit_cache = Some(parse_audit_cache_mode(value)?);
                index += 2;
            }
            "--audit-cache=off" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(PackageAuditCacheMode::Off);
                index += 1;
            }
            "--audit-cache=read-through" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(PackageAuditCacheMode::ReadThrough);
                index += 1;
            }
            "--audit-cache=local-hit" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(PackageAuditCacheMode::LocalHit);
                index += 1;
            }
            token if token.starts_with("--audit-cache=") => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--audit-cache=");
                if value.is_empty() {
                    return Err(flag_error("--audit-cache", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(parse_audit_cache_mode(value)?);
                index += 1;
            }
            "--verifier-memo" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--verifier-memo", "package verify-certs")?;
                verifier_memo = Some(parse_verifier_memo_mode(value)?);
                index += 2;
            }
            "--verifier-memo=off" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(PackageVerifierMemoMode::Off);
                index += 1;
            }
            "--verifier-memo=read-through" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(PackageVerifierMemoMode::ReadThrough);
                index += 1;
            }
            "--verifier-memo=disk" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(PackageVerifierMemoMode::Disk);
                index += 1;
            }
            token if token.starts_with("--verifier-memo=") => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--verifier-memo=");
                if value.is_empty() {
                    return Err(flag_error("--verifier-memo", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(parse_verifier_memo_mode(value)?);
                index += 1;
            }
            "--jobs" => {
                if jobs.is_some() {
                    return Err(flag_error("--jobs", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--jobs", "package verify-certs")?;
                jobs = Some(parse_jobs(value)?);
                index += 2;
            }
            token if token.starts_with("--jobs=") => {
                if jobs.is_some() {
                    return Err(flag_error("--jobs", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--jobs=");
                if value.is_empty() {
                    return Err(flag_error("--jobs", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                jobs = Some(parse_jobs(value)?);
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--timings", "package verify-certs")?;
                timings = Some(parse_timing_mode(value, "package verify-certs")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                timings = Some(parse_timing_mode(value, "package verify-certs")?);
                index += 1;
            }
            "--runner-policy" => {
                if runner_policy.is_some() {
                    return Err(flag_error("--runner-policy", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--runner-policy", "package verify-certs")?;
                runner_policy = Some(PathBuf::from(value));
                index += 2;
            }
            token if token.starts_with("--runner-policy=") => {
                if runner_policy.is_some() {
                    return Err(flag_error("--runner-policy", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--runner-policy=");
                if value.is_empty() {
                    return Err(flag_error("--runner-policy", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                runner_policy = Some(PathBuf::from(value));
                index += 1;
            }
            "--runner-policy-hash" => {
                if runner_policy_hash.is_some() {
                    return Err(
                        flag_error("--runner-policy-hash", UsageReason::DuplicateFlag)
                            .with_command("package verify-certs"),
                    );
                }
                let value =
                    flag_value(args, index, "--runner-policy-hash", "package verify-certs")?;
                runner_policy_hash = Some(value.to_owned());
                index += 2;
            }
            token if token.starts_with("--runner-policy-hash=") => {
                if runner_policy_hash.is_some() {
                    return Err(
                        flag_error("--runner-policy-hash", UsageReason::DuplicateFlag)
                            .with_command("package verify-certs"),
                    );
                }
                let value = token.trim_start_matches("--runner-policy-hash=");
                if value.is_empty() {
                    return Err(
                        flag_error("--runner-policy-hash", UsageReason::MissingFlagValue)
                            .with_command("package verify-certs"),
                    );
                }
                runner_policy_hash = Some(value.to_owned());
                index += 1;
            }
            "--checker-registry" => {
                if checker_registry.is_some() {
                    return Err(flag_error("--checker-registry", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--checker-registry", "package verify-certs")?;
                checker_registry = Some(PathBuf::from(value));
                index += 2;
            }
            token if token.starts_with("--checker-registry=") => {
                if checker_registry.is_some() {
                    return Err(flag_error("--checker-registry", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--checker-registry=");
                if value.is_empty() {
                    return Err(
                        flag_error("--checker-registry", UsageReason::MissingFlagValue)
                            .with_command("package verify-certs"),
                    );
                }
                checker_registry = Some(PathBuf::from(value));
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package verify-certs",
        &[
            "--checker",
            "--package-lock",
            "--changed",
            "--runner-policy",
            "--runner-policy-hash",
            "--checker-registry",
            "--audit-cache",
            "--verifier-memo",
            "--jobs",
            "--timings",
        ],
    )?;
    let checker = checker.unwrap_or(PackageChecker::Reference);
    let package_lock_mode = package_lock_mode.unwrap_or(PackageLockInputMode::CheckedFile);
    let audit_cache = audit_cache.unwrap_or(PackageAuditCacheMode::Off);
    let verifier_memo = verifier_memo.unwrap_or(PackageVerifierMemoMode::Off);
    let jobs = jobs.unwrap_or(1);
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    let validation = PackageVerifyOptionsValidationInput {
        checker,
        changed,
        audit_cache,
        verifier_memo,
        jobs,
        external_options: PackageExternalCheckerOptionsState::from_flags(
            runner_policy.is_some(),
            runner_policy_hash.is_some(),
            checker_registry.is_some(),
        ),
        package_lock_mode,
    };
    if let Err(error) = validate_package_verify_options(validation) {
        return Err(package_verify_validation_cli_error(
            validation,
            error,
            &runner_policy,
            &runner_policy_hash,
            &checker_registry,
        ));
    }
    let external = if checker == PackageChecker::External {
        Some(PackageExternalCheckerOptions {
            runner_policy: runner_policy.expect("external runner policy validated"),
            runner_policy_hash: runner_policy_hash.expect("external runner policy hash validated"),
            checker_registry: checker_registry.expect("external checker registry validated"),
        })
    } else {
        None
    };
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::VerifyCerts(PackageVerifyCertsOptions {
            common,
            checker,
            changed,
            audit_cache,
            verifier_memo,
            jobs,
            external,
            timings,
            package_lock_mode,
        }),
    )))
}

fn package_verify_validation_cli_error(
    options: PackageVerifyOptionsValidationInput,
    error: PackageVerifyOptionsValidationError,
    runner_policy: &Option<PathBuf>,
    runner_policy_hash: &Option<String>,
    checker_registry: &Option<PathBuf>,
) -> CliUsageError {
    let unsupported = |flag: &'static str, value: String| {
        CliUsageError::new(UsageReason::UnsupportedFlag)
            .with_command("package verify-certs")
            .with_flag(flag)
            .with_value(value)
    };
    match error {
        PackageVerifyOptionsValidationError::JobsZero => {
            CliUsageError::new(UsageReason::InvalidFlagValue)
                .with_command("package verify-certs")
                .with_flag("--jobs")
                .with_value(options.jobs.to_string())
        }
        PackageVerifyOptionsValidationError::ChangedWithExternalChecker => {
            unsupported("--changed", options.checker.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ChangedWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ChangedWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithParallelJobs => {
            unsupported("--jobs", options.jobs.to_string())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithAuditCache => {
            unsupported("--audit-cache", options.audit_cache.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::ExternalCheckerWithReconstructedLock => unsupported(
            "--package-lock",
            format!(
                "{};checker={}",
                options.package_lock_mode.as_str(),
                options.checker.as_str()
            ),
        ),
        PackageVerifyOptionsValidationError::AuditCacheWithParallelJobs => unsupported(
            "--jobs",
            format!(
                "jobs={};audit_cache={}",
                options.jobs,
                options.audit_cache.as_str()
            ),
        ),
        PackageVerifyOptionsValidationError::AuditCacheWithVerifierMemo => {
            unsupported("--verifier-memo", options.verifier_memo.as_str().to_owned())
        }
        PackageVerifyOptionsValidationError::MissingExternalCheckerOptions => {
            let flag = if runner_policy.is_none() {
                "--runner-policy"
            } else if runner_policy_hash.is_none() {
                "--runner-policy-hash"
            } else {
                "--checker-registry"
            };
            flag_error(flag, UsageReason::MissingRequiredFlag).with_command("package verify-certs")
        }
        PackageVerifyOptionsValidationError::UnexpectedExternalCheckerOptions => {
            let flag = if runner_policy.is_some() {
                "--runner-policy"
            } else if runner_policy_hash.is_some() {
                "--runner-policy-hash"
            } else {
                debug_assert!(checker_registry.is_some());
                "--checker-registry"
            };
            flag_error(flag, UsageReason::UnsupportedFlag).with_command("package verify-certs")
        }
    }
}

fn parse_checker(value: &str) -> Result<PackageChecker, CliUsageError> {
    match value {
        "reference" => Ok(PackageChecker::Reference),
        "fast" => Ok(PackageChecker::Fast),
        "external" => Ok(PackageChecker::External),
        other => Err(CliUsageError::new(UsageReason::UnsupportedChecker)
            .with_command("package verify-certs")
            .with_flag("--checker")
            .with_value(other)),
    }
}

fn parse_package_lock_mode(value: &str) -> Result<PackageLockInputMode, CliUsageError> {
    match value {
        "checked" => Ok(PackageLockInputMode::CheckedFile),
        "reconstructed" => Ok(PackageLockInputMode::ReconstructedInMemory),
        other => Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package verify-certs")
            .with_flag("--package-lock")
            .with_value(other)),
    }
}

fn parse_audit_cache_mode(value: &str) -> Result<PackageAuditCacheMode, CliUsageError> {
    match value {
        "off" => Ok(PackageAuditCacheMode::Off),
        "read-through" => Ok(PackageAuditCacheMode::ReadThrough),
        "local-hit" => Ok(PackageAuditCacheMode::LocalHit),
        other => Err(CliUsageError::new(UsageReason::UnsupportedAuditCacheMode)
            .with_command("package verify-certs")
            .with_flag("--audit-cache")
            .with_value(other)),
    }
}

fn parse_verifier_memo_mode(value: &str) -> Result<PackageVerifierMemoMode, CliUsageError> {
    match value {
        "off" => Ok(PackageVerifierMemoMode::Off),
        "read-through" => Ok(PackageVerifierMemoMode::ReadThrough),
        "disk" => Ok(PackageVerifierMemoMode::Disk),
        other => Err(CliUsageError::new(UsageReason::UnsupportedVerifierMemoMode)
            .with_command("package verify-certs")
            .with_flag("--verifier-memo")
            .with_value(other)),
    }
}

fn parse_refactor_plan_scope(value: &str) -> Result<PackageRefactorPlanScope, CliUsageError> {
    match value {
        "modules" => Ok(PackageRefactorPlanScope::Modules),
        "theorems" => Ok(PackageRefactorPlanScope::Theorems),
        "both" => Ok(PackageRefactorPlanScope::Both),
        other => Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package refactor-plan")
            .with_flag("--scope")
            .with_value(other)),
    }
}

fn parse_refactor_plan_module(value: &str) -> Result<Name, CliUsageError> {
    let name = Name::from_dotted(value);
    if name.is_canonical() {
        Ok(name)
    } else {
        Err(CliUsageError::new(UsageReason::InvalidModuleName)
            .with_command("package refactor-plan")
            .with_flag("--module")
            .with_value(value))
    }
}

fn parse_refactor_plan_top(value: &str) -> Result<usize, CliUsageError> {
    let Ok(top) = value.parse::<usize>() else {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package refactor-plan")
            .with_flag("--top")
            .with_value(value));
    };
    if !(1..=200).contains(&top) {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package refactor-plan")
            .with_flag("--top")
            .with_value(value));
    }
    Ok(top)
}

fn parse_timing_mode(
    value: &str,
    command: &'static str,
) -> Result<PackageTimingMode, CliUsageError> {
    match value {
        "off" => Ok(PackageTimingMode::Off),
        "summary" => Ok(PackageTimingMode::Summary),
        "detailed" => Ok(PackageTimingMode::Detailed),
        other => Err(CliUsageError::new(UsageReason::UnsupportedTimingMode)
            .with_command(command)
            .with_flag("--timings")
            .with_value(other)),
    }
}

fn parse_build_check_cache_mode(value: &str) -> Result<PackageBuildCheckCacheMode, CliUsageError> {
    match value {
        "off" => Ok(PackageBuildCheckCacheMode::Off),
        "read-through" => Ok(PackageBuildCheckCacheMode::ReadThrough),
        other => Err(
            CliUsageError::new(UsageReason::UnsupportedBuildCheckCacheMode)
                .with_command("package build-certs")
                .with_flag("--build-check-cache")
                .with_value(other),
        ),
    }
}

fn parse_jobs(value: &str) -> Result<usize, CliUsageError> {
    let Ok(jobs) = value.parse::<usize>() else {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package verify-certs")
            .with_flag("--jobs")
            .with_value(value));
    };
    if !package_verify_jobs_are_valid(jobs) {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package verify-certs")
            .with_flag("--jobs")
            .with_value(value));
    }
    Ok(jobs)
}

fn parse_path_flag(
    args: &[String],
    index: &mut usize,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<PathBuf>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let value = flag_value(args, *index, flag, command)?;
    *target = Some(PathBuf::from(value));
    *index += 2;
    Ok(())
}

fn parse_path_equals_flag(
    token: &str,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<PathBuf>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let prefix = format!("{flag}=");
    let value = token.trim_start_matches(&prefix);
    if value.is_empty() {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    *target = Some(PathBuf::from(value));
    Ok(())
}

fn parse_string_flag(
    args: &[String],
    index: &mut usize,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<String>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let value = flag_value(args, *index, flag, command)?;
    *target = Some(value.to_owned());
    *index += 2;
    Ok(())
}

fn parse_string_equals_flag(
    token: &str,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<String>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let prefix = format!("{flag}=");
    let value = token.trim_start_matches(&prefix);
    if value.is_empty() {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    *target = Some(value.to_owned());
    Ok(())
}

fn parse_common_options(
    args: &[String],
    command: &'static str,
    command_flags: &[&str],
) -> Result<PackageCommonOptions, CliUsageError> {
    let mut common = PackageCommonOptions::default();
    let mut root_seen = false;
    let mut json_seen = false;
    let mut index = 0usize;

    while index < args.len() {
        match args[index].as_str() {
            "--root" => {
                if root_seen {
                    return Err(
                        flag_error("--root", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                let value = flag_value(args, index, "--root", command)?;
                common.root = PathBuf::from(value);
                root_seen = true;
                index += 2;
            }
            token if token.starts_with("--root=") => {
                if root_seen {
                    return Err(
                        flag_error("--root", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                let value = token.trim_start_matches("--root=");
                if value.is_empty() {
                    return Err(
                        flag_error("--root", UsageReason::MissingFlagValue).with_command(command)
                    );
                }
                common.root = PathBuf::from(value);
                root_seen = true;
                index += 1;
            }
            "--json" => {
                if json_seen {
                    return Err(
                        flag_error("--json", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                common.json = true;
                json_seen = true;
                index += 1;
            }
            flag if is_unsupported_clr04_flag(flag) || command_flags.contains(&flag) => {
                return Err(flag_error(flag, UsageReason::UnsupportedFlag).with_command(command));
            }
            flag if flag.starts_with('-') => {
                return Err(flag_error(flag, UsageReason::UnknownFlag).with_command(command));
            }
            value => {
                return Err(CliUsageError::new(UsageReason::UnknownCommand)
                    .with_command(format!("{command} {value}")));
            }
        }
    }

    Ok(common)
}

fn flag_value<'a>(
    args: &'a [String],
    index: usize,
    flag: &'static str,
    command: &'static str,
) -> Result<&'a str, CliUsageError> {
    let value = args
        .get(index + 1)
        .ok_or_else(|| flag_error(flag, UsageReason::MissingFlagValue).with_command(command))?;
    if value.starts_with('-') {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    Ok(value)
}

fn flag_equals_value<'a>(
    token: &'a str,
    flag: &'static str,
    command: &'static str,
) -> Result<&'a str, CliUsageError> {
    let value = token.strip_prefix(&format!("{flag}=")).unwrap_or_default();
    if value.is_empty() {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    Ok(value)
}

fn flag_error(flag: impl Into<String>, reason: UsageReason) -> CliUsageError {
    CliUsageError::new(reason).with_flag(flag)
}

fn contains_help(args: &[String]) -> bool {
    args.iter()
        .any(|argument| argument == "--help" || argument == "-h")
}

fn is_unsupported_clr04_flag(flag: &str) -> bool {
    matches!(
        flag,
        "--changed"
            | "--all"
            | "--registry"
            | "--network"
            | "--latest"
            | "--runner-policy"
            | "--runner-policy-hash"
            | "--checker-registry"
            | "--upload"
            | "--sign"
            | "--update-manifest-hashes"
            | "--include-source"
            | "--include-replay"
            | "--include-ai-traces"
            | "--checker"
            | "--package-lock"
            | "--audit-cache"
            | "--verifier-memo"
            | "--build-check-cache"
            | "--jobs"
            | "--timings"
            | "--base"
            | "--scope"
            | "--module"
            | "--declaration"
            | "--top"
            | "--include-source-metrics"
    ) || flag.starts_with("--changed=")
        || flag.starts_with("--all=")
        || flag.starts_with("--registry=")
        || flag.starts_with("--network=")
        || flag.starts_with("--latest=")
        || flag.starts_with("--runner-policy=")
        || flag.starts_with("--runner-policy-hash=")
        || flag.starts_with("--checker-registry=")
        || flag.starts_with("--upload=")
        || flag.starts_with("--sign=")
        || flag.starts_with("--update-manifest-hashes=")
        || flag.starts_with("--include-source=")
        || flag.starts_with("--include-replay=")
        || flag.starts_with("--include-ai-traces=")
        || flag.starts_with("--checker=")
        || flag.starts_with("--package-lock=")
        || flag.starts_with("--audit-cache=")
        || flag.starts_with("--verifier-memo=")
        || flag.starts_with("--build-check-cache=")
        || flag.starts_with("--jobs=")
        || flag.starts_with("--timings=")
        || flag.starts_with("--base=")
        || flag.starts_with("--scope=")
        || flag.starts_with("--module=")
        || flag.starts_with("--declaration=")
        || flag.starts_with("--top=")
        || flag.starts_with("--include-source-metrics=")
}

/// Render deterministic help text.
pub fn render_help(topic: HelpTopic) -> &'static str {
    match topic {
        HelpTopic::Root => {
            "Usage: npa <command> [options]\n\nCommands:\n  package    Package manifest and certificate commands\n  version    Print npa CLI version\n\nOptions:\n  --help\n  --version"
        }
        HelpTopic::Package => {
            "Usage: npa package <command> [options]\n\nCommands:\n  check\n  build-certs\n  axiom-report\n  index\n  theorem-premise-report\n  export-summary\n  export-candidate-metadata\n  prepare-l2-review-input\n  aggregate-l2-acceptance\n  validate-l2-acceptance\n  validate-l2-namespace-transport\n  prepare-promotion\n  materialize-promotion\n  validate-promotion-materialization\n  validate-promotion-origin-registry\n  register-equivalent-promotion-origin\n  verify-certs\n  check-hashes\n  audit-artifact-ledger\n  lock\n  publish-plan\n  check-generated\n  high-trust\n  gate-plan\n  refactor-plan\n\nCommon options:\n  --root PATH    Package root, default: .\n  --json         Emit deterministic JSON diagnostics\n  --help         Show help"
        }
        HelpTopic::PackageCheck => {
            "Usage: npa package check [--root PATH] [--json]\n\nValidate npa-package.toml metadata without reading source or certificate artifacts."
        }
        HelpTopic::PackageBuildCerts => {
            "Usage: npa package build-certs [--root PATH] [--json] [--check] [--build-check-cache off|read-through] [--update-manifest-hashes] [--module MODULE]... [--changed]\n\nRebuild package certificates. Build-check caching requires --check; for example: --check --build-check-cache read-through. --module and --changed select targeted authoring builds and are mutually exclusive. Targeted ordinary builds require --check; targeted writes require --update-manifest-hashes and rebuild the dependency-safe local dependent closure. Full build-certs --check and source-free verification remain required release gates. --update-manifest-hashes refreshes local module hash pins and declared metadata before rebuilding generated/package-lock.json."
        }
        HelpTopic::PackageAxiomReport => {
            "Usage: npa package axiom-report [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/axiom-report.json from source-free package certificate artifacts. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageIndex => {
            "Usage: npa package index [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/theorem-index.json from source-free package certificate artifacts. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageTheoremPremiseReport => {
            "Usage: npa package theorem-premise-report [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/theorem-premise-report.json from source-free package certificate artifacts. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageExportSummary => {
            "Usage: npa package export-summary [--root PATH] [--json] [--check] [--out PATH] [--timings off|summary|detailed]\n\nGenerate or check generated/verified-export-summary.json from source-free package certificate artifacts. If --out is provided, PATH is relative to --root; for example, --root proofs --out generated/custom-export-summary.json writes proofs/generated/custom-export-summary.json. Omitting --out uses generated/verified-export-summary.json. The summary and timing telemetry are not proof evidence."
        }
        HelpTopic::PackageExportCandidateMetadata => {
            "Usage: npa package export-candidate-metadata [--root PATH] [--json] --module MODULE --declaration DECL --out PATH\n\nExport npa.candidate-verification-metadata.v1 for a checked source-free package theorem. --out PATH is relative to --root; for example, --root proofs --out generated/name.metadata.json writes proofs/generated/name.metadata.json. The metadata is not proof evidence."
        }
        HelpTopic::PackageValidateL2Acceptance => {
            "Usage: npa package validate-l2-acceptance [--root PATH] [--json] --policy PATH --acceptance PATH [--module MODULE]...\n\nValidate repository-governed theorem-level L2 decisions against the current canonical policy, package manifest, and checked theorem index. Repeating --module requires complete L2 coverage of every local public theorem in each selected module. Acceptance metadata is not proof evidence."
        }
        HelpTopic::PackagePrepareL2ReviewInput => {
            "Usage: npa package prepare-l2-review-input [--root PATH] [--json] --policy PATH --module MODULE --declaration DECL --out PATH [--check]\n\nExport or check one immutable canonical theorem review input."
        }
        HelpTopic::PackageAggregateL2Acceptance => {
            "Usage: npa package aggregate-l2-acceptance [--root PATH] [--json] --policy PATH --review-input PATH... --review PATH... [--existing PATH] [--replace MODULE::DECL]... --out PATH [--check]\n\nValidate unanimous independent reports and atomically materialize a canonical v2 L2 ledger."
        }
        HelpTopic::PackageValidateL2NamespaceTransport => {
            "Usage: npa package validate-l2-namespace-transport --source-root PATH --target-baseline-root PATH --target-root PATH --acceptance-policy PATH --source-acceptance PATH --transport-policy PATH --mapping PATH [--out PATH] [--check] [--json]\n\nValidate source-free, canonical-certificate namespace-only transport."
        }
        HelpTopic::PackagePreparePromotion => {
            "Usage: npa package prepare-promotion --root PATH --target-baseline-root PATH --acceptance-policy PATH --source-acceptance PATH --transport-policy PATH --mapping PATH [--equivalent-origin-root PATH]... --out PATH [--check] [--json]\n       npa package prepare-promotion --root PATH --target-baseline-root PATH --declaration-request PATH [--equivalent-origin-root PATH]... --out PATH [--check] [--json]\n\nBuild or check a canonical mathlib promotion plan. The declaration request form selects a bounded verified declaration closure and is mutually exclusive with L2 namespace-transport inputs."
        }
        HelpTopic::PackageMaterializePromotion => {
            "Usage: npa package materialize-promotion --root PATH --target-baseline-root PATH --target-root PATH --plan PATH [--equivalent-origin-root PATH]... --phase temporary|tracked [--transport-attestation PATH|--verification-attestation PATH] [--dry-run|--apply] [--json]\n       npa package materialize-promotion --target-root PATH --recover PATH [--json]\n\nValidate and deterministically materialize a promotion plan. Plan v1 tracked apply requires transport evidence; plan v2 tracked apply requires a verified materialization attestation."
        }
        HelpTopic::PackageValidatePromotionMaterialization => {
            "Usage: npa package validate-promotion-materialization --root PATH --target-baseline-root PATH --target-root PATH --plan PATH --out PATH [--check] [--json]\n\nIndependently verify one disposable declaration-level target, including deterministic rebuild and normalized closure equality, then create or check its canonical attestation."
        }
        HelpTopic::PackageValidatePromotionOriginRegistry => {
            "Usage: npa package validate-promotion-origin-registry [--root PATH] [--source-root PATH]... [--previous-registry PATH] [--json]\n\nValidate the canonical target registry, current target identities, optional source identities, and an optional append-only transition."
        }
        HelpTopic::PackageRegisterEquivalentPromotionOrigin => {
            "Usage: npa package register-equivalent-promotion-origin --root PATH --target-root PATH --promotion-id HASH [--dry-run|--apply] [--json]\n\nValidate and optionally append one artifact-identical source package origin to an existing promotion route. Dry-run is the default."
        }
        HelpTopic::PackageVerifyCerts => {
            "Usage: npa package verify-certs [--root PATH] [--json] [--changed] [--checker reference|fast|external] [--package-lock checked|reconstructed] [--audit-cache off|read-through|local-hit] [--verifier-memo off|read-through|disk] [--jobs N] [--timings off|summary|detailed] [--runner-policy PATH --runner-policy-hash HASH --checker-registry PATH]\n\nVerify certificates through the source-free package verifier. The default checker is reference, the package-lock input defaults to checked, the default audit cache mode is off, the default verifier memo mode is off, the default jobs value is 1, and timings default to off. Reconstructed is unavailable with the external checker. --changed verifies only package modules whose certificate files are changed in Git, plus source-free imports needed by the verifier. read-through audit cache and verifier memo modes still run live verification; local-hit and disk verifier memo hits are local-only acceleration and are not proof evidence; timing telemetry is informational and is not proof evidence; external mode requires explicit runner policy and checker registry inputs and does not support audit-cache, verifier-memo, or changed-certificate acceleration."
        }
        HelpTopic::PackageCheckHashes => {
            "Usage: npa package check-hashes [--root PATH] [--json]\n\nCheck checked-in package artifact hashes."
        }
        HelpTopic::PackageAuditArtifactLedger => {
            "Usage: npa package audit-artifact-ledger [--root PATH] [--json]\n  [--module MODULE]...\n\nCompare current source/certificate bytes and live reference-checker identities\nwith npa-package.toml and declared meta.json ledgers. The command writes no\nfiles and does not require generated/package-lock.json."
        }
        HelpTopic::PackageLock => {
            "Usage: npa package lock <command> [options]\n\nCommands:\n  check\n  write\n\nCommon options:\n  --root PATH    Package root, default: .\n  --json         Emit deterministic JSON diagnostics\n  --help         Show help"
        }
        HelpTopic::PackageLockCheck => {
            "Usage: npa package lock check [--root PATH] [--json]\n\nCheck generated/package-lock.json against the current package manifest and certificate artifacts without writing files."
        }
        HelpTopic::PackageLockWrite => {
            "Usage: npa package lock write [--root PATH] [--json]\n\nRegenerate generated/package-lock.json from the current package manifest and certificate artifacts without rebuilding certificates."
        }
        HelpTopic::PackagePublishPlan => {
            "Usage: npa package publish-plan [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/publish-plan.json from source-free package release metadata. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageCheckGenerated => {
            "Usage: npa package check-generated [--root PATH] [--json] [--timings off|summary|detailed]\n\nCheck generated axiom report, theorem index, theorem-premise report, verified export summary, publish plan, and fast certificate verification from one source-free package snapshot. This local aggregate command is not proof evidence."
        }
        HelpTopic::PackageHighTrust => {
            "Usage: npa package high-trust [--root PATH] [--json] --release-policy PATH --release-policy-hash HASH --runner-policy PATH --runner-policy-hash HASH --challenge-runner-policy PATH --challenge-runner-policy-hash HASH --checker-registry PATH [--out PATH] [--check]\n\nGenerate or check verified_high_trust release evidence after external and high-trust-reference gates pass. The artifact is release evidence, not checker input."
        }
        HelpTopic::PackageGatePlan => {
            "Usage: npa package gate-plan [--root PATH] [--json] --base REF\n\nRecommend the cheapest sufficient package gate commands from git diff --name-only REF...HEAD. The planner runs no gates and is not proof evidence."
        }
        HelpTopic::PackageRefactorPlan => {
            "Usage: npa package refactor-plan [--root PATH] [--json] [--scope modules|theorems|both] [--module NAME] [--top N]\n\nRank advisory module and theorem-family refactor candidates from package metadata. The plan is not proof evidence and does not read source files."
        }
    }
}
