use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::trust::{
    theorem_invention_artifact_identity_hash, theorem_invention_generalized_context_hash,
    theorem_invention_verification_command_hash, ProofAcceptanceState, TheoremInventionArtifact,
    TheoremInventionPromotionIntent, TheoremLevel,
};
use crate::types::format_hash_string;
use npa_cert::Hash;
use sha2::{Digest, Sha256};

pub const SUBGOAL_CLUSTER_KEY_PROFILE: &str = "npa.library-growth.subgoal-cluster-key.v1";
pub const SUBGOAL_CLUSTER_LOCAL_CONTEXT_PROFILE: &str =
    "npa.library-growth.subgoal-cluster-local-context.v1";
pub const SUBGOAL_CLUSTER_PARENT_EXAMPLE_PROFILE: &str =
    "npa.library-growth.subgoal-cluster-parent-example.v1";
pub const LIBRARY_GAP_SIGNAL_PROFILE: &str = "npa.library-growth.gap-signal.v1";
pub const SUBGOAL_CLUSTER_MIN_PARENT_EXAMPLES: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgoalClusterKey {
    pub normalized_target_hash: Hash,
    pub normalized_local_type_hashes: Vec<Hash>,
    pub head_symbols: Vec<String>,
    pub universe_erased_shape_hash: Hash,
    pub approved_commutative_canonicalizations: Vec<SubgoalClusterCommutativeCanonicalization>,
    pub domain_tags: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgoalClusterCommutativeCanonicalization {
    pub operator_symbol: String,
    pub operand_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgoalClusterParentExample {
    pub example_hash: Hash,
    pub source_module: String,
    pub declaration_name: String,
    pub goal_fingerprint: Hash,
    pub parent_goal_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SubgoalClusterLikelyProofStrategy {
    ExistingPremiseSearch,
    IntroRewrite,
    Induction,
    Solver,
    Simplification,
    Unknown,
}

impl SubgoalClusterLikelyProofStrategy {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExistingPremiseSearch => "existing_premise_search",
            Self::IntroRewrite => "intro_rewrite",
            Self::Induction => "induction",
            Self::Solver => "solver",
            Self::Simplification => "simplification",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LibraryGapSignalKind {
    NoCandidateStop,
    RepeatedFailedSubgoal,
    FrequentExplicitProofPattern,
    RecreatedHelperTheorem,
    LargeDuplicatedProofTerm,
    ConcentratedImportProposal,
}

impl LibraryGapSignalKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NoCandidateStop => "no_candidate_stop",
            Self::RepeatedFailedSubgoal => "repeated_failed_subgoal",
            Self::FrequentExplicitProofPattern => "frequent_explicit_proof_pattern",
            Self::RecreatedHelperTheorem => "recreated_helper_theorem",
            Self::LargeDuplicatedProofTerm => "large_duplicated_proof_term",
            Self::ConcentratedImportProposal => "concentrated_import_proposal",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryGapSignalObservation {
    pub signal_hash: Hash,
    pub kind: LibraryGapSignalKind,
    pub source_module: String,
    pub source_id: String,
    pub evidence_hash: Hash,
    pub occurrence_count: u64,
    pub proposed_import_module: Option<String>,
    pub display_text: Option<String>,
    pub observed_wall_clock_ms: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryGapSignalSummary {
    pub kind: LibraryGapSignalKind,
    pub signal_count: u64,
    pub total_occurrences: u64,
    pub source_modules: Vec<String>,
    pub proposed_import_modules: Vec<String>,
    pub signal_hashes: Vec<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SubgoalClusterProposalStatus {
    ProposedCandidateLemma,
    Verified,
    Available,
    PromotionReady,
}

impl SubgoalClusterProposalStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProposedCandidateLemma => "proposed_candidate_lemma",
            Self::Verified => "verified",
            Self::Available => "available",
            Self::PromotionReady => "promotion_ready",
        }
    }

    pub const fn is_untrusted_proposal(self) -> bool {
        matches!(self, Self::ProposedCandidateLemma)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgoalClusterObservation {
    pub snapshot_hash: Hash,
    pub snapshot_verified: bool,
    pub key: SubgoalClusterKey,
    pub local_context_hash: Hash,
    pub parent_example: SubgoalClusterParentExample,
    pub likely_proof_strategy: SubgoalClusterLikelyProofStrategy,
    pub gap_signals: Vec<LibraryGapSignalObservation>,
    pub model_output_rank: Option<u64>,
    pub observed_wall_clock_ms: Option<u64>,
    pub display_text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgoalCluster {
    pub cluster_id: Hash,
    pub key: SubgoalClusterKey,
    pub parent_examples: Vec<SubgoalClusterParentExample>,
    pub gap_signals: Vec<LibraryGapSignalObservation>,
    pub likely_proof_strategy: SubgoalClusterLikelyProofStrategy,
    pub proposal_status: SubgoalClusterProposalStatus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgoalClusterOptions {
    pub accepted_snapshot_hashes: Vec<Hash>,
    pub min_parent_examples: usize,
}

impl SubgoalClusterOptions {
    pub fn authoring_boundary(accepted_snapshot_hashes: Vec<Hash>) -> Self {
        Self {
            accepted_snapshot_hashes,
            min_parent_examples: SUBGOAL_CLUSTER_MIN_PARENT_EXAMPLES,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SubgoalClusterField {
    HeadSymbol,
    DomainTag,
    CommutativeOperatorSymbol,
    ParentSourceModule,
    ParentDeclarationName,
    GapSignalSourceModule,
    GapSignalSourceId,
    GapSignalImportModule,
}

impl SubgoalClusterField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::HeadSymbol => "head_symbol",
            Self::DomainTag => "domain_tag",
            Self::CommutativeOperatorSymbol => "commutative_operator_symbol",
            Self::ParentSourceModule => "parent_source_module",
            Self::ParentDeclarationName => "parent_declaration_name",
            Self::GapSignalSourceModule => "gap_signal_source_module",
            Self::GapSignalSourceId => "gap_signal_source_id",
            Self::GapSignalImportModule => "gap_signal_import_module",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SubgoalClusterError {
    EmptyIdentifier {
        field: SubgoalClusterField,
    },
    StaleSnapshot {
        snapshot_hash: Hash,
    },
    UnverifiedSnapshot {
        snapshot_hash: Hash,
    },
    ModifiedLocalContext {
        expected: Hash,
        actual: Hash,
    },
    ParentExampleHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    GapSignalHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    InvalidProposalStatus {
        status: SubgoalClusterProposalStatus,
    },
    InsufficientParentExamples {
        cluster_id: Hash,
        required: usize,
        actual: usize,
    },
}

impl SubgoalClusterError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::StaleSnapshot { .. } => "stale_snapshot",
            Self::UnverifiedSnapshot { .. } => "unverified_snapshot",
            Self::ModifiedLocalContext { .. } => "modified_local_context",
            Self::ParentExampleHashMismatch { .. } => "parent_example_hash_mismatch",
            Self::GapSignalHashMismatch { .. } => "gap_signal_hash_mismatch",
            Self::InvalidProposalStatus { .. } => "invalid_proposal_status",
            Self::InsufficientParentExamples { .. } => "insufficient_parent_examples",
        }
    }
}

impl fmt::Display for SubgoalClusterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for SubgoalClusterError {}

pub const LEMMA_GENERALIZATION_INPUT_PROFILE: &str =
    "npa.library-growth.lemma-generalization-input.v1";
pub const LEMMA_GENERALIZED_STATEMENT_PROFILE: &str = "npa.library-growth.generalized-statement.v1";
pub const STATEMENT_NORMALIZATION_REPORT_PROFILE: &str =
    "npa.library-growth.statement-normalization-report.v1";
pub const LIBRARY_REUSE_SCORE_INPUT_PROFILE: &str = "npa.library-growth.reuse-score-input.v1";
pub const LIBRARY_REUSE_SCORE_REPORT_PROFILE: &str = "npa.library-growth.reuse-score-report.v1";
pub const LIBRARY_GROWTH_BUDGET_PROFILE: &str = "npa.library-growth.budget.pg012.v1";
pub const THEOREM_DUPLICATE_IDENTITY_PROFILE: &str =
    "npa.library-growth.theorem-duplicate-identity.v1";
pub const THEOREM_DUPLICATE_REPORT_PROFILE: &str = "npa.library-growth.theorem-duplicate-report.v1";
pub const PROMOTION_JUDGMENT_INPUT_PROFILE: &str = "npa.library-growth.promotion-judgment-input.v1";
pub const PROMOTION_JUDGMENT_REPORT_PROFILE: &str =
    "npa.library-growth.promotion-judgment-report.v1";
pub const PROMOTION_METADATA_PROFILE: &str = "npa.library-growth.promotion-metadata.v1";
pub const PROMOTION_METADATA_CONSISTENCY_REPORT_PROFILE: &str =
    "npa.library-growth.promotion-metadata-consistency-report.v1";
pub const PROMOTION_RANKING_PROFILE: &str = "npa.library-growth.promotion-ranking.pg014.v1";
pub const PROMOTION_RANKING_REPORT_PROFILE: &str = "npa.library-growth.promotion-ranking-report.v1";
pub const CORPUS_ALIAS_PROPOSAL_PROFILE: &str = "npa.library-growth.corpus-alias-proposal.v1";
pub const CORPUS_DEPRECATION_RECORD_PROFILE: &str =
    "npa.library-growth.corpus-deprecation-record.v1";
pub const CORPUS_DEPRECATED_THEOREM_INDEX_ENTRY_PROFILE: &str =
    "npa.library-growth.corpus-deprecated-theorem-index-entry.v1";
pub const PUBLIC_COMPATIBILITY_DECISION_PROFILE: &str =
    "npa.library-growth.public-compatibility-decision.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LemmaGeneralizationBinderKind {
    RegularLocal,
    IndexLocal,
    Carrier,
    Structure,
}

impl LemmaGeneralizationBinderKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RegularLocal => "regular_local",
            Self::IndexLocal => "index_local",
            Self::Carrier => "carrier",
            Self::Structure => "structure",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationLocal {
    pub local_id: String,
    pub type_hash: Hash,
    pub value_hash: Option<Hash>,
    pub depends_on_local_ids: Vec<String>,
    pub occurrence_count: u64,
    pub binder_kind: LemmaGeneralizationBinderKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationPremise {
    pub premise_id: String,
    pub premise_hash: Hash,
    pub depends_on_local_ids: Vec<String>,
    pub occurrence_count: u64,
    pub required_for_typecheck: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationConstantUse {
    pub constant_id: String,
    pub constant_hash: Hash,
    pub may_parameterize: bool,
    pub import_module: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationEqualityCandidate {
    pub equality_id: String,
    pub equality_hash: Hash,
    pub lhs_hash: Hash,
    pub rhs_hash: Hash,
    pub lhs_size: u64,
    pub rhs_size: u64,
    pub can_reverse: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LemmaGeneralizationEqualityOrientation {
    Keep,
    Reverse,
}

impl LemmaGeneralizationEqualityOrientation {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Keep => "keep",
            Self::Reverse => "reverse",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationEqualityDecision {
    pub equality_id: String,
    pub equality_hash: Hash,
    pub orientation: LemmaGeneralizationEqualityOrientation,
    pub oriented_lhs_hash: Hash,
    pub oriented_rhs_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LemmaGeneralizationStructureKind {
    Semigroup,
    Monoid,
    Group,
    Ring,
    Field,
}

impl LemmaGeneralizationStructureKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Semigroup => "semigroup",
            Self::Monoid => "monoid",
            Self::Group => "group",
            Self::Ring => "ring",
            Self::Field => "field",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationStructureCandidate {
    pub structure_id: String,
    pub structure: LemmaGeneralizationStructureKind,
    pub evidence_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LemmaGeneralizationCarrierKind {
    FiniteToGeneral,
    IndexedCarrier,
}

impl LemmaGeneralizationCarrierKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FiniteToGeneral => "finite_to_general",
            Self::IndexedCarrier => "indexed_carrier",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationCarrierCandidate {
    pub carrier_id: String,
    pub kind: LemmaGeneralizationCarrierKind,
    pub source_hash: Hash,
    pub generalized_hash: Hash,
    pub evidence_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationImportNeed {
    pub module: String,
    pub reason_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationTypecheckWitness {
    pub generalized_statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub witness_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaGeneralizationInput {
    pub source_context_hash: Hash,
    pub original_goal_hash: Hash,
    pub normalized_target_hash: Hash,
    pub locals: Vec<LemmaGeneralizationLocal>,
    pub premises: Vec<LemmaGeneralizationPremise>,
    pub constants: Vec<LemmaGeneralizationConstantUse>,
    pub equality_candidates: Vec<LemmaGeneralizationEqualityCandidate>,
    pub structure_candidates: Vec<LemmaGeneralizationStructureCandidate>,
    pub carrier_candidates: Vec<LemmaGeneralizationCarrierCandidate>,
    pub import_candidates: Vec<StatementNormalizationImportNeed>,
    pub typecheck_witness: Option<StatementNormalizationTypecheckWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationBinder {
    pub local_id: String,
    pub type_hash: Hash,
    pub value_hash: Option<Hash>,
    pub binder_kind: LemmaGeneralizationBinderKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationPremise {
    pub premise_id: String,
    pub premise_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationConstantParameter {
    pub constant_id: String,
    pub constant_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationCarrierGeneralization {
    pub carrier_id: String,
    pub kind: LemmaGeneralizationCarrierKind,
    pub source_hash: Hash,
    pub generalized_hash: Hash,
    pub evidence_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StatementNormalizationRejectedAttemptKind {
    PremiseMinimization,
    AlgebraicStructure,
    CarrierGeneralization,
}

impl StatementNormalizationRejectedAttemptKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PremiseMinimization => "premise_minimization",
            Self::AlgebraicStructure => "algebraic_structure",
            Self::CarrierGeneralization => "carrier_generalization",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StatementNormalizationRejectionReason {
    RequiredForTypecheck,
    MissingStructureEvidence,
    MissingCarrierEvidence,
}

impl StatementNormalizationRejectionReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RequiredForTypecheck => "required_for_typecheck",
            Self::MissingStructureEvidence => "missing_structure_evidence",
            Self::MissingCarrierEvidence => "missing_carrier_evidence",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationRejectedAttempt {
    pub kind: StatementNormalizationRejectedAttemptKind,
    pub item_id: String,
    pub reason: StatementNormalizationRejectionReason,
    pub evidence_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementNormalizationReport {
    pub report_hash: Hash,
    pub input_hash: Hash,
    pub source_context_hash: Hash,
    pub original_goal_hash: Hash,
    pub normalized_target_hash: Hash,
    pub generalized_statement_hash: Hash,
    pub binder_order: Vec<StatementNormalizationBinder>,
    pub removed_premises: Vec<StatementNormalizationPremise>,
    pub retained_premises: Vec<StatementNormalizationPremise>,
    pub parameterized_constants: Vec<StatementNormalizationConstantParameter>,
    pub equality_orientations: Vec<StatementNormalizationEqualityDecision>,
    pub selected_structure: Option<LemmaGeneralizationStructureKind>,
    pub carrier_generalizations: Vec<StatementNormalizationCarrierGeneralization>,
    pub import_needs: Vec<StatementNormalizationImportNeed>,
    pub rejected_attempts: Vec<StatementNormalizationRejectedAttempt>,
    pub typecheck_witness: StatementNormalizationTypecheckWitness,
    pub proof_task_allowed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LemmaGeneralizationField {
    LocalId,
    PremiseId,
    ConstantId,
    EqualityId,
    StructureId,
    CarrierId,
    ImportModule,
}

impl LemmaGeneralizationField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LocalId => "local_id",
            Self::PremiseId => "premise_id",
            Self::ConstantId => "constant_id",
            Self::EqualityId => "equality_id",
            Self::StructureId => "structure_id",
            Self::CarrierId => "carrier_id",
            Self::ImportModule => "import_module",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LemmaGeneralizationError {
    EmptyIdentifier {
        field: LemmaGeneralizationField,
    },
    DuplicateLocal {
        local_id: String,
    },
    UnknownLocalDependency {
        local_id: String,
        dependency_local_id: String,
    },
    DependencyCycle {
        local_ids: Vec<String>,
    },
    MissingTypecheckWitness {
        generalized_statement_hash: Hash,
    },
    TypecheckWitnessMismatch {
        expected: Hash,
        actual: Hash,
    },
    ReportHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    DependencyOrderViolation {
        local_id: String,
        dependency_local_id: String,
    },
    OverGeneralization {
        reason: StatementNormalizationRejectionReason,
        item_id: String,
    },
}

impl LemmaGeneralizationError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::DuplicateLocal { .. } => "duplicate_local",
            Self::UnknownLocalDependency { .. } => "unknown_local_dependency",
            Self::DependencyCycle { .. } => "dependency_cycle",
            Self::MissingTypecheckWitness { .. } => "missing_typecheck_witness",
            Self::TypecheckWitnessMismatch { .. } => "typecheck_witness_mismatch",
            Self::ReportHashMismatch { .. } => "report_hash_mismatch",
            Self::DependencyOrderViolation { .. } => "dependency_order_violation",
            Self::OverGeneralization { .. } => "over_generalization",
        }
    }
}

impl fmt::Display for LemmaGeneralizationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for LemmaGeneralizationError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LibraryGrowthStage {
    AuthoringStage,
    PromotionCandidate,
}

impl LibraryGrowthStage {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AuthoringStage => "authoring_stage",
            Self::PromotionCandidate => "promotion_candidate",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LibraryReuseDuplicateStatus {
    Unique,
    CompatibilityAlias,
    Duplicate,
    Unknown,
}

impl LibraryReuseDuplicateStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unique => "unique",
            Self::CompatibilityAlias => "compatibility_alias",
            Self::Duplicate => "duplicate",
            Self::Unknown => "unknown",
        }
    }

    pub const fn blocks_public_readiness(self) -> bool {
        matches!(self, Self::Duplicate | Self::Unknown)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LibraryGrowthRecommendation {
    AuthoringUseful,
    PromotionReviewRequired,
    Defer,
}

impl LibraryGrowthRecommendation {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AuthoringUseful => "authoring_useful",
            Self::PromotionReviewRequired => "promotion_review_required",
            Self::Defer => "defer",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LibraryGrowthBudgetFailureKind {
    WidenedAxiomPolicy,
    ExcessiveImportClosure,
    AxiomCost,
    DuplicateStatus,
    UnknownTheoremLevel,
    NonL2TheoremLevel,
    CertificateGrowth,
    EnvironmentGrowth,
    IndexEntryGrowth,
    PremiseSearchLatency,
}

impl LibraryGrowthBudgetFailureKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::WidenedAxiomPolicy => "widened_axiom_policy",
            Self::ExcessiveImportClosure => "excessive_import_closure",
            Self::AxiomCost => "axiom_cost",
            Self::DuplicateStatus => "duplicate_status",
            Self::UnknownTheoremLevel => "unknown_theorem_level",
            Self::NonL2TheoremLevel => "non_l2_theorem_level",
            Self::CertificateGrowth => "certificate_growth",
            Self::EnvironmentGrowth => "environment_growth",
            Self::IndexEntryGrowth => "index_entry_growth",
            Self::PremiseSearchLatency => "premise_search_latency",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LibraryReuseScoreField {
    CandidateId,
    TargetModule,
    DeclarationName,
    BudgetHash,
    ReportHash,
}

impl LibraryReuseScoreField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CandidateId => "candidate_id",
            Self::TargetModule => "target_module",
            Self::DeclarationName => "declaration_name",
            Self::BudgetHash => "budget_hash",
            Self::ReportHash => "report_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryReuseScoreInput {
    pub candidate_id: String,
    pub target_module: String,
    pub declaration_name: String,
    pub theorem_level: TheoremLevel,
    pub stage: LibraryGrowthStage,
    pub downstream_unlock_count: u64,
    pub repeated_parent_goal_count: u64,
    pub proof_shortening_nodes: u64,
    pub statement_stability_score: u64,
    pub import_closure_added_modules: u64,
    pub axiom_cost: u64,
    pub proof_difficulty_score: u64,
    pub certificate_growth_bytes: u64,
    pub environment_growth_entries: u64,
    pub index_entry_growth: u64,
    pub premise_search_latency_delta_ms: u64,
    pub axiom_policy_widened: bool,
    pub duplicate_status: LibraryReuseDuplicateStatus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryGrowthBudget {
    pub budget_hash: Hash,
    pub max_import_closure_added_modules: u64,
    pub max_axiom_cost: u64,
    pub max_certificate_growth_bytes: u64,
    pub max_environment_growth_entries: u64,
    pub max_index_entry_growth: u64,
    pub max_premise_search_latency_delta_ms: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryReuseScoreBreakdown {
    pub downstream_unlock_score: u64,
    pub repeated_parent_goal_score: u64,
    pub proof_shortening_score: u64,
    pub statement_stability_score: u64,
    pub proof_difficulty_score: u64,
    pub import_closure_penalty: u64,
    pub axiom_cost_penalty: u64,
    pub certificate_growth_penalty: u64,
    pub environment_growth_penalty: u64,
    pub index_entry_growth_penalty: u64,
    pub premise_search_latency_penalty: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryGrowthBudgetFailure {
    pub kind: LibraryGrowthBudgetFailureKind,
    pub actual: u64,
    pub limit: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryReuseScoreReport {
    pub report_hash: Hash,
    pub input_hash: Hash,
    pub budget_hash: Hash,
    pub candidate_id: String,
    pub target_module: String,
    pub declaration_name: String,
    pub theorem_level: TheoremLevel,
    pub stage: LibraryGrowthStage,
    pub score_is_untrusted: bool,
    pub public_promotion_allowed_by_score: bool,
    pub authoring_usefulness_score: u64,
    pub public_readiness_score: u64,
    pub score_breakdown: LibraryReuseScoreBreakdown,
    pub budget_failures: Vec<LibraryGrowthBudgetFailure>,
    pub authoring_recommendation: LibraryGrowthRecommendation,
    pub public_package_recommendation: LibraryGrowthRecommendation,
    pub public_package_ready_for_review: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LibraryReuseScoreError {
    EmptyIdentifier { field: LibraryReuseScoreField },
    BudgetHashMismatch { expected: Hash, actual: Hash },
    ReportHashMismatch { expected: Hash, actual: Hash },
}

impl LibraryReuseScoreError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::BudgetHashMismatch { .. } => "budget_hash_mismatch",
            Self::ReportHashMismatch { .. } => "report_hash_mismatch",
        }
    }
}

impl fmt::Display for LibraryReuseScoreError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for LibraryReuseScoreError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateNamespace {
    StagedCorpus,
    PublicMathlib,
}

impl TheoremDuplicateNamespace {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StagedCorpus => "staged_corpus",
            Self::PublicMathlib => "public_mathlib",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateReviewStage {
    StatementHash,
    AlphaEquivalence,
    ReducibleNormalization,
    MutualImplication,
    HumanReviewQueue,
}

impl TheoremDuplicateReviewStage {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StatementHash => "statement_hash",
            Self::AlphaEquivalence => "alpha_equivalence",
            Self::ReducibleNormalization => "reducible_normalization",
            Self::MutualImplication => "mutual_implication",
            Self::HumanReviewQueue => "human_review_queue",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateRelationKind {
    ExactStatementHash,
    AlphaEquivalent,
    ReduciblyEqual,
    MutualImplicationEquivalent,
    ProposedStronger,
    ProposedWeaker,
    Inconclusive,
}

impl TheoremDuplicateRelationKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExactStatementHash => "exact_statement_hash",
            Self::AlphaEquivalent => "alpha_equivalent",
            Self::ReduciblyEqual => "reducibly_equal",
            Self::MutualImplicationEquivalent => "mutual_implication_equivalent",
            Self::ProposedStronger => "proposed_stronger",
            Self::ProposedWeaker => "proposed_weaker",
            Self::Inconclusive => "inconclusive",
        }
    }

    pub const fn is_duplicate(self) -> bool {
        matches!(
            self,
            Self::ExactStatementHash
                | Self::AlphaEquivalent
                | Self::ReduciblyEqual
                | Self::MutualImplicationEquivalent
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateRecommendedAction {
    RejectBeforeProofTask,
    CompatibilityAliasReview,
    ReviewSubsumption,
    KeepStaged,
}

impl TheoremDuplicateRecommendedAction {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RejectBeforeProofTask => "reject_before_proof_task",
            Self::CompatibilityAliasReview => "compatibility_alias_review",
            Self::ReviewSubsumption => "review_subsumption",
            Self::KeepStaged => "keep_staged",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateCostOrdering {
    ExistingLower,
    ProposedLower,
    Equal,
}

impl TheoremDuplicateCostOrdering {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExistingLower => "existing_lower",
            Self::ProposedLower => "proposed_lower",
            Self::Equal => "equal",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateAxiomPolicyRelation {
    Same,
    ProposedWidens,
    ProposedNarrows,
    ChangedUnknown,
}

impl TheoremDuplicateAxiomPolicyRelation {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Same => "same",
            Self::ProposedWidens => "proposed_widens",
            Self::ProposedNarrows => "proposed_narrows",
            Self::ChangedUnknown => "changed_unknown",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremDuplicateField {
    Module,
    DeclarationName,
    ExistingModule,
    ExistingDeclarationName,
    ProposedModule,
    ProposedDeclarationName,
    NormalizedStatement,
    SkippedReason,
    ReportHash,
}

impl TheoremDuplicateField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Module => "module",
            Self::DeclarationName => "declaration_name",
            Self::ExistingModule => "existing_module",
            Self::ExistingDeclarationName => "existing_declaration_name",
            Self::ProposedModule => "proposed_module",
            Self::ProposedDeclarationName => "proposed_declaration_name",
            Self::NormalizedStatement => "normalized_statement",
            Self::SkippedReason => "skipped_reason",
            Self::ReportHash => "report_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremDuplicateIdentity {
    pub namespace: TheoremDuplicateNamespace,
    pub module: String,
    pub declaration_name: String,
    pub theorem_level: TheoremLevel,
    pub normalized_statement: String,
    pub statement_hash: Hash,
    pub alpha_equivalence_hash: Hash,
    pub reducible_normal_form_hash: Option<Hash>,
    pub import_closure_modules: Vec<String>,
    pub axiom_policy_hash: Hash,
    pub axiom_cost: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremDuplicateMutualImplicationEvidence {
    pub existing_implies_proposed: Option<bool>,
    pub proposed_implies_existing: Option<bool>,
    pub skipped_reason: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremDuplicateImportCostComparison {
    pub existing_import_closure_modules: u64,
    pub proposed_import_closure_modules: u64,
    pub proposed_only_import_modules: Vec<String>,
    pub existing_only_import_modules: Vec<String>,
    pub ordering: TheoremDuplicateCostOrdering,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremDuplicateAxiomPolicyComparison {
    pub existing_axiom_policy_hash: Hash,
    pub proposed_axiom_policy_hash: Hash,
    pub existing_axiom_cost: u64,
    pub proposed_axiom_cost: u64,
    pub relation: TheoremDuplicateAxiomPolicyRelation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremDuplicateReviewReport {
    pub report_hash: Hash,
    pub existing_identity_hash: Hash,
    pub proposed_identity_hash: Hash,
    pub existing: TheoremDuplicateIdentity,
    pub proposed: TheoremDuplicateIdentity,
    pub review_stages: Vec<TheoremDuplicateReviewStage>,
    pub relation_kind: TheoremDuplicateRelationKind,
    pub import_cost_comparison: TheoremDuplicateImportCostComparison,
    pub axiom_policy_comparison: TheoremDuplicateAxiomPolicyComparison,
    pub mutual_implication_skipped_reason: Option<String>,
    pub compatibility_alias_marked: bool,
    pub recommended_action: TheoremDuplicateRecommendedAction,
    pub proof_task_creation_blocked: bool,
    pub public_promotion_blocked: bool,
    pub public_promotion_allowed_by_report: bool,
    pub handles_staged_and_public_identities_separately: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoremDuplicateReviewError {
    EmptyIdentifier {
        field: TheoremDuplicateField,
    },
    SameTheoremIdentity {
        module: String,
        declaration_name: String,
    },
    ReportHashMismatch {
        expected: Hash,
        actual: Hash,
    },
}

impl TheoremDuplicateReviewError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::SameTheoremIdentity { .. } => "same_theorem_identity",
            Self::ReportHashMismatch { .. } => "report_hash_mismatch",
        }
    }
}

impl fmt::Display for TheoremDuplicateReviewError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for TheoremDuplicateReviewError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionJudgmentDecision {
    Promote,
    Defer,
    RejectForNow,
}

impl PromotionJudgmentDecision {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Promote => "promote",
            Self::Defer => "defer",
            Self::RejectForNow => "reject_for_now",
        }
    }

    pub const fn audit_label(self) -> &'static str {
        match self {
            Self::Promote => "Promote",
            Self::Defer => "Defer",
            Self::RejectForNow => "Reject for now",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionJudgmentReasonKind {
    NonL2TheoremLevel,
    UnknownTheoremLevel,
    ConclusionAssuming,
    StaleArtifact,
    UnresolvedImport,
    WidenedAxiomPolicy,
    Duplicate,
    UnresolvedCompatibility,
    MissingClosureAudit,
    MissingTheoremCard,
    MissingSourceFreeVerification,
    MissingImportClosure,
    MissingAxiomPolicy,
    MissingNamingReview,
    MissingApiReview,
    MissingDownstreamPlan,
    MissingPromotionRunbook,
    PromotionIntentNotReady,
    BudgetFailure,
    InsufficientReuse,
    UnstableStatement,
    DuplicateReviewIncomplete,
    ReuseScoreNotReady,
}

impl PromotionJudgmentReasonKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NonL2TheoremLevel => "non_l2_theorem_level",
            Self::UnknownTheoremLevel => "unknown_theorem_level",
            Self::ConclusionAssuming => "conclusion_assuming",
            Self::StaleArtifact => "stale_artifact",
            Self::UnresolvedImport => "unresolved_import",
            Self::WidenedAxiomPolicy => "widened_axiom_policy",
            Self::Duplicate => "duplicate",
            Self::UnresolvedCompatibility => "unresolved_compatibility",
            Self::MissingClosureAudit => "missing_closure_audit",
            Self::MissingTheoremCard => "missing_theorem_card",
            Self::MissingSourceFreeVerification => "missing_source_free_verification",
            Self::MissingImportClosure => "missing_import_closure",
            Self::MissingAxiomPolicy => "missing_axiom_policy",
            Self::MissingNamingReview => "missing_naming_review",
            Self::MissingApiReview => "missing_api_review",
            Self::MissingDownstreamPlan => "missing_downstream_plan",
            Self::MissingPromotionRunbook => "missing_promotion_runbook",
            Self::PromotionIntentNotReady => "promotion_intent_not_ready",
            Self::BudgetFailure => "budget_failure",
            Self::InsufficientReuse => "insufficient_reuse",
            Self::UnstableStatement => "unstable_statement",
            Self::DuplicateReviewIncomplete => "duplicate_review_incomplete",
            Self::ReuseScoreNotReady => "reuse_score_not_ready",
        }
    }

    pub const fn is_hard_rejection(self) -> bool {
        matches!(
            self,
            Self::NonL2TheoremLevel
                | Self::UnknownTheoremLevel
                | Self::ConclusionAssuming
                | Self::StaleArtifact
                | Self::UnresolvedImport
                | Self::WidenedAxiomPolicy
                | Self::Duplicate
                | Self::UnresolvedCompatibility
                | Self::MissingClosureAudit
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionJudgmentReason {
    pub kind: PromotionJudgmentReasonKind,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionJudgmentInput {
    pub candidate_id: String,
    pub theorem_card_hash: Option<Hash>,
    pub artifact: TheoremInventionArtifact,
    pub reuse_score_report: LibraryReuseScoreReport,
    pub duplicate_review_report: Option<TheoremDuplicateReviewReport>,
    pub closure_audit_hash: Option<Hash>,
    pub source_free_verification_hash: Option<Hash>,
    pub import_closure_hash: Option<Hash>,
    pub axiom_policy_hash: Option<Hash>,
    pub axiom_report_hash: Option<Hash>,
    pub naming_review_hash: Option<Hash>,
    pub api_review_hash: Option<Hash>,
    pub compatibility_decision_hash: Option<Hash>,
    pub downstream_plan_hash: Option<Hash>,
    pub promotion_runbook_hash: Option<Hash>,
    pub unresolved_imports: Vec<String>,
    pub statement_stability_confirmed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionJudgmentReport {
    pub report_hash: Hash,
    pub input_hash: Hash,
    pub candidate_id: String,
    pub target_module: String,
    pub declaration_name: String,
    pub theorem_level: TheoremLevel,
    pub decision: PromotionJudgmentDecision,
    pub hard_rejection_reasons: Vec<PromotionJudgmentReason>,
    pub defer_reasons: Vec<PromotionJudgmentReason>,
    pub public_promotion_allowed: bool,
    pub staged_artifact_preserved: bool,
    pub audit_text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionJudgmentField {
    CandidateId,
    TargetModule,
    DeclarationName,
    TheoremLevel,
    StatementHash,
    UnresolvedImport,
    ArtifactIdentityHash,
    GeneralizedContextHash,
    VerificationCommandHash,
    ReuseScoreReportHash,
    DuplicateReviewReportHash,
    ReportHash,
}

impl PromotionJudgmentField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CandidateId => "candidate_id",
            Self::TargetModule => "target_module",
            Self::DeclarationName => "declaration_name",
            Self::TheoremLevel => "theorem_level",
            Self::StatementHash => "statement_hash",
            Self::UnresolvedImport => "unresolved_import",
            Self::ArtifactIdentityHash => "artifact_identity_hash",
            Self::GeneralizedContextHash => "generalized_context_hash",
            Self::VerificationCommandHash => "verification_command_hash",
            Self::ReuseScoreReportHash => "reuse_score_report_hash",
            Self::DuplicateReviewReportHash => "duplicate_review_report_hash",
            Self::ReportHash => "report_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PromotionJudgmentError {
    EmptyIdentifier {
        field: PromotionJudgmentField,
    },
    HashMismatch {
        field: PromotionJudgmentField,
        expected: Hash,
        actual: Hash,
    },
    InputMismatch {
        field: PromotionJudgmentField,
        expected: String,
        actual: String,
    },
    ReportHashMismatch {
        expected: Hash,
        actual: Hash,
    },
}

impl PromotionJudgmentError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::InputMismatch { .. } => "input_mismatch",
            Self::ReportHashMismatch { .. } => "report_hash_mismatch",
        }
    }
}

impl fmt::Display for PromotionJudgmentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for PromotionJudgmentError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionMetadataReviewPhase {
    PreMaterialization,
    PostMaterialization,
}

impl PromotionMetadataReviewPhase {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PreMaterialization => "pre_materialization",
            Self::PostMaterialization => "post_materialization",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataFileEvidence {
    pub path: String,
    pub hash: Option<Hash>,
    pub stale: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataVerificationEvidence {
    pub command: String,
    pub command_hash: Option<Hash>,
    pub stale: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataImportClosureEntry {
    pub module: String,
    pub certificate: PromotionMetadataFileEvidence,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataTheoremIndexEntry {
    pub module: String,
    pub declaration_name: String,
    pub theorem_level: TheoremLevel,
    pub certificate_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataTheoremIndexEvidence {
    pub file: PromotionMetadataFileEvidence,
    pub entries: Vec<PromotionMetadataTheoremIndexEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataPublishPlanEntry {
    pub module: String,
    pub release_target: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataPublishPlanEvidence {
    pub file: PromotionMetadataFileEvidence,
    pub entries: Vec<PromotionMetadataPublishPlanEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadata {
    pub metadata_hash: Hash,
    pub review_phase: PromotionMetadataReviewPhase,
    pub candidate_id: String,
    pub theorem_card: PromotionMetadataFileEvidence,
    pub staged_theorem_level: TheoremLevel,
    pub theorem_card_level: TheoremLevel,
    pub source_module: String,
    pub source_declaration_name: String,
    pub target_mathlib_module: String,
    pub target_declaration_name: String,
    pub source_free_verification: PromotionMetadataVerificationEvidence,
    pub certificate: PromotionMetadataFileEvidence,
    pub import_closure: Vec<PromotionMetadataImportClosureEntry>,
    pub axiom_policy_hash: Option<Hash>,
    pub axiom_report: PromotionMetadataFileEvidence,
    pub reuse_evidence_hash: Option<Hash>,
    pub duplicate_review_hash: Option<Hash>,
    pub compatibility_decision_hash: Option<Hash>,
    pub downstream_plan_hash: Option<Hash>,
    pub closure_audit: PromotionMetadataFileEvidence,
    pub theorem_index: PromotionMetadataTheoremIndexEvidence,
    pub publish_plan: PromotionMetadataPublishPlanEvidence,
    pub release_target: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionMetadataField {
    MetadataHash,
    ReportHash,
    CandidateId,
    TheoremCard,
    StagedTheoremLevel,
    TheoremCardLevel,
    SourceModule,
    SourceDeclarationName,
    TargetMathlibModule,
    TargetDeclarationName,
    SourceFreeVerificationCommand,
    SourceFreeVerificationCommandHash,
    Certificate,
    CertificateHash,
    ImportClosure,
    ImportClosureModule,
    ImportClosureCertificate,
    ImportClosureCertificateHash,
    AxiomPolicyHash,
    AxiomReport,
    AxiomReportHash,
    ReuseEvidenceHash,
    DuplicateReviewHash,
    CompatibilityDecisionHash,
    DownstreamPlanHash,
    ClosureAudit,
    ClosureAuditHash,
    TheoremIndex,
    TheoremIndexHash,
    TheoremIndexEntry,
    PublishPlan,
    PublishPlanHash,
    PublishPlanEntry,
    ReleaseTarget,
}

impl PromotionMetadataField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MetadataHash => "metadata_hash",
            Self::ReportHash => "report_hash",
            Self::CandidateId => "candidate_id",
            Self::TheoremCard => "theorem_card",
            Self::StagedTheoremLevel => "staged_theorem_level",
            Self::TheoremCardLevel => "theorem_card_level",
            Self::SourceModule => "source_module",
            Self::SourceDeclarationName => "source_declaration_name",
            Self::TargetMathlibModule => "target_mathlib_module",
            Self::TargetDeclarationName => "target_declaration_name",
            Self::SourceFreeVerificationCommand => "source_free_verification_command",
            Self::SourceFreeVerificationCommandHash => "source_free_verification_command_hash",
            Self::Certificate => "certificate",
            Self::CertificateHash => "certificate_hash",
            Self::ImportClosure => "import_closure",
            Self::ImportClosureModule => "import_closure_module",
            Self::ImportClosureCertificate => "import_closure_certificate",
            Self::ImportClosureCertificateHash => "import_closure_certificate_hash",
            Self::AxiomPolicyHash => "axiom_policy_hash",
            Self::AxiomReport => "axiom_report",
            Self::AxiomReportHash => "axiom_report_hash",
            Self::ReuseEvidenceHash => "reuse_evidence_hash",
            Self::DuplicateReviewHash => "duplicate_review_hash",
            Self::CompatibilityDecisionHash => "compatibility_decision_hash",
            Self::DownstreamPlanHash => "downstream_plan_hash",
            Self::ClosureAudit => "closure_audit",
            Self::ClosureAuditHash => "closure_audit_hash",
            Self::TheoremIndex => "theorem_index",
            Self::TheoremIndexHash => "theorem_index_hash",
            Self::TheoremIndexEntry => "theorem_index_entry",
            Self::PublishPlan => "publish_plan",
            Self::PublishPlanHash => "publish_plan_hash",
            Self::PublishPlanEntry => "publish_plan_entry",
            Self::ReleaseTarget => "release_target",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionMetadataIssueKind {
    EmptyIdentifier,
    InvalidTargetModule,
    InvalidStagedTheoremLevel,
    TheoremCardLevelMismatch,
    MissingHash,
    StaleEvidence,
    MissingImportClosure,
    MissingAxiomReport,
    MissingTheoremIndexEntry,
    MissingPublishPlanEntry,
}

impl PromotionMetadataIssueKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::EmptyIdentifier => "empty_identifier",
            Self::InvalidTargetModule => "invalid_target_module",
            Self::InvalidStagedTheoremLevel => "invalid_staged_theorem_level",
            Self::TheoremCardLevelMismatch => "theorem_card_level_mismatch",
            Self::MissingHash => "missing_hash",
            Self::StaleEvidence => "stale_evidence",
            Self::MissingImportClosure => "missing_import_closure",
            Self::MissingAxiomReport => "missing_axiom_report",
            Self::MissingTheoremIndexEntry => "missing_theorem_index_entry",
            Self::MissingPublishPlanEntry => "missing_publish_plan_entry",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataIssue {
    pub kind: PromotionMetadataIssueKind,
    pub field: PromotionMetadataField,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionMetadataConsistencyReport {
    pub report_hash: Hash,
    pub metadata_hash: Hash,
    pub candidate_id: String,
    pub review_phase: PromotionMetadataReviewPhase,
    pub source_module: String,
    pub target_mathlib_module: String,
    pub target_declaration_name: String,
    pub theorem_card_level: TheoremLevel,
    pub promotion_blocked: bool,
    pub reviewable_before_materialization: bool,
    pub rechecked_after_materialization: bool,
    pub source_free_package_verification_compatible: bool,
    pub issues: Vec<PromotionMetadataIssue>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PromotionMetadataError {
    HashMismatch {
        field: PromotionMetadataField,
        expected: Hash,
        actual: Hash,
    },
    ReportMismatch {
        expected: Hash,
        actual: Hash,
    },
}

impl PromotionMetadataError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::ReportMismatch { .. } => "report_mismatch",
        }
    }
}

impl fmt::Display for PromotionMetadataError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for PromotionMetadataError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionRankingProfile {
    pub profile_hash: Hash,
    pub reuse_weight: u64,
    pub foundational_value_weight: u64,
    pub statement_stability_weight: u64,
    pub release_readiness_weight: u64,
    pub import_cost_weight: u64,
    pub axiom_cost_weight: u64,
    pub duplicate_subsumption_risk_weight: u64,
    pub downstream_migration_cost_weight: u64,
    pub package_growth_weight: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionRankingCandidateInput {
    pub candidate_id: String,
    pub reuse_score_report: LibraryReuseScoreReport,
    pub duplicate_review_report: Option<TheoremDuplicateReviewReport>,
    pub promotion_judgment_report: PromotionJudgmentReport,
    pub promotion_metadata_report: PromotionMetadataConsistencyReport,
    pub import_closure_hash: Option<Hash>,
    pub axiom_report_hash: Option<Hash>,
    pub performance_budget_report_hash: Option<Hash>,
    pub theorem_card_metadata_hash: Option<Hash>,
    pub downstream_plan_hash: Option<Hash>,
    pub foundational_value_score: u64,
    pub downstream_migration_cost: u64,
    pub release_readiness_score: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionRankingEvidenceHashes {
    pub reuse_score_report_hash: Hash,
    pub duplicate_review_report_hash: Option<Hash>,
    pub promotion_judgment_report_hash: Hash,
    pub promotion_metadata_report_hash: Hash,
    pub import_closure_hash: Option<Hash>,
    pub axiom_report_hash: Option<Hash>,
    pub performance_budget_report_hash: Option<Hash>,
    pub theorem_card_metadata_hash: Option<Hash>,
    pub downstream_plan_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionRankingEntry {
    pub rank: u64,
    pub ranking_identity_hash: Hash,
    pub candidate_id: String,
    pub target_module: String,
    pub declaration_name: String,
    pub theorem_level: TheoremLevel,
    pub decision: PromotionJudgmentDecision,
    pub decision_label: String,
    pub hard_rejection_dominates_numeric_rank: bool,
    pub numeric_score: u64,
    pub reuse_score: u64,
    pub foundational_value_score: u64,
    pub statement_stability_score: u64,
    pub release_readiness_score: u64,
    pub import_cost_penalty: u64,
    pub axiom_cost_penalty: u64,
    pub duplicate_subsumption_risk_penalty: u64,
    pub downstream_migration_cost_penalty: u64,
    pub package_growth_penalty: u64,
    pub package_growth_budget_failures: Vec<LibraryGrowthBudgetFailure>,
    pub hard_rejection_reasons: Vec<PromotionJudgmentReason>,
    pub defer_reasons: Vec<PromotionJudgmentReason>,
    pub metadata_issues: Vec<PromotionMetadataIssue>,
    pub evidence_hashes: PromotionRankingEvidenceHashes,
    pub rank_explanation: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionRankingReport {
    pub report_hash: Hash,
    pub profile_hash: Hash,
    pub operator_aid_only: bool,
    pub entries: Vec<PromotionRankingEntry>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PromotionRankingField {
    CandidateId,
    ProfileHash,
    ReportHash,
    ReuseScoreReportHash,
    DuplicateReviewReportHash,
    PromotionJudgmentReportHash,
    PromotionMetadataReportHash,
}

impl PromotionRankingField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CandidateId => "candidate_id",
            Self::ProfileHash => "profile_hash",
            Self::ReportHash => "report_hash",
            Self::ReuseScoreReportHash => "reuse_score_report_hash",
            Self::DuplicateReviewReportHash => "duplicate_review_report_hash",
            Self::PromotionJudgmentReportHash => "promotion_judgment_report_hash",
            Self::PromotionMetadataReportHash => "promotion_metadata_report_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PromotionRankingError {
    EmptyIdentifier {
        field: PromotionRankingField,
    },
    HashMismatch {
        field: PromotionRankingField,
        expected: Hash,
        actual: Hash,
    },
    InputMismatch {
        field: PromotionRankingField,
        expected: String,
        actual: String,
    },
}

impl PromotionRankingError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::InputMismatch { .. } => "input_mismatch",
        }
    }
}

impl fmt::Display for PromotionRankingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for PromotionRankingError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorpusAliasScope {
    LocalCorpusAlias,
    PublicPackageCompatibilityAlias,
}

impl CorpusAliasScope {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LocalCorpusAlias => "local_corpus_alias",
            Self::PublicPackageCompatibilityAlias => "public_package_compatibility_alias",
        }
    }

    pub const fn requires_public_compatibility_decision(self) -> bool {
        matches!(self, Self::PublicPackageCompatibilityAlias)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorpusMigrationEvidenceKind {
    MigrationProof,
    LocalAlias,
    PublicCompatibilityAlias,
}

impl CorpusMigrationEvidenceKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MigrationProof => "migration_proof",
            Self::LocalAlias => "local_alias",
            Self::PublicCompatibilityAlias => "public_compatibility_alias",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorpusCertificateCompatibility {
    ReplacementCertificateVerified,
    CompatibilityAliasVerified,
    CompatibilityDecisionRequired,
    Incompatible,
}

impl CorpusCertificateCompatibility {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReplacementCertificateVerified => "replacement_certificate_verified",
            Self::CompatibilityAliasVerified => "compatibility_alias_verified",
            Self::CompatibilityDecisionRequired => "compatibility_decision_required",
            Self::Incompatible => "incompatible",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorpusPublicTheoremAction {
    PreservePublicTheorem,
    ProposeCompatibilityAlias,
    RemoveOrRewritePublicTheorem,
}

impl CorpusPublicTheoremAction {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PreservePublicTheorem => "preserve_public_theorem",
            Self::ProposeCompatibilityAlias => "propose_compatibility_alias",
            Self::RemoveOrRewritePublicTheorem => "remove_or_rewrite_public_theorem",
        }
    }

    pub const fn requires_public_compatibility_decision(self) -> bool {
        matches!(
            self,
            Self::ProposeCompatibilityAlias | Self::RemoveOrRewritePublicTheorem
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PublicCompatibilityAction {
    PreservePublicName,
    AddCompatibilityAlias,
    DeprecateAlias,
    RemoveOrRewriteAtRemovalVersion,
}

impl PublicCompatibilityAction {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PreservePublicName => "preserve_public_name",
            Self::AddCompatibilityAlias => "add_compatibility_alias",
            Self::DeprecateAlias => "deprecate_alias",
            Self::RemoveOrRewriteAtRemovalVersion => "remove_or_rewrite_at_removal_version",
        }
    }

    pub const fn requires_alias(self) -> bool {
        matches!(self, Self::AddCompatibilityAlias | Self::DeprecateAlias)
    }

    pub const fn requires_removal_version(self) -> bool {
        matches!(
            self,
            Self::DeprecateAlias | Self::RemoveOrRewriteAtRemovalVersion
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorpusReplacementVerificationEvidence {
    pub replacement_theorem_level: TheoremLevel,
    pub source_free_status: ProofAcceptanceState,
    pub replacement_statement_hash: Hash,
    pub verified_statement_hash: Hash,
    pub replacement_certificate_hash: Hash,
    pub verified_certificate_hash: Hash,
    pub source_free_verification_hash: Hash,
    pub axiom_policy_hash: Hash,
    pub stale_artifact: bool,
    pub axiom_policy_widened: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorpusDownstreamUsage {
    pub module: String,
    pub declaration_name: String,
    pub usage_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorpusTheoremIndexHistoryEntry {
    pub module: String,
    pub declaration_name: String,
    pub statement_hash: Hash,
    pub theorem_index_hash: Hash,
    pub deprecated: bool,
    pub preferred_retrieval: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorpusAliasProposalMetadata {
    pub proposal_hash: Hash,
    pub alias_scope: CorpusAliasScope,
    pub migration_evidence_kind: CorpusMigrationEvidenceKind,
    pub alias_module: String,
    pub alias_declaration_name: String,
    pub replacement_module: String,
    pub replacement_declaration_name: String,
    pub replacement_statement_hash: Hash,
    pub migration_evidence_hash: Option<Hash>,
    pub downstream_usages: Vec<CorpusDownstreamUsage>,
    pub verification: CorpusReplacementVerificationEvidence,
    pub public_compatibility_decision_hash: Option<Hash>,
    pub risk_note: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicCompatibilityDecisionRecord {
    pub decision_hash: Hash,
    pub action: PublicCompatibilityAction,
    pub public_module: String,
    pub public_declaration_name: String,
    pub replacement_module: String,
    pub replacement_declaration_name: String,
    pub replacement_statement_hash: Hash,
    pub alias_module: Option<String>,
    pub alias_declaration_name: Option<String>,
    pub intended_removal_version: Option<String>,
    pub certificate_compatibility: CorpusCertificateCompatibility,
    pub theorem_index_history: Vec<CorpusTheoremIndexHistoryEntry>,
    pub downstream_usages: Vec<CorpusDownstreamUsage>,
    pub replacement_verification: CorpusReplacementVerificationEvidence,
    pub risk_note: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorpusDeprecationRecord {
    pub record_hash: Hash,
    pub deprecated_module: String,
    pub deprecated_declaration_name: String,
    pub deprecated_statement_hash: Hash,
    pub replacement_module: String,
    pub replacement_declaration_name: String,
    pub replacement_statement_hash: Hash,
    pub migration_evidence_hash: Option<Hash>,
    pub alias_proposal: CorpusAliasProposalMetadata,
    pub downstream_usages: Vec<CorpusDownstreamUsage>,
    pub intended_removal_version: String,
    pub certificate_compatibility: CorpusCertificateCompatibility,
    pub theorem_index_history: Vec<CorpusTheoremIndexHistoryEntry>,
    pub risk_note: String,
    pub public_action: CorpusPublicTheoremAction,
    pub public_compatibility_decision_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorpusDeprecatedTheoremIndexEntry {
    pub entry_hash: Hash,
    pub module: String,
    pub declaration_name: String,
    pub statement_hash: Hash,
    pub deprecated: bool,
    pub replacement_module: Option<String>,
    pub replacement_declaration_name: Option<String>,
    pub replacement_statement_hash: Option<Hash>,
    pub preferred_retrieval: bool,
    pub theorem_index_history_hash: Hash,
    pub alias_scope: Option<CorpusAliasScope>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorpusDeprecationField {
    RecordHash,
    ProposalHash,
    PublicCompatibilityDecisionHash,
    PublicCompatibilityAction,
    PublicModule,
    PublicDeclarationName,
    TheoremIndexEntryHash,
    DeprecatedModule,
    DeprecatedDeclarationName,
    ReplacementModule,
    ReplacementDeclarationName,
    AliasModule,
    AliasDeclarationName,
    AliasScope,
    MigrationEvidenceKind,
    DownstreamModule,
    DownstreamDeclarationName,
    HistoryModule,
    HistoryDeclarationName,
    IntendedRemovalVersion,
    RiskNote,
}

impl CorpusDeprecationField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RecordHash => "record_hash",
            Self::ProposalHash => "proposal_hash",
            Self::PublicCompatibilityDecisionHash => "public_compatibility_decision_hash",
            Self::PublicCompatibilityAction => "public_compatibility_action",
            Self::PublicModule => "public_module",
            Self::PublicDeclarationName => "public_declaration_name",
            Self::TheoremIndexEntryHash => "theorem_index_entry_hash",
            Self::DeprecatedModule => "deprecated_module",
            Self::DeprecatedDeclarationName => "deprecated_declaration_name",
            Self::ReplacementModule => "replacement_module",
            Self::ReplacementDeclarationName => "replacement_declaration_name",
            Self::AliasModule => "alias_module",
            Self::AliasDeclarationName => "alias_declaration_name",
            Self::AliasScope => "alias_scope",
            Self::MigrationEvidenceKind => "migration_evidence_kind",
            Self::DownstreamModule => "downstream_module",
            Self::DownstreamDeclarationName => "downstream_declaration_name",
            Self::HistoryModule => "history_module",
            Self::HistoryDeclarationName => "history_declaration_name",
            Self::IntendedRemovalVersion => "intended_removal_version",
            Self::RiskNote => "risk_note",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CorpusDeprecationError {
    EmptyIdentifier {
        field: CorpusDeprecationField,
    },
    HashMismatch {
        field: CorpusDeprecationField,
        expected: Hash,
        actual: Hash,
    },
    InputMismatch {
        field: CorpusDeprecationField,
        expected: String,
        actual: String,
    },
    MissingMigrationEvidence,
    MissingDownstreamUsage,
    MissingTheoremIndexHistory,
    ReplacementNotL2 {
        actual: TheoremLevel,
    },
    ReplacementNotSourceFreeVerified {
        actual: ProofAcceptanceState,
    },
    ReplacementStale,
    ReplacementStatementMismatch {
        expected: Hash,
        actual: Hash,
    },
    ReplacementCertificateMismatch {
        expected: Hash,
        actual: Hash,
    },
    AxiomPolicyWidened,
    IncompatibleCertificate,
    MissingCompatibilityAlias,
    MissingRemovalVersion,
    PublicCompatibilityDecisionMissing,
    PublicRewriteRequiresCompatibilityDecision,
    DeprecatedAliasPreferredRetrieval {
        module: String,
        declaration_name: String,
    },
    MissingDeprecatedAliasHistory {
        module: String,
        declaration_name: String,
    },
}

impl CorpusDeprecationError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::InputMismatch { .. } => "input_mismatch",
            Self::MissingMigrationEvidence => "missing_migration_evidence",
            Self::MissingDownstreamUsage => "missing_downstream_usage",
            Self::MissingTheoremIndexHistory => "missing_theorem_index_history",
            Self::ReplacementNotL2 { .. } => "replacement_not_l2",
            Self::ReplacementNotSourceFreeVerified { .. } => "replacement_not_source_free_verified",
            Self::ReplacementStale => "replacement_stale",
            Self::ReplacementStatementMismatch { .. } => "replacement_statement_mismatch",
            Self::ReplacementCertificateMismatch { .. } => "replacement_certificate_mismatch",
            Self::AxiomPolicyWidened => "axiom_policy_widened",
            Self::IncompatibleCertificate => "incompatible_certificate",
            Self::MissingCompatibilityAlias => "missing_compatibility_alias",
            Self::MissingRemovalVersion => "missing_removal_version",
            Self::PublicCompatibilityDecisionMissing => "public_compatibility_decision_missing",
            Self::PublicRewriteRequiresCompatibilityDecision => {
                "public_rewrite_requires_compatibility_decision"
            }
            Self::DeprecatedAliasPreferredRetrieval { .. } => {
                "deprecated_alias_preferred_retrieval"
            }
            Self::MissingDeprecatedAliasHistory { .. } => "missing_deprecated_alias_history",
        }
    }
}

impl fmt::Display for CorpusDeprecationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for CorpusDeprecationError {}

#[derive(Clone, Debug)]
struct SubgoalClusterAccumulator {
    key: SubgoalClusterKey,
    parent_examples: BTreeMap<Hash, SubgoalClusterParentExample>,
    gap_signals: BTreeMap<Hash, LibraryGapSignalObservation>,
    strategy_counts: BTreeMap<SubgoalClusterLikelyProofStrategy, u64>,
}

pub fn subgoal_cluster_identity_hash(key: &SubgoalClusterKey) -> Hash {
    let key = canonical_subgoal_cluster_key(key);
    let mut out = Vec::new();
    encode_string(&mut out, SUBGOAL_CLUSTER_KEY_PROFILE);
    encode_hash(&mut out, &key.normalized_target_hash);
    encode_uvar(&mut out, key.normalized_local_type_hashes.len() as u64);
    for local_type_hash in &key.normalized_local_type_hashes {
        encode_hash(&mut out, local_type_hash);
    }
    encode_uvar(&mut out, key.head_symbols.len() as u64);
    for head_symbol in &key.head_symbols {
        encode_string(&mut out, head_symbol);
    }
    encode_hash(&mut out, &key.universe_erased_shape_hash);
    encode_uvar(
        &mut out,
        key.approved_commutative_canonicalizations.len() as u64,
    );
    for canonicalization in &key.approved_commutative_canonicalizations {
        encode_string(&mut out, &canonicalization.operator_symbol);
        encode_uvar(&mut out, canonicalization.operand_hashes.len() as u64);
        for operand_hash in &canonicalization.operand_hashes {
            encode_hash(&mut out, operand_hash);
        }
    }
    encode_uvar(&mut out, key.domain_tags.len() as u64);
    for domain_tag in &key.domain_tags {
        encode_string(&mut out, domain_tag);
    }
    hash_with_domain("npa.library-growth.subgoal-cluster-key.hash.v1", &out)
}

pub fn subgoal_cluster_local_context_hash(normalized_local_type_hashes: &[Hash]) -> Hash {
    let mut local_type_hashes = normalized_local_type_hashes.to_vec();
    local_type_hashes.sort();
    let mut out = Vec::new();
    encode_string(&mut out, SUBGOAL_CLUSTER_LOCAL_CONTEXT_PROFILE);
    encode_uvar(&mut out, local_type_hashes.len() as u64);
    for local_type_hash in &local_type_hashes {
        encode_hash(&mut out, local_type_hash);
    }
    hash_with_domain(
        "npa.library-growth.subgoal-cluster-local-context.hash.v1",
        &out,
    )
}

pub fn subgoal_cluster_parent_example_hash(example: &SubgoalClusterParentExample) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, SUBGOAL_CLUSTER_PARENT_EXAMPLE_PROFILE);
    encode_string(&mut out, &example.source_module);
    encode_string(&mut out, &example.declaration_name);
    encode_hash(&mut out, &example.goal_fingerprint);
    encode_hash(&mut out, &example.parent_goal_hash);
    hash_with_domain(
        "npa.library-growth.subgoal-cluster-parent-example.hash.v1",
        &out,
    )
}

pub fn library_gap_signal_hash(signal: &LibraryGapSignalObservation) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LIBRARY_GAP_SIGNAL_PROFILE);
    encode_string(&mut out, signal.kind.as_str());
    encode_string(&mut out, &signal.source_module);
    encode_string(&mut out, &signal.source_id);
    encode_hash(&mut out, &signal.evidence_hash);
    encode_uvar(&mut out, signal.occurrence_count);
    encode_option_string(&mut out, signal.proposed_import_module.as_deref());
    hash_with_domain("npa.library-growth.gap-signal.hash.v1", &out)
}

pub fn canonical_subgoal_cluster_key(key: &SubgoalClusterKey) -> SubgoalClusterKey {
    let mut normalized_local_type_hashes = key.normalized_local_type_hashes.clone();
    normalized_local_type_hashes.sort();

    let mut head_symbols = key.head_symbols.clone();
    head_symbols.sort();
    head_symbols.dedup();

    let mut approved_commutative_canonicalizations = key
        .approved_commutative_canonicalizations
        .iter()
        .map(|canonicalization| {
            let mut operand_hashes = canonicalization.operand_hashes.clone();
            operand_hashes.sort();
            SubgoalClusterCommutativeCanonicalization {
                operator_symbol: canonicalization.operator_symbol.clone(),
                operand_hashes,
            }
        })
        .collect::<Vec<_>>();
    approved_commutative_canonicalizations.sort_by(|left, right| {
        left.operator_symbol
            .cmp(&right.operator_symbol)
            .then_with(|| left.operand_hashes.cmp(&right.operand_hashes))
    });

    let mut domain_tags = key.domain_tags.clone();
    domain_tags.sort();
    domain_tags.dedup();

    SubgoalClusterKey {
        normalized_target_hash: key.normalized_target_hash,
        normalized_local_type_hashes,
        head_symbols,
        universe_erased_shape_hash: key.universe_erased_shape_hash,
        approved_commutative_canonicalizations,
        domain_tags,
    }
}

pub fn validate_subgoal_cluster_observation(
    observation: &SubgoalClusterObservation,
    options: &SubgoalClusterOptions,
) -> Result<(), SubgoalClusterError> {
    if !observation.snapshot_verified {
        return Err(SubgoalClusterError::UnverifiedSnapshot {
            snapshot_hash: observation.snapshot_hash,
        });
    }
    if options.accepted_snapshot_hashes.is_empty()
        || !options
            .accepted_snapshot_hashes
            .contains(&observation.snapshot_hash)
    {
        return Err(SubgoalClusterError::StaleSnapshot {
            snapshot_hash: observation.snapshot_hash,
        });
    }
    validate_subgoal_cluster_key(&observation.key)?;
    validate_subgoal_parent_example(&observation.parent_example)?;
    for signal in &observation.gap_signals {
        validate_library_gap_signal(signal)?;
    }
    let expected_local_context_hash =
        subgoal_cluster_local_context_hash(&observation.key.normalized_local_type_hashes);
    if expected_local_context_hash != observation.local_context_hash {
        return Err(SubgoalClusterError::ModifiedLocalContext {
            expected: expected_local_context_hash,
            actual: observation.local_context_hash,
        });
    }
    Ok(())
}

pub fn cluster_library_growth_subgoals(
    observations: &[SubgoalClusterObservation],
    options: &SubgoalClusterOptions,
) -> Result<Vec<SubgoalCluster>, SubgoalClusterError> {
    let mut clusters = BTreeMap::<Hash, SubgoalClusterAccumulator>::new();
    for observation in observations {
        validate_subgoal_cluster_observation(observation, options)?;
        let key = canonical_subgoal_cluster_key(&observation.key);
        let cluster_id = subgoal_cluster_identity_hash(&key);
        let accumulator = clusters
            .entry(cluster_id)
            .or_insert_with(|| SubgoalClusterAccumulator {
                key,
                parent_examples: BTreeMap::new(),
                gap_signals: BTreeMap::new(),
                strategy_counts: BTreeMap::new(),
            });
        accumulator.parent_examples.insert(
            observation.parent_example.example_hash,
            observation.parent_example.clone(),
        );
        for signal in &observation.gap_signals {
            accumulator
                .gap_signals
                .insert(signal.signal_hash, canonical_library_gap_signal(signal));
        }
        *accumulator
            .strategy_counts
            .entry(observation.likely_proof_strategy)
            .or_insert(0) += 1;
    }

    let mut out = Vec::new();
    for (cluster_id, accumulator) in clusters {
        let parent_examples = accumulator
            .parent_examples
            .into_values()
            .collect::<Vec<SubgoalClusterParentExample>>();
        let required_parent_examples = required_parent_examples(options);
        if parent_examples.len() < required_parent_examples {
            return Err(SubgoalClusterError::InsufficientParentExamples {
                cluster_id,
                required: required_parent_examples,
                actual: parent_examples.len(),
            });
        }
        let gap_signals = accumulator
            .gap_signals
            .into_values()
            .collect::<Vec<LibraryGapSignalObservation>>();
        let likely_proof_strategy = select_likely_proof_strategy(&accumulator.strategy_counts);
        let cluster = SubgoalCluster {
            cluster_id,
            key: accumulator.key,
            parent_examples,
            gap_signals,
            likely_proof_strategy,
            proposal_status: SubgoalClusterProposalStatus::ProposedCandidateLemma,
        };
        validate_subgoal_cluster(&cluster, options)?;
        out.push(cluster);
    }
    Ok(out)
}

pub fn validate_subgoal_cluster(
    cluster: &SubgoalCluster,
    options: &SubgoalClusterOptions,
) -> Result<(), SubgoalClusterError> {
    if !cluster.proposal_status.is_untrusted_proposal() {
        return Err(SubgoalClusterError::InvalidProposalStatus {
            status: cluster.proposal_status,
        });
    }
    let required_parent_examples = required_parent_examples(options);
    if cluster.parent_examples.len() < required_parent_examples {
        return Err(SubgoalClusterError::InsufficientParentExamples {
            cluster_id: cluster.cluster_id,
            required: required_parent_examples,
            actual: cluster.parent_examples.len(),
        });
    }
    for parent_example in &cluster.parent_examples {
        validate_subgoal_parent_example(parent_example)?;
    }
    for signal in &cluster.gap_signals {
        validate_library_gap_signal(signal)?;
    }
    Ok(())
}

pub fn library_gap_signal_collection(clusters: &[SubgoalCluster]) -> Vec<LibraryGapSignalSummary> {
    let mut summaries = BTreeMap::<LibraryGapSignalKind, LibraryGapSignalSummary>::new();
    for cluster in clusters {
        for signal in &cluster.gap_signals {
            let summary = summaries
                .entry(signal.kind)
                .or_insert_with(|| LibraryGapSignalSummary {
                    kind: signal.kind,
                    signal_count: 0,
                    total_occurrences: 0,
                    source_modules: Vec::new(),
                    proposed_import_modules: Vec::new(),
                    signal_hashes: Vec::new(),
                });
            summary.signal_count += 1;
            summary.total_occurrences += signal.occurrence_count;
            summary.source_modules.push(signal.source_module.clone());
            if let Some(module) = signal.proposed_import_module.as_ref() {
                summary.proposed_import_modules.push(module.clone());
            }
            summary.signal_hashes.push(signal.signal_hash);
        }
    }
    summaries
        .into_values()
        .map(|mut summary| {
            sort_dedup_strings(&mut summary.source_modules);
            sort_dedup_strings(&mut summary.proposed_import_modules);
            summary.signal_hashes.sort();
            summary.signal_hashes.dedup();
            summary
        })
        .collect()
}

pub fn lemma_generalization_dependency_order(
    input: &LemmaGeneralizationInput,
) -> Result<StatementNormalizationReport, LemmaGeneralizationError> {
    validate_lemma_generalization_input(input)?;
    let input_hash = lemma_generalization_input_hash(input)?;
    let retained_premises = retained_normalization_premises(input);
    let removed_premises = removed_normalization_premises(input);
    let binder_order = statement_normalization_binder_order(input, &retained_premises)?;
    let parameterized_constants = parameterized_constants(input)?;
    let equality_orientations = equality_orientation_decisions(input)?;
    let selected_structure = selected_weakest_structure(input);
    let carrier_generalizations = accepted_carrier_generalizations(input)?;
    let import_needs = statement_normalization_import_needs(input)?;
    let rejected_attempts = statement_normalization_rejected_attempts(input);
    let generalized_statement_hash = generalized_statement_hash_from_parts(
        input,
        GeneralizedStatementHashParts {
            binder_order: &binder_order,
            retained_premises: &retained_premises,
            parameterized_constants: &parameterized_constants,
            equality_orientations: &equality_orientations,
            selected_structure,
            carrier_generalizations: &carrier_generalizations,
            import_needs: &import_needs,
        },
    );
    let typecheck_witness = input.typecheck_witness.clone().ok_or(
        LemmaGeneralizationError::MissingTypecheckWitness {
            generalized_statement_hash,
        },
    )?;
    if typecheck_witness.generalized_statement_hash != generalized_statement_hash {
        return Err(LemmaGeneralizationError::TypecheckWitnessMismatch {
            expected: generalized_statement_hash,
            actual: typecheck_witness.generalized_statement_hash,
        });
    }

    let mut report = StatementNormalizationReport {
        report_hash: [0; 32],
        input_hash,
        source_context_hash: input.source_context_hash,
        original_goal_hash: input.original_goal_hash,
        normalized_target_hash: input.normalized_target_hash,
        generalized_statement_hash,
        binder_order,
        removed_premises,
        retained_premises,
        parameterized_constants,
        equality_orientations,
        selected_structure,
        carrier_generalizations,
        import_needs,
        rejected_attempts,
        typecheck_witness,
        proof_task_allowed: true,
    };
    report.report_hash = statement_normalization_report_hash(&report);
    Ok(report)
}

pub fn validate_statement_normalization_report(
    input: &LemmaGeneralizationInput,
    report: &StatementNormalizationReport,
) -> Result<(), LemmaGeneralizationError> {
    let expected = lemma_generalization_dependency_order(input)?;
    validate_report_binder_dependency_order(input, report)?;
    for premise in input
        .premises
        .iter()
        .filter(|premise| premise.required_for_typecheck)
    {
        if !report
            .retained_premises
            .iter()
            .any(|retained| retained.premise_id == premise.premise_id)
        {
            return Err(LemmaGeneralizationError::OverGeneralization {
                reason: StatementNormalizationRejectionReason::RequiredForTypecheck,
                item_id: premise.premise_id.clone(),
            });
        }
    }
    if let Some(selected_structure) = report.selected_structure {
        let selected_has_evidence = input.structure_candidates.iter().any(|structure| {
            structure.structure == selected_structure && structure.evidence_hash.is_some()
        });
        if !selected_has_evidence {
            let item_id = input
                .structure_candidates
                .iter()
                .find(|structure| structure.structure == selected_structure)
                .map(|structure| structure.structure_id.clone())
                .unwrap_or_else(|| selected_structure.as_str().to_owned());
            return Err(LemmaGeneralizationError::OverGeneralization {
                reason: StatementNormalizationRejectionReason::MissingStructureEvidence,
                item_id,
            });
        }
    }
    for applied_carrier in &report.carrier_generalizations {
        let carrier_has_evidence = input.carrier_candidates.iter().any(|carrier| {
            carrier.carrier_id == applied_carrier.carrier_id && carrier.evidence_hash.is_some()
        });
        if !carrier_has_evidence {
            return Err(LemmaGeneralizationError::OverGeneralization {
                reason: StatementNormalizationRejectionReason::MissingCarrierEvidence,
                item_id: applied_carrier.carrier_id.clone(),
            });
        }
    }
    if report != &expected {
        return Err(LemmaGeneralizationError::ReportHashMismatch {
            expected: expected.report_hash,
            actual: report.report_hash,
        });
    }
    Ok(())
}

pub fn lemma_generalization_input_hash(
    input: &LemmaGeneralizationInput,
) -> Result<Hash, LemmaGeneralizationError> {
    validate_lemma_generalization_input(input)?;
    let mut out = Vec::new();
    encode_string(&mut out, LEMMA_GENERALIZATION_INPUT_PROFILE);
    encode_hash(&mut out, &input.source_context_hash);
    encode_hash(&mut out, &input.original_goal_hash);
    encode_hash(&mut out, &input.normalized_target_hash);
    encode_uvar(&mut out, input.locals.len() as u64);
    for local in sorted_locals(&input.locals) {
        encode_local(&mut out, local);
    }
    encode_uvar(&mut out, input.premises.len() as u64);
    for premise in sorted_premises(&input.premises) {
        encode_premise(&mut out, premise);
    }
    encode_uvar(&mut out, input.constants.len() as u64);
    for constant in sorted_constants(&input.constants) {
        encode_string(&mut out, &constant.constant_id);
        encode_hash(&mut out, &constant.constant_hash);
        encode_bool(&mut out, constant.may_parameterize);
        encode_option_string(&mut out, constant.import_module.as_deref());
    }
    encode_uvar(&mut out, input.equality_candidates.len() as u64);
    for equality in sorted_equalities(&input.equality_candidates) {
        encode_string(&mut out, &equality.equality_id);
        encode_hash(&mut out, &equality.equality_hash);
        encode_hash(&mut out, &equality.lhs_hash);
        encode_hash(&mut out, &equality.rhs_hash);
        encode_uvar(&mut out, equality.lhs_size);
        encode_uvar(&mut out, equality.rhs_size);
        encode_bool(&mut out, equality.can_reverse);
    }
    encode_uvar(&mut out, input.structure_candidates.len() as u64);
    for structure in sorted_structures(&input.structure_candidates) {
        encode_string(&mut out, &structure.structure_id);
        encode_string(&mut out, structure.structure.as_str());
        encode_option_hash(&mut out, structure.evidence_hash.as_ref());
    }
    encode_uvar(&mut out, input.carrier_candidates.len() as u64);
    for carrier in sorted_carriers(&input.carrier_candidates) {
        encode_string(&mut out, &carrier.carrier_id);
        encode_string(&mut out, carrier.kind.as_str());
        encode_hash(&mut out, &carrier.source_hash);
        encode_hash(&mut out, &carrier.generalized_hash);
        encode_option_hash(&mut out, carrier.evidence_hash.as_ref());
    }
    encode_uvar(&mut out, input.import_candidates.len() as u64);
    for import in sorted_imports(&input.import_candidates) {
        encode_import_need(&mut out, import);
    }
    match input.typecheck_witness.as_ref() {
        Some(witness) => {
            out.push(0x01);
            encode_typecheck_witness(&mut out, witness);
        }
        None => out.push(0x00),
    }
    Ok(hash_with_domain(
        "npa.library-growth.lemma-generalization-input.hash.v1",
        &out,
    ))
}

pub fn lemma_generalization_proposed_statement_hash(
    input: &LemmaGeneralizationInput,
) -> Result<Hash, LemmaGeneralizationError> {
    validate_lemma_generalization_input(input)?;
    let retained_premises = retained_normalization_premises(input);
    let binder_order = statement_normalization_binder_order(input, &retained_premises)?;
    let parameterized_constants = parameterized_constants(input)?;
    let equality_orientations = equality_orientation_decisions(input)?;
    let selected_structure = selected_weakest_structure(input);
    let carrier_generalizations = accepted_carrier_generalizations(input)?;
    let import_needs = statement_normalization_import_needs(input)?;
    Ok(generalized_statement_hash_from_parts(
        input,
        GeneralizedStatementHashParts {
            binder_order: &binder_order,
            retained_premises: &retained_premises,
            parameterized_constants: &parameterized_constants,
            equality_orientations: &equality_orientations,
            selected_structure,
            carrier_generalizations: &carrier_generalizations,
            import_needs: &import_needs,
        },
    ))
}

pub fn statement_normalization_report_hash(report: &StatementNormalizationReport) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, STATEMENT_NORMALIZATION_REPORT_PROFILE);
    encode_hash(&mut out, &report.input_hash);
    encode_hash(&mut out, &report.source_context_hash);
    encode_hash(&mut out, &report.original_goal_hash);
    encode_hash(&mut out, &report.normalized_target_hash);
    encode_hash(&mut out, &report.generalized_statement_hash);
    encode_uvar(&mut out, report.binder_order.len() as u64);
    for binder in &report.binder_order {
        encode_binder(&mut out, binder);
    }
    encode_uvar(&mut out, report.removed_premises.len() as u64);
    for premise in &report.removed_premises {
        encode_statement_premise(&mut out, premise);
    }
    encode_uvar(&mut out, report.retained_premises.len() as u64);
    for premise in &report.retained_premises {
        encode_statement_premise(&mut out, premise);
    }
    encode_uvar(&mut out, report.parameterized_constants.len() as u64);
    for constant in &report.parameterized_constants {
        encode_string(&mut out, &constant.constant_id);
        encode_hash(&mut out, &constant.constant_hash);
    }
    encode_uvar(&mut out, report.equality_orientations.len() as u64);
    for equality in &report.equality_orientations {
        encode_equality_decision(&mut out, equality);
    }
    match report.selected_structure {
        Some(structure) => {
            out.push(0x01);
            encode_string(&mut out, structure.as_str());
        }
        None => out.push(0x00),
    }
    encode_uvar(&mut out, report.carrier_generalizations.len() as u64);
    for carrier in &report.carrier_generalizations {
        encode_carrier_generalization(&mut out, carrier);
    }
    encode_uvar(&mut out, report.import_needs.len() as u64);
    for import in &report.import_needs {
        encode_import_need(&mut out, import);
    }
    encode_uvar(&mut out, report.rejected_attempts.len() as u64);
    for rejected in &report.rejected_attempts {
        encode_rejected_attempt(&mut out, rejected);
    }
    encode_typecheck_witness(&mut out, &report.typecheck_witness);
    encode_bool(&mut out, report.proof_task_allowed);
    hash_with_domain(
        "npa.library-growth.statement-normalization-report.hash.v1",
        &out,
    )
}

pub fn library_reuse_score_input_hash(
    input: &LibraryReuseScoreInput,
) -> Result<Hash, LibraryReuseScoreError> {
    validate_library_reuse_score_input(input)?;
    let mut out = Vec::new();
    encode_string(&mut out, LIBRARY_REUSE_SCORE_INPUT_PROFILE);
    encode_string(&mut out, &input.candidate_id);
    encode_string(&mut out, &input.target_module);
    encode_string(&mut out, &input.declaration_name);
    encode_string(&mut out, input.theorem_level.as_str());
    encode_string(&mut out, input.stage.as_str());
    encode_uvar(&mut out, input.downstream_unlock_count);
    encode_uvar(&mut out, input.repeated_parent_goal_count);
    encode_uvar(&mut out, input.proof_shortening_nodes);
    encode_uvar(&mut out, input.statement_stability_score);
    encode_uvar(&mut out, input.import_closure_added_modules);
    encode_uvar(&mut out, input.axiom_cost);
    encode_uvar(&mut out, input.proof_difficulty_score);
    encode_uvar(&mut out, input.certificate_growth_bytes);
    encode_uvar(&mut out, input.environment_growth_entries);
    encode_uvar(&mut out, input.index_entry_growth);
    encode_uvar(&mut out, input.premise_search_latency_delta_ms);
    encode_bool(&mut out, input.axiom_policy_widened);
    encode_string(&mut out, input.duplicate_status.as_str());
    Ok(hash_with_domain(
        "npa.library-growth.reuse-score-input.hash.v1",
        &out,
    ))
}

pub fn library_growth_budget(
    max_import_closure_added_modules: u64,
    max_axiom_cost: u64,
    max_certificate_growth_bytes: u64,
    max_environment_growth_entries: u64,
    max_index_entry_growth: u64,
    max_premise_search_latency_delta_ms: u64,
) -> LibraryGrowthBudget {
    let mut budget = LibraryGrowthBudget {
        budget_hash: [0; 32],
        max_import_closure_added_modules,
        max_axiom_cost,
        max_certificate_growth_bytes,
        max_environment_growth_entries,
        max_index_entry_growth,
        max_premise_search_latency_delta_ms,
    };
    budget.budget_hash = library_growth_budget_hash(&budget);
    budget
}

pub fn default_library_growth_budget() -> LibraryGrowthBudget {
    library_growth_budget(4, 0, 64 * 1024, 32, 8, 50)
}

pub fn library_growth_budget_hash(budget: &LibraryGrowthBudget) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LIBRARY_GROWTH_BUDGET_PROFILE);
    encode_uvar(&mut out, budget.max_import_closure_added_modules);
    encode_uvar(&mut out, budget.max_axiom_cost);
    encode_uvar(&mut out, budget.max_certificate_growth_bytes);
    encode_uvar(&mut out, budget.max_environment_growth_entries);
    encode_uvar(&mut out, budget.max_index_entry_growth);
    encode_uvar(&mut out, budget.max_premise_search_latency_delta_ms);
    hash_with_domain("npa.library-growth.budget.pg012.hash.v1", &out)
}

pub fn library_reuse_score_report_hash(report: &LibraryReuseScoreReport) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LIBRARY_REUSE_SCORE_REPORT_PROFILE);
    encode_hash(&mut out, &report.input_hash);
    encode_hash(&mut out, &report.budget_hash);
    encode_string(&mut out, &report.candidate_id);
    encode_string(&mut out, &report.target_module);
    encode_string(&mut out, &report.declaration_name);
    encode_string(&mut out, report.theorem_level.as_str());
    encode_string(&mut out, report.stage.as_str());
    encode_bool(&mut out, report.score_is_untrusted);
    encode_bool(&mut out, report.public_promotion_allowed_by_score);
    encode_uvar(&mut out, report.authoring_usefulness_score);
    encode_uvar(&mut out, report.public_readiness_score);
    encode_library_reuse_score_breakdown(&mut out, &report.score_breakdown);
    encode_uvar(&mut out, report.budget_failures.len() as u64);
    for failure in &report.budget_failures {
        encode_library_growth_budget_failure(&mut out, failure);
    }
    encode_string(&mut out, report.authoring_recommendation.as_str());
    encode_string(&mut out, report.public_package_recommendation.as_str());
    encode_bool(&mut out, report.public_package_ready_for_review);
    hash_with_domain("npa.library-growth.reuse-score-report.hash.v1", &out)
}

pub fn library_reuse_score(
    input: &LibraryReuseScoreInput,
    budget: &LibraryGrowthBudget,
) -> Result<LibraryReuseScoreReport, LibraryReuseScoreError> {
    validate_library_reuse_score_input(input)?;
    validate_library_growth_budget(budget)?;

    let input_hash = library_reuse_score_input_hash(input)?;
    let score_breakdown = library_reuse_score_breakdown(input);
    let authoring_positive = positive_reuse_score(&score_breakdown);
    let growth_penalty = library_growth_penalty(&score_breakdown);
    let authoring_usefulness_score = authoring_positive.saturating_sub(growth_penalty / 2);
    let public_readiness_score = authoring_positive.saturating_sub(growth_penalty);
    let budget_failures = library_growth_budget_failures(input, budget);
    let public_package_ready_for_review = input.stage == LibraryGrowthStage::PromotionCandidate
        && budget_failures.is_empty()
        && input.theorem_level.is_l2_derived_certificate();
    let authoring_recommendation = if authoring_usefulness_score > 0
        && input.duplicate_status != LibraryReuseDuplicateStatus::Duplicate
    {
        LibraryGrowthRecommendation::AuthoringUseful
    } else {
        LibraryGrowthRecommendation::Defer
    };
    let public_package_recommendation = if public_package_ready_for_review {
        LibraryGrowthRecommendation::PromotionReviewRequired
    } else {
        LibraryGrowthRecommendation::Defer
    };

    let mut report = LibraryReuseScoreReport {
        report_hash: [0; 32],
        input_hash,
        budget_hash: budget.budget_hash,
        candidate_id: input.candidate_id.clone(),
        target_module: input.target_module.clone(),
        declaration_name: input.declaration_name.clone(),
        theorem_level: input.theorem_level,
        stage: input.stage,
        score_is_untrusted: true,
        public_promotion_allowed_by_score: false,
        authoring_usefulness_score,
        public_readiness_score,
        score_breakdown,
        budget_failures,
        authoring_recommendation,
        public_package_recommendation,
        public_package_ready_for_review,
    };
    report.report_hash = library_reuse_score_report_hash(&report);
    Ok(report)
}

pub fn validate_library_reuse_score_report(
    input: &LibraryReuseScoreInput,
    budget: &LibraryGrowthBudget,
    report: &LibraryReuseScoreReport,
) -> Result<(), LibraryReuseScoreError> {
    let expected = library_reuse_score(input, budget)?;
    if report.report_hash != library_reuse_score_report_hash(report) {
        return Err(LibraryReuseScoreError::ReportHashMismatch {
            expected: library_reuse_score_report_hash(report),
            actual: report.report_hash,
        });
    }
    if report != &expected {
        return Err(LibraryReuseScoreError::ReportHashMismatch {
            expected: expected.report_hash,
            actual: report.report_hash,
        });
    }
    Ok(())
}

pub fn theorem_duplicate_identity_hash(
    identity: &TheoremDuplicateIdentity,
) -> Result<Hash, TheoremDuplicateReviewError> {
    validate_theorem_duplicate_identity_for_hash(identity)?;
    let mut out = Vec::new();
    encode_string(&mut out, THEOREM_DUPLICATE_IDENTITY_PROFILE);
    encode_theorem_duplicate_identity(&mut out, identity);
    Ok(hash_with_domain(
        "npa.library-growth.theorem-duplicate-identity.hash.v1",
        &out,
    ))
}

pub fn theorem_duplicate_review_report_hash(report: &TheoremDuplicateReviewReport) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, THEOREM_DUPLICATE_REPORT_PROFILE);
    encode_hash(&mut out, &report.existing_identity_hash);
    encode_hash(&mut out, &report.proposed_identity_hash);
    encode_theorem_duplicate_identity(&mut out, &report.existing);
    encode_theorem_duplicate_identity(&mut out, &report.proposed);
    encode_uvar(&mut out, report.review_stages.len() as u64);
    for stage in &report.review_stages {
        encode_string(&mut out, stage.as_str());
    }
    encode_string(&mut out, report.relation_kind.as_str());
    encode_theorem_duplicate_import_cost_comparison(&mut out, &report.import_cost_comparison);
    encode_theorem_duplicate_axiom_policy_comparison(&mut out, &report.axiom_policy_comparison);
    encode_option_string(
        &mut out,
        report.mutual_implication_skipped_reason.as_deref(),
    );
    encode_bool(&mut out, report.compatibility_alias_marked);
    encode_string(&mut out, report.recommended_action.as_str());
    encode_bool(&mut out, report.proof_task_creation_blocked);
    encode_bool(&mut out, report.public_promotion_blocked);
    encode_bool(&mut out, report.public_promotion_allowed_by_report);
    encode_bool(
        &mut out,
        report.handles_staged_and_public_identities_separately,
    );
    hash_with_domain("npa.library-growth.theorem-duplicate-report.hash.v1", &out)
}

pub fn theorem_duplicate_review_report(
    existing: TheoremDuplicateIdentity,
    proposed: TheoremDuplicateIdentity,
    mutual_implication: Option<TheoremDuplicateMutualImplicationEvidence>,
    compatibility_alias_marked: bool,
) -> Result<TheoremDuplicateReviewReport, TheoremDuplicateReviewError> {
    validate_theorem_duplicate_identity(&existing, true)?;
    validate_theorem_duplicate_identity(&proposed, false)?;
    if existing.namespace == proposed.namespace
        && existing.module == proposed.module
        && existing.declaration_name == proposed.declaration_name
    {
        return Err(TheoremDuplicateReviewError::SameTheoremIdentity {
            module: proposed.module,
            declaration_name: proposed.declaration_name,
        });
    }
    if let Some(evidence) = &mutual_implication {
        if let Some(reason) = &evidence.skipped_reason {
            validate_theorem_duplicate_identifier(TheoremDuplicateField::SkippedReason, reason)?;
        }
    }

    let existing_identity_hash = theorem_duplicate_identity_hash(&existing)?;
    let proposed_identity_hash = theorem_duplicate_identity_hash(&proposed)?;
    let (relation_kind, review_stages, mutual_implication_skipped_reason) =
        theorem_duplicate_relation(&existing, &proposed, mutual_implication.as_ref());
    let import_cost_comparison = theorem_duplicate_import_cost_comparison(&existing, &proposed);
    let axiom_policy_comparison = theorem_duplicate_axiom_policy_comparison(&existing, &proposed);
    let recommended_action =
        theorem_duplicate_recommended_action(relation_kind, compatibility_alias_marked);
    let proof_task_creation_blocked = relation_kind.is_duplicate() && !compatibility_alias_marked;
    let public_promotion_blocked = matches!(
        relation_kind,
        TheoremDuplicateRelationKind::ProposedStronger
            | TheoremDuplicateRelationKind::ProposedWeaker
            | TheoremDuplicateRelationKind::Inconclusive
    ) || (relation_kind.is_duplicate()
        && !compatibility_alias_marked);
    let handles_staged_and_public_identities_separately = existing.namespace != proposed.namespace;

    let mut report = TheoremDuplicateReviewReport {
        report_hash: [0; 32],
        existing_identity_hash,
        proposed_identity_hash,
        existing,
        proposed,
        review_stages,
        relation_kind,
        import_cost_comparison,
        axiom_policy_comparison,
        mutual_implication_skipped_reason,
        compatibility_alias_marked,
        recommended_action,
        proof_task_creation_blocked,
        public_promotion_blocked,
        public_promotion_allowed_by_report: false,
        handles_staged_and_public_identities_separately,
    };
    report.report_hash = theorem_duplicate_review_report_hash(&report);
    Ok(report)
}

pub fn validate_theorem_duplicate_review_report(
    report: &TheoremDuplicateReviewReport,
) -> Result<(), TheoremDuplicateReviewError> {
    if report.report_hash != theorem_duplicate_review_report_hash(report) {
        return Err(TheoremDuplicateReviewError::ReportHashMismatch {
            expected: theorem_duplicate_review_report_hash(report),
            actual: report.report_hash,
        });
    }
    let existing_identity_hash = theorem_duplicate_identity_hash(&report.existing)?;
    let proposed_identity_hash = theorem_duplicate_identity_hash(&report.proposed)?;
    let import_cost_comparison =
        theorem_duplicate_import_cost_comparison(&report.existing, &report.proposed);
    let axiom_policy_comparison =
        theorem_duplicate_axiom_policy_comparison(&report.existing, &report.proposed);
    let recommended_action = theorem_duplicate_recommended_action(
        report.relation_kind,
        report.compatibility_alias_marked,
    );
    let proof_task_creation_blocked =
        report.relation_kind.is_duplicate() && !report.compatibility_alias_marked;
    let public_promotion_blocked = matches!(
        report.relation_kind,
        TheoremDuplicateRelationKind::ProposedStronger
            | TheoremDuplicateRelationKind::ProposedWeaker
            | TheoremDuplicateRelationKind::Inconclusive
    ) || (report.relation_kind.is_duplicate()
        && !report.compatibility_alias_marked);
    let handles_staged_and_public_identities_separately =
        report.existing.namespace != report.proposed.namespace;
    let relation_consistent = if report.existing.statement_hash == report.proposed.statement_hash {
        report.relation_kind == TheoremDuplicateRelationKind::ExactStatementHash
    } else if report.existing.alpha_equivalence_hash == report.proposed.alpha_equivalence_hash {
        report.relation_kind == TheoremDuplicateRelationKind::AlphaEquivalent
    } else if report.existing.reducible_normal_form_hash.is_some()
        && report.existing.reducible_normal_form_hash == report.proposed.reducible_normal_form_hash
    {
        report.relation_kind == TheoremDuplicateRelationKind::ReduciblyEqual
    } else {
        true
    };
    let stages_consistent =
        theorem_duplicate_review_stages_consistent(report.relation_kind, &report.review_stages);
    if report.existing_identity_hash != existing_identity_hash
        || report.proposed_identity_hash != proposed_identity_hash
        || report.import_cost_comparison != import_cost_comparison
        || report.axiom_policy_comparison != axiom_policy_comparison
        || report.recommended_action != recommended_action
        || report.proof_task_creation_blocked != proof_task_creation_blocked
        || report.public_promotion_blocked != public_promotion_blocked
        || report.public_promotion_allowed_by_report
        || report.handles_staged_and_public_identities_separately
            != handles_staged_and_public_identities_separately
        || !relation_consistent
        || !stages_consistent
    {
        return Err(TheoremDuplicateReviewError::ReportHashMismatch {
            expected: theorem_duplicate_review_report_hash(report),
            actual: report.report_hash,
        });
    }
    Ok(())
}

pub fn promotion_judgment_input_hash(
    input: &PromotionJudgmentInput,
) -> Result<Hash, PromotionJudgmentError> {
    validate_promotion_judgment_input(input)?;
    Ok(promotion_judgment_input_hash_unchecked(input))
}

pub fn promotion_judgment_report_hash(report: &PromotionJudgmentReport) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMOTION_JUDGMENT_REPORT_PROFILE);
    encode_hash(&mut out, &report.input_hash);
    encode_string(&mut out, &report.candidate_id);
    encode_string(&mut out, &report.target_module);
    encode_string(&mut out, &report.declaration_name);
    encode_string(&mut out, report.theorem_level.as_str());
    encode_string(&mut out, report.decision.as_str());
    encode_uvar(&mut out, report.hard_rejection_reasons.len() as u64);
    for reason in &report.hard_rejection_reasons {
        encode_promotion_judgment_reason(&mut out, reason);
    }
    encode_uvar(&mut out, report.defer_reasons.len() as u64);
    for reason in &report.defer_reasons {
        encode_promotion_judgment_reason(&mut out, reason);
    }
    encode_bool(&mut out, report.public_promotion_allowed);
    encode_bool(&mut out, report.staged_artifact_preserved);
    encode_string(&mut out, &report.audit_text);
    hash_with_domain("npa.library-growth.promotion-judgment-report.hash.v1", &out)
}

pub fn promotion_judgment_hard_rejection_reasons(
    input: &PromotionJudgmentInput,
) -> Result<Vec<PromotionJudgmentReason>, PromotionJudgmentError> {
    validate_promotion_judgment_input(input)?;
    Ok(collect_promotion_judgment_hard_rejection_reasons(input))
}

pub fn promotion_judgment_defer_reasons(
    input: &PromotionJudgmentInput,
) -> Result<Vec<PromotionJudgmentReason>, PromotionJudgmentError> {
    validate_promotion_judgment_input(input)?;
    Ok(collect_promotion_judgment_defer_reasons(input))
}

pub fn promotion_judgment(
    input: &PromotionJudgmentInput,
) -> Result<PromotionJudgmentReport, PromotionJudgmentError> {
    validate_promotion_judgment_input(input)?;
    let input_hash = promotion_judgment_input_hash_unchecked(input);
    let hard_rejection_reasons = collect_promotion_judgment_hard_rejection_reasons(input);
    let defer_reasons = collect_promotion_judgment_defer_reasons(input);
    let decision = if !hard_rejection_reasons.is_empty() {
        PromotionJudgmentDecision::RejectForNow
    } else if !defer_reasons.is_empty() {
        PromotionJudgmentDecision::Defer
    } else {
        PromotionJudgmentDecision::Promote
    };
    let public_promotion_allowed = decision == PromotionJudgmentDecision::Promote;
    let audit_text = promotion_judgment_audit_text(
        input,
        input_hash,
        decision,
        &hard_rejection_reasons,
        &defer_reasons,
        public_promotion_allowed,
    );
    let mut report = PromotionJudgmentReport {
        report_hash: [0; 32],
        input_hash,
        candidate_id: input.candidate_id.clone(),
        target_module: input.artifact.target_proof_corpus_module.clone(),
        declaration_name: input.artifact.declaration_name.clone(),
        theorem_level: input.artifact.theorem_level,
        decision,
        hard_rejection_reasons,
        defer_reasons,
        public_promotion_allowed,
        staged_artifact_preserved: true,
        audit_text,
    };
    report.report_hash = promotion_judgment_report_hash(&report);
    Ok(report)
}

pub fn validate_promotion_judgment_report(
    input: &PromotionJudgmentInput,
    report: &PromotionJudgmentReport,
) -> Result<(), PromotionJudgmentError> {
    let expected = promotion_judgment(input)?;
    let actual_hash = promotion_judgment_report_hash(report);
    if report.report_hash != actual_hash {
        return Err(PromotionJudgmentError::HashMismatch {
            field: PromotionJudgmentField::ReportHash,
            expected: actual_hash,
            actual: report.report_hash,
        });
    }
    if report != &expected {
        return Err(PromotionJudgmentError::ReportHashMismatch {
            expected: expected.report_hash,
            actual: report.report_hash,
        });
    }
    Ok(())
}

pub fn promotion_metadata_hash(metadata: &PromotionMetadata) -> Hash {
    promotion_metadata_hash_unchecked(metadata)
}

pub fn promotion_metadata_consistency_report_hash(
    report: &PromotionMetadataConsistencyReport,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMOTION_METADATA_CONSISTENCY_REPORT_PROFILE);
    encode_hash(&mut out, &report.metadata_hash);
    encode_string(&mut out, &report.candidate_id);
    encode_string(&mut out, report.review_phase.as_str());
    encode_string(&mut out, &report.source_module);
    encode_string(&mut out, &report.target_mathlib_module);
    encode_string(&mut out, &report.target_declaration_name);
    encode_string(&mut out, report.theorem_card_level.as_str());
    encode_bool(&mut out, report.promotion_blocked);
    encode_bool(&mut out, report.reviewable_before_materialization);
    encode_bool(&mut out, report.rechecked_after_materialization);
    encode_bool(&mut out, report.source_free_package_verification_compatible);
    encode_uvar(&mut out, report.issues.len() as u64);
    for issue in &report.issues {
        encode_promotion_metadata_issue(&mut out, issue);
    }
    hash_with_domain(
        "npa.library-growth.promotion-metadata-consistency-report.hash.v1",
        &out,
    )
}

pub fn promotion_metadata_consistency(
    metadata: &PromotionMetadata,
) -> Result<PromotionMetadataConsistencyReport, PromotionMetadataError> {
    let expected_metadata_hash = promotion_metadata_hash_unchecked(metadata);
    if metadata.metadata_hash != expected_metadata_hash {
        return Err(PromotionMetadataError::HashMismatch {
            field: PromotionMetadataField::MetadataHash,
            expected: expected_metadata_hash,
            actual: metadata.metadata_hash,
        });
    }

    let issues = collect_promotion_metadata_issues(metadata);
    let promotion_blocked = !issues.is_empty();
    let mut report = PromotionMetadataConsistencyReport {
        report_hash: [0; 32],
        metadata_hash: metadata.metadata_hash,
        candidate_id: metadata.candidate_id.clone(),
        review_phase: metadata.review_phase,
        source_module: metadata.source_module.clone(),
        target_mathlib_module: metadata.target_mathlib_module.clone(),
        target_declaration_name: metadata.target_declaration_name.clone(),
        theorem_card_level: metadata.theorem_card_level,
        promotion_blocked,
        reviewable_before_materialization: metadata.review_phase
            == PromotionMetadataReviewPhase::PreMaterialization,
        rechecked_after_materialization: metadata.review_phase
            == PromotionMetadataReviewPhase::PostMaterialization,
        source_free_package_verification_compatible: !promotion_blocked,
        issues,
    };
    report.report_hash = promotion_metadata_consistency_report_hash(&report);
    Ok(report)
}

pub fn validate_promotion_metadata_consistency_report(
    metadata: &PromotionMetadata,
    report: &PromotionMetadataConsistencyReport,
) -> Result<(), PromotionMetadataError> {
    let expected = promotion_metadata_consistency(metadata)?;
    let actual_hash = promotion_metadata_consistency_report_hash(report);
    if report.report_hash != actual_hash {
        return Err(PromotionMetadataError::HashMismatch {
            field: PromotionMetadataField::ReportHash,
            expected: actual_hash,
            actual: report.report_hash,
        });
    }
    if report != &expected {
        return Err(PromotionMetadataError::ReportMismatch {
            expected: expected.report_hash,
            actual: report.report_hash,
        });
    }
    Ok(())
}

pub fn default_promotion_ranking_profile() -> PromotionRankingProfile {
    let mut profile = PromotionRankingProfile {
        profile_hash: [0; 32],
        reuse_weight: 4,
        foundational_value_weight: 3,
        statement_stability_weight: 2,
        release_readiness_weight: 2,
        import_cost_weight: 1,
        axiom_cost_weight: 3,
        duplicate_subsumption_risk_weight: 4,
        downstream_migration_cost_weight: 1,
        package_growth_weight: 2,
    };
    profile.profile_hash = promotion_ranking_profile_hash(&profile);
    profile
}

pub fn promotion_ranking_profile_hash(profile: &PromotionRankingProfile) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMOTION_RANKING_PROFILE);
    encode_uvar(&mut out, profile.reuse_weight);
    encode_uvar(&mut out, profile.foundational_value_weight);
    encode_uvar(&mut out, profile.statement_stability_weight);
    encode_uvar(&mut out, profile.release_readiness_weight);
    encode_uvar(&mut out, profile.import_cost_weight);
    encode_uvar(&mut out, profile.axiom_cost_weight);
    encode_uvar(&mut out, profile.duplicate_subsumption_risk_weight);
    encode_uvar(&mut out, profile.downstream_migration_cost_weight);
    encode_uvar(&mut out, profile.package_growth_weight);
    hash_with_domain("npa.library-growth.promotion-ranking-profile.hash.v1", &out)
}

pub fn promotion_ranking_identity_hash(
    candidate: &PromotionRankingCandidateInput,
) -> Result<Hash, PromotionRankingError> {
    validate_promotion_ranking_candidate(candidate)?;
    Ok(promotion_ranking_identity_hash_unchecked(candidate))
}

pub fn promotion_ranking_report_hash(report: &PromotionRankingReport) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMOTION_RANKING_REPORT_PROFILE);
    encode_hash(&mut out, &report.profile_hash);
    encode_bool(&mut out, report.operator_aid_only);
    encode_uvar(&mut out, report.entries.len() as u64);
    for entry in &report.entries {
        encode_promotion_ranking_entry(&mut out, entry);
    }
    hash_with_domain("npa.library-growth.promotion-ranking-report.hash.v1", &out)
}

pub fn promotion_ranking(
    candidates: &[PromotionRankingCandidateInput],
    profile: &PromotionRankingProfile,
) -> Result<PromotionRankingReport, PromotionRankingError> {
    validate_promotion_ranking_profile(profile)?;

    let mut entries = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        validate_promotion_ranking_candidate(candidate)?;
        entries.push(promotion_ranking_entry(candidate, profile)?);
    }
    entries.sort_by(|left, right| {
        promotion_ranking_decision_bucket(left.decision)
            .cmp(&promotion_ranking_decision_bucket(right.decision))
            .then_with(|| right.numeric_score.cmp(&left.numeric_score))
            .then_with(|| {
                left.package_growth_penalty
                    .cmp(&right.package_growth_penalty)
            })
            .then_with(|| left.ranking_identity_hash.cmp(&right.ranking_identity_hash))
            .then_with(|| left.candidate_id.cmp(&right.candidate_id))
    });
    for (index, entry) in entries.iter_mut().enumerate() {
        entry.rank = index as u64 + 1;
        entry.rank_explanation = promotion_ranking_explanation(entry);
    }

    let mut report = PromotionRankingReport {
        report_hash: [0; 32],
        profile_hash: profile.profile_hash,
        operator_aid_only: true,
        entries,
    };
    report.report_hash = promotion_ranking_report_hash(&report);
    Ok(report)
}

pub fn validate_promotion_ranking_report(
    candidates: &[PromotionRankingCandidateInput],
    profile: &PromotionRankingProfile,
    report: &PromotionRankingReport,
) -> Result<(), PromotionRankingError> {
    let expected = promotion_ranking(candidates, profile)?;
    let actual_hash = promotion_ranking_report_hash(report);
    if report.report_hash != actual_hash {
        return Err(PromotionRankingError::HashMismatch {
            field: PromotionRankingField::ReportHash,
            expected: actual_hash,
            actual: report.report_hash,
        });
    }
    if report != &expected {
        return Err(PromotionRankingError::HashMismatch {
            field: PromotionRankingField::ReportHash,
            expected: expected.report_hash,
            actual: report.report_hash,
        });
    }
    Ok(())
}

pub fn corpus_alias_proposal_hash(
    proposal: &CorpusAliasProposalMetadata,
) -> Result<Hash, CorpusDeprecationError> {
    validate_corpus_alias_proposal_semantics(proposal)?;
    Ok(corpus_alias_proposal_hash_unchecked(proposal))
}

pub fn validate_corpus_alias_proposal(
    proposal: &CorpusAliasProposalMetadata,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_alias_proposal_semantics(proposal)?;
    let expected = corpus_alias_proposal_hash_unchecked(proposal);
    if proposal.proposal_hash != expected {
        return Err(CorpusDeprecationError::HashMismatch {
            field: CorpusDeprecationField::ProposalHash,
            expected,
            actual: proposal.proposal_hash,
        });
    }
    Ok(())
}

pub fn public_compatibility_decision_hash(
    decision: &PublicCompatibilityDecisionRecord,
) -> Result<Hash, CorpusDeprecationError> {
    validate_public_compatibility_decision_semantics(decision)?;
    Ok(public_compatibility_decision_hash_unchecked(decision))
}

pub fn validate_public_compatibility_decision(
    decision: &PublicCompatibilityDecisionRecord,
) -> Result<(), CorpusDeprecationError> {
    validate_public_compatibility_decision_semantics(decision)?;
    let expected = public_compatibility_decision_hash_unchecked(decision);
    if decision.decision_hash != expected {
        return Err(CorpusDeprecationError::HashMismatch {
            field: CorpusDeprecationField::PublicCompatibilityDecisionHash,
            expected,
            actual: decision.decision_hash,
        });
    }
    Ok(())
}

pub fn validate_public_compatibility_decision_for_deprecation(
    record: &CorpusDeprecationRecord,
    decision: &PublicCompatibilityDecisionRecord,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_record(record)?;
    validate_public_compatibility_decision(decision)?;
    if record.public_compatibility_decision_hash != Some(decision.decision_hash) {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::PublicCompatibilityDecisionHash,
            expected: format!("{:?}", record.public_compatibility_decision_hash),
            actual: format!("{:?}", Some(decision.decision_hash)),
        });
    }
    validate_corpus_deprecation_match(
        CorpusDeprecationField::PublicModule,
        &record.deprecated_module,
        &decision.public_module,
    )?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::PublicDeclarationName,
        &record.deprecated_declaration_name,
        &decision.public_declaration_name,
    )?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::ReplacementModule,
        &record.replacement_module,
        &decision.replacement_module,
    )?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::ReplacementDeclarationName,
        &record.replacement_declaration_name,
        &decision.replacement_declaration_name,
    )?;
    if record.replacement_statement_hash != decision.replacement_statement_hash {
        return Err(CorpusDeprecationError::ReplacementStatementMismatch {
            expected: record.replacement_statement_hash,
            actual: decision.replacement_statement_hash,
        });
    }
    if let Some(alias_module) = decision.alias_module.as_deref() {
        validate_corpus_deprecation_match(
            CorpusDeprecationField::AliasModule,
            &record.alias_proposal.alias_module,
            alias_module,
        )?;
    }
    if let Some(alias_declaration_name) = decision.alias_declaration_name.as_deref() {
        validate_corpus_deprecation_match(
            CorpusDeprecationField::AliasDeclarationName,
            &record.alias_proposal.alias_declaration_name,
            alias_declaration_name,
        )?;
    }
    if let Some(intended_removal_version) = decision.intended_removal_version.as_deref() {
        validate_corpus_deprecation_match(
            CorpusDeprecationField::IntendedRemovalVersion,
            &record.intended_removal_version,
            intended_removal_version,
        )?;
    }
    if record.certificate_compatibility != decision.certificate_compatibility {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::PublicCompatibilityAction,
            expected: record.certificate_compatibility.as_str().to_owned(),
            actual: decision.certificate_compatibility.as_str().to_owned(),
        });
    }
    if record.downstream_usages != decision.downstream_usages {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::DownstreamModule,
            expected: "record_downstream_usages".to_owned(),
            actual: "decision_downstream_usages".to_owned(),
        });
    }
    if record.theorem_index_history != decision.theorem_index_history {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::HistoryModule,
            expected: "record_theorem_index_history".to_owned(),
            actual: "decision_theorem_index_history".to_owned(),
        });
    }
    validate_public_compatibility_action_matches_record(record.public_action, decision.action)
}

pub fn corpus_deprecation_record_hash(
    record: &CorpusDeprecationRecord,
) -> Result<Hash, CorpusDeprecationError> {
    validate_corpus_deprecation_record_semantics(record)?;
    Ok(corpus_deprecation_record_hash_unchecked(record))
}

pub fn validate_corpus_deprecation_record(
    record: &CorpusDeprecationRecord,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_record_semantics(record)?;
    let expected = corpus_deprecation_record_hash_unchecked(record);
    if record.record_hash != expected {
        return Err(CorpusDeprecationError::HashMismatch {
            field: CorpusDeprecationField::RecordHash,
            expected,
            actual: record.record_hash,
        });
    }
    Ok(())
}

pub fn corpus_theorem_index_history_hash(
    history: &[CorpusTheoremIndexHistoryEntry],
) -> Result<Hash, CorpusDeprecationError> {
    validate_corpus_theorem_index_history(history)?;
    Ok(corpus_theorem_index_history_hash_unchecked(history))
}

pub fn corpus_deprecated_theorem_index_entry_hash(
    entry: &CorpusDeprecatedTheoremIndexEntry,
) -> Hash {
    corpus_deprecated_theorem_index_entry_hash_unchecked(entry)
}

pub fn validate_corpus_deprecated_theorem_index_entry(
    entry: &CorpusDeprecatedTheoremIndexEntry,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_identifier(CorpusDeprecationField::HistoryModule, &entry.module)?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::HistoryDeclarationName,
        &entry.declaration_name,
    )?;
    if entry.deprecated && entry.preferred_retrieval {
        return Err(CorpusDeprecationError::DeprecatedAliasPreferredRetrieval {
            module: entry.module.clone(),
            declaration_name: entry.declaration_name.clone(),
        });
    }
    let expected = corpus_deprecated_theorem_index_entry_hash_unchecked(entry);
    if entry.entry_hash != expected {
        return Err(CorpusDeprecationError::HashMismatch {
            field: CorpusDeprecationField::TheoremIndexEntryHash,
            expected,
            actual: entry.entry_hash,
        });
    }
    Ok(())
}

pub fn corpus_deprecation_theorem_index_entries(
    record: &CorpusDeprecationRecord,
) -> Result<Vec<CorpusDeprecatedTheoremIndexEntry>, CorpusDeprecationError> {
    validate_corpus_deprecation_record(record)?;
    let history_hash = corpus_theorem_index_history_hash_unchecked(&record.theorem_index_history);
    let mut deprecated = CorpusDeprecatedTheoremIndexEntry {
        entry_hash: [0; 32],
        module: record.deprecated_module.clone(),
        declaration_name: record.deprecated_declaration_name.clone(),
        statement_hash: record.deprecated_statement_hash,
        deprecated: true,
        replacement_module: Some(record.replacement_module.clone()),
        replacement_declaration_name: Some(record.replacement_declaration_name.clone()),
        replacement_statement_hash: Some(record.replacement_statement_hash),
        preferred_retrieval: false,
        theorem_index_history_hash: history_hash,
        alias_scope: Some(record.alias_proposal.alias_scope),
    };
    deprecated.entry_hash = corpus_deprecated_theorem_index_entry_hash_unchecked(&deprecated);
    let mut replacement = CorpusDeprecatedTheoremIndexEntry {
        entry_hash: [0; 32],
        module: record.replacement_module.clone(),
        declaration_name: record.replacement_declaration_name.clone(),
        statement_hash: record.replacement_statement_hash,
        deprecated: false,
        replacement_module: None,
        replacement_declaration_name: None,
        replacement_statement_hash: None,
        preferred_retrieval: true,
        theorem_index_history_hash: history_hash,
        alias_scope: None,
    };
    replacement.entry_hash = corpus_deprecated_theorem_index_entry_hash_unchecked(&replacement);
    validate_corpus_deprecated_theorem_index_entry(&deprecated)?;
    validate_corpus_deprecated_theorem_index_entry(&replacement)?;
    Ok(vec![deprecated, replacement])
}

pub fn canonical_library_gap_signal(
    signal: &LibraryGapSignalObservation,
) -> LibraryGapSignalObservation {
    let mut signal = signal.clone();
    signal.display_text = None;
    signal.observed_wall_clock_ms = None;
    signal
}

fn validate_library_reuse_score_input(
    input: &LibraryReuseScoreInput,
) -> Result<(), LibraryReuseScoreError> {
    validate_library_reuse_identifier(LibraryReuseScoreField::CandidateId, &input.candidate_id)?;
    validate_library_reuse_identifier(LibraryReuseScoreField::TargetModule, &input.target_module)?;
    validate_library_reuse_identifier(
        LibraryReuseScoreField::DeclarationName,
        &input.declaration_name,
    )
}

fn validate_library_growth_budget(
    budget: &LibraryGrowthBudget,
) -> Result<(), LibraryReuseScoreError> {
    let expected = library_growth_budget_hash(budget);
    if expected != budget.budget_hash {
        return Err(LibraryReuseScoreError::BudgetHashMismatch {
            expected,
            actual: budget.budget_hash,
        });
    }
    Ok(())
}

fn library_reuse_score_breakdown(input: &LibraryReuseScoreInput) -> LibraryReuseScoreBreakdown {
    LibraryReuseScoreBreakdown {
        downstream_unlock_score: score_cap(input.downstream_unlock_count, 20, 400),
        repeated_parent_goal_score: score_cap(input.repeated_parent_goal_count, 15, 300),
        proof_shortening_score: score_cap(input.proof_shortening_nodes, 2, 400),
        statement_stability_score: input.statement_stability_score.min(100),
        proof_difficulty_score: input.proof_difficulty_score.min(100),
        import_closure_penalty: score_cap(input.import_closure_added_modules, 25, 500),
        axiom_cost_penalty: score_cap(input.axiom_cost, 100, 500),
        certificate_growth_penalty: score_units(input.certificate_growth_bytes, 1024, 5, 500),
        environment_growth_penalty: score_cap(input.environment_growth_entries, 10, 500),
        index_entry_growth_penalty: score_cap(input.index_entry_growth, 20, 500),
        premise_search_latency_penalty: score_units(
            input.premise_search_latency_delta_ms,
            5,
            1,
            500,
        ),
    }
}

fn library_growth_budget_failures(
    input: &LibraryReuseScoreInput,
    budget: &LibraryGrowthBudget,
) -> Vec<LibraryGrowthBudgetFailure> {
    let mut failures = Vec::new();
    if input.axiom_policy_widened {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::WidenedAxiomPolicy,
            1,
            0,
        ));
    }
    if input.import_closure_added_modules > budget.max_import_closure_added_modules {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::ExcessiveImportClosure,
            input.import_closure_added_modules,
            budget.max_import_closure_added_modules,
        ));
    }
    if input.axiom_cost > budget.max_axiom_cost {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::AxiomCost,
            input.axiom_cost,
            budget.max_axiom_cost,
        ));
    }
    if input.duplicate_status.blocks_public_readiness() {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::DuplicateStatus,
            1,
            0,
        ));
    }
    match input.theorem_level {
        TheoremLevel::Unknown => failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::UnknownTheoremLevel,
            1,
            0,
        )),
        level if !level.is_l2_derived_certificate() => {
            failures.push(library_growth_budget_failure(
                LibraryGrowthBudgetFailureKind::NonL2TheoremLevel,
                1,
                0,
            ));
        }
        _ => {}
    }
    if input.certificate_growth_bytes > budget.max_certificate_growth_bytes {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::CertificateGrowth,
            input.certificate_growth_bytes,
            budget.max_certificate_growth_bytes,
        ));
    }
    if input.environment_growth_entries > budget.max_environment_growth_entries {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::EnvironmentGrowth,
            input.environment_growth_entries,
            budget.max_environment_growth_entries,
        ));
    }
    if input.index_entry_growth > budget.max_index_entry_growth {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::IndexEntryGrowth,
            input.index_entry_growth,
            budget.max_index_entry_growth,
        ));
    }
    if input.premise_search_latency_delta_ms > budget.max_premise_search_latency_delta_ms {
        failures.push(library_growth_budget_failure(
            LibraryGrowthBudgetFailureKind::PremiseSearchLatency,
            input.premise_search_latency_delta_ms,
            budget.max_premise_search_latency_delta_ms,
        ));
    }
    failures
}

fn library_growth_budget_failure(
    kind: LibraryGrowthBudgetFailureKind,
    actual: u64,
    limit: u64,
) -> LibraryGrowthBudgetFailure {
    LibraryGrowthBudgetFailure {
        kind,
        actual,
        limit,
    }
}

fn positive_reuse_score(score: &LibraryReuseScoreBreakdown) -> u64 {
    [
        score.downstream_unlock_score,
        score.repeated_parent_goal_score,
        score.proof_shortening_score,
        score.statement_stability_score,
        score.proof_difficulty_score,
    ]
    .into_iter()
    .fold(0u64, u64::saturating_add)
}

fn library_growth_penalty(score: &LibraryReuseScoreBreakdown) -> u64 {
    [
        score.import_closure_penalty,
        score.axiom_cost_penalty,
        score.certificate_growth_penalty,
        score.environment_growth_penalty,
        score.index_entry_growth_penalty,
        score.premise_search_latency_penalty,
    ]
    .into_iter()
    .fold(0u64, u64::saturating_add)
}

fn score_cap(value: u64, multiplier: u64, cap: u64) -> u64 {
    value.saturating_mul(multiplier).min(cap)
}

fn score_units(value: u64, unit: u64, multiplier: u64, cap: u64) -> u64 {
    if value == 0 {
        0
    } else {
        (((value - 1) / unit) + 1)
            .saturating_mul(multiplier)
            .min(cap)
    }
}

fn validate_library_reuse_identifier(
    field: LibraryReuseScoreField,
    value: &str,
) -> Result<(), LibraryReuseScoreError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(LibraryReuseScoreError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn validate_promotion_judgment_input(
    input: &PromotionJudgmentInput,
) -> Result<(), PromotionJudgmentError> {
    validate_promotion_judgment_identifier(
        PromotionJudgmentField::CandidateId,
        &input.candidate_id,
    )?;
    validate_promotion_judgment_identifier(
        PromotionJudgmentField::TargetModule,
        &input.artifact.target_proof_corpus_module,
    )?;
    validate_promotion_judgment_identifier(
        PromotionJudgmentField::DeclarationName,
        &input.artifact.declaration_name,
    )?;
    for unresolved_import in &input.unresolved_imports {
        validate_promotion_judgment_identifier(
            PromotionJudgmentField::UnresolvedImport,
            unresolved_import,
        )?;
    }

    let expected_artifact_hash = theorem_invention_artifact_identity_hash(&input.artifact);
    if input.artifact.artifact_identity_hash != expected_artifact_hash {
        return Err(PromotionJudgmentError::HashMismatch {
            field: PromotionJudgmentField::ArtifactIdentityHash,
            expected: expected_artifact_hash,
            actual: input.artifact.artifact_identity_hash,
        });
    }
    let expected_context_hash =
        theorem_invention_generalized_context_hash(&input.artifact.generalized_context);
    if input.artifact.generalized_context.context_hash != expected_context_hash {
        return Err(PromotionJudgmentError::HashMismatch {
            field: PromotionJudgmentField::GeneralizedContextHash,
            expected: expected_context_hash,
            actual: input.artifact.generalized_context.context_hash,
        });
    }
    for command in &input.artifact.verification_commands {
        let expected_command_hash = theorem_invention_verification_command_hash(command);
        if command.command_hash != expected_command_hash {
            return Err(PromotionJudgmentError::HashMismatch {
                field: PromotionJudgmentField::VerificationCommandHash,
                expected: expected_command_hash,
                actual: command.command_hash,
            });
        }
    }

    let expected_reuse_report_hash = library_reuse_score_report_hash(&input.reuse_score_report);
    if input.reuse_score_report.report_hash != expected_reuse_report_hash {
        return Err(PromotionJudgmentError::HashMismatch {
            field: PromotionJudgmentField::ReuseScoreReportHash,
            expected: expected_reuse_report_hash,
            actual: input.reuse_score_report.report_hash,
        });
    }
    validate_promotion_judgment_match(
        PromotionJudgmentField::CandidateId,
        &input.candidate_id,
        &input.reuse_score_report.candidate_id,
    )?;
    validate_promotion_judgment_match(
        PromotionJudgmentField::TargetModule,
        &input.artifact.target_proof_corpus_module,
        &input.reuse_score_report.target_module,
    )?;
    validate_promotion_judgment_match(
        PromotionJudgmentField::DeclarationName,
        &input.artifact.declaration_name,
        &input.reuse_score_report.declaration_name,
    )?;
    if input.artifact.theorem_level != input.reuse_score_report.theorem_level {
        return Err(PromotionJudgmentError::InputMismatch {
            field: PromotionJudgmentField::TheoremLevel,
            expected: input.artifact.theorem_level.as_str().to_owned(),
            actual: input.reuse_score_report.theorem_level.as_str().to_owned(),
        });
    }

    if let Some(duplicate_report) = &input.duplicate_review_report {
        let expected_duplicate_report_hash = theorem_duplicate_review_report_hash(duplicate_report);
        if duplicate_report.report_hash != expected_duplicate_report_hash {
            return Err(PromotionJudgmentError::HashMismatch {
                field: PromotionJudgmentField::DuplicateReviewReportHash,
                expected: expected_duplicate_report_hash,
                actual: duplicate_report.report_hash,
            });
        }
        validate_promotion_judgment_match(
            PromotionJudgmentField::TargetModule,
            &input.artifact.target_proof_corpus_module,
            &duplicate_report.proposed.module,
        )?;
        validate_promotion_judgment_match(
            PromotionJudgmentField::DeclarationName,
            &input.artifact.declaration_name,
            &duplicate_report.proposed.declaration_name,
        )?;
        if input.artifact.statement_hash != duplicate_report.proposed.statement_hash {
            return Err(PromotionJudgmentError::InputMismatch {
                field: PromotionJudgmentField::StatementHash,
                expected: format_hash_string(&input.artifact.statement_hash),
                actual: format_hash_string(&duplicate_report.proposed.statement_hash),
            });
        }
        if input.artifact.theorem_level != duplicate_report.proposed.theorem_level {
            return Err(PromotionJudgmentError::InputMismatch {
                field: PromotionJudgmentField::TheoremLevel,
                expected: input.artifact.theorem_level.as_str().to_owned(),
                actual: duplicate_report.proposed.theorem_level.as_str().to_owned(),
            });
        }
    }

    Ok(())
}

fn validate_promotion_judgment_identifier(
    field: PromotionJudgmentField,
    value: &str,
) -> Result<(), PromotionJudgmentError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(PromotionJudgmentError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn validate_promotion_judgment_match(
    field: PromotionJudgmentField,
    expected: &str,
    actual: &str,
) -> Result<(), PromotionJudgmentError> {
    if expected == actual {
        Ok(())
    } else {
        Err(PromotionJudgmentError::InputMismatch {
            field,
            expected: expected.to_owned(),
            actual: actual.to_owned(),
        })
    }
}

fn validate_corpus_alias_proposal_semantics(
    proposal: &CorpusAliasProposalMetadata,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::AliasModule,
        &proposal.alias_module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::AliasDeclarationName,
        &proposal.alias_declaration_name,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::ReplacementModule,
        &proposal.replacement_module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::ReplacementDeclarationName,
        &proposal.replacement_declaration_name,
    )?;
    validate_corpus_nonempty_text(CorpusDeprecationField::RiskNote, &proposal.risk_note)?;
    if proposal.migration_evidence_hash.is_none() {
        return Err(CorpusDeprecationError::MissingMigrationEvidence);
    }
    if proposal.downstream_usages.is_empty() {
        return Err(CorpusDeprecationError::MissingDownstreamUsage);
    }
    for usage in &proposal.downstream_usages {
        validate_corpus_downstream_usage(usage)?;
    }
    validate_corpus_replacement_verification(
        &proposal.verification,
        proposal.replacement_statement_hash,
    )?;
    if proposal
        .alias_scope
        .requires_public_compatibility_decision()
        && proposal.public_compatibility_decision_hash.is_none()
    {
        return Err(CorpusDeprecationError::PublicCompatibilityDecisionMissing);
    }
    if proposal.migration_evidence_kind == CorpusMigrationEvidenceKind::LocalAlias
        && proposal.alias_scope != CorpusAliasScope::LocalCorpusAlias
    {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::AliasScope,
            expected: CorpusAliasScope::LocalCorpusAlias.as_str().to_owned(),
            actual: proposal.alias_scope.as_str().to_owned(),
        });
    }
    if proposal.migration_evidence_kind == CorpusMigrationEvidenceKind::PublicCompatibilityAlias
        && proposal.public_compatibility_decision_hash.is_none()
    {
        return Err(CorpusDeprecationError::PublicCompatibilityDecisionMissing);
    }
    if proposal.migration_evidence_kind == CorpusMigrationEvidenceKind::PublicCompatibilityAlias
        && proposal.alias_scope != CorpusAliasScope::PublicPackageCompatibilityAlias
    {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::MigrationEvidenceKind,
            expected: CorpusAliasScope::PublicPackageCompatibilityAlias
                .as_str()
                .to_owned(),
            actual: proposal.alias_scope.as_str().to_owned(),
        });
    }
    Ok(())
}

fn validate_public_compatibility_decision_semantics(
    decision: &PublicCompatibilityDecisionRecord,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::PublicModule,
        &decision.public_module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::PublicDeclarationName,
        &decision.public_declaration_name,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::ReplacementModule,
        &decision.replacement_module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::ReplacementDeclarationName,
        &decision.replacement_declaration_name,
    )?;
    validate_corpus_nonempty_text(CorpusDeprecationField::RiskNote, &decision.risk_note)?;
    if decision.downstream_usages.is_empty() {
        return Err(CorpusDeprecationError::MissingDownstreamUsage);
    }
    for usage in &decision.downstream_usages {
        validate_corpus_downstream_usage(usage)?;
    }
    validate_corpus_theorem_index_history(&decision.theorem_index_history)?;
    validate_corpus_replacement_verification(
        &decision.replacement_verification,
        decision.replacement_statement_hash,
    )?;
    if matches!(
        decision.certificate_compatibility,
        CorpusCertificateCompatibility::CompatibilityDecisionRequired
            | CorpusCertificateCompatibility::Incompatible
    ) {
        return Err(CorpusDeprecationError::IncompatibleCertificate);
    }
    if decision.action.requires_alias() {
        validate_optional_alias_identifier(
            CorpusDeprecationField::AliasModule,
            decision.alias_module.as_deref(),
        )?;
        validate_optional_alias_identifier(
            CorpusDeprecationField::AliasDeclarationName,
            decision.alias_declaration_name.as_deref(),
        )?;
    }
    if decision.action.requires_removal_version() {
        let Some(version) = decision.intended_removal_version.as_deref() else {
            return Err(CorpusDeprecationError::MissingRemovalVersion);
        };
        validate_corpus_nonempty_text(CorpusDeprecationField::IntendedRemovalVersion, version)?;
    } else if let Some(version) = decision.intended_removal_version.as_deref() {
        validate_corpus_nonempty_text(CorpusDeprecationField::IntendedRemovalVersion, version)?;
    }
    if let Some(alias_module) = decision.alias_module.as_deref() {
        validate_corpus_deprecation_identifier(CorpusDeprecationField::AliasModule, alias_module)?;
    }
    if let Some(alias_name) = decision.alias_declaration_name.as_deref() {
        validate_corpus_deprecation_identifier(
            CorpusDeprecationField::AliasDeclarationName,
            alias_name,
        )?;
    }
    if decision.action == PublicCompatibilityAction::DeprecateAlias
        && !decision.theorem_index_history.iter().any(|entry| {
            entry.module == decision.public_module
                && entry.declaration_name == decision.public_declaration_name
                && entry.deprecated
        })
    {
        return Err(CorpusDeprecationError::MissingDeprecatedAliasHistory {
            module: decision.public_module.clone(),
            declaration_name: decision.public_declaration_name.clone(),
        });
    }
    Ok(())
}

fn validate_public_compatibility_action_matches_record(
    public_action: CorpusPublicTheoremAction,
    decision_action: PublicCompatibilityAction,
) -> Result<(), CorpusDeprecationError> {
    let matches = match public_action {
        CorpusPublicTheoremAction::PreservePublicTheorem => {
            decision_action == PublicCompatibilityAction::PreservePublicName
        }
        CorpusPublicTheoremAction::ProposeCompatibilityAlias => matches!(
            decision_action,
            PublicCompatibilityAction::AddCompatibilityAlias
                | PublicCompatibilityAction::DeprecateAlias
        ),
        CorpusPublicTheoremAction::RemoveOrRewritePublicTheorem => {
            decision_action == PublicCompatibilityAction::RemoveOrRewriteAtRemovalVersion
        }
    };
    if matches {
        Ok(())
    } else {
        Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::PublicCompatibilityAction,
            expected: public_action.as_str().to_owned(),
            actual: decision_action.as_str().to_owned(),
        })
    }
}

fn validate_optional_alias_identifier(
    field: CorpusDeprecationField,
    value: Option<&str>,
) -> Result<(), CorpusDeprecationError> {
    let Some(value) = value else {
        return Err(CorpusDeprecationError::MissingCompatibilityAlias);
    };
    validate_corpus_deprecation_identifier(field, value)
}

fn validate_corpus_deprecation_record_semantics(
    record: &CorpusDeprecationRecord,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::DeprecatedModule,
        &record.deprecated_module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::DeprecatedDeclarationName,
        &record.deprecated_declaration_name,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::ReplacementModule,
        &record.replacement_module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::ReplacementDeclarationName,
        &record.replacement_declaration_name,
    )?;
    validate_corpus_nonempty_text(
        CorpusDeprecationField::IntendedRemovalVersion,
        &record.intended_removal_version,
    )?;
    validate_corpus_nonempty_text(CorpusDeprecationField::RiskNote, &record.risk_note)?;
    if record.migration_evidence_hash.is_none() {
        return Err(CorpusDeprecationError::MissingMigrationEvidence);
    }
    if record.downstream_usages.is_empty() {
        return Err(CorpusDeprecationError::MissingDownstreamUsage);
    }
    for usage in &record.downstream_usages {
        validate_corpus_downstream_usage(usage)?;
    }
    validate_corpus_alias_proposal(&record.alias_proposal)?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::AliasModule,
        &record.deprecated_module,
        &record.alias_proposal.alias_module,
    )?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::AliasDeclarationName,
        &record.deprecated_declaration_name,
        &record.alias_proposal.alias_declaration_name,
    )?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::ReplacementModule,
        &record.replacement_module,
        &record.alias_proposal.replacement_module,
    )?;
    validate_corpus_deprecation_match(
        CorpusDeprecationField::ReplacementDeclarationName,
        &record.replacement_declaration_name,
        &record.alias_proposal.replacement_declaration_name,
    )?;
    if record.replacement_statement_hash != record.alias_proposal.replacement_statement_hash {
        return Err(CorpusDeprecationError::ReplacementStatementMismatch {
            expected: record.replacement_statement_hash,
            actual: record.alias_proposal.replacement_statement_hash,
        });
    }
    if record.migration_evidence_hash != record.alias_proposal.migration_evidence_hash {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::ProposalHash,
            expected: format!("{:?}", record.migration_evidence_hash),
            actual: format!("{:?}", record.alias_proposal.migration_evidence_hash),
        });
    }
    if record.downstream_usages != record.alias_proposal.downstream_usages {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::ProposalHash,
            expected: "record_downstream_usages".to_owned(),
            actual: "alias_proposal_downstream_usages".to_owned(),
        });
    }
    if record.public_action == CorpusPublicTheoremAction::RemoveOrRewritePublicTheorem
        && record.public_compatibility_decision_hash.is_none()
    {
        return Err(CorpusDeprecationError::PublicRewriteRequiresCompatibilityDecision);
    }
    if (record
        .public_action
        .requires_public_compatibility_decision()
        || record
            .alias_proposal
            .alias_scope
            .requires_public_compatibility_decision()
        || record.certificate_compatibility
            == CorpusCertificateCompatibility::CompatibilityDecisionRequired)
        && record.public_compatibility_decision_hash.is_none()
    {
        return Err(CorpusDeprecationError::PublicCompatibilityDecisionMissing);
    }
    if record.public_compatibility_decision_hash
        != record.alias_proposal.public_compatibility_decision_hash
    {
        return Err(CorpusDeprecationError::InputMismatch {
            field: CorpusDeprecationField::ProposalHash,
            expected: format!("{:?}", record.public_compatibility_decision_hash),
            actual: format!(
                "{:?}",
                record.alias_proposal.public_compatibility_decision_hash
            ),
        });
    }
    if record.certificate_compatibility == CorpusCertificateCompatibility::Incompatible {
        return Err(CorpusDeprecationError::IncompatibleCertificate);
    }
    validate_corpus_theorem_index_history(&record.theorem_index_history)?;
    if !record.theorem_index_history.iter().any(|entry| {
        entry.module == record.deprecated_module
            && entry.declaration_name == record.deprecated_declaration_name
            && entry.deprecated
    }) {
        return Err(CorpusDeprecationError::MissingDeprecatedAliasHistory {
            module: record.deprecated_module.clone(),
            declaration_name: record.deprecated_declaration_name.clone(),
        });
    }
    Ok(())
}

fn validate_corpus_replacement_verification(
    verification: &CorpusReplacementVerificationEvidence,
    expected_statement_hash: Hash,
) -> Result<(), CorpusDeprecationError> {
    if !verification
        .replacement_theorem_level
        .is_l2_derived_certificate()
    {
        return Err(CorpusDeprecationError::ReplacementNotL2 {
            actual: verification.replacement_theorem_level,
        });
    }
    if verification.source_free_status < ProofAcceptanceState::CertificateVerified {
        return Err(CorpusDeprecationError::ReplacementNotSourceFreeVerified {
            actual: verification.source_free_status,
        });
    }
    if verification.stale_artifact {
        return Err(CorpusDeprecationError::ReplacementStale);
    }
    if verification.replacement_statement_hash != expected_statement_hash {
        return Err(CorpusDeprecationError::ReplacementStatementMismatch {
            expected: expected_statement_hash,
            actual: verification.replacement_statement_hash,
        });
    }
    if verification.verified_statement_hash != verification.replacement_statement_hash {
        return Err(CorpusDeprecationError::ReplacementStatementMismatch {
            expected: verification.replacement_statement_hash,
            actual: verification.verified_statement_hash,
        });
    }
    if verification.verified_certificate_hash != verification.replacement_certificate_hash {
        return Err(CorpusDeprecationError::ReplacementCertificateMismatch {
            expected: verification.replacement_certificate_hash,
            actual: verification.verified_certificate_hash,
        });
    }
    if verification.axiom_policy_widened {
        return Err(CorpusDeprecationError::AxiomPolicyWidened);
    }
    Ok(())
}

fn validate_corpus_theorem_index_history(
    history: &[CorpusTheoremIndexHistoryEntry],
) -> Result<(), CorpusDeprecationError> {
    if history.is_empty() {
        return Err(CorpusDeprecationError::MissingTheoremIndexHistory);
    }
    for entry in history {
        validate_corpus_deprecation_identifier(
            CorpusDeprecationField::HistoryModule,
            &entry.module,
        )?;
        validate_corpus_deprecation_identifier(
            CorpusDeprecationField::HistoryDeclarationName,
            &entry.declaration_name,
        )?;
        if entry.deprecated && entry.preferred_retrieval {
            return Err(CorpusDeprecationError::DeprecatedAliasPreferredRetrieval {
                module: entry.module.clone(),
                declaration_name: entry.declaration_name.clone(),
            });
        }
    }
    Ok(())
}

fn validate_corpus_downstream_usage(
    usage: &CorpusDownstreamUsage,
) -> Result<(), CorpusDeprecationError> {
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::DownstreamModule,
        &usage.module,
    )?;
    validate_corpus_deprecation_identifier(
        CorpusDeprecationField::DownstreamDeclarationName,
        &usage.declaration_name,
    )
}

fn validate_corpus_deprecation_identifier(
    field: CorpusDeprecationField,
    value: &str,
) -> Result<(), CorpusDeprecationError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(CorpusDeprecationError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn validate_corpus_nonempty_text(
    field: CorpusDeprecationField,
    value: &str,
) -> Result<(), CorpusDeprecationError> {
    if value.trim().is_empty() || value.chars().any(char::is_control) {
        Err(CorpusDeprecationError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn validate_corpus_deprecation_match(
    field: CorpusDeprecationField,
    expected: &str,
    actual: &str,
) -> Result<(), CorpusDeprecationError> {
    if expected == actual {
        Ok(())
    } else {
        Err(CorpusDeprecationError::InputMismatch {
            field,
            expected: expected.to_owned(),
            actual: actual.to_owned(),
        })
    }
}

fn promotion_metadata_hash_unchecked(metadata: &PromotionMetadata) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMOTION_METADATA_PROFILE);
    encode_string(&mut out, metadata.review_phase.as_str());
    encode_string(&mut out, &metadata.candidate_id);
    encode_promotion_metadata_file_evidence(&mut out, &metadata.theorem_card);
    encode_string(&mut out, metadata.staged_theorem_level.as_str());
    encode_string(&mut out, metadata.theorem_card_level.as_str());
    encode_string(&mut out, &metadata.source_module);
    encode_string(&mut out, &metadata.source_declaration_name);
    encode_string(&mut out, &metadata.target_mathlib_module);
    encode_string(&mut out, &metadata.target_declaration_name);
    encode_promotion_metadata_verification_evidence(&mut out, &metadata.source_free_verification);
    encode_promotion_metadata_file_evidence(&mut out, &metadata.certificate);
    encode_uvar(&mut out, metadata.import_closure.len() as u64);
    for entry in &metadata.import_closure {
        encode_string(&mut out, &entry.module);
        encode_promotion_metadata_file_evidence(&mut out, &entry.certificate);
    }
    encode_option_hash(&mut out, metadata.axiom_policy_hash.as_ref());
    encode_promotion_metadata_file_evidence(&mut out, &metadata.axiom_report);
    encode_option_hash(&mut out, metadata.reuse_evidence_hash.as_ref());
    encode_option_hash(&mut out, metadata.duplicate_review_hash.as_ref());
    encode_option_hash(&mut out, metadata.compatibility_decision_hash.as_ref());
    encode_option_hash(&mut out, metadata.downstream_plan_hash.as_ref());
    encode_promotion_metadata_file_evidence(&mut out, &metadata.closure_audit);
    encode_promotion_metadata_theorem_index_evidence(&mut out, &metadata.theorem_index);
    encode_promotion_metadata_publish_plan_evidence(&mut out, &metadata.publish_plan);
    encode_string(&mut out, &metadata.release_target);
    hash_with_domain("npa.library-growth.promotion-metadata.hash.v1", &out)
}

fn collect_promotion_metadata_issues(metadata: &PromotionMetadata) -> Vec<PromotionMetadataIssue> {
    let mut issues = Vec::new();
    push_promotion_metadata_empty_identifier(
        &mut issues,
        PromotionMetadataField::CandidateId,
        &metadata.candidate_id,
    );
    push_promotion_metadata_empty_identifier(
        &mut issues,
        PromotionMetadataField::SourceModule,
        &metadata.source_module,
    );
    push_promotion_metadata_empty_identifier(
        &mut issues,
        PromotionMetadataField::SourceDeclarationName,
        &metadata.source_declaration_name,
    );
    push_promotion_metadata_empty_identifier(
        &mut issues,
        PromotionMetadataField::TargetMathlibModule,
        &metadata.target_mathlib_module,
    );
    push_promotion_metadata_empty_identifier(
        &mut issues,
        PromotionMetadataField::TargetDeclarationName,
        &metadata.target_declaration_name,
    );
    push_promotion_metadata_empty_identifier(
        &mut issues,
        PromotionMetadataField::ReleaseTarget,
        &metadata.release_target,
    );

    if !metadata.target_mathlib_module.starts_with("Mathlib.") {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::InvalidTargetModule,
            PromotionMetadataField::TargetMathlibModule,
            format!(
                "target module `{}` is outside the Mathlib namespace",
                metadata.target_mathlib_module
            ),
        );
    }
    if !metadata.staged_theorem_level.is_l2_derived_certificate() {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::InvalidStagedTheoremLevel,
            PromotionMetadataField::StagedTheoremLevel,
            format!(
                "staged theorem level `{}` is not L2 Derived certificate",
                metadata.staged_theorem_level.as_str()
            ),
        );
    }
    let expected_card_level = match metadata.review_phase {
        PromotionMetadataReviewPhase::PreMaterialization => TheoremLevel::L2DerivedCertificate,
        PromotionMetadataReviewPhase::PostMaterialization => TheoremLevel::L3PublicClosure,
    };
    if metadata.theorem_card_level != expected_card_level {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::TheoremCardLevelMismatch,
            PromotionMetadataField::TheoremCardLevel,
            format!(
                "theorem card level `{}` must be `{}` for `{}` review",
                metadata.theorem_card_level.as_str(),
                expected_card_level.as_str(),
                metadata.review_phase.as_str()
            ),
        );
    }

    push_promotion_metadata_file_issues(
        &mut issues,
        PromotionMetadataField::TheoremCard,
        PromotionMetadataField::TheoremCard,
        &metadata.theorem_card,
    );
    push_promotion_metadata_verification_issues(&mut issues, &metadata.source_free_verification);
    push_promotion_metadata_file_issues(
        &mut issues,
        PromotionMetadataField::Certificate,
        PromotionMetadataField::CertificateHash,
        &metadata.certificate,
    );
    if metadata.import_closure.is_empty() {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::MissingImportClosure,
            PromotionMetadataField::ImportClosure,
            "import closure is empty; record the checked closure, even for a singleton module",
        );
    }
    for entry in &metadata.import_closure {
        push_promotion_metadata_empty_identifier(
            &mut issues,
            PromotionMetadataField::ImportClosureModule,
            &entry.module,
        );
        push_promotion_metadata_file_issues(
            &mut issues,
            PromotionMetadataField::ImportClosureCertificate,
            PromotionMetadataField::ImportClosureCertificateHash,
            &entry.certificate,
        );
    }

    push_promotion_metadata_required_hash(
        &mut issues,
        PromotionMetadataField::AxiomPolicyHash,
        metadata.axiom_policy_hash.as_ref(),
    );
    if metadata.axiom_report.path.trim().is_empty() || metadata.axiom_report.hash.is_none() {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::MissingAxiomReport,
            PromotionMetadataField::AxiomReport,
            "package axiom report evidence is missing",
        );
    }
    push_promotion_metadata_file_issues(
        &mut issues,
        PromotionMetadataField::AxiomReport,
        PromotionMetadataField::AxiomReportHash,
        &metadata.axiom_report,
    );
    push_promotion_metadata_required_hash(
        &mut issues,
        PromotionMetadataField::ReuseEvidenceHash,
        metadata.reuse_evidence_hash.as_ref(),
    );
    push_promotion_metadata_required_hash(
        &mut issues,
        PromotionMetadataField::DuplicateReviewHash,
        metadata.duplicate_review_hash.as_ref(),
    );
    push_promotion_metadata_required_hash(
        &mut issues,
        PromotionMetadataField::CompatibilityDecisionHash,
        metadata.compatibility_decision_hash.as_ref(),
    );
    push_promotion_metadata_required_hash(
        &mut issues,
        PromotionMetadataField::DownstreamPlanHash,
        metadata.downstream_plan_hash.as_ref(),
    );
    push_promotion_metadata_file_issues(
        &mut issues,
        PromotionMetadataField::ClosureAudit,
        PromotionMetadataField::ClosureAuditHash,
        &metadata.closure_audit,
    );
    push_promotion_metadata_file_issues(
        &mut issues,
        PromotionMetadataField::TheoremIndex,
        PromotionMetadataField::TheoremIndexHash,
        &metadata.theorem_index.file,
    );
    if !metadata.theorem_index.entries.iter().any(|entry| {
        entry.module == metadata.target_mathlib_module
            && entry.declaration_name == metadata.target_declaration_name
    }) {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::MissingTheoremIndexEntry,
            PromotionMetadataField::TheoremIndexEntry,
            format!(
                "theorem index is missing `{}`::`{}`",
                metadata.target_mathlib_module, metadata.target_declaration_name
            ),
        );
    }
    for entry in &metadata.theorem_index.entries {
        push_promotion_metadata_empty_identifier(
            &mut issues,
            PromotionMetadataField::TheoremIndexEntry,
            &entry.module,
        );
        push_promotion_metadata_empty_identifier(
            &mut issues,
            PromotionMetadataField::TheoremIndexEntry,
            &entry.declaration_name,
        );
    }
    push_promotion_metadata_file_issues(
        &mut issues,
        PromotionMetadataField::PublishPlan,
        PromotionMetadataField::PublishPlanHash,
        &metadata.publish_plan.file,
    );
    if !metadata.publish_plan.entries.iter().any(|entry| {
        entry.module == metadata.target_mathlib_module
            && entry.release_target == metadata.release_target
    }) {
        push_promotion_metadata_issue(
            &mut issues,
            PromotionMetadataIssueKind::MissingPublishPlanEntry,
            PromotionMetadataField::PublishPlanEntry,
            format!(
                "publish plan is missing `{}` for release target `{}`",
                metadata.target_mathlib_module, metadata.release_target
            ),
        );
    }
    for entry in &metadata.publish_plan.entries {
        push_promotion_metadata_empty_identifier(
            &mut issues,
            PromotionMetadataField::PublishPlanEntry,
            &entry.module,
        );
        push_promotion_metadata_empty_identifier(
            &mut issues,
            PromotionMetadataField::PublishPlanEntry,
            &entry.release_target,
        );
    }

    issues
}

fn push_promotion_metadata_verification_issues(
    issues: &mut Vec<PromotionMetadataIssue>,
    evidence: &PromotionMetadataVerificationEvidence,
) {
    push_promotion_metadata_empty_identifier(
        issues,
        PromotionMetadataField::SourceFreeVerificationCommand,
        &evidence.command,
    );
    push_promotion_metadata_required_hash(
        issues,
        PromotionMetadataField::SourceFreeVerificationCommandHash,
        evidence.command_hash.as_ref(),
    );
    if evidence.stale {
        push_promotion_metadata_issue(
            issues,
            PromotionMetadataIssueKind::StaleEvidence,
            PromotionMetadataField::SourceFreeVerificationCommand,
            "source-free verification command evidence is stale",
        );
    }
}

fn push_promotion_metadata_file_issues(
    issues: &mut Vec<PromotionMetadataIssue>,
    path_field: PromotionMetadataField,
    hash_field: PromotionMetadataField,
    evidence: &PromotionMetadataFileEvidence,
) {
    push_promotion_metadata_empty_identifier(issues, path_field, &evidence.path);
    push_promotion_metadata_required_hash(issues, hash_field, evidence.hash.as_ref());
    if evidence.stale {
        push_promotion_metadata_issue(
            issues,
            PromotionMetadataIssueKind::StaleEvidence,
            path_field,
            format!("path evidence `{}` is stale", evidence.path),
        );
    }
}

fn push_promotion_metadata_required_hash(
    issues: &mut Vec<PromotionMetadataIssue>,
    field: PromotionMetadataField,
    hash: Option<&Hash>,
) {
    if hash.is_none() {
        push_promotion_metadata_issue(
            issues,
            PromotionMetadataIssueKind::MissingHash,
            field,
            format!("required hash `{}` is missing", field.as_str()),
        );
    }
}

fn push_promotion_metadata_empty_identifier(
    issues: &mut Vec<PromotionMetadataIssue>,
    field: PromotionMetadataField,
    value: &str,
) {
    if value.trim().is_empty() || value.chars().any(char::is_control) {
        push_promotion_metadata_issue(
            issues,
            PromotionMetadataIssueKind::EmptyIdentifier,
            field,
            format!(
                "identifier `{}` is empty or contains controls",
                field.as_str()
            ),
        );
    }
}

fn push_promotion_metadata_issue(
    issues: &mut Vec<PromotionMetadataIssue>,
    kind: PromotionMetadataIssueKind,
    field: PromotionMetadataField,
    detail: impl Into<String>,
) {
    let issue = PromotionMetadataIssue {
        kind,
        field,
        detail: detail.into(),
    };
    if !issues.contains(&issue) {
        issues.push(issue);
    }
}

fn validate_promotion_ranking_profile(
    profile: &PromotionRankingProfile,
) -> Result<(), PromotionRankingError> {
    let expected = promotion_ranking_profile_hash(profile);
    if profile.profile_hash != expected {
        return Err(PromotionRankingError::HashMismatch {
            field: PromotionRankingField::ProfileHash,
            expected,
            actual: profile.profile_hash,
        });
    }
    Ok(())
}

fn validate_promotion_ranking_candidate(
    candidate: &PromotionRankingCandidateInput,
) -> Result<(), PromotionRankingError> {
    if candidate.candidate_id.is_empty() || candidate.candidate_id.chars().any(char::is_control) {
        return Err(PromotionRankingError::EmptyIdentifier {
            field: PromotionRankingField::CandidateId,
        });
    }
    let expected_reuse_hash = library_reuse_score_report_hash(&candidate.reuse_score_report);
    if candidate.reuse_score_report.report_hash != expected_reuse_hash {
        return Err(PromotionRankingError::HashMismatch {
            field: PromotionRankingField::ReuseScoreReportHash,
            expected: expected_reuse_hash,
            actual: candidate.reuse_score_report.report_hash,
        });
    }
    validate_promotion_ranking_match(
        PromotionRankingField::CandidateId,
        &candidate.candidate_id,
        &candidate.reuse_score_report.candidate_id,
    )?;

    if let Some(duplicate_report) = &candidate.duplicate_review_report {
        let expected_duplicate_hash = theorem_duplicate_review_report_hash(duplicate_report);
        if duplicate_report.report_hash != expected_duplicate_hash {
            return Err(PromotionRankingError::HashMismatch {
                field: PromotionRankingField::DuplicateReviewReportHash,
                expected: expected_duplicate_hash,
                actual: duplicate_report.report_hash,
            });
        }
    }

    let expected_judgment_hash =
        promotion_judgment_report_hash(&candidate.promotion_judgment_report);
    if candidate.promotion_judgment_report.report_hash != expected_judgment_hash {
        return Err(PromotionRankingError::HashMismatch {
            field: PromotionRankingField::PromotionJudgmentReportHash,
            expected: expected_judgment_hash,
            actual: candidate.promotion_judgment_report.report_hash,
        });
    }
    validate_promotion_ranking_match(
        PromotionRankingField::CandidateId,
        &candidate.candidate_id,
        &candidate.promotion_judgment_report.candidate_id,
    )?;
    validate_promotion_ranking_match(
        PromotionRankingField::CandidateId,
        &candidate.candidate_id,
        &candidate.promotion_metadata_report.candidate_id,
    )?;

    let expected_metadata_hash =
        promotion_metadata_consistency_report_hash(&candidate.promotion_metadata_report);
    if candidate.promotion_metadata_report.report_hash != expected_metadata_hash {
        return Err(PromotionRankingError::HashMismatch {
            field: PromotionRankingField::PromotionMetadataReportHash,
            expected: expected_metadata_hash,
            actual: candidate.promotion_metadata_report.report_hash,
        });
    }
    Ok(())
}

fn validate_promotion_ranking_match(
    field: PromotionRankingField,
    expected: &str,
    actual: &str,
) -> Result<(), PromotionRankingError> {
    if expected == actual {
        Ok(())
    } else {
        Err(PromotionRankingError::InputMismatch {
            field,
            expected: expected.to_owned(),
            actual: actual.to_owned(),
        })
    }
}

fn promotion_ranking_entry(
    candidate: &PromotionRankingCandidateInput,
    profile: &PromotionRankingProfile,
) -> Result<PromotionRankingEntry, PromotionRankingError> {
    let ranking_identity_hash = promotion_ranking_identity_hash_unchecked(candidate);
    let reuse_score = candidate.reuse_score_report.public_readiness_score;
    let foundational_value_score = candidate.foundational_value_score.min(100);
    let statement_stability_score = candidate
        .reuse_score_report
        .score_breakdown
        .statement_stability_score;
    let release_readiness_score = candidate.release_readiness_score.min(100);
    let import_cost_penalty = candidate
        .reuse_score_report
        .score_breakdown
        .import_closure_penalty;
    let axiom_cost_penalty = candidate
        .reuse_score_report
        .score_breakdown
        .axiom_cost_penalty;
    let duplicate_subsumption_risk_penalty = duplicate_subsumption_risk_penalty(candidate);
    let downstream_migration_cost_penalty = score_cap(candidate.downstream_migration_cost, 10, 500);
    let package_growth_penalty = promotion_ranking_package_growth_penalty(candidate);
    let positive_score = reuse_score
        .saturating_mul(profile.reuse_weight)
        .saturating_add(foundational_value_score.saturating_mul(profile.foundational_value_weight))
        .saturating_add(
            statement_stability_score.saturating_mul(profile.statement_stability_weight),
        )
        .saturating_add(release_readiness_score.saturating_mul(profile.release_readiness_weight));
    let negative_score = import_cost_penalty
        .saturating_mul(profile.import_cost_weight)
        .saturating_add(axiom_cost_penalty.saturating_mul(profile.axiom_cost_weight))
        .saturating_add(
            duplicate_subsumption_risk_penalty
                .saturating_mul(profile.duplicate_subsumption_risk_weight),
        )
        .saturating_add(
            downstream_migration_cost_penalty
                .saturating_mul(profile.downstream_migration_cost_weight),
        )
        .saturating_add(package_growth_penalty.saturating_mul(profile.package_growth_weight));
    let numeric_score = positive_score.saturating_sub(negative_score);
    let evidence_hashes = promotion_ranking_evidence_hashes(candidate);
    let package_growth_budget_failures = promotion_ranking_package_growth_budget_failures(
        &candidate.reuse_score_report.budget_failures,
    );

    let mut entry = PromotionRankingEntry {
        rank: 0,
        ranking_identity_hash,
        candidate_id: candidate.candidate_id.clone(),
        target_module: candidate.promotion_judgment_report.target_module.clone(),
        declaration_name: candidate.promotion_judgment_report.declaration_name.clone(),
        theorem_level: candidate.promotion_judgment_report.theorem_level,
        decision: candidate.promotion_judgment_report.decision,
        decision_label: candidate
            .promotion_judgment_report
            .decision
            .audit_label()
            .to_owned(),
        hard_rejection_dominates_numeric_rank: !candidate
            .promotion_judgment_report
            .hard_rejection_reasons
            .is_empty(),
        numeric_score,
        reuse_score,
        foundational_value_score,
        statement_stability_score,
        release_readiness_score,
        import_cost_penalty,
        axiom_cost_penalty,
        duplicate_subsumption_risk_penalty,
        downstream_migration_cost_penalty,
        package_growth_penalty,
        package_growth_budget_failures,
        hard_rejection_reasons: candidate
            .promotion_judgment_report
            .hard_rejection_reasons
            .clone(),
        defer_reasons: candidate.promotion_judgment_report.defer_reasons.clone(),
        metadata_issues: candidate.promotion_metadata_report.issues.clone(),
        evidence_hashes,
        rank_explanation: String::new(),
    };
    entry.rank_explanation = promotion_ranking_explanation(&entry);
    Ok(entry)
}

fn promotion_ranking_identity_hash_unchecked(candidate: &PromotionRankingCandidateInput) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.library-growth.promotion-ranking-identity.v1");
    encode_string(&mut out, &candidate.candidate_id);
    encode_string(&mut out, &candidate.promotion_judgment_report.target_module);
    encode_string(
        &mut out,
        &candidate.promotion_judgment_report.declaration_name,
    );
    hash_with_domain(
        "npa.library-growth.promotion-ranking-identity.hash.v1",
        &out,
    )
}

fn promotion_ranking_evidence_hashes(
    candidate: &PromotionRankingCandidateInput,
) -> PromotionRankingEvidenceHashes {
    PromotionRankingEvidenceHashes {
        reuse_score_report_hash: candidate.reuse_score_report.report_hash,
        duplicate_review_report_hash: candidate
            .duplicate_review_report
            .as_ref()
            .map(|report| report.report_hash),
        promotion_judgment_report_hash: candidate.promotion_judgment_report.report_hash,
        promotion_metadata_report_hash: candidate.promotion_metadata_report.report_hash,
        import_closure_hash: candidate.import_closure_hash,
        axiom_report_hash: candidate.axiom_report_hash,
        performance_budget_report_hash: candidate.performance_budget_report_hash,
        theorem_card_metadata_hash: candidate.theorem_card_metadata_hash,
        downstream_plan_hash: candidate.downstream_plan_hash,
    }
}

fn promotion_ranking_decision_bucket(decision: PromotionJudgmentDecision) -> u8 {
    match decision {
        PromotionJudgmentDecision::Promote => 0,
        PromotionJudgmentDecision::Defer => 1,
        PromotionJudgmentDecision::RejectForNow => 2,
    }
}

fn duplicate_subsumption_risk_penalty(candidate: &PromotionRankingCandidateInput) -> u64 {
    match candidate.duplicate_review_report.as_ref() {
        Some(report) if report.public_promotion_blocked => 500,
        Some(report)
            if report.relation_kind.is_duplicate() && !report.compatibility_alias_marked =>
        {
            400
        }
        Some(report)
            if matches!(
                report.relation_kind,
                TheoremDuplicateRelationKind::ProposedStronger
                    | TheoremDuplicateRelationKind::ProposedWeaker
                    | TheoremDuplicateRelationKind::Inconclusive
            ) =>
        {
            250
        }
        Some(report) if report.compatibility_alias_marked => 25,
        None if has_reuse_budget_failure(
            &candidate.reuse_score_report,
            LibraryGrowthBudgetFailureKind::DuplicateStatus,
        ) =>
        {
            300
        }
        _ => 0,
    }
}

fn promotion_ranking_package_growth_penalty(candidate: &PromotionRankingCandidateInput) -> u64 {
    let score = &candidate.reuse_score_report.score_breakdown;
    score
        .certificate_growth_penalty
        .saturating_add(score.environment_growth_penalty)
        .saturating_add(score.index_entry_growth_penalty)
        .saturating_add(score.premise_search_latency_penalty)
}

fn promotion_ranking_package_growth_budget_failures(
    failures: &[LibraryGrowthBudgetFailure],
) -> Vec<LibraryGrowthBudgetFailure> {
    failures
        .iter()
        .filter(|failure| {
            matches!(
                failure.kind,
                LibraryGrowthBudgetFailureKind::CertificateGrowth
                    | LibraryGrowthBudgetFailureKind::EnvironmentGrowth
                    | LibraryGrowthBudgetFailureKind::IndexEntryGrowth
                    | LibraryGrowthBudgetFailureKind::PremiseSearchLatency
                    | LibraryGrowthBudgetFailureKind::ExcessiveImportClosure
            )
        })
        .cloned()
        .collect()
}

fn promotion_ranking_explanation(entry: &PromotionRankingEntry) -> String {
    let mut parts = Vec::new();
    parts.push(format!(
        "{}: score {}",
        entry.decision_label, entry.numeric_score
    ));
    parts.push(format!(
        "reuse {} foundational {} statement_stability {} release_readiness {}",
        entry.reuse_score,
        entry.foundational_value_score,
        entry.statement_stability_score,
        entry.release_readiness_score
    ));
    parts.push(format!(
        "penalties import {} axiom {} duplicate_subsumption {} downstream_migration {} package_growth {}",
        entry.import_cost_penalty,
        entry.axiom_cost_penalty,
        entry.duplicate_subsumption_risk_penalty,
        entry.downstream_migration_cost_penalty,
        entry.package_growth_penalty
    ));
    if entry.hard_rejection_dominates_numeric_rank {
        let reasons = entry
            .hard_rejection_reasons
            .iter()
            .map(|reason| reason.kind.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        parts.push(format!(
            "hard rejection dominates numeric rank: {}",
            reasons
        ));
    }
    if !entry.defer_reasons.is_empty() {
        let reasons = entry
            .defer_reasons
            .iter()
            .map(|reason| reason.kind.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        parts.push(format!("defer reasons: {}", reasons));
    }
    if !entry.package_growth_budget_failures.is_empty() {
        let failures = entry
            .package_growth_budget_failures
            .iter()
            .map(|failure| {
                format!(
                    "{} actual={} limit={}",
                    failure.kind.as_str(),
                    failure.actual,
                    failure.limit
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        parts.push(format!("package-growth budget failures: {}", failures));
    }
    if !entry.metadata_issues.is_empty() {
        let issues = entry
            .metadata_issues
            .iter()
            .map(|issue| issue.kind.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        parts.push(format!("metadata issues: {}", issues));
    }
    parts.join("; ")
}

fn corpus_alias_proposal_hash_unchecked(proposal: &CorpusAliasProposalMetadata) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, CORPUS_ALIAS_PROPOSAL_PROFILE);
    encode_corpus_alias_proposal(&mut out, proposal);
    hash_with_domain("npa.library-growth.corpus-alias-proposal.hash.v1", &out)
}

fn corpus_deprecation_record_hash_unchecked(record: &CorpusDeprecationRecord) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, CORPUS_DEPRECATION_RECORD_PROFILE);
    encode_string(&mut out, &record.deprecated_module);
    encode_string(&mut out, &record.deprecated_declaration_name);
    encode_hash(&mut out, &record.deprecated_statement_hash);
    encode_string(&mut out, &record.replacement_module);
    encode_string(&mut out, &record.replacement_declaration_name);
    encode_hash(&mut out, &record.replacement_statement_hash);
    encode_option_hash(&mut out, record.migration_evidence_hash.as_ref());
    encode_hash(&mut out, &record.alias_proposal.proposal_hash);
    encode_corpus_alias_proposal(&mut out, &record.alias_proposal);
    encode_uvar(&mut out, record.downstream_usages.len() as u64);
    for usage in &record.downstream_usages {
        encode_corpus_downstream_usage(&mut out, usage);
    }
    encode_string(&mut out, &record.intended_removal_version);
    encode_string(&mut out, record.certificate_compatibility.as_str());
    encode_uvar(&mut out, record.theorem_index_history.len() as u64);
    for entry in &record.theorem_index_history {
        encode_corpus_theorem_index_history_entry(&mut out, entry);
    }
    encode_string(&mut out, &record.risk_note);
    encode_string(&mut out, record.public_action.as_str());
    encode_option_hash(&mut out, record.public_compatibility_decision_hash.as_ref());
    hash_with_domain("npa.library-growth.corpus-deprecation-record.hash.v1", &out)
}

fn public_compatibility_decision_hash_unchecked(
    decision: &PublicCompatibilityDecisionRecord,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PUBLIC_COMPATIBILITY_DECISION_PROFILE);
    encode_string(&mut out, decision.action.as_str());
    encode_string(&mut out, &decision.public_module);
    encode_string(&mut out, &decision.public_declaration_name);
    encode_string(&mut out, &decision.replacement_module);
    encode_string(&mut out, &decision.replacement_declaration_name);
    encode_hash(&mut out, &decision.replacement_statement_hash);
    encode_option_string(&mut out, decision.alias_module.as_deref());
    encode_option_string(&mut out, decision.alias_declaration_name.as_deref());
    encode_option_string(&mut out, decision.intended_removal_version.as_deref());
    encode_string(&mut out, decision.certificate_compatibility.as_str());
    encode_uvar(&mut out, decision.theorem_index_history.len() as u64);
    for entry in &decision.theorem_index_history {
        encode_corpus_theorem_index_history_entry(&mut out, entry);
    }
    encode_uvar(&mut out, decision.downstream_usages.len() as u64);
    for usage in &decision.downstream_usages {
        encode_corpus_downstream_usage(&mut out, usage);
    }
    encode_corpus_replacement_verification(&mut out, &decision.replacement_verification);
    encode_string(&mut out, &decision.risk_note);
    hash_with_domain(
        "npa.library-growth.public-compatibility-decision.hash.v1",
        &out,
    )
}

fn corpus_theorem_index_history_hash_unchecked(history: &[CorpusTheoremIndexHistoryEntry]) -> Hash {
    let mut out = Vec::new();
    encode_string(
        &mut out,
        "npa.library-growth.corpus-theorem-index-history.v1",
    );
    encode_uvar(&mut out, history.len() as u64);
    for entry in history {
        encode_corpus_theorem_index_history_entry(&mut out, entry);
    }
    hash_with_domain(
        "npa.library-growth.corpus-theorem-index-history.hash.v1",
        &out,
    )
}

fn corpus_deprecated_theorem_index_entry_hash_unchecked(
    entry: &CorpusDeprecatedTheoremIndexEntry,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, CORPUS_DEPRECATED_THEOREM_INDEX_ENTRY_PROFILE);
    encode_string(&mut out, &entry.module);
    encode_string(&mut out, &entry.declaration_name);
    encode_hash(&mut out, &entry.statement_hash);
    encode_bool(&mut out, entry.deprecated);
    encode_option_string(&mut out, entry.replacement_module.as_deref());
    encode_option_string(&mut out, entry.replacement_declaration_name.as_deref());
    encode_option_hash(&mut out, entry.replacement_statement_hash.as_ref());
    encode_bool(&mut out, entry.preferred_retrieval);
    encode_hash(&mut out, &entry.theorem_index_history_hash);
    match entry.alias_scope {
        Some(scope) => {
            out.push(0x01);
            encode_string(&mut out, scope.as_str());
        }
        None => out.push(0x00),
    }
    hash_with_domain(
        "npa.library-growth.corpus-deprecated-theorem-index-entry.hash.v1",
        &out,
    )
}

fn promotion_judgment_input_hash_unchecked(input: &PromotionJudgmentInput) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PROMOTION_JUDGMENT_INPUT_PROFILE);
    encode_string(&mut out, &input.candidate_id);
    encode_option_hash(&mut out, input.theorem_card_hash.as_ref());
    encode_hash(&mut out, &input.artifact.artifact_identity_hash);
    encode_hash(&mut out, &input.reuse_score_report.report_hash);
    match input.duplicate_review_report.as_ref() {
        Some(report) => {
            out.push(0x01);
            encode_hash(&mut out, &report.report_hash);
        }
        None => out.push(0x00),
    }
    encode_option_hash(&mut out, input.closure_audit_hash.as_ref());
    encode_option_hash(&mut out, input.source_free_verification_hash.as_ref());
    encode_option_hash(&mut out, input.import_closure_hash.as_ref());
    encode_option_hash(&mut out, input.axiom_policy_hash.as_ref());
    encode_option_hash(&mut out, input.axiom_report_hash.as_ref());
    encode_option_hash(&mut out, input.naming_review_hash.as_ref());
    encode_option_hash(&mut out, input.api_review_hash.as_ref());
    encode_option_hash(&mut out, input.compatibility_decision_hash.as_ref());
    encode_option_hash(&mut out, input.downstream_plan_hash.as_ref());
    encode_option_hash(&mut out, input.promotion_runbook_hash.as_ref());
    let mut unresolved_imports = input.unresolved_imports.clone();
    unresolved_imports.sort();
    unresolved_imports.dedup();
    encode_uvar(&mut out, unresolved_imports.len() as u64);
    for unresolved_import in unresolved_imports {
        encode_string(&mut out, &unresolved_import);
    }
    encode_bool(&mut out, input.statement_stability_confirmed);
    hash_with_domain("npa.library-growth.promotion-judgment-input.hash.v1", &out)
}

fn collect_promotion_judgment_hard_rejection_reasons(
    input: &PromotionJudgmentInput,
) -> Vec<PromotionJudgmentReason> {
    let mut reasons = Vec::new();
    match input.artifact.theorem_level {
        TheoremLevel::Unknown => push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::UnknownTheoremLevel,
            "theorem level is unknown; public promotion requires explicit L2 Derived certificate evidence",
        ),
        level if !level.is_l2_derived_certificate() => push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::NonL2TheoremLevel,
            format!(
                "theorem level `{}` is not L2 Derived certificate",
                level.as_str()
            ),
        ),
        _ => {}
    }
    if input.artifact.conclusion_assuming {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::ConclusionAssuming,
            "artifact is marked conclusion-assuming",
        );
    }
    if input.artifact.replay_is_stale || input.artifact.import_closure_is_stale {
        let mut stale_parts = Vec::new();
        if input.artifact.replay_is_stale {
            stale_parts.push("replay");
        }
        if input.artifact.import_closure_is_stale {
            stale_parts.push("import_closure");
        }
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::StaleArtifact,
            format!("stale artifact components: {}", stale_parts.join(", ")),
        );
    }
    if !input.unresolved_imports.is_empty() {
        let mut unresolved_imports = input.unresolved_imports.clone();
        unresolved_imports.sort();
        unresolved_imports.dedup();
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::UnresolvedImport,
            format!("unresolved imports: {}", unresolved_imports.join(", ")),
        );
    }
    if input.artifact.axiom_policy_widened
        || has_reuse_budget_failure(
            &input.reuse_score_report,
            LibraryGrowthBudgetFailureKind::WidenedAxiomPolicy,
        )
    {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::WidenedAxiomPolicy,
            "candidate widens the accepted axiom policy",
        );
    }
    if let Some(duplicate_report) = &input.duplicate_review_report {
        if duplicate_report.relation_kind.is_duplicate()
            && duplicate_report.public_promotion_blocked
        {
            push_promotion_judgment_reason(
                &mut reasons,
                PromotionJudgmentReasonKind::Duplicate,
                format!(
                    "duplicate relation `{}` blocks public promotion without a compatibility alias",
                    duplicate_report.relation_kind.as_str()
                ),
            );
        }
    }
    if input.compatibility_decision_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::UnresolvedCompatibility,
            "compatibility decision evidence is missing",
        );
    }
    if input.closure_audit_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingClosureAudit,
            "closure audit evidence is missing",
        );
    }
    reasons
}

fn collect_promotion_judgment_defer_reasons(
    input: &PromotionJudgmentInput,
) -> Vec<PromotionJudgmentReason> {
    let mut reasons = Vec::new();
    if input.theorem_card_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingTheoremCard,
            "theorem-card evidence is missing",
        );
    }
    if input.source_free_verification_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingSourceFreeVerification,
            "source-free verification evidence is missing",
        );
    }
    if input.import_closure_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingImportClosure,
            "import-closure evidence is missing",
        );
    }
    if input.axiom_policy_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingAxiomPolicy,
            "axiom-policy evidence is missing",
        );
    }
    if input.naming_review_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingNamingReview,
            "naming review evidence is missing",
        );
    }
    if input.api_review_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingApiReview,
            "API review evidence is missing",
        );
    }
    if input.downstream_plan_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingDownstreamPlan,
            "downstream plan evidence is missing",
        );
    }
    if input.promotion_runbook_hash.is_none() {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::MissingPromotionRunbook,
            "promotion runbook evidence is missing",
        );
    }
    if input.artifact.promotion_intent != TheoremInventionPromotionIntent::PromotionReady {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::PromotionIntentNotReady,
            format!(
                "promotion intent is `{}`",
                input.artifact.promotion_intent.as_str()
            ),
        );
    }

    let defer_budget_failures = promotion_judgment_defer_budget_failures(input);
    if !defer_budget_failures.is_empty() {
        let detail = defer_budget_failures
            .iter()
            .map(|failure| failure.kind.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::BudgetFailure,
            format!("library-growth budget failures: {detail}"),
        );
    }
    if input.reuse_score_report.public_readiness_score == 0 {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::InsufficientReuse,
            "public readiness score is zero",
        );
    }
    if !input.statement_stability_confirmed {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::UnstableStatement,
            "statement stability has not been confirmed",
        );
    }
    if promotion_judgment_duplicate_review_incomplete(input) {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::DuplicateReviewIncomplete,
            "duplicate/subsumption review is unresolved for public promotion",
        );
    }
    if !input.reuse_score_report.public_package_ready_for_review
        && input.reuse_score_report.budget_failures.is_empty()
    {
        push_promotion_judgment_reason(
            &mut reasons,
            PromotionJudgmentReasonKind::ReuseScoreNotReady,
            "reuse score has not marked the candidate ready for public review",
        );
    }
    reasons
}

fn promotion_judgment_defer_budget_failures(
    input: &PromotionJudgmentInput,
) -> Vec<&LibraryGrowthBudgetFailure> {
    input
        .reuse_score_report
        .budget_failures
        .iter()
        .filter(|failure| {
            !matches!(
                failure.kind,
                LibraryGrowthBudgetFailureKind::WidenedAxiomPolicy
                    | LibraryGrowthBudgetFailureKind::UnknownTheoremLevel
                    | LibraryGrowthBudgetFailureKind::NonL2TheoremLevel
            )
        })
        .collect()
}

fn promotion_judgment_duplicate_review_incomplete(input: &PromotionJudgmentInput) -> bool {
    match input.duplicate_review_report.as_ref() {
        Some(report) => {
            report.public_promotion_blocked
                && (!report.relation_kind.is_duplicate() || report.compatibility_alias_marked)
        }
        None => has_reuse_budget_failure(
            &input.reuse_score_report,
            LibraryGrowthBudgetFailureKind::DuplicateStatus,
        ),
    }
}

fn has_reuse_budget_failure(
    report: &LibraryReuseScoreReport,
    kind: LibraryGrowthBudgetFailureKind,
) -> bool {
    report
        .budget_failures
        .iter()
        .any(|failure| failure.kind == kind)
}

fn push_promotion_judgment_reason(
    reasons: &mut Vec<PromotionJudgmentReason>,
    kind: PromotionJudgmentReasonKind,
    detail: impl Into<String>,
) {
    if reasons.iter().any(|reason| reason.kind == kind) {
        return;
    }
    reasons.push(PromotionJudgmentReason {
        kind,
        detail: detail.into(),
    });
}

fn promotion_judgment_audit_text(
    input: &PromotionJudgmentInput,
    input_hash: Hash,
    decision: PromotionJudgmentDecision,
    hard_rejection_reasons: &[PromotionJudgmentReason],
    defer_reasons: &[PromotionJudgmentReason],
    public_promotion_allowed: bool,
) -> String {
    let mut out = String::new();
    out.push_str("## Promotion Judgment\n\n");
    out.push_str(&format!("- Candidate: `{}`\n", input.candidate_id));
    out.push_str(&format!(
        "- Theorem: `{}`::`{}`\n",
        input.artifact.target_proof_corpus_module, input.artifact.declaration_name
    ));
    out.push_str(&format!(
        "- Decision: `{}` ({})\n",
        decision.as_str(),
        decision.audit_label()
    ));
    out.push_str(&format!(
        "- Input hash: `{}`\n",
        format_hash_string(&input_hash)
    ));
    out.push_str(&format!(
        "- Theorem level: `{}`",
        input.artifact.theorem_level.as_str()
    ));
    if input.artifact.theorem_level.is_l2_derived_certificate() {
        out.push_str(" (L2 Derived certificate)");
    }
    out.push('\n');
    out.push_str(&format!(
        "- Public promotion allowed: `{}`\n",
        public_promotion_allowed
    ));
    out.push_str("- Staged artifact preservation: `true`\n\n");
    out.push_str("### Evidence\n\n");
    out.push_str(&promotion_judgment_hash_line(
        "theorem_card_hash",
        input.theorem_card_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "artifact_identity_hash",
        Some(&input.artifact.artifact_identity_hash),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "reuse_score_report_hash",
        Some(&input.reuse_score_report.report_hash),
    ));
    let duplicate_report_hash = input
        .duplicate_review_report
        .as_ref()
        .map(|report| &report.report_hash);
    out.push_str(&promotion_judgment_hash_line(
        "duplicate_review_report_hash",
        duplicate_report_hash,
    ));
    out.push_str(&promotion_judgment_hash_line(
        "closure_audit_hash",
        input.closure_audit_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "source_free_verification_hash",
        input.source_free_verification_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "import_closure_hash",
        input.import_closure_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "axiom_policy_hash",
        input.axiom_policy_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "axiom_report_hash",
        input.axiom_report_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "naming_review_hash",
        input.naming_review_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "api_review_hash",
        input.api_review_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "compatibility_decision_hash",
        input.compatibility_decision_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "downstream_plan_hash",
        input.downstream_plan_hash.as_ref(),
    ));
    out.push_str(&promotion_judgment_hash_line(
        "promotion_runbook_hash",
        input.promotion_runbook_hash.as_ref(),
    ));
    out.push('\n');
    out.push_str("### Hard Rejection Reasons\n\n");
    promotion_judgment_reason_lines(&mut out, hard_rejection_reasons);
    out.push('\n');
    out.push_str("### Defer Reasons\n\n");
    promotion_judgment_reason_lines(&mut out, defer_reasons);
    out
}

fn promotion_judgment_hash_line(label: &str, hash: Option<&Hash>) -> String {
    match hash {
        Some(hash) => format!("- {label}: `{}`\n", format_hash_string(hash)),
        None => format!("- {label}: `missing`\n"),
    }
}

fn promotion_judgment_reason_lines(out: &mut String, reasons: &[PromotionJudgmentReason]) {
    if reasons.is_empty() {
        out.push_str("- `none`\n");
        return;
    }
    for reason in reasons {
        out.push_str(&format!(
            "- `{}`: {}\n",
            reason.kind.as_str(),
            reason.detail
        ));
    }
}

fn validate_theorem_duplicate_identity(
    identity: &TheoremDuplicateIdentity,
    existing: bool,
) -> Result<(), TheoremDuplicateReviewError> {
    let module_field = if existing {
        TheoremDuplicateField::ExistingModule
    } else {
        TheoremDuplicateField::ProposedModule
    };
    let declaration_field = if existing {
        TheoremDuplicateField::ExistingDeclarationName
    } else {
        TheoremDuplicateField::ProposedDeclarationName
    };
    validate_theorem_duplicate_identifier(module_field, &identity.module)?;
    validate_theorem_duplicate_identifier(declaration_field, &identity.declaration_name)?;
    if identity.normalized_statement.is_empty() {
        return Err(TheoremDuplicateReviewError::EmptyIdentifier {
            field: TheoremDuplicateField::NormalizedStatement,
        });
    }
    for module in &identity.import_closure_modules {
        validate_theorem_duplicate_identifier(module_field, module)?;
    }
    Ok(())
}

fn validate_theorem_duplicate_identity_for_hash(
    identity: &TheoremDuplicateIdentity,
) -> Result<(), TheoremDuplicateReviewError> {
    validate_theorem_duplicate_identifier(TheoremDuplicateField::Module, &identity.module)?;
    validate_theorem_duplicate_identifier(
        TheoremDuplicateField::DeclarationName,
        &identity.declaration_name,
    )?;
    if identity.normalized_statement.is_empty() {
        return Err(TheoremDuplicateReviewError::EmptyIdentifier {
            field: TheoremDuplicateField::NormalizedStatement,
        });
    }
    for module in &identity.import_closure_modules {
        validate_theorem_duplicate_identifier(TheoremDuplicateField::Module, module)?;
    }
    Ok(())
}

fn validate_theorem_duplicate_identifier(
    field: TheoremDuplicateField,
    value: &str,
) -> Result<(), TheoremDuplicateReviewError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(TheoremDuplicateReviewError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn theorem_duplicate_relation(
    existing: &TheoremDuplicateIdentity,
    proposed: &TheoremDuplicateIdentity,
    mutual_implication: Option<&TheoremDuplicateMutualImplicationEvidence>,
) -> (
    TheoremDuplicateRelationKind,
    Vec<TheoremDuplicateReviewStage>,
    Option<String>,
) {
    if existing.statement_hash == proposed.statement_hash {
        return (
            TheoremDuplicateRelationKind::ExactStatementHash,
            vec![TheoremDuplicateReviewStage::StatementHash],
            None,
        );
    }
    if existing.alpha_equivalence_hash == proposed.alpha_equivalence_hash {
        return (
            TheoremDuplicateRelationKind::AlphaEquivalent,
            vec![
                TheoremDuplicateReviewStage::StatementHash,
                TheoremDuplicateReviewStage::AlphaEquivalence,
            ],
            None,
        );
    }
    if let (Some(existing_normal), Some(proposed_normal)) = (
        existing.reducible_normal_form_hash.as_ref(),
        proposed.reducible_normal_form_hash.as_ref(),
    ) {
        if existing_normal == proposed_normal {
            return (
                TheoremDuplicateRelationKind::ReduciblyEqual,
                vec![
                    TheoremDuplicateReviewStage::StatementHash,
                    TheoremDuplicateReviewStage::AlphaEquivalence,
                    TheoremDuplicateReviewStage::ReducibleNormalization,
                ],
                None,
            );
        }
    }

    let mut stages = vec![
        TheoremDuplicateReviewStage::StatementHash,
        TheoremDuplicateReviewStage::AlphaEquivalence,
        TheoremDuplicateReviewStage::ReducibleNormalization,
        TheoremDuplicateReviewStage::MutualImplication,
    ];
    let Some(evidence) = mutual_implication else {
        stages.push(TheoremDuplicateReviewStage::HumanReviewQueue);
        return (
            TheoremDuplicateRelationKind::Inconclusive,
            stages,
            Some("mutual implication check not supplied".to_owned()),
        );
    };
    if let Some(reason) = &evidence.skipped_reason {
        stages.push(TheoremDuplicateReviewStage::HumanReviewQueue);
        return (
            TheoremDuplicateRelationKind::Inconclusive,
            stages,
            Some(reason.clone()),
        );
    }
    let relation = match (
        evidence.existing_implies_proposed,
        evidence.proposed_implies_existing,
    ) {
        (Some(true), Some(true)) => TheoremDuplicateRelationKind::MutualImplicationEquivalent,
        (Some(true), Some(false)) => TheoremDuplicateRelationKind::ProposedWeaker,
        (Some(false), Some(true)) => TheoremDuplicateRelationKind::ProposedStronger,
        _ => {
            stages.push(TheoremDuplicateReviewStage::HumanReviewQueue);
            return (
                TheoremDuplicateRelationKind::Inconclusive,
                stages,
                Some("mutual implication result incomplete".to_owned()),
            );
        }
    };
    if matches!(
        relation,
        TheoremDuplicateRelationKind::ProposedStronger
            | TheoremDuplicateRelationKind::ProposedWeaker
    ) {
        stages.push(TheoremDuplicateReviewStage::HumanReviewQueue);
    }
    (relation, stages, None)
}

fn theorem_duplicate_review_stages_consistent(
    relation: TheoremDuplicateRelationKind,
    stages: &[TheoremDuplicateReviewStage],
) -> bool {
    match relation {
        TheoremDuplicateRelationKind::ExactStatementHash => {
            stages == [TheoremDuplicateReviewStage::StatementHash].as_slice()
        }
        TheoremDuplicateRelationKind::AlphaEquivalent => {
            stages
                == [
                    TheoremDuplicateReviewStage::StatementHash,
                    TheoremDuplicateReviewStage::AlphaEquivalence,
                ]
                .as_slice()
        }
        TheoremDuplicateRelationKind::ReduciblyEqual => {
            stages
                == [
                    TheoremDuplicateReviewStage::StatementHash,
                    TheoremDuplicateReviewStage::AlphaEquivalence,
                    TheoremDuplicateReviewStage::ReducibleNormalization,
                ]
                .as_slice()
        }
        TheoremDuplicateRelationKind::MutualImplicationEquivalent => {
            stages
                == [
                    TheoremDuplicateReviewStage::StatementHash,
                    TheoremDuplicateReviewStage::AlphaEquivalence,
                    TheoremDuplicateReviewStage::ReducibleNormalization,
                    TheoremDuplicateReviewStage::MutualImplication,
                ]
                .as_slice()
        }
        TheoremDuplicateRelationKind::ProposedStronger
        | TheoremDuplicateRelationKind::ProposedWeaker
        | TheoremDuplicateRelationKind::Inconclusive => {
            stages
                == [
                    TheoremDuplicateReviewStage::StatementHash,
                    TheoremDuplicateReviewStage::AlphaEquivalence,
                    TheoremDuplicateReviewStage::ReducibleNormalization,
                    TheoremDuplicateReviewStage::MutualImplication,
                    TheoremDuplicateReviewStage::HumanReviewQueue,
                ]
                .as_slice()
        }
    }
}

fn theorem_duplicate_recommended_action(
    relation: TheoremDuplicateRelationKind,
    compatibility_alias_marked: bool,
) -> TheoremDuplicateRecommendedAction {
    if relation.is_duplicate() {
        if compatibility_alias_marked {
            TheoremDuplicateRecommendedAction::CompatibilityAliasReview
        } else {
            TheoremDuplicateRecommendedAction::RejectBeforeProofTask
        }
    } else if matches!(
        relation,
        TheoremDuplicateRelationKind::ProposedStronger
            | TheoremDuplicateRelationKind::ProposedWeaker
    ) {
        TheoremDuplicateRecommendedAction::ReviewSubsumption
    } else {
        TheoremDuplicateRecommendedAction::KeepStaged
    }
}

fn theorem_duplicate_import_cost_comparison(
    existing: &TheoremDuplicateIdentity,
    proposed: &TheoremDuplicateIdentity,
) -> TheoremDuplicateImportCostComparison {
    let existing_set = existing
        .import_closure_modules
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let proposed_set = proposed
        .import_closure_modules
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let proposed_only_import_modules = proposed_set
        .difference(&existing_set)
        .cloned()
        .collect::<Vec<_>>();
    let existing_only_import_modules = existing_set
        .difference(&proposed_set)
        .cloned()
        .collect::<Vec<_>>();
    let existing_import_closure_modules = existing_set.len() as u64;
    let proposed_import_closure_modules = proposed_set.len() as u64;
    let ordering = if existing_import_closure_modules < proposed_import_closure_modules {
        TheoremDuplicateCostOrdering::ExistingLower
    } else if proposed_import_closure_modules < existing_import_closure_modules {
        TheoremDuplicateCostOrdering::ProposedLower
    } else {
        TheoremDuplicateCostOrdering::Equal
    };
    TheoremDuplicateImportCostComparison {
        existing_import_closure_modules,
        proposed_import_closure_modules,
        proposed_only_import_modules,
        existing_only_import_modules,
        ordering,
    }
}

fn theorem_duplicate_axiom_policy_comparison(
    existing: &TheoremDuplicateIdentity,
    proposed: &TheoremDuplicateIdentity,
) -> TheoremDuplicateAxiomPolicyComparison {
    let relation = if existing.axiom_policy_hash == proposed.axiom_policy_hash
        && existing.axiom_cost == proposed.axiom_cost
    {
        TheoremDuplicateAxiomPolicyRelation::Same
    } else if proposed.axiom_cost > existing.axiom_cost {
        TheoremDuplicateAxiomPolicyRelation::ProposedWidens
    } else if proposed.axiom_cost < existing.axiom_cost {
        TheoremDuplicateAxiomPolicyRelation::ProposedNarrows
    } else {
        TheoremDuplicateAxiomPolicyRelation::ChangedUnknown
    };
    TheoremDuplicateAxiomPolicyComparison {
        existing_axiom_policy_hash: existing.axiom_policy_hash,
        proposed_axiom_policy_hash: proposed.axiom_policy_hash,
        existing_axiom_cost: existing.axiom_cost,
        proposed_axiom_cost: proposed.axiom_cost,
        relation,
    }
}

fn validate_lemma_generalization_input(
    input: &LemmaGeneralizationInput,
) -> Result<(), LemmaGeneralizationError> {
    let mut local_ids = BTreeSet::new();
    for local in &input.locals {
        validate_lemma_identifier(LemmaGeneralizationField::LocalId, &local.local_id)?;
        if !local_ids.insert(local.local_id.clone()) {
            return Err(LemmaGeneralizationError::DuplicateLocal {
                local_id: local.local_id.clone(),
            });
        }
        for dependency in &local.depends_on_local_ids {
            validate_lemma_identifier(LemmaGeneralizationField::LocalId, dependency)?;
        }
    }
    for local in &input.locals {
        for dependency in &local.depends_on_local_ids {
            if !local_ids.contains(dependency) {
                return Err(LemmaGeneralizationError::UnknownLocalDependency {
                    local_id: local.local_id.clone(),
                    dependency_local_id: dependency.clone(),
                });
            }
        }
    }
    for premise in &input.premises {
        validate_lemma_identifier(LemmaGeneralizationField::PremiseId, &premise.premise_id)?;
        for dependency in &premise.depends_on_local_ids {
            if !local_ids.contains(dependency) {
                return Err(LemmaGeneralizationError::UnknownLocalDependency {
                    local_id: premise.premise_id.clone(),
                    dependency_local_id: dependency.clone(),
                });
            }
        }
    }
    for constant in &input.constants {
        validate_lemma_identifier(LemmaGeneralizationField::ConstantId, &constant.constant_id)?;
        if let Some(module) = constant.import_module.as_ref() {
            validate_lemma_identifier(LemmaGeneralizationField::ImportModule, module)?;
        }
    }
    for equality in &input.equality_candidates {
        validate_lemma_identifier(LemmaGeneralizationField::EqualityId, &equality.equality_id)?;
    }
    for structure in &input.structure_candidates {
        validate_lemma_identifier(
            LemmaGeneralizationField::StructureId,
            &structure.structure_id,
        )?;
    }
    for carrier in &input.carrier_candidates {
        validate_lemma_identifier(LemmaGeneralizationField::CarrierId, &carrier.carrier_id)?;
    }
    for import in &input.import_candidates {
        validate_lemma_identifier(LemmaGeneralizationField::ImportModule, &import.module)?;
    }
    topological_local_order(&input.locals).map(|_| ())
}

fn retained_normalization_premises(
    input: &LemmaGeneralizationInput,
) -> Vec<StatementNormalizationPremise> {
    sorted_premises(&input.premises)
        .into_iter()
        .filter(|premise| premise.occurrence_count > 0 || premise.required_for_typecheck)
        .map(statement_premise_from_input)
        .collect()
}

fn removed_normalization_premises(
    input: &LemmaGeneralizationInput,
) -> Vec<StatementNormalizationPremise> {
    sorted_premises(&input.premises)
        .into_iter()
        .filter(|premise| premise.occurrence_count == 0 && !premise.required_for_typecheck)
        .map(statement_premise_from_input)
        .collect()
}

fn statement_normalization_binder_order(
    input: &LemmaGeneralizationInput,
    retained_premises: &[StatementNormalizationPremise],
) -> Result<Vec<StatementNormalizationBinder>, LemmaGeneralizationError> {
    let local_by_id = input
        .locals
        .iter()
        .map(|local| (local.local_id.clone(), local))
        .collect::<BTreeMap<_, _>>();
    let retained_premise_ids = retained_premises
        .iter()
        .map(|premise| premise.premise_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut needed = BTreeSet::<String>::new();
    for local in &input.locals {
        if local.occurrence_count > 0 {
            collect_local_with_dependencies(local, &local_by_id, &mut needed)?;
        }
    }
    for premise in &input.premises {
        if retained_premise_ids.contains(premise.premise_id.as_str()) {
            for dependency in &premise.depends_on_local_ids {
                let Some(local) = local_by_id.get(dependency) else {
                    return Err(LemmaGeneralizationError::UnknownLocalDependency {
                        local_id: premise.premise_id.clone(),
                        dependency_local_id: dependency.clone(),
                    });
                };
                collect_local_with_dependencies(local, &local_by_id, &mut needed)?;
            }
        }
    }
    Ok(topological_local_order(&input.locals)?
        .into_iter()
        .filter(|local| needed.contains(&local.local_id))
        .map(|local| StatementNormalizationBinder {
            local_id: local.local_id.clone(),
            type_hash: local.type_hash,
            value_hash: local.value_hash,
            binder_kind: local.binder_kind,
        })
        .collect())
}

fn topological_local_order(
    locals: &[LemmaGeneralizationLocal],
) -> Result<Vec<&LemmaGeneralizationLocal>, LemmaGeneralizationError> {
    let mut local_by_id = BTreeMap::new();
    let mut remaining = BTreeSet::new();
    for local in locals {
        if local_by_id.insert(local.local_id.clone(), local).is_some() {
            return Err(LemmaGeneralizationError::DuplicateLocal {
                local_id: local.local_id.clone(),
            });
        }
        remaining.insert(local.local_id.clone());
    }

    let mut emitted = BTreeSet::new();
    let mut out = Vec::new();
    while !remaining.is_empty() {
        let ready = remaining
            .iter()
            .filter(|local_id| {
                local_by_id[*local_id]
                    .depends_on_local_ids
                    .iter()
                    .all(|dependency| emitted.contains(dependency))
            })
            .cloned()
            .collect::<Vec<_>>();
        if ready.is_empty() {
            return Err(LemmaGeneralizationError::DependencyCycle {
                local_ids: remaining.into_iter().collect(),
            });
        }
        for local_id in ready {
            remaining.remove(&local_id);
            emitted.insert(local_id.clone());
            out.push(local_by_id[&local_id]);
        }
    }
    Ok(out)
}

fn collect_local_with_dependencies(
    local: &LemmaGeneralizationLocal,
    local_by_id: &BTreeMap<String, &LemmaGeneralizationLocal>,
    needed: &mut BTreeSet<String>,
) -> Result<(), LemmaGeneralizationError> {
    if !needed.insert(local.local_id.clone()) {
        return Ok(());
    }
    for dependency in &local.depends_on_local_ids {
        let Some(dependency_local) = local_by_id.get(dependency) else {
            return Err(LemmaGeneralizationError::UnknownLocalDependency {
                local_id: local.local_id.clone(),
                dependency_local_id: dependency.clone(),
            });
        };
        collect_local_with_dependencies(dependency_local, local_by_id, needed)?;
    }
    Ok(())
}

fn parameterized_constants(
    input: &LemmaGeneralizationInput,
) -> Result<Vec<StatementNormalizationConstantParameter>, LemmaGeneralizationError> {
    Ok(sorted_constants(&input.constants)
        .into_iter()
        .filter(|constant| constant.may_parameterize)
        .map(|constant| StatementNormalizationConstantParameter {
            constant_id: constant.constant_id.clone(),
            constant_hash: constant.constant_hash,
        })
        .collect())
}

fn equality_orientation_decisions(
    input: &LemmaGeneralizationInput,
) -> Result<Vec<StatementNormalizationEqualityDecision>, LemmaGeneralizationError> {
    Ok(sorted_equalities(&input.equality_candidates)
        .into_iter()
        .map(|equality| {
            let reverse = equality.can_reverse && equality.lhs_size > equality.rhs_size;
            StatementNormalizationEqualityDecision {
                equality_id: equality.equality_id.clone(),
                equality_hash: equality.equality_hash,
                orientation: if reverse {
                    LemmaGeneralizationEqualityOrientation::Reverse
                } else {
                    LemmaGeneralizationEqualityOrientation::Keep
                },
                oriented_lhs_hash: if reverse {
                    equality.rhs_hash
                } else {
                    equality.lhs_hash
                },
                oriented_rhs_hash: if reverse {
                    equality.lhs_hash
                } else {
                    equality.rhs_hash
                },
            }
        })
        .collect())
}

fn selected_weakest_structure(
    input: &LemmaGeneralizationInput,
) -> Option<LemmaGeneralizationStructureKind> {
    sorted_structures(&input.structure_candidates)
        .into_iter()
        .filter(|structure| structure.evidence_hash.is_some())
        .map(|structure| structure.structure)
        .min()
}

fn accepted_carrier_generalizations(
    input: &LemmaGeneralizationInput,
) -> Result<Vec<StatementNormalizationCarrierGeneralization>, LemmaGeneralizationError> {
    Ok(sorted_carriers(&input.carrier_candidates)
        .into_iter()
        .filter_map(|carrier| {
            carrier.evidence_hash.map(
                |evidence_hash| StatementNormalizationCarrierGeneralization {
                    carrier_id: carrier.carrier_id.clone(),
                    kind: carrier.kind,
                    source_hash: carrier.source_hash,
                    generalized_hash: carrier.generalized_hash,
                    evidence_hash,
                },
            )
        })
        .collect())
}

fn statement_normalization_import_needs(
    input: &LemmaGeneralizationInput,
) -> Result<Vec<StatementNormalizationImportNeed>, LemmaGeneralizationError> {
    let mut imports = BTreeMap::<String, Hash>::new();
    for import in &input.import_candidates {
        imports
            .entry(import.module.clone())
            .or_insert(import.reason_hash);
    }
    for constant in &input.constants {
        if let Some(module) = constant.import_module.as_ref() {
            imports
                .entry(module.clone())
                .or_insert(constant.constant_hash);
        }
    }
    Ok(imports
        .into_iter()
        .map(|(module, reason_hash)| StatementNormalizationImportNeed {
            module,
            reason_hash,
        })
        .collect())
}

fn statement_normalization_rejected_attempts(
    input: &LemmaGeneralizationInput,
) -> Vec<StatementNormalizationRejectedAttempt> {
    let mut rejected = Vec::new();
    for premise in sorted_premises(&input.premises) {
        if premise.occurrence_count == 0 && premise.required_for_typecheck {
            rejected.push(StatementNormalizationRejectedAttempt {
                kind: StatementNormalizationRejectedAttemptKind::PremiseMinimization,
                item_id: premise.premise_id.clone(),
                reason: StatementNormalizationRejectionReason::RequiredForTypecheck,
                evidence_hash: Some(premise.premise_hash),
            });
        }
    }
    for structure in sorted_structures(&input.structure_candidates) {
        if structure.evidence_hash.is_none() {
            rejected.push(StatementNormalizationRejectedAttempt {
                kind: StatementNormalizationRejectedAttemptKind::AlgebraicStructure,
                item_id: structure.structure_id.clone(),
                reason: StatementNormalizationRejectionReason::MissingStructureEvidence,
                evidence_hash: None,
            });
        }
    }
    for carrier in sorted_carriers(&input.carrier_candidates) {
        if carrier.evidence_hash.is_none() {
            rejected.push(StatementNormalizationRejectedAttempt {
                kind: StatementNormalizationRejectedAttemptKind::CarrierGeneralization,
                item_id: carrier.carrier_id.clone(),
                reason: StatementNormalizationRejectionReason::MissingCarrierEvidence,
                evidence_hash: None,
            });
        }
    }
    rejected
}

struct GeneralizedStatementHashParts<'a> {
    binder_order: &'a [StatementNormalizationBinder],
    retained_premises: &'a [StatementNormalizationPremise],
    parameterized_constants: &'a [StatementNormalizationConstantParameter],
    equality_orientations: &'a [StatementNormalizationEqualityDecision],
    selected_structure: Option<LemmaGeneralizationStructureKind>,
    carrier_generalizations: &'a [StatementNormalizationCarrierGeneralization],
    import_needs: &'a [StatementNormalizationImportNeed],
}

fn generalized_statement_hash_from_parts(
    input: &LemmaGeneralizationInput,
    parts: GeneralizedStatementHashParts<'_>,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LEMMA_GENERALIZED_STATEMENT_PROFILE);
    encode_hash(&mut out, &input.source_context_hash);
    encode_hash(&mut out, &input.original_goal_hash);
    encode_hash(&mut out, &input.normalized_target_hash);
    encode_uvar(&mut out, parts.binder_order.len() as u64);
    for binder in parts.binder_order {
        encode_binder(&mut out, binder);
    }
    encode_uvar(&mut out, parts.retained_premises.len() as u64);
    for premise in parts.retained_premises {
        encode_statement_premise(&mut out, premise);
    }
    encode_uvar(&mut out, parts.parameterized_constants.len() as u64);
    for constant in parts.parameterized_constants {
        encode_string(&mut out, &constant.constant_id);
        encode_hash(&mut out, &constant.constant_hash);
    }
    encode_uvar(&mut out, parts.equality_orientations.len() as u64);
    for equality in parts.equality_orientations {
        encode_equality_decision(&mut out, equality);
    }
    match parts.selected_structure {
        Some(structure) => {
            out.push(0x01);
            encode_string(&mut out, structure.as_str());
        }
        None => out.push(0x00),
    }
    encode_uvar(&mut out, parts.carrier_generalizations.len() as u64);
    for carrier in parts.carrier_generalizations {
        encode_carrier_generalization(&mut out, carrier);
    }
    encode_uvar(&mut out, parts.import_needs.len() as u64);
    for import in parts.import_needs {
        encode_import_need(&mut out, import);
    }
    hash_with_domain("npa.library-growth.generalized-statement.hash.v1", &out)
}

fn validate_report_binder_dependency_order(
    input: &LemmaGeneralizationInput,
    report: &StatementNormalizationReport,
) -> Result<(), LemmaGeneralizationError> {
    let local_by_id = input
        .locals
        .iter()
        .map(|local| (local.local_id.as_str(), local))
        .collect::<BTreeMap<_, _>>();
    let mut positions = BTreeMap::new();
    for (index, binder) in report.binder_order.iter().enumerate() {
        positions.insert(binder.local_id.as_str(), index);
    }
    for binder in &report.binder_order {
        let Some(local) = local_by_id.get(binder.local_id.as_str()) else {
            return Err(LemmaGeneralizationError::UnknownLocalDependency {
                local_id: binder.local_id.clone(),
                dependency_local_id: binder.local_id.clone(),
            });
        };
        for dependency in &local.depends_on_local_ids {
            let Some(dependency_position) = positions.get(dependency.as_str()) else {
                return Err(LemmaGeneralizationError::DependencyOrderViolation {
                    local_id: binder.local_id.clone(),
                    dependency_local_id: dependency.clone(),
                });
            };
            if *dependency_position >= positions[binder.local_id.as_str()] {
                return Err(LemmaGeneralizationError::DependencyOrderViolation {
                    local_id: binder.local_id.clone(),
                    dependency_local_id: dependency.clone(),
                });
            }
        }
    }
    Ok(())
}

fn validate_lemma_identifier(
    field: LemmaGeneralizationField,
    value: &str,
) -> Result<(), LemmaGeneralizationError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(LemmaGeneralizationError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn validate_subgoal_cluster_key(key: &SubgoalClusterKey) -> Result<(), SubgoalClusterError> {
    for head_symbol in &key.head_symbols {
        validate_non_empty_identifier(SubgoalClusterField::HeadSymbol, head_symbol)?;
    }
    for domain_tag in &key.domain_tags {
        validate_non_empty_identifier(SubgoalClusterField::DomainTag, domain_tag)?;
    }
    for canonicalization in &key.approved_commutative_canonicalizations {
        validate_non_empty_identifier(
            SubgoalClusterField::CommutativeOperatorSymbol,
            &canonicalization.operator_symbol,
        )?;
    }
    Ok(())
}

fn validate_subgoal_parent_example(
    example: &SubgoalClusterParentExample,
) -> Result<(), SubgoalClusterError> {
    validate_non_empty_identifier(
        SubgoalClusterField::ParentSourceModule,
        &example.source_module,
    )?;
    validate_non_empty_identifier(
        SubgoalClusterField::ParentDeclarationName,
        &example.declaration_name,
    )?;
    let expected = subgoal_cluster_parent_example_hash(example);
    if expected != example.example_hash {
        return Err(SubgoalClusterError::ParentExampleHashMismatch {
            expected,
            actual: example.example_hash,
        });
    }
    Ok(())
}

fn validate_library_gap_signal(
    signal: &LibraryGapSignalObservation,
) -> Result<(), SubgoalClusterError> {
    validate_non_empty_identifier(
        SubgoalClusterField::GapSignalSourceModule,
        &signal.source_module,
    )?;
    validate_non_empty_identifier(SubgoalClusterField::GapSignalSourceId, &signal.source_id)?;
    if let Some(module) = signal.proposed_import_module.as_ref() {
        validate_non_empty_identifier(SubgoalClusterField::GapSignalImportModule, module)?;
    }
    let expected = library_gap_signal_hash(signal);
    if expected != signal.signal_hash {
        return Err(SubgoalClusterError::GapSignalHashMismatch {
            expected,
            actual: signal.signal_hash,
        });
    }
    Ok(())
}

fn required_parent_examples(options: &SubgoalClusterOptions) -> usize {
    options
        .min_parent_examples
        .max(SUBGOAL_CLUSTER_MIN_PARENT_EXAMPLES)
}

fn select_likely_proof_strategy(
    counts: &BTreeMap<SubgoalClusterLikelyProofStrategy, u64>,
) -> SubgoalClusterLikelyProofStrategy {
    counts
        .iter()
        .max_by(
            |(left_strategy, left_count), (right_strategy, right_count)| {
                left_count
                    .cmp(right_count)
                    .then_with(|| right_strategy.cmp(left_strategy))
            },
        )
        .map(|(strategy, _)| *strategy)
        .unwrap_or(SubgoalClusterLikelyProofStrategy::Unknown)
}

fn validate_non_empty_identifier(
    field: SubgoalClusterField,
    value: &str,
) -> Result<(), SubgoalClusterError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(SubgoalClusterError::EmptyIdentifier { field })
    } else {
        Ok(())
    }
}

fn sort_dedup_strings(values: &mut Vec<String>) {
    values.sort();
    values.dedup();
}

fn sorted_locals(locals: &[LemmaGeneralizationLocal]) -> Vec<&LemmaGeneralizationLocal> {
    let mut locals = locals.iter().collect::<Vec<_>>();
    locals.sort_by(|left, right| left.local_id.cmp(&right.local_id));
    locals
}

fn sorted_premises(premises: &[LemmaGeneralizationPremise]) -> Vec<&LemmaGeneralizationPremise> {
    let mut premises = premises.iter().collect::<Vec<_>>();
    premises.sort_by(|left, right| left.premise_id.cmp(&right.premise_id));
    premises
}

fn sorted_constants(
    constants: &[LemmaGeneralizationConstantUse],
) -> Vec<&LemmaGeneralizationConstantUse> {
    let mut constants = constants.iter().collect::<Vec<_>>();
    constants.sort_by(|left, right| left.constant_id.cmp(&right.constant_id));
    constants
}

fn sorted_equalities(
    equalities: &[LemmaGeneralizationEqualityCandidate],
) -> Vec<&LemmaGeneralizationEqualityCandidate> {
    let mut equalities = equalities.iter().collect::<Vec<_>>();
    equalities.sort_by(|left, right| left.equality_id.cmp(&right.equality_id));
    equalities
}

fn sorted_structures(
    structures: &[LemmaGeneralizationStructureCandidate],
) -> Vec<&LemmaGeneralizationStructureCandidate> {
    let mut structures = structures.iter().collect::<Vec<_>>();
    structures.sort_by(|left, right| {
        left.structure
            .cmp(&right.structure)
            .then_with(|| left.structure_id.cmp(&right.structure_id))
    });
    structures
}

fn sorted_carriers(
    carriers: &[LemmaGeneralizationCarrierCandidate],
) -> Vec<&LemmaGeneralizationCarrierCandidate> {
    let mut carriers = carriers.iter().collect::<Vec<_>>();
    carriers.sort_by(|left, right| left.carrier_id.cmp(&right.carrier_id));
    carriers
}

fn sorted_imports(
    imports: &[StatementNormalizationImportNeed],
) -> Vec<&StatementNormalizationImportNeed> {
    let mut imports = imports.iter().collect::<Vec<_>>();
    imports.sort_by(|left, right| {
        left.module
            .cmp(&right.module)
            .then_with(|| left.reason_hash.cmp(&right.reason_hash))
    });
    imports
}

fn statement_premise_from_input(
    premise: &LemmaGeneralizationPremise,
) -> StatementNormalizationPremise {
    StatementNormalizationPremise {
        premise_id: premise.premise_id.clone(),
        premise_hash: premise.premise_hash,
    }
}

fn encode_local(out: &mut Vec<u8>, local: &LemmaGeneralizationLocal) {
    encode_string(out, &local.local_id);
    encode_hash(out, &local.type_hash);
    encode_option_hash(out, local.value_hash.as_ref());
    let mut dependencies = local.depends_on_local_ids.clone();
    dependencies.sort();
    dependencies.dedup();
    encode_uvar(out, dependencies.len() as u64);
    for dependency in dependencies {
        encode_string(out, &dependency);
    }
    encode_uvar(out, local.occurrence_count);
    encode_string(out, local.binder_kind.as_str());
}

fn encode_premise(out: &mut Vec<u8>, premise: &LemmaGeneralizationPremise) {
    encode_string(out, &premise.premise_id);
    encode_hash(out, &premise.premise_hash);
    let mut dependencies = premise.depends_on_local_ids.clone();
    dependencies.sort();
    dependencies.dedup();
    encode_uvar(out, dependencies.len() as u64);
    for dependency in dependencies {
        encode_string(out, &dependency);
    }
    encode_uvar(out, premise.occurrence_count);
    encode_bool(out, premise.required_for_typecheck);
}

fn encode_binder(out: &mut Vec<u8>, binder: &StatementNormalizationBinder) {
    encode_string(out, &binder.local_id);
    encode_hash(out, &binder.type_hash);
    encode_option_hash(out, binder.value_hash.as_ref());
    encode_string(out, binder.binder_kind.as_str());
}

fn encode_statement_premise(out: &mut Vec<u8>, premise: &StatementNormalizationPremise) {
    encode_string(out, &premise.premise_id);
    encode_hash(out, &premise.premise_hash);
}

fn encode_equality_decision(out: &mut Vec<u8>, equality: &StatementNormalizationEqualityDecision) {
    encode_string(out, &equality.equality_id);
    encode_hash(out, &equality.equality_hash);
    encode_string(out, equality.orientation.as_str());
    encode_hash(out, &equality.oriented_lhs_hash);
    encode_hash(out, &equality.oriented_rhs_hash);
}

fn encode_carrier_generalization(
    out: &mut Vec<u8>,
    carrier: &StatementNormalizationCarrierGeneralization,
) {
    encode_string(out, &carrier.carrier_id);
    encode_string(out, carrier.kind.as_str());
    encode_hash(out, &carrier.source_hash);
    encode_hash(out, &carrier.generalized_hash);
    encode_hash(out, &carrier.evidence_hash);
}

fn encode_import_need(out: &mut Vec<u8>, import: &StatementNormalizationImportNeed) {
    encode_string(out, &import.module);
    encode_hash(out, &import.reason_hash);
}

fn encode_rejected_attempt(out: &mut Vec<u8>, rejected: &StatementNormalizationRejectedAttempt) {
    encode_string(out, rejected.kind.as_str());
    encode_string(out, &rejected.item_id);
    encode_string(out, rejected.reason.as_str());
    encode_option_hash(out, rejected.evidence_hash.as_ref());
}

fn encode_typecheck_witness(out: &mut Vec<u8>, witness: &StatementNormalizationTypecheckWitness) {
    encode_hash(out, &witness.generalized_statement_hash);
    encode_hash(out, &witness.expected_type_hash);
    encode_hash(out, &witness.environment_hash);
    encode_hash(out, &witness.witness_hash);
}

fn encode_library_reuse_score_breakdown(out: &mut Vec<u8>, score: &LibraryReuseScoreBreakdown) {
    encode_uvar(out, score.downstream_unlock_score);
    encode_uvar(out, score.repeated_parent_goal_score);
    encode_uvar(out, score.proof_shortening_score);
    encode_uvar(out, score.statement_stability_score);
    encode_uvar(out, score.proof_difficulty_score);
    encode_uvar(out, score.import_closure_penalty);
    encode_uvar(out, score.axiom_cost_penalty);
    encode_uvar(out, score.certificate_growth_penalty);
    encode_uvar(out, score.environment_growth_penalty);
    encode_uvar(out, score.index_entry_growth_penalty);
    encode_uvar(out, score.premise_search_latency_penalty);
}

fn encode_library_growth_budget_failure(out: &mut Vec<u8>, failure: &LibraryGrowthBudgetFailure) {
    encode_string(out, failure.kind.as_str());
    encode_uvar(out, failure.actual);
    encode_uvar(out, failure.limit);
}

fn encode_promotion_judgment_reason(out: &mut Vec<u8>, reason: &PromotionJudgmentReason) {
    encode_string(out, reason.kind.as_str());
    encode_string(out, &reason.detail);
}

fn encode_promotion_metadata_file_evidence(
    out: &mut Vec<u8>,
    evidence: &PromotionMetadataFileEvidence,
) {
    encode_string(out, &evidence.path);
    encode_option_hash(out, evidence.hash.as_ref());
    encode_bool(out, evidence.stale);
}

fn encode_promotion_metadata_verification_evidence(
    out: &mut Vec<u8>,
    evidence: &PromotionMetadataVerificationEvidence,
) {
    encode_string(out, &evidence.command);
    encode_option_hash(out, evidence.command_hash.as_ref());
    encode_bool(out, evidence.stale);
}

fn encode_promotion_metadata_theorem_index_evidence(
    out: &mut Vec<u8>,
    evidence: &PromotionMetadataTheoremIndexEvidence,
) {
    encode_promotion_metadata_file_evidence(out, &evidence.file);
    encode_uvar(out, evidence.entries.len() as u64);
    for entry in &evidence.entries {
        encode_string(out, &entry.module);
        encode_string(out, &entry.declaration_name);
        encode_string(out, entry.theorem_level.as_str());
        encode_hash(out, &entry.certificate_hash);
    }
}

fn encode_promotion_metadata_publish_plan_evidence(
    out: &mut Vec<u8>,
    evidence: &PromotionMetadataPublishPlanEvidence,
) {
    encode_promotion_metadata_file_evidence(out, &evidence.file);
    encode_uvar(out, evidence.entries.len() as u64);
    for entry in &evidence.entries {
        encode_string(out, &entry.module);
        encode_string(out, &entry.release_target);
    }
}

fn encode_promotion_metadata_issue(out: &mut Vec<u8>, issue: &PromotionMetadataIssue) {
    encode_string(out, issue.kind.as_str());
    encode_string(out, issue.field.as_str());
    encode_string(out, &issue.detail);
}

fn encode_promotion_ranking_entry(out: &mut Vec<u8>, entry: &PromotionRankingEntry) {
    encode_uvar(out, entry.rank);
    encode_hash(out, &entry.ranking_identity_hash);
    encode_string(out, &entry.candidate_id);
    encode_string(out, &entry.target_module);
    encode_string(out, &entry.declaration_name);
    encode_string(out, entry.theorem_level.as_str());
    encode_string(out, entry.decision.as_str());
    encode_string(out, &entry.decision_label);
    encode_bool(out, entry.hard_rejection_dominates_numeric_rank);
    encode_uvar(out, entry.numeric_score);
    encode_uvar(out, entry.reuse_score);
    encode_uvar(out, entry.foundational_value_score);
    encode_uvar(out, entry.statement_stability_score);
    encode_uvar(out, entry.release_readiness_score);
    encode_uvar(out, entry.import_cost_penalty);
    encode_uvar(out, entry.axiom_cost_penalty);
    encode_uvar(out, entry.duplicate_subsumption_risk_penalty);
    encode_uvar(out, entry.downstream_migration_cost_penalty);
    encode_uvar(out, entry.package_growth_penalty);
    encode_uvar(out, entry.package_growth_budget_failures.len() as u64);
    for failure in &entry.package_growth_budget_failures {
        encode_library_growth_budget_failure(out, failure);
    }
    encode_uvar(out, entry.hard_rejection_reasons.len() as u64);
    for reason in &entry.hard_rejection_reasons {
        encode_promotion_judgment_reason(out, reason);
    }
    encode_uvar(out, entry.defer_reasons.len() as u64);
    for reason in &entry.defer_reasons {
        encode_promotion_judgment_reason(out, reason);
    }
    encode_uvar(out, entry.metadata_issues.len() as u64);
    for issue in &entry.metadata_issues {
        encode_promotion_metadata_issue(out, issue);
    }
    encode_promotion_ranking_evidence_hashes(out, &entry.evidence_hashes);
    encode_string(out, &entry.rank_explanation);
}

fn encode_promotion_ranking_evidence_hashes(
    out: &mut Vec<u8>,
    hashes: &PromotionRankingEvidenceHashes,
) {
    encode_hash(out, &hashes.reuse_score_report_hash);
    encode_option_hash(out, hashes.duplicate_review_report_hash.as_ref());
    encode_hash(out, &hashes.promotion_judgment_report_hash);
    encode_hash(out, &hashes.promotion_metadata_report_hash);
    encode_option_hash(out, hashes.import_closure_hash.as_ref());
    encode_option_hash(out, hashes.axiom_report_hash.as_ref());
    encode_option_hash(out, hashes.performance_budget_report_hash.as_ref());
    encode_option_hash(out, hashes.theorem_card_metadata_hash.as_ref());
    encode_option_hash(out, hashes.downstream_plan_hash.as_ref());
}

fn encode_corpus_alias_proposal(out: &mut Vec<u8>, proposal: &CorpusAliasProposalMetadata) {
    encode_string(out, proposal.alias_scope.as_str());
    encode_string(out, proposal.migration_evidence_kind.as_str());
    encode_string(out, &proposal.alias_module);
    encode_string(out, &proposal.alias_declaration_name);
    encode_string(out, &proposal.replacement_module);
    encode_string(out, &proposal.replacement_declaration_name);
    encode_hash(out, &proposal.replacement_statement_hash);
    encode_option_hash(out, proposal.migration_evidence_hash.as_ref());
    encode_uvar(out, proposal.downstream_usages.len() as u64);
    for usage in &proposal.downstream_usages {
        encode_corpus_downstream_usage(out, usage);
    }
    encode_corpus_replacement_verification(out, &proposal.verification);
    encode_option_hash(out, proposal.public_compatibility_decision_hash.as_ref());
    encode_string(out, &proposal.risk_note);
}

fn encode_corpus_replacement_verification(
    out: &mut Vec<u8>,
    verification: &CorpusReplacementVerificationEvidence,
) {
    encode_string(out, verification.replacement_theorem_level.as_str());
    encode_string(out, verification.source_free_status.as_str());
    encode_hash(out, &verification.replacement_statement_hash);
    encode_hash(out, &verification.verified_statement_hash);
    encode_hash(out, &verification.replacement_certificate_hash);
    encode_hash(out, &verification.verified_certificate_hash);
    encode_hash(out, &verification.source_free_verification_hash);
    encode_hash(out, &verification.axiom_policy_hash);
    encode_bool(out, verification.stale_artifact);
    encode_bool(out, verification.axiom_policy_widened);
}

fn encode_corpus_downstream_usage(out: &mut Vec<u8>, usage: &CorpusDownstreamUsage) {
    encode_string(out, &usage.module);
    encode_string(out, &usage.declaration_name);
    encode_hash(out, &usage.usage_hash);
}

fn encode_corpus_theorem_index_history_entry(
    out: &mut Vec<u8>,
    entry: &CorpusTheoremIndexHistoryEntry,
) {
    encode_string(out, &entry.module);
    encode_string(out, &entry.declaration_name);
    encode_hash(out, &entry.statement_hash);
    encode_hash(out, &entry.theorem_index_hash);
    encode_bool(out, entry.deprecated);
    encode_bool(out, entry.preferred_retrieval);
}

fn encode_theorem_duplicate_identity(out: &mut Vec<u8>, identity: &TheoremDuplicateIdentity) {
    encode_string(out, identity.namespace.as_str());
    encode_string(out, &identity.module);
    encode_string(out, &identity.declaration_name);
    encode_string(out, identity.theorem_level.as_str());
    encode_string(out, &identity.normalized_statement);
    encode_hash(out, &identity.statement_hash);
    encode_hash(out, &identity.alpha_equivalence_hash);
    encode_option_hash(out, identity.reducible_normal_form_hash.as_ref());
    encode_uvar(out, identity.import_closure_modules.len() as u64);
    for module in &identity.import_closure_modules {
        encode_string(out, module);
    }
    encode_hash(out, &identity.axiom_policy_hash);
    encode_uvar(out, identity.axiom_cost);
}

fn encode_theorem_duplicate_import_cost_comparison(
    out: &mut Vec<u8>,
    comparison: &TheoremDuplicateImportCostComparison,
) {
    encode_uvar(out, comparison.existing_import_closure_modules);
    encode_uvar(out, comparison.proposed_import_closure_modules);
    encode_uvar(out, comparison.proposed_only_import_modules.len() as u64);
    for module in &comparison.proposed_only_import_modules {
        encode_string(out, module);
    }
    encode_uvar(out, comparison.existing_only_import_modules.len() as u64);
    for module in &comparison.existing_only_import_modules {
        encode_string(out, module);
    }
    encode_string(out, comparison.ordering.as_str());
}

fn encode_theorem_duplicate_axiom_policy_comparison(
    out: &mut Vec<u8>,
    comparison: &TheoremDuplicateAxiomPolicyComparison,
) {
    encode_hash(out, &comparison.existing_axiom_policy_hash);
    encode_hash(out, &comparison.proposed_axiom_policy_hash);
    encode_uvar(out, comparison.existing_axiom_cost);
    encode_uvar(out, comparison.proposed_axiom_cost);
    encode_string(out, comparison.relation.as_str());
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_option_string(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_string(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_hash(out: &mut Vec<u8>, hash: &Hash) {
    out.extend(hash);
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            encode_hash(out, hash);
        }
        None => out.push(0x00),
    }
}

fn encode_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push(((value as u8) & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, domain);
    encode_uvar(&mut out, payload.len() as u64);
    out.extend(payload);
    Sha256::digest(&out).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn base_key() -> SubgoalClusterKey {
        SubgoalClusterKey {
            normalized_target_hash: test_hash(0x10),
            normalized_local_type_hashes: vec![test_hash(0x12), test_hash(0x11)],
            head_symbols: vec!["Eq".to_owned(), "Nat.add".to_owned()],
            universe_erased_shape_hash: test_hash(0x13),
            approved_commutative_canonicalizations: vec![
                SubgoalClusterCommutativeCanonicalization {
                    operator_symbol: "Nat.add".to_owned(),
                    operand_hashes: vec![test_hash(0x15), test_hash(0x14)],
                },
            ],
            domain_tags: vec!["arithmetic".to_owned(), "equality".to_owned()],
        }
    }

    fn alternate_order_key() -> SubgoalClusterKey {
        SubgoalClusterKey {
            normalized_target_hash: test_hash(0x10),
            normalized_local_type_hashes: vec![test_hash(0x11), test_hash(0x12)],
            head_symbols: vec!["Nat.add".to_owned(), "Eq".to_owned(), "Eq".to_owned()],
            universe_erased_shape_hash: test_hash(0x13),
            approved_commutative_canonicalizations: vec![
                SubgoalClusterCommutativeCanonicalization {
                    operator_symbol: "Nat.add".to_owned(),
                    operand_hashes: vec![test_hash(0x14), test_hash(0x15)],
                },
            ],
            domain_tags: vec!["equality".to_owned(), "arithmetic".to_owned()],
        }
    }

    fn parent_example(byte: u8, declaration_name: &str) -> SubgoalClusterParentExample {
        let mut example = SubgoalClusterParentExample {
            example_hash: [0; 32],
            source_module: "Proofs.Ai.Nat".to_owned(),
            declaration_name: declaration_name.to_owned(),
            goal_fingerprint: test_hash(byte),
            parent_goal_hash: test_hash(byte.wrapping_add(1)),
        };
        example.example_hash = subgoal_cluster_parent_example_hash(&example);
        example
    }

    fn gap_signal(
        kind: LibraryGapSignalKind,
        source_id: &str,
        occurrence_count: u64,
    ) -> LibraryGapSignalObservation {
        let mut signal = LibraryGapSignalObservation {
            signal_hash: [0; 32],
            kind,
            source_module: "Proofs.Ai.Nat".to_owned(),
            source_id: source_id.to_owned(),
            evidence_hash: test_hash(0x40 + kind as u8),
            occurrence_count,
            proposed_import_module: if kind == LibraryGapSignalKind::ConcentratedImportProposal {
                Some("Proofs.Ai.Order".to_owned())
            } else {
                None
            },
            display_text: Some("human-only gap signal text".to_owned()),
            observed_wall_clock_ms: Some(999),
        };
        signal.signal_hash = library_gap_signal_hash(&signal);
        signal
    }

    fn observation(
        key: SubgoalClusterKey,
        parent_example: SubgoalClusterParentExample,
        strategy: SubgoalClusterLikelyProofStrategy,
        gap_signals: Vec<LibraryGapSignalObservation>,
    ) -> SubgoalClusterObservation {
        SubgoalClusterObservation {
            snapshot_hash: test_hash(0xaa),
            snapshot_verified: true,
            local_context_hash: subgoal_cluster_local_context_hash(
                &key.normalized_local_type_hashes,
            ),
            key,
            parent_example,
            likely_proof_strategy: strategy,
            gap_signals,
            model_output_rank: Some(7),
            observed_wall_clock_ms: Some(1234),
            display_text: Some("human display text must not affect cluster identity".to_owned()),
        }
    }

    fn options() -> SubgoalClusterOptions {
        SubgoalClusterOptions::authoring_boundary(vec![test_hash(0xaa)])
    }

    fn base_lemma_generalization_input_without_witness() -> LemmaGeneralizationInput {
        LemmaGeneralizationInput {
            source_context_hash: test_hash(0xb0),
            original_goal_hash: test_hash(0xb1),
            normalized_target_hash: test_hash(0xb2),
            locals: vec![
                LemmaGeneralizationLocal {
                    local_id: "x".to_owned(),
                    type_hash: test_hash(0xc4),
                    value_hash: None,
                    depends_on_local_ids: vec!["A".to_owned()],
                    occurrence_count: 1,
                    binder_kind: LemmaGeneralizationBinderKind::RegularLocal,
                },
                LemmaGeneralizationLocal {
                    local_id: "M".to_owned(),
                    type_hash: test_hash(0xc3),
                    value_hash: None,
                    depends_on_local_ids: vec!["A".to_owned()],
                    occurrence_count: 1,
                    binder_kind: LemmaGeneralizationBinderKind::Structure,
                },
                LemmaGeneralizationLocal {
                    local_id: "n".to_owned(),
                    type_hash: test_hash(0xc2),
                    value_hash: None,
                    depends_on_local_ids: vec![],
                    occurrence_count: 1,
                    binder_kind: LemmaGeneralizationBinderKind::IndexLocal,
                },
                LemmaGeneralizationLocal {
                    local_id: "A".to_owned(),
                    type_hash: test_hash(0xc1),
                    value_hash: None,
                    depends_on_local_ids: vec![],
                    occurrence_count: 1,
                    binder_kind: LemmaGeneralizationBinderKind::Carrier,
                },
            ],
            premises: vec![
                LemmaGeneralizationPremise {
                    premise_id: "used_eq".to_owned(),
                    premise_hash: test_hash(0xd1),
                    depends_on_local_ids: vec!["x".to_owned()],
                    occurrence_count: 2,
                    required_for_typecheck: false,
                },
                LemmaGeneralizationPremise {
                    premise_id: "required_typeclass".to_owned(),
                    premise_hash: test_hash(0xd2),
                    depends_on_local_ids: vec!["M".to_owned()],
                    occurrence_count: 0,
                    required_for_typecheck: true,
                },
                LemmaGeneralizationPremise {
                    premise_id: "unused_noise".to_owned(),
                    premise_hash: test_hash(0xd3),
                    depends_on_local_ids: vec!["x".to_owned()],
                    occurrence_count: 0,
                    required_for_typecheck: false,
                },
            ],
            constants: vec![
                LemmaGeneralizationConstantUse {
                    constant_id: "Nat.add".to_owned(),
                    constant_hash: test_hash(0xe1),
                    may_parameterize: false,
                    import_module: Some("Std.Nat.Basic".to_owned()),
                },
                LemmaGeneralizationConstantUse {
                    constant_id: "zero".to_owned(),
                    constant_hash: test_hash(0xe2),
                    may_parameterize: true,
                    import_module: Some("Std.Nat.Basic".to_owned()),
                },
            ],
            equality_candidates: vec![LemmaGeneralizationEqualityCandidate {
                equality_id: "eq-main".to_owned(),
                equality_hash: test_hash(0xe3),
                lhs_hash: test_hash(0xe4),
                rhs_hash: test_hash(0xe5),
                lhs_size: 10,
                rhs_size: 2,
                can_reverse: true,
            }],
            structure_candidates: vec![
                LemmaGeneralizationStructureCandidate {
                    structure_id: "monoid-law".to_owned(),
                    structure: LemmaGeneralizationStructureKind::Monoid,
                    evidence_hash: Some(test_hash(0xe6)),
                },
                LemmaGeneralizationStructureCandidate {
                    structure_id: "ring-law".to_owned(),
                    structure: LemmaGeneralizationStructureKind::Ring,
                    evidence_hash: Some(test_hash(0xe7)),
                },
                LemmaGeneralizationStructureCandidate {
                    structure_id: "field-law".to_owned(),
                    structure: LemmaGeneralizationStructureKind::Field,
                    evidence_hash: None,
                },
            ],
            carrier_candidates: vec![
                LemmaGeneralizationCarrierCandidate {
                    carrier_id: "finite-carrier".to_owned(),
                    kind: LemmaGeneralizationCarrierKind::FiniteToGeneral,
                    source_hash: test_hash(0xe8),
                    generalized_hash: test_hash(0xe9),
                    evidence_hash: Some(test_hash(0xea)),
                },
                LemmaGeneralizationCarrierCandidate {
                    carrier_id: "indexed-carrier".to_owned(),
                    kind: LemmaGeneralizationCarrierKind::IndexedCarrier,
                    source_hash: test_hash(0xeb),
                    generalized_hash: test_hash(0xec),
                    evidence_hash: None,
                },
            ],
            import_candidates: vec![StatementNormalizationImportNeed {
                module: "Proofs.Ai.Eq".to_owned(),
                reason_hash: test_hash(0xed),
            }],
            typecheck_witness: None,
        }
    }

    fn base_lemma_generalization_input() -> LemmaGeneralizationInput {
        let mut input = base_lemma_generalization_input_without_witness();
        let generalized_statement_hash = lemma_generalization_proposed_statement_hash(&input)
            .expect("fixture should produce a proposed generalized statement");
        input.typecheck_witness = Some(StatementNormalizationTypecheckWitness {
            generalized_statement_hash,
            expected_type_hash: test_hash(0xf1),
            environment_hash: test_hash(0xf2),
            witness_hash: test_hash(0xf3),
        });
        input
    }

    fn base_library_reuse_score_input(stage: LibraryGrowthStage) -> LibraryReuseScoreInput {
        LibraryReuseScoreInput {
            candidate_id: "pua-m14-generated-reuse-helper".to_owned(),
            target_module: "Proofs.Ai.LibraryGrowth".to_owned(),
            declaration_name: "generated_reuse_helper".to_owned(),
            theorem_level: TheoremLevel::L2DerivedCertificate,
            stage,
            downstream_unlock_count: 8,
            repeated_parent_goal_count: 5,
            proof_shortening_nodes: 120,
            statement_stability_score: 96,
            import_closure_added_modules: 2,
            axiom_cost: 0,
            proof_difficulty_score: 80,
            certificate_growth_bytes: 8 * 1024,
            environment_growth_entries: 4,
            index_entry_growth: 2,
            premise_search_latency_delta_ms: 15,
            axiom_policy_widened: false,
            duplicate_status: LibraryReuseDuplicateStatus::Unique,
        }
    }

    fn theorem_duplicate_identity(
        namespace: TheoremDuplicateNamespace,
        module: &str,
        declaration_name: &str,
        statement_hash: Hash,
        alpha_equivalence_hash: Hash,
    ) -> TheoremDuplicateIdentity {
        TheoremDuplicateIdentity {
            namespace,
            module: module.to_owned(),
            declaration_name: declaration_name.to_owned(),
            theorem_level: TheoremLevel::L2DerivedCertificate,
            normalized_statement: "forall (A : Type) (x : A), x = x".to_owned(),
            statement_hash,
            alpha_equivalence_hash,
            reducible_normal_form_hash: Some(test_hash(0x80)),
            import_closure_modules: vec![module.to_owned()],
            axiom_policy_hash: test_hash(0x90),
            axiom_cost: 0,
        }
    }

    fn has_budget_failure(
        report: &LibraryReuseScoreReport,
        kind: LibraryGrowthBudgetFailureKind,
    ) -> bool {
        report
            .budget_failures
            .iter()
            .any(|failure| failure.kind == kind)
    }

    #[test]
    fn library_reuse_score_is_deterministic() {
        let budget = default_library_growth_budget();
        let input = base_library_reuse_score_input(LibraryGrowthStage::PromotionCandidate);

        let report = library_reuse_score(&input, &budget).unwrap();
        let rerun = library_reuse_score(&input, &budget).unwrap();

        assert_eq!(report, rerun);
        assert_eq!(report.report_hash, library_reuse_score_report_hash(&report));
        validate_library_reuse_score_report(&input, &budget, &report).unwrap();
        assert!(report.score_is_untrusted);
        assert!(!report.public_promotion_allowed_by_score);
        assert_eq!(
            report.authoring_recommendation,
            LibraryGrowthRecommendation::AuthoringUseful
        );
        assert_eq!(
            report.public_package_recommendation,
            LibraryGrowthRecommendation::PromotionReviewRequired
        );
        assert!(report.public_package_ready_for_review);
        assert!(report.authoring_usefulness_score > 0);
        assert!(report.public_readiness_score > 0);
        assert!(report.budget_failures.is_empty());

        let authoring = library_reuse_score(
            &base_library_reuse_score_input(LibraryGrowthStage::AuthoringStage),
            &budget,
        )
        .unwrap();
        assert_eq!(
            authoring.authoring_recommendation,
            LibraryGrowthRecommendation::AuthoringUseful
        );
        assert_eq!(
            authoring.public_package_recommendation,
            LibraryGrowthRecommendation::Defer
        );
        assert!(!authoring.public_package_ready_for_review);

        let mut stale_report = report.clone();
        stale_report.public_promotion_allowed_by_score = true;
        stale_report.report_hash = library_reuse_score_report_hash(&stale_report);
        let error =
            validate_library_reuse_score_report(&input, &budget, &stale_report).unwrap_err();
        assert!(matches!(
            error,
            LibraryReuseScoreError::ReportHashMismatch { .. }
        ));
    }

    #[test]
    fn library_reuse_score_defers_policy_and_growth_failures() {
        let budget = default_library_growth_budget();
        let base = base_library_reuse_score_input(LibraryGrowthStage::PromotionCandidate);

        let mut widened = base.clone();
        widened.proof_shortening_nodes = 10_000;
        widened.axiom_policy_widened = true;
        let report = library_reuse_score(&widened, &budget).unwrap();
        assert!(report.public_readiness_score > 0);
        assert_eq!(
            report.public_package_recommendation,
            LibraryGrowthRecommendation::Defer
        );
        assert!(has_budget_failure(
            &report,
            LibraryGrowthBudgetFailureKind::WidenedAxiomPolicy
        ));

        let mut large_import_closure = base.clone();
        large_import_closure.proof_shortening_nodes = 10_000;
        large_import_closure.import_closure_added_modules =
            budget.max_import_closure_added_modules + 1;
        let report = library_reuse_score(&large_import_closure, &budget).unwrap();
        assert_eq!(
            report.public_package_recommendation,
            LibraryGrowthRecommendation::Defer
        );
        assert!(has_budget_failure(
            &report,
            LibraryGrowthBudgetFailureKind::ExcessiveImportClosure
        ));

        let mut duplicate = base.clone();
        duplicate.proof_shortening_nodes = 10_000;
        duplicate.duplicate_status = LibraryReuseDuplicateStatus::Duplicate;
        let report = library_reuse_score(&duplicate, &budget).unwrap();
        assert_eq!(
            report.public_package_recommendation,
            LibraryGrowthRecommendation::Defer
        );
        assert!(has_budget_failure(
            &report,
            LibraryGrowthBudgetFailureKind::DuplicateStatus
        ));

        let mut unknown_level = base.clone();
        unknown_level.proof_shortening_nodes = 10_000;
        unknown_level.theorem_level = TheoremLevel::Unknown;
        let report = library_reuse_score(&unknown_level, &budget).unwrap();
        assert_eq!(
            report.public_package_recommendation,
            LibraryGrowthRecommendation::Defer
        );
        assert!(has_budget_failure(
            &report,
            LibraryGrowthBudgetFailureKind::UnknownTheoremLevel
        ));

        let mut slow_premise_search = base;
        slow_premise_search.proof_shortening_nodes = 10_000;
        slow_premise_search.premise_search_latency_delta_ms =
            budget.max_premise_search_latency_delta_ms + 1;
        let report = library_reuse_score(&slow_premise_search, &budget).unwrap();
        assert_eq!(
            report.public_package_recommendation,
            LibraryGrowthRecommendation::Defer
        );
        assert!(has_budget_failure(
            &report,
            LibraryGrowthBudgetFailureKind::PremiseSearchLatency
        ));
    }

    #[test]
    fn duplicate_statement_hash_detection() {
        let existing = theorem_duplicate_identity(
            TheoremDuplicateNamespace::PublicMathlib,
            "Mathlib.Basic",
            "refl_public",
            test_hash(0x61),
            test_hash(0x71),
        );
        let mut proposed = theorem_duplicate_identity(
            TheoremDuplicateNamespace::StagedCorpus,
            "Proofs.Ai.Basic",
            "generated_refl",
            test_hash(0x61),
            test_hash(0x72),
        );
        proposed.import_closure_modules =
            vec!["Proofs.Ai.Basic".to_owned(), "Proofs.Ai.Eq".to_owned()];

        let report =
            theorem_duplicate_review_report(existing.clone(), proposed.clone(), None, false)
                .unwrap();
        let rerun = theorem_duplicate_review_report(existing, proposed, None, false).unwrap();

        assert_eq!(report, rerun);
        assert_eq!(
            report.report_hash,
            theorem_duplicate_review_report_hash(&report)
        );
        validate_theorem_duplicate_review_report(&report).unwrap();
        assert_eq!(
            report.relation_kind,
            TheoremDuplicateRelationKind::ExactStatementHash
        );
        assert_eq!(
            report.review_stages,
            vec![TheoremDuplicateReviewStage::StatementHash]
        );
        assert_eq!(
            report.recommended_action,
            TheoremDuplicateRecommendedAction::RejectBeforeProofTask
        );
        assert!(report.proof_task_creation_blocked);
        assert!(report.public_promotion_blocked);
        assert!(!report.public_promotion_allowed_by_report);
        assert!(report.handles_staged_and_public_identities_separately);
        assert_eq!(
            report.import_cost_comparison.ordering,
            TheoremDuplicateCostOrdering::ExistingLower
        );
        assert_eq!(
            report.axiom_policy_comparison.relation,
            TheoremDuplicateAxiomPolicyRelation::Same
        );

        let alias_report = theorem_duplicate_review_report(
            report.existing.clone(),
            report.proposed.clone(),
            None,
            true,
        )
        .unwrap();
        assert_eq!(
            alias_report.recommended_action,
            TheoremDuplicateRecommendedAction::CompatibilityAliasReview
        );
        assert!(!alias_report.proof_task_creation_blocked);
        assert!(!alias_report.public_promotion_allowed_by_report);
    }

    #[test]
    fn duplicate_alpha_equivalence_detection() {
        let mut existing = theorem_duplicate_identity(
            TheoremDuplicateNamespace::StagedCorpus,
            "Proofs.Ai.List",
            "forall_intro_existing",
            test_hash(0x62),
            test_hash(0x73),
        );
        existing.reducible_normal_form_hash = None;
        let mut proposed = theorem_duplicate_identity(
            TheoremDuplicateNamespace::PublicMathlib,
            "Mathlib.List.Basic",
            "forall_intro_public",
            test_hash(0x63),
            test_hash(0x73),
        );
        proposed.normalized_statement = "forall (B : Type) (y : B), y = y".to_owned();
        proposed.reducible_normal_form_hash = None;

        let report = theorem_duplicate_review_report(existing, proposed, None, false).unwrap();

        validate_theorem_duplicate_review_report(&report).unwrap();
        assert_eq!(
            report.relation_kind,
            TheoremDuplicateRelationKind::AlphaEquivalent
        );
        assert_eq!(
            report.review_stages,
            vec![
                TheoremDuplicateReviewStage::StatementHash,
                TheoremDuplicateReviewStage::AlphaEquivalence
            ]
        );
        assert_eq!(
            report.recommended_action,
            TheoremDuplicateRecommendedAction::RejectBeforeProofTask
        );
        assert!(report.proof_task_creation_blocked);
        assert!(report.public_promotion_blocked);
        assert!(report.handles_staged_and_public_identities_separately);
        assert!(report.mutual_implication_skipped_reason.is_none());
    }

    #[test]
    fn duplicate_subsumption_review_keeps_candidates_staged() {
        let mut existing = theorem_duplicate_identity(
            TheoremDuplicateNamespace::PublicMathlib,
            "Mathlib.Order.Basic",
            "existing_order_fact",
            test_hash(0x64),
            test_hash(0x74),
        );
        existing.normalized_statement = "forall (A : Type), Prop".to_owned();
        existing.reducible_normal_form_hash = Some(test_hash(0x84));
        existing.import_closure_modules =
            vec!["Mathlib.Order.Basic".to_owned(), "Mathlib.Core".to_owned()];
        existing.axiom_policy_hash = test_hash(0x94);
        let mut proposed = theorem_duplicate_identity(
            TheoremDuplicateNamespace::StagedCorpus,
            "Proofs.Ai.Order",
            "generated_stronger_order_fact",
            test_hash(0x65),
            test_hash(0x75),
        );
        proposed.normalized_statement = "forall (A : Type) (x : A), Prop".to_owned();
        proposed.reducible_normal_form_hash = Some(test_hash(0x85));
        proposed.axiom_policy_hash = test_hash(0x94);

        let stronger = theorem_duplicate_review_report(
            existing.clone(),
            proposed.clone(),
            Some(TheoremDuplicateMutualImplicationEvidence {
                existing_implies_proposed: Some(false),
                proposed_implies_existing: Some(true),
                skipped_reason: None,
            }),
            false,
        )
        .unwrap();
        validate_theorem_duplicate_review_report(&stronger).unwrap();
        assert_eq!(
            stronger.relation_kind,
            TheoremDuplicateRelationKind::ProposedStronger
        );
        assert_eq!(
            stronger.recommended_action,
            TheoremDuplicateRecommendedAction::ReviewSubsumption
        );
        assert!(!stronger.proof_task_creation_blocked);
        assert!(stronger.public_promotion_blocked);
        assert!(stronger
            .review_stages
            .contains(&TheoremDuplicateReviewStage::HumanReviewQueue));

        let inconclusive = theorem_duplicate_review_report(
            existing,
            proposed,
            Some(TheoremDuplicateMutualImplicationEvidence {
                existing_implies_proposed: None,
                proposed_implies_existing: None,
                skipped_reason: Some("budget exhausted before implication search".to_owned()),
            }),
            false,
        )
        .unwrap();
        validate_theorem_duplicate_review_report(&inconclusive).unwrap();
        assert_eq!(
            inconclusive.relation_kind,
            TheoremDuplicateRelationKind::Inconclusive
        );
        assert_eq!(
            inconclusive.recommended_action,
            TheoremDuplicateRecommendedAction::KeepStaged
        );
        assert!(!inconclusive.proof_task_creation_blocked);
        assert!(inconclusive.public_promotion_blocked);
        assert_eq!(
            inconclusive.mutual_implication_skipped_reason.as_deref(),
            Some("budget exhausted before implication search")
        );
    }

    #[test]
    fn lemma_generalization_dependency_order_respects_dependencies_and_report_identity() {
        let input = base_lemma_generalization_input();

        let report = lemma_generalization_dependency_order(&input).unwrap();
        validate_statement_normalization_report(&input, &report).unwrap();
        let rerun = lemma_generalization_dependency_order(&input).unwrap();

        assert_eq!(report, rerun);
        assert_eq!(
            report.report_hash,
            statement_normalization_report_hash(&report)
        );
        assert_eq!(
            report
                .binder_order
                .iter()
                .map(|binder| binder.local_id.as_str())
                .collect::<Vec<_>>(),
            vec!["A", "n", "M", "x"]
        );
        assert_eq!(
            report
                .removed_premises
                .iter()
                .map(|premise| premise.premise_id.as_str())
                .collect::<Vec<_>>(),
            vec!["unused_noise"]
        );
        assert_eq!(
            report
                .retained_premises
                .iter()
                .map(|premise| premise.premise_id.as_str())
                .collect::<Vec<_>>(),
            vec!["required_typeclass", "used_eq"]
        );
        assert_eq!(
            report
                .parameterized_constants
                .iter()
                .map(|constant| constant.constant_id.as_str())
                .collect::<Vec<_>>(),
            vec!["zero"]
        );
        assert_eq!(
            report
                .import_needs
                .iter()
                .map(|import| import.module.as_str())
                .collect::<Vec<_>>(),
            vec!["Proofs.Ai.Eq", "Std.Nat.Basic"]
        );

        let equality = &report.equality_orientations[0];
        assert_eq!(
            equality.orientation,
            LemmaGeneralizationEqualityOrientation::Reverse
        );
        assert_eq!(equality.oriented_lhs_hash, test_hash(0xe5));
        assert_eq!(equality.oriented_rhs_hash, test_hash(0xe4));
        assert_eq!(
            report.selected_structure,
            Some(LemmaGeneralizationStructureKind::Monoid)
        );
        assert_eq!(report.carrier_generalizations.len(), 1);
        assert_eq!(
            report.carrier_generalizations[0].carrier_id,
            "finite-carrier"
        );
        assert!(report.rejected_attempts.iter().any(|rejected| {
            rejected.kind == StatementNormalizationRejectedAttemptKind::PremiseMinimization
                && rejected.item_id == "required_typeclass"
                && rejected.reason == StatementNormalizationRejectionReason::RequiredForTypecheck
        }));
        assert!(report.rejected_attempts.iter().any(|rejected| {
            rejected.kind == StatementNormalizationRejectedAttemptKind::AlgebraicStructure
                && rejected.item_id == "field-law"
                && rejected.reason
                    == StatementNormalizationRejectionReason::MissingStructureEvidence
        }));
        assert!(report.rejected_attempts.iter().any(|rejected| {
            rejected.kind == StatementNormalizationRejectedAttemptKind::CarrierGeneralization
                && rejected.item_id == "indexed-carrier"
                && rejected.reason == StatementNormalizationRejectionReason::MissingCarrierEvidence
        }));
        assert!(report.proof_task_allowed);
    }

    #[test]
    fn lemma_generalization_rejects_over_generalization_with_structured_diagnostics() {
        let input = base_lemma_generalization_input();
        let report = lemma_generalization_dependency_order(&input).unwrap();

        let missing_witness = lemma_generalization_dependency_order(
            &base_lemma_generalization_input_without_witness(),
        )
        .unwrap_err();
        assert!(matches!(
            missing_witness,
            LemmaGeneralizationError::MissingTypecheckWitness { .. }
        ));

        let mut wrong_witness = input.clone();
        wrong_witness
            .typecheck_witness
            .as_mut()
            .expect("fixture has a witness")
            .generalized_statement_hash = test_hash(0xfe);
        let witness_error = lemma_generalization_dependency_order(&wrong_witness).unwrap_err();
        assert!(matches!(
            witness_error,
            LemmaGeneralizationError::TypecheckWitnessMismatch { .. }
        ));

        let mut reordered = report.clone();
        reordered.binder_order.swap(0, 2);
        reordered.report_hash = statement_normalization_report_hash(&reordered);
        assert_eq!(
            validate_statement_normalization_report(&input, &reordered).unwrap_err(),
            LemmaGeneralizationError::DependencyOrderViolation {
                local_id: "M".to_owned(),
                dependency_local_id: "A".to_owned(),
            }
        );

        let mut dropped_required_premise = report.clone();
        dropped_required_premise
            .retained_premises
            .retain(|premise| premise.premise_id != "required_typeclass");
        dropped_required_premise.report_hash =
            statement_normalization_report_hash(&dropped_required_premise);
        assert_eq!(
            validate_statement_normalization_report(&input, &dropped_required_premise).unwrap_err(),
            LemmaGeneralizationError::OverGeneralization {
                reason: StatementNormalizationRejectionReason::RequiredForTypecheck,
                item_id: "required_typeclass".to_owned(),
            }
        );

        let mut unavailable_structure = report.clone();
        unavailable_structure.selected_structure = Some(LemmaGeneralizationStructureKind::Field);
        unavailable_structure.report_hash =
            statement_normalization_report_hash(&unavailable_structure);
        assert_eq!(
            validate_statement_normalization_report(&input, &unavailable_structure).unwrap_err(),
            LemmaGeneralizationError::OverGeneralization {
                reason: StatementNormalizationRejectionReason::MissingStructureEvidence,
                item_id: "field-law".to_owned(),
            }
        );

        let mut unavailable_carrier = report.clone();
        unavailable_carrier.carrier_generalizations.push(
            StatementNormalizationCarrierGeneralization {
                carrier_id: "indexed-carrier".to_owned(),
                kind: LemmaGeneralizationCarrierKind::IndexedCarrier,
                source_hash: test_hash(0xeb),
                generalized_hash: test_hash(0xec),
                evidence_hash: test_hash(0xee),
            },
        );
        unavailable_carrier.report_hash = statement_normalization_report_hash(&unavailable_carrier);
        assert_eq!(
            validate_statement_normalization_report(&input, &unavailable_carrier).unwrap_err(),
            LemmaGeneralizationError::OverGeneralization {
                reason: StatementNormalizationRejectionReason::MissingCarrierEvidence,
                item_id: "indexed-carrier".to_owned(),
            }
        );
    }

    #[test]
    fn subgoal_cluster_identity_equal_verified_inputs_are_ordered_and_model_order_independent() {
        let shared_signal = gap_signal(
            LibraryGapSignalKind::FrequentExplicitProofPattern,
            "shared-explicit-pattern",
            2,
        );
        let mut same_signal_different_advisory_fields = shared_signal.clone();
        same_signal_different_advisory_fields.display_text =
            Some("same signal with different display text".to_owned());
        same_signal_different_advisory_fields.observed_wall_clock_ms = Some(1);

        let first = observation(
            base_key(),
            parent_example(0x20, "add_zero_goal"),
            SubgoalClusterLikelyProofStrategy::IntroRewrite,
            vec![
                shared_signal,
                gap_signal(
                    LibraryGapSignalKind::RepeatedFailedSubgoal,
                    "failed-subgoal-1",
                    3,
                ),
            ],
        );
        let mut second = observation(
            alternate_order_key(),
            parent_example(0x22, "zero_add_goal"),
            SubgoalClusterLikelyProofStrategy::IntroRewrite,
            vec![
                same_signal_different_advisory_fields,
                gap_signal(LibraryGapSignalKind::NoCandidateStop, "no-candidate-1", 1),
            ],
        );
        second.model_output_rank = Some(1);
        second.observed_wall_clock_ms = Some(1);
        second.display_text = Some("different display text".to_owned());

        let forward =
            cluster_library_growth_subgoals(&[first.clone(), second.clone()], &options()).unwrap();
        let reverse = cluster_library_growth_subgoals(&[second, first], &options()).unwrap();

        assert_eq!(forward, reverse);
        assert_eq!(forward.len(), 1);
        let cluster = &forward[0];
        assert_eq!(
            cluster.cluster_id,
            subgoal_cluster_identity_hash(&base_key())
        );
        assert_eq!(cluster.parent_examples.len(), 2);
        assert_eq!(
            cluster.proposal_status,
            SubgoalClusterProposalStatus::ProposedCandidateLemma
        );

        let mut invalid = cluster.clone();
        invalid.proposal_status = SubgoalClusterProposalStatus::PromotionReady;
        let error = validate_subgoal_cluster(&invalid, &options()).unwrap_err();
        assert_eq!(
            error,
            SubgoalClusterError::InvalidProposalStatus {
                status: SubgoalClusterProposalStatus::PromotionReady,
            }
        );
    }

    #[test]
    fn library_gap_signal_collection_counts_all_signal_kinds() {
        let signals = [
            gap_signal(LibraryGapSignalKind::NoCandidateStop, "no-candidate", 1),
            gap_signal(
                LibraryGapSignalKind::RepeatedFailedSubgoal,
                "failed-subgoal",
                4,
            ),
            gap_signal(
                LibraryGapSignalKind::FrequentExplicitProofPattern,
                "explicit-pattern",
                5,
            ),
            gap_signal(
                LibraryGapSignalKind::RecreatedHelperTheorem,
                "helper-theorem",
                2,
            ),
            gap_signal(
                LibraryGapSignalKind::LargeDuplicatedProofTerm,
                "duplicated-proof",
                3,
            ),
            gap_signal(
                LibraryGapSignalKind::ConcentratedImportProposal,
                "import-proposal",
                6,
            ),
        ];
        let clusters = cluster_library_growth_subgoals(
            &[
                observation(
                    base_key(),
                    parent_example(0x20, "gap_collection_one"),
                    SubgoalClusterLikelyProofStrategy::ExistingPremiseSearch,
                    signals[..3].to_vec(),
                ),
                observation(
                    alternate_order_key(),
                    parent_example(0x22, "gap_collection_two"),
                    SubgoalClusterLikelyProofStrategy::ExistingPremiseSearch,
                    signals[3..].to_vec(),
                ),
            ],
            &options(),
        )
        .unwrap();

        let summaries = library_gap_signal_collection(&clusters);
        assert_eq!(summaries.len(), 6);
        assert_eq!(
            summaries
                .iter()
                .map(|summary| summary.kind.as_str())
                .collect::<Vec<_>>(),
            vec![
                "no_candidate_stop",
                "repeated_failed_subgoal",
                "frequent_explicit_proof_pattern",
                "recreated_helper_theorem",
                "large_duplicated_proof_term",
                "concentrated_import_proposal",
            ]
        );
        assert_eq!(
            summaries
                .iter()
                .map(|summary| summary.total_occurrences)
                .sum::<u64>(),
            21
        );
        let import_summary = summaries
            .iter()
            .find(|summary| summary.kind == LibraryGapSignalKind::ConcentratedImportProposal)
            .unwrap();
        assert_eq!(
            import_summary.proposed_import_modules,
            vec!["Proofs.Ai.Order".to_owned()]
        );
    }

    #[test]
    fn subgoal_cluster_rejects_stale_snapshot_and_modified_local_context() {
        let missing_boundary = observation(
            base_key(),
            parent_example(0x1e, "missing_snapshot_boundary_goal"),
            SubgoalClusterLikelyProofStrategy::Simplification,
            vec![],
        );
        let error = cluster_library_growth_subgoals(
            &[missing_boundary],
            &SubgoalClusterOptions {
                accepted_snapshot_hashes: vec![],
                min_parent_examples: SUBGOAL_CLUSTER_MIN_PARENT_EXAMPLES,
            },
        )
        .unwrap_err();
        assert_eq!(
            error,
            SubgoalClusterError::StaleSnapshot {
                snapshot_hash: test_hash(0xaa),
            }
        );

        let stale = SubgoalClusterObservation {
            snapshot_hash: test_hash(0xbb),
            ..observation(
                base_key(),
                parent_example(0x20, "stale_snapshot_goal"),
                SubgoalClusterLikelyProofStrategy::Simplification,
                vec![],
            )
        };
        let error = cluster_library_growth_subgoals(&[stale], &options()).unwrap_err();
        assert_eq!(
            error,
            SubgoalClusterError::StaleSnapshot {
                snapshot_hash: test_hash(0xbb),
            }
        );

        let mut modified_key = base_key();
        modified_key
            .normalized_local_type_hashes
            .push(test_hash(0x99));
        let mut modified_context = observation(
            modified_key,
            parent_example(0x24, "modified_context_goal"),
            SubgoalClusterLikelyProofStrategy::Simplification,
            vec![],
        );
        modified_context.local_context_hash =
            subgoal_cluster_local_context_hash(&base_key().normalized_local_type_hashes);

        let error = cluster_library_growth_subgoals(&[modified_context], &options()).unwrap_err();
        assert!(matches!(
            error,
            SubgoalClusterError::ModifiedLocalContext { .. }
        ));

        let too_few_examples = observation(
            base_key(),
            parent_example(0x26, "single_parent_goal"),
            SubgoalClusterLikelyProofStrategy::Simplification,
            vec![],
        );
        let error = cluster_library_growth_subgoals(
            &[too_few_examples],
            &SubgoalClusterOptions {
                accepted_snapshot_hashes: vec![test_hash(0xaa)],
                min_parent_examples: 0,
            },
        )
        .unwrap_err();
        assert_eq!(
            error,
            SubgoalClusterError::InsufficientParentExamples {
                cluster_id: subgoal_cluster_identity_hash(&base_key()),
                required: SUBGOAL_CLUSTER_MIN_PARENT_EXAMPLES,
                actual: 1,
            }
        );
    }
}
