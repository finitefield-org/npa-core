//! Phase 9 advanced AI validation and replay substrate.
//!
//! This module is a deterministic, untrusted orchestration layer for advanced
//! candidates. It validates request shapes, canonical bytes, hashes, and
//! replayable handoffs, but it is not a trusted checker. AI sidecars, theorem
//! graph scores, SMT solver output, and natural-language formalization
//! confidence may guide candidate construction only; they cannot create a
//! checker verdict or widen the certificate acceptance boundary.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use npa_cert::{
    AxiomPolicy, CoreModule, ExportKind, Hash, InductiveArtifactProfileCheckV1, ModuleName, Name,
    VerifierSession,
};
use npa_kernel::{Binder, ConstructorDecl, Ctx, Decl, Env, Expr, InductiveDecl, Level};
use npa_tactic::{
    machine_local_context_canonical_bytes, machine_tactic_options_canonical_bytes,
    tactic_budget_canonical_bytes, CandidateApplyArg, CandidateRewriteRuleRef, EqFamilyRef,
    MachineLocalDecl, MachineProofSpec, MachineTacticCandidate, MachineTacticOptions, NatFamilyRef,
    RawMachineTerm, RewriteDirection, RewriteSite, SimpRuleRef, TacticBudget, TacticHead,
    VerifiedImportRef,
};
use sha2::{Digest, Sha256};

use crate::adapter::{
    machine_tactic_extract_closed_machine_theorem_decl,
    machine_tactic_run_machine_tactic_with_budget, machine_tactic_start_machine_proof,
    machine_tactic_validate_machine_tactic_candidate, MachineApiDiagnosticPhase,
};
use crate::types::machine_api_name_canonical_bytes;
use crate::MachineApiErrorKind;

const CANDIDATE_HASH_TAG: &str = "npa.advanced-ai.candidate.v1";
const OPTIONS_HASH_TAG: &str = "npa.advanced-ai.options.v1";
const ENV_FINGERPRINT_TAG: &str = "npa.advanced-ai.env.v1";
const GOAL_FINGERPRINT_TAG: &str = "npa.advanced-ai.goal.v1";
const VALIDATION_RESULT_HASH_TAG: &str = "npa.advanced-ai.validation_result.v1";
const UNIVERSE_CONSTRAINT_SET_HASH_TAG: &str = "npa.advanced-ai.universe.constraints.v1";
const THEOREM_GRAPH_SNAPSHOT_HASH_TAG: &str = "npa.advanced-ai.theorem_graph.snapshot.v1";
const THEOREM_GRAPH_QUERY_FEATURES_HASH_TAG: &str =
    "npa.advanced-ai.theorem_graph.query_features.v1";
const SMT_PROBLEM_HASH_TAG: &str = "npa.advanced-ai.smt.problem.v1";
const SMT_ENCODING_HASH_TAG: &str = "npa.advanced-ai.smt.encoding.v1";
const SMT_LIB_PROBLEM_HASH_TAG: &str = "npa.advanced-ai.smt.smtlib_problem.v1";
const SMT_PROOF_PAYLOAD_HASH_TAG: &str = "npa.advanced-ai.smt.proof_payload.v1";
const SMT_OPAQUE_PROOF_PAYLOAD_HASH_TAG: &str = "npa.advanced-ai.smt.opaque_proof_payload.v1";
const SMT_RECONSTRUCTION_PLAN_HASH_TAG: &str = "npa.advanced-ai.smt.reconstruction_plan.v1";
const SMT_CERTIFICATE_METADATA_HASH_TAG: &str = "npa.advanced-ai.smt.certificate_metadata.v1";
const SMT_NAT_TO_INT_SIDE_CONDITION_HASH_TAG: &str =
    "npa.advanced-ai.smt.nat_to_int_side_condition.v1";
const SMT_COMMAND_ID_HASH_TAG: &str = "npa.advanced-ai.smt.command_id.v1";
const SMT_SYMBOL_HASH_TAG: &str = "npa.advanced-ai.smt.symbol.v1";
const SMT_RULE_DESCRIPTOR_HASH_TAG: &str = "npa.advanced-ai.smt.rule_descriptor.v1";
const SMT_RULE_DESCRIPTOR_FINGERPRINT_TAG: &str =
    "npa.advanced-ai.smt.rule_descriptor_fingerprint.v1";
const SMT_RULE_REGISTRY_HASH_TAG: &str = "npa.advanced-ai.smt.rule_registry.v1";
const SMT_SOLVER_PROCESS_POLICY_HASH_TAG: &str = "npa.advanced-ai.smt.solver_process_policy.v1";
const SMT_SOLVER_PROCESS_PROFILE_HASH_TAG: &str = "npa.advanced-ai.smt.solver_process_profile.v1";
const SMT_SOLVER_HANDOFF_HASH_TAG: &str = "npa.advanced-ai.smt.solver_handoff.v1";
const FORMALIZATION_SOURCE_DOCUMENT_HASH_TAG: &str =
    "npa.advanced-ai.formalization.source_document.v1";
const FORMALIZATION_CLAIM_SPAN_HASH_TAG: &str = "npa.advanced-ai.formalization.claim_span.v1";
const FORMALIZATION_REJECTION_REASON_HASH_TAG: &str =
    "npa.advanced-ai.formalization.rejection_reason.v1";
const FORMALIZATION_CANDIDATE_STATEMENT_HASH_TAG: &str =
    "npa.advanced-ai.formalization.candidate_statement.v1";
const FORMALIZATION_ACCEPTED_STATEMENT_HASH_TAG: &str =
    "npa.advanced-ai.formalization.accepted_statement.v1";
const FORMALIZATION_PROOF_ROOT_HASH_TAG: &str = "npa.advanced-ai.formalization.proof_root.v1";
const EXTERNAL_INDEX_UPDATE_KEY_HASH_TAG: &str = "npa.advanced-ai.external_index_update.key.v1";

const MAX_OPTIONS_BYTES: usize = 16_000_000;
const MAX_ADVANCED_AI_GLOBAL_REFS: u64 = 65_536;
const MAX_ADVANCED_AI_INDUCTIVE_ITEMS: u64 = 65_536;
const MAX_ADVANCED_AI_INDUCTIVE_EXPR_NODES: u64 = 1_000_000;
const MAX_ADVANCED_AI_INDUCTIVE_LEVEL_NODES: u64 = 1_000_000;
const MAX_ADVANCED_AI_TYPECLASS_CANDIDATES: u64 = 65_536;
const MAX_ADVANCED_AI_TYPECLASS_DEPTH: u32 = 1_024;
const MAX_ADVANCED_AI_TYPECLASS_NODES: u32 = 1_000_000;
const MAX_ADVANCED_AI_THEOREM_GRAPH_SNAPSHOT_BYTES: usize = 128_000_000;
const MAX_ADVANCED_AI_THEOREM_GRAPH_QUERY_FEATURES_BYTES: usize = 16_000_000;
const MAX_ADVANCED_AI_THEOREM_GRAPH_NODES: u64 = 1_000_000;
const MAX_ADVANCED_AI_THEOREM_GRAPH_EDGES: u64 = 1_000_000;
const MAX_ADVANCED_AI_THEOREM_GRAPH_FEATURES: u64 = 65_536;
const MAX_ADVANCED_AI_THEOREM_GRAPH_RESULT_LIMIT: u32 = 256;
const MAX_ADVANCED_AI_SMT_RAW_BYTES: usize = 64_000_000;
const MAX_ADVANCED_AI_SMT_ITEMS: u64 = 1_000_000;
const MAX_ADVANCED_AI_SMT_REFS: u64 = 65_536;
const MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS: u64 = 65_536;
const MAX_ADVANCED_AI_FORMALIZATION_SOURCE_BYTES: usize = 16_000_000;
const MAX_ADVANCED_AI_FORMALIZATION_REASON_BYTES: usize = 1_000_000;
const MAX_ADVANCED_AI_FORMALIZATION_TERM_BYTES: usize = 1_000_000;
const MAX_ADVANCED_AI_FORMALIZATION_UNIVERSE_PARAMS: u64 = 65_536;
const MAX_ADVANCED_AI_FORMALIZATION_TACTIC_ITEMS: u64 = 65_536;
const MAX_NAME_COMPONENTS: u64 = 256;
const MAX_STRING_BYTES: u64 = 1_048_576;

pub const ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT: &str = "/machine/advanced-ai/inductive/check";
pub const ADVANCED_AI_UNIVERSE_REPAIR_CHECK_ENDPOINT: &str =
    "/machine/advanced-ai/universe/repair/check";
pub const ADVANCED_AI_TYPECLASS_RESOLVE_ENDPOINT: &str = "/machine/advanced-ai/typeclass/resolve";
pub const ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT: &str = "/machine/advanced-ai/smt/reconstruct";
pub const ADVANCED_AI_THEOREM_GRAPH_QUERY_ENDPOINT: &str =
    "/machine/advanced-ai/theorem-graph/query";
pub const ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT: &str = "/machine/advanced-ai/formalize/check";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiProfileVersion {
    MvpV1,
}

impl AdvancedAiProfileVersion {
    fn tag(self) -> u8 {
        match self {
            Self::MvpV1 => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpV1),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiTaskKind {
    AdvancedInductive,
    UniverseRepair,
    TypeclassResolution,
    SmtCertificate,
    TheoremGraphQuery,
    NaturalLanguageFormalization,
}

impl AdvancedAiTaskKind {
    fn tag(self) -> u8 {
        match self {
            Self::AdvancedInductive => 0,
            Self::UniverseRepair => 1,
            Self::TypeclassResolution => 2,
            Self::SmtCertificate => 4,
            Self::TheoremGraphQuery => 5,
            Self::NaturalLanguageFormalization => 6,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::AdvancedInductive),
            1 => Some(Self::UniverseRepair),
            2 => Some(Self::TypeclassResolution),
            4 => Some(Self::SmtCertificate),
            5 => Some(Self::TheoremGraphQuery),
            6 => Some(Self::NaturalLanguageFormalization),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedAiTarget {
    pub env_fingerprint: Hash,
    pub target_decl_hash: Option<Hash>,
    pub goal_fingerprint: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedImportIdentity {
    pub module: ModuleName,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
}

impl AdvancedImportIdentity {
    pub fn from_verified_import(import: &VerifiedImportRef) -> Self {
        Self {
            module: import.module().clone(),
            export_hash: import.export_hash(),
            certificate_hash: import.certificate_hash(),
        }
    }
}

pub const ADVANCED_AI_EXTERNAL_INDEX_UPDATE_SCHEMA: &str =
    "npa.advanced-ai.external-index-update.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdvancedExternalIndexKind {
    TheoremGraph,
    Embedding,
    PremiseSet,
    Usage,
}

impl AdvancedExternalIndexKind {
    fn tag(self) -> u8 {
        match self {
            Self::TheoremGraph => 0,
            Self::Embedding => 1,
            Self::PremiseSet => 2,
            Self::Usage => 3,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedExternalIndexUpdateTrigger {
    Authoring,
    ExternalService,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedExternalIndexSchedulerIntegration {
    Deferred,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedExternalIndexUpdateRequest {
    pub module: ModuleName,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub indexes: Vec<AdvancedExternalIndexKind>,
    pub trigger: AdvancedExternalIndexUpdateTrigger,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedExternalIndexUpdateEntry {
    pub module: ModuleName,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub index: AdvancedExternalIndexKind,
    pub update_key_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedExternalIndexUpdatePlan {
    pub schema: &'static str,
    pub trigger: AdvancedExternalIndexUpdateTrigger,
    pub scheduler_integration: AdvancedExternalIndexSchedulerIntegration,
    pub module: ModuleName,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub entries: Vec<AdvancedExternalIndexUpdateEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedExternalIndexUpdateReport {
    pub schema: &'static str,
    pub trigger: AdvancedExternalIndexUpdateTrigger,
    pub scheduler_integration: AdvancedExternalIndexSchedulerIntegration,
    pub module: ModuleName,
    pub export_hash: Hash,
    pub updated_entries: Vec<AdvancedExternalIndexUpdateEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedExternalIndexUpdateError {
    Unavailable {
        index: AdvancedExternalIndexKind,
    },
    Rejected {
        index: AdvancedExternalIndexKind,
        reason: String,
    },
}

pub trait AdvancedExternalIndexUpdateSink {
    fn update_external_index(
        &mut self,
        entry: &AdvancedExternalIndexUpdateEntry,
    ) -> std::result::Result<(), AdvancedExternalIndexUpdateError>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedAiOptionsRef {
    Inline {
        options_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        options_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedAiCandidateEnvelope {
    pub profile_version: AdvancedAiProfileVersion,
    pub task_kind: AdvancedAiTaskKind,
    pub target: AdvancedAiTarget,
    pub imports: Vec<AdvancedImportIdentity>,
    pub options: AdvancedAiOptionsRef,
    pub payload: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiOptionsVersion {
    MvpV1,
}

impl AdvancedAiOptionsVersion {
    fn tag(self) -> u8 {
        match self {
            Self::MvpV1 => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpV1),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedIndependentCheckerProfile {
    IndependentCheckerMvpReference,
}

impl AdvancedIndependentCheckerProfile {
    fn tag(self) -> u8 {
        match self {
            Self::IndependentCheckerMvpReference => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::IndependentCheckerMvpReference),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedIndependentCheckerOptions {
    pub profile: AdvancedIndependentCheckerProfile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedInductiveOptions {
    pub approved_nested_type_constructors: Vec<AdvancedAiGlobalRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedTypeclassOptions {
    pub class_declarations: Vec<AdvancedAiGlobalRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTypeclassResolutionPlan {
    pub goal: AdvancedAiGoal,
    pub ordered_candidates: Vec<AdvancedMachineInstanceCandidateRef>,
    pub max_depth: u32,
    pub max_nodes: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineInstanceCandidateRef {
    pub target: AdvancedMachineInstanceTargetRef,
    pub priority_hint: Option<i32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineInstanceTargetRef {
    Imported { global_ref: AdvancedAiGlobalRef },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtOptions {
    pub eq: AdvancedAiGlobalRef,
    pub prop_false: Option<AdvancedAiGlobalRef>,
    pub prop_not: Option<AdvancedAiGlobalRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineSmtCertificateCandidate {
    pub goal: AdvancedAiGoal,
    pub solver: AdvancedSmtSolver,
    pub logic: AdvancedSmtLogic,
    pub encoded_problem: AdvancedMachineSmtProblemRef,
    pub certificate_format: AdvancedSmtCertificateFormat,
    pub rule_registry_profile: AdvancedSmtRuleRegistryProfile,
    pub proof_payload: AdvancedMachineSmtProofPayloadRef,
    pub reconstruction_plan: AdvancedMachineSmtReconstructionPlan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineSmtProblemRef {
    Inline {
        problem_hash: Hash,
        encoding_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        problem_hash: Hash,
        encoding_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineSmtEncodedProblem {
    pub encoder_version: AdvancedSmtEncoderVersion,
    pub goal_fingerprint: Hash,
    pub logic: AdvancedSmtLogic,
    pub command_profile: AdvancedSmtCommandProfile,
    pub commands: Vec<AdvancedSmtEncodedCommand>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolver {
    Cvc5,
    Z3,
    VeriT,
    OpaqueExternal,
}

impl AdvancedSmtSolver {
    fn tag(self) -> u8 {
        match self {
            Self::Cvc5 => 0,
            Self::Z3 => 1,
            Self::VeriT => 2,
            Self::OpaqueExternal => 3,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Cvc5),
            1 => Some(Self::Z3),
            2 => Some(Self::VeriT),
            3 => Some(Self::OpaqueExternal),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtPinnedSolverIdentity {
    pub solver: AdvancedSmtSolver,
    pub version_ascii: Vec<u8>,
    pub binary_hash: Hash,
    pub container_digest_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverNetworkPolicy {
    NoNetwork,
}

impl AdvancedSmtSolverNetworkPolicy {
    fn tag(self) -> u8 {
        match self {
            Self::NoNetwork => 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverFilesystemPolicy {
    ReadOnlyInputsWritableOutput,
}

impl AdvancedSmtSolverFilesystemPolicy {
    fn tag(self) -> u8 {
        match self {
            Self::ReadOnlyInputsWritableOutput => 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtSolverProcessPolicy {
    /// External SMT solver_process policy: no network, bounded output, and pinned child processes.
    pub network: AdvancedSmtSolverNetworkPolicy,
    pub filesystem: AdvancedSmtSolverFilesystemPolicy,
    pub max_output_bytes: u64,
    pub max_cpu_millis: u64,
    pub max_memory_bytes: u64,
    pub timeout_millis: u64,
    pub max_child_processes: u64,
    pub child_process_allowlist: Vec<Vec<u8>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtSolverProcessProfile {
    pub identity: AdvancedSmtPinnedSolverIdentity,
    pub arguments: Vec<Vec<u8>>,
    pub policy: AdvancedSmtSolverProcessPolicy,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtSolverHandoff {
    pub solver: AdvancedSmtSolver,
    pub supported_fragment: AdvancedSmtSupportedFragment,
    pub problem_canonical_bytes: Vec<u8>,
    pub smtlib_bytes: Vec<u8>,
    pub problem_hash: Hash,
    pub smtlib_hash: Hash,
    pub encoding_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub solver_process_profile_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AdvancedSmtSolverResourceUsage {
    pub output_bytes: u64,
    pub cpu_millis: u64,
    pub memory_bytes: u64,
    pub wall_clock_millis: u64,
    pub child_processes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverBareResult {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverOutputRef {
    CertificatePayload {
        certificate_format: AdvancedSmtCertificateFormat,
        payload_hash: Hash,
        size_bytes: u64,
    },
    ProofNodeTable {
        payload_hash: Hash,
        node_count: u64,
        size_bytes: u64,
    },
    CounterexampleModel {
        model_hash: Hash,
        size_bytes: u64,
    },
    BareResult {
        result: AdvancedSmtSolverBareResult,
    },
    ExitStatus {
        code: i32,
    },
    Logs {
        stdout_hash: Hash,
        stderr_hash: Hash,
        size_bytes: u64,
    },
    UncheckedProofText {
        proof_text_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtSolverProcessResult {
    pub solver_process_profile_hash: Hash,
    pub smtlib_hash: Hash,
    pub output: AdvancedSmtSolverOutputRef,
    pub resource_usage: AdvancedSmtSolverResourceUsage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverHandoffPayloadKind {
    CertificatePayload,
    ProofNodeTable,
    CounterexampleModel,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverResourceField {
    OutputBytes,
    CpuMillis,
    MemoryBytes,
    WallClockMillis,
    ChildProcesses,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSolverHandoffError {
    MissingEnvironmentHash,
    MissingPolicyHash,
    NonCanonicalSolverProcessProfile,
    UnsupportedFragment,
    ProblemHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    EncodingHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    SmtLibHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    PolicyHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    SolverVersionMetadataMismatch {
        expected: Hash,
        actual: Hash,
    },
    ResourceLimitExceeded {
        field: AdvancedSmtSolverResourceField,
        limit: u64,
        actual: u64,
    },
    MissingPayloadHash,
    BareResultOnly,
    ExitStatusOnly,
    LogsOnly,
    UncheckedProofText,
    OpaquePayloadWithoutRegisteredChecker,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtCommandProfile {
    MvpNormalizedQf,
}

impl AdvancedSmtCommandProfile {
    fn tag(self) -> u8 {
        match self {
            Self::MvpNormalizedQf => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpNormalizedQf),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtLogic {
    MvpQfUf,
    MvpQfLia,
    MvpQfBv,
    MvpQfUfLiaBv,
}

impl AdvancedSmtLogic {
    fn tag(self) -> u8 {
        match self {
            Self::MvpQfUf => 0,
            Self::MvpQfLia => 1,
            Self::MvpQfBv => 2,
            Self::MvpQfUfLiaBv => 3,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpQfUf),
            1 => Some(Self::MvpQfLia),
            2 => Some(Self::MvpQfBv),
            3 => Some(Self::MvpQfUfLiaBv),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtEncoderVersion {
    MvpNormalizedQfV1,
}

impl AdvancedSmtEncoderVersion {
    fn tag(self) -> u8 {
        match self {
            Self::MvpNormalizedQfV1 => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpNormalizedQfV1),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtCertificateFormat {
    MvpProofNodeTableV1,
    AletheOpaqueV1,
    LfscOpaqueV1,
    SolverResultOnlyV1,
}

impl AdvancedSmtCertificateFormat {
    fn tag(self) -> u8 {
        match self {
            Self::MvpProofNodeTableV1 => 0,
            Self::AletheOpaqueV1 => 1,
            Self::LfscOpaqueV1 => 2,
            Self::SolverResultOnlyV1 => 3,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpProofNodeTableV1),
            1 => Some(Self::AletheOpaqueV1),
            2 => Some(Self::LfscOpaqueV1),
            3 => Some(Self::SolverResultOnlyV1),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSupportedFragment {
    QfPropositional,
    QfEuf,
    QfSimpleLia,
    QfEufLia,
    QfBitVecBitblastLrat,
}

impl AdvancedSmtSupportedFragment {
    fn tag(self) -> u8 {
        match self {
            Self::QfPropositional => 0,
            Self::QfEuf => 1,
            Self::QfSimpleLia => 2,
            Self::QfEufLia => 3,
            Self::QfBitVecBitblastLrat => 4,
        }
    }

    pub fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::QfPropositional),
            1 => Some(Self::QfEuf),
            2 => Some(Self::QfSimpleLia),
            3 => Some(Self::QfEufLia),
            4 => Some(Self::QfBitVecBitblastLrat),
            _ => None,
        }
    }

    fn smtlib_logic(self) -> &'static str {
        match self {
            Self::QfPropositional => "QF_UF",
            Self::QfEuf => "QF_UF",
            Self::QfSimpleLia => "QF_LIA",
            Self::QfEufLia => "QF_UFLIA",
            Self::QfBitVecBitblastLrat => "QF_BV",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSupportedSortProfile {
    BoolOnly,
    BoolAndUninterpreted,
    BoolAndInt,
    BoolIntAndUninterpreted,
    BoolAndBitVec,
}

impl AdvancedSmtSupportedSortProfile {
    fn tag(self) -> u8 {
        match self {
            Self::BoolOnly => 0,
            Self::BoolAndUninterpreted => 1,
            Self::BoolAndInt => 2,
            Self::BoolIntAndUninterpreted => 3,
            Self::BoolAndBitVec => 4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSupportedOperatorProfile {
    PropositionalCore,
    EufCore,
    SimpleLia,
    EufLia,
    BitVecViaBitblastLrat,
}

impl AdvancedSmtSupportedOperatorProfile {
    fn tag(self) -> u8 {
        match self {
            Self::PropositionalCore => 0,
            Self::EufCore => 1,
            Self::SimpleLia => 2,
            Self::EufLia => 3,
            Self::BitVecViaBitblastLrat => 4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtCheckerProfile {
    KernelCheckedPayloadNodeV1,
    BitblastLratBridgeV1,
}

impl AdvancedSmtCheckerProfile {
    fn tag(self) -> u8 {
        match self {
            Self::KernelCheckedPayloadNodeV1 => 0,
            Self::BitblastLratBridgeV1 => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSoundnessRequirement {
    KernelCheckedPayloadNode,
    EufCongruenceReconstruction,
    SimpleLiaReconstruction,
    EufLiaCombination,
    BitblastLratSoundnessBridge,
}

impl AdvancedSmtSoundnessRequirement {
    fn tag(self) -> u8 {
        match self {
            Self::KernelCheckedPayloadNode => 0,
            Self::EufCongruenceReconstruction => 1,
            Self::SimpleLiaReconstruction => 2,
            Self::EufLiaCombination => 3,
            Self::BitblastLratSoundnessBridge => 4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtEncodingError {
    UnsupportedFragment,
    NonCanonicalPayload,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtCertificateMetadata {
    pub format: AdvancedSmtCertificateFormat,
    pub solver: AdvancedSmtSolver,
    pub logic: AdvancedSmtLogic,
    pub encoded_goal_hash: Hash,
    pub smt_problem_hash: Hash,
    pub proof_hash: Hash,
    pub reconstruction: AdvancedSmtReconstructionMetadata,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtReconstructionMetadata {
    pub rule_registry_profile: AdvancedSmtRuleRegistryProfile,
    pub reconstruction_plan_hash: Hash,
    pub imported_theory_count: u64,
    pub step_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtNatToIntSideCondition {
    pub source_core_expr: Expr,
    pub int_symbol: AdvancedSmtSymbol,
    pub nonnegative_assertion: AdvancedSmtExpr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtRuleRegistryProfile {
    MvpEmptyRegistryV1,
    MvpProofNodeTableQfV1,
}

impl AdvancedSmtRuleRegistryProfile {
    fn tag(self) -> u8 {
        match self {
            Self::MvpEmptyRegistryV1 => 0,
            Self::MvpProofNodeTableQfV1 => 1,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpEmptyRegistryV1),
            1 => Some(Self::MvpProofNodeTableQfV1),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtRuleDescriptorKind {
    MvpKernelCheckedPayloadNodeV1,
    BitblastLratSoundnessBridgeV1,
}

impl AdvancedSmtRuleDescriptorKind {
    fn tag(self) -> u8 {
        match self {
            Self::MvpKernelCheckedPayloadNodeV1 => 0,
            Self::BitblastLratSoundnessBridgeV1 => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtRuleDescriptor {
    pub rule_registry_profile: AdvancedSmtRuleRegistryProfile,
    pub certificate_format: AdvancedSmtCertificateFormat,
    pub logic: AdvancedSmtLogic,
    pub command_profile: AdvancedSmtCommandProfile,
    pub supported_fragment: AdvancedSmtSupportedFragment,
    pub supported_sort_profile: AdvancedSmtSupportedSortProfile,
    pub supported_operator_profile: AdvancedSmtSupportedOperatorProfile,
    pub kind: AdvancedSmtRuleDescriptorKind,
    pub checker_profile: AdvancedSmtCheckerProfile,
    pub soundness_requirements: Vec<AdvancedSmtSoundnessRequirement>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtRuleRegistry {
    pub profile: AdvancedSmtRuleRegistryProfile,
    pub descriptors: Vec<AdvancedSmtRuleDescriptor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtProveHashes {
    pub problem_hash: Hash,
    pub proof_hash: Hash,
    pub npa_proof_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtSymbol {
    pub ascii: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtEncodedCommand {
    pub phase: AdvancedSmtCommandPhase,
    pub command_id: Hash,
    pub payload: AdvancedSmtCommandPayload,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdvancedSmtCommandPhase {
    SortDecl,
    DatatypeDecl,
    FunctionDecl,
    ContextAssumption,
    TargetAssertion,
    FinalCheck,
}

impl AdvancedSmtCommandPhase {
    fn tag(self) -> u8 {
        match self {
            Self::SortDecl => 0,
            Self::DatatypeDecl => 1,
            Self::FunctionDecl => 2,
            Self::ContextAssumption => 3,
            Self::TargetAssertion => 4,
            Self::FinalCheck => 5,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::SortDecl),
            1 => Some(Self::DatatypeDecl),
            2 => Some(Self::FunctionDecl),
            3 => Some(Self::ContextAssumption),
            4 => Some(Self::TargetAssertion),
            5 => Some(Self::FinalCheck),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtCommandPayload {
    SortDecl {
        symbol: AdvancedSmtSymbol,
        arity: u32,
    },
    FunctionDecl {
        symbol: AdvancedSmtSymbol,
        args: Vec<AdvancedSmtSortExpr>,
        result: AdvancedSmtSortExpr,
    },
    DatatypeDecl {
        symbol: AdvancedSmtSymbol,
        constructors: Vec<AdvancedSmtDatatypeConstructor>,
    },
    ContextAssumption {
        source_local_index: u32,
        core_expr: Expr,
        encoded_expr: AdvancedSmtExpr,
    },
    TargetAssertion {
        core_expr: Expr,
        encoded_expr: AdvancedSmtExpr,
    },
    FinalCheck,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtSortExpr {
    Bool,
    Int,
    BitVec {
        width: u32,
    },
    User {
        symbol: AdvancedSmtSymbol,
        args: Vec<AdvancedSmtSortExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtDatatypeConstructor {
    pub constructor: AdvancedSmtSymbol,
    pub selectors: Vec<AdvancedSmtDatatypeSelector>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtDatatypeSelector {
    pub selector: AdvancedSmtSymbol,
    pub sort: AdvancedSmtSortExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtExpr {
    Var {
        symbol: AdvancedSmtSymbol,
        sort: AdvancedSmtSortExpr,
    },
    BoolLit(bool),
    IntLit(i128),
    BitVecLit {
        width: u32,
        value: Vec<u8>,
    },
    App {
        symbol: AdvancedSmtSymbol,
        args: Vec<AdvancedSmtExpr>,
        result_sort: AdvancedSmtSortExpr,
    },
    BuiltinApp {
        op: AdvancedSmtBuiltinOp,
        args: Vec<AdvancedSmtExpr>,
        result_sort: AdvancedSmtSortExpr,
    },
    Not(Box<AdvancedSmtExpr>),
    And(Vec<AdvancedSmtExpr>),
    Or(Vec<AdvancedSmtExpr>),
    Eq(Box<AdvancedSmtExpr>, Box<AdvancedSmtExpr>),
    Imp(Box<AdvancedSmtExpr>, Box<AdvancedSmtExpr>),
    Ite {
        cond: Box<AdvancedSmtExpr>,
        then_expr: Box<AdvancedSmtExpr>,
        else_expr: Box<AdvancedSmtExpr>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtBuiltinOp {
    IntNeg,
    IntAdd,
    IntSub,
    IntLe,
    IntLt,
    IntGe,
    IntGt,
    BvNot,
    BvAnd,
    BvOr,
    BvXor,
    BvAdd,
    BvSub,
    BvMul,
    BvUlt,
    BvUle,
    BvConcat,
    BvExtract { high: u32, low: u32 },
}

impl AdvancedSmtBuiltinOp {
    fn tag(self) -> u8 {
        match self {
            Self::IntNeg => 0,
            Self::IntAdd => 1,
            Self::IntSub => 2,
            Self::IntLe => 3,
            Self::IntLt => 4,
            Self::IntGe => 5,
            Self::IntGt => 6,
            Self::BvNot => 7,
            Self::BvAnd => 8,
            Self::BvOr => 9,
            Self::BvXor => 10,
            Self::BvAdd => 11,
            Self::BvSub => 12,
            Self::BvMul => 13,
            Self::BvUlt => 14,
            Self::BvUle => 15,
            Self::BvConcat => 16,
            Self::BvExtract { .. } => 17,
        }
    }

    fn from_tag(tag: u8, decoder: &mut Decoder<'_>) -> std::result::Result<Self, DecodeError> {
        Ok(match tag {
            0 => Self::IntNeg,
            1 => Self::IntAdd,
            2 => Self::IntSub,
            3 => Self::IntLe,
            4 => Self::IntLt,
            5 => Self::IntGe,
            6 => Self::IntGt,
            7 => Self::BvNot,
            8 => Self::BvAnd,
            9 => Self::BvOr,
            10 => Self::BvXor,
            11 => Self::BvAdd,
            12 => Self::BvSub,
            13 => Self::BvMul,
            14 => Self::BvUlt,
            15 => Self::BvUle,
            16 => Self::BvConcat,
            17 => Self::BvExtract {
                high: decoder.u32()?,
                low: decoder.u32()?,
            },
            _ => return Err(DecodeError::Malformed),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtProofNodeTable {
    pub certificate_format: AdvancedSmtCertificateFormat,
    pub nodes: Vec<AdvancedSmtProofNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtProofNode {
    pub node_id: u32,
    pub rule_fingerprint: Hash,
    pub premises: Vec<u32>,
    pub conclusion_encoding: AdvancedSmtConclusionEncoding,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedSmtConclusionEncoding {
    pub encoder_version: AdvancedSmtEncoderVersion,
    pub logic: AdvancedSmtLogic,
    pub command_profile: AdvancedSmtCommandProfile,
    pub core_expr: Expr,
    pub encoded_expr: AdvancedSmtExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineSmtProofPayloadRef {
    Inline {
        payload_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        payload_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineSmtReconstructionPlan {
    pub imported_theory_refs: Vec<AdvancedAiGlobalRef>,
    pub steps: Vec<AdvancedMachineSmtReconstructionStep>,
    pub final_step: u32,
    pub final_proof: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineSmtReconstructionStep {
    pub step_id: u32,
    pub rule: AdvancedSmtReconstructionRule,
    pub payload_bindings: Vec<AdvancedMachineSmtPayloadBinding>,
    pub premises: Vec<u32>,
    pub conclusion: Expr,
    pub proof: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineSmtPayloadBinding {
    pub payload_hash: Hash,
    pub node_id: u32,
    pub rule_fingerprint: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtReconstructionRule {
    PayloadNode {
        certificate_format: AdvancedSmtCertificateFormat,
        rule_fingerprint: Hash,
    },
    LocalBookkeeping {
        kind: AdvancedSmtLocalBookkeepingRule,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedSmtLocalBookkeepingRule {
    ReorderPremises {
        permutation: Vec<u32>,
    },
    IntroduceTheoryLemma {
        lemma: AdvancedAiGlobalRef,
        level_args: Vec<Level>,
        term_args: Vec<Expr>,
    },
    ComposeProof {
        combinator: AdvancedAiGlobalRef,
        level_args: Vec<Level>,
        term_args: Vec<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedFormalizationOptions {
    pub tactic_options_canonical_bytes: Vec<u8>,
    pub tactic_budget_canonical_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedAiOptions {
    pub schema_version: AdvancedAiOptionsVersion,
    pub independent_checker: AdvancedIndependentCheckerOptions,
    pub advanced_inductive: AdvancedInductiveOptions,
    pub typeclass: AdvancedTypeclassOptions,
    pub smt: Option<AdvancedSmtOptions>,
    pub formalization: Option<AdvancedFormalizationOptions>,
}

impl Default for AdvancedAiOptions {
    fn default() -> Self {
        Self {
            schema_version: AdvancedAiOptionsVersion::MvpV1,
            independent_checker: AdvancedIndependentCheckerOptions {
                profile: AdvancedIndependentCheckerProfile::IndependentCheckerMvpReference,
            },
            advanced_inductive: AdvancedInductiveOptions {
                approved_nested_type_constructors: Vec::new(),
            },
            typeclass: AdvancedTypeclassOptions {
                class_declarations: Vec::new(),
            },
            smt: None,
            formalization: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedAiGlobalRef {
    pub module: ModuleName,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub name: Name,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineInductiveProposal {
    pub block_name: Option<Name>,
    pub expected_decl_hash: Option<Hash>,
    pub universe_params: Vec<String>,
    pub inductives: Vec<AdvancedMachineInductiveFamilyProposal>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineInductiveFamilyProposal {
    pub name: Name,
    pub params: Vec<AdvancedMachineTelescopeBinder>,
    pub indices: Vec<AdvancedMachineTelescopeBinder>,
    pub result_sort: Level,
    pub constructors: Vec<AdvancedMachineConstructorProposal>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTelescopeBinder {
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineConstructorProposal {
    pub name: Name,
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedAiGoal {
    pub universe_params: Vec<String>,
    pub local_context: Vec<MachineLocalDecl>,
    pub target: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineFormalizationCheckPayload {
    pub candidate: AdvancedMachineFormalizationCandidate,
    pub intent_record: Option<AdvancedFormalizationIntentRecord>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineFormalizationCandidate {
    pub source_document: AdvancedMachineFormalizationSourceDocumentRef,
    pub claim_span: AdvancedMachineFormalizationClaimSpan,
    pub statement: AdvancedMachineSurfaceTerm,
    pub optional_proof_candidate: Option<AdvancedMachineFormalizationProofCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineSurfaceTerm {
    pub universe_params: Vec<String>,
    pub term_canonical_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineFormalizationProofCandidate {
    pub candidate_statement_hash: Hash,
    pub tactic: MachineTacticCandidate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineFormalizationSourceDocumentRef {
    Inline {
        source_document_hash: Hash,
        raw_utf8_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        source_document_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineFormalizationClaimSpan {
    pub start_byte: u64,
    pub end_byte: u64,
    pub claim_span_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedReviewerId {
    Human {
        stable_id_ascii: Vec<u8>,
    },
    System {
        system_id_ascii: Vec<u8>,
        actor_id_ascii: Vec<u8>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedFormalizationIntentRecord {
    pub source_document_hash: Hash,
    pub claim_span_hash: Hash,
    pub candidate_statement_hash: Hash,
    pub status: AdvancedFormalizationIntentStatus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedFormalizationIntentStatus {
    Unreviewed,
    Reviewed {
        reviewer: AdvancedReviewerId,
        accepted_statement_hash: Hash,
    },
    Rejected {
        reviewer: AdvancedReviewerId,
        rejection_reason: AdvancedMachineFormalizationRejectionReasonRef,
        rejection_reason_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineFormalizationRejectionReasonRef {
    Inline {
        rejection_reason_hash: Hash,
        raw_utf8_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        rejection_reason_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedUniverseRepairCandidate {
    pub goal: Option<AdvancedAiGoal>,
    pub target_expr: Expr,
    pub instantiations: Vec<AdvancedUniverseInstantiationPatch>,
    pub constraint_hints: Vec<AdvancedUniverseConstraintHint>,
    pub minimization_hint: Option<AdvancedUniverseMinimizationHint>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedUniverseInstantiationPatch {
    pub occurrence: AdvancedMachineExprOccurrence,
    pub explicit_level_args: Vec<Level>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineExprOccurrence {
    pub path: Vec<AdvancedMachineExprPathStep>,
    pub expected_ref: AdvancedAiGlobalRef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdvancedMachineExprPathStep {
    AppFun,
    AppArg,
    LamType,
    LamBody,
    PiDomain,
    PiCodomain,
    LetType,
    LetValue,
    LetBody,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedUniverseConstraintHint {
    pub constraint: AdvancedUniverseConstraint,
    pub reason: AdvancedUniverseConstraintHintReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedUniverseConstraint {
    pub lhs: Level,
    pub relation: AdvancedUniverseConstraintRelation,
    pub rhs: Level,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedUniverseConstraintRelation {
    Le,
    Eq,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedUniverseConstraintHintReason {
    KernelDiagnostic,
    RepairCandidate,
    MinimizationExplanation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedUniverseMinimizationHint {
    KernelDefault,
    PreferLowerLevels,
    PreferExistingExplicitArgs,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiValidationError {
    EnvelopeMalformed,
    TargetFingerprintMismatch,
    ImportClosureMismatch,
    PayloadHashMismatch,
    KernelRejected,
    IndependentCheckerRejected,
    NonDeterministicResult,
    BudgetExceeded,
    AmbiguousResolution,
    NoSolution,
    FeatureRejected,
    UnsupportedFeature,
}

impl AdvancedAiValidationError {
    fn tag(self) -> u8 {
        match self {
            Self::EnvelopeMalformed => 0,
            Self::TargetFingerprintMismatch => 1,
            Self::ImportClosureMismatch => 2,
            Self::PayloadHashMismatch => 3,
            Self::KernelRejected => 4,
            Self::IndependentCheckerRejected => 5,
            Self::NonDeterministicResult => 6,
            Self::BudgetExceeded => 7,
            Self::AmbiguousResolution => 8,
            Self::NoSolution => 9,
            Self::FeatureRejected => 10,
            Self::UnsupportedFeature => 11,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiEndpointError {
    NonCanonicalRequestBytes,
    ArtifactUnavailable,
    InternalValidatorFailure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiFeatureError {
    AdvancedInductive(AdvancedInductiveError),
    UniverseRepair(AdvancedUniverseRepairError),
    TypeclassResolution(AdvancedTypeclassResolutionError),
    SmtCertificate(AdvancedSmtCertificateError),
    TheoremGraphQuery(AdvancedTheoremGraphError),
    Formalization(AdvancedFormalizationError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedInductiveError {
    TargetRefMismatch,
    PositivityProfileUnsupported,
    ArtifactGeneratorUnavailable,
    GeneratedArtifactMismatch,
    NameCollision,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedUniverseRepairError {
    UnknownUniverseParam,
    IllFormedLevelExpr,
    UnsatisfiedConstraint,
    NonCanonicalSolution,
    TargetFingerprintMismatch,
    InvalidOccurrencePath,
    AmbiguousOccurrence,
    TargetRefMismatch,
    ConstraintHintMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedTypeclassResolutionError {
    ClassDeclarationMismatch,
    CandidateInterfaceInvalid,
    ClassHeadUnsupported,
    NoSolution,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedSmtCertificateError {
    EncodingMismatch,
    RuleFingerprintMismatch,
    RuleRegistryMismatch,
    NonCanonicalPayload,
    ReconstructionProofMismatch,
    ConclusionEncodingMismatch,
    PayloadBindingMismatch,
    ReconstructionConclusionMismatch,
    ReconstructionPremiseMismatch,
    PublicInterfaceMismatch,
    TheoryRefMismatch,
    UnsupportedFragment,
    SolverResultOnly,
    MalformedProofPayload,
    ReconstructionPlanHashMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedTheoremGraphError {
    SnapshotMalformed,
    QueryFeaturesMalformed,
    NodeResolutionMismatch,
    LimitOutOfRange,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedFormalizationError {
    IntentRecordMismatch,
    CandidateStatementElaborationFailed,
    FormalizationProofStatementMismatch,
    RejectedIntentHasProofCandidate,
    ProofBridgeFailed,
}

/// Deterministic validation output for untrusted Phase 9 advanced AI endpoints.
///
/// A success payload is endpoint-specific replay evidence or a checked proof
/// candidate fragment. It is not a checker verdict; certificate acceptance is
/// still decided by the Rust kernel and independent checker over canonical
/// certificates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedAiSuccessPayload {
    AdvancedInductive {
        decl_interface_hash: Hash,
        decl_certificate_hash: Hash,
    },
    UniverseRepair {
        repaired_expr: Expr,
        constraint_set_hash: Hash,
    },
    TypeclassResolution {
        proof: Expr,
    },
    SmtCertificate {
        final_proof: Expr,
    },
    TheoremGraphQuery {
        result: AdvancedMachineTheoremGraphResult,
    },
    NaturalLanguageFormalization {
        kind: AdvancedFormalizationSuccessKind,
        accepted_statement_hash: Option<Hash>,
        formalization_proof_root_hash: Option<Hash>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphResult {
    pub entries: Vec<AdvancedMachineTheoremGraphResultEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphResultEntry {
    pub node: AdvancedMachineTheoremGraphNodeRef,
    pub score: AdvancedMachineTheoremGraphScore,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphScore {
    pub score_microunits: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphNodeRef {
    pub module: ModuleName,
    pub name: Name,
    pub export_hash: Hash,
    pub decl_certificate_hash: Hash,
    pub type_hash: Hash,
    pub certificate_hash: Hash,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphQuery {
    pub env_fingerprint: Hash,
    pub goal_fingerprint: Hash,
    pub goal: AdvancedAiGoal,
    pub snapshot: AdvancedMachineTheoremGraphSnapshotRef,
    pub query_features: AdvancedMachineTheoremGraphQueryFeaturesRef,
    pub ranking_profile: AdvancedTheoremGraphRankingProfile,
    pub limit: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphSnapshotRef {
    pub source_release_hash: Hash,
    pub extractor_version: AdvancedTheoremGraphExtractorVersion,
    pub source: AdvancedMachineTheoremGraphSnapshotSource,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineTheoremGraphSnapshotSource {
    Inline {
        graph_snapshot_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        graph_snapshot_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedMachineTheoremGraphQueryFeaturesRef {
    Inline {
        query_features_hash: Hash,
        canonical_bytes: Vec<u8>,
    },
    Artifact {
        path: String,
        file_hash: Hash,
        query_features_hash: Hash,
        size_bytes: u64,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedTheoremGraphRankingProfile {
    MvpTupleOrder,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphSnapshot {
    pub source_release_hash: Hash,
    pub extractor_version: AdvancedTheoremGraphExtractorVersion,
    pub nodes: Vec<AdvancedMachineTheoremGraphNodeRef>,
    pub edges: Vec<AdvancedMachineTheoremGraphEdge>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphEdge {
    pub from: AdvancedMachineTheoremGraphNodeRef,
    pub to: AdvancedMachineTheoremGraphNodeRef,
    pub kind: AdvancedTheoremGraphEdgeKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphQueryFeatures {
    pub env_fingerprint: Hash,
    pub goal_fingerprint: Hash,
    pub feature_schema_version: AdvancedTheoremGraphFeatureSchemaVersion,
    pub features: Vec<AdvancedMachineTheoremGraphFeature>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedMachineTheoremGraphFeature {
    pub key: AdvancedTheoremGraphFeatureKey,
    pub value: AdvancedTheoremGraphFeatureValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedTheoremGraphExtractorVersion {
    MvpCertificateGraphV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedTheoremGraphFeatureSchemaVersion {
    MvpGoalFeaturesV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedTheoremGraphEdgeKind {
    ImportsDeclaration,
    UsesConstant,
    MentionsType,
    UsedBy,
    SimilarStatement,
    AxiomPath,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedTheoremGraphFeatureKey {
    pub namespace_ascii: Vec<u8>,
    pub name_ascii: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedTheoremGraphFeatureValue {
    Bool(bool),
    I64(i64),
    Hash(Hash),
}

impl AdvancedTheoremGraphRankingProfile {
    fn tag(self) -> u8 {
        match self {
            Self::MvpTupleOrder => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpTupleOrder),
            _ => None,
        }
    }
}

impl AdvancedTheoremGraphExtractorVersion {
    fn tag(self) -> u8 {
        match self {
            Self::MvpCertificateGraphV1 => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpCertificateGraphV1),
            _ => None,
        }
    }
}

impl AdvancedTheoremGraphFeatureSchemaVersion {
    fn tag(self) -> u8 {
        match self {
            Self::MvpGoalFeaturesV1 => 0,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::MvpGoalFeaturesV1),
            _ => None,
        }
    }
}

impl AdvancedTheoremGraphEdgeKind {
    fn tag(self) -> u8 {
        match self {
            Self::ImportsDeclaration => 0,
            Self::UsesConstant => 1,
            Self::MentionsType => 2,
            Self::UsedBy => 3,
            Self::SimilarStatement => 4,
            Self::AxiomPath => 5,
        }
    }

    fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::ImportsDeclaration),
            1 => Some(Self::UsesConstant),
            2 => Some(Self::MentionsType),
            3 => Some(Self::UsedBy),
            4 => Some(Self::SimilarStatement),
            5 => Some(Self::AxiomPath),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedFormalizationSuccessKind {
    CandidateStatementChecked,
    IntentRecordOnly,
    ProofBridgeChecked,
}

/// Phase 9 advanced AI endpoint response.
///
/// The response records candidate and validation-result hashes for deterministic
/// replay. `Success` means the untrusted endpoint accepted its bounded
/// validation task; it does not mean the final certificate has been accepted by
/// the trusted checker boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdvancedAiEndpointResponse {
    Success {
        candidate_hash: Hash,
        validation_result_hash: Hash,
        payload: Box<AdvancedAiSuccessPayload>,
    },
    Rejected {
        candidate_hash: Hash,
        validation_result_hash: Hash,
        error: AdvancedAiValidationError,
        feature_error: Option<AdvancedAiFeatureError>,
    },
    Error {
        error: AdvancedAiEndpointError,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedValidatedCommonEnvelope {
    pub candidate_hash: Hash,
    pub options_hash: Hash,
    pub env_fingerprint: Hash,
    pub envelope: AdvancedAiCandidateEnvelope,
    pub options: AdvancedAiOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvancedFormalizationRequestMetadata {
    pub candidate_hash: Hash,
    pub candidate_statement_hash: Hash,
    pub payload: AdvancedMachineFormalizationCheckPayload,
    pub request_without_proof_candidate_canonical_bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvancedAiCanonicalError {
    InvalidName,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DecodeError {
    Malformed,
    TheoremGraphSnapshotBytesTooLarge,
    TheoremGraphQueryFeaturesBytesTooLarge,
}

pub fn advanced_ai_candidate_hash(envelope_canonical_bytes: &[u8]) -> Hash {
    hash_with_domain(CANDIDATE_HASH_TAG, envelope_canonical_bytes)
}

pub fn advanced_ai_options_hash(options_canonical_bytes: &[u8]) -> Hash {
    hash_with_domain(OPTIONS_HASH_TAG, options_canonical_bytes)
}

pub fn advanced_ai_file_hash(bytes: &[u8]) -> Hash {
    sha256(bytes)
}

pub fn advanced_external_index_update_key_hash(
    module: &ModuleName,
    export_hash: Hash,
    index: AdvancedExternalIndexKind,
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    let mut payload = Vec::new();
    encode_name_to(&mut payload, module)?;
    encode_hash_to(&mut payload, &export_hash);
    payload.push(index.tag());
    Ok(hash_with_domain(
        EXTERNAL_INDEX_UPDATE_KEY_HASH_TAG,
        &payload,
    ))
}

/// Build the external-index opt-in update plan for external authoring indexes.
///
/// Scheduler-driven asynchronous coalescing remains deferred behind this
/// explicit authoring/service boundary; normal verification does not consult
/// this plan or any sink implementation.
pub fn advanced_external_index_update_plan(
    request: AdvancedExternalIndexUpdateRequest,
) -> std::result::Result<AdvancedExternalIndexUpdatePlan, AdvancedAiCanonicalError> {
    let indexes = request.indexes.into_iter().collect::<BTreeSet<_>>();
    let entries = indexes
        .into_iter()
        .map(|index| {
            let update_key_hash = advanced_external_index_update_key_hash(
                &request.module,
                request.export_hash,
                index,
            )?;
            Ok(AdvancedExternalIndexUpdateEntry {
                module: request.module.clone(),
                export_hash: request.export_hash,
                certificate_hash: request.certificate_hash,
                index,
                update_key_hash,
            })
        })
        .collect::<std::result::Result<Vec<_>, AdvancedAiCanonicalError>>()?;
    Ok(AdvancedExternalIndexUpdatePlan {
        schema: ADVANCED_AI_EXTERNAL_INDEX_UPDATE_SCHEMA,
        trigger: request.trigger,
        scheduler_integration: AdvancedExternalIndexSchedulerIntegration::Deferred,
        module: request.module,
        export_hash: request.export_hash,
        certificate_hash: request.certificate_hash,
        entries,
    })
}

pub fn run_advanced_external_index_update_plan<S: AdvancedExternalIndexUpdateSink + ?Sized>(
    plan: &AdvancedExternalIndexUpdatePlan,
    sink: &mut S,
) -> std::result::Result<AdvancedExternalIndexUpdateReport, AdvancedExternalIndexUpdateError> {
    let mut updated_entries = Vec::with_capacity(plan.entries.len());
    for entry in &plan.entries {
        sink.update_external_index(entry)?;
        updated_entries.push(entry.clone());
    }
    Ok(AdvancedExternalIndexUpdateReport {
        schema: plan.schema,
        trigger: plan.trigger,
        scheduler_integration: plan.scheduler_integration,
        module: plan.module.clone(),
        export_hash: plan.export_hash,
        updated_entries,
    })
}

pub fn advanced_ai_validation_result_hash_for_rejection(
    candidate_hash: Hash,
    error: AdvancedAiValidationError,
    feature_error: Option<AdvancedAiFeatureError>,
) -> Hash {
    let mut payload = Vec::new();
    payload.push(1);
    encode_validation_error_to(&mut payload, error);
    encode_feature_error_option_to(&mut payload, feature_error);
    validation_result_hash(candidate_hash, &payload)
}

pub fn advanced_ai_validation_result_hash_for_success(
    candidate_hash: Hash,
    success: &AdvancedAiSuccessPayload,
) -> Hash {
    let mut payload = Vec::new();
    payload.push(0);
    encode_success_payload_to(&mut payload, success);
    validation_result_hash(candidate_hash, &payload)
}

pub fn advanced_ai_env_fingerprint(
    profile_version: AdvancedAiProfileVersion,
    task_kind: AdvancedAiTaskKind,
    imports: &[AdvancedImportIdentity],
    options_hash: Hash,
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    let mut payload = Vec::new();
    payload.push(profile_version.tag());
    payload.push(task_kind.tag());
    encode_import_identities_to(&mut payload, imports)?;
    encode_hash_to(&mut payload, &options_hash);
    Ok(hash_with_domain(ENV_FINGERPRINT_TAG, &payload))
}

pub fn advanced_ai_goal_fingerprint(env_fingerprint: Hash, goal: &AdvancedAiGoal) -> Hash {
    let mut payload = Vec::new();
    encode_hash_to(&mut payload, &env_fingerprint);
    payload.extend_from_slice(&advanced_ai_universe_params_canonical_bytes(
        &goal.universe_params,
    ));
    payload.extend_from_slice(&machine_local_context_canonical_bytes(&goal.local_context));
    payload.extend_from_slice(&npa_cert::core_expr_canonical_bytes(&goal.target));
    hash_with_domain(GOAL_FINGERPRINT_TAG, &payload)
}

pub fn advanced_ai_goal_canonical_bytes(
    goal: &AdvancedAiGoal,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_goal_to(&mut out, goal)?;
    Ok(out)
}

pub fn advanced_ai_formalization_payload_canonical_bytes(
    payload: &AdvancedMachineFormalizationCheckPayload,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_formalization_payload_to(&mut out, payload)?;
    Ok(out)
}

pub fn advanced_ai_formalization_source_document_hash(raw_utf8_bytes: &[u8]) -> Hash {
    hash_with_domain(FORMALIZATION_SOURCE_DOCUMENT_HASH_TAG, raw_utf8_bytes)
}

pub fn advanced_ai_formalization_claim_span_hash(
    source_document_hash: Hash,
    start_byte: u64,
    end_byte: u64,
    claim_bytes: &[u8],
) -> Hash {
    let mut payload = Vec::new();
    encode_hash_to(&mut payload, &source_document_hash);
    encode_u64_to(&mut payload, start_byte);
    encode_u64_to(&mut payload, end_byte);
    payload.extend_from_slice(claim_bytes);
    hash_with_domain(FORMALIZATION_CLAIM_SPAN_HASH_TAG, &payload)
}

pub fn advanced_ai_formalization_rejection_reason_hash(raw_utf8_bytes: &[u8]) -> Hash {
    hash_with_domain(FORMALIZATION_REJECTION_REASON_HASH_TAG, raw_utf8_bytes)
}

pub fn advanced_ai_formalization_candidate_statement_hash(
    statement: &AdvancedMachineSurfaceTerm,
) -> Hash {
    hash_with_domain(
        FORMALIZATION_CANDIDATE_STATEMENT_HASH_TAG,
        &advanced_ai_machine_surface_term_canonical_bytes(statement),
    )
}

pub fn advanced_ai_formalization_accepted_statement_hash(
    env_fingerprint: Hash,
    accepted_universe_params: &[String],
    accepted_theorem_type: &Expr,
) -> Hash {
    let mut payload = Vec::new();
    encode_hash_to(&mut payload, &env_fingerprint);
    payload.extend_from_slice(&advanced_ai_universe_params_canonical_bytes(
        accepted_universe_params,
    ));
    payload.extend_from_slice(&npa_cert::core_expr_canonical_bytes(accepted_theorem_type));
    hash_with_domain(FORMALIZATION_ACCEPTED_STATEMENT_HASH_TAG, &payload)
}

pub fn advanced_ai_formalization_proof_root_hash(
    env_fingerprint: Hash,
    candidate_statement_hash: Hash,
    accepted_statement_hash: Hash,
) -> Hash {
    let mut payload = Vec::new();
    encode_hash_to(&mut payload, &env_fingerprint);
    encode_hash_to(&mut payload, &candidate_statement_hash);
    encode_hash_to(&mut payload, &accepted_statement_hash);
    hash_with_domain(FORMALIZATION_PROOF_ROOT_HASH_TAG, &payload)
}

pub fn advanced_ai_inductive_proposal_canonical_bytes(
    proposal: &AdvancedMachineInductiveProposal,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_inductive_proposal_to(&mut out, proposal)?;
    Ok(out)
}

pub fn advanced_ai_smt_candidate_canonical_bytes(
    candidate: &AdvancedMachineSmtCertificateCandidate,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_smt_candidate_to(&mut out, candidate)?;
    Ok(out)
}

pub fn advanced_ai_smt_problem_canonical_bytes(
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_smt_encoded_problem_to(&mut out, problem)?;
    Ok(out)
}

pub fn advanced_ai_smt_problem_hash(
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    Ok(hash_with_domain(
        SMT_PROBLEM_HASH_TAG,
        &advanced_ai_smt_problem_canonical_bytes(problem)?,
    ))
}

pub fn advanced_ai_smt_encoding_hash(
    problem: &AdvancedMachineSmtEncodedProblem,
    problem_hash: Hash,
) -> Hash {
    let mut out = Vec::new();
    out.push(problem.encoder_version.tag());
    out.push(problem.logic.tag());
    out.push(problem.command_profile.tag());
    encode_hash_to(&mut out, &problem.goal_fingerprint);
    encode_hash_to(&mut out, &problem_hash);
    hash_with_domain(SMT_ENCODING_HASH_TAG, &out)
}

pub fn advanced_ai_smt_proof_payload_canonical_bytes(
    payload: &AdvancedSmtProofNodeTable,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_smt_proof_node_table_to(&mut out, payload)?;
    Ok(out)
}

pub fn advanced_ai_smt_proof_payload_hash(
    payload: &AdvancedSmtProofNodeTable,
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    Ok(hash_with_domain(
        SMT_PROOF_PAYLOAD_HASH_TAG,
        &advanced_ai_smt_proof_payload_canonical_bytes(payload)?,
    ))
}

pub fn advanced_ai_smt_opaque_proof_payload_hash(
    format: AdvancedSmtCertificateFormat,
    payload_bytes: &[u8],
) -> std::result::Result<Hash, AdvancedSmtEncodingError> {
    if !matches!(
        format,
        AdvancedSmtCertificateFormat::AletheOpaqueV1
            | AdvancedSmtCertificateFormat::LfscOpaqueV1
            | AdvancedSmtCertificateFormat::SolverResultOnlyV1
    ) || payload_bytes.is_empty()
        || (format == AdvancedSmtCertificateFormat::SolverResultOnlyV1
            && payload_bytes != b"unsat\n")
    {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }
    let mut out = Vec::new();
    out.push(format.tag());
    encode_bytes_to(&mut out, payload_bytes);
    Ok(hash_with_domain(SMT_OPAQUE_PROOF_PAYLOAD_HASH_TAG, &out))
}

pub fn advanced_ai_smt_reconstruction_plan_canonical_bytes(
    plan: &AdvancedMachineSmtReconstructionPlan,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_smt_reconstruction_plan_to(&mut out, plan)?;
    Ok(out)
}

pub fn advanced_ai_smt_reconstruction_plan_hash(
    plan: &AdvancedMachineSmtReconstructionPlan,
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    Ok(hash_with_domain(
        SMT_RECONSTRUCTION_PLAN_HASH_TAG,
        &advanced_ai_smt_reconstruction_plan_canonical_bytes(plan)?,
    ))
}

pub fn advanced_ai_smt_certificate_metadata(
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<AdvancedSmtCertificateMetadata, AdvancedSmtEncodingError> {
    if problem.logic != candidate.logic {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }
    let proof_hash = match &candidate.proof_payload {
        AdvancedMachineSmtProofPayloadRef::Inline { payload_hash, .. }
        | AdvancedMachineSmtProofPayloadRef::Artifact { payload_hash, .. } => *payload_hash,
    };
    let reconstruction_plan_hash =
        advanced_ai_smt_reconstruction_plan_hash(&candidate.reconstruction_plan)
            .map_err(|_| AdvancedSmtEncodingError::NonCanonicalPayload)?;
    Ok(AdvancedSmtCertificateMetadata {
        format: candidate.certificate_format,
        solver: candidate.solver,
        logic: candidate.logic,
        encoded_goal_hash: problem.goal_fingerprint,
        smt_problem_hash: advanced_ai_smt_lib_problem_hash(problem)?,
        proof_hash,
        reconstruction: AdvancedSmtReconstructionMetadata {
            rule_registry_profile: candidate.rule_registry_profile,
            reconstruction_plan_hash,
            imported_theory_count: candidate.reconstruction_plan.imported_theory_refs.len() as u64,
            step_count: candidate.reconstruction_plan.steps.len() as u64,
        },
    })
}

pub fn advanced_ai_smt_certificate_metadata_canonical_bytes(
    metadata: &AdvancedSmtCertificateMetadata,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(metadata.format.tag());
    out.push(metadata.solver.tag());
    out.push(metadata.logic.tag());
    encode_hash_to(&mut out, &metadata.encoded_goal_hash);
    encode_hash_to(&mut out, &metadata.smt_problem_hash);
    encode_hash_to(&mut out, &metadata.proof_hash);
    out.push(metadata.reconstruction.rule_registry_profile.tag());
    encode_hash_to(&mut out, &metadata.reconstruction.reconstruction_plan_hash);
    encode_u64_to(&mut out, metadata.reconstruction.imported_theory_count);
    encode_u64_to(&mut out, metadata.reconstruction.step_count);
    out
}

pub fn advanced_ai_smt_certificate_metadata_hash(
    metadata: &AdvancedSmtCertificateMetadata,
) -> Hash {
    hash_with_domain(
        SMT_CERTIFICATE_METADATA_HASH_TAG,
        &advanced_ai_smt_certificate_metadata_canonical_bytes(metadata),
    )
}

pub fn advanced_ai_validate_smt_certificate_metadata(
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: &AdvancedMachineSmtEncodedProblem,
    metadata: &AdvancedSmtCertificateMetadata,
) -> std::result::Result<(), AdvancedSmtCertificateError> {
    let expected =
        advanced_ai_smt_certificate_metadata(candidate, problem).map_err(|error| match error {
            AdvancedSmtEncodingError::UnsupportedFragment => {
                AdvancedSmtCertificateError::UnsupportedFragment
            }
            AdvancedSmtEncodingError::NonCanonicalPayload => {
                AdvancedSmtCertificateError::NonCanonicalPayload
            }
        })?;
    if metadata.format != expected.format
        || metadata.solver != expected.solver
        || metadata.logic != expected.logic
        || metadata.reconstruction.rule_registry_profile
            != expected.reconstruction.rule_registry_profile
    {
        return Err(AdvancedSmtCertificateError::RuleRegistryMismatch);
    }
    if metadata.encoded_goal_hash != expected.encoded_goal_hash
        || metadata.smt_problem_hash != expected.smt_problem_hash
    {
        return Err(AdvancedSmtCertificateError::EncodingMismatch);
    }
    if metadata.proof_hash != expected.proof_hash {
        return Err(AdvancedSmtCertificateError::PayloadBindingMismatch);
    }
    if metadata.reconstruction.reconstruction_plan_hash
        != expected.reconstruction.reconstruction_plan_hash
        || metadata.reconstruction.imported_theory_count
            != expected.reconstruction.imported_theory_count
        || metadata.reconstruction.step_count != expected.reconstruction.step_count
    {
        return Err(AdvancedSmtCertificateError::ReconstructionPlanHashMismatch);
    }
    Ok(())
}

pub fn advanced_ai_smt_nat_to_int_side_condition(
    source_core_expr: Expr,
    int_symbol: AdvancedSmtSymbol,
) -> AdvancedSmtNatToIntSideCondition {
    let int_var = AdvancedSmtExpr::Var {
        symbol: int_symbol.clone(),
        sort: AdvancedSmtSortExpr::Int,
    };
    AdvancedSmtNatToIntSideCondition {
        source_core_expr,
        int_symbol,
        nonnegative_assertion: AdvancedSmtExpr::BuiltinApp {
            op: AdvancedSmtBuiltinOp::IntGe,
            args: vec![int_var, AdvancedSmtExpr::IntLit(0)],
            result_sort: AdvancedSmtSortExpr::Bool,
        },
    }
}

pub fn advanced_ai_smt_nat_to_int_side_condition_canonical_bytes(
    side_condition: &AdvancedSmtNatToIntSideCondition,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_expr_to(&mut out, &side_condition.source_core_expr);
    encode_smt_symbol_to(&mut out, &side_condition.int_symbol);
    encode_smt_expr_to(&mut out, &side_condition.nonnegative_assertion);
    out
}

pub fn advanced_ai_smt_nat_to_int_side_condition_hash(
    side_condition: &AdvancedSmtNatToIntSideCondition,
) -> Hash {
    hash_with_domain(
        SMT_NAT_TO_INT_SIDE_CONDITION_HASH_TAG,
        &advanced_ai_smt_nat_to_int_side_condition_canonical_bytes(side_condition),
    )
}

pub fn advanced_ai_smt_mvp_payload_node_rule_descriptor(
    logic: AdvancedSmtLogic,
) -> AdvancedSmtRuleDescriptor {
    let fragment = match logic {
        AdvancedSmtLogic::MvpQfUf => AdvancedSmtSupportedFragment::QfPropositional,
        AdvancedSmtLogic::MvpQfLia => AdvancedSmtSupportedFragment::QfSimpleLia,
        AdvancedSmtLogic::MvpQfBv | AdvancedSmtLogic::MvpQfUfLiaBv => {
            AdvancedSmtSupportedFragment::QfBitVecBitblastLrat
        }
    };
    advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(fragment)
}

pub fn advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(
    fragment: AdvancedSmtSupportedFragment,
) -> AdvancedSmtRuleDescriptor {
    if fragment == AdvancedSmtSupportedFragment::QfBitVecBitblastLrat {
        return advanced_ai_smt_bitblast_lrat_rule_descriptor();
    }
    let (logic, sort_profile, operator_profile, soundness_requirements) = match fragment {
        AdvancedSmtSupportedFragment::QfPropositional => (
            AdvancedSmtLogic::MvpQfUf,
            AdvancedSmtSupportedSortProfile::BoolOnly,
            AdvancedSmtSupportedOperatorProfile::PropositionalCore,
            vec![AdvancedSmtSoundnessRequirement::KernelCheckedPayloadNode],
        ),
        AdvancedSmtSupportedFragment::QfEuf => (
            AdvancedSmtLogic::MvpQfUf,
            AdvancedSmtSupportedSortProfile::BoolAndUninterpreted,
            AdvancedSmtSupportedOperatorProfile::EufCore,
            vec![
                AdvancedSmtSoundnessRequirement::KernelCheckedPayloadNode,
                AdvancedSmtSoundnessRequirement::EufCongruenceReconstruction,
            ],
        ),
        AdvancedSmtSupportedFragment::QfSimpleLia => (
            AdvancedSmtLogic::MvpQfLia,
            AdvancedSmtSupportedSortProfile::BoolAndInt,
            AdvancedSmtSupportedOperatorProfile::SimpleLia,
            vec![
                AdvancedSmtSoundnessRequirement::KernelCheckedPayloadNode,
                AdvancedSmtSoundnessRequirement::SimpleLiaReconstruction,
            ],
        ),
        AdvancedSmtSupportedFragment::QfEufLia => (
            AdvancedSmtLogic::MvpQfLia,
            AdvancedSmtSupportedSortProfile::BoolIntAndUninterpreted,
            AdvancedSmtSupportedOperatorProfile::EufLia,
            vec![
                AdvancedSmtSoundnessRequirement::KernelCheckedPayloadNode,
                AdvancedSmtSoundnessRequirement::EufCongruenceReconstruction,
                AdvancedSmtSoundnessRequirement::SimpleLiaReconstruction,
                AdvancedSmtSoundnessRequirement::EufLiaCombination,
            ],
        ),
        AdvancedSmtSupportedFragment::QfBitVecBitblastLrat => unreachable!(),
    };
    AdvancedSmtRuleDescriptor {
        rule_registry_profile: AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1,
        certificate_format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
        logic,
        command_profile: AdvancedSmtCommandProfile::MvpNormalizedQf,
        supported_fragment: fragment,
        supported_sort_profile: sort_profile,
        supported_operator_profile: operator_profile,
        kind: AdvancedSmtRuleDescriptorKind::MvpKernelCheckedPayloadNodeV1,
        checker_profile: AdvancedSmtCheckerProfile::KernelCheckedPayloadNodeV1,
        soundness_requirements,
    }
}

pub fn advanced_ai_smt_bitblast_lrat_rule_descriptor() -> AdvancedSmtRuleDescriptor {
    AdvancedSmtRuleDescriptor {
        rule_registry_profile: AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1,
        certificate_format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
        logic: AdvancedSmtLogic::MvpQfBv,
        command_profile: AdvancedSmtCommandProfile::MvpNormalizedQf,
        supported_fragment: AdvancedSmtSupportedFragment::QfBitVecBitblastLrat,
        supported_sort_profile: AdvancedSmtSupportedSortProfile::BoolAndBitVec,
        supported_operator_profile: AdvancedSmtSupportedOperatorProfile::BitVecViaBitblastLrat,
        kind: AdvancedSmtRuleDescriptorKind::BitblastLratSoundnessBridgeV1,
        checker_profile: AdvancedSmtCheckerProfile::BitblastLratBridgeV1,
        soundness_requirements: vec![AdvancedSmtSoundnessRequirement::BitblastLratSoundnessBridge],
    }
}

pub fn advanced_ai_smt_rule_registry(
    profile: AdvancedSmtRuleRegistryProfile,
) -> AdvancedSmtRuleRegistry {
    let descriptors = match profile {
        AdvancedSmtRuleRegistryProfile::MvpEmptyRegistryV1 => Vec::new(),
        AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1 => vec![
            advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(
                AdvancedSmtSupportedFragment::QfPropositional,
            ),
            advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(
                AdvancedSmtSupportedFragment::QfEuf,
            ),
            advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(
                AdvancedSmtSupportedFragment::QfSimpleLia,
            ),
            advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(
                AdvancedSmtSupportedFragment::QfEufLia,
            ),
            advanced_ai_smt_bitblast_lrat_rule_descriptor(),
        ],
    };
    AdvancedSmtRuleRegistry {
        profile,
        descriptors,
    }
}

pub fn advanced_ai_smt_rule_descriptor_canonical_bytes(
    descriptor: &AdvancedSmtRuleDescriptor,
) -> Vec<u8> {
    let mut out = vec![
        descriptor.rule_registry_profile.tag(),
        descriptor.certificate_format.tag(),
        descriptor.logic.tag(),
        descriptor.command_profile.tag(),
        descriptor.supported_fragment.tag(),
        descriptor.supported_sort_profile.tag(),
        descriptor.supported_operator_profile.tag(),
        descriptor.kind.tag(),
        descriptor.checker_profile.tag(),
    ];
    encode_len_to(&mut out, descriptor.soundness_requirements.len());
    for requirement in &descriptor.soundness_requirements {
        out.push(requirement.tag());
    }
    out
}

pub fn advanced_ai_smt_rule_descriptor_hash(descriptor: &AdvancedSmtRuleDescriptor) -> Hash {
    hash_with_domain(
        SMT_RULE_DESCRIPTOR_HASH_TAG,
        &advanced_ai_smt_rule_descriptor_canonical_bytes(descriptor),
    )
}

pub fn advanced_ai_smt_rule_descriptor_fingerprint(descriptor: &AdvancedSmtRuleDescriptor) -> Hash {
    hash_with_domain(
        SMT_RULE_DESCRIPTOR_FINGERPRINT_TAG,
        &advanced_ai_smt_rule_descriptor_canonical_bytes(descriptor),
    )
}

pub fn advanced_ai_smt_rule_registry_canonical_bytes(
    registry: &AdvancedSmtRuleRegistry,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(registry.profile.tag());
    encode_len_to(&mut out, registry.descriptors.len());
    for descriptor in &registry.descriptors {
        encode_hash_to(&mut out, &advanced_ai_smt_rule_descriptor_hash(descriptor));
    }
    out
}

pub fn advanced_ai_smt_rule_registry_hash(registry: &AdvancedSmtRuleRegistry) -> Hash {
    hash_with_domain(
        SMT_RULE_REGISTRY_HASH_TAG,
        &advanced_ai_smt_rule_registry_canonical_bytes(registry),
    )
}

pub fn advanced_ai_smt_solver_process_policy_canonical_bytes(
    policy: &AdvancedSmtSolverProcessPolicy,
) -> std::result::Result<Vec<u8>, AdvancedSmtSolverHandoffError> {
    validate_smt_solver_process_policy(policy)?;
    let mut out = Vec::new();
    out.push(policy.network.tag());
    out.push(policy.filesystem.tag());
    encode_u64_to(&mut out, policy.max_output_bytes);
    encode_u64_to(&mut out, policy.max_cpu_millis);
    encode_u64_to(&mut out, policy.max_memory_bytes);
    encode_u64_to(&mut out, policy.timeout_millis);
    encode_u64_to(&mut out, policy.max_child_processes);
    encode_raw_bytes_list_to(&mut out, &policy.child_process_allowlist);
    Ok(out)
}

pub fn advanced_ai_smt_solver_process_policy_hash(
    policy: &AdvancedSmtSolverProcessPolicy,
) -> std::result::Result<Hash, AdvancedSmtSolverHandoffError> {
    Ok(hash_with_domain(
        SMT_SOLVER_PROCESS_POLICY_HASH_TAG,
        &advanced_ai_smt_solver_process_policy_canonical_bytes(policy)?,
    ))
}

pub fn advanced_ai_smt_solver_process_profile_canonical_bytes(
    profile: &AdvancedSmtSolverProcessProfile,
) -> std::result::Result<Vec<u8>, AdvancedSmtSolverHandoffError> {
    validate_smt_solver_process_profile(profile)?;
    let mut out = Vec::new();
    out.push(profile.identity.solver.tag());
    encode_bytes_to(&mut out, &profile.identity.version_ascii);
    encode_hash_to(&mut out, &profile.identity.binary_hash);
    encode_option_hash_to(&mut out, profile.identity.container_digest_hash.as_ref());
    encode_raw_bytes_list_to(&mut out, &profile.arguments);
    encode_hash_to(
        &mut out,
        &advanced_ai_smt_solver_process_policy_hash(&profile.policy)?,
    );
    Ok(out)
}

pub fn advanced_ai_smt_solver_process_profile_hash(
    profile: &AdvancedSmtSolverProcessProfile,
) -> std::result::Result<Hash, AdvancedSmtSolverHandoffError> {
    Ok(hash_with_domain(
        SMT_SOLVER_PROCESS_PROFILE_HASH_TAG,
        &advanced_ai_smt_solver_process_profile_canonical_bytes(profile)?,
    ))
}

pub fn advanced_ai_smt_solver_handoff(
    problem: &AdvancedMachineSmtEncodedProblem,
    profile: &AdvancedSmtSolverProcessProfile,
    environment_hash: Hash,
) -> std::result::Result<AdvancedSmtSolverHandoff, AdvancedSmtSolverHandoffError> {
    if environment_hash == [0; 32] {
        return Err(AdvancedSmtSolverHandoffError::MissingEnvironmentHash);
    }
    let supported_fragment = advanced_ai_smt_classify_supported_fragment(problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    let problem_canonical_bytes = advanced_ai_smt_problem_canonical_bytes(problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    let problem_hash = advanced_ai_smt_problem_hash(problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    let smtlib_bytes = advanced_ai_smt_lib_problem_bytes(problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    let smtlib_hash = advanced_ai_smt_lib_problem_hash(problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    let policy_hash = advanced_ai_smt_solver_process_policy_hash(&profile.policy)?;
    let solver_process_profile_hash = advanced_ai_smt_solver_process_profile_hash(profile)?;
    Ok(AdvancedSmtSolverHandoff {
        solver: profile.identity.solver,
        supported_fragment,
        problem_canonical_bytes,
        smtlib_bytes,
        problem_hash,
        smtlib_hash,
        encoding_hash: advanced_ai_smt_encoding_hash(problem, problem_hash),
        environment_hash,
        policy_hash,
        solver_process_profile_hash,
    })
}

pub fn advanced_ai_smt_solver_handoff_canonical_bytes(
    handoff: &AdvancedSmtSolverHandoff,
) -> std::result::Result<Vec<u8>, AdvancedSmtSolverHandoffError> {
    validate_smt_solver_handoff_shape(handoff)?;
    let mut out = Vec::new();
    out.push(handoff.solver.tag());
    out.push(handoff.supported_fragment.tag());
    encode_hash_to(&mut out, &handoff.problem_hash);
    encode_hash_to(&mut out, &handoff.smtlib_hash);
    encode_hash_to(&mut out, &handoff.encoding_hash);
    encode_hash_to(&mut out, &handoff.environment_hash);
    encode_hash_to(&mut out, &handoff.policy_hash);
    encode_hash_to(&mut out, &handoff.solver_process_profile_hash);
    encode_u64_to(&mut out, handoff.problem_canonical_bytes.len() as u64);
    encode_u64_to(&mut out, handoff.smtlib_bytes.len() as u64);
    Ok(out)
}

pub fn advanced_ai_smt_solver_handoff_hash(
    handoff: &AdvancedSmtSolverHandoff,
) -> std::result::Result<Hash, AdvancedSmtSolverHandoffError> {
    Ok(hash_with_domain(
        SMT_SOLVER_HANDOFF_HASH_TAG,
        &advanced_ai_smt_solver_handoff_canonical_bytes(handoff)?,
    ))
}

pub fn advanced_ai_validate_smt_solver_process_result(
    handoff: &AdvancedSmtSolverHandoff,
    profile: &AdvancedSmtSolverProcessProfile,
    result: &AdvancedSmtSolverProcessResult,
) -> std::result::Result<AdvancedSmtSolverHandoffPayloadKind, AdvancedSmtSolverHandoffError> {
    validate_smt_solver_handoff_shape(handoff)?;
    let expected_policy_hash = advanced_ai_smt_solver_process_policy_hash(&profile.policy)?;
    if handoff.policy_hash != expected_policy_hash {
        return Err(AdvancedSmtSolverHandoffError::PolicyHashMismatch {
            expected: expected_policy_hash,
            actual: handoff.policy_hash,
        });
    }
    let expected_profile_hash = advanced_ai_smt_solver_process_profile_hash(profile)?;
    if handoff.solver_process_profile_hash != expected_profile_hash {
        return Err(
            AdvancedSmtSolverHandoffError::SolverVersionMetadataMismatch {
                expected: handoff.solver_process_profile_hash,
                actual: expected_profile_hash,
            },
        );
    }
    if result.solver_process_profile_hash != expected_profile_hash {
        return Err(
            AdvancedSmtSolverHandoffError::SolverVersionMetadataMismatch {
                expected: expected_profile_hash,
                actual: result.solver_process_profile_hash,
            },
        );
    }
    if result.smtlib_hash != handoff.smtlib_hash {
        return Err(AdvancedSmtSolverHandoffError::SmtLibHashMismatch {
            expected: handoff.smtlib_hash,
            actual: result.smtlib_hash,
        });
    }
    enforce_smt_solver_resource_policy(&profile.policy, result.resource_usage)?;
    match &result.output {
        AdvancedSmtSolverOutputRef::CertificatePayload {
            certificate_format,
            payload_hash,
            size_bytes,
        } => {
            if *payload_hash == [0; 32] || *size_bytes == 0 {
                return Err(AdvancedSmtSolverHandoffError::MissingPayloadHash);
            }
            match certificate_format {
                AdvancedSmtCertificateFormat::MvpProofNodeTableV1 => {
                    Ok(AdvancedSmtSolverHandoffPayloadKind::CertificatePayload)
                }
                AdvancedSmtCertificateFormat::AletheOpaqueV1
                | AdvancedSmtCertificateFormat::LfscOpaqueV1 => {
                    Err(AdvancedSmtSolverHandoffError::OpaquePayloadWithoutRegisteredChecker)
                }
                AdvancedSmtCertificateFormat::SolverResultOnlyV1 => {
                    Err(AdvancedSmtSolverHandoffError::BareResultOnly)
                }
            }
        }
        AdvancedSmtSolverOutputRef::ProofNodeTable {
            payload_hash,
            node_count,
            size_bytes,
        } => {
            if *payload_hash == [0; 32] || *node_count == 0 || *size_bytes == 0 {
                return Err(AdvancedSmtSolverHandoffError::MissingPayloadHash);
            }
            Ok(AdvancedSmtSolverHandoffPayloadKind::ProofNodeTable)
        }
        AdvancedSmtSolverOutputRef::CounterexampleModel {
            model_hash,
            size_bytes,
        } => {
            if *model_hash == [0; 32] || *size_bytes == 0 {
                return Err(AdvancedSmtSolverHandoffError::MissingPayloadHash);
            }
            Ok(AdvancedSmtSolverHandoffPayloadKind::CounterexampleModel)
        }
        AdvancedSmtSolverOutputRef::BareResult { .. } => {
            Err(AdvancedSmtSolverHandoffError::BareResultOnly)
        }
        AdvancedSmtSolverOutputRef::ExitStatus { .. } => {
            Err(AdvancedSmtSolverHandoffError::ExitStatusOnly)
        }
        AdvancedSmtSolverOutputRef::Logs { .. } => Err(AdvancedSmtSolverHandoffError::LogsOnly),
        AdvancedSmtSolverOutputRef::UncheckedProofText { .. } => {
            Err(AdvancedSmtSolverHandoffError::UncheckedProofText)
        }
    }
}

fn validate_smt_solver_process_policy(
    policy: &AdvancedSmtSolverProcessPolicy,
) -> std::result::Result<(), AdvancedSmtSolverHandoffError> {
    if policy.max_output_bytes == 0
        || policy.max_cpu_millis == 0
        || policy.max_memory_bytes == 0
        || policy.timeout_millis == 0
    {
        return Err(AdvancedSmtSolverHandoffError::NonCanonicalSolverProcessProfile);
    }
    if policy.child_process_allowlist.len() as u64 > policy.max_child_processes {
        return Err(AdvancedSmtSolverHandoffError::ResourceLimitExceeded {
            field: AdvancedSmtSolverResourceField::ChildProcesses,
            limit: policy.max_child_processes,
            actual: policy.child_process_allowlist.len() as u64,
        });
    }
    let mut previous: Option<&[u8]> = None;
    for child in &policy.child_process_allowlist {
        if !advanced_ai_smt_solver_token_is_valid(child)
            || previous.is_some_and(|previous| previous >= child.as_slice())
        {
            return Err(AdvancedSmtSolverHandoffError::NonCanonicalSolverProcessProfile);
        }
        previous = Some(child);
    }
    Ok(())
}

fn validate_smt_solver_process_profile(
    profile: &AdvancedSmtSolverProcessProfile,
) -> std::result::Result<(), AdvancedSmtSolverHandoffError> {
    validate_smt_solver_process_policy(&profile.policy)?;
    if !advanced_ai_smt_solver_token_is_valid(&profile.identity.version_ascii)
        || profile.identity.binary_hash == [0; 32]
        || profile
            .identity
            .container_digest_hash
            .is_some_and(|hash| hash == [0; 32])
    {
        return Err(AdvancedSmtSolverHandoffError::NonCanonicalSolverProcessProfile);
    }
    for argument in &profile.arguments {
        if !advanced_ai_smt_solver_token_is_valid(argument) {
            return Err(AdvancedSmtSolverHandoffError::NonCanonicalSolverProcessProfile);
        }
    }
    Ok(())
}

fn advanced_ai_smt_solver_token_is_valid(token: &[u8]) -> bool {
    !token.is_empty() && token.len() <= 1024 && token.iter().all(|byte| byte.is_ascii_graphic())
}

fn validate_smt_solver_handoff_shape(
    handoff: &AdvancedSmtSolverHandoff,
) -> std::result::Result<(), AdvancedSmtSolverHandoffError> {
    if handoff.environment_hash == [0; 32] {
        return Err(AdvancedSmtSolverHandoffError::MissingEnvironmentHash);
    }
    if handoff.policy_hash == [0; 32] || handoff.solver_process_profile_hash == [0; 32] {
        return Err(AdvancedSmtSolverHandoffError::MissingPolicyHash);
    }
    let problem = decode_smt_encoded_problem(&handoff.problem_canonical_bytes)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    let supported_fragment = advanced_ai_smt_classify_supported_fragment(&problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    if supported_fragment != handoff.supported_fragment {
        return Err(AdvancedSmtSolverHandoffError::UnsupportedFragment);
    }
    let problem_hash = advanced_ai_smt_problem_hash(&problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    if handoff.problem_hash != problem_hash {
        return Err(AdvancedSmtSolverHandoffError::ProblemHashMismatch {
            expected: problem_hash,
            actual: handoff.problem_hash,
        });
    }
    let smtlib_hash = advanced_ai_smt_lib_problem_hash(&problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    if handoff.smtlib_hash != smtlib_hash {
        return Err(AdvancedSmtSolverHandoffError::SmtLibHashMismatch {
            expected: smtlib_hash,
            actual: handoff.smtlib_hash,
        });
    }
    let expected_smtlib = advanced_ai_smt_lib_problem_bytes(&problem)
        .map_err(|_| AdvancedSmtSolverHandoffError::UnsupportedFragment)?;
    if handoff.smtlib_bytes != expected_smtlib {
        return Err(AdvancedSmtSolverHandoffError::SmtLibHashMismatch {
            expected: smtlib_hash,
            actual: hash_with_domain(SMT_LIB_PROBLEM_HASH_TAG, &handoff.smtlib_bytes),
        });
    }
    let expected_encoding_hash = advanced_ai_smt_encoding_hash(&problem, problem_hash);
    if handoff.encoding_hash != expected_encoding_hash {
        return Err(AdvancedSmtSolverHandoffError::EncodingHashMismatch {
            expected: expected_encoding_hash,
            actual: handoff.encoding_hash,
        });
    }
    Ok(())
}

fn enforce_smt_solver_resource_policy(
    policy: &AdvancedSmtSolverProcessPolicy,
    usage: AdvancedSmtSolverResourceUsage,
) -> std::result::Result<(), AdvancedSmtSolverHandoffError> {
    validate_smt_solver_process_policy(policy)?;
    enforce_smt_solver_resource_limit(
        AdvancedSmtSolverResourceField::OutputBytes,
        usage.output_bytes,
        policy.max_output_bytes,
    )?;
    enforce_smt_solver_resource_limit(
        AdvancedSmtSolverResourceField::CpuMillis,
        usage.cpu_millis,
        policy.max_cpu_millis,
    )?;
    enforce_smt_solver_resource_limit(
        AdvancedSmtSolverResourceField::MemoryBytes,
        usage.memory_bytes,
        policy.max_memory_bytes,
    )?;
    enforce_smt_solver_resource_limit(
        AdvancedSmtSolverResourceField::WallClockMillis,
        usage.wall_clock_millis,
        policy.timeout_millis,
    )?;
    enforce_smt_solver_resource_limit(
        AdvancedSmtSolverResourceField::ChildProcesses,
        usage.child_processes,
        policy.max_child_processes,
    )
}

fn enforce_smt_solver_resource_limit(
    field: AdvancedSmtSolverResourceField,
    actual: u64,
    limit: u64,
) -> std::result::Result<(), AdvancedSmtSolverHandoffError> {
    if actual > limit {
        Err(AdvancedSmtSolverHandoffError::ResourceLimitExceeded {
            field,
            limit,
            actual,
        })
    } else {
        Ok(())
    }
}

pub fn advanced_ai_smt_classify_supported_fragment(
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<AdvancedSmtSupportedFragment, AdvancedSmtEncodingError> {
    if problem.encoder_version != AdvancedSmtEncoderVersion::MvpNormalizedQfV1
        || problem.command_profile != AdvancedSmtCommandProfile::MvpNormalizedQf
        || matches!(
            problem.logic,
            AdvancedSmtLogic::MvpQfBv | AdvancedSmtLogic::MvpQfUfLiaBv
        )
    {
        return Err(AdvancedSmtEncodingError::UnsupportedFragment);
    }

    let mut features = AdvancedSmtFragmentFeatures::default();
    let mut context = AdvancedSmtCommandContext::default();
    let mut previous_key: Option<Vec<u8>> = None;
    let mut target_assertions = 0usize;
    let mut final_checks = 0usize;
    for command in &problem.commands {
        if !advanced_ai_smt_command_phase_matches_payload(command.phase, &command.payload) {
            return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
        }
        let expected_id = advanced_ai_smt_command_id(command)
            .map_err(|_| AdvancedSmtEncodingError::NonCanonicalPayload)?;
        if command.command_id != expected_id {
            return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
        }
        let key = advanced_ai_smt_command_order_key(command)
            .map_err(|_| AdvancedSmtEncodingError::NonCanonicalPayload)?;
        if previous_key
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
        }
        previous_key = Some(key);

        match &command.payload {
            AdvancedSmtCommandPayload::SortDecl { symbol, arity } => {
                if !advanced_ai_smt_decl_symbol_is_valid(symbol) {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
                if context
                    .sort_arities
                    .insert(symbol.ascii.clone(), *arity)
                    .is_some()
                {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
                features.has_euf = true;
            }
            AdvancedSmtCommandPayload::FunctionDecl {
                symbol,
                args,
                result,
            } => {
                if !advanced_ai_smt_decl_symbol_is_valid(symbol) {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
                features.has_euf = true;
                for arg in args {
                    advanced_ai_smt_scan_sort_for_fragment(
                        problem.logic,
                        arg,
                        &mut features,
                        &context,
                    )?;
                }
                advanced_ai_smt_scan_sort_for_fragment(
                    problem.logic,
                    result,
                    &mut features,
                    &context,
                )?;
                if context
                    .functions
                    .insert(symbol.ascii.clone(), (args.clone(), result.clone()))
                    .is_some()
                {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
            }
            AdvancedSmtCommandPayload::DatatypeDecl { .. } => {
                return Err(AdvancedSmtEncodingError::UnsupportedFragment);
            }
            AdvancedSmtCommandPayload::ContextAssumption { encoded_expr, .. }
            | AdvancedSmtCommandPayload::TargetAssertion { encoded_expr, .. } => {
                if matches!(
                    &command.payload,
                    AdvancedSmtCommandPayload::TargetAssertion { .. }
                ) {
                    target_assertions += 1;
                }
                advanced_ai_smt_scan_expr_for_fragment(
                    problem.logic,
                    encoded_expr,
                    &mut features,
                    &context,
                )?;
            }
            AdvancedSmtCommandPayload::FinalCheck => {
                final_checks += 1;
            }
        }
    }
    if target_assertions != 1
        || final_checks != 1
        || !matches!(
            problem.commands.last().map(|command| command.phase),
            Some(AdvancedSmtCommandPhase::FinalCheck)
        )
    {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }

    Ok(match (features.has_euf, features.has_lia) {
        (false, false) => AdvancedSmtSupportedFragment::QfPropositional,
        (true, false) => AdvancedSmtSupportedFragment::QfEuf,
        (false, true) => AdvancedSmtSupportedFragment::QfSimpleLia,
        (true, true) => AdvancedSmtSupportedFragment::QfEufLia,
    })
}

pub fn advanced_ai_smt_lib_problem_bytes(
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<Vec<u8>, AdvancedSmtEncodingError> {
    let fragment = advanced_ai_smt_classify_supported_fragment(problem)?;
    let mut out = Vec::new();
    out.extend_from_slice(b"(set-option :produce-proofs true)\n");
    out.extend_from_slice(format!("(set-logic {})\n", fragment.smtlib_logic()).as_bytes());
    for command in &problem.commands {
        advanced_ai_smt_lib_render_command(&mut out, command)?;
    }
    Ok(out)
}

pub fn advanced_ai_smt_lib_problem_hash(
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<Hash, AdvancedSmtEncodingError> {
    Ok(hash_with_domain(
        SMT_LIB_PROBLEM_HASH_TAG,
        &advanced_ai_smt_lib_problem_bytes(problem)?,
    ))
}

pub fn advanced_ai_smt_symbol_canonical_bytes(symbol: &AdvancedSmtSymbol) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(SMT_SYMBOL_HASH_TAG.as_bytes());
    encode_bytes_to(&mut out, &symbol.ascii);
    out
}

pub fn advanced_ai_smt_command_id(
    command: &AdvancedSmtEncodedCommand,
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    out.push(command.phase.tag());
    out.extend_from_slice(&advanced_ai_smt_command_id_source_key(&command.payload)?);
    Ok(hash_with_domain(SMT_COMMAND_ID_HASH_TAG, &out))
}

#[derive(Default)]
struct AdvancedSmtFragmentFeatures {
    has_euf: bool,
    has_lia: bool,
}

fn advanced_ai_smt_scan_sort_for_fragment(
    logic: AdvancedSmtLogic,
    sort: &AdvancedSmtSortExpr,
    features: &mut AdvancedSmtFragmentFeatures,
    context: &AdvancedSmtCommandContext,
) -> std::result::Result<(), AdvancedSmtEncodingError> {
    match sort {
        AdvancedSmtSortExpr::Bool => Ok(()),
        AdvancedSmtSortExpr::Int => {
            if logic == AdvancedSmtLogic::MvpQfLia {
                features.has_lia = true;
                Ok(())
            } else {
                Err(AdvancedSmtEncodingError::UnsupportedFragment)
            }
        }
        AdvancedSmtSortExpr::BitVec { .. } => Err(AdvancedSmtEncodingError::UnsupportedFragment),
        AdvancedSmtSortExpr::User { symbol, args } => {
            let Some(arity) = context.sort_arities.get(&symbol.ascii) else {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            };
            if *arity != args.len() as u32 {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            features.has_euf = true;
            for arg in args {
                advanced_ai_smt_scan_sort_for_fragment(logic, arg, features, context)?;
            }
            Ok(())
        }
    }
}

fn advanced_ai_smt_scan_expr_for_fragment(
    logic: AdvancedSmtLogic,
    expr: &AdvancedSmtExpr,
    features: &mut AdvancedSmtFragmentFeatures,
    context: &AdvancedSmtCommandContext,
) -> std::result::Result<AdvancedSmtSortExpr, AdvancedSmtEncodingError> {
    match expr {
        AdvancedSmtExpr::Var { symbol, sort } => {
            if !advanced_ai_smt_var_symbol_is_valid(symbol) {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            advanced_ai_smt_scan_sort_for_fragment(logic, sort, features, context)?;
            Ok(sort.clone())
        }
        AdvancedSmtExpr::BoolLit(_) => Ok(AdvancedSmtSortExpr::Bool),
        AdvancedSmtExpr::IntLit(_) => {
            if logic == AdvancedSmtLogic::MvpQfLia {
                features.has_lia = true;
                Ok(AdvancedSmtSortExpr::Int)
            } else {
                Err(AdvancedSmtEncodingError::UnsupportedFragment)
            }
        }
        AdvancedSmtExpr::BitVecLit { .. } => Err(AdvancedSmtEncodingError::UnsupportedFragment),
        AdvancedSmtExpr::App {
            symbol,
            args,
            result_sort,
        } => {
            let Some((expected_args, expected_result)) = context.functions.get(&symbol.ascii)
            else {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            };
            if expected_args.len() != args.len() || expected_result != result_sort {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            features.has_euf = true;
            for (arg, expected_sort) in args.iter().zip(expected_args) {
                let actual_sort =
                    advanced_ai_smt_scan_expr_for_fragment(logic, arg, features, context)?;
                if &actual_sort != expected_sort {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
            }
            advanced_ai_smt_scan_sort_for_fragment(logic, result_sort, features, context)?;
            Ok(result_sort.clone())
        }
        AdvancedSmtExpr::BuiltinApp {
            op,
            args,
            result_sort,
        } => {
            let Some((expected_arity, expected_result)) =
                advanced_ai_smt_lia_builtin_signature(*op)
            else {
                return Err(AdvancedSmtEncodingError::UnsupportedFragment);
            };
            if logic != AdvancedSmtLogic::MvpQfLia {
                return Err(AdvancedSmtEncodingError::UnsupportedFragment);
            }
            if args.len() != expected_arity || result_sort != &expected_result {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            features.has_lia = true;
            for arg in args {
                let actual_sort =
                    advanced_ai_smt_scan_expr_for_fragment(logic, arg, features, context)?;
                if actual_sort != AdvancedSmtSortExpr::Int {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
            }
            Ok(result_sort.clone())
        }
        AdvancedSmtExpr::Not(inner) => {
            let inner_sort =
                advanced_ai_smt_scan_expr_for_fragment(logic, inner, features, context)?;
            if inner_sort != AdvancedSmtSortExpr::Bool {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::And(args) | AdvancedSmtExpr::Or(args) => {
            if args.is_empty() {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            for arg in args {
                let sort = advanced_ai_smt_scan_expr_for_fragment(logic, arg, features, context)?;
                if sort != AdvancedSmtSortExpr::Bool {
                    return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
                }
            }
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::Eq(lhs, rhs) => {
            let lhs_sort = advanced_ai_smt_scan_expr_for_fragment(logic, lhs, features, context)?;
            let rhs_sort = advanced_ai_smt_scan_expr_for_fragment(logic, rhs, features, context)?;
            if lhs_sort != rhs_sort {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::Imp(lhs, rhs) => {
            let lhs_sort = advanced_ai_smt_scan_expr_for_fragment(logic, lhs, features, context)?;
            let rhs_sort = advanced_ai_smt_scan_expr_for_fragment(logic, rhs, features, context)?;
            if lhs_sort != AdvancedSmtSortExpr::Bool || rhs_sort != AdvancedSmtSortExpr::Bool {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond_sort = advanced_ai_smt_scan_expr_for_fragment(logic, cond, features, context)?;
            if cond_sort != AdvancedSmtSortExpr::Bool {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            let then_sort =
                advanced_ai_smt_scan_expr_for_fragment(logic, then_expr, features, context)?;
            let else_sort =
                advanced_ai_smt_scan_expr_for_fragment(logic, else_expr, features, context)?;
            if then_sort != else_sort {
                return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
            }
            Ok(then_sort)
        }
    }
}

fn advanced_ai_smt_lia_builtin_signature(
    op: AdvancedSmtBuiltinOp,
) -> Option<(usize, AdvancedSmtSortExpr)> {
    match op {
        AdvancedSmtBuiltinOp::IntNeg => Some((1, AdvancedSmtSortExpr::Int)),
        AdvancedSmtBuiltinOp::IntAdd | AdvancedSmtBuiltinOp::IntSub => {
            Some((2, AdvancedSmtSortExpr::Int))
        }
        AdvancedSmtBuiltinOp::IntLe
        | AdvancedSmtBuiltinOp::IntLt
        | AdvancedSmtBuiltinOp::IntGe
        | AdvancedSmtBuiltinOp::IntGt => Some((2, AdvancedSmtSortExpr::Bool)),
        _ => None,
    }
}

fn advanced_ai_smt_lib_render_command(
    out: &mut Vec<u8>,
    command: &AdvancedSmtEncodedCommand,
) -> std::result::Result<(), AdvancedSmtEncodingError> {
    match &command.payload {
        AdvancedSmtCommandPayload::SortDecl { symbol, arity } => {
            out.extend_from_slice(
                format!(
                    "(declare-sort {} {})\n",
                    advanced_ai_smt_lib_decl_symbol(symbol)?,
                    arity
                )
                .as_bytes(),
            );
        }
        AdvancedSmtCommandPayload::FunctionDecl {
            symbol,
            args,
            result,
        } => {
            let rendered_args = args
                .iter()
                .map(advanced_ai_smt_lib_render_sort)
                .collect::<std::result::Result<Vec<_>, _>>()?
                .join(" ");
            out.extend_from_slice(
                format!(
                    "(declare-fun {} ({}) {})\n",
                    advanced_ai_smt_lib_decl_symbol(symbol)?,
                    rendered_args,
                    advanced_ai_smt_lib_render_sort(result)?
                )
                .as_bytes(),
            );
        }
        AdvancedSmtCommandPayload::DatatypeDecl { .. } => {
            return Err(AdvancedSmtEncodingError::UnsupportedFragment);
        }
        AdvancedSmtCommandPayload::ContextAssumption { encoded_expr, .. }
        | AdvancedSmtCommandPayload::TargetAssertion { encoded_expr, .. } => {
            out.extend_from_slice(
                format!(
                    "(assert {})\n",
                    advanced_ai_smt_lib_render_expr(encoded_expr)?
                )
                .as_bytes(),
            );
        }
        AdvancedSmtCommandPayload::FinalCheck => {
            out.extend_from_slice(b"(check-sat)\n(get-proof)\n");
        }
    }
    Ok(())
}

fn advanced_ai_smt_lib_render_sort(
    sort: &AdvancedSmtSortExpr,
) -> std::result::Result<String, AdvancedSmtEncodingError> {
    Ok(match sort {
        AdvancedSmtSortExpr::Bool => "Bool".to_owned(),
        AdvancedSmtSortExpr::Int => "Int".to_owned(),
        AdvancedSmtSortExpr::BitVec { .. } => {
            return Err(AdvancedSmtEncodingError::UnsupportedFragment);
        }
        AdvancedSmtSortExpr::User { symbol, args } => {
            let rendered_symbol = advanced_ai_smt_lib_decl_symbol(symbol)?;
            if args.is_empty() {
                rendered_symbol
            } else {
                let rendered_args = args
                    .iter()
                    .map(advanced_ai_smt_lib_render_sort)
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .join(" ");
                format!("({rendered_symbol} {rendered_args})")
            }
        }
    })
}

fn advanced_ai_smt_lib_render_expr(
    expr: &AdvancedSmtExpr,
) -> std::result::Result<String, AdvancedSmtEncodingError> {
    Ok(match expr {
        AdvancedSmtExpr::Var { symbol, .. } => advanced_ai_smt_lib_var_symbol(symbol)?,
        AdvancedSmtExpr::BoolLit(value) => {
            if *value {
                "true".to_owned()
            } else {
                "false".to_owned()
            }
        }
        AdvancedSmtExpr::IntLit(value) => advanced_ai_smt_lib_int_literal(*value),
        AdvancedSmtExpr::BitVecLit { .. } => {
            return Err(AdvancedSmtEncodingError::UnsupportedFragment);
        }
        AdvancedSmtExpr::App { symbol, args, .. } => {
            let rendered_symbol = advanced_ai_smt_lib_decl_symbol(symbol)?;
            if args.is_empty() {
                rendered_symbol
            } else {
                let rendered_args = args
                    .iter()
                    .map(advanced_ai_smt_lib_render_expr)
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .join(" ");
                format!("({rendered_symbol} {rendered_args})")
            }
        }
        AdvancedSmtExpr::BuiltinApp { op, args, .. } => {
            let rendered_args = args
                .iter()
                .map(advanced_ai_smt_lib_render_expr)
                .collect::<std::result::Result<Vec<_>, _>>()?;
            let op = match op {
                AdvancedSmtBuiltinOp::IntNeg => "-",
                AdvancedSmtBuiltinOp::IntAdd => "+",
                AdvancedSmtBuiltinOp::IntSub => "-",
                AdvancedSmtBuiltinOp::IntLe => "<=",
                AdvancedSmtBuiltinOp::IntLt => "<",
                AdvancedSmtBuiltinOp::IntGe => ">=",
                AdvancedSmtBuiltinOp::IntGt => ">",
                _ => return Err(AdvancedSmtEncodingError::UnsupportedFragment),
            };
            format!("({} {})", op, rendered_args.join(" "))
        }
        AdvancedSmtExpr::Not(inner) => {
            format!("(not {})", advanced_ai_smt_lib_render_expr(inner)?)
        }
        AdvancedSmtExpr::And(args) => advanced_ai_smt_lib_render_nary("and", args)?,
        AdvancedSmtExpr::Or(args) => advanced_ai_smt_lib_render_nary("or", args)?,
        AdvancedSmtExpr::Eq(lhs, rhs) => format!(
            "(= {} {})",
            advanced_ai_smt_lib_render_expr(lhs)?,
            advanced_ai_smt_lib_render_expr(rhs)?
        ),
        AdvancedSmtExpr::Imp(lhs, rhs) => format!(
            "(=> {} {})",
            advanced_ai_smt_lib_render_expr(lhs)?,
            advanced_ai_smt_lib_render_expr(rhs)?
        ),
        AdvancedSmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => format!(
            "(ite {} {} {})",
            advanced_ai_smt_lib_render_expr(cond)?,
            advanced_ai_smt_lib_render_expr(then_expr)?,
            advanced_ai_smt_lib_render_expr(else_expr)?
        ),
    })
}

fn advanced_ai_smt_lib_render_nary(
    op: &str,
    args: &[AdvancedSmtExpr],
) -> std::result::Result<String, AdvancedSmtEncodingError> {
    if args.is_empty() {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }
    if args.len() == 1 {
        return advanced_ai_smt_lib_render_expr(&args[0]);
    }
    Ok(format!(
        "({} {})",
        op,
        args.iter()
            .map(advanced_ai_smt_lib_render_expr)
            .collect::<std::result::Result<Vec<_>, _>>()?
            .join(" ")
    ))
}

fn advanced_ai_smt_lib_int_literal(value: i128) -> String {
    if value >= 0 {
        value.to_string()
    } else {
        format!("(- {})", value.unsigned_abs())
    }
}

fn advanced_ai_smt_lib_decl_symbol(
    symbol: &AdvancedSmtSymbol,
) -> std::result::Result<String, AdvancedSmtEncodingError> {
    if !advanced_ai_smt_decl_symbol_is_valid(symbol) {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }
    advanced_ai_smt_lib_quoted_symbol(symbol)
}

fn advanced_ai_smt_lib_var_symbol(
    symbol: &AdvancedSmtSymbol,
) -> std::result::Result<String, AdvancedSmtEncodingError> {
    if !advanced_ai_smt_var_symbol_is_valid(symbol) {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }
    advanced_ai_smt_lib_quoted_symbol(symbol)
}

fn advanced_ai_smt_lib_quoted_symbol(
    symbol: &AdvancedSmtSymbol,
) -> std::result::Result<String, AdvancedSmtEncodingError> {
    if !symbol
        .ascii
        .iter()
        .all(|byte| byte.is_ascii_graphic() && !matches!(*byte, b'|' | b'\\'))
    {
        return Err(AdvancedSmtEncodingError::NonCanonicalPayload);
    }
    let ascii = std::str::from_utf8(&symbol.ascii)
        .map_err(|_| AdvancedSmtEncodingError::NonCanonicalPayload)?;
    Ok(format!("|{}|", ascii))
}

pub fn advanced_ai_typeclass_resolution_plan_canonical_bytes(
    plan: &AdvancedMachineTypeclassResolutionPlan,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_typeclass_resolution_plan_to(&mut out, plan)?;
    Ok(out)
}

pub fn advanced_ai_theorem_graph_query_canonical_bytes(
    query: &AdvancedMachineTheoremGraphQuery,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_theorem_graph_query_to(&mut out, query)?;
    Ok(out)
}

pub fn advanced_ai_theorem_graph_snapshot_canonical_bytes(
    snapshot: &AdvancedMachineTheoremGraphSnapshot,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_theorem_graph_snapshot_to(&mut out, snapshot)?;
    Ok(out)
}

pub fn advanced_ai_theorem_graph_query_features_canonical_bytes(
    features: &AdvancedMachineTheoremGraphQueryFeatures,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_theorem_graph_query_features_to(&mut out, features)?;
    Ok(out)
}

pub fn advanced_ai_theorem_graph_snapshot_hash(
    canonical_bytes: &[u8],
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    decode_theorem_graph_snapshot(canonical_bytes)
        .map_err(|_| AdvancedAiCanonicalError::InvalidName)?;
    Ok(hash_with_domain(
        THEOREM_GRAPH_SNAPSHOT_HASH_TAG,
        canonical_bytes,
    ))
}

pub fn advanced_ai_theorem_graph_query_features_hash(
    canonical_bytes: &[u8],
) -> std::result::Result<Hash, AdvancedAiCanonicalError> {
    decode_theorem_graph_query_features(canonical_bytes)
        .map_err(|_| AdvancedAiCanonicalError::InvalidName)?;
    Ok(hash_with_domain(
        THEOREM_GRAPH_QUERY_FEATURES_HASH_TAG,
        canonical_bytes,
    ))
}

pub fn advanced_ai_universe_repair_candidate_canonical_bytes(
    candidate: &AdvancedUniverseRepairCandidate,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_universe_repair_candidate_to(&mut out, candidate)?;
    Ok(out)
}

pub fn advanced_ai_options_canonical_bytes(
    options: &AdvancedAiOptions,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_options_to(&mut out, options)?;
    Ok(out)
}

pub fn advanced_ai_candidate_envelope_canonical_bytes(
    envelope: &AdvancedAiCandidateEnvelope,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_candidate_envelope_to(&mut out, envelope)?;
    Ok(out)
}

pub fn validate_advanced_ai_common_envelope(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
    expected_task_kind: AdvancedAiTaskKind,
) -> std::result::Result<AdvancedValidatedCommonEnvelope, AdvancedAiEndpointResponse> {
    let envelope = match decode_candidate_envelope(request_canonical_bytes) {
        Ok(envelope) => envelope,
        Err(_) => {
            return Err(AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::NonCanonicalRequestBytes,
            });
        }
    };
    let candidate_hash = advanced_ai_candidate_hash(request_canonical_bytes);

    if envelope.task_kind != expected_task_kind {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    }

    validate_imports(candidate_hash, &envelope.imports, verified_imports)?;

    let (options, options_hash) =
        validate_options_ref(candidate_hash, &envelope.options, workspace_root)?;

    if !options
        .advanced_inductive
        .approved_nested_type_constructors
        .is_empty()
    {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        ));
    }

    let env_fingerprint = advanced_ai_env_fingerprint(
        envelope.profile_version,
        envelope.task_kind,
        &envelope.imports,
        options_hash,
    )
    .map_err(|_| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;

    if envelope.target.env_fingerprint != env_fingerprint {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        ));
    }

    validate_target_shape(candidate_hash, envelope.task_kind, &envelope.target)?;
    validate_required_options(candidate_hash, envelope.task_kind, &options)?;
    validate_task_options_shape(candidate_hash, envelope.task_kind, &options)?;

    Ok(AdvancedValidatedCommonEnvelope {
        candidate_hash,
        options_hash,
        env_fingerprint,
        envelope,
        options,
    })
}

pub fn run_advanced_ai_inductive_check_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    match validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::AdvancedInductive,
    ) {
        Ok(validated) => run_advanced_ai_inductive_validated(validated, verified_imports),
        Err(response) => response,
    }
}

pub fn run_advanced_ai_universe_repair_check_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    match validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::UniverseRepair,
    ) {
        Ok(validated) => run_advanced_ai_universe_repair_validated(validated, verified_imports),
        Err(response) => response,
    }
}

pub fn run_advanced_ai_typeclass_resolve_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    match validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::TypeclassResolution,
    ) {
        Ok(validated) => run_advanced_ai_typeclass_resolve_validated(validated, verified_imports),
        Err(response) => response,
    }
}

pub fn run_advanced_ai_smt_reconstruct_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    match validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::SmtCertificate,
    ) {
        Ok(validated) => {
            run_advanced_ai_smt_reconstruct_validated(validated, verified_imports, workspace_root)
        }
        Err(response) => response,
    }
}

pub fn advanced_ai_smt_prove_hashes_from_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> std::result::Result<AdvancedSmtProveHashes, AdvancedAiEndpointResponse> {
    let final_proof = match run_advanced_ai_smt_reconstruct_request(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
    ) {
        AdvancedAiEndpointResponse::Success { payload, .. } => match *payload {
            AdvancedAiSuccessPayload::SmtCertificate { final_proof } => final_proof,
            _ => {
                return Err(AdvancedAiEndpointResponse::Error {
                    error: AdvancedAiEndpointError::InternalValidatorFailure,
                });
            }
        },
        response => return Err(response),
    };
    let validated = validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::SmtCertificate,
    )?;
    let candidate = decode_smt_candidate(&validated.envelope.payload).map_err(|_| {
        smt_rejected_response(
            validated.candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        )
    })?;
    let problem_hash = match &candidate.encoded_problem {
        AdvancedMachineSmtProblemRef::Inline { problem_hash, .. }
        | AdvancedMachineSmtProblemRef::Artifact { problem_hash, .. } => *problem_hash,
    };
    Ok(AdvancedSmtProveHashes {
        problem_hash,
        proof_hash: advanced_ai_smt_declared_payload_hash(&candidate),
        npa_proof_hash: npa_tactic::core_expr_hash(&final_proof),
    })
}

pub fn run_advanced_ai_theorem_graph_query_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    match validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::TheoremGraphQuery,
    ) {
        Ok(validated) => run_advanced_ai_theorem_graph_query_validated(
            validated,
            verified_imports,
            workspace_root,
        ),
        Err(response) => response,
    }
}

pub fn run_advanced_ai_formalize_check_request(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    match validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::NaturalLanguageFormalization,
    ) {
        Ok(validated) => {
            run_advanced_ai_formalize_check_validated(validated, verified_imports, workspace_root)
        }
        Err(response) => response,
    }
}

pub fn advanced_ai_formalization_request_metadata(
    request_canonical_bytes: &[u8],
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> std::result::Result<AdvancedFormalizationRequestMetadata, AdvancedAiEndpointResponse> {
    let validated = validate_advanced_ai_common_envelope(
        request_canonical_bytes,
        verified_imports,
        workspace_root,
        AdvancedAiTaskKind::NaturalLanguageFormalization,
    )?;
    let mut payload = decode_formalization_payload(&validated.envelope.payload).map_err(|_| {
        rejected_response(
            validated.candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;
    if !formalization_statement_wrapper_is_valid(&payload.candidate.statement) {
        return Err(rejected_response(
            validated.candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    }
    let candidate_hash = validated.candidate_hash;
    let candidate_statement_hash =
        advanced_ai_formalization_candidate_statement_hash(&payload.candidate.statement);
    let original_payload = payload.clone();
    payload.candidate.optional_proof_candidate = None;
    let mut envelope_without_proof = validated.envelope;
    envelope_without_proof.payload = advanced_ai_formalization_payload_canonical_bytes(&payload)
        .map_err(|_| AdvancedAiEndpointResponse::Error {
            error: AdvancedAiEndpointError::InternalValidatorFailure,
        })?;
    let request_without_proof_candidate_canonical_bytes =
        advanced_ai_candidate_envelope_canonical_bytes(&envelope_without_proof).map_err(|_| {
            AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            }
        })?;
    Ok(AdvancedFormalizationRequestMetadata {
        candidate_hash,
        candidate_statement_hash,
        payload: original_payload,
        request_without_proof_candidate_canonical_bytes,
    })
}

fn run_advanced_ai_formalize_check_validated(
    validated: AdvancedValidatedCommonEnvelope,
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    let candidate_hash = validated.candidate_hash;
    let payload = match decode_formalization_payload(&validated.envelope.payload) {
        Ok(payload) => payload,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };

    if !formalization_statement_wrapper_is_valid(&payload.candidate.statement) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }
    let candidate_statement_hash =
        advanced_ai_formalization_candidate_statement_hash(&payload.candidate.statement);

    let (source_document_hash, source_bytes) = match validate_formalization_source_document_ref(
        candidate_hash,
        &payload.candidate.source_document,
        workspace_root,
    ) {
        Ok(validated) => validated,
        Err(response) => return response,
    };
    let claim_span_hash = match validate_formalization_claim_span(
        candidate_hash,
        &payload.candidate.claim_span,
        source_document_hash,
        &source_bytes,
    ) {
        Ok(hash) => hash,
        Err(response) => return response,
    };
    let rejected_reason_hash = match rejected_reason_ref(&payload.intent_record) {
        Some(reason) => match validate_formalization_rejection_reason_ref(
            candidate_hash,
            reason,
            workspace_root,
        ) {
            Ok(hash) => Some(hash),
            Err(response) => return response,
        },
        None => None,
    };

    if payload
        .intent_record
        .as_ref()
        .and_then(|intent| reviewer_for_intent_status(&intent.status))
        .is_some_and(|reviewer| !reviewer_id_is_valid(reviewer))
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    if matches!(
        payload.intent_record.as_ref().map(|intent| &intent.status),
        Some(AdvancedFormalizationIntentStatus::Rejected { .. })
    ) && payload.candidate.optional_proof_candidate.is_some()
    {
        return formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::RejectedIntentHasProofCandidate,
        );
    }

    if let Some(intent) = payload.intent_record.as_ref() {
        if intent.source_document_hash != source_document_hash
            || intent.claim_span_hash != claim_span_hash
            || intent.candidate_statement_hash != candidate_statement_hash
            || rejected_reason_hash
                .is_some_and(|hash| rejected_status_reason_hash(&intent.status) != Some(hash))
        {
            return formalization_rejected_response(
                candidate_hash,
                AdvancedFormalizationError::IntentRecordMismatch,
            );
        }
    }

    if matches!(
        payload.intent_record.as_ref().map(|intent| &intent.status),
        Some(AdvancedFormalizationIntentStatus::Rejected { .. })
    ) {
        return success_response(
            candidate_hash,
            AdvancedAiSuccessPayload::NaturalLanguageFormalization {
                kind: AdvancedFormalizationSuccessKind::IntentRecordOnly,
                accepted_statement_hash: None,
                formalization_proof_root_hash: None,
            },
        );
    }

    let (accepted_theorem_type, computed_accepted_statement_hash) =
        match elaborate_formalization_statement(
            candidate_hash,
            validated.env_fingerprint,
            &payload.candidate.statement,
            verified_imports,
        ) {
            Ok(accepted) => accepted,
            Err(response) => return response,
        };

    let reviewed_accepted_statement_hash =
        payload
            .intent_record
            .as_ref()
            .and_then(|intent| match &intent.status {
                AdvancedFormalizationIntentStatus::Reviewed {
                    accepted_statement_hash,
                    ..
                } => Some(*accepted_statement_hash),
                _ => None,
            });
    let accepted_statement_matches = reviewed_accepted_statement_hash
        .is_none_or(|hash| hash == computed_accepted_statement_hash);

    if let Some(proof_candidate) = payload.candidate.optional_proof_candidate.as_ref() {
        if !accepted_statement_matches
            || proof_candidate.candidate_statement_hash != candidate_statement_hash
        {
            return formalization_rejected_response(
                candidate_hash,
                AdvancedFormalizationError::FormalizationProofStatementMismatch,
            );
        }
        let proof_root_hash = advanced_ai_formalization_proof_root_hash(
            validated.env_fingerprint,
            candidate_statement_hash,
            computed_accepted_statement_hash,
        );
        match run_advanced_ai_formalization_proof_bridge(
            candidate_hash,
            proof_root_hash,
            &payload.candidate.statement,
            &accepted_theorem_type,
            proof_candidate,
            &validated.options,
            verified_imports,
        ) {
            Ok(()) => {
                return success_response(
                    candidate_hash,
                    AdvancedAiSuccessPayload::NaturalLanguageFormalization {
                        kind: AdvancedFormalizationSuccessKind::ProofBridgeChecked,
                        accepted_statement_hash: Some(computed_accepted_statement_hash),
                        formalization_proof_root_hash: Some(proof_root_hash),
                    },
                );
            }
            Err(response) => return response,
        }
    }

    if !accepted_statement_matches {
        return success_response(
            candidate_hash,
            AdvancedAiSuccessPayload::NaturalLanguageFormalization {
                kind: AdvancedFormalizationSuccessKind::IntentRecordOnly,
                accepted_statement_hash: None,
                formalization_proof_root_hash: None,
            },
        );
    }

    success_response(
        candidate_hash,
        AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind: AdvancedFormalizationSuccessKind::CandidateStatementChecked,
            accepted_statement_hash: Some(computed_accepted_statement_hash),
            formalization_proof_root_hash: None,
        },
    )
}

fn formalization_statement_wrapper_is_valid(statement: &AdvancedMachineSurfaceTerm) -> bool {
    advanced_ai_string_list_is_unique(&statement.universe_params)
        && statement
            .universe_params
            .iter()
            .all(|param| advanced_ai_machine_identifier_compatible(param))
        && statement.term_canonical_bytes.len() <= MAX_ADVANCED_AI_FORMALIZATION_TERM_BYTES
        && npa_frontend::decode_machine_term_source_canonical(&statement.term_canonical_bytes)
            .is_ok()
}

fn advanced_ai_machine_identifier_compatible(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
        && !matches!(
            value,
            "succ"
                | "max"
                | "imax"
                | "import"
                | "def"
                | "theorem"
                | "fun"
                | "forall"
                | "let"
                | "in"
                | "Prop"
                | "Type"
                | "Sort"
                | "open"
                | "namespace"
                | "match"
                | "with"
                | "notation"
                | "infix"
                | "infixl"
                | "infixr"
                | "axiom"
                | "inductive"
        )
}

fn validate_formalization_source_document_ref(
    candidate_hash: Hash,
    source: &AdvancedMachineFormalizationSourceDocumentRef,
    workspace_root: &Path,
) -> std::result::Result<(Hash, Vec<u8>), AdvancedAiEndpointResponse> {
    let (embedded_hash, bytes) = match source {
        AdvancedMachineFormalizationSourceDocumentRef::Inline {
            source_document_hash,
            raw_utf8_bytes,
        } => {
            if raw_utf8_bytes.len() > MAX_ADVANCED_AI_FORMALIZATION_SOURCE_BYTES {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    None,
                ));
            }
            (*source_document_hash, raw_utf8_bytes.clone())
        }
        AdvancedMachineFormalizationSourceDocumentRef::Artifact {
            path,
            file_hash,
            source_document_hash,
            size_bytes,
        } => {
            let bytes = read_advanced_ai_formalization_artifact(
                candidate_hash,
                workspace_root,
                path,
                *file_hash,
                *size_bytes,
                MAX_ADVANCED_AI_FORMALIZATION_SOURCE_BYTES,
            )?;
            (*source_document_hash, bytes)
        }
    };
    if std::str::from_utf8(&bytes).is_err() {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    }
    let actual_hash = advanced_ai_formalization_source_document_hash(&bytes);
    if actual_hash != embedded_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok((actual_hash, bytes))
}

fn validate_formalization_claim_span(
    candidate_hash: Hash,
    claim_span: &AdvancedMachineFormalizationClaimSpan,
    source_document_hash: Hash,
    source_bytes: &[u8],
) -> std::result::Result<Hash, AdvancedAiEndpointResponse> {
    let Ok(source) = std::str::from_utf8(source_bytes) else {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    };
    let start = usize::try_from(claim_span.start_byte).map_err(|_| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;
    let end = usize::try_from(claim_span.end_byte).map_err(|_| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;
    if start > end
        || end > source_bytes.len()
        || !source.is_char_boundary(start)
        || !source.is_char_boundary(end)
    {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    }
    let actual_hash = advanced_ai_formalization_claim_span_hash(
        source_document_hash,
        claim_span.start_byte,
        claim_span.end_byte,
        &source_bytes[start..end],
    );
    if actual_hash != claim_span.claim_span_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok(actual_hash)
}

fn validate_formalization_rejection_reason_ref(
    candidate_hash: Hash,
    reason: &AdvancedMachineFormalizationRejectionReasonRef,
    workspace_root: &Path,
) -> std::result::Result<Hash, AdvancedAiEndpointResponse> {
    let (embedded_hash, bytes) = match reason {
        AdvancedMachineFormalizationRejectionReasonRef::Inline {
            rejection_reason_hash,
            raw_utf8_bytes,
        } => {
            if raw_utf8_bytes.len() > MAX_ADVANCED_AI_FORMALIZATION_REASON_BYTES {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    None,
                ));
            }
            (*rejection_reason_hash, raw_utf8_bytes.clone())
        }
        AdvancedMachineFormalizationRejectionReasonRef::Artifact {
            path,
            file_hash,
            rejection_reason_hash,
            size_bytes,
        } => {
            let bytes = read_advanced_ai_formalization_artifact(
                candidate_hash,
                workspace_root,
                path,
                *file_hash,
                *size_bytes,
                MAX_ADVANCED_AI_FORMALIZATION_REASON_BYTES,
            )?;
            (*rejection_reason_hash, bytes)
        }
    };
    if std::str::from_utf8(&bytes).is_err() {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    }
    let actual_hash = advanced_ai_formalization_rejection_reason_hash(&bytes);
    if actual_hash != embedded_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok(actual_hash)
}

fn read_advanced_ai_formalization_artifact(
    candidate_hash: Hash,
    workspace_root: &Path,
    path: &str,
    file_hash: Hash,
    size_bytes: u64,
    cap: usize,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    if usize::try_from(size_bytes)
        .map(|size| size > cap)
        .unwrap_or(true)
    {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ));
    }
    let path = match validate_artifact_path(workspace_root, path) {
        Ok(path) => path,
        Err(ArtifactPathError::EnvelopeMalformed) => {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            ));
        }
        Err(ArtifactPathError::ArtifactUnavailable) => {
            return Err(AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::ArtifactUnavailable,
            });
        }
    };
    let metadata = std::fs::metadata(&path).map_err(|_| AdvancedAiEndpointResponse::Error {
        error: AdvancedAiEndpointError::ArtifactUnavailable,
    })?;
    if metadata.len() != size_bytes {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    let bytes = std::fs::read(path).map_err(|_| AdvancedAiEndpointResponse::Error {
        error: AdvancedAiEndpointError::ArtifactUnavailable,
    })?;
    if advanced_ai_file_hash(&bytes) != file_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok(bytes)
}

fn rejected_reason_ref(
    intent_record: &Option<AdvancedFormalizationIntentRecord>,
) -> Option<&AdvancedMachineFormalizationRejectionReasonRef> {
    match intent_record.as_ref().map(|intent| &intent.status) {
        Some(AdvancedFormalizationIntentStatus::Rejected {
            rejection_reason, ..
        }) => Some(rejection_reason),
        _ => None,
    }
}

fn reviewer_for_intent_status(
    status: &AdvancedFormalizationIntentStatus,
) -> Option<&AdvancedReviewerId> {
    match status {
        AdvancedFormalizationIntentStatus::Unreviewed => None,
        AdvancedFormalizationIntentStatus::Reviewed { reviewer, .. }
        | AdvancedFormalizationIntentStatus::Rejected { reviewer, .. } => Some(reviewer),
    }
}

fn rejected_status_reason_hash(status: &AdvancedFormalizationIntentStatus) -> Option<Hash> {
    match status {
        AdvancedFormalizationIntentStatus::Rejected {
            rejection_reason_hash,
            ..
        } => Some(*rejection_reason_hash),
        _ => None,
    }
}

fn reviewer_id_is_valid(reviewer: &AdvancedReviewerId) -> bool {
    match reviewer {
        AdvancedReviewerId::Human { stable_id_ascii } => {
            reviewer_ascii_field_is_valid(stable_id_ascii)
        }
        AdvancedReviewerId::System {
            system_id_ascii,
            actor_id_ascii,
        } => {
            reviewer_ascii_field_is_valid(system_id_ascii)
                && reviewer_ascii_field_is_valid(actor_id_ascii)
        }
    }
}

fn reviewer_ascii_field_is_valid(bytes: &[u8]) -> bool {
    !bytes.is_empty()
        && bytes.len() <= 128
        && bytes.iter().all(|byte| {
            byte.is_ascii_alphanumeric() || matches!(*byte, b'.' | b'_' | b'@' | b':' | b'-')
        })
}

fn elaborate_formalization_statement(
    candidate_hash: Hash,
    env_fingerprint: Hash,
    statement: &AdvancedMachineSurfaceTerm,
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(Expr, Hash), AdvancedAiEndpointResponse> {
    let ast = npa_frontend::decode_machine_term_source_canonical(&statement.term_canonical_bytes)
        .map_err(|_| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;
    let import_modules = verified_imports
        .iter()
        .map(|import| import.verified_module().clone())
        .collect::<Vec<_>>();
    let context = npa_frontend::MachineTermElabContext::from_verified_modules(
        &import_modules,
        &import_modules,
        Vec::new(),
        statement.universe_params.clone(),
    )
    .map_err(|_| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        )
    })?;
    let options = npa_frontend::MachineCompileOptions {
        mode: npa_frontend::MachineSurfaceMode::Complete,
        allow_universe_meta: false,
    };
    let (accepted_theorem_type, inferred_type) =
        npa_frontend::elaborate_machine_term_infer_from_ast(&ast, &context, &options).map_err(
            |_| {
                formalization_rejected_response(
                    candidate_hash,
                    AdvancedFormalizationError::CandidateStatementElaborationFailed,
                )
            },
        )?;
    match context
        .kernel_env()
        .env()
        .whnf(&Ctx::new(), &statement.universe_params, &inferred_type)
    {
        Ok(Expr::Sort(_)) => {
            let accepted_statement_hash = advanced_ai_formalization_accepted_statement_hash(
                env_fingerprint,
                &statement.universe_params,
                &accepted_theorem_type,
            );
            Ok((accepted_theorem_type, accepted_statement_hash))
        }
        Ok(_) | Err(_) => Err(formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::CandidateStatementElaborationFailed,
        )),
    }
}

fn run_advanced_ai_formalization_proof_bridge(
    candidate_hash: Hash,
    proof_root_hash: Hash,
    statement: &AdvancedMachineSurfaceTerm,
    accepted_theorem_type: &Expr,
    proof_candidate: &AdvancedMachineFormalizationProofCandidate,
    options: &AdvancedAiOptions,
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let Some(formalization_options) = options.formalization.as_ref() else {
        return Err(AdvancedAiEndpointResponse::Error {
            error: AdvancedAiEndpointError::InternalValidatorFailure,
        });
    };
    let tactic_options =
        decode_machine_tactic_options(&formalization_options.tactic_options_canonical_bytes)
            .map_err(|_| AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            })?;
    let tactic_budget =
        decode_machine_tactic_budget(&formalization_options.tactic_budget_canonical_bytes)
            .map_err(|_| AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            })?;
    let module = formalization_scratch_module(proof_root_hash);
    let theorem_name = formalization_scratch_theorem(proof_root_hash);
    let start = machine_tactic_start_machine_proof(
        MachineProofSpec {
            module: module.clone(),
            theorem_name: theorem_name.clone(),
            source_index: 0,
            universe_params: statement.universe_params.clone(),
            theorem_type: accepted_theorem_type.clone(),
        },
        verified_imports.to_vec(),
        Vec::new(),
        tactic_options,
    )
    .map_err(|err| {
        formalization_machine_tactic_error_response(candidate_hash, err.diagnostic.kind)
    })?;
    let [goal_id] = start.state.open_goals.as_slice() else {
        return Err(formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::ProofBridgeFailed,
        ));
    };
    let tactic =
        machine_tactic_validate_machine_tactic_candidate(*goal_id, proof_candidate.tactic.clone())
            .map_err(|err| {
                formalization_machine_tactic_error_response(candidate_hash, err.diagnostic.kind)
            })?;
    let run =
        machine_tactic_run_machine_tactic_with_budget(&start.state, tactic.tactic, tactic_budget)
            .map_err(|err| {
            formalization_machine_tactic_error_response(candidate_hash, err.diagnostic.kind)
        })?;
    if !run.state.open_goals.is_empty() {
        return Err(formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::ProofBridgeFailed,
        ));
    }
    let extracted = machine_tactic_extract_closed_machine_theorem_decl(
        &run.state,
        MachineApiDiagnosticPhase::KernelCheck,
    )
    .map_err(|err| {
        formalization_machine_tactic_error_response(candidate_hash, err.diagnostic.kind)
    })?;
    let Decl::Theorem {
        name,
        universe_params,
        ty,
        proof,
    } = extracted.theorem
    else {
        return Err(formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::ProofBridgeFailed,
        ));
    };
    if name != theorem_name.as_dotted()
        || universe_params != statement.universe_params
        || !advanced_ai_core_expr_bytes_eq(&ty, accepted_theorem_type)
    {
        return Err(formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::FormalizationProofStatementMismatch,
        ));
    }
    let import_modules = verified_imports
        .iter()
        .map(|import| import.verified_module().clone())
        .collect::<Vec<_>>();
    let cert = match npa_cert::build_module_cert(
        CoreModule {
            name: module,
            declarations: vec![Decl::Theorem {
                name,
                universe_params,
                ty,
                proof,
            }],
        },
        &import_modules,
    ) {
        Ok(cert) => cert,
        Err(npa_cert::CertError::Kernel(_)) => {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            ));
        }
        Err(_) => {
            return Err(AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            });
        }
    };
    let cert_bytes =
        npa_cert::encode_module_cert(&cert).map_err(|_| AdvancedAiEndpointResponse::Error {
            error: AdvancedAiEndpointError::InternalValidatorFailure,
        })?;
    let mut verifier_session = VerifierSession::new();
    for import in import_modules {
        verifier_session.register_verified_module(import);
    }
    npa_cert::verify_module_cert(&cert_bytes, &mut verifier_session, &AxiomPolicy::normal())
        .map_err(|_| {
            rejected_response(
                candidate_hash,
                AdvancedAiValidationError::IndependentCheckerRejected,
                None,
            )
        })?;
    Ok(())
}

fn formalization_scratch_module(proof_root_hash: Hash) -> ModuleName {
    Name(vec![
        "NPA".to_owned(),
        "Advanced".to_owned(),
        "FormalizationScratch".to_owned(),
        lowerhex_name_component(proof_root_hash),
    ])
}

fn formalization_scratch_theorem(proof_root_hash: Hash) -> Name {
    let mut components = formalization_scratch_module(proof_root_hash).0;
    components.push("theorem".to_owned());
    Name(components)
}

fn lowerhex_hash(hash: Hash) -> String {
    let mut output = String::with_capacity(64);
    for byte in hash {
        use std::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to string cannot fail");
    }
    output
}

fn lowerhex_name_component(hash: Hash) -> String {
    format!("h{}", lowerhex_hash(hash))
}

fn formalization_machine_tactic_error_response(
    candidate_hash: Hash,
    kind: MachineApiErrorKind,
) -> AdvancedAiEndpointResponse {
    match kind {
        MachineApiErrorKind::BudgetExceeded
        | MachineApiErrorKind::TooLargeTerm
        | MachineApiErrorKind::TooManyGoals => rejected_response(
            candidate_hash,
            AdvancedAiValidationError::BudgetExceeded,
            None,
        ),
        MachineApiErrorKind::UnsupportedTactic => rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            None,
        ),
        MachineApiErrorKind::InvalidMachineApiOptions => rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        ),
        _ => formalization_rejected_response(
            candidate_hash,
            AdvancedFormalizationError::ProofBridgeFailed,
        ),
    }
}

fn formalization_rejected_response(
    candidate_hash: Hash,
    error: AdvancedFormalizationError,
) -> AdvancedAiEndpointResponse {
    rejected_response(
        candidate_hash,
        AdvancedAiValidationError::FeatureRejected,
        Some(AdvancedAiFeatureError::Formalization(error)),
    )
}

fn run_advanced_ai_inductive_validated(
    validated: AdvancedValidatedCommonEnvelope,
    verified_imports: &[VerifiedImportRef],
) -> AdvancedAiEndpointResponse {
    let candidate_hash = validated.candidate_hash;
    let proposal = match decode_inductive_proposal(&validated.envelope.payload) {
        Ok(proposal) => proposal,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };

    let [family] = proposal.inductives.as_slice() else {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        );
    };

    let family_public_name =
        advanced_ai_family_public_name(proposal.block_name.as_ref(), &family.name);
    let constructor_public_names = family
        .constructors
        .iter()
        .map(|constructor| advanced_ai_append_name(&family_public_name, &constructor.name))
        .collect::<Vec<_>>();
    let recursor_public_name =
        advanced_ai_append_name(&family_public_name, &Name::from_dotted("rec"));
    if advanced_ai_inductive_names_collide(
        family,
        &family_public_name,
        &constructor_public_names,
        &recursor_public_name,
    ) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::NameCollision,
            )),
        );
    }

    if !advanced_ai_string_list_is_unique(&proposal.universe_params)
        || !level_is_in_scope(&family.result_sort, &proposal.universe_params)
        || !advanced_ai_inductive_family_levels_are_in_scope(family, &proposal.universe_params)
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    if advanced_ai_telescope_contains_const_name(&family.params, &family_public_name.as_dotted())
        || advanced_ai_telescope_contains_const_name(
            &family.indices,
            &family_public_name.as_dotted(),
        )
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::TargetRefMismatch,
            )),
        );
    }
    if !advanced_ai_telescope_imported_refs_are_resolved(
        &family.params,
        verified_imports,
        &BTreeSet::new(),
    ) || !advanced_ai_telescope_imported_refs_are_resolved(
        &family.indices,
        verified_imports,
        &BTreeSet::new(),
    ) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        );
    }

    let env = match advanced_ai_kernel_env_from_imports(verified_imports) {
        Ok(env) => env,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            );
        }
    };
    if advanced_ai_check_telescope_kernel(
        &env,
        &proposal.universe_params,
        family.params.iter().chain(&family.indices),
    )
    .is_err()
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::KernelRejected,
            None,
        );
    }

    let generated_names = constructor_public_names
        .iter()
        .chain(std::iter::once(&recursor_public_name))
        .map(Name::as_dotted)
        .collect::<BTreeSet<_>>();
    if family.constructors.iter().any(|constructor| {
        generated_names
            .iter()
            .any(|name| expr_contains_const_name(&constructor.ty, name))
    }) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::TargetRefMismatch,
            )),
        );
    }
    let mut allowed_local_names = BTreeSet::new();
    allowed_local_names.insert(family_public_name.as_dotted());
    if !family.constructors.iter().all(|constructor| {
        expr_imported_refs_are_resolved_with_allowed_locals(
            &constructor.ty,
            verified_imports,
            &allowed_local_names,
        )
    }) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        );
    }

    let base_decl = advanced_ai_base_inductive_decl(
        &proposal,
        family,
        &family_public_name,
        &constructor_public_names,
    );
    let mut constructor_env = env.clone();
    if constructor_env
        .add_axiom(
            base_decl.name.clone(),
            base_decl.universe_params.clone(),
            advanced_ai_inductive_type(&base_decl),
        )
        .is_err()
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::NameCollision,
            )),
        );
    }
    for constructor in &base_decl.constructors {
        if expect_sort_public(
            &constructor_env,
            &Ctx::new(),
            &proposal.universe_params,
            &constructor.ty,
        )
        .is_err()
        {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            );
        }
    }

    for constructor in &base_decl.constructors {
        match advanced_ai_check_constructor_result(&constructor_env, &base_decl, constructor) {
            Ok(()) => {}
            Err(AdvancedInductiveCheckError::TargetRefMismatch) => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    Some(AdvancedAiFeatureError::AdvancedInductive(
                        AdvancedInductiveError::TargetRefMismatch,
                    )),
                );
            }
            Err(AdvancedInductiveCheckError::KernelRejected) => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::KernelRejected,
                    None,
                );
            }
            Err(AdvancedInductiveCheckError::UnsupportedPositivity) => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::UnsupportedFeature,
                    Some(AdvancedAiFeatureError::AdvancedInductive(
                        AdvancedInductiveError::PositivityProfileUnsupported,
                    )),
                );
            }
        }
    }

    for constructor in &base_decl.constructors {
        match advanced_ai_check_constructor_positivity(&base_decl, constructor) {
            Ok(()) => {}
            Err(AdvancedInductiveCheckError::TargetRefMismatch) => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    Some(AdvancedAiFeatureError::AdvancedInductive(
                        AdvancedInductiveError::TargetRefMismatch,
                    )),
                );
            }
            Err(AdvancedInductiveCheckError::UnsupportedPositivity) => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::UnsupportedFeature,
                    Some(AdvancedAiFeatureError::AdvancedInductive(
                        AdvancedInductiveError::PositivityProfileUnsupported,
                    )),
                );
            }
            Err(AdvancedInductiveCheckError::KernelRejected) => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::KernelRejected,
                    None,
                );
            }
        }
    }

    if npa_cert::classify_inductive_artifact_profile_v1(&base_decl)
        != InductiveArtifactProfileCheckV1::SupportedMvpRecursor
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        );
    }
    let final_decl = match npa_cert::generate_inductive_artifacts_v1(&base_decl) {
        Ok(final_decl) => final_decl,
        Err(_) => {
            return AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            };
        }
    };
    let cert_decl = Decl::Inductive {
        name: final_decl.name.clone(),
        universe_params: final_decl.universe_params.clone(),
        ty: advanced_ai_inductive_type(&final_decl),
        data: Box::new(final_decl),
    };
    let import_modules = verified_imports
        .iter()
        .map(|import| import.verified_module().clone())
        .collect::<Vec<_>>();
    let cert = match npa_cert::build_module_cert(
        CoreModule {
            name: family_public_name.clone(),
            declarations: vec![cert_decl],
        },
        &import_modules,
    ) {
        Ok(cert) => cert,
        Err(npa_cert::CertError::Kernel(_)) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            );
        }
        Err(_) => {
            return AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            };
        }
    };
    let cert_bytes = match npa_cert::encode_module_cert(&cert) {
        Ok(bytes) => bytes,
        Err(_) => {
            return AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            };
        }
    };
    let mut verifier_session = VerifierSession::new();
    for import in import_modules {
        verifier_session.register_verified_module(import);
    }
    if npa_cert::verify_module_cert(&cert_bytes, &mut verifier_session, &AxiomPolicy::normal())
        .is_err()
    {
        return AdvancedAiEndpointResponse::Error {
            error: AdvancedAiEndpointError::InternalValidatorFailure,
        };
    }
    let Some(decl) = cert.declarations.first() else {
        return AdvancedAiEndpointResponse::Error {
            error: AdvancedAiEndpointError::InternalValidatorFailure,
        };
    };
    if proposal
        .expected_decl_hash
        .is_some_and(|expected| expected != decl.hashes.decl_certificate_hash)
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }
    success_response(
        candidate_hash,
        AdvancedAiSuccessPayload::AdvancedInductive {
            decl_interface_hash: decl.hashes.decl_interface_hash,
            decl_certificate_hash: decl.hashes.decl_certificate_hash,
        },
    )
}

fn run_advanced_ai_smt_reconstruct_validated(
    validated: AdvancedValidatedCommonEnvelope,
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    let candidate_hash = validated.candidate_hash;
    let candidate = match decode_smt_candidate(&validated.envelope.payload) {
        Ok(candidate) => candidate,
        Err(_) => {
            return smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            );
        }
    };

    let goal_fingerprint = advanced_ai_goal_fingerprint(validated.env_fingerprint, &candidate.goal);
    if validated.envelope.target.goal_fingerprint != Some(goal_fingerprint) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }
    match validate_advanced_ai_goal(&candidate.goal, verified_imports) {
        Ok(()) => {}
        Err(AdvancedGoalValidationError::EnvelopeMalformed) => {
            return smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            );
        }
        Err(AdvancedGoalValidationError::ImportClosureMismatch) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            );
        }
        Err(AdvancedGoalValidationError::KernelRejected) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            );
        }
    }

    let problem_bytes = match advanced_ai_smt_problem_bytes(
        candidate_hash,
        &candidate.encoded_problem,
        workspace_root,
    ) {
        Ok(bytes) => bytes,
        Err(response) => return response,
    };
    let problem =
        match advanced_ai_validate_smt_problem_bytes(candidate_hash, &problem_bytes, &candidate) {
            Ok(problem) => problem,
            Err(response) => return response,
        };
    if problem.goal_fingerprint != goal_fingerprint {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }
    if problem.logic != candidate.logic {
        return smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::EncodingMismatch,
        );
    }

    let env = match advanced_ai_kernel_env_from_imports(verified_imports) {
        Ok(env) => env,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            );
        }
    };
    let Some(smt_options) = validated.options.smt.as_ref() else {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    };
    let primitives = match advanced_ai_resolve_smt_primitives(
        candidate_hash,
        &env,
        smt_options,
        verified_imports,
    ) {
        Ok(primitives) => primitives,
        Err(response) => return response,
    };

    let command_context = match advanced_ai_validate_smt_commands(
        candidate_hash,
        &candidate,
        &problem,
        &primitives,
    ) {
        Ok(context) => context,
        Err(response) => return response,
    };

    let payload_bytes = match advanced_ai_smt_payload_bytes(
        candidate_hash,
        &candidate.proof_payload,
        workspace_root,
    ) {
        Ok(bytes) => bytes,
        Err(response) => return response,
    };
    let proof_payload = match advanced_ai_validate_smt_proof_payload_bytes(
        candidate_hash,
        &payload_bytes,
        &candidate,
    ) {
        Ok(payload) => payload,
        Err(response) => return response,
    };
    match &proof_payload {
        AdvancedValidatedSmtProofPayload::ProofNodeTable(table) => {
            if let Err(response) = advanced_ai_validate_smt_proof_table(
                candidate_hash,
                table,
                &candidate,
                &problem,
                &command_context,
                verified_imports,
            ) {
                return response;
            }
        }
        AdvancedValidatedSmtProofPayload::Opaque {
            format,
            payload_hash,
            size_bytes,
        } => {
            let _ = (*format, *payload_hash, *size_bytes);
        }
        AdvancedValidatedSmtProofPayload::SolverResultOnly {
            payload_hash,
            size_bytes,
        } => {
            let _ = (*payload_hash, *size_bytes);
            return smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::UnsupportedFeature,
                AdvancedSmtCertificateError::SolverResultOnly,
            );
        }
    }

    if let Err(response) =
        advanced_ai_validate_smt_reconstruction_plan(candidate_hash, &candidate, verified_imports)
    {
        return response;
    }

    let supported_fragment = match advanced_ai_validate_smt_rule_registry_for_problem(
        candidate_hash,
        &candidate,
        &problem,
    ) {
        Ok(fragment) => fragment,
        Err(response) => return response,
    };

    let final_proof = match advanced_ai_reconstruct_smt_final_proof(
        candidate_hash,
        &candidate,
        &proof_payload,
        supported_fragment,
        &env,
        verified_imports,
    ) {
        Ok(final_proof) => final_proof,
        Err(response) => return response,
    };

    success_response(
        candidate_hash,
        AdvancedAiSuccessPayload::SmtCertificate { final_proof },
    )
}

fn run_advanced_ai_typeclass_resolve_validated(
    validated: AdvancedValidatedCommonEnvelope,
    verified_imports: &[VerifiedImportRef],
) -> AdvancedAiEndpointResponse {
    let candidate_hash = validated.candidate_hash;
    let plan = match decode_typeclass_resolution_plan(&validated.envelope.payload) {
        Ok(plan) => plan,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };
    if !advanced_ai_typeclass_candidate_targets_are_unique(&plan.ordered_candidates) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    if validated.envelope.target.goal_fingerprint
        != Some(advanced_ai_goal_fingerprint(
            validated.env_fingerprint,
            &plan.goal,
        ))
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }

    match validate_advanced_ai_goal(&plan.goal, verified_imports) {
        Ok(()) => {}
        Err(AdvancedGoalValidationError::EnvelopeMalformed) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
        Err(AdvancedGoalValidationError::ImportClosureMismatch) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            );
        }
        Err(AdvancedGoalValidationError::KernelRejected) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            );
        }
    }

    let env = match advanced_ai_kernel_env_from_imports(verified_imports) {
        Ok(env) => env,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            );
        }
    };
    let goal_ctx = advanced_ai_goal_ctx(&plan.goal);

    let class_declarations = match advanced_ai_resolve_typeclass_class_declarations(
        candidate_hash,
        &env,
        &validated.options.typeclass.class_declarations,
        verified_imports,
    ) {
        Ok(class_declarations) => class_declarations,
        Err(response) => return response,
    };

    let candidates = match advanced_ai_resolve_typeclass_candidates(
        candidate_hash,
        &env,
        &class_declarations,
        &plan.ordered_candidates,
        verified_imports,
    ) {
        Ok(candidates) => candidates,
        Err(response) => return response,
    };

    if advanced_ai_typeclass_head_name(
        &env,
        &goal_ctx,
        &plan.goal.universe_params,
        &plan.goal.target,
        &class_declarations,
    )
    .is_none()
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::TypeclassResolution(
                AdvancedTypeclassResolutionError::ClassHeadUnsupported,
            )),
        );
    }

    let proof = match advanced_ai_typeclass_search(
        &env,
        &goal_ctx,
        &plan.goal.universe_params,
        &plan.goal.target,
        &class_declarations,
        &candidates,
        plan.max_depth,
        plan.max_nodes,
    ) {
        AdvancedTypeclassSearchOutcome::Success(proof) => proof,
        AdvancedTypeclassSearchOutcome::NoSolution => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::NoSolution,
                Some(AdvancedAiFeatureError::TypeclassResolution(
                    AdvancedTypeclassResolutionError::NoSolution,
                )),
            );
        }
        AdvancedTypeclassSearchOutcome::BudgetExceeded => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::BudgetExceeded,
                None,
            );
        }
        AdvancedTypeclassSearchOutcome::AmbiguousResolution => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::AmbiguousResolution,
                None,
            );
        }
        AdvancedTypeclassSearchOutcome::CandidateInterfaceInvalid => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::TypeclassResolution(
                    AdvancedTypeclassResolutionError::CandidateInterfaceInvalid,
                )),
            );
        }
    };

    if env
        .check(
            &goal_ctx,
            &plan.goal.universe_params,
            &proof,
            &plan.goal.target,
        )
        .is_err()
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::KernelRejected,
            None,
        );
    }

    success_response(
        candidate_hash,
        AdvancedAiSuccessPayload::TypeclassResolution { proof },
    )
}

fn run_advanced_ai_theorem_graph_query_validated(
    validated: AdvancedValidatedCommonEnvelope,
    verified_imports: &[VerifiedImportRef],
    workspace_root: &Path,
) -> AdvancedAiEndpointResponse {
    let candidate_hash = validated.candidate_hash;
    let query = match decode_theorem_graph_query(&validated.envelope.payload) {
        Ok(query) => query,
        Err(DecodeError::TheoremGraphSnapshotBytesTooLarge) => {
            return theorem_graph_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedTheoremGraphError::SnapshotMalformed,
            );
        }
        Err(DecodeError::TheoremGraphQueryFeaturesBytesTooLarge) => {
            return theorem_graph_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedTheoremGraphError::QueryFeaturesMalformed,
            );
        }
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };

    if query.env_fingerprint != validated.envelope.target.env_fingerprint
        || Some(query.goal_fingerprint) != validated.envelope.target.goal_fingerprint
        || advanced_ai_goal_fingerprint(validated.env_fingerprint, &query.goal)
            != query.goal_fingerprint
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }

    match validate_advanced_ai_goal(&query.goal, verified_imports) {
        Ok(()) => {}
        Err(AdvancedGoalValidationError::EnvelopeMalformed) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
        Err(AdvancedGoalValidationError::ImportClosureMismatch) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            );
        }
        Err(AdvancedGoalValidationError::KernelRejected) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                None,
            );
        }
    }

    if query.limit > MAX_ADVANCED_AI_THEOREM_GRAPH_RESULT_LIMIT {
        return theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::LimitOutOfRange,
        );
    }

    let snapshot_bytes = match advanced_ai_theorem_graph_snapshot_bytes(
        candidate_hash,
        &query.snapshot.source,
        workspace_root,
    ) {
        Ok(bytes) => bytes,
        Err(response) => return response,
    };
    let snapshot = match advanced_ai_validate_theorem_graph_snapshot_bytes(
        candidate_hash,
        &snapshot_bytes,
        &query.snapshot,
    ) {
        Ok(snapshot) => snapshot,
        Err(response) => return response,
    };

    let feature_bytes = match advanced_ai_theorem_graph_query_features_bytes(
        candidate_hash,
        &query.query_features,
        workspace_root,
    ) {
        Ok(bytes) => bytes,
        Err(response) => return response,
    };
    let query_features = match advanced_ai_validate_theorem_graph_query_features_bytes(
        candidate_hash,
        &feature_bytes,
        &query,
    ) {
        Ok(query_features) => query_features,
        Err(response) => return response,
    };

    if snapshot.source_release_hash != query.snapshot.source_release_hash
        || snapshot.extractor_version != query.snapshot.extractor_version
    {
        return theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::SnapshotMalformed,
        );
    }
    if query_features.env_fingerprint != query.env_fingerprint
        || query_features.goal_fingerprint != query.goal_fingerprint
        || query_features.feature_schema_version
            != AdvancedTheoremGraphFeatureSchemaVersion::MvpGoalFeaturesV1
    {
        return theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::QueryFeaturesMalformed,
        );
    }
    if !advanced_ai_theorem_graph_features_are_well_formed(&query_features.features) {
        return theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::QueryFeaturesMalformed,
        );
    }
    if !advanced_ai_theorem_graph_snapshot_is_well_formed(&snapshot) {
        return theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::SnapshotMalformed,
        );
    }

    let mut entries = Vec::new();
    for node in &snapshot.nodes {
        match advanced_ai_resolve_theorem_graph_node(node, verified_imports) {
            AdvancedTheoremGraphNodeResolution::Missing => {}
            AdvancedTheoremGraphNodeResolution::Mismatch => {
                return theorem_graph_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    AdvancedTheoremGraphError::NodeResolutionMismatch,
                );
            }
            AdvancedTheoremGraphNodeResolution::Resolved { eligible } => {
                if eligible && entries.len() < query.limit as usize {
                    entries.push(AdvancedMachineTheoremGraphResultEntry {
                        node: node.clone(),
                        score: AdvancedMachineTheoremGraphScore {
                            score_microunits: 0,
                        },
                    });
                }
            }
        }
    }

    success_response(
        candidate_hash,
        AdvancedAiSuccessPayload::TheoremGraphQuery {
            result: AdvancedMachineTheoremGraphResult { entries },
        },
    )
}

struct AdvancedUniverseRepairCandidateOuter {
    goal: Option<AdvancedAiGoal>,
    target_expr: Expr,
    instantiation_items: Vec<Vec<u8>>,
    constraint_hint_items: Vec<Vec<u8>>,
    minimization_hint: Option<AdvancedUniverseMinimizationHint>,
}

fn run_advanced_ai_universe_repair_validated(
    validated: AdvancedValidatedCommonEnvelope,
    verified_imports: &[VerifiedImportRef],
) -> AdvancedAiEndpointResponse {
    let candidate_hash = validated.candidate_hash;
    let raw = match decode_universe_repair_candidate_outer(&validated.envelope.payload) {
        Ok(raw) => raw,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };

    if validated.envelope.target.target_decl_hash.is_some() {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            None,
        );
    }

    let goal = match raw.goal.as_ref() {
        Some(goal) => goal,
        None => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };
    if !advanced_ai_core_expr_bytes_eq(&goal.target, &raw.target_expr) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::TargetFingerprintMismatch,
            )),
        );
    }
    if validated.envelope.target.goal_fingerprint
        != Some(advanced_ai_goal_fingerprint(
            validated.env_fingerprint,
            goal,
        ))
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::TargetFingerprintMismatch,
            )),
        );
    }

    if !advanced_ai_string_list_is_unique(&goal.universe_params)
        || !expr_levels_are_in_scope(&goal.target, &goal.universe_params)
        || !goal
            .local_context
            .iter()
            .all(|local| local_decl_levels_are_in_scope(local, &goal.universe_params))
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }
    if !goal_imported_refs_are_resolved(goal, verified_imports) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        );
    }
    if validate_goal_kernel(goal, verified_imports).is_err() {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::KernelRejected,
            None,
        );
    }

    let instantiations = match decode_universe_instantiation_items(&raw.instantiation_items) {
        Ok(instantiations) => instantiations,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };
    if !universe_instantiations_are_strictly_sorted(&instantiations) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    let constraint_hints = match decode_universe_constraint_hint_items(&raw.constraint_hint_items) {
        Ok(hints) => hints,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            );
        }
    };
    if !universe_constraint_hints_are_strictly_sorted(&constraint_hints) {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }
    for hint in &constraint_hints {
        if !constraint_levels_are_in_scope(&hint.constraint, &goal.universe_params) {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::UnknownUniverseParam,
                )),
            );
        }
    }

    let mut repaired_expr = raw.target_expr.clone();
    for patch in &instantiations {
        let reached = match expr_at_path(&raw.target_expr, &patch.occurrence.path) {
            Some(reached) => reached,
            None => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    Some(AdvancedAiFeatureError::UniverseRepair(
                        AdvancedUniverseRepairError::InvalidOccurrencePath,
                    )),
                );
            }
        };
        let Expr::Const { name, .. } = reached else {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::InvalidOccurrencePath,
                )),
            );
        };
        let resolved = match resolve_advanced_ai_global_ref(
            &patch.occurrence.expected_ref,
            verified_imports,
        ) {
            Some(resolved) => resolved,
            None => {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::ImportClosureMismatch,
                    None,
                );
            }
        };
        if name != &resolved.const_name {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::TargetRefMismatch,
                )),
            );
        }
        if patch.explicit_level_args.len() != resolved.universe_arity {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::IllFormedLevelExpr,
                )),
            );
        }
        for level in &patch.explicit_level_args {
            if !level_is_in_scope(level, &goal.universe_params) {
                return rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    Some(AdvancedAiFeatureError::UniverseRepair(
                        AdvancedUniverseRepairError::UnknownUniverseParam,
                    )),
                );
            }
        }
        if replace_const_levels_at_path(
            &mut repaired_expr,
            &patch.occurrence.path,
            patch.explicit_level_args.clone(),
        )
        .is_none()
        {
            return AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            };
        }
    }

    let constraints = match derive_universe_constraints(goal, &repaired_expr, verified_imports) {
        Ok(constraints) => constraints,
        Err(_) => {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::NoSolution,
                Some(AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::UnsatisfiedConstraint,
                )),
            );
        }
    };
    let constraint_keys = constraints
        .iter()
        .map(advanced_ai_universe_constraint_canonical_bytes)
        .collect::<BTreeSet<_>>();
    for hint in &constraint_hints {
        let key = advanced_ai_universe_constraint_canonical_bytes(&hint.constraint);
        if !constraint_keys.contains(&key) {
            return rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::ConstraintHintMismatch,
                )),
            );
        }
    }
    if constraints
        .iter()
        .any(|constraint| !universe_constraint_is_satisfiable(constraint))
    {
        return rejected_response(
            candidate_hash,
            AdvancedAiValidationError::NoSolution,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::UnsatisfiedConstraint,
            )),
        );
    }
    let constraint_set_hash = advanced_ai_universe_constraint_set_hash(&constraints);
    let success = AdvancedAiSuccessPayload::UniverseRepair {
        repaired_expr,
        constraint_set_hash,
    };
    success_response(candidate_hash, success)
}

fn success_response(
    candidate_hash: Hash,
    payload: AdvancedAiSuccessPayload,
) -> AdvancedAiEndpointResponse {
    let validation_result_hash =
        advanced_ai_validation_result_hash_for_success(candidate_hash, &payload);
    AdvancedAiEndpointResponse::Success {
        candidate_hash,
        validation_result_hash,
        payload: Box::new(payload),
    }
}

fn validate_imports(
    candidate_hash: Hash,
    imports: &[AdvancedImportIdentity],
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let mut previous: Option<&AdvancedImportIdentity> = None;
    for import in imports {
        if !import.module.is_canonical() {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            ));
        }
        if let Some(previous) = previous {
            match compare_import_identities(previous, import) {
                Ok(Ordering::Greater) => {
                    return Err(rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        None,
                    ));
                }
                Ok(Ordering::Equal) => {
                    return Err(rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::ImportClosureMismatch,
                        None,
                    ));
                }
                Ok(Ordering::Less) => {}
                Err(_) => {
                    return Err(rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        None,
                    ));
                }
            }
        }
        previous = Some(import);
    }

    if imports.len() != verified_imports.len() {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        ));
    }

    for (expected, actual) in imports.iter().zip(verified_imports) {
        let actual = AdvancedImportIdentity::from_verified_import(actual);
        if expected != &actual {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            ));
        }
    }

    Ok(())
}

fn validate_options_ref(
    candidate_hash: Hash,
    options_ref: &AdvancedAiOptionsRef,
    workspace_root: &Path,
) -> std::result::Result<(AdvancedAiOptions, Hash), AdvancedAiEndpointResponse> {
    let (declared_options_hash, canonical_bytes) = match options_ref {
        AdvancedAiOptionsRef::Inline {
            options_hash,
            canonical_bytes,
        } => {
            if canonical_bytes.len() > MAX_OPTIONS_BYTES {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    None,
                ));
            }
            (*options_hash, canonical_bytes.clone())
        }
        AdvancedAiOptionsRef::Artifact {
            path,
            file_hash,
            options_hash,
            size_bytes,
        } => {
            if usize::try_from(*size_bytes)
                .map(|size| size > MAX_OPTIONS_BYTES)
                .unwrap_or(true)
            {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    None,
                ));
            }
            let path = match validate_artifact_path(workspace_root, path) {
                Ok(path) => path,
                Err(ArtifactPathError::EnvelopeMalformed) => {
                    return Err(rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        None,
                    ));
                }
                Err(ArtifactPathError::ArtifactUnavailable) => {
                    return Err(AdvancedAiEndpointResponse::Error {
                        error: AdvancedAiEndpointError::ArtifactUnavailable,
                    });
                }
            };
            let bytes = std::fs::read(path).map_err(|_| AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::ArtifactUnavailable,
            })?;
            if bytes.len() as u64 != *size_bytes || advanced_ai_file_hash(&bytes) != *file_hash {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::PayloadHashMismatch,
                    None,
                ));
            }
            (*options_hash, bytes)
        }
    };

    let options = decode_options(&canonical_bytes).map_err(|_| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;
    let actual_options_hash = advanced_ai_options_hash(&canonical_bytes);
    if actual_options_hash != declared_options_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }

    Ok((options, actual_options_hash))
}

fn validate_target_shape(
    candidate_hash: Hash,
    task_kind: AdvancedAiTaskKind,
    target: &AdvancedAiTarget,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let valid = match task_kind {
        AdvancedAiTaskKind::AdvancedInductive
        | AdvancedAiTaskKind::NaturalLanguageFormalization => {
            target.target_decl_hash.is_none() && target.goal_fingerprint.is_none()
        }
        AdvancedAiTaskKind::UniverseRepair => {
            (target.target_decl_hash.is_none() && target.goal_fingerprint.is_some())
                || (target.target_decl_hash.is_some() && target.goal_fingerprint.is_none())
        }
        AdvancedAiTaskKind::TypeclassResolution
        | AdvancedAiTaskKind::SmtCertificate
        | AdvancedAiTaskKind::TheoremGraphQuery => {
            target.target_decl_hash.is_none() && target.goal_fingerprint.is_some()
        }
    };
    if valid {
        Ok(())
    } else {
        Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ))
    }
}

fn validate_required_options(
    candidate_hash: Hash,
    task_kind: AdvancedAiTaskKind,
    options: &AdvancedAiOptions,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let valid = match task_kind {
        AdvancedAiTaskKind::SmtCertificate => options.smt.is_some(),
        AdvancedAiTaskKind::NaturalLanguageFormalization => options.formalization.is_some(),
        AdvancedAiTaskKind::AdvancedInductive
        | AdvancedAiTaskKind::UniverseRepair
        | AdvancedAiTaskKind::TypeclassResolution
        | AdvancedAiTaskKind::TheoremGraphQuery => true,
    };
    if valid {
        Ok(())
    } else {
        Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        ))
    }
}

fn validate_task_options_shape(
    candidate_hash: Hash,
    task_kind: AdvancedAiTaskKind,
    options: &AdvancedAiOptions,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    if task_kind != AdvancedAiTaskKind::NaturalLanguageFormalization {
        return Ok(());
    }
    let Some(formalization) = options.formalization.as_ref() else {
        return Ok(());
    };
    decode_machine_tactic_options(&formalization.tactic_options_canonical_bytes)
        .and_then(|options| {
            if options.max_simp_rewrite_steps == 0
                || options.max_open_goals == 0
                || options.max_metas == 0
            {
                return Err(());
            }
            Ok(options)
        })
        .map_err(|()| {
            rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                None,
            )
        })?;
    decode_machine_tactic_budget(&formalization.tactic_budget_canonical_bytes).map_err(|()| {
        rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        )
    })?;
    Ok(())
}

#[derive(Clone)]
struct AdvancedResolvedGlobalDecl {
    const_name: String,
    universe_params: Vec<String>,
    ty: Expr,
}

fn advanced_ai_resolve_global_decl(
    global_ref: &AdvancedAiGlobalRef,
    imports: &[VerifiedImportRef],
) -> Option<AdvancedResolvedGlobalDecl> {
    let mut matches = Vec::new();
    for import in imports {
        let identity = AdvancedImportIdentity::from_verified_import(import);
        if identity.module != global_ref.module
            || identity.export_hash != global_ref.export_hash
            || identity.certificate_hash != global_ref.certificate_hash
        {
            continue;
        }
        for export in import.exports().iter().filter(|export| {
            export.name == global_ref.name
                && export.decl_interface_hash == global_ref.decl_interface_hash
        }) {
            let decl = import
                .certified_env_decls()
                .iter()
                .find(|decl| decl.name() == export.name.as_dotted())?;
            matches.push(AdvancedResolvedGlobalDecl {
                const_name: export.name.as_dotted(),
                universe_params: decl.universe_params().to_vec(),
                ty: decl.ty().clone(),
            });
        }
    }
    let [resolved] = matches.as_slice() else {
        return None;
    };
    Some(resolved.clone())
}

fn advanced_ai_resolved_single_universe(resolved: &AdvancedResolvedGlobalDecl) -> Option<Level> {
    let [param] = resolved.universe_params.as_slice() else {
        return None;
    };
    Some(Level::param(param.clone()))
}

fn advanced_ai_resolved_public_type_defeq(
    env: &Env,
    resolved: &AdvancedResolvedGlobalDecl,
    expected: &Expr,
) -> bool {
    advanced_ai_resolved_defeq(
        env,
        &Ctx::new(),
        &resolved.universe_params,
        &resolved.ty,
        expected,
    )
}

fn advanced_ai_resolved_defeq(
    env: &Env,
    ctx: &Ctx,
    delta: &[String],
    actual: &Expr,
    expected: &Expr,
) -> bool {
    matches!(env.is_defeq(ctx, delta, actual, expected), Ok(true))
}

#[derive(Clone)]
struct AdvancedResolvedTypeclassGlobalRef {
    const_name: String,
    universe_params: Vec<String>,
    ty: Expr,
}

#[derive(Clone)]
struct AdvancedResolvedTypeclassCandidate {
    target_key: Vec<u8>,
    const_name: String,
    universe_params: Vec<String>,
    telescope: Vec<Expr>,
    result: Expr,
    class_head: Option<String>,
}

struct AdvancedTypeclassCandidateApplication {
    levels: Vec<Level>,
    args: Vec<Option<Expr>>,
    recursive_obligations: Vec<(usize, Expr)>,
    fingerprint: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AdvancedTypeclassSearchStop {
    AmbiguousResolution,
    BudgetExceeded,
    CandidateInterfaceInvalid,
}

enum AdvancedTypeclassSearchOutcome {
    Success(Expr),
    NoSolution,
    BudgetExceeded,
    AmbiguousResolution,
    CandidateInterfaceInvalid,
}

fn advanced_ai_typeclass_candidate_targets_are_unique(
    candidates: &[AdvancedMachineInstanceCandidateRef],
) -> bool {
    let mut seen = BTreeSet::new();
    for candidate in candidates {
        let Ok(key) = advanced_ai_instance_target_canonical_bytes(&candidate.target) else {
            return false;
        };
        if !seen.insert(key) {
            return false;
        }
    }
    true
}

fn advanced_ai_goal_ctx(goal: &AdvancedAiGoal) -> Ctx {
    let mut ctx = Ctx::new();
    for local in &goal.local_context {
        if let Some(value) = &local.value {
            ctx.push_definition(local.name.clone(), local.ty.clone(), value.clone());
        } else {
            ctx.push_assumption(local.name.clone(), local.ty.clone());
        }
    }
    ctx
}

fn advanced_ai_resolve_typeclass_class_declarations(
    candidate_hash: Hash,
    env: &Env,
    class_declarations: &[AdvancedAiGlobalRef],
    imports: &[VerifiedImportRef],
) -> std::result::Result<BTreeSet<String>, AdvancedAiEndpointResponse> {
    let mut resolved_classes = BTreeSet::new();
    for class_ref in class_declarations {
        let Some(resolved) = advanced_ai_resolve_typeclass_global_ref(class_ref, imports) else {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            ));
        };
        if !advanced_ai_typeclass_class_declaration_is_valid(env, &resolved) {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::TypeclassResolution(
                    AdvancedTypeclassResolutionError::ClassDeclarationMismatch,
                )),
            ));
        }
        resolved_classes.insert(resolved.const_name);
    }
    Ok(resolved_classes)
}

fn advanced_ai_resolve_typeclass_candidates(
    candidate_hash: Hash,
    env: &Env,
    class_declarations: &BTreeSet<String>,
    candidates: &[AdvancedMachineInstanceCandidateRef],
    imports: &[VerifiedImportRef],
) -> std::result::Result<Vec<AdvancedResolvedTypeclassCandidate>, AdvancedAiEndpointResponse> {
    let mut resolved = Vec::new();
    for candidate in candidates {
        let target_key =
            advanced_ai_instance_target_canonical_bytes(&candidate.target).map_err(|_| {
                rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    None,
                )
            })?;
        let AdvancedMachineInstanceTargetRef::Imported { global_ref } = &candidate.target;
        let Some(resolved_ref) = advanced_ai_resolve_typeclass_global_ref(global_ref, imports)
        else {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            ));
        };
        let Some((telescope, result)) =
            advanced_ai_decompose_typeclass_candidate_type(env, &resolved_ref)
        else {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::TypeclassResolution(
                    AdvancedTypeclassResolutionError::CandidateInterfaceInvalid,
                )),
            ));
        };
        if !advanced_ai_candidate_expr_has_only_telescope_bvars(&result, telescope.len(), 0) {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                Some(AdvancedAiFeatureError::TypeclassResolution(
                    AdvancedTypeclassResolutionError::CandidateInterfaceInvalid,
                )),
            ));
        }
        let class_head = advanced_ai_typeclass_head_name(
            env,
            &advanced_ai_telescope_ctx(&telescope),
            &resolved_ref.universe_params,
            &result,
            class_declarations,
        );
        resolved.push(AdvancedResolvedTypeclassCandidate {
            target_key,
            const_name: resolved_ref.const_name,
            universe_params: resolved_ref.universe_params,
            telescope,
            result,
            class_head,
        });
    }
    Ok(resolved)
}

fn advanced_ai_resolve_typeclass_global_ref(
    global_ref: &AdvancedAiGlobalRef,
    imports: &[VerifiedImportRef],
) -> Option<AdvancedResolvedTypeclassGlobalRef> {
    let mut matches = Vec::new();
    for import in imports {
        let identity = AdvancedImportIdentity::from_verified_import(import);
        if identity.module != global_ref.module
            || identity.export_hash != global_ref.export_hash
            || identity.certificate_hash != global_ref.certificate_hash
        {
            continue;
        }
        for export in import.exports().iter().filter(|export| {
            export.name == global_ref.name
                && export.decl_interface_hash == global_ref.decl_interface_hash
        }) {
            let decl = import
                .certified_env_decls()
                .iter()
                .find(|decl| decl.name() == export.name.as_dotted())?;
            matches.push(AdvancedResolvedTypeclassGlobalRef {
                const_name: export.name.as_dotted(),
                universe_params: decl.universe_params().to_vec(),
                ty: decl.ty().clone(),
            });
        }
    }
    let [resolved] = matches.as_slice() else {
        return None;
    };
    Some(resolved.clone())
}

fn advanced_ai_typeclass_class_declaration_is_valid(
    env: &Env,
    class_decl: &AdvancedResolvedTypeclassGlobalRef,
) -> bool {
    let mut ctx = Ctx::new();
    let mut current = class_decl.ty.clone();
    loop {
        let Ok(whnf) = env.whnf(&ctx, &class_decl.universe_params, &current) else {
            return false;
        };
        match whnf {
            Expr::Sort(_) => return true,
            Expr::Pi { binder, ty, body } => {
                if expect_sort_public(env, &ctx, &class_decl.universe_params, &ty).is_err() {
                    return false;
                }
                ctx.push_assumption(binder, (*ty).clone());
                current = Arc::unwrap_or_clone(body);
            }
            _ => return false,
        }
    }
}

fn advanced_ai_decompose_typeclass_candidate_type(
    env: &Env,
    candidate: &AdvancedResolvedTypeclassGlobalRef,
) -> Option<(Vec<Expr>, Expr)> {
    let mut ctx = Ctx::new();
    let mut telescope = Vec::new();
    let mut current = candidate.ty.clone();
    loop {
        let whnf = env.whnf(&ctx, &candidate.universe_params, &current).ok()?;
        match whnf {
            Expr::Pi { binder, ty, body } => {
                let domain = (*ty).clone();
                ctx.push_assumption(binder, domain.clone());
                telescope.push(domain);
                current = Arc::unwrap_or_clone(body);
            }
            result => return Some((telescope, result)),
        }
    }
}

fn advanced_ai_telescope_ctx(telescope: &[Expr]) -> Ctx {
    let mut ctx = Ctx::new();
    for ty in telescope {
        ctx.push_assumption("_", ty.clone());
    }
    ctx
}

fn advanced_ai_typeclass_head_name(
    env: &Env,
    ctx: &Ctx,
    delta: &[String],
    target: &Expr,
    class_declarations: &BTreeSet<String>,
) -> Option<String> {
    let whnf = env.whnf(ctx, delta, target).ok()?;
    let (head, _) = npa_kernel::expr::collect_apps(&whnf);
    let Expr::Const { name, .. } = head else {
        return None;
    };
    if class_declarations.contains(&name) {
        Some(name)
    } else {
        None
    }
}

#[allow(clippy::too_many_arguments)]
fn advanced_ai_typeclass_search(
    env: &Env,
    goal_ctx: &Ctx,
    goal_universe_params: &[String],
    goal_target: &Expr,
    class_declarations: &BTreeSet<String>,
    candidates: &[AdvancedResolvedTypeclassCandidate],
    max_depth: u32,
    max_nodes: u32,
) -> AdvancedTypeclassSearchOutcome {
    let mut node_count = 0u32;
    let mut successes = BTreeMap::<Vec<u8>, Expr>::new();
    match advanced_ai_collect_typeclass_solutions(
        env,
        goal_ctx,
        goal_universe_params,
        goal_target,
        class_declarations,
        candidates,
        max_depth,
        max_nodes,
        0,
        &mut node_count,
        &[],
    ) {
        Ok(proofs) => {
            for proof in proofs {
                let key = advanced_ai_expr_canonical_bytes(&proof);
                successes.entry(key).or_insert(proof);
                if successes.len() > 1 {
                    return AdvancedTypeclassSearchOutcome::AmbiguousResolution;
                }
            }
        }
        Err(AdvancedTypeclassSearchStop::AmbiguousResolution) => {
            return AdvancedTypeclassSearchOutcome::AmbiguousResolution;
        }
        Err(AdvancedTypeclassSearchStop::BudgetExceeded) => {
            return AdvancedTypeclassSearchOutcome::BudgetExceeded;
        }
        Err(AdvancedTypeclassSearchStop::CandidateInterfaceInvalid) => {
            return AdvancedTypeclassSearchOutcome::CandidateInterfaceInvalid;
        }
    }
    match successes.into_values().next() {
        Some(proof) => AdvancedTypeclassSearchOutcome::Success(proof),
        None => AdvancedTypeclassSearchOutcome::NoSolution,
    }
}

#[allow(clippy::too_many_arguments)]
fn advanced_ai_collect_typeclass_solutions(
    env: &Env,
    goal_ctx: &Ctx,
    goal_universe_params: &[String],
    obligation: &Expr,
    class_declarations: &BTreeSet<String>,
    candidates: &[AdvancedResolvedTypeclassCandidate],
    max_depth: u32,
    max_nodes: u32,
    current_depth: u32,
    node_count: &mut u32,
    visited: &[(Vec<u8>, Vec<u8>)],
) -> std::result::Result<Vec<Expr>, AdvancedTypeclassSearchStop> {
    let Some(obligation_head) = advanced_ai_typeclass_head_name(
        env,
        goal_ctx,
        goal_universe_params,
        obligation,
        class_declarations,
    ) else {
        return Ok(Vec::new());
    };
    let mut solutions = BTreeMap::<Vec<u8>, Expr>::new();
    for candidate in candidates {
        if *node_count >= max_nodes {
            return Err(AdvancedTypeclassSearchStop::BudgetExceeded);
        }
        *node_count += 1;
        if candidate.class_head.as_ref() != Some(&obligation_head) {
            continue;
        }
        let Some(application) = advanced_ai_try_typeclass_candidate(
            env,
            goal_ctx,
            goal_universe_params,
            obligation,
            class_declarations,
            candidate,
        )?
        else {
            continue;
        };
        if current_depth >= max_depth {
            return Err(AdvancedTypeclassSearchStop::BudgetExceeded);
        }
        let cycle_entry = (
            application.fingerprint.clone(),
            candidate.target_key.clone(),
        );
        if visited.iter().any(|entry| entry == &cycle_entry) {
            continue;
        }
        let mut child_visited = visited.to_owned();
        child_visited.push(cycle_entry);
        let recursive_sets = advanced_ai_collect_recursive_typeclass_solutions(
            env,
            goal_ctx,
            goal_universe_params,
            class_declarations,
            candidates,
            max_depth,
            max_nodes,
            current_depth + 1,
            node_count,
            &child_visited,
            &application.recursive_obligations,
        )?;
        if recursive_sets.len() != application.recursive_obligations.len() {
            continue;
        }
        let mut candidate_solutions = Vec::new();
        advanced_ai_build_typeclass_proofs(
            candidate,
            &application,
            &recursive_sets,
            0,
            &mut application.args.clone(),
            &mut candidate_solutions,
        );
        for proof in candidate_solutions {
            if env
                .check(goal_ctx, goal_universe_params, &proof, obligation)
                .is_err()
            {
                continue;
            }
            let key = advanced_ai_expr_canonical_bytes(&proof);
            solutions.entry(key).or_insert(proof);
            if solutions.len() > 1 {
                return Err(AdvancedTypeclassSearchStop::AmbiguousResolution);
            }
        }
    }
    Ok(solutions.into_values().collect())
}

#[allow(clippy::too_many_arguments)]
fn advanced_ai_collect_recursive_typeclass_solutions(
    env: &Env,
    goal_ctx: &Ctx,
    goal_universe_params: &[String],
    class_declarations: &BTreeSet<String>,
    candidates: &[AdvancedResolvedTypeclassCandidate],
    max_depth: u32,
    max_nodes: u32,
    current_depth: u32,
    node_count: &mut u32,
    visited: &[(Vec<u8>, Vec<u8>)],
    obligations: &[(usize, Expr)],
) -> std::result::Result<Vec<(usize, Vec<Expr>)>, AdvancedTypeclassSearchStop> {
    let mut recursive_sets = Vec::new();
    for (arg_index, obligation) in obligations {
        let proofs = advanced_ai_collect_typeclass_solutions(
            env,
            goal_ctx,
            goal_universe_params,
            obligation,
            class_declarations,
            candidates,
            max_depth,
            max_nodes,
            current_depth,
            node_count,
            visited,
        )?;
        if proofs.is_empty() {
            return Ok(Vec::new());
        }
        recursive_sets.push((*arg_index, proofs));
    }
    Ok(recursive_sets)
}

fn advanced_ai_build_typeclass_proofs(
    candidate: &AdvancedResolvedTypeclassCandidate,
    application: &AdvancedTypeclassCandidateApplication,
    recursive_sets: &[(usize, Vec<Expr>)],
    index: usize,
    args: &mut [Option<Expr>],
    proofs: &mut Vec<Expr>,
) {
    if index == recursive_sets.len() {
        let Some(final_args) = args.iter().cloned().collect::<Option<Vec<_>>>() else {
            return;
        };
        proofs.push(Expr::apps(
            Expr::konst(candidate.const_name.clone(), application.levels.clone()),
            final_args,
        ));
        return;
    }
    let (arg_index, choices) = &recursive_sets[index];
    for proof in choices {
        args[*arg_index] = Some(proof.clone());
        advanced_ai_build_typeclass_proofs(
            candidate,
            application,
            recursive_sets,
            index + 1,
            args,
            proofs,
        );
    }
    args[*arg_index] = None;
}

fn advanced_ai_try_typeclass_candidate(
    env: &Env,
    goal_ctx: &Ctx,
    goal_universe_params: &[String],
    obligation: &Expr,
    class_declarations: &BTreeSet<String>,
    candidate: &AdvancedResolvedTypeclassCandidate,
) -> std::result::Result<Option<AdvancedTypeclassCandidateApplication>, AdvancedTypeclassSearchStop>
{
    let obligation = env
        .whnf(goal_ctx, goal_universe_params, obligation)
        .map_err(|_| AdvancedTypeclassSearchStop::CandidateInterfaceInvalid)?;
    let mut universe_assignments = vec![None; candidate.universe_params.len()];
    let mut term_assignments = vec![None; candidate.telescope.len()];
    if !advanced_ai_match_typeclass_expr(
        &candidate.result,
        &obligation,
        candidate.telescope.len(),
        0,
        &candidate.universe_params,
        &mut universe_assignments,
        &mut term_assignments,
    )? {
        return Ok(None);
    }
    let Some(levels) = universe_assignments.into_iter().collect::<Option<Vec<_>>>() else {
        return Ok(None);
    };

    let mut args = vec![None; candidate.telescope.len()];
    let mut recursive_obligations = Vec::new();
    for index in 0..candidate.telescope.len() {
        let Some(binder_ty) = advanced_ai_instantiate_candidate_expr(
            &candidate.telescope[index],
            index,
            &candidate.universe_params,
            &levels,
            &term_assignments,
        )?
        else {
            return Ok(None);
        };
        if let Some(term) = &term_assignments[index] {
            if env
                .check(goal_ctx, goal_universe_params, term, &binder_ty)
                .is_err()
            {
                return Ok(None);
            }
            args[index] = Some(term.clone());
        } else if advanced_ai_typeclass_head_name(
            env,
            goal_ctx,
            goal_universe_params,
            &binder_ty,
            class_declarations,
        )
        .is_some()
        {
            recursive_obligations.push((index, binder_ty));
        } else {
            return Ok(None);
        }
    }

    Ok(Some(AdvancedTypeclassCandidateApplication {
        levels,
        args,
        recursive_obligations,
        fingerprint: advanced_ai_expr_canonical_bytes(&obligation),
    }))
}

fn advanced_ai_match_typeclass_expr(
    pattern: &Expr,
    target: &Expr,
    telescope_len: usize,
    local_depth: u32,
    universe_params: &[String],
    universe_assignments: &mut [Option<Level>],
    term_assignments: &mut [Option<Expr>],
) -> std::result::Result<bool, AdvancedTypeclassSearchStop> {
    match pattern {
        Expr::Sort(level) => match target {
            Expr::Sort(target_level) => advanced_ai_match_typeclass_level(
                level,
                target_level,
                universe_params,
                universe_assignments,
            ),
            _ => Ok(false),
        },
        Expr::BVar(index) => {
            let Some(pattern_index) =
                advanced_ai_candidate_bvar_to_pattern_index(*index, telescope_len, local_depth)
            else {
                return Err(AdvancedTypeclassSearchStop::CandidateInterfaceInvalid);
            };
            let assigned = &mut term_assignments[pattern_index];
            let target = if local_depth == 0 {
                target.clone()
            } else {
                npa_kernel::subst::shift(target, -(local_depth as i32), 0)
                    .map_err(|_| AdvancedTypeclassSearchStop::CandidateInterfaceInvalid)?
            };
            if let Some(existing) = assigned {
                Ok(advanced_ai_expr_canonical_bytes(existing)
                    == advanced_ai_expr_canonical_bytes(&target))
            } else {
                *assigned = Some(target);
                Ok(true)
            }
        }
        Expr::Const { name, levels } => match target {
            Expr::Const {
                name: target_name,
                levels: target_levels,
            } if name == target_name && levels.len() == target_levels.len() => {
                for (level, target_level) in levels.iter().zip(target_levels) {
                    if !advanced_ai_match_typeclass_level(
                        level,
                        target_level,
                        universe_params,
                        universe_assignments,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        },
        Expr::App(fun, arg) => match target {
            Expr::App(target_fun, target_arg) => Ok(advanced_ai_match_typeclass_expr(
                fun,
                target_fun,
                telescope_len,
                local_depth,
                universe_params,
                universe_assignments,
                term_assignments,
            )? && advanced_ai_match_typeclass_expr(
                arg,
                target_arg,
                telescope_len,
                local_depth,
                universe_params,
                universe_assignments,
                term_assignments,
            )?),
            _ => Ok(false),
        },
        Expr::Lam { ty, body, .. } => match target {
            Expr::Lam {
                ty: target_ty,
                body: target_body,
                ..
            } => Ok(advanced_ai_match_typeclass_expr(
                ty,
                target_ty,
                telescope_len,
                local_depth,
                universe_params,
                universe_assignments,
                term_assignments,
            )? && advanced_ai_match_typeclass_expr(
                body,
                target_body,
                telescope_len,
                local_depth + 1,
                universe_params,
                universe_assignments,
                term_assignments,
            )?),
            _ => Ok(false),
        },
        Expr::Pi { ty, body, .. } => match target {
            Expr::Pi {
                ty: target_ty,
                body: target_body,
                ..
            } => Ok(advanced_ai_match_typeclass_expr(
                ty,
                target_ty,
                telescope_len,
                local_depth,
                universe_params,
                universe_assignments,
                term_assignments,
            )? && advanced_ai_match_typeclass_expr(
                body,
                target_body,
                telescope_len,
                local_depth + 1,
                universe_params,
                universe_assignments,
                term_assignments,
            )?),
            _ => Ok(false),
        },
        Expr::Let { .. } => Ok(false),
    }
}

fn advanced_ai_match_typeclass_level(
    pattern: &Level,
    target: &Level,
    universe_params: &[String],
    universe_assignments: &mut [Option<Level>],
) -> std::result::Result<bool, AdvancedTypeclassSearchStop> {
    if let Level::Param(name) = pattern {
        if let Some(index) = universe_params.iter().position(|param| param == name) {
            if let Some(existing) = &universe_assignments[index] {
                return Ok(advanced_ai_level_canonical_bytes(existing)
                    == advanced_ai_level_canonical_bytes(target));
            }
            universe_assignments[index] = Some(target.clone());
            return Ok(true);
        }
    }
    match (pattern, target) {
        (Level::Zero, Level::Zero) => Ok(true),
        (Level::Succ(pattern), Level::Succ(target)) => advanced_ai_match_typeclass_level(
            pattern,
            target,
            universe_params,
            universe_assignments,
        ),
        (Level::Max(pattern_left, pattern_right), Level::Max(target_left, target_right))
        | (Level::IMax(pattern_left, pattern_right), Level::IMax(target_left, target_right)) => {
            Ok(advanced_ai_match_typeclass_level(
                pattern_left,
                target_left,
                universe_params,
                universe_assignments,
            )? && advanced_ai_match_typeclass_level(
                pattern_right,
                target_right,
                universe_params,
                universe_assignments,
            )?)
        }
        (Level::Param(lhs), Level::Param(rhs)) => Ok(lhs == rhs),
        _ => Ok(false),
    }
}

fn advanced_ai_instantiate_candidate_expr(
    expr: &Expr,
    candidate_context_len: usize,
    universe_params: &[String],
    levels: &[Level],
    term_assignments: &[Option<Expr>],
) -> std::result::Result<Option<Expr>, AdvancedTypeclassSearchStop> {
    let expr = npa_kernel::subst::subst_levels_expr(expr, universe_params, levels);
    advanced_ai_replace_candidate_bvars(&expr, candidate_context_len, 0, term_assignments)
}

fn advanced_ai_replace_candidate_bvars(
    expr: &Expr,
    candidate_context_len: usize,
    local_depth: u32,
    term_assignments: &[Option<Expr>],
) -> std::result::Result<Option<Expr>, AdvancedTypeclassSearchStop> {
    Ok(Some(match expr {
        Expr::Sort(level) => Expr::sort(level.clone()),
        Expr::BVar(index) if *index < local_depth => Expr::bvar(*index),
        Expr::BVar(index) => {
            let Some(pattern_index) = advanced_ai_candidate_bvar_to_pattern_index(
                *index,
                candidate_context_len,
                local_depth,
            ) else {
                return Err(AdvancedTypeclassSearchStop::CandidateInterfaceInvalid);
            };
            let Some(term) = &term_assignments[pattern_index] else {
                return Ok(None);
            };
            npa_kernel::subst::shift(term, local_depth as i32, 0)
                .map_err(|_| AdvancedTypeclassSearchStop::CandidateInterfaceInvalid)?
        }
        Expr::Const { name, levels } => Expr::konst(name.clone(), levels.clone()),
        Expr::App(fun, arg) => Expr::app(
            match advanced_ai_replace_candidate_bvars(
                fun,
                candidate_context_len,
                local_depth,
                term_assignments,
            )? {
                Some(fun) => fun,
                None => return Ok(None),
            },
            match advanced_ai_replace_candidate_bvars(
                arg,
                candidate_context_len,
                local_depth,
                term_assignments,
            )? {
                Some(arg) => arg,
                None => return Ok(None),
            },
        ),
        Expr::Lam { binder, ty, body } => Expr::lam(
            binder.clone(),
            match advanced_ai_replace_candidate_bvars(
                ty,
                candidate_context_len,
                local_depth,
                term_assignments,
            )? {
                Some(ty) => ty,
                None => return Ok(None),
            },
            match advanced_ai_replace_candidate_bvars(
                body,
                candidate_context_len,
                local_depth + 1,
                term_assignments,
            )? {
                Some(body) => body,
                None => return Ok(None),
            },
        ),
        Expr::Pi { binder, ty, body } => Expr::pi(
            binder.clone(),
            match advanced_ai_replace_candidate_bvars(
                ty,
                candidate_context_len,
                local_depth,
                term_assignments,
            )? {
                Some(ty) => ty,
                None => return Ok(None),
            },
            match advanced_ai_replace_candidate_bvars(
                body,
                candidate_context_len,
                local_depth + 1,
                term_assignments,
            )? {
                Some(body) => body,
                None => return Ok(None),
            },
        ),
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => Expr::let_in(
            binder.clone(),
            match advanced_ai_replace_candidate_bvars(
                ty,
                candidate_context_len,
                local_depth,
                term_assignments,
            )? {
                Some(ty) => ty,
                None => return Ok(None),
            },
            match advanced_ai_replace_candidate_bvars(
                value,
                candidate_context_len,
                local_depth,
                term_assignments,
            )? {
                Some(value) => value,
                None => return Ok(None),
            },
            match advanced_ai_replace_candidate_bvars(
                body,
                candidate_context_len,
                local_depth + 1,
                term_assignments,
            )? {
                Some(body) => body,
                None => return Ok(None),
            },
        ),
    }))
}

fn advanced_ai_candidate_expr_has_only_telescope_bvars(
    expr: &Expr,
    candidate_context_len: usize,
    local_depth: u32,
) -> bool {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => true,
        Expr::BVar(index) if *index < local_depth => true,
        Expr::BVar(index) => {
            advanced_ai_candidate_bvar_to_pattern_index(*index, candidate_context_len, local_depth)
                .is_some()
        }
        Expr::App(fun, arg) => {
            advanced_ai_candidate_expr_has_only_telescope_bvars(
                fun,
                candidate_context_len,
                local_depth,
            ) && advanced_ai_candidate_expr_has_only_telescope_bvars(
                arg,
                candidate_context_len,
                local_depth,
            )
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            advanced_ai_candidate_expr_has_only_telescope_bvars(
                ty,
                candidate_context_len,
                local_depth,
            ) && advanced_ai_candidate_expr_has_only_telescope_bvars(
                body,
                candidate_context_len,
                local_depth + 1,
            )
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            advanced_ai_candidate_expr_has_only_telescope_bvars(
                ty,
                candidate_context_len,
                local_depth,
            ) && advanced_ai_candidate_expr_has_only_telescope_bvars(
                value,
                candidate_context_len,
                local_depth,
            ) && advanced_ai_candidate_expr_has_only_telescope_bvars(
                body,
                candidate_context_len,
                local_depth + 1,
            )
        }
    }
}

fn advanced_ai_candidate_bvar_to_pattern_index(
    index: u32,
    candidate_context_len: usize,
    local_depth: u32,
) -> Option<usize> {
    if index < local_depth {
        return None;
    }
    let candidate_index_from_recent = usize::try_from(index - local_depth).ok()?;
    if candidate_index_from_recent >= candidate_context_len {
        return None;
    }
    Some(candidate_context_len - 1 - candidate_index_from_recent)
}

fn advanced_ai_expr_canonical_bytes(expr: &Expr) -> Vec<u8> {
    let mut out = Vec::new();
    encode_expr_to(&mut out, expr);
    out
}

fn advanced_ai_level_canonical_bytes(level: &Level) -> Vec<u8> {
    let mut out = Vec::new();
    encode_level_to(&mut out, level);
    out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AdvancedGoalValidationError {
    EnvelopeMalformed,
    ImportClosureMismatch,
    KernelRejected,
}

fn validate_advanced_ai_goal(
    goal: &AdvancedAiGoal,
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(), AdvancedGoalValidationError> {
    if !advanced_ai_string_list_is_unique(&goal.universe_params)
        || !expr_levels_are_in_scope(&goal.target, &goal.universe_params)
        || !goal
            .local_context
            .iter()
            .all(|local| local_decl_levels_are_in_scope(local, &goal.universe_params))
    {
        return Err(AdvancedGoalValidationError::EnvelopeMalformed);
    }
    if !goal_imported_refs_are_resolved(goal, verified_imports) {
        return Err(AdvancedGoalValidationError::ImportClosureMismatch);
    }
    validate_goal_kernel(goal, verified_imports)
        .map_err(|_| AdvancedGoalValidationError::KernelRejected)
}

fn smt_rejected_response(
    candidate_hash: Hash,
    error: AdvancedAiValidationError,
    smt_error: AdvancedSmtCertificateError,
) -> AdvancedAiEndpointResponse {
    rejected_response(
        candidate_hash,
        error,
        Some(AdvancedAiFeatureError::SmtCertificate(smt_error)),
    )
}

#[derive(Clone)]
struct AdvancedResolvedSmtPrimitives {
    eq: AdvancedResolvedGlobalDecl,
    prop_false: Option<AdvancedResolvedGlobalDecl>,
    prop_not: Option<AdvancedResolvedGlobalDecl>,
}

#[derive(Default)]
struct AdvancedSmtCommandContext {
    sort_arities: BTreeMap<Vec<u8>, u32>,
    functions: BTreeMap<Vec<u8>, (Vec<AdvancedSmtSortExpr>, AdvancedSmtSortExpr)>,
}

enum AdvancedValidatedSmtProofPayload {
    ProofNodeTable(AdvancedSmtProofNodeTable),
    Opaque {
        format: AdvancedSmtCertificateFormat,
        payload_hash: Hash,
        size_bytes: u64,
    },
    SolverResultOnly {
        payload_hash: Hash,
        size_bytes: u64,
    },
}

fn advanced_ai_smt_problem_bytes(
    candidate_hash: Hash,
    source: &AdvancedMachineSmtProblemRef,
    workspace_root: &Path,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    match source {
        AdvancedMachineSmtProblemRef::Inline {
            canonical_bytes, ..
        } => {
            if canonical_bytes.len() > MAX_ADVANCED_AI_SMT_RAW_BYTES {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            Ok(canonical_bytes.clone())
        }
        AdvancedMachineSmtProblemRef::Artifact {
            path,
            file_hash,
            size_bytes,
            ..
        } => advanced_ai_smt_artifact_bytes(
            candidate_hash,
            workspace_root,
            path,
            *file_hash,
            *size_bytes,
        ),
    }
}

fn advanced_ai_smt_payload_bytes(
    candidate_hash: Hash,
    source: &AdvancedMachineSmtProofPayloadRef,
    workspace_root: &Path,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    match source {
        AdvancedMachineSmtProofPayloadRef::Inline {
            canonical_bytes, ..
        } => {
            if canonical_bytes.len() > MAX_ADVANCED_AI_SMT_RAW_BYTES {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            Ok(canonical_bytes.clone())
        }
        AdvancedMachineSmtProofPayloadRef::Artifact {
            path,
            file_hash,
            size_bytes,
            ..
        } => advanced_ai_smt_artifact_bytes(
            candidate_hash,
            workspace_root,
            path,
            *file_hash,
            *size_bytes,
        ),
    }
}

fn advanced_ai_smt_artifact_bytes(
    candidate_hash: Hash,
    workspace_root: &Path,
    path: &str,
    file_hash: Hash,
    size_bytes: u64,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    if usize::try_from(size_bytes)
        .map(|size| size > MAX_ADVANCED_AI_SMT_RAW_BYTES)
        .unwrap_or(true)
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    let path = match validate_artifact_path(workspace_root, path) {
        Ok(path) => path,
        Err(ArtifactPathError::EnvelopeMalformed) => {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        Err(ArtifactPathError::ArtifactUnavailable) => {
            return Err(AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::ArtifactUnavailable,
            });
        }
    };
    let metadata = std::fs::metadata(&path).map_err(|_| AdvancedAiEndpointResponse::Error {
        error: AdvancedAiEndpointError::ArtifactUnavailable,
    })?;
    if metadata.len() != size_bytes {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    let bytes = std::fs::read(path).map_err(|_| AdvancedAiEndpointResponse::Error {
        error: AdvancedAiEndpointError::ArtifactUnavailable,
    })?;
    if advanced_ai_file_hash(&bytes) != file_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok(bytes)
}

fn advanced_ai_validate_smt_problem_bytes(
    candidate_hash: Hash,
    bytes: &[u8],
    candidate: &AdvancedMachineSmtCertificateCandidate,
) -> std::result::Result<AdvancedMachineSmtEncodedProblem, AdvancedAiEndpointResponse> {
    let problem = decode_smt_encoded_problem(bytes).map_err(|_| {
        smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        )
    })?;
    let declared_problem_hash = match &candidate.encoded_problem {
        AdvancedMachineSmtProblemRef::Inline { problem_hash, .. }
        | AdvancedMachineSmtProblemRef::Artifact { problem_hash, .. } => *problem_hash,
    };
    let declared_encoding_hash = match &candidate.encoded_problem {
        AdvancedMachineSmtProblemRef::Inline { encoding_hash, .. }
        | AdvancedMachineSmtProblemRef::Artifact { encoding_hash, .. } => *encoding_hash,
    };
    let problem_hash = advanced_ai_smt_problem_hash(&problem).map_err(|_| {
        smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        )
    })?;
    if problem_hash != declared_problem_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    if advanced_ai_smt_encoding_hash(&problem, problem_hash) != declared_encoding_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok(problem)
}

fn advanced_ai_validate_smt_proof_payload_bytes(
    candidate_hash: Hash,
    bytes: &[u8],
    candidate: &AdvancedMachineSmtCertificateCandidate,
) -> std::result::Result<AdvancedValidatedSmtProofPayload, AdvancedAiEndpointResponse> {
    let declared_hash = match &candidate.proof_payload {
        AdvancedMachineSmtProofPayloadRef::Inline { payload_hash, .. }
        | AdvancedMachineSmtProofPayloadRef::Artifact { payload_hash, .. } => *payload_hash,
    };
    match candidate.certificate_format {
        AdvancedSmtCertificateFormat::MvpProofNodeTableV1 => {
            let table = decode_smt_proof_node_table(bytes).map_err(|_| {
                smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::MalformedProofPayload,
                )
            })?;
            let payload_hash = advanced_ai_smt_proof_payload_hash(&table).map_err(|_| {
                smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::MalformedProofPayload,
                )
            })?;
            if payload_hash != declared_hash {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::PayloadHashMismatch,
                    None,
                ));
            }
            Ok(AdvancedValidatedSmtProofPayload::ProofNodeTable(table))
        }
        AdvancedSmtCertificateFormat::AletheOpaqueV1
        | AdvancedSmtCertificateFormat::LfscOpaqueV1 => {
            let payload_hash =
                advanced_ai_smt_opaque_proof_payload_hash(candidate.certificate_format, bytes)
                    .map_err(|_| {
                        smt_rejected_response(
                            candidate_hash,
                            AdvancedAiValidationError::EnvelopeMalformed,
                            AdvancedSmtCertificateError::MalformedProofPayload,
                        )
                    })?;
            if payload_hash != declared_hash {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::PayloadHashMismatch,
                    None,
                ));
            }
            Ok(AdvancedValidatedSmtProofPayload::Opaque {
                format: candidate.certificate_format,
                payload_hash,
                size_bytes: bytes.len() as u64,
            })
        }
        AdvancedSmtCertificateFormat::SolverResultOnlyV1 => {
            if bytes != b"unsat\n" {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::MalformedProofPayload,
                ));
            }
            let payload_hash =
                advanced_ai_smt_opaque_proof_payload_hash(candidate.certificate_format, bytes)
                    .map_err(|_| {
                        smt_rejected_response(
                            candidate_hash,
                            AdvancedAiValidationError::EnvelopeMalformed,
                            AdvancedSmtCertificateError::MalformedProofPayload,
                        )
                    })?;
            if payload_hash != declared_hash {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::PayloadHashMismatch,
                    None,
                ));
            }
            Ok(AdvancedValidatedSmtProofPayload::SolverResultOnly {
                payload_hash,
                size_bytes: bytes.len() as u64,
            })
        }
    }
}

fn advanced_ai_validate_smt_rule_registry_for_problem(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<AdvancedSmtSupportedFragment, AdvancedAiEndpointResponse> {
    if problem.logic != candidate.logic
        || problem.command_profile != AdvancedSmtCommandProfile::MvpNormalizedQf
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::EncodingMismatch,
        ));
    }
    let supported_fragment =
        advanced_ai_smt_classify_supported_fragment(problem).map_err(|error| {
            let (validation, smt) = match error {
                AdvancedSmtEncodingError::UnsupportedFragment => (
                    AdvancedAiValidationError::UnsupportedFeature,
                    AdvancedSmtCertificateError::UnsupportedFragment,
                ),
                AdvancedSmtEncodingError::NonCanonicalPayload => (
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ),
            };
            smt_rejected_response(candidate_hash, validation, smt)
        })?;
    let registry = advanced_ai_smt_rule_registry(candidate.rule_registry_profile);
    if !registry.descriptors.iter().any(|descriptor| {
        advanced_ai_smt_rule_descriptor_matches_problem(
            descriptor,
            candidate,
            problem,
            supported_fragment,
        )
    }) {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            AdvancedSmtCertificateError::RuleRegistryMismatch,
        ));
    }
    Ok(supported_fragment)
}

fn advanced_ai_smt_rule_descriptor_matches_problem(
    descriptor: &AdvancedSmtRuleDescriptor,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: &AdvancedMachineSmtEncodedProblem,
    supported_fragment: AdvancedSmtSupportedFragment,
) -> bool {
    descriptor.rule_registry_profile == candidate.rule_registry_profile
        && descriptor.certificate_format == candidate.certificate_format
        && descriptor.logic == candidate.logic
        && descriptor.logic == problem.logic
        && descriptor.command_profile == problem.command_profile
        && descriptor.supported_fragment == supported_fragment
}

fn advanced_ai_smt_rule_descriptor_for_fingerprint(
    profile: AdvancedSmtRuleRegistryProfile,
    rule_fingerprint: Hash,
) -> Option<AdvancedSmtRuleDescriptor> {
    advanced_ai_smt_rule_registry(profile)
        .descriptors
        .into_iter()
        .find(|descriptor| {
            advanced_ai_smt_rule_descriptor_fingerprint(descriptor) == rule_fingerprint
        })
}

fn advanced_ai_resolve_smt_primitives(
    candidate_hash: Hash,
    env: &Env,
    options: &AdvancedSmtOptions,
    imports: &[VerifiedImportRef],
) -> std::result::Result<AdvancedResolvedSmtPrimitives, AdvancedAiEndpointResponse> {
    let Some(eq) = advanced_ai_resolve_global_decl(&options.eq, imports) else {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        ));
    };
    let prop_false = match &options.prop_false {
        Some(global_ref) => Some(
            advanced_ai_resolve_global_decl(global_ref, imports).ok_or_else(|| {
                rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::ImportClosureMismatch,
                    None,
                )
            })?,
        ),
        None => None,
    };
    let prop_not = match &options.prop_not {
        Some(global_ref) => Some(
            advanced_ai_resolve_global_decl(global_ref, imports).ok_or_else(|| {
                rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::ImportClosureMismatch,
                    None,
                )
            })?,
        ),
        None => None,
    };
    let resolved = AdvancedResolvedSmtPrimitives {
        eq,
        prop_false,
        prop_not,
    };
    if !advanced_ai_smt_public_interface_is_valid(env, &resolved) {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::PublicInterfaceMismatch,
        ));
    }
    Ok(resolved)
}

fn advanced_ai_smt_public_interface_is_valid(
    env: &Env,
    resolved: &AdvancedResolvedSmtPrimitives,
) -> bool {
    advanced_ai_smt_eq_interface_is_valid(env, &resolved.eq)
        && resolved
            .prop_false
            .as_ref()
            .is_none_or(|prop_false| advanced_ai_smt_false_interface_is_valid(env, prop_false))
        && resolved
            .prop_not
            .as_ref()
            .is_none_or(|prop_not| advanced_ai_smt_not_interface_is_valid(env, prop_not))
}

fn advanced_ai_smt_eq_interface_is_valid(env: &Env, resolved: &AdvancedResolvedGlobalDecl) -> bool {
    let Some(universe) = advanced_ai_resolved_single_universe(resolved) else {
        return false;
    };
    let expected = Expr::pi(
        "_",
        Expr::sort(universe),
        Expr::pi(
            "_",
            Expr::bvar(0),
            Expr::pi("_", Expr::bvar(1), Expr::sort(Level::zero())),
        ),
    );
    advanced_ai_resolved_public_type_defeq(env, resolved, &expected)
}

fn advanced_ai_smt_false_interface_is_valid(
    env: &Env,
    resolved: &AdvancedResolvedGlobalDecl,
) -> bool {
    resolved.universe_params.is_empty()
        && advanced_ai_resolved_public_type_defeq(env, resolved, &Expr::sort(Level::zero()))
}

fn advanced_ai_smt_not_interface_is_valid(
    env: &Env,
    resolved: &AdvancedResolvedGlobalDecl,
) -> bool {
    resolved.universe_params.is_empty()
        && advanced_ai_resolved_public_type_defeq(
            env,
            resolved,
            &Expr::pi("_", Expr::sort(Level::zero()), Expr::sort(Level::zero())),
        )
}

fn advanced_ai_validate_smt_commands(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: &AdvancedMachineSmtEncodedProblem,
    primitives: &AdvancedResolvedSmtPrimitives,
) -> std::result::Result<AdvancedSmtCommandContext, AdvancedAiEndpointResponse> {
    if problem.encoder_version != AdvancedSmtEncoderVersion::MvpNormalizedQfV1
        || problem.command_profile != AdvancedSmtCommandProfile::MvpNormalizedQf
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::EncodingMismatch,
        ));
    }
    for command in &problem.commands {
        let expected = advanced_ai_smt_command_id(command).map_err(|_| {
            smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            )
        })?;
        if command.command_id != expected {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::PayloadHashMismatch,
                None,
            ));
        }
    }

    let mut context = AdvancedSmtCommandContext::default();
    let mut previous_key: Option<Vec<u8>> = None;
    let mut target_assertions = 0usize;
    let mut final_checks = 0usize;
    for command in &problem.commands {
        if !advanced_ai_smt_command_phase_matches_payload(command.phase, &command.payload) {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        let key = advanced_ai_smt_command_order_key(command).map_err(|_| {
            smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            )
        })?;
        if previous_key
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        previous_key = Some(key);

        match &command.payload {
            AdvancedSmtCommandPayload::SortDecl { symbol, arity } => {
                if !advanced_ai_smt_decl_symbol_is_valid(symbol) {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        AdvancedSmtCertificateError::NonCanonicalPayload,
                    ));
                }
                if context
                    .sort_arities
                    .insert(symbol.ascii.clone(), *arity)
                    .is_some()
                {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        AdvancedSmtCertificateError::NonCanonicalPayload,
                    ));
                }
            }
            AdvancedSmtCommandPayload::DatatypeDecl {
                symbol,
                constructors,
            } => {
                if !advanced_ai_smt_decl_symbol_is_valid(symbol) || constructors.is_empty() {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        AdvancedSmtCertificateError::NonCanonicalPayload,
                    ));
                }
                for constructor in constructors {
                    if !advanced_ai_smt_decl_symbol_is_valid(&constructor.constructor) {
                        return Err(smt_rejected_response(
                            candidate_hash,
                            AdvancedAiValidationError::EnvelopeMalformed,
                            AdvancedSmtCertificateError::NonCanonicalPayload,
                        ));
                    }
                    for selector in &constructor.selectors {
                        if !advanced_ai_smt_decl_symbol_is_valid(&selector.selector) {
                            return Err(smt_rejected_response(
                                candidate_hash,
                                AdvancedAiValidationError::EnvelopeMalformed,
                                AdvancedSmtCertificateError::NonCanonicalPayload,
                            ));
                        }
                        advanced_ai_validate_smt_sort(
                            candidate_hash,
                            &selector.sort,
                            problem.logic,
                            &context,
                        )?;
                    }
                }
                context.sort_arities.insert(symbol.ascii.clone(), 0);
            }
            AdvancedSmtCommandPayload::FunctionDecl {
                symbol,
                args,
                result,
            } => {
                if !advanced_ai_smt_decl_symbol_is_valid(symbol) {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        AdvancedSmtCertificateError::NonCanonicalPayload,
                    ));
                }
                for arg in args {
                    advanced_ai_validate_smt_sort(candidate_hash, arg, problem.logic, &context)?;
                }
                advanced_ai_validate_smt_sort(candidate_hash, result, problem.logic, &context)?;
                if context
                    .functions
                    .insert(symbol.ascii.clone(), (args.clone(), result.clone()))
                    .is_some()
                {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        AdvancedSmtCertificateError::NonCanonicalPayload,
                    ));
                }
            }
            AdvancedSmtCommandPayload::ContextAssumption {
                source_local_index,
                core_expr,
                encoded_expr,
            } => {
                let Some(local) = candidate
                    .goal
                    .local_context
                    .get(usize::try_from(*source_local_index).unwrap_or(usize::MAX))
                else {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::EnvelopeMalformed,
                        AdvancedSmtCertificateError::NonCanonicalPayload,
                    ));
                };
                if !advanced_ai_core_expr_bytes_eq(&local.ty, core_expr) {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::FeatureRejected,
                        AdvancedSmtCertificateError::EncodingMismatch,
                    ));
                }
                let expected = advanced_ai_smt_encode_core_bool(core_expr, primitives, false)
                    .ok_or_else(|| {
                        rejected_response(
                            candidate_hash,
                            AdvancedAiValidationError::UnsupportedFeature,
                            None,
                        )
                    })?;
                if &expected != encoded_expr {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::FeatureRejected,
                        AdvancedSmtCertificateError::EncodingMismatch,
                    ));
                }
                advanced_ai_validate_smt_expr(
                    candidate_hash,
                    encoded_expr,
                    problem.logic,
                    &context,
                )?;
            }
            AdvancedSmtCommandPayload::TargetAssertion {
                core_expr,
                encoded_expr,
            } => {
                target_assertions += 1;
                if !advanced_ai_core_expr_bytes_eq(&candidate.goal.target, core_expr) {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::FeatureRejected,
                        AdvancedSmtCertificateError::EncodingMismatch,
                    ));
                }
                let expected = advanced_ai_smt_encode_core_bool(core_expr, primitives, true)
                    .ok_or_else(|| {
                        rejected_response(
                            candidate_hash,
                            AdvancedAiValidationError::UnsupportedFeature,
                            None,
                        )
                    })?;
                if &expected != encoded_expr {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::FeatureRejected,
                        AdvancedSmtCertificateError::EncodingMismatch,
                    ));
                }
                advanced_ai_validate_smt_expr(
                    candidate_hash,
                    encoded_expr,
                    problem.logic,
                    &context,
                )?;
            }
            AdvancedSmtCommandPayload::FinalCheck => {
                final_checks += 1;
            }
        }
    }
    if target_assertions != 1
        || final_checks != 1
        || !matches!(
            problem.commands.last().map(|command| command.phase),
            Some(AdvancedSmtCommandPhase::FinalCheck)
        )
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    Ok(context)
}

fn advanced_ai_smt_command_phase_matches_payload(
    phase: AdvancedSmtCommandPhase,
    payload: &AdvancedSmtCommandPayload,
) -> bool {
    matches!(
        (phase, payload),
        (
            AdvancedSmtCommandPhase::SortDecl,
            AdvancedSmtCommandPayload::SortDecl { .. }
        ) | (
            AdvancedSmtCommandPhase::DatatypeDecl,
            AdvancedSmtCommandPayload::DatatypeDecl { .. }
        ) | (
            AdvancedSmtCommandPhase::FunctionDecl,
            AdvancedSmtCommandPayload::FunctionDecl { .. }
        ) | (
            AdvancedSmtCommandPhase::ContextAssumption,
            AdvancedSmtCommandPayload::ContextAssumption { .. }
        ) | (
            AdvancedSmtCommandPhase::TargetAssertion,
            AdvancedSmtCommandPayload::TargetAssertion { .. }
        ) | (
            AdvancedSmtCommandPhase::FinalCheck,
            AdvancedSmtCommandPayload::FinalCheck
        )
    )
}

fn advanced_ai_smt_command_order_key(
    command: &AdvancedSmtEncodedCommand,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut key = vec![command.phase.tag()];
    key.extend_from_slice(&advanced_ai_smt_command_id_source_key(&command.payload)?);
    Ok(key)
}

fn advanced_ai_smt_decl_symbol_is_valid(symbol: &AdvancedSmtSymbol) -> bool {
    symbol.ascii.starts_with(b"smt:")
        && symbol.ascii.len() <= 128
        && symbol.ascii.len() > 4
        && symbol.ascii[4..]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(*byte, b'_' | b'.' | b'-'))
}

fn advanced_ai_smt_var_symbol_is_valid(symbol: &AdvancedSmtSymbol) -> bool {
    symbol.ascii.starts_with(b"lc:")
        && symbol.ascii.len() <= 128
        && symbol.ascii.len() > 3
        && symbol.ascii[3..]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(*byte, b'_' | b'.' | b'-'))
}

fn advanced_ai_smt_encode_core_bool(
    expr: &Expr,
    primitives: &AdvancedResolvedSmtPrimitives,
    negate: bool,
) -> Option<AdvancedSmtExpr> {
    let mut encoded = if primitives
        .prop_false
        .as_ref()
        .is_some_and(|false_ref| advanced_ai_core_expr_is_const(expr, &false_ref.const_name))
    {
        AdvancedSmtExpr::BoolLit(false)
    } else if let Some(prop_not) = &primitives.prop_not {
        let (head, args) = npa_kernel::expr::collect_apps(expr);
        if let Expr::Const { name, levels } = head {
            if name == prop_not.const_name && levels.is_empty() && args.len() == 1 {
                AdvancedSmtExpr::Not(Box::new(advanced_ai_smt_encode_core_bool(
                    &args[0], primitives, false,
                )?))
            } else {
                return None;
            }
        } else {
            return None;
        }
    } else {
        return None;
    };
    if negate {
        encoded = AdvancedSmtExpr::Not(Box::new(encoded));
    }
    Some(encoded)
}

fn advanced_ai_core_expr_is_const(expr: &Expr, expected_name: &str) -> bool {
    matches!(expr, Expr::Const { name, levels } if name == expected_name && levels.is_empty())
}

fn advanced_ai_validate_smt_sort(
    candidate_hash: Hash,
    sort: &AdvancedSmtSortExpr,
    logic: AdvancedSmtLogic,
    context: &AdvancedSmtCommandContext,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    match sort {
        AdvancedSmtSortExpr::Bool => Ok(()),
        AdvancedSmtSortExpr::Int => {
            if matches!(
                logic,
                AdvancedSmtLogic::MvpQfLia | AdvancedSmtLogic::MvpQfUfLiaBv
            ) {
                Ok(())
            } else {
                Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::UnsupportedFeature,
                    AdvancedSmtCertificateError::UnsupportedFragment,
                ))
            }
        }
        AdvancedSmtSortExpr::BitVec { width } => {
            if *width == 0 {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            if matches!(
                logic,
                AdvancedSmtLogic::MvpQfBv | AdvancedSmtLogic::MvpQfUfLiaBv
            ) {
                Ok(())
            } else {
                Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::UnsupportedFeature,
                    AdvancedSmtCertificateError::UnsupportedFragment,
                ))
            }
        }
        AdvancedSmtSortExpr::User { symbol, args } => {
            let Some(arity) = context.sort_arities.get(&symbol.ascii) else {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            };
            if *arity != args.len() as u32 {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            for arg in args {
                advanced_ai_validate_smt_sort(candidate_hash, arg, logic, context)?;
            }
            Ok(())
        }
    }
}

fn advanced_ai_validate_smt_expr(
    candidate_hash: Hash,
    expr: &AdvancedSmtExpr,
    logic: AdvancedSmtLogic,
    context: &AdvancedSmtCommandContext,
) -> std::result::Result<AdvancedSmtSortExpr, AdvancedAiEndpointResponse> {
    match expr {
        AdvancedSmtExpr::Var { symbol, sort } => {
            if !advanced_ai_smt_var_symbol_is_valid(symbol) {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            advanced_ai_validate_smt_sort(candidate_hash, sort, logic, context)?;
            Ok(sort.clone())
        }
        AdvancedSmtExpr::BoolLit(_) => Ok(AdvancedSmtSortExpr::Bool),
        AdvancedSmtExpr::IntLit(_) => {
            advanced_ai_validate_smt_sort(
                candidate_hash,
                &AdvancedSmtSortExpr::Int,
                logic,
                context,
            )?;
            Ok(AdvancedSmtSortExpr::Int)
        }
        AdvancedSmtExpr::BitVecLit { width, value } => {
            let sort = AdvancedSmtSortExpr::BitVec { width: *width };
            advanced_ai_validate_smt_sort(candidate_hash, &sort, logic, context)?;
            let min_bytes = usize::try_from(u64::from(*width).div_ceil(8)).unwrap_or(usize::MAX);
            if value.len() != min_bytes {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            Ok(sort)
        }
        AdvancedSmtExpr::App {
            symbol,
            args,
            result_sort,
        } => {
            let Some((expected_args, expected_result)) = context.functions.get(&symbol.ascii)
            else {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            };
            if expected_args.len() != args.len() || expected_result != result_sort {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            for (arg, expected_sort) in args.iter().zip(expected_args) {
                let actual_sort =
                    advanced_ai_validate_smt_expr(candidate_hash, arg, logic, context)?;
                if &actual_sort != expected_sort {
                    return Err(smt_rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::FeatureRejected,
                        AdvancedSmtCertificateError::EncodingMismatch,
                    ));
                }
            }
            advanced_ai_validate_smt_sort(candidate_hash, result_sort, logic, context)?;
            Ok(result_sort.clone())
        }
        AdvancedSmtExpr::BuiltinApp {
            op,
            args,
            result_sort,
        } => advanced_ai_validate_smt_builtin_app(
            candidate_hash,
            *op,
            args,
            result_sort,
            logic,
            context,
        ),
        AdvancedSmtExpr::Not(inner) => {
            advanced_ai_expect_smt_sort(
                candidate_hash,
                advanced_ai_validate_smt_expr(candidate_hash, inner, logic, context)?,
                AdvancedSmtSortExpr::Bool,
            )?;
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::And(args) | AdvancedSmtExpr::Or(args) => {
            if args.is_empty() {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            for arg in args {
                advanced_ai_expect_smt_sort(
                    candidate_hash,
                    advanced_ai_validate_smt_expr(candidate_hash, arg, logic, context)?,
                    AdvancedSmtSortExpr::Bool,
                )?;
            }
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::Eq(lhs, rhs) => {
            let lhs_sort = advanced_ai_validate_smt_expr(candidate_hash, lhs, logic, context)?;
            let rhs_sort = advanced_ai_validate_smt_expr(candidate_hash, rhs, logic, context)?;
            advanced_ai_expect_smt_sort(candidate_hash, lhs_sort, rhs_sort)?;
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::Imp(lhs, rhs) => {
            advanced_ai_expect_smt_sort(
                candidate_hash,
                advanced_ai_validate_smt_expr(candidate_hash, lhs, logic, context)?,
                AdvancedSmtSortExpr::Bool,
            )?;
            advanced_ai_expect_smt_sort(
                candidate_hash,
                advanced_ai_validate_smt_expr(candidate_hash, rhs, logic, context)?,
                AdvancedSmtSortExpr::Bool,
            )?;
            Ok(AdvancedSmtSortExpr::Bool)
        }
        AdvancedSmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            advanced_ai_expect_smt_sort(
                candidate_hash,
                advanced_ai_validate_smt_expr(candidate_hash, cond, logic, context)?,
                AdvancedSmtSortExpr::Bool,
            )?;
            let then_sort =
                advanced_ai_validate_smt_expr(candidate_hash, then_expr, logic, context)?;
            let else_sort =
                advanced_ai_validate_smt_expr(candidate_hash, else_expr, logic, context)?;
            advanced_ai_expect_smt_sort(candidate_hash, then_sort.clone(), else_sort)?;
            Ok(then_sort)
        }
    }
}

fn advanced_ai_validate_smt_builtin_app(
    candidate_hash: Hash,
    op: AdvancedSmtBuiltinOp,
    args: &[AdvancedSmtExpr],
    result_sort: &AdvancedSmtSortExpr,
    logic: AdvancedSmtLogic,
    context: &AdvancedSmtCommandContext,
) -> std::result::Result<AdvancedSmtSortExpr, AdvancedAiEndpointResponse> {
    let int = AdvancedSmtSortExpr::Int;
    let bool_sort = AdvancedSmtSortExpr::Bool;
    let expected = match op {
        AdvancedSmtBuiltinOp::IntNeg => {
            advanced_ai_expect_smt_arity(candidate_hash, args, 1)?;
            vec![int.clone()]
        }
        AdvancedSmtBuiltinOp::IntAdd | AdvancedSmtBuiltinOp::IntSub => {
            advanced_ai_expect_smt_arity(candidate_hash, args, 2)?;
            vec![int.clone(), int.clone()]
        }
        AdvancedSmtBuiltinOp::IntLe
        | AdvancedSmtBuiltinOp::IntLt
        | AdvancedSmtBuiltinOp::IntGe
        | AdvancedSmtBuiltinOp::IntGt => {
            advanced_ai_expect_smt_arity(candidate_hash, args, 2)?;
            vec![int.clone(), int.clone()]
        }
        AdvancedSmtBuiltinOp::BvNot => {
            advanced_ai_expect_smt_arity(candidate_hash, args, 1)?;
            Vec::new()
        }
        AdvancedSmtBuiltinOp::BvAnd
        | AdvancedSmtBuiltinOp::BvOr
        | AdvancedSmtBuiltinOp::BvXor
        | AdvancedSmtBuiltinOp::BvAdd
        | AdvancedSmtBuiltinOp::BvSub
        | AdvancedSmtBuiltinOp::BvMul
        | AdvancedSmtBuiltinOp::BvUlt
        | AdvancedSmtBuiltinOp::BvUle
        | AdvancedSmtBuiltinOp::BvConcat => {
            advanced_ai_expect_smt_arity(candidate_hash, args, 2)?;
            Vec::new()
        }
        AdvancedSmtBuiltinOp::BvExtract { high, low } => {
            advanced_ai_expect_smt_arity(candidate_hash, args, 1)?;
            if high < low {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                ));
            }
            Vec::new()
        }
    };

    match op {
        AdvancedSmtBuiltinOp::IntNeg
        | AdvancedSmtBuiltinOp::IntAdd
        | AdvancedSmtBuiltinOp::IntSub
        | AdvancedSmtBuiltinOp::IntLe
        | AdvancedSmtBuiltinOp::IntLt
        | AdvancedSmtBuiltinOp::IntGe
        | AdvancedSmtBuiltinOp::IntGt => {
            advanced_ai_validate_smt_sort(candidate_hash, &int, logic, context)?;
            for (arg, sort) in args.iter().zip(expected) {
                advanced_ai_expect_smt_sort(
                    candidate_hash,
                    advanced_ai_validate_smt_expr(candidate_hash, arg, logic, context)?,
                    sort,
                )?;
            }
            let result = match op {
                AdvancedSmtBuiltinOp::IntNeg
                | AdvancedSmtBuiltinOp::IntAdd
                | AdvancedSmtBuiltinOp::IntSub => int,
                _ => bool_sort,
            };
            advanced_ai_expect_smt_sort(candidate_hash, result_sort.clone(), result.clone())?;
            Ok(result)
        }
        _ => {
            if !matches!(
                logic,
                AdvancedSmtLogic::MvpQfBv | AdvancedSmtLogic::MvpQfUfLiaBv
            ) {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::UnsupportedFeature,
                    AdvancedSmtCertificateError::UnsupportedFragment,
                ));
            }
            let arg_sorts = args
                .iter()
                .map(|arg| advanced_ai_validate_smt_expr(candidate_hash, arg, logic, context))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            if !arg_sorts
                .iter()
                .all(|sort| matches!(sort, AdvancedSmtSortExpr::BitVec { width } if *width > 0))
            {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    AdvancedSmtCertificateError::EncodingMismatch,
                ));
            }
            let result = match op {
                AdvancedSmtBuiltinOp::BvUlt | AdvancedSmtBuiltinOp::BvUle => {
                    AdvancedSmtSortExpr::Bool
                }
                AdvancedSmtBuiltinOp::BvConcat => {
                    let AdvancedSmtSortExpr::BitVec { width: left } = arg_sorts[0] else {
                        unreachable!()
                    };
                    let AdvancedSmtSortExpr::BitVec { width: right } = arg_sorts[1] else {
                        unreachable!()
                    };
                    AdvancedSmtSortExpr::BitVec {
                        width: left.checked_add(right).ok_or_else(|| {
                            smt_rejected_response(
                                candidate_hash,
                                AdvancedAiValidationError::EnvelopeMalformed,
                                AdvancedSmtCertificateError::NonCanonicalPayload,
                            )
                        })?,
                    }
                }
                AdvancedSmtBuiltinOp::BvExtract { high, low } => {
                    let width = high
                        .checked_sub(low)
                        .and_then(|width| width.checked_add(1))
                        .ok_or_else(|| {
                            smt_rejected_response(
                                candidate_hash,
                                AdvancedAiValidationError::EnvelopeMalformed,
                                AdvancedSmtCertificateError::NonCanonicalPayload,
                            )
                        })?;
                    AdvancedSmtSortExpr::BitVec { width }
                }
                _ => arg_sorts[0].clone(),
            };
            advanced_ai_expect_smt_sort(candidate_hash, result_sort.clone(), result.clone())?;
            Ok(result)
        }
    }
}

fn advanced_ai_expect_smt_arity(
    candidate_hash: Hash,
    args: &[AdvancedSmtExpr],
    expected: usize,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ))
    }
}

fn advanced_ai_expect_smt_sort(
    candidate_hash: Hash,
    actual: AdvancedSmtSortExpr,
    expected: AdvancedSmtSortExpr,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    if actual == expected {
        Ok(())
    } else {
        Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::EncodingMismatch,
        ))
    }
}

fn advanced_ai_validate_smt_proof_table(
    candidate_hash: Hash,
    table: &AdvancedSmtProofNodeTable,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: &AdvancedMachineSmtEncodedProblem,
    command_context: &AdvancedSmtCommandContext,
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    if table.certificate_format != candidate.certificate_format {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::EncodingMismatch,
        ));
    }
    for (index, node) in table.nodes.iter().enumerate() {
        if node.node_id != index as u32
            || node.premises.iter().any(|premise| *premise >= node.node_id)
        {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        let conclusion = &node.conclusion_encoding;
        if conclusion.encoder_version != problem.encoder_version
            || conclusion.logic != problem.logic
            || conclusion.command_profile != problem.command_profile
        {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                AdvancedSmtCertificateError::ConclusionEncodingMismatch,
            ));
        }
        if !expr_levels_are_in_scope(&conclusion.core_expr, &candidate.goal.universe_params) {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        if !expr_imported_refs_are_resolved(&conclusion.core_expr, verified_imports) {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            ));
        }
        advanced_ai_validate_smt_expr(
            candidate_hash,
            &conclusion.encoded_expr,
            problem.logic,
            command_context,
        )?;
    }
    Ok(())
}

fn advanced_ai_validate_smt_reconstruction_plan(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let plan = &candidate.reconstruction_plan;
    if ensure_sorted_global_refs(&plan.imported_theory_refs).is_err() {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    if plan.steps.is_empty()
        || usize::try_from(plan.final_step).map_or(true, |i| i >= plan.steps.len())
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    let mut used_theory_refs = BTreeSet::new();
    for (index, step) in plan.steps.iter().enumerate() {
        if step.step_id != index as u32
            || step.premises.iter().any(|premise| *premise >= step.step_id)
        {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        if !expr_levels_are_in_scope(&step.conclusion, &candidate.goal.universe_params)
            || !expr_levels_are_in_scope(&step.proof, &candidate.goal.universe_params)
        {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
        if !expr_imported_refs_are_resolved(&step.conclusion, verified_imports)
            || !expr_imported_refs_are_resolved(&step.proof, verified_imports)
        {
            return Err(rejected_response(
                candidate_hash,
                AdvancedAiValidationError::ImportClosureMismatch,
                None,
            ));
        }
        if let AdvancedSmtReconstructionRule::LocalBookkeeping { kind } = &step.rule {
            let theory_ref = match kind {
                AdvancedSmtLocalBookkeepingRule::ReorderPremises { permutation } => {
                    if permutation.len() != step.premises.len() {
                        return Err(smt_rejected_response(
                            candidate_hash,
                            AdvancedAiValidationError::EnvelopeMalformed,
                            AdvancedSmtCertificateError::NonCanonicalPayload,
                        ));
                    }
                    return Err(rejected_response(
                        candidate_hash,
                        AdvancedAiValidationError::UnsupportedFeature,
                        None,
                    ));
                }
                AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
                    lemma,
                    level_args,
                    term_args,
                } => {
                    if step.premises.is_empty() {
                        advanced_ai_validate_smt_bookkeeping_args(
                            candidate_hash,
                            candidate,
                            level_args,
                            term_args,
                            verified_imports,
                        )?;
                    }
                    lemma
                }
                AdvancedSmtLocalBookkeepingRule::ComposeProof {
                    combinator,
                    level_args,
                    term_args,
                } => {
                    advanced_ai_validate_smt_bookkeeping_args(
                        candidate_hash,
                        candidate,
                        level_args,
                        term_args,
                        verified_imports,
                    )?;
                    combinator
                }
            };
            used_theory_refs.insert(global_ref_sort_key(theory_ref).map_err(|_| {
                smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedSmtCertificateError::NonCanonicalPayload,
                )
            })?);
            if !plan
                .imported_theory_refs
                .iter()
                .any(|imported| imported == theory_ref)
            {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    AdvancedSmtCertificateError::TheoryRefMismatch,
                ));
            }
            if resolve_advanced_ai_global_ref(theory_ref, verified_imports).is_none() {
                return Err(rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::ImportClosureMismatch,
                    None,
                ));
            }
            if !step.payload_bindings.is_empty() {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    AdvancedSmtCertificateError::PayloadBindingMismatch,
                ));
            }
            if matches!(
                kind,
                AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma { .. }
            ) && !step.premises.is_empty()
            {
                return Err(smt_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::FeatureRejected,
                    AdvancedSmtCertificateError::ReconstructionPremiseMismatch,
                ));
            }
        }
    }
    if !expr_levels_are_in_scope(&plan.final_proof, &candidate.goal.universe_params) {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    if !expr_imported_refs_are_resolved(&plan.final_proof, verified_imports) {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        ));
    }
    for imported in &plan.imported_theory_refs {
        let key = global_ref_sort_key(imported).map_err(|_| {
            smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            )
        })?;
        if !used_theory_refs.contains(&key) {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                AdvancedSmtCertificateError::NonCanonicalPayload,
            ));
        }
    }
    Ok(())
}

fn advanced_ai_reconstruct_smt_final_proof(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    proof_payload: &AdvancedValidatedSmtProofPayload,
    supported_fragment: AdvancedSmtSupportedFragment,
    env: &Env,
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<Expr, AdvancedAiEndpointResponse> {
    let has_payload_node = candidate
        .reconstruction_plan
        .steps
        .iter()
        .any(|step| matches!(step.rule, AdvancedSmtReconstructionRule::PayloadNode { .. }));
    if candidate.rule_registry_profile == AdvancedSmtRuleRegistryProfile::MvpEmptyRegistryV1 {
        return Err(if has_payload_node {
            smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::UnsupportedFeature,
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )
        } else {
            rejected_response(
                candidate_hash,
                AdvancedAiValidationError::UnsupportedFeature,
                None,
            )
        });
    }
    if !has_payload_node {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            None,
        ));
    }

    let AdvancedValidatedSmtProofPayload::ProofNodeTable(table) = proof_payload else {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            AdvancedSmtCertificateError::RuleRegistryMismatch,
        ));
    };

    let payload_hash = advanced_ai_smt_declared_payload_hash(candidate);
    let ctx = advanced_ai_goal_ctx(&candidate.goal);
    let mut accepted_payload_node_by_step = BTreeMap::new();
    for step in &candidate.reconstruction_plan.steps {
        if let AdvancedSmtReconstructionRule::PayloadNode {
            certificate_format,
            rule_fingerprint,
        } = &step.rule
        {
            advanced_ai_check_smt_payload_node_step(
                candidate_hash,
                candidate,
                table,
                payload_hash,
                env,
                &ctx,
                &accepted_payload_node_by_step,
                step,
                *certificate_format,
                *rule_fingerprint,
                supported_fragment,
            )?;
            let binding = step
                .payload_bindings
                .first()
                .expect("payload node binding was validated above");
            accepted_payload_node_by_step.insert(step.step_id, binding.node_id);
        }

        if env
            .check(
                &ctx,
                &candidate.goal.universe_params,
                &step.proof,
                &step.conclusion,
            )
            .is_err()
        {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::FeatureRejected,
                AdvancedSmtCertificateError::ReconstructionProofMismatch,
            ));
        }
    }

    let final_step =
        &candidate.reconstruction_plan.steps[candidate.reconstruction_plan.final_step as usize];
    if env
        .is_defeq(
            &ctx,
            &candidate.goal.universe_params,
            &final_step.conclusion,
            &candidate.goal.target,
        )
        .map_or(true, |defeq| !defeq)
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::ReconstructionConclusionMismatch,
        ));
    }
    if !advanced_ai_core_expr_bytes_eq(
        &candidate.reconstruction_plan.final_proof,
        &final_step.proof,
    ) {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::ReconstructionProofMismatch,
        ));
    }
    advanced_ai_check_smt_final_proof_certificate(
        candidate_hash,
        candidate,
        env,
        verified_imports,
        &candidate.reconstruction_plan.final_proof,
    )?;
    Ok(candidate.reconstruction_plan.final_proof.clone())
}

#[allow(clippy::too_many_arguments)]
fn advanced_ai_check_smt_payload_node_step(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    table: &AdvancedSmtProofNodeTable,
    payload_hash: Hash,
    env: &Env,
    ctx: &Ctx,
    accepted_payload_node_by_step: &BTreeMap<u32, u32>,
    step: &AdvancedMachineSmtReconstructionStep,
    certificate_format: AdvancedSmtCertificateFormat,
    rule_fingerprint: Hash,
    supported_fragment: AdvancedSmtSupportedFragment,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let Some(descriptor) = advanced_ai_smt_rule_descriptor_for_fingerprint(
        candidate.rule_registry_profile,
        rule_fingerprint,
    ) else {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            AdvancedSmtCertificateError::RuleRegistryMismatch,
        ));
    };
    if descriptor.certificate_format != certificate_format
        || certificate_format != candidate.certificate_format
        || descriptor.logic != candidate.logic
        || descriptor.command_profile != AdvancedSmtCommandProfile::MvpNormalizedQf
        || descriptor.supported_fragment != supported_fragment
        || descriptor.kind != AdvancedSmtRuleDescriptorKind::MvpKernelCheckedPayloadNodeV1
        || descriptor.checker_profile != AdvancedSmtCheckerProfile::KernelCheckedPayloadNodeV1
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            AdvancedSmtCertificateError::RuleRegistryMismatch,
        ));
    }
    if step.payload_bindings.is_empty() {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::PayloadBindingMismatch,
        ));
    }
    if step
        .payload_bindings
        .iter()
        .any(|binding| binding.payload_hash != payload_hash)
    {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    let [binding] = step.payload_bindings.as_slice() else {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::UnsupportedFeature,
            AdvancedSmtCertificateError::PayloadBindingMismatch,
        ));
    };
    if binding.rule_fingerprint != rule_fingerprint {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::PayloadBindingMismatch,
        ));
    }
    let Some(node) = table.nodes.get(binding.node_id as usize) else {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::PayloadBindingMismatch,
        ));
    };
    if node.node_id != binding.node_id {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    if node.rule_fingerprint != rule_fingerprint {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::PayloadBindingMismatch,
        ));
    }
    let expected_premises = step
        .premises
        .iter()
        .map(|premise_step| accepted_payload_node_by_step.get(premise_step).copied())
        .collect::<Option<Vec<_>>>();
    if expected_premises.as_deref() != Some(node.premises.as_slice()) {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::ReconstructionPremiseMismatch,
        ));
    }
    if env
        .is_defeq(
            ctx,
            &candidate.goal.universe_params,
            &node.conclusion_encoding.core_expr,
            &step.conclusion,
        )
        .map_or(true, |defeq| !defeq)
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedSmtCertificateError::ReconstructionConclusionMismatch,
        ));
    }
    Ok(())
}

fn advanced_ai_check_smt_final_proof_certificate(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    env: &Env,
    verified_imports: &[VerifiedImportRef],
    final_proof: &Expr,
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    let ctx = advanced_ai_goal_ctx(&candidate.goal);
    if env
        .check(
            &ctx,
            &candidate.goal.universe_params,
            final_proof,
            &candidate.goal.target,
        )
        .is_err()
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::KernelRejected,
            AdvancedSmtCertificateError::ReconstructionProofMismatch,
        ));
    }

    let (closed_type, closed_proof) =
        advanced_ai_close_smt_goal_for_certificate(&candidate.goal, final_proof);
    let module = advanced_ai_smt_scratch_module(candidate_hash);
    let theorem_name = advanced_ai_smt_scratch_theorem(candidate_hash).as_dotted();
    let import_modules = verified_imports
        .iter()
        .map(|import| import.verified_module().clone())
        .collect::<Vec<_>>();
    let cert = match npa_cert::build_module_cert(
        CoreModule {
            name: module,
            declarations: vec![Decl::Theorem {
                name: theorem_name,
                universe_params: candidate.goal.universe_params.clone(),
                ty: closed_type,
                proof: closed_proof,
            }],
        },
        &import_modules,
    ) {
        Ok(cert) => cert,
        Err(npa_cert::CertError::Kernel(_)) => {
            return Err(smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::KernelRejected,
                AdvancedSmtCertificateError::ReconstructionProofMismatch,
            ));
        }
        Err(_) => {
            return Err(AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::InternalValidatorFailure,
            });
        }
    };
    let cert_bytes =
        npa_cert::encode_module_cert(&cert).map_err(|_| AdvancedAiEndpointResponse::Error {
            error: AdvancedAiEndpointError::InternalValidatorFailure,
        })?;
    let mut verifier_session = VerifierSession::new();
    for import in import_modules {
        verifier_session.register_verified_module(import);
    }
    npa_cert::verify_module_cert(&cert_bytes, &mut verifier_session, &AxiomPolicy::normal())
        .map_err(|_| {
            smt_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::IndependentCheckerRejected,
                AdvancedSmtCertificateError::ReconstructionProofMismatch,
            )
        })?;
    Ok(())
}

fn advanced_ai_close_smt_goal_for_certificate(goal: &AdvancedAiGoal, proof: &Expr) -> (Expr, Expr) {
    let mut ty = goal.target.clone();
    let mut value = proof.clone();
    for local in goal.local_context.iter().rev() {
        if let Some(local_value) = &local.value {
            ty = Expr::let_in(
                local.name.clone(),
                local.ty.clone(),
                local_value.clone(),
                ty,
            );
            value = Expr::let_in(
                local.name.clone(),
                local.ty.clone(),
                local_value.clone(),
                value,
            );
        } else {
            ty = Expr::pi(local.name.clone(), local.ty.clone(), ty);
            value = Expr::lam(local.name.clone(), local.ty.clone(), value);
        }
    }
    (ty, value)
}

fn advanced_ai_smt_scratch_module(candidate_hash: Hash) -> ModuleName {
    Name(vec![
        "NPA".to_owned(),
        "Advanced".to_owned(),
        "SmtScratch".to_owned(),
        lowerhex_name_component(candidate_hash),
    ])
}

fn advanced_ai_smt_scratch_theorem(candidate_hash: Hash) -> Name {
    let mut components = advanced_ai_smt_scratch_module(candidate_hash).0;
    components.push("proof".to_owned());
    Name(components)
}

fn advanced_ai_smt_declared_payload_hash(
    candidate: &AdvancedMachineSmtCertificateCandidate,
) -> Hash {
    match &candidate.proof_payload {
        AdvancedMachineSmtProofPayloadRef::Inline { payload_hash, .. }
        | AdvancedMachineSmtProofPayloadRef::Artifact { payload_hash, .. } => *payload_hash,
    }
}

fn advanced_ai_validate_smt_bookkeeping_args(
    candidate_hash: Hash,
    candidate: &AdvancedMachineSmtCertificateCandidate,
    level_args: &[Level],
    term_args: &[Expr],
    verified_imports: &[VerifiedImportRef],
) -> std::result::Result<(), AdvancedAiEndpointResponse> {
    if !level_args
        .iter()
        .all(|level| level_is_in_scope(level, &candidate.goal.universe_params))
        || !term_args
            .iter()
            .all(|term| expr_levels_are_in_scope(term, &candidate.goal.universe_params))
    {
        return Err(smt_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedSmtCertificateError::NonCanonicalPayload,
        ));
    }
    if !term_args
        .iter()
        .all(|term| expr_imported_refs_are_resolved(term, verified_imports))
    {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        ));
    }
    Ok(())
}

fn theorem_graph_rejected_response(
    candidate_hash: Hash,
    error: AdvancedAiValidationError,
    graph_error: AdvancedTheoremGraphError,
) -> AdvancedAiEndpointResponse {
    rejected_response(
        candidate_hash,
        error,
        Some(AdvancedAiFeatureError::TheoremGraphQuery(graph_error)),
    )
}

fn advanced_ai_theorem_graph_snapshot_bytes(
    candidate_hash: Hash,
    source: &AdvancedMachineTheoremGraphSnapshotSource,
    workspace_root: &Path,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    match source {
        AdvancedMachineTheoremGraphSnapshotSource::Inline {
            canonical_bytes, ..
        } => {
            if canonical_bytes.len() > MAX_ADVANCED_AI_THEOREM_GRAPH_SNAPSHOT_BYTES {
                return Err(theorem_graph_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedTheoremGraphError::SnapshotMalformed,
                ));
            }
            Ok(canonical_bytes.clone())
        }
        AdvancedMachineTheoremGraphSnapshotSource::Artifact {
            path,
            file_hash,
            size_bytes,
            ..
        } => advanced_ai_theorem_graph_artifact_bytes(
            candidate_hash,
            workspace_root,
            path,
            *file_hash,
            *size_bytes,
            MAX_ADVANCED_AI_THEOREM_GRAPH_SNAPSHOT_BYTES,
            AdvancedTheoremGraphError::SnapshotMalformed,
        ),
    }
}

fn advanced_ai_theorem_graph_query_features_bytes(
    candidate_hash: Hash,
    source: &AdvancedMachineTheoremGraphQueryFeaturesRef,
    workspace_root: &Path,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    match source {
        AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
            canonical_bytes, ..
        } => {
            if canonical_bytes.len() > MAX_ADVANCED_AI_THEOREM_GRAPH_QUERY_FEATURES_BYTES {
                return Err(theorem_graph_rejected_response(
                    candidate_hash,
                    AdvancedAiValidationError::EnvelopeMalformed,
                    AdvancedTheoremGraphError::QueryFeaturesMalformed,
                ));
            }
            Ok(canonical_bytes.clone())
        }
        AdvancedMachineTheoremGraphQueryFeaturesRef::Artifact {
            path,
            file_hash,
            size_bytes,
            ..
        } => advanced_ai_theorem_graph_artifact_bytes(
            candidate_hash,
            workspace_root,
            path,
            *file_hash,
            *size_bytes,
            MAX_ADVANCED_AI_THEOREM_GRAPH_QUERY_FEATURES_BYTES,
            AdvancedTheoremGraphError::QueryFeaturesMalformed,
        ),
    }
}

fn advanced_ai_theorem_graph_artifact_bytes(
    candidate_hash: Hash,
    workspace_root: &Path,
    path: &str,
    file_hash: Hash,
    size_bytes: u64,
    max_bytes: usize,
    malformed_error: AdvancedTheoremGraphError,
) -> std::result::Result<Vec<u8>, AdvancedAiEndpointResponse> {
    if usize::try_from(size_bytes)
        .map(|size| size > max_bytes)
        .unwrap_or(true)
    {
        return Err(theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            malformed_error,
        ));
    }
    let path = match validate_artifact_path(workspace_root, path) {
        Ok(path) => path,
        Err(ArtifactPathError::EnvelopeMalformed) => {
            return Err(theorem_graph_rejected_response(
                candidate_hash,
                AdvancedAiValidationError::EnvelopeMalformed,
                malformed_error,
            ));
        }
        Err(ArtifactPathError::ArtifactUnavailable) => {
            return Err(AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::ArtifactUnavailable,
            });
        }
    };
    let metadata = std::fs::metadata(&path).map_err(|_| AdvancedAiEndpointResponse::Error {
        error: AdvancedAiEndpointError::ArtifactUnavailable,
    })?;
    if metadata.len() != size_bytes {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    let bytes = std::fs::read(path).map_err(|_| AdvancedAiEndpointResponse::Error {
        error: AdvancedAiEndpointError::ArtifactUnavailable,
    })?;
    if advanced_ai_file_hash(&bytes) != file_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    Ok(bytes)
}

fn advanced_ai_validate_theorem_graph_snapshot_bytes(
    candidate_hash: Hash,
    bytes: &[u8],
    snapshot_ref: &AdvancedMachineTheoremGraphSnapshotRef,
) -> std::result::Result<AdvancedMachineTheoremGraphSnapshot, AdvancedAiEndpointResponse> {
    advanced_ai_precheck_theorem_graph_snapshot_outer(bytes).map_err(|_| {
        theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::SnapshotMalformed,
        )
    })?;
    let expected_hash = match &snapshot_ref.source {
        AdvancedMachineTheoremGraphSnapshotSource::Inline {
            graph_snapshot_hash,
            ..
        }
        | AdvancedMachineTheoremGraphSnapshotSource::Artifact {
            graph_snapshot_hash,
            ..
        } => *graph_snapshot_hash,
    };
    if hash_with_domain(THEOREM_GRAPH_SNAPSHOT_HASH_TAG, bytes) != expected_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    let snapshot = decode_theorem_graph_snapshot(bytes).map_err(|_| {
        theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::SnapshotMalformed,
        )
    })?;
    Ok(snapshot)
}

fn advanced_ai_validate_theorem_graph_query_features_bytes(
    candidate_hash: Hash,
    bytes: &[u8],
    query: &AdvancedMachineTheoremGraphQuery,
) -> std::result::Result<AdvancedMachineTheoremGraphQueryFeatures, AdvancedAiEndpointResponse> {
    advanced_ai_precheck_theorem_graph_query_features_outer(bytes).map_err(|_| {
        theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::QueryFeaturesMalformed,
        )
    })?;
    let expected_hash = match &query.query_features {
        AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
            query_features_hash,
            ..
        }
        | AdvancedMachineTheoremGraphQueryFeaturesRef::Artifact {
            query_features_hash,
            ..
        } => *query_features_hash,
    };
    if hash_with_domain(THEOREM_GRAPH_QUERY_FEATURES_HASH_TAG, bytes) != expected_hash {
        return Err(rejected_response(
            candidate_hash,
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        ));
    }
    let query_features = decode_theorem_graph_query_features(bytes).map_err(|_| {
        theorem_graph_rejected_response(
            candidate_hash,
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedTheoremGraphError::QueryFeaturesMalformed,
        )
    })?;
    Ok(query_features)
}

fn advanced_ai_precheck_theorem_graph_snapshot_outer(
    bytes: &[u8],
) -> std::result::Result<(), DecodeError> {
    let mut decoder = Decoder::new(bytes);
    decoder.hash()?;
    AdvancedTheoremGraphExtractorVersion::from_tag(decoder.u8()?).ok_or(DecodeError::Malformed)?;
    let node_len = decoder.u64()?;
    if node_len > MAX_ADVANCED_AI_THEOREM_GRAPH_NODES {
        return Err(DecodeError::Malformed);
    }
    for _ in 0..node_len {
        decoder.skip_theorem_graph_node()?;
    }
    let edge_len = decoder.u64()?;
    if edge_len > MAX_ADVANCED_AI_THEOREM_GRAPH_EDGES {
        return Err(DecodeError::Malformed);
    }
    for _ in 0..edge_len {
        decoder.skip_theorem_graph_edge()?;
    }
    decoder.done()
}

fn advanced_ai_precheck_theorem_graph_query_features_outer(
    bytes: &[u8],
) -> std::result::Result<(), DecodeError> {
    let mut decoder = Decoder::new(bytes);
    decoder.hash()?;
    decoder.hash()?;
    AdvancedTheoremGraphFeatureSchemaVersion::from_tag(decoder.u8()?)
        .ok_or(DecodeError::Malformed)?;
    let feature_len = decoder.u64()?;
    if feature_len > MAX_ADVANCED_AI_THEOREM_GRAPH_FEATURES {
        return Err(DecodeError::Malformed);
    }
    for _ in 0..feature_len {
        decoder.skip_theorem_graph_feature()?;
    }
    decoder.done()
}

fn advanced_ai_theorem_graph_features_are_well_formed(
    features: &[AdvancedMachineTheoremGraphFeature],
) -> bool {
    let mut previous = None;
    for feature in features {
        if !advanced_ai_theorem_graph_feature_key_is_valid(&feature.key) {
            return false;
        }
        let key = advanced_ai_theorem_graph_feature_key_canonical_bytes(&feature.key);
        if previous.as_ref().is_some_and(|previous| previous >= &key) {
            return false;
        }
        previous = Some(key);
    }
    true
}

fn advanced_ai_theorem_graph_feature_key_is_valid(key: &AdvancedTheoremGraphFeatureKey) -> bool {
    advanced_ai_theorem_graph_feature_key_component_is_valid(&key.namespace_ascii)
        && advanced_ai_theorem_graph_feature_key_component_is_valid(&key.name_ascii)
}

fn advanced_ai_theorem_graph_feature_key_component_is_valid(bytes: &[u8]) -> bool {
    if bytes.is_empty() || bytes.len() > 64 {
        return false;
    }
    let Some(first) = bytes.first().copied() else {
        return false;
    };
    if !first.is_ascii_alphabetic() && first != b'_' {
        return false;
    }
    bytes[1..]
        .iter()
        .all(|byte| byte.is_ascii_alphanumeric() || matches!(*byte, b'_' | b'.' | b':' | b'-'))
}

fn advanced_ai_theorem_graph_feature_key_canonical_bytes(
    key: &AdvancedTheoremGraphFeatureKey,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_bytes_to(&mut out, &key.namespace_ascii);
    encode_bytes_to(&mut out, &key.name_ascii);
    out
}

fn advanced_ai_theorem_graph_snapshot_is_well_formed(
    snapshot: &AdvancedMachineTheoremGraphSnapshot,
) -> bool {
    let mut previous_node = None;
    let mut node_bytes = BTreeSet::new();
    for node in &snapshot.nodes {
        let identity = advanced_ai_theorem_graph_node_identity_key(node);
        if previous_node
            .as_ref()
            .is_some_and(|previous| previous >= &identity)
        {
            return false;
        }
        previous_node = Some(identity);
        let Ok(bytes) = advanced_ai_theorem_graph_node_canonical_bytes(node) else {
            return false;
        };
        node_bytes.insert(bytes);
    }

    let mut previous_edge = None;
    for edge in &snapshot.edges {
        let key = advanced_ai_theorem_graph_edge_key(edge);
        if previous_edge
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return false;
        }
        previous_edge = Some(key);

        let Ok(from) = advanced_ai_theorem_graph_node_canonical_bytes(&edge.from) else {
            return false;
        };
        let Ok(to) = advanced_ai_theorem_graph_node_canonical_bytes(&edge.to) else {
            return false;
        };
        if !node_bytes.contains(&from) || !node_bytes.contains(&to) {
            return false;
        }
    }
    true
}

fn advanced_ai_theorem_graph_node_identity_key(
    node: &AdvancedMachineTheoremGraphNodeRef,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name_to(&mut out, &node.module).expect("decoded theorem graph module is canonical");
    encode_name_to(&mut out, &node.name).expect("decoded theorem graph name is canonical");
    encode_hash_to(&mut out, &node.export_hash);
    encode_hash_to(&mut out, &node.certificate_hash);
    encode_hash_to(&mut out, &node.decl_interface_hash);
    out
}

fn advanced_ai_theorem_graph_edge_key(edge: &AdvancedMachineTheoremGraphEdge) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&advanced_ai_theorem_graph_node_identity_key(&edge.from));
    out.extend_from_slice(&advanced_ai_theorem_graph_node_identity_key(&edge.to));
    out.push(edge.kind.tag());
    out
}

enum AdvancedTheoremGraphNodeResolution {
    Missing,
    Mismatch,
    Resolved { eligible: bool },
}

fn advanced_ai_resolve_theorem_graph_node(
    node: &AdvancedMachineTheoremGraphNodeRef,
    imports: &[VerifiedImportRef],
) -> AdvancedTheoremGraphNodeResolution {
    let Some(import) = imports.iter().find(|import| {
        import.module() == &node.module
            && import.export_hash() == node.export_hash
            && import.certificate_hash() == node.certificate_hash
    }) else {
        return AdvancedTheoremGraphNodeResolution::Missing;
    };

    let matches = import
        .exports()
        .iter()
        .filter(|export| {
            export.name == node.name && export.decl_interface_hash == node.decl_interface_hash
        })
        .collect::<Vec<_>>();
    let [export] = matches.as_slice() else {
        return AdvancedTheoremGraphNodeResolution::Missing;
    };
    if export.type_hash != node.type_hash {
        return AdvancedTheoremGraphNodeResolution::Mismatch;
    }
    let Some(decl) = import
        .verified_module()
        .declarations()
        .iter()
        .find(|decl| decl.hashes.decl_interface_hash == export.decl_interface_hash)
    else {
        return AdvancedTheoremGraphNodeResolution::Mismatch;
    };
    if decl.hashes.decl_certificate_hash != node.decl_certificate_hash {
        return AdvancedTheoremGraphNodeResolution::Mismatch;
    }
    AdvancedTheoremGraphNodeResolution::Resolved {
        eligible: matches!(export.kind, ExportKind::Axiom | ExportKind::Theorem),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AdvancedInductiveCheckError {
    TargetRefMismatch,
    KernelRejected,
    UnsupportedPositivity,
}

struct ResolvedAdvancedAiGlobalRef {
    const_name: String,
    universe_arity: usize,
}

fn advanced_ai_family_public_name(block_name: Option<&Name>, family_name: &Name) -> Name {
    match block_name {
        Some(block_name) => advanced_ai_append_name(block_name, family_name),
        None => family_name.clone(),
    }
}

fn advanced_ai_append_name(prefix: &Name, suffix: &Name) -> Name {
    let mut components = prefix.0.clone();
    components.extend(suffix.0.iter().cloned());
    Name(components)
}

fn advanced_ai_inductive_names_collide(
    family: &AdvancedMachineInductiveFamilyProposal,
    family_public_name: &Name,
    constructor_public_names: &[Name],
    recursor_public_name: &Name,
) -> bool {
    let mut local_names = BTreeSet::new();
    if !local_names.insert(family.name.clone()) {
        return true;
    }
    for constructor in &family.constructors {
        if !local_names.insert(constructor.name.clone()) {
            return true;
        }
    }

    let mut public_names = BTreeSet::new();
    if !public_names.insert(family_public_name.clone()) {
        return true;
    }
    for constructor_name in constructor_public_names {
        if !public_names.insert(constructor_name.clone()) {
            return true;
        }
    }
    !public_names.insert(recursor_public_name.clone())
}

fn advanced_ai_inductive_family_levels_are_in_scope(
    family: &AdvancedMachineInductiveFamilyProposal,
    params: &[String],
) -> bool {
    family
        .params
        .iter()
        .chain(&family.indices)
        .all(|binder| expr_levels_are_in_scope(&binder.ty, params))
        && family
            .constructors
            .iter()
            .all(|constructor| expr_levels_are_in_scope(&constructor.ty, params))
}

fn advanced_ai_telescope_contains_const_name(
    telescope: &[AdvancedMachineTelescopeBinder],
    name: &str,
) -> bool {
    telescope
        .iter()
        .any(|binder| expr_contains_const_name(&binder.ty, name))
}

fn expr_contains_const_name(expr: &Expr, needle: &str) -> bool {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => false,
        Expr::Const { name, .. } => name == needle,
        Expr::App(fun, arg) => {
            expr_contains_const_name(fun, needle) || expr_contains_const_name(arg, needle)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_contains_const_name(ty, needle) || expr_contains_const_name(body, needle)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_contains_const_name(ty, needle)
                || expr_contains_const_name(value, needle)
                || expr_contains_const_name(body, needle)
        }
    }
}

fn advanced_ai_telescope_imported_refs_are_resolved(
    telescope: &[AdvancedMachineTelescopeBinder],
    imports: &[VerifiedImportRef],
    allowed_local_names: &BTreeSet<String>,
) -> bool {
    telescope.iter().all(|binder| {
        expr_imported_refs_are_resolved_with_allowed_locals(
            &binder.ty,
            imports,
            allowed_local_names,
        )
    })
}

fn expr_imported_refs_are_resolved_with_allowed_locals(
    expr: &Expr,
    imports: &[VerifiedImportRef],
    allowed_local_names: &BTreeSet<String>,
) -> bool {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => true,
        Expr::Const { name, .. } => {
            allowed_local_names.contains(name) || const_name_is_exported_once(name, imports)
        }
        Expr::App(fun, arg) => {
            expr_imported_refs_are_resolved_with_allowed_locals(fun, imports, allowed_local_names)
                && expr_imported_refs_are_resolved_with_allowed_locals(
                    arg,
                    imports,
                    allowed_local_names,
                )
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_imported_refs_are_resolved_with_allowed_locals(ty, imports, allowed_local_names)
                && expr_imported_refs_are_resolved_with_allowed_locals(
                    body,
                    imports,
                    allowed_local_names,
                )
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_imported_refs_are_resolved_with_allowed_locals(ty, imports, allowed_local_names)
                && expr_imported_refs_are_resolved_with_allowed_locals(
                    value,
                    imports,
                    allowed_local_names,
                )
                && expr_imported_refs_are_resolved_with_allowed_locals(
                    body,
                    imports,
                    allowed_local_names,
                )
        }
    }
}

fn advanced_ai_check_telescope_kernel<'a>(
    env: &Env,
    delta: &[String],
    telescope: impl Iterator<Item = &'a AdvancedMachineTelescopeBinder>,
) -> std::result::Result<(), ()> {
    let mut ctx = Ctx::new();
    for (index, binder) in telescope.enumerate() {
        expect_sort_public(env, &ctx, delta, &binder.ty)?;
        ctx.push_assumption(format!("x{index}"), binder.ty.clone());
    }
    Ok(())
}

fn advanced_ai_base_inductive_decl(
    proposal: &AdvancedMachineInductiveProposal,
    family: &AdvancedMachineInductiveFamilyProposal,
    family_public_name: &Name,
    constructor_public_names: &[Name],
) -> InductiveDecl {
    InductiveDecl::new(
        family_public_name.as_dotted(),
        proposal.universe_params.clone(),
        family
            .params
            .iter()
            .enumerate()
            .map(|(index, binder)| Binder::new(format!("p{index}"), binder.ty.clone()))
            .collect(),
        family
            .indices
            .iter()
            .enumerate()
            .map(|(index, binder)| Binder::new(format!("i{index}"), binder.ty.clone()))
            .collect(),
        family.result_sort.clone(),
        family
            .constructors
            .iter()
            .zip(constructor_public_names)
            .map(|(constructor, public_name)| {
                ConstructorDecl::new(public_name.as_dotted(), constructor.ty.clone())
            })
            .collect(),
        None,
    )
}

fn advanced_ai_inductive_type(data: &InductiveDecl) -> Expr {
    data.params
        .iter()
        .chain(&data.indices)
        .rev()
        .fold(Expr::sort(data.sort.clone()), |body, binder| {
            Expr::pi(binder.name.clone(), binder.ty.clone(), body)
        })
}

fn advanced_ai_check_constructor_result(
    env: &Env,
    data: &InductiveDecl,
    constructor: &ConstructorDecl,
) -> std::result::Result<(), AdvancedInductiveCheckError> {
    let (domains, result) = advanced_ai_peel_pi_domains(&constructor.ty);
    let result = env
        .whnf(&Ctx::new(), &data.universe_params, &result)
        .map_err(|_| AdvancedInductiveCheckError::KernelRejected)?;
    let (head, args) = npa_kernel::expr::collect_apps(&result);
    let levels = match head {
        Expr::Const { name, levels } if name == data.name => levels,
        _ => return Err(AdvancedInductiveCheckError::TargetRefMismatch),
    };
    let expected_levels = data
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect::<Vec<_>>();
    if !npa_kernel::level::levels_eq(&levels, &expected_levels)
        || args.len() != data.params.len() + data.indices.len()
        || domains.len() < data.params.len()
    {
        return Err(AdvancedInductiveCheckError::TargetRefMismatch);
    }
    for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
        let expected = advanced_ai_bvar_for_abs(domains.len(), param_index)
            .ok_or(AdvancedInductiveCheckError::TargetRefMismatch)?;
        if arg != &expected {
            return Err(AdvancedInductiveCheckError::TargetRefMismatch);
        }
    }
    Ok(())
}

fn advanced_ai_check_constructor_positivity(
    data: &InductiveDecl,
    constructor: &ConstructorDecl,
) -> std::result::Result<(), AdvancedInductiveCheckError> {
    let (domains, _) = advanced_ai_peel_pi_domains(&constructor.ty);
    for (domain_index, domain) in domains.iter().enumerate() {
        if domain_index >= data.params.len() {
            match advanced_ai_direct_recursive_domain_status(data, domain, domain_index)? {
                AdvancedDirectRecursiveDomain::Direct => continue,
                AdvancedDirectRecursiveDomain::BadTarget => {
                    return Err(AdvancedInductiveCheckError::TargetRefMismatch)
                }
                AdvancedDirectRecursiveDomain::NotRecursive => {}
            }
        }
        if expr_contains_const_name(domain, &data.name) {
            return Err(AdvancedInductiveCheckError::UnsupportedPositivity);
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AdvancedDirectRecursiveDomain {
    Direct,
    BadTarget,
    NotRecursive,
}

fn advanced_ai_direct_recursive_domain_status(
    data: &InductiveDecl,
    domain: &Expr,
    ctx_len: usize,
) -> std::result::Result<AdvancedDirectRecursiveDomain, AdvancedInductiveCheckError> {
    let (head, args) = npa_kernel::expr::collect_apps(domain);
    let levels = match head {
        Expr::Const { name, levels } if name == data.name => levels,
        _ => return Ok(AdvancedDirectRecursiveDomain::NotRecursive),
    };
    let expected_levels = data
        .universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect::<Vec<_>>();
    if !npa_kernel::level::levels_eq(&levels, &expected_levels)
        || args.len() != data.params.len() + data.indices.len()
    {
        return Ok(AdvancedDirectRecursiveDomain::BadTarget);
    }
    for (param_index, arg) in args.iter().take(data.params.len()).enumerate() {
        let expected = advanced_ai_bvar_for_abs(ctx_len, param_index)
            .ok_or(AdvancedInductiveCheckError::TargetRefMismatch)?;
        if arg != &expected {
            return Ok(AdvancedDirectRecursiveDomain::BadTarget);
        }
    }
    if args
        .iter()
        .skip(data.params.len())
        .any(|arg| expr_contains_const_name(arg, &data.name))
    {
        return Err(AdvancedInductiveCheckError::UnsupportedPositivity);
    }
    Ok(AdvancedDirectRecursiveDomain::Direct)
}

fn advanced_ai_peel_pi_domains(ty: &Expr) -> (Vec<Expr>, Expr) {
    let mut domains = Vec::new();
    let mut current = ty;
    while let Expr::Pi { ty, body, .. } = current {
        domains.push((**ty).clone());
        current = body;
    }
    (domains, current.clone())
}

fn advanced_ai_bvar_for_abs(ctx_len: usize, abs: usize) -> Option<Expr> {
    if abs >= ctx_len {
        return None;
    }
    Some(Expr::bvar((ctx_len - 1 - abs) as u32))
}

fn advanced_ai_universe_constraint_set_hash(constraints: &[AdvancedUniverseConstraint]) -> Hash {
    let mut canonical = constraints.to_vec();
    canonical.sort_by_key(advanced_ai_universe_constraint_canonical_bytes);
    let mut out = Vec::new();
    encode_len_to(&mut out, canonical.len());
    for constraint in &canonical {
        encode_universe_constraint_to(&mut out, constraint);
    }
    hash_with_domain(UNIVERSE_CONSTRAINT_SET_HASH_TAG, &out)
}

fn advanced_ai_universe_params_canonical_bytes(params: &[String]) -> Vec<u8> {
    let mut out = Vec::new();
    encode_len_to(&mut out, params.len());
    for param in params {
        encode_string_to(&mut out, param);
    }
    out
}

fn advanced_ai_core_expr_bytes_eq(lhs: &Expr, rhs: &Expr) -> bool {
    npa_cert::core_expr_canonical_bytes(lhs) == npa_cert::core_expr_canonical_bytes(rhs)
}

fn advanced_ai_string_list_is_unique(values: &[String]) -> bool {
    let mut seen = BTreeSet::new();
    values.iter().all(|value| seen.insert(value))
}

fn local_decl_levels_are_in_scope(local: &MachineLocalDecl, params: &[String]) -> bool {
    expr_levels_are_in_scope(&local.ty, params)
        && local
            .value
            .as_ref()
            .is_none_or(|value| expr_levels_are_in_scope(value, params))
}

fn expr_levels_are_in_scope(expr: &Expr, params: &[String]) -> bool {
    match expr {
        Expr::Sort(level) => level_is_in_scope(level, params),
        Expr::BVar(_) => true,
        Expr::Const { levels, .. } => levels.iter().all(|level| level_is_in_scope(level, params)),
        Expr::App(fun, arg) => {
            expr_levels_are_in_scope(fun, params) && expr_levels_are_in_scope(arg, params)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_levels_are_in_scope(ty, params) && expr_levels_are_in_scope(body, params)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_levels_are_in_scope(ty, params)
                && expr_levels_are_in_scope(value, params)
                && expr_levels_are_in_scope(body, params)
        }
    }
}

fn level_is_in_scope(level: &Level, params: &[String]) -> bool {
    match level {
        Level::Zero => true,
        Level::Succ(inner) => level_is_in_scope(inner, params),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            level_is_in_scope(lhs, params) && level_is_in_scope(rhs, params)
        }
        Level::Param(name) => params.iter().any(|param| param == name),
    }
}

fn constraint_levels_are_in_scope(
    constraint: &AdvancedUniverseConstraint,
    params: &[String],
) -> bool {
    level_is_in_scope(&constraint.lhs, params) && level_is_in_scope(&constraint.rhs, params)
}

fn goal_imported_refs_are_resolved(goal: &AdvancedAiGoal, imports: &[VerifiedImportRef]) -> bool {
    goal.local_context.iter().all(|local| {
        expr_imported_refs_are_resolved(&local.ty, imports)
            && local
                .value
                .as_ref()
                .is_none_or(|value| expr_imported_refs_are_resolved(value, imports))
    }) && expr_imported_refs_are_resolved(&goal.target, imports)
}

fn expr_imported_refs_are_resolved(expr: &Expr, imports: &[VerifiedImportRef]) -> bool {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => true,
        Expr::Const { name, .. } => const_name_is_exported_once(name, imports),
        Expr::App(fun, arg) => {
            expr_imported_refs_are_resolved(fun, imports)
                && expr_imported_refs_are_resolved(arg, imports)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_imported_refs_are_resolved(ty, imports)
                && expr_imported_refs_are_resolved(body, imports)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_imported_refs_are_resolved(ty, imports)
                && expr_imported_refs_are_resolved(value, imports)
                && expr_imported_refs_are_resolved(body, imports)
        }
    }
}

fn const_name_is_exported_once(name: &str, imports: &[VerifiedImportRef]) -> bool {
    let mut matches = 0usize;
    for import in imports {
        for export in import.exports() {
            if export.name.as_dotted() == name {
                matches += 1;
            }
        }
    }
    matches == 1
}

fn validate_goal_kernel(
    goal: &AdvancedAiGoal,
    imports: &[VerifiedImportRef],
) -> std::result::Result<(), ()> {
    let env = advanced_ai_kernel_env_from_imports(imports)?;
    let mut ctx = Ctx::new();
    for local in &goal.local_context {
        expect_sort_public(&env, &ctx, &goal.universe_params, &local.ty)?;
        if let Some(value) = &local.value {
            env.check(&ctx, &goal.universe_params, value, &local.ty)
                .map_err(|_| ())?;
            ctx.push_definition(local.name.clone(), local.ty.clone(), value.clone());
        } else {
            ctx.push_assumption(local.name.clone(), local.ty.clone());
        }
    }
    expect_sort_public(&env, &ctx, &goal.universe_params, &goal.target)
}

fn derive_universe_constraints(
    goal: &AdvancedAiGoal,
    repaired_expr: &Expr,
    imports: &[VerifiedImportRef],
) -> std::result::Result<Vec<AdvancedUniverseConstraint>, ()> {
    // The current kernel stores no declaration-local universe constraints, so
    // rechecking the repaired goal is the deterministic solver boundary for M2.
    let mut repaired_goal = goal.clone();
    repaired_goal.target = repaired_expr.clone();
    validate_goal_kernel(&repaired_goal, imports)?;
    Ok(Vec::new())
}

fn advanced_ai_kernel_env_from_imports(
    imports: &[VerifiedImportRef],
) -> std::result::Result<Env, ()> {
    let mut env = Env::new();
    for import in imports {
        for decl in import.certified_env_decls() {
            if env.decl(decl.name()).is_some() {
                continue;
            }
            match decl {
                npa_kernel::Decl::Axiom {
                    name,
                    universe_params,
                    ty,
                } => env
                    .add_axiom(name.clone(), universe_params.clone(), ty.clone())
                    .map_err(|_| ())?,
                npa_kernel::Decl::AxiomConstrained {
                    name,
                    universe_params,
                    universe_constraints,
                    ty,
                } => env
                    .add_axiom_with_universe_constraints(
                        name.clone(),
                        universe_params.clone(),
                        universe_constraints.clone(),
                        ty.clone(),
                    )
                    .map_err(|_| ())?,
                npa_kernel::Decl::Def {
                    name,
                    universe_params,
                    ty,
                    value,
                    reducibility,
                } => env
                    .add_def(
                        name.clone(),
                        universe_params.clone(),
                        ty.clone(),
                        value.clone(),
                        reducibility.clone(),
                    )
                    .map_err(|_| ())?,
                npa_kernel::Decl::DefConstrained {
                    name,
                    universe_params,
                    universe_constraints,
                    ty,
                    value,
                    reducibility,
                } => env
                    .add_def_with_universe_constraints(
                        name.clone(),
                        universe_params.clone(),
                        universe_constraints.clone(),
                        ty.clone(),
                        value.clone(),
                        reducibility.clone(),
                    )
                    .map_err(|_| ())?,
                npa_kernel::Decl::Theorem {
                    name,
                    universe_params,
                    ty,
                    proof,
                } => env
                    .add_theorem(
                        name.clone(),
                        universe_params.clone(),
                        ty.clone(),
                        proof.clone(),
                    )
                    .map_err(|_| ())?,
                npa_kernel::Decl::TheoremConstrained {
                    name,
                    universe_params,
                    universe_constraints,
                    ty,
                    proof,
                } => env
                    .add_theorem_with_universe_constraints(
                        name.clone(),
                        universe_params.clone(),
                        universe_constraints.clone(),
                        ty.clone(),
                        proof.clone(),
                    )
                    .map_err(|_| ())?,
                npa_kernel::Decl::Inductive { data, .. } => {
                    env.add_inductive((**data).clone()).map_err(|_| ())?
                }
                npa_kernel::Decl::MutualInductiveBlock { data, .. } => {
                    env.add_mutual_inductive((**data).clone()).map_err(|_| ())?
                }
                npa_kernel::Decl::Constructor { .. } | npa_kernel::Decl::Recursor { .. } => {}
            }
        }
    }
    Ok(env)
}

fn expect_sort_public(
    env: &Env,
    ctx: &Ctx,
    delta: &[String],
    term: &Expr,
) -> std::result::Result<(), ()> {
    match env
        .whnf(ctx, delta, &env.infer(ctx, delta, term).map_err(|_| ())?)
        .map_err(|_| ())?
    {
        Expr::Sort(_) => Ok(()),
        _ => Err(()),
    }
}

fn resolve_advanced_ai_global_ref(
    global_ref: &AdvancedAiGlobalRef,
    imports: &[VerifiedImportRef],
) -> Option<ResolvedAdvancedAiGlobalRef> {
    let mut matches = Vec::new();
    for import in imports {
        let identity = AdvancedImportIdentity::from_verified_import(import);
        if identity.module != global_ref.module
            || identity.export_hash != global_ref.export_hash
            || identity.certificate_hash != global_ref.certificate_hash
        {
            continue;
        }
        for export in import.exports().iter().filter(|export| {
            export.name == global_ref.name
                && export.decl_interface_hash == global_ref.decl_interface_hash
        }) {
            let decl = import
                .certified_env_decls()
                .iter()
                .find(|decl| decl.name() == export.name.as_dotted())?;
            matches.push(ResolvedAdvancedAiGlobalRef {
                const_name: export.name.as_dotted(),
                universe_arity: decl.universe_params().len(),
            });
        }
    }
    let [resolved] = matches.as_slice() else {
        return None;
    };
    Some(ResolvedAdvancedAiGlobalRef {
        const_name: resolved.const_name.clone(),
        universe_arity: resolved.universe_arity,
    })
}

fn expr_at_path<'a>(expr: &'a Expr, path: &[AdvancedMachineExprPathStep]) -> Option<&'a Expr> {
    let mut current = expr;
    for step in path {
        current = match (current, step) {
            (Expr::App(fun, _), AdvancedMachineExprPathStep::AppFun) => fun,
            (Expr::App(_, arg), AdvancedMachineExprPathStep::AppArg) => arg,
            (Expr::Lam { ty, .. }, AdvancedMachineExprPathStep::LamType) => ty,
            (Expr::Lam { body, .. }, AdvancedMachineExprPathStep::LamBody) => body,
            (Expr::Pi { ty, .. }, AdvancedMachineExprPathStep::PiDomain) => ty,
            (Expr::Pi { body, .. }, AdvancedMachineExprPathStep::PiCodomain) => body,
            (Expr::Let { ty, .. }, AdvancedMachineExprPathStep::LetType) => ty,
            (Expr::Let { value, .. }, AdvancedMachineExprPathStep::LetValue) => value,
            (Expr::Let { body, .. }, AdvancedMachineExprPathStep::LetBody) => body,
            _ => return None,
        };
    }
    Some(current)
}

fn replace_const_levels_at_path(
    expr: &mut Expr,
    path: &[AdvancedMachineExprPathStep],
    explicit_level_args: Vec<Level>,
) -> Option<()> {
    let current = expr_at_path_mut(expr, path)?;
    let Expr::Const { levels, .. } = current else {
        return None;
    };
    *levels = explicit_level_args;
    Some(())
}

fn expr_at_path_mut<'a>(
    expr: &'a mut Expr,
    path: &[AdvancedMachineExprPathStep],
) -> Option<&'a mut Expr> {
    let mut current = expr;
    for step in path {
        current = match (current, step) {
            (Expr::App(fun, _), AdvancedMachineExprPathStep::AppFun) => Arc::make_mut(fun),
            (Expr::App(_, arg), AdvancedMachineExprPathStep::AppArg) => Arc::make_mut(arg),
            (Expr::Lam { ty, .. }, AdvancedMachineExprPathStep::LamType) => Arc::make_mut(ty),
            (Expr::Lam { body, .. }, AdvancedMachineExprPathStep::LamBody) => Arc::make_mut(body),
            (Expr::Pi { ty, .. }, AdvancedMachineExprPathStep::PiDomain) => Arc::make_mut(ty),
            (Expr::Pi { body, .. }, AdvancedMachineExprPathStep::PiCodomain) => Arc::make_mut(body),
            (Expr::Let { ty, .. }, AdvancedMachineExprPathStep::LetType) => Arc::make_mut(ty),
            (Expr::Let { value, .. }, AdvancedMachineExprPathStep::LetValue) => {
                Arc::make_mut(value)
            }
            (Expr::Let { body, .. }, AdvancedMachineExprPathStep::LetBody) => Arc::make_mut(body),
            _ => return None,
        };
    }
    Some(current)
}

fn decode_universe_instantiation_items(
    items: &[Vec<u8>],
) -> std::result::Result<Vec<AdvancedUniverseInstantiationPatch>, DecodeError> {
    items
        .iter()
        .map(|item| decode_universe_instantiation_patch(item))
        .collect()
}

fn decode_universe_constraint_hint_items(
    items: &[Vec<u8>],
) -> std::result::Result<Vec<AdvancedUniverseConstraintHint>, DecodeError> {
    items
        .iter()
        .map(|item| decode_universe_constraint_hint(item))
        .collect()
}

fn universe_instantiations_are_strictly_sorted(
    instantiations: &[AdvancedUniverseInstantiationPatch],
) -> bool {
    let mut previous: Option<Vec<u8>> = None;
    for patch in instantiations {
        let key = universe_instantiation_key(patch);
        if previous.as_ref().is_some_and(|previous| previous >= &key) {
            return false;
        }
        previous = Some(key);
    }
    true
}

fn universe_instantiation_key(patch: &AdvancedUniverseInstantiationPatch) -> Vec<u8> {
    let mut out = Vec::new();
    encode_path_steps_to(&mut out, &patch.occurrence.path);
    encode_global_ref_to(&mut out, &patch.occurrence.expected_ref)
        .expect("decoded global refs must be canonical");
    out
}

fn universe_constraint_hints_are_strictly_sorted(hints: &[AdvancedUniverseConstraintHint]) -> bool {
    let mut previous: Option<Vec<u8>> = None;
    for hint in hints {
        let key = advanced_ai_universe_constraint_canonical_bytes(&hint.constraint);
        if previous.as_ref().is_some_and(|previous| previous >= &key) {
            return false;
        }
        previous = Some(key);
    }
    true
}

fn advanced_ai_universe_constraint_canonical_bytes(
    constraint: &AdvancedUniverseConstraint,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_universe_constraint_to(&mut out, constraint);
    out
}

fn universe_constraint_is_satisfiable(constraint: &AdvancedUniverseConstraint) -> bool {
    match constraint.relation {
        AdvancedUniverseConstraintRelation::Eq => {
            normalized_levels_are_equal(&constraint.lhs, &constraint.rhs)
        }
        AdvancedUniverseConstraintRelation::Le => {
            level_leq_is_satisfiable(&constraint.lhs, &constraint.rhs)
        }
    }
}

fn normalized_levels_are_equal(lhs: &Level, rhs: &Level) -> bool {
    npa_kernel::level::normalize_level(lhs.clone())
        == npa_kernel::level::normalize_level(rhs.clone())
}

fn level_leq_is_satisfiable(lhs: &Level, rhs: &Level) -> bool {
    let lhs = npa_kernel::level::normalize_level(lhs.clone());
    let rhs = npa_kernel::level::normalize_level(rhs.clone());
    if lhs == rhs || lhs == Level::Zero {
        return true;
    }
    match (&lhs, &rhs) {
        (Level::Succ(inner), _) if **inner == rhs => false,
        (Level::Succ(lhs_inner), Level::Succ(rhs_inner)) => {
            level_leq_is_satisfiable(lhs_inner, rhs_inner)
        }
        (Level::Param(_), Level::Succ(_)) => true,
        (_, Level::Max(left, right)) => {
            level_leq_is_satisfiable(&lhs, left) || level_leq_is_satisfiable(&lhs, right)
        }
        _ => true,
    }
}

fn rejected_response(
    candidate_hash: Hash,
    error: AdvancedAiValidationError,
    feature_error: Option<AdvancedAiFeatureError>,
) -> AdvancedAiEndpointResponse {
    AdvancedAiEndpointResponse::Rejected {
        candidate_hash,
        validation_result_hash: advanced_ai_validation_result_hash_for_rejection(
            candidate_hash,
            error,
            feature_error,
        ),
        error,
        feature_error,
    }
}

fn validation_result_hash(candidate_hash: Hash, payload: &[u8]) -> Hash {
    let mut bytes = Vec::new();
    encode_hash_to(&mut bytes, &candidate_hash);
    bytes.extend_from_slice(payload);
    hash_with_domain(VALIDATION_RESULT_HASH_TAG, &bytes)
}

fn encode_success_payload_to(out: &mut Vec<u8>, success: &AdvancedAiSuccessPayload) {
    match success {
        AdvancedAiSuccessPayload::AdvancedInductive {
            decl_interface_hash,
            decl_certificate_hash,
        } => {
            out.push(0);
            encode_hash_to(out, decl_interface_hash);
            encode_hash_to(out, decl_certificate_hash);
        }
        AdvancedAiSuccessPayload::UniverseRepair {
            repaired_expr,
            constraint_set_hash,
        } => {
            out.push(1);
            encode_expr_to(out, repaired_expr);
            encode_hash_to(out, constraint_set_hash);
        }
        AdvancedAiSuccessPayload::TypeclassResolution { proof } => {
            out.push(2);
            encode_expr_to(out, proof);
        }
        AdvancedAiSuccessPayload::SmtCertificate { final_proof } => {
            out.push(4);
            encode_expr_to(out, final_proof);
        }
        AdvancedAiSuccessPayload::TheoremGraphQuery { result } => {
            out.push(5);
            encode_theorem_graph_result_to(out, result);
        }
        AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind,
            accepted_statement_hash,
            formalization_proof_root_hash,
        } => {
            out.push(6);
            out.push(match kind {
                AdvancedFormalizationSuccessKind::CandidateStatementChecked => 0,
                AdvancedFormalizationSuccessKind::IntentRecordOnly => 1,
                AdvancedFormalizationSuccessKind::ProofBridgeChecked => 2,
            });
            encode_option_hash_to(out, accepted_statement_hash.as_ref());
            encode_option_hash_to(out, formalization_proof_root_hash.as_ref());
        }
    }
}

fn encode_candidate_envelope_to(
    out: &mut Vec<u8>,
    envelope: &AdvancedAiCandidateEnvelope,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    out.push(envelope.profile_version.tag());
    out.push(envelope.task_kind.tag());
    encode_target_to(out, &envelope.target);
    encode_import_identities_to(out, &envelope.imports)?;
    encode_options_ref_to(out, &envelope.options);
    encode_bytes_to(out, &envelope.payload);
    Ok(())
}

fn encode_target_to(out: &mut Vec<u8>, target: &AdvancedAiTarget) {
    encode_hash_to(out, &target.env_fingerprint);
    encode_option_hash_to(out, target.target_decl_hash.as_ref());
    encode_option_hash_to(out, target.goal_fingerprint.as_ref());
}

fn encode_import_identities_to(
    out: &mut Vec<u8>,
    imports: &[AdvancedImportIdentity],
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_len_to(out, imports.len());
    for import in imports {
        encode_name_to(out, &import.module)?;
        encode_hash_to(out, &import.export_hash);
        encode_hash_to(out, &import.certificate_hash);
    }
    Ok(())
}

fn encode_options_ref_to(out: &mut Vec<u8>, options_ref: &AdvancedAiOptionsRef) {
    match options_ref {
        AdvancedAiOptionsRef::Inline {
            options_hash,
            canonical_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, options_hash);
            encode_bytes_to(out, canonical_bytes);
        }
        AdvancedAiOptionsRef::Artifact {
            path,
            file_hash,
            options_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, options_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
}

fn encode_options_to(
    out: &mut Vec<u8>,
    options: &AdvancedAiOptions,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    out.push(options.schema_version.tag());
    out.push(options.independent_checker.profile.tag());
    encode_global_ref_list_to(
        out,
        &options.advanced_inductive.approved_nested_type_constructors,
    )?;
    encode_global_ref_list_to(out, &options.typeclass.class_declarations)?;
    encode_option_smt_to(out, options.smt.as_ref())?;
    encode_option_formalization_to(out, options.formalization.as_ref());
    Ok(())
}

fn encode_global_ref_list_to(
    out: &mut Vec<u8>,
    refs: &[AdvancedAiGlobalRef],
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_len_to(out, refs.len());
    for global_ref in refs {
        encode_global_ref_to(out, global_ref)?;
    }
    Ok(())
}

fn encode_global_ref_to(
    out: &mut Vec<u8>,
    global_ref: &AdvancedAiGlobalRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_name_to(out, &global_ref.module)?;
    encode_hash_to(out, &global_ref.export_hash);
    encode_hash_to(out, &global_ref.certificate_hash);
    encode_name_to(out, &global_ref.name)?;
    encode_hash_to(out, &global_ref.decl_interface_hash);
    Ok(())
}

fn encode_option_smt_to(
    out: &mut Vec<u8>,
    options: Option<&AdvancedSmtOptions>,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match options {
        Some(options) => {
            out.push(1);
            encode_global_ref_to(out, &options.eq)?;
            encode_option_global_ref_to(out, options.prop_false.as_ref())?;
            encode_option_global_ref_to(out, options.prop_not.as_ref())?;
        }
        None => out.push(0),
    }
    Ok(())
}

fn encode_option_global_ref_to(
    out: &mut Vec<u8>,
    global_ref: Option<&AdvancedAiGlobalRef>,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match global_ref {
        Some(global_ref) => {
            out.push(1);
            encode_global_ref_to(out, global_ref)?;
        }
        None => out.push(0),
    }
    Ok(())
}

fn encode_option_formalization_to(
    out: &mut Vec<u8>,
    options: Option<&AdvancedFormalizationOptions>,
) {
    match options {
        Some(options) => {
            out.push(1);
            encode_bytes_to(out, &options.tactic_options_canonical_bytes);
            encode_bytes_to(out, &options.tactic_budget_canonical_bytes);
        }
        None => out.push(0),
    }
}

fn encode_inductive_proposal_to(
    out: &mut Vec<u8>,
    proposal: &AdvancedMachineInductiveProposal,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_option_name_to(out, proposal.block_name.as_ref())?;
    encode_option_hash_to(out, proposal.expected_decl_hash.as_ref());
    encode_len_to(out, proposal.universe_params.len());
    for param in &proposal.universe_params {
        encode_string_to(out, param);
    }
    encode_len_to(out, proposal.inductives.len());
    for family in &proposal.inductives {
        encode_inductive_family_to(out, family)?;
    }
    Ok(())
}

fn encode_option_name_to(
    out: &mut Vec<u8>,
    name: Option<&Name>,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match name {
        Some(name) => {
            out.push(1);
            encode_name_to(out, name)?;
        }
        None => out.push(0),
    }
    Ok(())
}

fn encode_inductive_family_to(
    out: &mut Vec<u8>,
    family: &AdvancedMachineInductiveFamilyProposal,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_name_to(out, &family.name)?;
    encode_telescope_to(out, &family.params);
    encode_telescope_to(out, &family.indices);
    encode_level_to(out, &family.result_sort);
    encode_len_to(out, family.constructors.len());
    for constructor in &family.constructors {
        encode_name_to(out, &constructor.name)?;
        encode_expr_to(out, &constructor.ty);
    }
    Ok(())
}

fn encode_telescope_to(out: &mut Vec<u8>, telescope: &[AdvancedMachineTelescopeBinder]) {
    encode_len_to(out, telescope.len());
    for binder in telescope {
        encode_expr_to(out, &binder.ty);
    }
}

fn encode_smt_candidate_to(
    out: &mut Vec<u8>,
    candidate: &AdvancedMachineSmtCertificateCandidate,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_goal_to(out, &candidate.goal)?;
    out.push(candidate.solver.tag());
    out.push(candidate.logic.tag());
    encode_smt_problem_ref_to(out, &candidate.encoded_problem);
    out.push(candidate.certificate_format.tag());
    out.push(candidate.rule_registry_profile.tag());
    encode_smt_proof_payload_ref_to(out, &candidate.proof_payload);
    encode_smt_reconstruction_plan_to(out, &candidate.reconstruction_plan)?;
    Ok(())
}

fn encode_smt_problem_ref_to(out: &mut Vec<u8>, problem: &AdvancedMachineSmtProblemRef) {
    match problem {
        AdvancedMachineSmtProblemRef::Inline {
            problem_hash,
            encoding_hash,
            canonical_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, problem_hash);
            encode_hash_to(out, encoding_hash);
            encode_bytes_to(out, canonical_bytes);
        }
        AdvancedMachineSmtProblemRef::Artifact {
            path,
            file_hash,
            problem_hash,
            encoding_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, problem_hash);
            encode_hash_to(out, encoding_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
}

fn encode_smt_proof_payload_ref_to(out: &mut Vec<u8>, payload: &AdvancedMachineSmtProofPayloadRef) {
    match payload {
        AdvancedMachineSmtProofPayloadRef::Inline {
            payload_hash,
            canonical_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, payload_hash);
            encode_bytes_to(out, canonical_bytes);
        }
        AdvancedMachineSmtProofPayloadRef::Artifact {
            path,
            file_hash,
            payload_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, payload_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
}

fn encode_smt_encoded_problem_to(
    out: &mut Vec<u8>,
    problem: &AdvancedMachineSmtEncodedProblem,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    out.push(problem.encoder_version.tag());
    encode_hash_to(out, &problem.goal_fingerprint);
    out.push(problem.logic.tag());
    out.push(problem.command_profile.tag());
    encode_len_to(out, problem.commands.len());
    for command in &problem.commands {
        encode_smt_command_to(out, command)?;
    }
    Ok(())
}

fn encode_smt_command_to(
    out: &mut Vec<u8>,
    command: &AdvancedSmtEncodedCommand,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    out.push(command.phase.tag());
    encode_hash_to(out, &command.command_id);
    encode_smt_command_payload_to(out, &command.payload)?;
    Ok(())
}

fn encode_smt_command_payload_to(
    out: &mut Vec<u8>,
    payload: &AdvancedSmtCommandPayload,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match payload {
        AdvancedSmtCommandPayload::SortDecl { symbol, arity } => {
            out.push(0);
            encode_smt_symbol_to(out, symbol);
            encode_u32_to(out, *arity);
        }
        AdvancedSmtCommandPayload::FunctionDecl {
            symbol,
            args,
            result,
        } => {
            out.push(1);
            encode_smt_symbol_to(out, symbol);
            encode_len_to(out, args.len());
            for arg in args {
                encode_smt_sort_expr_to(out, arg);
            }
            encode_smt_sort_expr_to(out, result);
        }
        AdvancedSmtCommandPayload::DatatypeDecl {
            symbol,
            constructors,
        } => {
            out.push(2);
            encode_smt_symbol_to(out, symbol);
            encode_len_to(out, constructors.len());
            for constructor in constructors {
                encode_smt_datatype_constructor_to(out, constructor);
            }
        }
        AdvancedSmtCommandPayload::ContextAssumption {
            source_local_index,
            core_expr,
            encoded_expr,
        } => {
            out.push(3);
            encode_u32_to(out, *source_local_index);
            encode_expr_to(out, core_expr);
            encode_smt_expr_to(out, encoded_expr);
        }
        AdvancedSmtCommandPayload::TargetAssertion {
            core_expr,
            encoded_expr,
        } => {
            out.push(4);
            encode_expr_to(out, core_expr);
            encode_smt_expr_to(out, encoded_expr);
        }
        AdvancedSmtCommandPayload::FinalCheck => out.push(5),
    }
    Ok(())
}

fn encode_smt_symbol_to(out: &mut Vec<u8>, symbol: &AdvancedSmtSymbol) {
    encode_bytes_to(out, &symbol.ascii);
}

fn encode_smt_sort_expr_to(out: &mut Vec<u8>, sort: &AdvancedSmtSortExpr) {
    match sort {
        AdvancedSmtSortExpr::Bool => out.push(0),
        AdvancedSmtSortExpr::Int => out.push(1),
        AdvancedSmtSortExpr::BitVec { width } => {
            out.push(2);
            encode_u32_to(out, *width);
        }
        AdvancedSmtSortExpr::User { symbol, args } => {
            out.push(3);
            encode_smt_symbol_to(out, symbol);
            encode_len_to(out, args.len());
            for arg in args {
                encode_smt_sort_expr_to(out, arg);
            }
        }
    }
}

fn encode_smt_datatype_constructor_to(
    out: &mut Vec<u8>,
    constructor: &AdvancedSmtDatatypeConstructor,
) {
    encode_smt_symbol_to(out, &constructor.constructor);
    encode_len_to(out, constructor.selectors.len());
    for selector in &constructor.selectors {
        encode_smt_symbol_to(out, &selector.selector);
        encode_smt_sort_expr_to(out, &selector.sort);
    }
}

fn encode_smt_expr_to(out: &mut Vec<u8>, expr: &AdvancedSmtExpr) {
    match expr {
        AdvancedSmtExpr::Var { symbol, sort } => {
            out.push(0);
            encode_smt_symbol_to(out, symbol);
            encode_smt_sort_expr_to(out, sort);
        }
        AdvancedSmtExpr::BoolLit(value) => {
            out.push(1);
            out.push(u8::from(*value));
        }
        AdvancedSmtExpr::IntLit(value) => {
            out.push(2);
            encode_i128_to(out, *value);
        }
        AdvancedSmtExpr::BitVecLit { width, value } => {
            out.push(3);
            encode_u32_to(out, *width);
            encode_bytes_to(out, value);
        }
        AdvancedSmtExpr::App {
            symbol,
            args,
            result_sort,
        } => {
            out.push(4);
            encode_smt_symbol_to(out, symbol);
            encode_len_to(out, args.len());
            for arg in args {
                encode_smt_expr_to(out, arg);
            }
            encode_smt_sort_expr_to(out, result_sort);
        }
        AdvancedSmtExpr::BuiltinApp {
            op,
            args,
            result_sort,
        } => {
            out.push(5);
            encode_smt_builtin_op_to(out, *op);
            encode_len_to(out, args.len());
            for arg in args {
                encode_smt_expr_to(out, arg);
            }
            encode_smt_sort_expr_to(out, result_sort);
        }
        AdvancedSmtExpr::Not(inner) => {
            out.push(6);
            encode_smt_expr_to(out, inner);
        }
        AdvancedSmtExpr::And(args) => {
            out.push(7);
            encode_len_to(out, args.len());
            for arg in args {
                encode_smt_expr_to(out, arg);
            }
        }
        AdvancedSmtExpr::Or(args) => {
            out.push(8);
            encode_len_to(out, args.len());
            for arg in args {
                encode_smt_expr_to(out, arg);
            }
        }
        AdvancedSmtExpr::Eq(lhs, rhs) => {
            out.push(9);
            encode_smt_expr_to(out, lhs);
            encode_smt_expr_to(out, rhs);
        }
        AdvancedSmtExpr::Imp(lhs, rhs) => {
            out.push(10);
            encode_smt_expr_to(out, lhs);
            encode_smt_expr_to(out, rhs);
        }
        AdvancedSmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            out.push(11);
            encode_smt_expr_to(out, cond);
            encode_smt_expr_to(out, then_expr);
            encode_smt_expr_to(out, else_expr);
        }
    }
}

fn encode_smt_builtin_op_to(out: &mut Vec<u8>, op: AdvancedSmtBuiltinOp) {
    out.push(op.tag());
    if let AdvancedSmtBuiltinOp::BvExtract { high, low } = op {
        encode_u32_to(out, high);
        encode_u32_to(out, low);
    }
}

fn encode_smt_proof_node_table_to(
    out: &mut Vec<u8>,
    table: &AdvancedSmtProofNodeTable,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    out.push(table.certificate_format.tag());
    encode_len_to(out, table.nodes.len());
    for node in &table.nodes {
        encode_smt_proof_node_to(out, node);
    }
    Ok(())
}

fn encode_smt_proof_node_to(out: &mut Vec<u8>, node: &AdvancedSmtProofNode) {
    encode_u32_to(out, node.node_id);
    encode_hash_to(out, &node.rule_fingerprint);
    encode_len_to(out, node.premises.len());
    for premise in &node.premises {
        encode_u32_to(out, *premise);
    }
    encode_smt_conclusion_encoding_to(out, &node.conclusion_encoding);
}

fn encode_smt_conclusion_encoding_to(
    out: &mut Vec<u8>,
    conclusion: &AdvancedSmtConclusionEncoding,
) {
    out.push(conclusion.encoder_version.tag());
    out.push(conclusion.logic.tag());
    out.push(conclusion.command_profile.tag());
    encode_expr_to(out, &conclusion.core_expr);
    encode_smt_expr_to(out, &conclusion.encoded_expr);
}

fn encode_smt_reconstruction_plan_to(
    out: &mut Vec<u8>,
    plan: &AdvancedMachineSmtReconstructionPlan,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_global_ref_list_to(out, &plan.imported_theory_refs)?;
    encode_len_to(out, plan.steps.len());
    for step in &plan.steps {
        encode_smt_reconstruction_step_to(out, step)?;
    }
    encode_u32_to(out, plan.final_step);
    encode_expr_to(out, &plan.final_proof);
    Ok(())
}

fn encode_smt_reconstruction_step_to(
    out: &mut Vec<u8>,
    step: &AdvancedMachineSmtReconstructionStep,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_u32_to(out, step.step_id);
    encode_smt_reconstruction_rule_to(out, &step.rule)?;
    encode_len_to(out, step.payload_bindings.len());
    for binding in &step.payload_bindings {
        encode_hash_to(out, &binding.payload_hash);
        encode_u32_to(out, binding.node_id);
        encode_hash_to(out, &binding.rule_fingerprint);
    }
    encode_len_to(out, step.premises.len());
    for premise in &step.premises {
        encode_u32_to(out, *premise);
    }
    encode_expr_to(out, &step.conclusion);
    encode_expr_to(out, &step.proof);
    Ok(())
}

fn encode_smt_reconstruction_rule_to(
    out: &mut Vec<u8>,
    rule: &AdvancedSmtReconstructionRule,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match rule {
        AdvancedSmtReconstructionRule::PayloadNode {
            certificate_format,
            rule_fingerprint,
        } => {
            out.push(0);
            out.push(certificate_format.tag());
            encode_hash_to(out, rule_fingerprint);
        }
        AdvancedSmtReconstructionRule::LocalBookkeeping { kind } => {
            out.push(1);
            encode_smt_local_bookkeeping_rule_to(out, kind)?;
        }
    }
    Ok(())
}

fn encode_smt_local_bookkeeping_rule_to(
    out: &mut Vec<u8>,
    rule: &AdvancedSmtLocalBookkeepingRule,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match rule {
        AdvancedSmtLocalBookkeepingRule::ReorderPremises { permutation } => {
            out.push(0);
            encode_len_to(out, permutation.len());
            for index in permutation {
                encode_u32_to(out, *index);
            }
        }
        AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
            lemma,
            level_args,
            term_args,
        } => {
            out.push(1);
            encode_global_ref_to(out, lemma)?;
            encode_len_to(out, level_args.len());
            for level in level_args {
                encode_level_to(out, level);
            }
            encode_len_to(out, term_args.len());
            for term in term_args {
                encode_expr_to(out, term);
            }
        }
        AdvancedSmtLocalBookkeepingRule::ComposeProof {
            combinator,
            level_args,
            term_args,
        } => {
            out.push(2);
            encode_global_ref_to(out, combinator)?;
            encode_len_to(out, level_args.len());
            for level in level_args {
                encode_level_to(out, level);
            }
            encode_len_to(out, term_args.len());
            for term in term_args {
                encode_expr_to(out, term);
            }
        }
    }
    Ok(())
}

fn advanced_ai_smt_command_id_source_key(
    payload: &AdvancedSmtCommandPayload,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    match payload {
        AdvancedSmtCommandPayload::SortDecl { symbol, .. }
        | AdvancedSmtCommandPayload::DatatypeDecl { symbol, .. }
        | AdvancedSmtCommandPayload::FunctionDecl { symbol, .. } => {
            encode_smt_symbol_to(&mut out, symbol);
        }
        AdvancedSmtCommandPayload::ContextAssumption {
            source_local_index,
            core_expr,
            ..
        } => {
            encode_u32_to(&mut out, *source_local_index);
            encode_expr_to(&mut out, core_expr);
        }
        AdvancedSmtCommandPayload::TargetAssertion { .. }
        | AdvancedSmtCommandPayload::FinalCheck => {}
    }
    Ok(out)
}

fn encode_typeclass_resolution_plan_to(
    out: &mut Vec<u8>,
    plan: &AdvancedMachineTypeclassResolutionPlan,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_goal_to(out, &plan.goal)?;
    encode_len_to(out, plan.ordered_candidates.len());
    for candidate in &plan.ordered_candidates {
        encode_instance_candidate_to(out, candidate)?;
    }
    encode_u64_to(out, u64::from(plan.max_depth));
    encode_u64_to(out, u64::from(plan.max_nodes));
    Ok(())
}

fn encode_instance_candidate_to(
    out: &mut Vec<u8>,
    candidate: &AdvancedMachineInstanceCandidateRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_instance_target_to(out, &candidate.target)?;
    encode_option_i32_to(out, candidate.priority_hint);
    Ok(())
}

fn encode_instance_target_to(
    out: &mut Vec<u8>,
    target: &AdvancedMachineInstanceTargetRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match target {
        AdvancedMachineInstanceTargetRef::Imported { global_ref } => {
            out.push(0);
            encode_global_ref_to(out, global_ref)?;
        }
    }
    Ok(())
}

fn advanced_ai_instance_target_canonical_bytes(
    target: &AdvancedMachineInstanceTargetRef,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_instance_target_to(&mut out, target)?;
    Ok(out)
}

fn encode_theorem_graph_query_to(
    out: &mut Vec<u8>,
    query: &AdvancedMachineTheoremGraphQuery,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_hash_to(out, &query.env_fingerprint);
    encode_hash_to(out, &query.goal_fingerprint);
    encode_goal_to(out, &query.goal)?;
    encode_theorem_graph_snapshot_ref_to(out, &query.snapshot)?;
    encode_theorem_graph_query_features_ref_to(out, &query.query_features);
    out.push(query.ranking_profile.tag());
    encode_u64_to(out, u64::from(query.limit));
    Ok(())
}

fn encode_theorem_graph_snapshot_ref_to(
    out: &mut Vec<u8>,
    snapshot: &AdvancedMachineTheoremGraphSnapshotRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_hash_to(out, &snapshot.source_release_hash);
    out.push(snapshot.extractor_version.tag());
    match &snapshot.source {
        AdvancedMachineTheoremGraphSnapshotSource::Inline {
            graph_snapshot_hash,
            canonical_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, graph_snapshot_hash);
            encode_bytes_to(out, canonical_bytes);
        }
        AdvancedMachineTheoremGraphSnapshotSource::Artifact {
            path,
            file_hash,
            graph_snapshot_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, graph_snapshot_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
    Ok(())
}

fn encode_theorem_graph_query_features_ref_to(
    out: &mut Vec<u8>,
    features: &AdvancedMachineTheoremGraphQueryFeaturesRef,
) {
    match features {
        AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
            query_features_hash,
            canonical_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, query_features_hash);
            encode_bytes_to(out, canonical_bytes);
        }
        AdvancedMachineTheoremGraphQueryFeaturesRef::Artifact {
            path,
            file_hash,
            query_features_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, query_features_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
}

fn encode_theorem_graph_snapshot_to(
    out: &mut Vec<u8>,
    snapshot: &AdvancedMachineTheoremGraphSnapshot,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_hash_to(out, &snapshot.source_release_hash);
    out.push(snapshot.extractor_version.tag());
    encode_len_to(out, snapshot.nodes.len());
    for node in &snapshot.nodes {
        encode_theorem_graph_node_to(out, node)?;
    }
    encode_len_to(out, snapshot.edges.len());
    for edge in &snapshot.edges {
        encode_theorem_graph_edge_to(out, edge)?;
    }
    Ok(())
}

fn encode_theorem_graph_query_features_to(
    out: &mut Vec<u8>,
    features: &AdvancedMachineTheoremGraphQueryFeatures,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_hash_to(out, &features.env_fingerprint);
    encode_hash_to(out, &features.goal_fingerprint);
    out.push(features.feature_schema_version.tag());
    encode_len_to(out, features.features.len());
    for feature in &features.features {
        encode_theorem_graph_feature_to(out, feature);
    }
    Ok(())
}

fn encode_theorem_graph_result_to(out: &mut Vec<u8>, result: &AdvancedMachineTheoremGraphResult) {
    encode_len_to(out, result.entries.len());
    for entry in &result.entries {
        encode_theorem_graph_node_to(out, &entry.node)
            .expect("validated theorem graph result node names are canonical");
        encode_i64_to(out, entry.score.score_microunits);
    }
}

fn encode_theorem_graph_edge_to(
    out: &mut Vec<u8>,
    edge: &AdvancedMachineTheoremGraphEdge,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_theorem_graph_node_to(out, &edge.from)?;
    encode_theorem_graph_node_to(out, &edge.to)?;
    out.push(edge.kind.tag());
    Ok(())
}

fn encode_theorem_graph_node_to(
    out: &mut Vec<u8>,
    node: &AdvancedMachineTheoremGraphNodeRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_name_to(out, &node.module)?;
    encode_name_to(out, &node.name)?;
    encode_hash_to(out, &node.export_hash);
    encode_hash_to(out, &node.decl_certificate_hash);
    encode_hash_to(out, &node.type_hash);
    encode_hash_to(out, &node.certificate_hash);
    encode_hash_to(out, &node.decl_interface_hash);
    Ok(())
}

fn advanced_ai_theorem_graph_node_canonical_bytes(
    node: &AdvancedMachineTheoremGraphNodeRef,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut out = Vec::new();
    encode_theorem_graph_node_to(&mut out, node)?;
    Ok(out)
}

fn encode_theorem_graph_feature_to(
    out: &mut Vec<u8>,
    feature: &AdvancedMachineTheoremGraphFeature,
) {
    encode_bytes_to(out, &feature.key.namespace_ascii);
    encode_bytes_to(out, &feature.key.name_ascii);
    match &feature.value {
        AdvancedTheoremGraphFeatureValue::Bool(value) => {
            out.push(0);
            out.push(u8::from(*value));
        }
        AdvancedTheoremGraphFeatureValue::I64(value) => {
            out.push(1);
            encode_i64_to(out, *value);
        }
        AdvancedTheoremGraphFeatureValue::Hash(value) => {
            out.push(2);
            encode_hash_to(out, value);
        }
    }
}

fn encode_universe_repair_candidate_to(
    out: &mut Vec<u8>,
    candidate: &AdvancedUniverseRepairCandidate,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_option_goal_to(out, candidate.goal.as_ref())?;
    encode_expr_to(out, &candidate.target_expr);
    encode_len_to(out, candidate.instantiations.len());
    for patch in &candidate.instantiations {
        let mut item = Vec::new();
        encode_universe_instantiation_patch_to(&mut item, patch)?;
        encode_bytes_to(out, &item);
    }
    encode_len_to(out, candidate.constraint_hints.len());
    for hint in &candidate.constraint_hints {
        let mut item = Vec::new();
        encode_universe_constraint_hint_to(&mut item, hint);
        encode_bytes_to(out, &item);
    }
    encode_option_minimization_hint_to(out, candidate.minimization_hint);
    Ok(())
}

fn encode_universe_repair_candidate_outer_to(
    out: &mut Vec<u8>,
    candidate: &AdvancedUniverseRepairCandidateOuter,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_option_goal_to(out, candidate.goal.as_ref())?;
    encode_expr_to(out, &candidate.target_expr);
    encode_raw_bytes_list_to(out, &candidate.instantiation_items);
    encode_raw_bytes_list_to(out, &candidate.constraint_hint_items);
    encode_option_minimization_hint_to(out, candidate.minimization_hint);
    Ok(())
}

fn encode_option_goal_to(
    out: &mut Vec<u8>,
    goal: Option<&AdvancedAiGoal>,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match goal {
        Some(goal) => {
            out.push(1);
            encode_goal_to(out, goal)?;
        }
        None => out.push(0),
    }
    Ok(())
}

fn encode_goal_to(
    out: &mut Vec<u8>,
    goal: &AdvancedAiGoal,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_len_to(out, goal.universe_params.len());
    for param in &goal.universe_params {
        encode_string_to(out, param);
    }
    encode_len_to(out, goal.local_context.len());
    for local in &goal.local_context {
        encode_machine_local_decl_to(out, local);
    }
    encode_expr_to(out, &goal.target);
    Ok(())
}

fn encode_machine_local_decl_to(out: &mut Vec<u8>, local: &MachineLocalDecl) {
    encode_string_to(out, &local.name);
    encode_expr_to(out, &local.ty);
    match &local.value {
        Some(value) => {
            out.push(1);
            encode_expr_to(out, value);
        }
        None => out.push(0),
    }
}

fn encode_formalization_payload_to(
    out: &mut Vec<u8>,
    payload: &AdvancedMachineFormalizationCheckPayload,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_formalization_candidate_to(out, &payload.candidate)?;
    encode_option_formalization_intent_record_to(out, payload.intent_record.as_ref())?;
    Ok(())
}

fn encode_formalization_candidate_to(
    out: &mut Vec<u8>,
    candidate: &AdvancedMachineFormalizationCandidate,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_formalization_source_document_ref_to(out, &candidate.source_document);
    encode_formalization_claim_span_to(out, &candidate.claim_span);
    encode_machine_surface_term_to(out, &candidate.statement);
    encode_option_formalization_proof_candidate_to(
        out,
        candidate.optional_proof_candidate.as_ref(),
    )?;
    Ok(())
}

fn advanced_ai_machine_surface_term_canonical_bytes(
    statement: &AdvancedMachineSurfaceTerm,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_machine_surface_term_to(&mut out, statement);
    out
}

fn encode_machine_surface_term_to(out: &mut Vec<u8>, statement: &AdvancedMachineSurfaceTerm) {
    encode_len_to(out, statement.universe_params.len());
    for param in &statement.universe_params {
        encode_string_to(out, param);
    }
    encode_bytes_to(out, &statement.term_canonical_bytes);
}

fn encode_formalization_source_document_ref_to(
    out: &mut Vec<u8>,
    source: &AdvancedMachineFormalizationSourceDocumentRef,
) {
    match source {
        AdvancedMachineFormalizationSourceDocumentRef::Inline {
            source_document_hash,
            raw_utf8_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, source_document_hash);
            encode_bytes_to(out, raw_utf8_bytes);
        }
        AdvancedMachineFormalizationSourceDocumentRef::Artifact {
            path,
            file_hash,
            source_document_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, source_document_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
}

fn encode_formalization_claim_span_to(
    out: &mut Vec<u8>,
    span: &AdvancedMachineFormalizationClaimSpan,
) {
    encode_u64_to(out, span.start_byte);
    encode_u64_to(out, span.end_byte);
    encode_hash_to(out, &span.claim_span_hash);
}

fn encode_option_formalization_proof_candidate_to(
    out: &mut Vec<u8>,
    proof: Option<&AdvancedMachineFormalizationProofCandidate>,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match proof {
        Some(proof) => {
            out.push(1);
            encode_hash_to(out, &proof.candidate_statement_hash);
            encode_advanced_ai_tactic_candidate_to(out, &proof.tactic)?;
        }
        None => out.push(0),
    }
    Ok(())
}

fn encode_option_formalization_intent_record_to(
    out: &mut Vec<u8>,
    intent_record: Option<&AdvancedFormalizationIntentRecord>,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match intent_record {
        Some(intent_record) => {
            out.push(1);
            encode_hash_to(out, &intent_record.source_document_hash);
            encode_hash_to(out, &intent_record.claim_span_hash);
            encode_hash_to(out, &intent_record.candidate_statement_hash);
            encode_formalization_intent_status_to(out, &intent_record.status)?;
        }
        None => out.push(0),
    }
    Ok(())
}

fn encode_formalization_intent_status_to(
    out: &mut Vec<u8>,
    status: &AdvancedFormalizationIntentStatus,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match status {
        AdvancedFormalizationIntentStatus::Unreviewed => out.push(0),
        AdvancedFormalizationIntentStatus::Reviewed {
            reviewer,
            accepted_statement_hash,
        } => {
            out.push(1);
            encode_reviewer_id_to(out, reviewer);
            encode_hash_to(out, accepted_statement_hash);
        }
        AdvancedFormalizationIntentStatus::Rejected {
            reviewer,
            rejection_reason,
            rejection_reason_hash,
        } => {
            out.push(2);
            encode_reviewer_id_to(out, reviewer);
            encode_formalization_rejection_reason_ref_to(out, rejection_reason);
            encode_hash_to(out, rejection_reason_hash);
        }
    }
    Ok(())
}

fn encode_reviewer_id_to(out: &mut Vec<u8>, reviewer: &AdvancedReviewerId) {
    match reviewer {
        AdvancedReviewerId::Human { stable_id_ascii } => {
            out.push(0);
            encode_bytes_to(out, stable_id_ascii);
        }
        AdvancedReviewerId::System {
            system_id_ascii,
            actor_id_ascii,
        } => {
            out.push(1);
            encode_bytes_to(out, system_id_ascii);
            encode_bytes_to(out, actor_id_ascii);
        }
    }
}

fn encode_formalization_rejection_reason_ref_to(
    out: &mut Vec<u8>,
    reason: &AdvancedMachineFormalizationRejectionReasonRef,
) {
    match reason {
        AdvancedMachineFormalizationRejectionReasonRef::Inline {
            rejection_reason_hash,
            raw_utf8_bytes,
        } => {
            out.push(0);
            encode_hash_to(out, rejection_reason_hash);
            encode_bytes_to(out, raw_utf8_bytes);
        }
        AdvancedMachineFormalizationRejectionReasonRef::Artifact {
            path,
            file_hash,
            rejection_reason_hash,
            size_bytes,
        } => {
            out.push(1);
            encode_string_to(out, path);
            encode_hash_to(out, file_hash);
            encode_hash_to(out, rejection_reason_hash);
            encode_u64_to(out, *size_bytes);
        }
    }
}

fn encode_advanced_ai_tactic_candidate_to(
    out: &mut Vec<u8>,
    tactic: &MachineTacticCandidate,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match tactic {
        MachineTacticCandidate::Exact { term } => {
            out.push(0);
            encode_string_to(out, &term.source);
        }
        MachineTacticCandidate::Intro { name } => {
            out.push(1);
            encode_string_to(out, name);
        }
        MachineTacticCandidate::Apply {
            head,
            universe_args,
            args,
        } => {
            out.push(2);
            encode_advanced_ai_tactic_head_to(out, head)?;
            encode_len_to(out, universe_args.len());
            for level in universe_args {
                encode_level_to(out, level);
            }
            encode_len_to(out, args.len());
            for arg in args {
                encode_advanced_ai_apply_arg_to(out, arg);
            }
        }
        MachineTacticCandidate::Rewrite {
            rule,
            direction,
            site,
        } => {
            out.push(3);
            encode_advanced_ai_candidate_rewrite_rule_to(out, rule)?;
            encode_advanced_ai_rewrite_direction_to(out, *direction);
            encode_advanced_ai_rewrite_site_to(out, *site);
        }
        MachineTacticCandidate::SimpLite { rules } => {
            out.push(4);
            encode_len_to(out, rules.len());
            for rule in rules {
                encode_advanced_ai_simp_rule_ref_to(out, rule)?;
            }
        }
        MachineTacticCandidate::Smt { lemmas } => {
            out.push(6);
            encode_len_to(out, lemmas.len());
            for lemma in lemmas {
                encode_advanced_ai_tactic_head_to(out, &lemma.head)?;
                encode_len_to(out, lemma.universe_args.len());
                for level in &lemma.universe_args {
                    encode_level_to(out, level);
                }
            }
        }
        MachineTacticCandidate::InductionNat { local_name } => {
            out.push(5);
            encode_string_to(out, local_name);
        }
        MachineTacticCandidate::Constructor(_)
        | MachineTacticCandidate::Cases(_)
        | MachineTacticCandidate::GeneralInduction(_)
        | MachineTacticCandidate::Refine(_)
        | MachineTacticCandidate::Have(_)
        | MachineTacticCandidate::Suffices(_)
        | MachineTacticCandidate::Specialize(_)
        | MachineTacticCandidate::Revert(_)
        | MachineTacticCandidate::Generalize(_)
        | MachineTacticCandidate::Change(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Congr(_)
        | MachineTacticCandidate::Subst(_)
        | MachineTacticCandidate::Contradiction(_)
        | MachineTacticCandidate::FiniteDecide
        | MachineTacticCandidate::Omega
        | MachineTacticCandidate::Ring
        | MachineTacticCandidate::Bitblast => {
            out.push(7);
            encode_string_to(
                out,
                &crate::ai_search::ai_search_candidate_payload_json(tactic),
            );
        }
    }
    Ok(())
}

fn encode_advanced_ai_candidate_rewrite_rule_to(
    out: &mut Vec<u8>,
    rule: &CandidateRewriteRuleRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_advanced_ai_tactic_head_to(out, &rule.head)?;
    encode_len_to(out, rule.universe_args.len());
    for level in &rule.universe_args {
        encode_level_to(out, level);
    }
    encode_len_to(out, rule.args.len());
    for arg in &rule.args {
        encode_advanced_ai_apply_arg_to(out, arg);
    }
    Ok(())
}

fn encode_advanced_ai_tactic_head_to(
    out: &mut Vec<u8>,
    head: &TacticHead,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    match head {
        TacticHead::Imported {
            name,
            decl_interface_hash,
        } => {
            out.push(0);
            encode_name_to(out, name)?;
            encode_hash_to(out, decl_interface_hash);
        }
        TacticHead::CurrentModule {
            name,
            decl_interface_hash,
        } => {
            out.push(1);
            encode_name_to(out, name)?;
            encode_hash_to(out, decl_interface_hash);
        }
        TacticHead::Local { name } => {
            out.push(2);
            encode_string_to(out, name);
        }
    }
    Ok(())
}

fn encode_advanced_ai_apply_arg_to(out: &mut Vec<u8>, arg: &CandidateApplyArg) {
    match arg {
        CandidateApplyArg::Term(term) => {
            out.push(0);
            encode_string_to(out, &term.source);
        }
        CandidateApplyArg::Subgoal { name_hint } => {
            out.push(1);
            match name_hint {
                Some(name_hint) => {
                    out.push(1);
                    encode_string_to(out, name_hint);
                }
                None => out.push(0),
            }
        }
        CandidateApplyArg::InferFromTarget => out.push(2),
    }
}

fn encode_advanced_ai_simp_rule_ref_to(
    out: &mut Vec<u8>,
    rule: &SimpRuleRef,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_name_to(out, &rule.name)?;
    encode_hash_to(out, &rule.decl_interface_hash);
    encode_advanced_ai_rewrite_direction_to(out, rule.direction);
    Ok(())
}

fn encode_advanced_ai_rewrite_direction_to(out: &mut Vec<u8>, direction: RewriteDirection) {
    out.push(match direction {
        RewriteDirection::Forward => 0,
        RewriteDirection::Backward => 1,
    });
}

fn encode_advanced_ai_rewrite_site_to(out: &mut Vec<u8>, site: RewriteSite) {
    out.push(match site {
        RewriteSite::EqTargetLeft => 0,
        RewriteSite::EqTargetRight => 1,
    });
}

fn encode_universe_instantiation_patch_to(
    out: &mut Vec<u8>,
    patch: &AdvancedUniverseInstantiationPatch,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    encode_path_steps_to(out, &patch.occurrence.path);
    encode_global_ref_to(out, &patch.occurrence.expected_ref)?;
    encode_len_to(out, patch.explicit_level_args.len());
    for level in &patch.explicit_level_args {
        encode_level_to(out, level);
    }
    Ok(())
}

fn encode_universe_constraint_hint_to(out: &mut Vec<u8>, hint: &AdvancedUniverseConstraintHint) {
    encode_universe_constraint_to(out, &hint.constraint);
    out.push(match hint.reason {
        AdvancedUniverseConstraintHintReason::KernelDiagnostic => 0,
        AdvancedUniverseConstraintHintReason::RepairCandidate => 1,
        AdvancedUniverseConstraintHintReason::MinimizationExplanation => 2,
    });
}

fn encode_universe_constraint_to(out: &mut Vec<u8>, constraint: &AdvancedUniverseConstraint) {
    encode_level_to(out, &constraint.lhs);
    out.push(match constraint.relation {
        AdvancedUniverseConstraintRelation::Le => 0,
        AdvancedUniverseConstraintRelation::Eq => 1,
    });
    encode_level_to(out, &constraint.rhs);
}

fn encode_option_minimization_hint_to(
    out: &mut Vec<u8>,
    hint: Option<AdvancedUniverseMinimizationHint>,
) {
    match hint {
        Some(hint) => {
            out.push(1);
            out.push(match hint {
                AdvancedUniverseMinimizationHint::KernelDefault => 0,
                AdvancedUniverseMinimizationHint::PreferLowerLevels => 1,
                AdvancedUniverseMinimizationHint::PreferExistingExplicitArgs => 2,
            });
        }
        None => out.push(0),
    }
}

fn encode_path_steps_to(out: &mut Vec<u8>, path: &[AdvancedMachineExprPathStep]) {
    encode_len_to(out, path.len());
    for step in path {
        out.push(match step {
            AdvancedMachineExprPathStep::AppFun => 0,
            AdvancedMachineExprPathStep::AppArg => 1,
            AdvancedMachineExprPathStep::LamType => 2,
            AdvancedMachineExprPathStep::LamBody => 3,
            AdvancedMachineExprPathStep::PiDomain => 4,
            AdvancedMachineExprPathStep::PiCodomain => 5,
            AdvancedMachineExprPathStep::LetType => 6,
            AdvancedMachineExprPathStep::LetValue => 7,
            AdvancedMachineExprPathStep::LetBody => 8,
        });
    }
}

fn encode_expr_to(out: &mut Vec<u8>, expr: &Expr) {
    match expr {
        Expr::Sort(level) => {
            out.push(0);
            encode_level_to(out, level);
        }
        Expr::BVar(index) => {
            out.push(1);
            encode_u64_to(out, u64::from(*index));
        }
        Expr::Const { name, levels } => {
            out.push(2);
            encode_string_to(out, name);
            encode_len_to(out, levels.len());
            for level in levels {
                encode_level_to(out, level);
            }
        }
        Expr::App(fun, arg) => {
            out.push(3);
            encode_expr_to(out, fun);
            encode_expr_to(out, arg);
        }
        Expr::Lam { ty, body, .. } => {
            out.push(4);
            encode_expr_to(out, ty);
            encode_expr_to(out, body);
        }
        Expr::Pi { ty, body, .. } => {
            out.push(5);
            encode_expr_to(out, ty);
            encode_expr_to(out, body);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            out.push(6);
            encode_expr_to(out, ty);
            encode_expr_to(out, value);
            encode_expr_to(out, body);
        }
    }
}

fn encode_level_to(out: &mut Vec<u8>, level: &Level) {
    match npa_kernel::level::normalize_level(level.clone()) {
        Level::Zero => out.push(0),
        Level::Succ(inner) => {
            out.push(1);
            encode_level_to(out, &inner);
        }
        Level::Max(lhs, rhs) => {
            out.push(2);
            encode_level_to(out, &lhs);
            encode_level_to(out, &rhs);
        }
        Level::IMax(lhs, rhs) => {
            out.push(3);
            encode_level_to(out, &lhs);
            encode_level_to(out, &rhs);
        }
        Level::Param(name) => {
            out.push(4);
            encode_string_to(out, &name);
        }
    }
}

fn encode_raw_bytes_list_to(out: &mut Vec<u8>, items: &[Vec<u8>]) {
    encode_len_to(out, items.len());
    for item in items {
        encode_bytes_to(out, item);
    }
}

fn decode_candidate_envelope(
    input: &[u8],
) -> std::result::Result<AdvancedAiCandidateEnvelope, DecodeError> {
    let mut decoder = Decoder::new(input);
    let profile_version =
        AdvancedAiProfileVersion::from_tag(decoder.u8()?).ok_or(DecodeError::Malformed)?;
    let task_kind = AdvancedAiTaskKind::from_tag(decoder.u8()?).ok_or(DecodeError::Malformed)?;
    let target = decoder.target()?;
    let imports = decoder.import_identities()?;
    let options = decoder.options_ref()?;
    let payload = decoder.bytes()?;
    decoder.done()?;

    let envelope = AdvancedAiCandidateEnvelope {
        profile_version,
        task_kind,
        target,
        imports,
        options,
        payload,
    };
    let encoded = advanced_ai_candidate_envelope_canonical_bytes(&envelope)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(envelope)
}

fn decode_options(input: &[u8]) -> std::result::Result<AdvancedAiOptions, DecodeError> {
    let mut decoder = Decoder::new(input);
    let schema_version =
        AdvancedAiOptionsVersion::from_tag(decoder.u8()?).ok_or(DecodeError::Malformed)?;
    let independent_checker = AdvancedIndependentCheckerOptions {
        profile: AdvancedIndependentCheckerProfile::from_tag(decoder.u8()?)
            .ok_or(DecodeError::Malformed)?,
    };
    let approved_nested_type_constructors = decoder.global_ref_list()?;
    ensure_sorted_global_refs(&approved_nested_type_constructors)?;
    let class_declarations = decoder.global_ref_list()?;
    ensure_sorted_global_refs(&class_declarations)?;
    let smt = decoder.option_smt()?;
    let formalization = decoder.option_formalization()?;
    decoder.done()?;

    let options = AdvancedAiOptions {
        schema_version,
        independent_checker,
        advanced_inductive: AdvancedInductiveOptions {
            approved_nested_type_constructors,
        },
        typeclass: AdvancedTypeclassOptions { class_declarations },
        smt,
        formalization,
    };
    let encoded =
        advanced_ai_options_canonical_bytes(&options).map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(options)
}

fn decode_machine_tactic_options(input: &[u8]) -> std::result::Result<MachineTacticOptions, ()> {
    let mut decoder = MachineTacticDecoder::new(input);
    decoder.tag("npa.machine-tactic.tactic-options.v1")?;
    let rule_len = decoder.uvar()?;
    if rule_len > MAX_ADVANCED_AI_FORMALIZATION_TACTIC_ITEMS {
        return Err(());
    }
    let mut simp_rules = Vec::new();
    for _ in 0..rule_len {
        simp_rules.push(decoder.simp_rule_ref()?);
    }
    let options = MachineTacticOptions {
        simp_rules,
        eq_family: decoder.option_eq_family_ref()?,
        nat_family: decoder.option_nat_family_ref()?,
        max_simp_rewrite_steps: decoder.uvar()?,
        max_open_goals: decoder.usize()?,
        max_metas: decoder.usize()?,
    };
    decoder.done()?;
    if machine_tactic_options_canonical_bytes(&options) != input {
        return Err(());
    }
    Ok(options)
}

fn decode_machine_tactic_budget(input: &[u8]) -> std::result::Result<TacticBudget, ()> {
    let mut decoder = MachineTacticDecoder::new(input);
    decoder.tag("npa.machine-tactic.tactic-budget.v1")?;
    let budget = TacticBudget {
        max_tactic_steps: decoder.uvar()?,
        max_whnf_steps: decoder.uvar()?,
        max_conversion_steps: decoder.uvar()?,
        max_rewrite_steps: decoder.uvar()?,
        max_meta_allocations: decoder.uvar()?,
        max_expr_nodes: decoder.uvar()?,
    };
    decoder.done()?;
    if tactic_budget_canonical_bytes(budget) != input {
        return Err(());
    }
    Ok(budget)
}

struct MachineTacticDecoder<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> MachineTacticDecoder<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self { input, pos: 0 }
    }

    fn done(&self) -> std::result::Result<(), ()> {
        if self.pos == self.input.len() {
            Ok(())
        } else {
            Err(())
        }
    }

    fn u8(&mut self) -> std::result::Result<u8, ()> {
        let byte = *self.input.get(self.pos).ok_or(())?;
        self.pos += 1;
        Ok(byte)
    }

    fn uvar(&mut self) -> std::result::Result<u64, ()> {
        let mut shift = 0u32;
        let mut value = 0u64;
        loop {
            if shift >= 64 {
                return Err(());
            }
            let byte = self.u8()?;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
            shift += 7;
        }
    }

    fn usize(&mut self) -> std::result::Result<usize, ()> {
        usize::try_from(self.uvar()?).map_err(|_| ())
    }

    fn bytes(&mut self) -> std::result::Result<Vec<u8>, ()> {
        let len = usize::try_from(self.uvar()?).map_err(|_| ())?;
        let end = self.pos.checked_add(len).ok_or(())?;
        let bytes = self.input.get(self.pos..end).ok_or(())?;
        self.pos = end;
        Ok(bytes.to_vec())
    }

    fn string(&mut self) -> std::result::Result<String, ()> {
        let bytes = self.bytes()?;
        if bytes.len() as u64 > MAX_STRING_BYTES {
            return Err(());
        }
        String::from_utf8(bytes).map_err(|_| ())
    }

    fn tag(&mut self, expected: &str) -> std::result::Result<(), ()> {
        if self.string()? == expected {
            Ok(())
        } else {
            Err(())
        }
    }

    fn hash(&mut self) -> std::result::Result<Hash, ()> {
        let end = self.pos.checked_add(32).ok_or(())?;
        let bytes = self.input.get(self.pos..end).ok_or(())?;
        self.pos = end;
        Ok(bytes.try_into().unwrap())
    }

    fn name(&mut self) -> std::result::Result<Name, ()> {
        let len = self.uvar()?;
        if len == 0 || len > MAX_NAME_COMPONENTS {
            return Err(());
        }
        let mut components = Vec::new();
        for _ in 0..len {
            components.push(self.string()?);
        }
        let name = Name(components);
        if name.is_canonical() {
            Ok(name)
        } else {
            Err(())
        }
    }

    fn rewrite_direction(&mut self) -> std::result::Result<RewriteDirection, ()> {
        match self.u8()? {
            0x00 => Ok(RewriteDirection::Forward),
            0x01 => Ok(RewriteDirection::Backward),
            _ => Err(()),
        }
    }

    fn simp_rule_ref(&mut self) -> std::result::Result<SimpRuleRef, ()> {
        Ok(SimpRuleRef {
            name: self.name()?,
            decl_interface_hash: self.hash()?,
            direction: self.rewrite_direction()?,
        })
    }

    fn option_eq_family_ref(&mut self) -> std::result::Result<Option<EqFamilyRef>, ()> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(EqFamilyRef {
                eq_name: self.name()?,
                eq_interface_hash: self.hash()?,
                refl_name: self.name()?,
                refl_interface_hash: self.hash()?,
                rec_name: self.name()?,
                rec_interface_hash: self.hash()?,
            })),
            _ => Err(()),
        }
    }

    fn option_nat_family_ref(&mut self) -> std::result::Result<Option<NatFamilyRef>, ()> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(NatFamilyRef {
                nat_name: self.name()?,
                nat_interface_hash: self.hash()?,
                zero_name: self.name()?,
                zero_interface_hash: self.hash()?,
                succ_name: self.name()?,
                succ_interface_hash: self.hash()?,
                rec_name: self.name()?,
                rec_interface_hash: self.hash()?,
            })),
            _ => Err(()),
        }
    }
}

struct AdvancedInductiveDecodeBudget {
    expr_nodes: u64,
    level_nodes: u64,
}

impl AdvancedInductiveDecodeBudget {
    fn new() -> Self {
        Self {
            expr_nodes: 0,
            level_nodes: 0,
        }
    }

    fn spend_expr(&mut self) -> std::result::Result<(), DecodeError> {
        self.expr_nodes = self
            .expr_nodes
            .checked_add(1)
            .ok_or(DecodeError::Malformed)?;
        if self.expr_nodes > MAX_ADVANCED_AI_INDUCTIVE_EXPR_NODES {
            return Err(DecodeError::Malformed);
        }
        Ok(())
    }

    fn spend_level(&mut self) -> std::result::Result<(), DecodeError> {
        self.level_nodes = self
            .level_nodes
            .checked_add(1)
            .ok_or(DecodeError::Malformed)?;
        if self.level_nodes > MAX_ADVANCED_AI_INDUCTIVE_LEVEL_NODES {
            return Err(DecodeError::Malformed);
        }
        Ok(())
    }
}

struct AdvancedSmtDecodeBudget {
    core: AdvancedInductiveDecodeBudget,
    smt_expr_nodes: u64,
    smt_sort_nodes: u64,
}

impl AdvancedSmtDecodeBudget {
    fn new() -> Self {
        Self {
            core: AdvancedInductiveDecodeBudget::new(),
            smt_expr_nodes: 0,
            smt_sort_nodes: 0,
        }
    }

    fn spend_smt_expr(&mut self) -> std::result::Result<(), DecodeError> {
        self.smt_expr_nodes = self
            .smt_expr_nodes
            .checked_add(1)
            .ok_or(DecodeError::Malformed)?;
        if self.smt_expr_nodes > MAX_ADVANCED_AI_SMT_ITEMS {
            return Err(DecodeError::Malformed);
        }
        Ok(())
    }

    fn spend_smt_sort(&mut self) -> std::result::Result<(), DecodeError> {
        self.smt_sort_nodes = self
            .smt_sort_nodes
            .checked_add(1)
            .ok_or(DecodeError::Malformed)?;
        if self.smt_sort_nodes > MAX_ADVANCED_AI_SMT_ITEMS {
            return Err(DecodeError::Malformed);
        }
        Ok(())
    }
}

fn decode_inductive_proposal(
    input: &[u8],
) -> std::result::Result<AdvancedMachineInductiveProposal, DecodeError> {
    let mut decoder = Decoder::new(input);
    let mut budget = AdvancedInductiveDecodeBudget::new();
    let block_name = decoder.option_name()?;
    let expected_decl_hash = decoder.option_hash()?;
    let universe_params = decoder.string_list_with_cap(MAX_ADVANCED_AI_INDUCTIVE_ITEMS)?;
    let inductive_len = decoder.u64()?;
    if inductive_len > MAX_ADVANCED_AI_INDUCTIVE_ITEMS {
        return Err(DecodeError::Malformed);
    }
    let mut inductives = Vec::new();
    for _ in 0..inductive_len {
        inductives.push(decoder.inductive_family(&mut budget)?);
    }
    decoder.done()?;
    let proposal = AdvancedMachineInductiveProposal {
        block_name,
        expected_decl_hash,
        universe_params,
        inductives,
    };
    let encoded = advanced_ai_inductive_proposal_canonical_bytes(&proposal)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(proposal)
}

fn decode_smt_candidate(
    input: &[u8],
) -> std::result::Result<AdvancedMachineSmtCertificateCandidate, DecodeError> {
    let mut decoder = Decoder::new(input);
    let mut budget = AdvancedSmtDecodeBudget::new();
    let candidate = decoder.smt_candidate(&mut budget)?;
    decoder.done()?;
    let encoded = advanced_ai_smt_candidate_canonical_bytes(&candidate)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(candidate)
}

fn decode_smt_encoded_problem(
    input: &[u8],
) -> std::result::Result<AdvancedMachineSmtEncodedProblem, DecodeError> {
    let mut decoder = Decoder::new(input);
    let mut budget = AdvancedSmtDecodeBudget::new();
    let problem = decoder.smt_encoded_problem(&mut budget)?;
    decoder.done()?;
    let encoded =
        advanced_ai_smt_problem_canonical_bytes(&problem).map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(problem)
}

fn decode_smt_proof_node_table(
    input: &[u8],
) -> std::result::Result<AdvancedSmtProofNodeTable, DecodeError> {
    let mut decoder = Decoder::new(input);
    let mut budget = AdvancedSmtDecodeBudget::new();
    let table = decoder.smt_proof_node_table(&mut budget)?;
    decoder.done()?;
    let encoded = advanced_ai_smt_proof_payload_canonical_bytes(&table)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(table)
}

fn decode_typeclass_resolution_plan(
    input: &[u8],
) -> std::result::Result<AdvancedMachineTypeclassResolutionPlan, DecodeError> {
    let mut decoder = Decoder::new(input);
    let plan = decoder.typeclass_resolution_plan()?;
    decoder.done()?;
    let encoded = advanced_ai_typeclass_resolution_plan_canonical_bytes(&plan)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(plan)
}

fn decode_theorem_graph_query(
    input: &[u8],
) -> std::result::Result<AdvancedMachineTheoremGraphQuery, DecodeError> {
    let mut decoder = Decoder::new(input);
    let query = decoder.theorem_graph_query()?;
    decoder.done()?;
    let encoded = advanced_ai_theorem_graph_query_canonical_bytes(&query)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(query)
}

fn decode_theorem_graph_snapshot(
    input: &[u8],
) -> std::result::Result<AdvancedMachineTheoremGraphSnapshot, DecodeError> {
    let mut decoder = Decoder::new(input);
    let snapshot = decoder.theorem_graph_snapshot()?;
    decoder.done()?;
    let encoded = advanced_ai_theorem_graph_snapshot_canonical_bytes(&snapshot)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(snapshot)
}

fn decode_theorem_graph_query_features(
    input: &[u8],
) -> std::result::Result<AdvancedMachineTheoremGraphQueryFeatures, DecodeError> {
    let mut decoder = Decoder::new(input);
    let features = decoder.theorem_graph_query_features()?;
    decoder.done()?;
    let encoded = advanced_ai_theorem_graph_query_features_canonical_bytes(&features)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(features)
}

fn decode_formalization_payload(
    input: &[u8],
) -> std::result::Result<AdvancedMachineFormalizationCheckPayload, DecodeError> {
    let mut decoder = Decoder::new(input);
    let payload = decoder.formalization_payload()?;
    decoder.done()?;
    let encoded = advanced_ai_formalization_payload_canonical_bytes(&payload)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(payload)
}

fn decode_universe_repair_candidate_outer(
    input: &[u8],
) -> std::result::Result<AdvancedUniverseRepairCandidateOuter, DecodeError> {
    let mut decoder = Decoder::new(input);
    let goal = decoder.option_goal()?;
    let target_expr = decoder.expr()?;
    let instantiation_items = decoder.bytes_list_with_cap(MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS)?;
    let constraint_hint_items =
        decoder.bytes_list_with_cap(MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS)?;
    let minimization_hint = decoder.option_minimization_hint()?;
    decoder.done()?;

    let candidate = AdvancedUniverseRepairCandidateOuter {
        goal,
        target_expr,
        instantiation_items,
        constraint_hint_items,
        minimization_hint,
    };
    let mut encoded = Vec::new();
    encode_universe_repair_candidate_outer_to(&mut encoded, &candidate)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(candidate)
}

fn decode_universe_instantiation_patch(
    input: &[u8],
) -> std::result::Result<AdvancedUniverseInstantiationPatch, DecodeError> {
    let mut decoder = Decoder::new(input);
    let path = decoder.path_steps()?;
    let expected_ref = decoder.global_ref()?;
    let explicit_level_args = decoder.level_list_with_cap(MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS)?;
    decoder.done()?;
    let patch = AdvancedUniverseInstantiationPatch {
        occurrence: AdvancedMachineExprOccurrence { path, expected_ref },
        explicit_level_args,
    };
    let mut encoded = Vec::new();
    encode_universe_instantiation_patch_to(&mut encoded, &patch)
        .map_err(|_| DecodeError::Malformed)?;
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(patch)
}

fn decode_universe_constraint_hint(
    input: &[u8],
) -> std::result::Result<AdvancedUniverseConstraintHint, DecodeError> {
    let mut decoder = Decoder::new(input);
    let constraint = decoder.universe_constraint()?;
    let reason = decoder.constraint_hint_reason()?;
    decoder.done()?;
    let hint = AdvancedUniverseConstraintHint { constraint, reason };
    let mut encoded = Vec::new();
    encode_universe_constraint_hint_to(&mut encoded, &hint);
    if encoded != input {
        return Err(DecodeError::Malformed);
    }
    Ok(hint)
}

struct Decoder<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> Decoder<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self { input, pos: 0 }
    }

    fn done(&self) -> std::result::Result<(), DecodeError> {
        if self.pos == self.input.len() {
            Ok(())
        } else {
            Err(DecodeError::Malformed)
        }
    }

    fn u8(&mut self) -> std::result::Result<u8, DecodeError> {
        let value = *self.input.get(self.pos).ok_or(DecodeError::Malformed)?;
        self.pos += 1;
        Ok(value)
    }

    fn u64(&mut self) -> std::result::Result<u64, DecodeError> {
        let end = self.pos.checked_add(8).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(u64::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn u32(&mut self) -> std::result::Result<u32, DecodeError> {
        let end = self.pos.checked_add(4).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(u32::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn i32(&mut self) -> std::result::Result<i32, DecodeError> {
        let end = self.pos.checked_add(4).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(i32::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn i64(&mut self) -> std::result::Result<i64, DecodeError> {
        let end = self.pos.checked_add(8).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(i64::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn i128(&mut self) -> std::result::Result<i128, DecodeError> {
        let end = self.pos.checked_add(16).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(i128::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn hash(&mut self) -> std::result::Result<Hash, DecodeError> {
        let end = self.pos.checked_add(32).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(bytes.try_into().unwrap())
    }

    fn bytes(&mut self) -> std::result::Result<Vec<u8>, DecodeError> {
        let len = usize::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        let end = self.pos.checked_add(len).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(bytes.to_vec())
    }

    fn bytes_with_cap(
        &mut self,
        cap: usize,
        cap_error: DecodeError,
    ) -> std::result::Result<Vec<u8>, DecodeError> {
        let len = self.u64()?;
        if usize::try_from(len).map(|len| len > cap).unwrap_or(true) {
            return Err(cap_error);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let end = self.pos.checked_add(len).ok_or(DecodeError::Malformed)?;
        let bytes = self
            .input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(bytes.to_vec())
    }

    fn skip_bytes(&mut self) -> std::result::Result<(), DecodeError> {
        let len = usize::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        self.skip_raw_bytes(len)
    }

    fn skip_string(&mut self) -> std::result::Result<(), DecodeError> {
        let len = usize::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        if len as u64 > MAX_STRING_BYTES {
            return Err(DecodeError::Malformed);
        }
        self.skip_raw_bytes(len)
    }

    fn skip_raw_bytes(&mut self, len: usize) -> std::result::Result<(), DecodeError> {
        let end = self.pos.checked_add(len).ok_or(DecodeError::Malformed)?;
        self.input
            .get(self.pos..end)
            .ok_or(DecodeError::Malformed)?;
        self.pos = end;
        Ok(())
    }

    fn bytes_list_with_cap(&mut self, cap: u64) -> std::result::Result<Vec<Vec<u8>>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut items = Vec::new();
        for _ in 0..len {
            items.push(self.bytes()?);
        }
        Ok(items)
    }

    fn string(&mut self) -> std::result::Result<String, DecodeError> {
        let bytes = self.bytes()?;
        if bytes.len() as u64 > MAX_STRING_BYTES {
            return Err(DecodeError::Malformed);
        }
        String::from_utf8(bytes).map_err(|_| DecodeError::Malformed)
    }

    fn name(&mut self) -> std::result::Result<Name, DecodeError> {
        let len = self.u64()?;
        if len == 0 || len > MAX_NAME_COMPONENTS {
            return Err(DecodeError::Malformed);
        }
        let mut components = Vec::new();
        for _ in 0..len {
            let component = self.string()?;
            components.push(component);
        }
        let name = Name(components);
        if name.is_canonical() {
            Ok(name)
        } else {
            Err(DecodeError::Malformed)
        }
    }

    fn option_name(&mut self) -> std::result::Result<Option<Name>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.name()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn target(&mut self) -> std::result::Result<AdvancedAiTarget, DecodeError> {
        Ok(AdvancedAiTarget {
            env_fingerprint: self.hash()?,
            target_decl_hash: self.option_hash()?,
            goal_fingerprint: self.option_hash()?,
        })
    }

    fn option_hash(&mut self) -> std::result::Result<Option<Hash>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.hash()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn string_list_with_cap(&mut self, cap: u64) -> std::result::Result<Vec<String>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut values = Vec::new();
        for _ in 0..len {
            values.push(self.string()?);
        }
        Ok(values)
    }

    fn import_identities(
        &mut self,
    ) -> std::result::Result<Vec<AdvancedImportIdentity>, DecodeError> {
        let len = usize::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        let mut imports = Vec::new();
        for _ in 0..len {
            imports.push(AdvancedImportIdentity {
                module: self.name()?,
                export_hash: self.hash()?,
                certificate_hash: self.hash()?,
            });
        }
        Ok(imports)
    }

    fn options_ref(&mut self) -> std::result::Result<AdvancedAiOptionsRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedAiOptionsRef::Inline {
                options_hash: self.hash()?,
                canonical_bytes: self.bytes()?,
            }),
            1 => Ok(AdvancedAiOptionsRef::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                options_hash: self.hash()?,
                size_bytes: self.u64()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_goal(&mut self) -> std::result::Result<Option<AdvancedAiGoal>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.goal()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn goal(&mut self) -> std::result::Result<AdvancedAiGoal, DecodeError> {
        let param_len = self.u64()?;
        if param_len > MAX_NAME_COMPONENTS {
            return Err(DecodeError::Malformed);
        }
        let mut universe_params = Vec::new();
        for _ in 0..param_len {
            universe_params.push(self.string()?);
        }
        let local_len = self.u64()?;
        if local_len > MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let mut local_context = Vec::new();
        for _ in 0..local_len {
            local_context.push(self.machine_local_decl()?);
        }
        let target = self.expr()?;
        Ok(AdvancedAiGoal {
            universe_params,
            local_context,
            target,
        })
    }

    fn machine_local_decl(&mut self) -> std::result::Result<MachineLocalDecl, DecodeError> {
        let name = self.string()?;
        let ty = self.expr()?;
        let value = match self.u8()? {
            0 => None,
            1 => Some(self.expr()?),
            _ => return Err(DecodeError::Malformed),
        };
        Ok(MachineLocalDecl { name, ty, value })
    }

    fn expr(&mut self) -> std::result::Result<Expr, DecodeError> {
        match self.u8()? {
            0 => Ok(Expr::sort(self.level()?)),
            1 => {
                let index = u32::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
                Ok(Expr::bvar(index))
            }
            2 => {
                let name = self.string()?;
                let levels = self.level_list_with_cap(MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS)?;
                Ok(Expr::konst(name, levels))
            }
            3 => {
                let fun = self.expr()?;
                let arg = self.expr()?;
                Ok(Expr::app(fun, arg))
            }
            4 => {
                let ty = self.expr()?;
                let body = self.expr()?;
                Ok(Expr::lam("_", ty, body))
            }
            5 => {
                let ty = self.expr()?;
                let body = self.expr()?;
                Ok(Expr::pi("_", ty, body))
            }
            6 => {
                let ty = self.expr()?;
                let value = self.expr()?;
                let body = self.expr()?;
                Ok(Expr::let_in("_", ty, value, body))
            }
            _ => Err(DecodeError::Malformed),
        }
    }

    fn level(&mut self) -> std::result::Result<Level, DecodeError> {
        match self.u8()? {
            0 => Ok(Level::Zero),
            1 => Ok(Level::succ(self.level()?)),
            2 => {
                let lhs = self.level()?;
                let rhs = self.level()?;
                Ok(Level::max(lhs, rhs))
            }
            3 => {
                let lhs = self.level()?;
                let rhs = self.level()?;
                Ok(Level::imax(lhs, rhs))
            }
            4 => Ok(Level::param(self.string()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn level_list_with_cap(&mut self, cap: u64) -> std::result::Result<Vec<Level>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut levels = Vec::new();
        for _ in 0..len {
            levels.push(self.level()?);
        }
        Ok(levels)
    }

    fn path_steps(&mut self) -> std::result::Result<Vec<AdvancedMachineExprPathStep>, DecodeError> {
        let len = self.u64()?;
        if len > MAX_ADVANCED_AI_UNIVERSE_REPAIR_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut path = Vec::new();
        for _ in 0..len {
            path.push(match self.u8()? {
                0 => AdvancedMachineExprPathStep::AppFun,
                1 => AdvancedMachineExprPathStep::AppArg,
                2 => AdvancedMachineExprPathStep::LamType,
                3 => AdvancedMachineExprPathStep::LamBody,
                4 => AdvancedMachineExprPathStep::PiDomain,
                5 => AdvancedMachineExprPathStep::PiCodomain,
                6 => AdvancedMachineExprPathStep::LetType,
                7 => AdvancedMachineExprPathStep::LetValue,
                8 => AdvancedMachineExprPathStep::LetBody,
                _ => return Err(DecodeError::Malformed),
            });
        }
        Ok(path)
    }

    fn option_minimization_hint(
        &mut self,
    ) -> std::result::Result<Option<AdvancedUniverseMinimizationHint>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(match self.u8()? {
                0 => AdvancedUniverseMinimizationHint::KernelDefault,
                1 => AdvancedUniverseMinimizationHint::PreferLowerLevels,
                2 => AdvancedUniverseMinimizationHint::PreferExistingExplicitArgs,
                _ => return Err(DecodeError::Malformed),
            })),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn universe_constraint(
        &mut self,
    ) -> std::result::Result<AdvancedUniverseConstraint, DecodeError> {
        let lhs = self.level()?;
        let relation = match self.u8()? {
            0 => AdvancedUniverseConstraintRelation::Le,
            1 => AdvancedUniverseConstraintRelation::Eq,
            _ => return Err(DecodeError::Malformed),
        };
        let rhs = self.level()?;
        Ok(AdvancedUniverseConstraint { lhs, relation, rhs })
    }

    fn constraint_hint_reason(
        &mut self,
    ) -> std::result::Result<AdvancedUniverseConstraintHintReason, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedUniverseConstraintHintReason::KernelDiagnostic),
            1 => Ok(AdvancedUniverseConstraintHintReason::RepairCandidate),
            2 => Ok(AdvancedUniverseConstraintHintReason::MinimizationExplanation),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn global_ref_list(&mut self) -> std::result::Result<Vec<AdvancedAiGlobalRef>, DecodeError> {
        let len = self.u64()?;
        if len > MAX_ADVANCED_AI_GLOBAL_REFS {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut refs = Vec::with_capacity(len);
        for _ in 0..len {
            refs.push(self.global_ref()?);
        }
        Ok(refs)
    }

    fn global_ref(&mut self) -> std::result::Result<AdvancedAiGlobalRef, DecodeError> {
        Ok(AdvancedAiGlobalRef {
            module: self.name()?,
            export_hash: self.hash()?,
            certificate_hash: self.hash()?,
            name: self.name()?,
            decl_interface_hash: self.hash()?,
        })
    }

    fn inductive_family(
        &mut self,
        budget: &mut AdvancedInductiveDecodeBudget,
    ) -> std::result::Result<AdvancedMachineInductiveFamilyProposal, DecodeError> {
        let name = self.name()?;
        let params = self.telescope_with_cap(MAX_ADVANCED_AI_INDUCTIVE_ITEMS, budget)?;
        let indices = self.telescope_with_cap(MAX_ADVANCED_AI_INDUCTIVE_ITEMS, budget)?;
        let result_sort = self.level_counted(budget)?;
        let constructor_len = self.u64()?;
        if constructor_len > MAX_ADVANCED_AI_INDUCTIVE_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let constructor_len =
            usize::try_from(constructor_len).map_err(|_| DecodeError::Malformed)?;
        let mut constructors = Vec::new();
        for _ in 0..constructor_len {
            constructors.push(AdvancedMachineConstructorProposal {
                name: self.name()?,
                ty: self.expr_counted(budget)?,
            });
        }
        Ok(AdvancedMachineInductiveFamilyProposal {
            name,
            params,
            indices,
            result_sort,
            constructors,
        })
    }

    fn telescope_with_cap(
        &mut self,
        cap: u64,
        budget: &mut AdvancedInductiveDecodeBudget,
    ) -> std::result::Result<Vec<AdvancedMachineTelescopeBinder>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut telescope = Vec::new();
        for _ in 0..len {
            telescope.push(AdvancedMachineTelescopeBinder {
                ty: self.expr_counted(budget)?,
            });
        }
        Ok(telescope)
    }

    fn smt_candidate(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedMachineSmtCertificateCandidate, DecodeError> {
        Ok(AdvancedMachineSmtCertificateCandidate {
            goal: self.goal()?,
            solver: AdvancedSmtSolver::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?,
            logic: AdvancedSmtLogic::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?,
            encoded_problem: self.smt_problem_ref()?,
            certificate_format: AdvancedSmtCertificateFormat::from_tag(self.u8()?)
                .ok_or(DecodeError::Malformed)?,
            rule_registry_profile: AdvancedSmtRuleRegistryProfile::from_tag(self.u8()?)
                .ok_or(DecodeError::Malformed)?,
            proof_payload: self.smt_proof_payload_ref()?,
            reconstruction_plan: self.smt_reconstruction_plan(budget)?,
        })
    }

    fn smt_problem_ref(
        &mut self,
    ) -> std::result::Result<AdvancedMachineSmtProblemRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedMachineSmtProblemRef::Inline {
                problem_hash: self.hash()?,
                encoding_hash: self.hash()?,
                canonical_bytes: self
                    .bytes_with_cap(MAX_ADVANCED_AI_SMT_RAW_BYTES, DecodeError::Malformed)?,
            }),
            1 => Ok(AdvancedMachineSmtProblemRef::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                problem_hash: self.hash()?,
                encoding_hash: self.hash()?,
                size_bytes: self.u64()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn smt_proof_payload_ref(
        &mut self,
    ) -> std::result::Result<AdvancedMachineSmtProofPayloadRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedMachineSmtProofPayloadRef::Inline {
                payload_hash: self.hash()?,
                canonical_bytes: self
                    .bytes_with_cap(MAX_ADVANCED_AI_SMT_RAW_BYTES, DecodeError::Malformed)?,
            }),
            1 => Ok(AdvancedMachineSmtProofPayloadRef::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                payload_hash: self.hash()?,
                size_bytes: self.u64()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn smt_encoded_problem(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedMachineSmtEncodedProblem, DecodeError> {
        let encoder_version =
            AdvancedSmtEncoderVersion::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?;
        let goal_fingerprint = self.hash()?;
        let logic = AdvancedSmtLogic::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?;
        let command_profile =
            AdvancedSmtCommandProfile::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?;
        let command_len = self.u64()?;
        if command_len > MAX_ADVANCED_AI_SMT_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let command_len = usize::try_from(command_len).map_err(|_| DecodeError::Malformed)?;
        let mut commands = Vec::with_capacity(command_len);
        for _ in 0..command_len {
            commands.push(self.smt_command(budget)?);
        }
        Ok(AdvancedMachineSmtEncodedProblem {
            encoder_version,
            goal_fingerprint,
            logic,
            command_profile,
            commands,
        })
    }

    fn smt_command(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtEncodedCommand, DecodeError> {
        Ok(AdvancedSmtEncodedCommand {
            phase: AdvancedSmtCommandPhase::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?,
            command_id: self.hash()?,
            payload: self.smt_command_payload(budget)?,
        })
    }

    fn smt_command_payload(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtCommandPayload, DecodeError> {
        Ok(match self.u8()? {
            0 => AdvancedSmtCommandPayload::SortDecl {
                symbol: self.smt_symbol()?,
                arity: self.u32()?,
            },
            1 => {
                let symbol = self.smt_symbol()?;
                let args = self.smt_sort_expr_list(MAX_ADVANCED_AI_SMT_REFS, budget)?;
                let result = self.smt_sort_expr(budget)?;
                AdvancedSmtCommandPayload::FunctionDecl {
                    symbol,
                    args,
                    result,
                }
            }
            2 => {
                let symbol = self.smt_symbol()?;
                let constructor_len = self.u64()?;
                if constructor_len > MAX_ADVANCED_AI_SMT_REFS {
                    return Err(DecodeError::Malformed);
                }
                let constructor_len =
                    usize::try_from(constructor_len).map_err(|_| DecodeError::Malformed)?;
                let mut constructors = Vec::with_capacity(constructor_len);
                for _ in 0..constructor_len {
                    constructors.push(self.smt_datatype_constructor(budget)?);
                }
                AdvancedSmtCommandPayload::DatatypeDecl {
                    symbol,
                    constructors,
                }
            }
            3 => AdvancedSmtCommandPayload::ContextAssumption {
                source_local_index: self.u32()?,
                core_expr: self.expr_counted(&mut budget.core)?,
                encoded_expr: self.smt_expr(budget)?,
            },
            4 => AdvancedSmtCommandPayload::TargetAssertion {
                core_expr: self.expr_counted(&mut budget.core)?,
                encoded_expr: self.smt_expr(budget)?,
            },
            5 => AdvancedSmtCommandPayload::FinalCheck,
            _ => return Err(DecodeError::Malformed),
        })
    }

    fn smt_symbol(&mut self) -> std::result::Result<AdvancedSmtSymbol, DecodeError> {
        Ok(AdvancedSmtSymbol {
            ascii: self.bytes()?,
        })
    }

    fn smt_sort_expr_list(
        &mut self,
        cap: u64,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<Vec<AdvancedSmtSortExpr>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut sorts = Vec::with_capacity(len);
        for _ in 0..len {
            sorts.push(self.smt_sort_expr(budget)?);
        }
        Ok(sorts)
    }

    fn smt_sort_expr(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtSortExpr, DecodeError> {
        budget.spend_smt_sort()?;
        Ok(match self.u8()? {
            0 => AdvancedSmtSortExpr::Bool,
            1 => AdvancedSmtSortExpr::Int,
            2 => AdvancedSmtSortExpr::BitVec { width: self.u32()? },
            3 => {
                let symbol = self.smt_symbol()?;
                let args = self.smt_sort_expr_list(MAX_ADVANCED_AI_SMT_REFS, budget)?;
                AdvancedSmtSortExpr::User { symbol, args }
            }
            _ => return Err(DecodeError::Malformed),
        })
    }

    fn smt_datatype_constructor(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtDatatypeConstructor, DecodeError> {
        let constructor = self.smt_symbol()?;
        let selector_len = self.u64()?;
        if selector_len > MAX_ADVANCED_AI_SMT_REFS {
            return Err(DecodeError::Malformed);
        }
        let selector_len = usize::try_from(selector_len).map_err(|_| DecodeError::Malformed)?;
        let mut selectors = Vec::with_capacity(selector_len);
        for _ in 0..selector_len {
            selectors.push(AdvancedSmtDatatypeSelector {
                selector: self.smt_symbol()?,
                sort: self.smt_sort_expr(budget)?,
            });
        }
        Ok(AdvancedSmtDatatypeConstructor {
            constructor,
            selectors,
        })
    }

    fn smt_expr(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtExpr, DecodeError> {
        budget.spend_smt_expr()?;
        Ok(match self.u8()? {
            0 => AdvancedSmtExpr::Var {
                symbol: self.smt_symbol()?,
                sort: self.smt_sort_expr(budget)?,
            },
            1 => match self.u8()? {
                0 => AdvancedSmtExpr::BoolLit(false),
                1 => AdvancedSmtExpr::BoolLit(true),
                _ => return Err(DecodeError::Malformed),
            },
            2 => AdvancedSmtExpr::IntLit(self.i128()?),
            3 => AdvancedSmtExpr::BitVecLit {
                width: self.u32()?,
                value: self.bytes()?,
            },
            4 => {
                let symbol = self.smt_symbol()?;
                let args = self.smt_expr_list(MAX_ADVANCED_AI_SMT_REFS, budget)?;
                let result_sort = self.smt_sort_expr(budget)?;
                AdvancedSmtExpr::App {
                    symbol,
                    args,
                    result_sort,
                }
            }
            5 => {
                let tag = self.u8()?;
                let op = AdvancedSmtBuiltinOp::from_tag(tag, self)?;
                let args = self.smt_expr_list(MAX_ADVANCED_AI_SMT_REFS, budget)?;
                let result_sort = self.smt_sort_expr(budget)?;
                AdvancedSmtExpr::BuiltinApp {
                    op,
                    args,
                    result_sort,
                }
            }
            6 => AdvancedSmtExpr::Not(Box::new(self.smt_expr(budget)?)),
            7 => AdvancedSmtExpr::And(self.smt_expr_list(MAX_ADVANCED_AI_SMT_REFS, budget)?),
            8 => AdvancedSmtExpr::Or(self.smt_expr_list(MAX_ADVANCED_AI_SMT_REFS, budget)?),
            9 => AdvancedSmtExpr::Eq(
                Box::new(self.smt_expr(budget)?),
                Box::new(self.smt_expr(budget)?),
            ),
            10 => AdvancedSmtExpr::Imp(
                Box::new(self.smt_expr(budget)?),
                Box::new(self.smt_expr(budget)?),
            ),
            11 => AdvancedSmtExpr::Ite {
                cond: Box::new(self.smt_expr(budget)?),
                then_expr: Box::new(self.smt_expr(budget)?),
                else_expr: Box::new(self.smt_expr(budget)?),
            },
            _ => return Err(DecodeError::Malformed),
        })
    }

    fn smt_expr_list(
        &mut self,
        cap: u64,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<Vec<AdvancedSmtExpr>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut exprs = Vec::with_capacity(len);
        for _ in 0..len {
            exprs.push(self.smt_expr(budget)?);
        }
        Ok(exprs)
    }

    fn smt_proof_node_table(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtProofNodeTable, DecodeError> {
        let certificate_format =
            AdvancedSmtCertificateFormat::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?;
        let node_len = self.u64()?;
        if node_len > MAX_ADVANCED_AI_SMT_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let node_len = usize::try_from(node_len).map_err(|_| DecodeError::Malformed)?;
        let mut nodes = Vec::with_capacity(node_len);
        for _ in 0..node_len {
            nodes.push(self.smt_proof_node(budget)?);
        }
        Ok(AdvancedSmtProofNodeTable {
            certificate_format,
            nodes,
        })
    }

    fn smt_proof_node(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtProofNode, DecodeError> {
        Ok(AdvancedSmtProofNode {
            node_id: self.u32()?,
            rule_fingerprint: self.hash()?,
            premises: self.u32_list_with_cap(MAX_ADVANCED_AI_SMT_REFS)?,
            conclusion_encoding: self.smt_conclusion_encoding(budget)?,
        })
    }

    fn smt_conclusion_encoding(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtConclusionEncoding, DecodeError> {
        Ok(AdvancedSmtConclusionEncoding {
            encoder_version: AdvancedSmtEncoderVersion::from_tag(self.u8()?)
                .ok_or(DecodeError::Malformed)?,
            logic: AdvancedSmtLogic::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?,
            command_profile: AdvancedSmtCommandProfile::from_tag(self.u8()?)
                .ok_or(DecodeError::Malformed)?,
            core_expr: self.expr_counted(&mut budget.core)?,
            encoded_expr: self.smt_expr(budget)?,
        })
    }

    fn smt_reconstruction_plan(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedMachineSmtReconstructionPlan, DecodeError> {
        let imported_theory_refs = self.global_ref_list_with_cap(MAX_ADVANCED_AI_SMT_REFS)?;
        let step_len = self.u64()?;
        if step_len > MAX_ADVANCED_AI_SMT_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let step_len = usize::try_from(step_len).map_err(|_| DecodeError::Malformed)?;
        let mut steps = Vec::with_capacity(step_len);
        for _ in 0..step_len {
            steps.push(self.smt_reconstruction_step(budget)?);
        }
        Ok(AdvancedMachineSmtReconstructionPlan {
            imported_theory_refs,
            steps,
            final_step: self.u32()?,
            final_proof: self.expr_counted(&mut budget.core)?,
        })
    }

    fn smt_reconstruction_step(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedMachineSmtReconstructionStep, DecodeError> {
        Ok(AdvancedMachineSmtReconstructionStep {
            step_id: self.u32()?,
            rule: self.smt_reconstruction_rule(budget)?,
            payload_bindings: self.smt_payload_binding_list()?,
            premises: self.u32_list_with_cap(MAX_ADVANCED_AI_SMT_REFS)?,
            conclusion: self.expr_counted(&mut budget.core)?,
            proof: self.expr_counted(&mut budget.core)?,
        })
    }

    fn smt_reconstruction_rule(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtReconstructionRule, DecodeError> {
        Ok(match self.u8()? {
            0 => AdvancedSmtReconstructionRule::PayloadNode {
                certificate_format: AdvancedSmtCertificateFormat::from_tag(self.u8()?)
                    .ok_or(DecodeError::Malformed)?,
                rule_fingerprint: self.hash()?,
            },
            1 => AdvancedSmtReconstructionRule::LocalBookkeeping {
                kind: self.smt_local_bookkeeping_rule(budget)?,
            },
            _ => return Err(DecodeError::Malformed),
        })
    }

    fn smt_payload_binding_list(
        &mut self,
    ) -> std::result::Result<Vec<AdvancedMachineSmtPayloadBinding>, DecodeError> {
        let len = self.u64()?;
        if len > MAX_ADVANCED_AI_SMT_REFS {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut bindings = Vec::with_capacity(len);
        for _ in 0..len {
            bindings.push(AdvancedMachineSmtPayloadBinding {
                payload_hash: self.hash()?,
                node_id: self.u32()?,
                rule_fingerprint: self.hash()?,
            });
        }
        Ok(bindings)
    }

    fn smt_local_bookkeeping_rule(
        &mut self,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<AdvancedSmtLocalBookkeepingRule, DecodeError> {
        Ok(match self.u8()? {
            0 => AdvancedSmtLocalBookkeepingRule::ReorderPremises {
                permutation: self.u32_list_with_cap(MAX_ADVANCED_AI_SMT_REFS)?,
            },
            1 => AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
                lemma: self.global_ref()?,
                level_args: self
                    .level_list_with_cap_counted(MAX_ADVANCED_AI_SMT_REFS, &mut budget.core)?,
                term_args: self.expr_list_with_cap_counted(MAX_ADVANCED_AI_SMT_REFS, budget)?,
            },
            2 => AdvancedSmtLocalBookkeepingRule::ComposeProof {
                combinator: self.global_ref()?,
                level_args: self
                    .level_list_with_cap_counted(MAX_ADVANCED_AI_SMT_REFS, &mut budget.core)?,
                term_args: self.expr_list_with_cap_counted(MAX_ADVANCED_AI_SMT_REFS, budget)?,
            },
            _ => return Err(DecodeError::Malformed),
        })
    }

    fn expr_list_with_cap_counted(
        &mut self,
        cap: u64,
        budget: &mut AdvancedSmtDecodeBudget,
    ) -> std::result::Result<Vec<Expr>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut exprs = Vec::with_capacity(len);
        for _ in 0..len {
            exprs.push(self.expr_counted(&mut budget.core)?);
        }
        Ok(exprs)
    }

    fn u32_list_with_cap(&mut self, cap: u64) -> std::result::Result<Vec<u32>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.u32()?);
        }
        Ok(values)
    }

    fn global_ref_list_with_cap(
        &mut self,
        cap: u64,
    ) -> std::result::Result<Vec<AdvancedAiGlobalRef>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut refs = Vec::with_capacity(len);
        for _ in 0..len {
            refs.push(self.global_ref()?);
        }
        Ok(refs)
    }

    fn expr_counted(
        &mut self,
        budget: &mut AdvancedInductiveDecodeBudget,
    ) -> std::result::Result<Expr, DecodeError> {
        budget.spend_expr()?;
        match self.u8()? {
            0 => Ok(Expr::sort(self.level_counted(budget)?)),
            1 => {
                let index = u32::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
                Ok(Expr::bvar(index))
            }
            2 => {
                let name = self.string()?;
                let levels =
                    self.level_list_with_cap_counted(MAX_ADVANCED_AI_INDUCTIVE_ITEMS, budget)?;
                Ok(Expr::konst(name, levels))
            }
            3 => {
                let fun = self.expr_counted(budget)?;
                let arg = self.expr_counted(budget)?;
                Ok(Expr::app(fun, arg))
            }
            4 => {
                let ty = self.expr_counted(budget)?;
                let body = self.expr_counted(budget)?;
                Ok(Expr::lam("_", ty, body))
            }
            5 => {
                let ty = self.expr_counted(budget)?;
                let body = self.expr_counted(budget)?;
                Ok(Expr::pi("_", ty, body))
            }
            6 => {
                let ty = self.expr_counted(budget)?;
                let value = self.expr_counted(budget)?;
                let body = self.expr_counted(budget)?;
                Ok(Expr::let_in("_", ty, value, body))
            }
            _ => Err(DecodeError::Malformed),
        }
    }

    fn level_counted(
        &mut self,
        budget: &mut AdvancedInductiveDecodeBudget,
    ) -> std::result::Result<Level, DecodeError> {
        budget.spend_level()?;
        match self.u8()? {
            0 => Ok(Level::Zero),
            1 => Ok(Level::succ(self.level_counted(budget)?)),
            2 => {
                let lhs = self.level_counted(budget)?;
                let rhs = self.level_counted(budget)?;
                Ok(Level::max(lhs, rhs))
            }
            3 => {
                let lhs = self.level_counted(budget)?;
                let rhs = self.level_counted(budget)?;
                Ok(Level::imax(lhs, rhs))
            }
            4 => Ok(Level::param(self.string()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn level_list_with_cap_counted(
        &mut self,
        cap: u64,
        budget: &mut AdvancedInductiveDecodeBudget,
    ) -> std::result::Result<Vec<Level>, DecodeError> {
        let len = self.u64()?;
        if len > cap {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut levels = Vec::new();
        for _ in 0..len {
            levels.push(self.level_counted(budget)?);
        }
        Ok(levels)
    }

    fn typeclass_resolution_plan(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTypeclassResolutionPlan, DecodeError> {
        let goal = self.goal()?;
        let candidate_len = self.u64()?;
        if candidate_len > MAX_ADVANCED_AI_TYPECLASS_CANDIDATES {
            return Err(DecodeError::Malformed);
        }
        let candidate_len = usize::try_from(candidate_len).map_err(|_| DecodeError::Malformed)?;
        let mut ordered_candidates = Vec::new();
        for _ in 0..candidate_len {
            ordered_candidates.push(self.instance_candidate()?);
        }
        let max_depth = u32::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        if max_depth > MAX_ADVANCED_AI_TYPECLASS_DEPTH {
            return Err(DecodeError::Malformed);
        }
        let max_nodes = u32::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        if max_nodes > MAX_ADVANCED_AI_TYPECLASS_NODES {
            return Err(DecodeError::Malformed);
        }
        Ok(AdvancedMachineTypeclassResolutionPlan {
            goal,
            ordered_candidates,
            max_depth,
            max_nodes,
        })
    }

    fn instance_candidate(
        &mut self,
    ) -> std::result::Result<AdvancedMachineInstanceCandidateRef, DecodeError> {
        Ok(AdvancedMachineInstanceCandidateRef {
            target: self.instance_target()?,
            priority_hint: self.option_i32()?,
        })
    }

    fn instance_target(
        &mut self,
    ) -> std::result::Result<AdvancedMachineInstanceTargetRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedMachineInstanceTargetRef::Imported {
                global_ref: self.global_ref()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_i32(&mut self) -> std::result::Result<Option<i32>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.i32()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn theorem_graph_query(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphQuery, DecodeError> {
        let env_fingerprint = self.hash()?;
        let goal_fingerprint = self.hash()?;
        let goal = self.goal()?;
        let snapshot = self.theorem_graph_snapshot_ref()?;
        let query_features = self.theorem_graph_query_features_ref()?;
        let ranking_profile = AdvancedTheoremGraphRankingProfile::from_tag(self.u8()?)
            .ok_or(DecodeError::Malformed)?;
        let limit = u32::try_from(self.u64()?).map_err(|_| DecodeError::Malformed)?;
        Ok(AdvancedMachineTheoremGraphQuery {
            env_fingerprint,
            goal_fingerprint,
            goal,
            snapshot,
            query_features,
            ranking_profile,
            limit,
        })
    }

    fn theorem_graph_snapshot_ref(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphSnapshotRef, DecodeError> {
        let source_release_hash = self.hash()?;
        let extractor_version = AdvancedTheoremGraphExtractorVersion::from_tag(self.u8()?)
            .ok_or(DecodeError::Malformed)?;
        let source = match self.u8()? {
            0 => AdvancedMachineTheoremGraphSnapshotSource::Inline {
                graph_snapshot_hash: self.hash()?,
                canonical_bytes: self.bytes_with_cap(
                    MAX_ADVANCED_AI_THEOREM_GRAPH_SNAPSHOT_BYTES,
                    DecodeError::TheoremGraphSnapshotBytesTooLarge,
                )?,
            },
            1 => AdvancedMachineTheoremGraphSnapshotSource::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                graph_snapshot_hash: self.hash()?,
                size_bytes: self.u64()?,
            },
            _ => return Err(DecodeError::Malformed),
        };
        Ok(AdvancedMachineTheoremGraphSnapshotRef {
            source_release_hash,
            extractor_version,
            source,
        })
    }

    fn theorem_graph_query_features_ref(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphQueryFeaturesRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
                query_features_hash: self.hash()?,
                canonical_bytes: self.bytes_with_cap(
                    MAX_ADVANCED_AI_THEOREM_GRAPH_QUERY_FEATURES_BYTES,
                    DecodeError::TheoremGraphQueryFeaturesBytesTooLarge,
                )?,
            }),
            1 => Ok(AdvancedMachineTheoremGraphQueryFeaturesRef::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                query_features_hash: self.hash()?,
                size_bytes: self.u64()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn theorem_graph_snapshot(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphSnapshot, DecodeError> {
        let source_release_hash = self.hash()?;
        let extractor_version = AdvancedTheoremGraphExtractorVersion::from_tag(self.u8()?)
            .ok_or(DecodeError::Malformed)?;
        let node_len = self.u64()?;
        if node_len > MAX_ADVANCED_AI_THEOREM_GRAPH_NODES {
            return Err(DecodeError::Malformed);
        }
        let node_len = usize::try_from(node_len).map_err(|_| DecodeError::Malformed)?;
        let mut nodes = Vec::new();
        for _ in 0..node_len {
            nodes.push(self.theorem_graph_node()?);
        }
        let edge_len = self.u64()?;
        if edge_len > MAX_ADVANCED_AI_THEOREM_GRAPH_EDGES {
            return Err(DecodeError::Malformed);
        }
        let edge_len = usize::try_from(edge_len).map_err(|_| DecodeError::Malformed)?;
        let mut edges = Vec::new();
        for _ in 0..edge_len {
            edges.push(self.theorem_graph_edge()?);
        }
        Ok(AdvancedMachineTheoremGraphSnapshot {
            source_release_hash,
            extractor_version,
            nodes,
            edges,
        })
    }

    fn theorem_graph_query_features(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphQueryFeatures, DecodeError> {
        let env_fingerprint = self.hash()?;
        let goal_fingerprint = self.hash()?;
        let feature_schema_version = AdvancedTheoremGraphFeatureSchemaVersion::from_tag(self.u8()?)
            .ok_or(DecodeError::Malformed)?;
        let feature_len = self.u64()?;
        if feature_len > MAX_ADVANCED_AI_THEOREM_GRAPH_FEATURES {
            return Err(DecodeError::Malformed);
        }
        let feature_len = usize::try_from(feature_len).map_err(|_| DecodeError::Malformed)?;
        let mut features = Vec::new();
        for _ in 0..feature_len {
            features.push(self.theorem_graph_feature()?);
        }
        Ok(AdvancedMachineTheoremGraphQueryFeatures {
            env_fingerprint,
            goal_fingerprint,
            feature_schema_version,
            features,
        })
    }

    fn theorem_graph_edge(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphEdge, DecodeError> {
        let from = self.theorem_graph_node()?;
        let to = self.theorem_graph_node()?;
        let kind =
            AdvancedTheoremGraphEdgeKind::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?;
        Ok(AdvancedMachineTheoremGraphEdge { from, to, kind })
    }

    fn theorem_graph_node(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphNodeRef, DecodeError> {
        Ok(AdvancedMachineTheoremGraphNodeRef {
            module: self.name()?,
            name: self.name()?,
            export_hash: self.hash()?,
            decl_certificate_hash: self.hash()?,
            type_hash: self.hash()?,
            certificate_hash: self.hash()?,
            decl_interface_hash: self.hash()?,
        })
    }

    fn theorem_graph_feature(
        &mut self,
    ) -> std::result::Result<AdvancedMachineTheoremGraphFeature, DecodeError> {
        let key = AdvancedTheoremGraphFeatureKey {
            namespace_ascii: self.bytes()?,
            name_ascii: self.bytes()?,
        };
        let value = match self.u8()? {
            0 => match self.u8()? {
                0 => AdvancedTheoremGraphFeatureValue::Bool(false),
                1 => AdvancedTheoremGraphFeatureValue::Bool(true),
                _ => return Err(DecodeError::Malformed),
            },
            1 => AdvancedTheoremGraphFeatureValue::I64(self.i64()?),
            2 => AdvancedTheoremGraphFeatureValue::Hash(self.hash()?),
            _ => return Err(DecodeError::Malformed),
        };
        Ok(AdvancedMachineTheoremGraphFeature { key, value })
    }

    fn skip_theorem_graph_edge(&mut self) -> std::result::Result<(), DecodeError> {
        self.skip_theorem_graph_node()?;
        self.skip_theorem_graph_node()?;
        AdvancedTheoremGraphEdgeKind::from_tag(self.u8()?).ok_or(DecodeError::Malformed)?;
        Ok(())
    }

    fn skip_theorem_graph_node(&mut self) -> std::result::Result<(), DecodeError> {
        self.skip_name()?;
        self.skip_name()?;
        self.hash()?;
        self.hash()?;
        self.hash()?;
        self.hash()?;
        self.hash()?;
        Ok(())
    }

    fn skip_theorem_graph_feature(&mut self) -> std::result::Result<(), DecodeError> {
        self.skip_bytes()?;
        self.skip_bytes()?;
        match self.u8()? {
            0 => match self.u8()? {
                0 | 1 => Ok(()),
                _ => Err(DecodeError::Malformed),
            },
            1 => {
                self.i64()?;
                Ok(())
            }
            2 => {
                self.hash()?;
                Ok(())
            }
            _ => Err(DecodeError::Malformed),
        }
    }

    fn skip_name(&mut self) -> std::result::Result<(), DecodeError> {
        let len = self.u64()?;
        if len == 0 || len > MAX_NAME_COMPONENTS {
            return Err(DecodeError::Malformed);
        }
        for _ in 0..len {
            self.skip_string()?;
        }
        Ok(())
    }

    fn formalization_payload(
        &mut self,
    ) -> std::result::Result<AdvancedMachineFormalizationCheckPayload, DecodeError> {
        Ok(AdvancedMachineFormalizationCheckPayload {
            candidate: self.formalization_candidate()?,
            intent_record: self.option_formalization_intent_record()?,
        })
    }

    fn formalization_candidate(
        &mut self,
    ) -> std::result::Result<AdvancedMachineFormalizationCandidate, DecodeError> {
        Ok(AdvancedMachineFormalizationCandidate {
            source_document: self.formalization_source_document_ref()?,
            claim_span: self.formalization_claim_span()?,
            statement: self.machine_surface_term()?,
            optional_proof_candidate: self.option_formalization_proof_candidate()?,
        })
    }

    fn machine_surface_term(
        &mut self,
    ) -> std::result::Result<AdvancedMachineSurfaceTerm, DecodeError> {
        Ok(AdvancedMachineSurfaceTerm {
            universe_params: self
                .string_list_with_cap(MAX_ADVANCED_AI_FORMALIZATION_UNIVERSE_PARAMS)?,
            term_canonical_bytes: self.bytes_with_cap(
                MAX_ADVANCED_AI_FORMALIZATION_TERM_BYTES,
                DecodeError::Malformed,
            )?,
        })
    }

    fn formalization_source_document_ref(
        &mut self,
    ) -> std::result::Result<AdvancedMachineFormalizationSourceDocumentRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedMachineFormalizationSourceDocumentRef::Inline {
                source_document_hash: self.hash()?,
                raw_utf8_bytes: self.bytes_with_cap(
                    MAX_ADVANCED_AI_FORMALIZATION_SOURCE_BYTES,
                    DecodeError::Malformed,
                )?,
            }),
            1 => Ok(AdvancedMachineFormalizationSourceDocumentRef::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                source_document_hash: self.hash()?,
                size_bytes: self.u64()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn formalization_claim_span(
        &mut self,
    ) -> std::result::Result<AdvancedMachineFormalizationClaimSpan, DecodeError> {
        Ok(AdvancedMachineFormalizationClaimSpan {
            start_byte: self.u64()?,
            end_byte: self.u64()?,
            claim_span_hash: self.hash()?,
        })
    }

    fn option_formalization_proof_candidate(
        &mut self,
    ) -> std::result::Result<Option<AdvancedMachineFormalizationProofCandidate>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(AdvancedMachineFormalizationProofCandidate {
                candidate_statement_hash: self.hash()?,
                tactic: self.advanced_ai_tactic_candidate()?,
            })),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_formalization_intent_record(
        &mut self,
    ) -> std::result::Result<Option<AdvancedFormalizationIntentRecord>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(AdvancedFormalizationIntentRecord {
                source_document_hash: self.hash()?,
                claim_span_hash: self.hash()?,
                candidate_statement_hash: self.hash()?,
                status: self.formalization_intent_status()?,
            })),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn formalization_intent_status(
        &mut self,
    ) -> std::result::Result<AdvancedFormalizationIntentStatus, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedFormalizationIntentStatus::Unreviewed),
            1 => Ok(AdvancedFormalizationIntentStatus::Reviewed {
                reviewer: self.reviewer_id()?,
                accepted_statement_hash: self.hash()?,
            }),
            2 => Ok(AdvancedFormalizationIntentStatus::Rejected {
                reviewer: self.reviewer_id()?,
                rejection_reason: self.formalization_rejection_reason_ref()?,
                rejection_reason_hash: self.hash()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn reviewer_id(&mut self) -> std::result::Result<AdvancedReviewerId, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedReviewerId::Human {
                stable_id_ascii: self.bytes()?,
            }),
            1 => Ok(AdvancedReviewerId::System {
                system_id_ascii: self.bytes()?,
                actor_id_ascii: self.bytes()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn formalization_rejection_reason_ref(
        &mut self,
    ) -> std::result::Result<AdvancedMachineFormalizationRejectionReasonRef, DecodeError> {
        match self.u8()? {
            0 => Ok(AdvancedMachineFormalizationRejectionReasonRef::Inline {
                rejection_reason_hash: self.hash()?,
                raw_utf8_bytes: self.bytes_with_cap(
                    MAX_ADVANCED_AI_FORMALIZATION_REASON_BYTES,
                    DecodeError::Malformed,
                )?,
            }),
            1 => Ok(AdvancedMachineFormalizationRejectionReasonRef::Artifact {
                path: self.string()?,
                file_hash: self.hash()?,
                rejection_reason_hash: self.hash()?,
                size_bytes: self.u64()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn advanced_ai_tactic_candidate(
        &mut self,
    ) -> std::result::Result<MachineTacticCandidate, DecodeError> {
        match self.u8()? {
            0 => Ok(MachineTacticCandidate::Exact {
                term: RawMachineTerm::new(self.string()?),
            }),
            1 => Ok(MachineTacticCandidate::Intro {
                name: self.string()?,
            }),
            2 => {
                let head = self.advanced_ai_tactic_head()?;
                let mut budget = AdvancedInductiveDecodeBudget::new();
                let universe_args = self.level_list_with_cap_counted(
                    MAX_ADVANCED_AI_FORMALIZATION_TACTIC_ITEMS,
                    &mut budget,
                )?;
                let args = self.advanced_ai_apply_args()?;
                Ok(MachineTacticCandidate::Apply {
                    head,
                    universe_args,
                    args,
                })
            }
            3 => Ok(MachineTacticCandidate::Rewrite {
                rule: self.advanced_ai_candidate_rewrite_rule()?,
                direction: self.advanced_ai_rewrite_direction()?,
                site: self.advanced_ai_rewrite_site()?,
            }),
            4 => {
                let len = self.u64()?;
                if len > MAX_ADVANCED_AI_FORMALIZATION_TACTIC_ITEMS {
                    return Err(DecodeError::Malformed);
                }
                let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
                let mut rules = Vec::new();
                for _ in 0..len {
                    rules.push(self.advanced_ai_simp_rule_ref()?);
                }
                Ok(MachineTacticCandidate::SimpLite { rules })
            }
            5 => Ok(MachineTacticCandidate::InductionNat {
                local_name: self.string()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn advanced_ai_apply_args(
        &mut self,
    ) -> std::result::Result<Vec<CandidateApplyArg>, DecodeError> {
        let len = self.u64()?;
        if len > MAX_ADVANCED_AI_FORMALIZATION_TACTIC_ITEMS {
            return Err(DecodeError::Malformed);
        }
        let len = usize::try_from(len).map_err(|_| DecodeError::Malformed)?;
        let mut args = Vec::new();
        for _ in 0..len {
            args.push(self.advanced_ai_apply_arg()?);
        }
        Ok(args)
    }

    fn advanced_ai_apply_arg(&mut self) -> std::result::Result<CandidateApplyArg, DecodeError> {
        match self.u8()? {
            0 => Ok(CandidateApplyArg::Term(RawMachineTerm::new(self.string()?))),
            1 => Ok(CandidateApplyArg::Subgoal {
                name_hint: self.option_string()?,
            }),
            2 => Ok(CandidateApplyArg::InferFromTarget),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_string(&mut self) -> std::result::Result<Option<String>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.string()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn advanced_ai_candidate_rewrite_rule(
        &mut self,
    ) -> std::result::Result<CandidateRewriteRuleRef, DecodeError> {
        let head = self.advanced_ai_tactic_head()?;
        let mut budget = AdvancedInductiveDecodeBudget::new();
        let universe_args = self
            .level_list_with_cap_counted(MAX_ADVANCED_AI_FORMALIZATION_TACTIC_ITEMS, &mut budget)?;
        let args = self.advanced_ai_apply_args()?;
        Ok(CandidateRewriteRuleRef {
            head,
            universe_args,
            args,
        })
    }

    fn advanced_ai_tactic_head(&mut self) -> std::result::Result<TacticHead, DecodeError> {
        match self.u8()? {
            0 => Ok(TacticHead::Imported {
                name: self.name()?,
                decl_interface_hash: self.hash()?,
            }),
            1 => Ok(TacticHead::CurrentModule {
                name: self.name()?,
                decl_interface_hash: self.hash()?,
            }),
            2 => Ok(TacticHead::Local {
                name: self.string()?,
            }),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn advanced_ai_simp_rule_ref(&mut self) -> std::result::Result<SimpRuleRef, DecodeError> {
        Ok(SimpRuleRef {
            name: self.name()?,
            decl_interface_hash: self.hash()?,
            direction: self.advanced_ai_rewrite_direction()?,
        })
    }

    fn advanced_ai_rewrite_direction(
        &mut self,
    ) -> std::result::Result<RewriteDirection, DecodeError> {
        match self.u8()? {
            0 => Ok(RewriteDirection::Forward),
            1 => Ok(RewriteDirection::Backward),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn advanced_ai_rewrite_site(&mut self) -> std::result::Result<RewriteSite, DecodeError> {
        match self.u8()? {
            0 => Ok(RewriteSite::EqTargetLeft),
            1 => Ok(RewriteSite::EqTargetRight),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_smt(&mut self) -> std::result::Result<Option<AdvancedSmtOptions>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(AdvancedSmtOptions {
                eq: self.global_ref()?,
                prop_false: self.option_global_ref()?,
                prop_not: self.option_global_ref()?,
            })),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_global_ref(
        &mut self,
    ) -> std::result::Result<Option<AdvancedAiGlobalRef>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.global_ref()?)),
            _ => Err(DecodeError::Malformed),
        }
    }

    fn option_formalization(
        &mut self,
    ) -> std::result::Result<Option<AdvancedFormalizationOptions>, DecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(AdvancedFormalizationOptions {
                tactic_options_canonical_bytes: self.bytes()?,
                tactic_budget_canonical_bytes: self.bytes()?,
            })),
            _ => Err(DecodeError::Malformed),
        }
    }
}

fn ensure_sorted_global_refs(refs: &[AdvancedAiGlobalRef]) -> std::result::Result<(), DecodeError> {
    let mut previous: Option<Vec<u8>> = None;
    for global_ref in refs {
        let key = global_ref_sort_key(global_ref).map_err(|_| DecodeError::Malformed)?;
        if let Some(previous) = previous.as_ref() {
            if previous >= &key {
                return Err(DecodeError::Malformed);
            }
        }
        previous = Some(key);
    }
    Ok(())
}

fn compare_import_identities(
    left: &AdvancedImportIdentity,
    right: &AdvancedImportIdentity,
) -> std::result::Result<Ordering, AdvancedAiCanonicalError> {
    Ok(import_identity_sort_key(left)?.cmp(&import_identity_sort_key(right)?))
}

fn import_identity_sort_key(
    import: &AdvancedImportIdentity,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut key = machine_api_name_canonical_bytes(&import.module)
        .map_err(|_| AdvancedAiCanonicalError::InvalidName)?;
    key.extend_from_slice(&import.export_hash);
    key.extend_from_slice(&import.certificate_hash);
    Ok(key)
}

fn global_ref_sort_key(
    global_ref: &AdvancedAiGlobalRef,
) -> std::result::Result<Vec<u8>, AdvancedAiCanonicalError> {
    let mut key = machine_api_name_canonical_bytes(&global_ref.module)
        .map_err(|_| AdvancedAiCanonicalError::InvalidName)?;
    key.extend_from_slice(&global_ref.export_hash);
    key.extend_from_slice(&global_ref.certificate_hash);
    key.extend_from_slice(
        &machine_api_name_canonical_bytes(&global_ref.name)
            .map_err(|_| AdvancedAiCanonicalError::InvalidName)?,
    );
    key.extend_from_slice(&global_ref.decl_interface_hash);
    Ok(key)
}

fn encode_validation_error_to(out: &mut Vec<u8>, error: AdvancedAiValidationError) {
    out.push(error.tag());
}

fn encode_feature_error_option_to(out: &mut Vec<u8>, feature: Option<AdvancedAiFeatureError>) {
    match feature {
        Some(feature) => {
            out.push(1);
            encode_feature_error_to(out, feature);
        }
        None => out.push(0),
    }
}

fn encode_feature_error_to(out: &mut Vec<u8>, feature: AdvancedAiFeatureError) {
    match feature {
        AdvancedAiFeatureError::AdvancedInductive(error) => {
            out.push(0);
            out.push(match error {
                AdvancedInductiveError::TargetRefMismatch => 0,
                AdvancedInductiveError::PositivityProfileUnsupported => 1,
                AdvancedInductiveError::ArtifactGeneratorUnavailable => 2,
                AdvancedInductiveError::GeneratedArtifactMismatch => 3,
                AdvancedInductiveError::NameCollision => 4,
            });
        }
        AdvancedAiFeatureError::UniverseRepair(error) => {
            out.push(1);
            out.push(match error {
                AdvancedUniverseRepairError::UnknownUniverseParam => 0,
                AdvancedUniverseRepairError::IllFormedLevelExpr => 1,
                AdvancedUniverseRepairError::UnsatisfiedConstraint => 2,
                AdvancedUniverseRepairError::NonCanonicalSolution => 3,
                AdvancedUniverseRepairError::TargetFingerprintMismatch => 4,
                AdvancedUniverseRepairError::InvalidOccurrencePath => 5,
                AdvancedUniverseRepairError::AmbiguousOccurrence => 6,
                AdvancedUniverseRepairError::TargetRefMismatch => 7,
                AdvancedUniverseRepairError::ConstraintHintMismatch => 8,
            });
        }
        AdvancedAiFeatureError::TypeclassResolution(error) => {
            out.push(2);
            out.push(match error {
                AdvancedTypeclassResolutionError::ClassDeclarationMismatch => 0,
                AdvancedTypeclassResolutionError::CandidateInterfaceInvalid => 1,
                AdvancedTypeclassResolutionError::ClassHeadUnsupported => 2,
                AdvancedTypeclassResolutionError::NoSolution => 3,
            });
        }
        AdvancedAiFeatureError::SmtCertificate(error) => {
            out.push(4);
            out.push(match error {
                AdvancedSmtCertificateError::EncodingMismatch => 0,
                AdvancedSmtCertificateError::RuleFingerprintMismatch => 1,
                AdvancedSmtCertificateError::RuleRegistryMismatch => 2,
                AdvancedSmtCertificateError::NonCanonicalPayload => 3,
                AdvancedSmtCertificateError::ReconstructionProofMismatch => 4,
                AdvancedSmtCertificateError::ConclusionEncodingMismatch => 5,
                AdvancedSmtCertificateError::PayloadBindingMismatch => 6,
                AdvancedSmtCertificateError::ReconstructionConclusionMismatch => 7,
                AdvancedSmtCertificateError::ReconstructionPremiseMismatch => 8,
                AdvancedSmtCertificateError::PublicInterfaceMismatch => 9,
                AdvancedSmtCertificateError::TheoryRefMismatch => 10,
                AdvancedSmtCertificateError::UnsupportedFragment => 11,
                AdvancedSmtCertificateError::SolverResultOnly => 12,
                AdvancedSmtCertificateError::MalformedProofPayload => 13,
                AdvancedSmtCertificateError::ReconstructionPlanHashMismatch => 14,
            });
        }
        AdvancedAiFeatureError::TheoremGraphQuery(error) => {
            out.push(5);
            out.push(match error {
                AdvancedTheoremGraphError::SnapshotMalformed => 0,
                AdvancedTheoremGraphError::QueryFeaturesMalformed => 1,
                AdvancedTheoremGraphError::NodeResolutionMismatch => 2,
                AdvancedTheoremGraphError::LimitOutOfRange => 3,
            });
        }
        AdvancedAiFeatureError::Formalization(error) => {
            out.push(6);
            out.push(match error {
                AdvancedFormalizationError::IntentRecordMismatch => 0,
                AdvancedFormalizationError::CandidateStatementElaborationFailed => 1,
                AdvancedFormalizationError::FormalizationProofStatementMismatch => 2,
                AdvancedFormalizationError::RejectedIntentHasProofCandidate => 3,
                AdvancedFormalizationError::ProofBridgeFailed => 4,
            });
        }
    }
}

fn encode_name_to(
    out: &mut Vec<u8>,
    name: &Name,
) -> std::result::Result<(), AdvancedAiCanonicalError> {
    if !name.is_canonical() {
        return Err(AdvancedAiCanonicalError::InvalidName);
    }
    encode_len_to(out, name.0.len());
    for component in &name.0 {
        encode_string_to(out, component);
    }
    Ok(())
}

fn encode_option_hash_to(out: &mut Vec<u8>, hash: Option<&Hash>) {
    match hash {
        Some(hash) => {
            out.push(1);
            encode_hash_to(out, hash);
        }
        None => out.push(0),
    }
}

fn encode_option_i32_to(out: &mut Vec<u8>, value: Option<i32>) {
    match value {
        Some(value) => {
            out.push(1);
            encode_i32_to(out, value);
        }
        None => out.push(0),
    }
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_bytes_to(out: &mut Vec<u8>, bytes: &[u8]) {
    encode_len_to(out, bytes.len());
    out.extend_from_slice(bytes);
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_bytes_to(out, value.as_bytes());
}

fn encode_len_to(out: &mut Vec<u8>, len: usize) {
    encode_u64_to(out, len as u64);
}

fn encode_u64_to(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn encode_u32_to(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn encode_i32_to(out: &mut Vec<u8>, value: i32) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn encode_i64_to(out: &mut Vec<u8>, value: i64) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn encode_i128_to(out: &mut Vec<u8>, value: i128) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(domain.as_bytes());
    bytes.extend_from_slice(payload);
    sha256(&bytes)
}

fn sha256(bytes: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArtifactPathError {
    EnvelopeMalformed,
    ArtifactUnavailable,
}

fn validate_artifact_path(
    workspace_root: &Path,
    path: &str,
) -> std::result::Result<PathBuf, ArtifactPathError> {
    if path.is_empty() || path.as_bytes().contains(&0) {
        return Err(ArtifactPathError::EnvelopeMalformed);
    }
    if path
        .split('/')
        .any(|component| component.is_empty() || component == "." || component == "..")
    {
        return Err(ArtifactPathError::EnvelopeMalformed);
    }
    let relative = Path::new(path);
    if relative.is_absolute() {
        return Err(ArtifactPathError::EnvelopeMalformed);
    }
    for component in relative.components() {
        match component {
            Component::Normal(_) => {}
            Component::CurDir
            | Component::ParentDir
            | Component::RootDir
            | Component::Prefix(_) => {
                return Err(ArtifactPathError::EnvelopeMalformed);
            }
        }
    }

    let root = workspace_root
        .canonicalize()
        .map_err(|_| ArtifactPathError::ArtifactUnavailable)?;
    let mut current = root.clone();
    for component in relative.components() {
        let Component::Normal(component) = component else {
            return Err(ArtifactPathError::EnvelopeMalformed);
        };
        current.push(component);
        match std::fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                let resolved = current
                    .canonicalize()
                    .map_err(|_| ArtifactPathError::ArtifactUnavailable)?;
                if !resolved.starts_with(&root) {
                    return Err(ArtifactPathError::EnvelopeMalformed);
                }
                current = resolved;
            }
            Ok(_) => {}
            Err(_) => break,
        }
    }
    Ok(workspace_root.join(relative))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::MachinePerformanceIsolationCounters;
    use std::fs;

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    #[derive(Default)]
    struct CountingExternalIndexUpdateSink {
        counters: MachinePerformanceIsolationCounters,
        updated: Vec<AdvancedExternalIndexKind>,
    }

    impl AdvancedExternalIndexUpdateSink for CountingExternalIndexUpdateSink {
        fn update_external_index(
            &mut self,
            entry: &AdvancedExternalIndexUpdateEntry,
        ) -> std::result::Result<(), AdvancedExternalIndexUpdateError> {
            match entry.index {
                AdvancedExternalIndexKind::TheoremGraph => {
                    self.counters.theorem_graph_calls += 1;
                }
                AdvancedExternalIndexKind::Embedding => {
                    self.counters.embedding_calls += 1;
                }
                AdvancedExternalIndexKind::PremiseSet | AdvancedExternalIndexKind::Usage => {
                    self.counters.database_calls += 1;
                }
            }
            self.updated.push(entry.index);
            Ok(())
        }
    }

    fn empty_options_bytes() -> Vec<u8> {
        advanced_ai_options_canonical_bytes(&AdvancedAiOptions::default()).unwrap()
    }

    #[test]
    fn performance_isolation_external_index_updates_are_opt_in_and_export_hash_keyed() {
        let request = AdvancedExternalIndexUpdateRequest {
            module: Name::from_dotted("GraphLib"),
            export_hash: hash(11),
            certificate_hash: hash(12),
            indexes: vec![
                AdvancedExternalIndexKind::Usage,
                AdvancedExternalIndexKind::TheoremGraph,
                AdvancedExternalIndexKind::Embedding,
                AdvancedExternalIndexKind::PremiseSet,
                AdvancedExternalIndexKind::TheoremGraph,
            ],
            trigger: AdvancedExternalIndexUpdateTrigger::Authoring,
        };

        let plan = advanced_external_index_update_plan(request.clone()).unwrap();
        assert_eq!(plan.schema, ADVANCED_AI_EXTERNAL_INDEX_UPDATE_SCHEMA);
        assert_eq!(
            plan.scheduler_integration,
            AdvancedExternalIndexSchedulerIntegration::Deferred
        );
        assert_eq!(
            plan.entries
                .iter()
                .map(|entry| entry.index)
                .collect::<Vec<_>>(),
            vec![
                AdvancedExternalIndexKind::TheoremGraph,
                AdvancedExternalIndexKind::Embedding,
                AdvancedExternalIndexKind::PremiseSet,
                AdvancedExternalIndexKind::Usage,
            ]
        );
        assert!(plan
            .entries
            .iter()
            .all(|entry| entry.module == request.module
                && entry.export_hash == request.export_hash
                && entry.certificate_hash == request.certificate_hash));

        let planned_only_sink = CountingExternalIndexUpdateSink::default();
        assert_eq!(
            planned_only_sink.counters,
            MachinePerformanceIsolationCounters::default()
        );

        let same_export_new_certificate =
            advanced_external_index_update_plan(AdvancedExternalIndexUpdateRequest {
                certificate_hash: hash(88),
                ..request.clone()
            })
            .unwrap();
        assert_eq!(
            plan.entries
                .iter()
                .map(|entry| entry.update_key_hash)
                .collect::<Vec<_>>(),
            same_export_new_certificate
                .entries
                .iter()
                .map(|entry| entry.update_key_hash)
                .collect::<Vec<_>>()
        );

        let changed_export =
            advanced_external_index_update_plan(AdvancedExternalIndexUpdateRequest {
                export_hash: hash(99),
                ..request
            })
            .unwrap();
        assert_ne!(
            plan.entries
                .iter()
                .map(|entry| entry.update_key_hash)
                .collect::<Vec<_>>(),
            changed_export
                .entries
                .iter()
                .map(|entry| entry.update_key_hash)
                .collect::<Vec<_>>()
        );

        let mut explicit_sink = CountingExternalIndexUpdateSink::default();
        let report = run_advanced_external_index_update_plan(&plan, &mut explicit_sink).unwrap();
        assert_eq!(report.schema, ADVANCED_AI_EXTERNAL_INDEX_UPDATE_SCHEMA);
        assert_eq!(
            explicit_sink.updated,
            vec![
                AdvancedExternalIndexKind::TheoremGraph,
                AdvancedExternalIndexKind::Embedding,
                AdvancedExternalIndexKind::PremiseSet,
                AdvancedExternalIndexKind::Usage,
            ]
        );
        assert_eq!(explicit_sink.counters.theorem_graph_calls, 1);
        assert_eq!(explicit_sink.counters.embedding_calls, 1);
        assert_eq!(explicit_sink.counters.database_calls, 2);
        assert_eq!(explicit_sink.counters.llm_calls, 0);
        assert_eq!(explicit_sink.counters.agent_calls, 0);
    }

    fn verified_universe_import() -> VerifiedImportRef {
        let module = npa_cert::CoreModule {
            name: Name::from_dotted("Lib"),
            declarations: vec![
                npa_kernel::Decl::Axiom {
                    name: "Lib.T".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: Expr::sort(Level::succ(Level::param("u"))),
                },
                npa_kernel::Decl::Axiom {
                    name: "Lib.F".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: Expr::pi(
                        "A",
                        Expr::sort(Level::param("u")),
                        Expr::sort(Level::param("u")),
                    ),
                },
            ],
        };
        let cert = npa_cert::build_module_cert(module, &[]).unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();
        let mut session = npa_cert::VerifierSession::new();
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .unwrap();
        VerifiedImportRef::from_verified_module(&verified).unwrap()
    }

    fn universe_global_ref_for(import: &VerifiedImportRef, name: &str) -> AdvancedAiGlobalRef {
        let export = import
            .exports()
            .iter()
            .find(|export| export.name == Name::from_dotted(name))
            .unwrap();
        AdvancedAiGlobalRef {
            module: import.module().clone(),
            export_hash: import.export_hash(),
            certificate_hash: import.certificate_hash(),
            name: export.name.clone(),
            decl_interface_hash: export.decl_interface_hash,
        }
    }

    fn universe_global_ref(import: &VerifiedImportRef) -> AdvancedAiGlobalRef {
        universe_global_ref_for(import, "Lib.T")
    }

    fn universe_target_expr() -> Expr {
        Expr::konst("Lib.T", vec![Level::param("u")])
    }

    fn verified_theorem_graph_import() -> VerifiedImportRef {
        let module = npa_cert::CoreModule {
            name: Name::from_dotted("GraphLib"),
            declarations: vec![
                npa_kernel::Decl::Axiom {
                    name: "GraphLib.P".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::succ(Level::zero())),
                },
                npa_kernel::Decl::Def {
                    name: "GraphLib.Type0".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::succ(Level::zero())),
                    value: Expr::sort(Level::zero()),
                    reducibility: npa_kernel::Reducibility::Reducible,
                },
            ],
        };
        let cert = npa_cert::build_module_cert(module, &[]).unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();
        let mut session = npa_cert::VerifierSession::new();
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .unwrap();
        VerifiedImportRef::from_verified_module(&verified).unwrap()
    }

    fn theorem_graph_node(
        import: &VerifiedImportRef,
        name: &str,
    ) -> AdvancedMachineTheoremGraphNodeRef {
        let export = import
            .exports()
            .iter()
            .find(|export| export.name == Name::from_dotted(name))
            .unwrap();
        let decl = import
            .verified_module()
            .declarations()
            .iter()
            .find(|decl| decl.hashes.decl_interface_hash == export.decl_interface_hash)
            .unwrap();
        AdvancedMachineTheoremGraphNodeRef {
            module: import.module().clone(),
            name: export.name.clone(),
            export_hash: import.export_hash(),
            decl_certificate_hash: decl.hashes.decl_certificate_hash,
            type_hash: export.type_hash,
            certificate_hash: import.certificate_hash(),
            decl_interface_hash: export.decl_interface_hash,
        }
    }

    fn missing_theorem_graph_node() -> AdvancedMachineTheoremGraphNodeRef {
        AdvancedMachineTheoremGraphNodeRef {
            module: Name::from_dotted("Missing"),
            name: Name::from_dotted("Missing.P"),
            export_hash: hash(31),
            decl_certificate_hash: hash(32),
            type_hash: hash(33),
            certificate_hash: hash(34),
            decl_interface_hash: hash(35),
        }
    }

    fn theorem_graph_goal() -> AdvancedAiGoal {
        AdvancedAiGoal {
            universe_params: Vec::new(),
            local_context: Vec::new(),
            target: Expr::sort(Level::zero()),
        }
    }

    fn theorem_graph_features(
        env_fingerprint: Hash,
        goal_fingerprint: Hash,
    ) -> AdvancedMachineTheoremGraphQueryFeatures {
        AdvancedMachineTheoremGraphQueryFeatures {
            env_fingerprint,
            goal_fingerprint,
            feature_schema_version: AdvancedTheoremGraphFeatureSchemaVersion::MvpGoalFeaturesV1,
            features: Vec::new(),
        }
    }

    fn theorem_graph_snapshot(
        source_release_hash: Hash,
        mut nodes: Vec<AdvancedMachineTheoremGraphNodeRef>,
    ) -> AdvancedMachineTheoremGraphSnapshot {
        nodes.sort_by_key(advanced_ai_theorem_graph_node_identity_key);
        AdvancedMachineTheoremGraphSnapshot {
            source_release_hash,
            extractor_version: AdvancedTheoremGraphExtractorVersion::MvpCertificateGraphV1,
            nodes,
            edges: Vec::new(),
        }
    }

    fn theorem_graph_snapshot_bytes_with_noncanonical_node_name(
        source_release_hash: Hash,
    ) -> Vec<u8> {
        let mut bytes = Vec::new();
        encode_hash_to(&mut bytes, &source_release_hash);
        bytes.push(AdvancedTheoremGraphExtractorVersion::MvpCertificateGraphV1.tag());
        encode_u64_to(&mut bytes, 1);
        encode_u64_to(&mut bytes, 1);
        encode_bytes_to(&mut bytes, b"");
        encode_name_to(&mut bytes, &Name::from_dotted("GraphLib.P")).unwrap();
        for seed in 51..=55 {
            encode_hash_to(&mut bytes, &hash(seed));
        }
        encode_u64_to(&mut bytes, 0);
        bytes
    }

    fn theorem_graph_inline_query_request(
        import: &VerifiedImportRef,
        snapshot_hash_override: Option<Hash>,
        query_features_hash_override: Option<Hash>,
        snapshot: AdvancedMachineTheoremGraphSnapshot,
        query_features_override: Option<AdvancedMachineTheoremGraphQueryFeatures>,
        limit: u32,
    ) -> Vec<u8> {
        let options_bytes = empty_options_bytes();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let imports = vec![AdvancedImportIdentity::from_verified_import(import)];
        let env_fingerprint = advanced_ai_env_fingerprint(
            AdvancedAiProfileVersion::MvpV1,
            AdvancedAiTaskKind::TheoremGraphQuery,
            &imports,
            options_hash,
        )
        .unwrap();
        let goal = theorem_graph_goal();
        let goal_fingerprint = advanced_ai_goal_fingerprint(env_fingerprint, &goal);
        let snapshot_bytes = advanced_ai_theorem_graph_snapshot_canonical_bytes(&snapshot).unwrap();
        let snapshot_hash = snapshot_hash_override
            .unwrap_or_else(|| advanced_ai_theorem_graph_snapshot_hash(&snapshot_bytes).unwrap());
        let query_features = query_features_override
            .unwrap_or_else(|| theorem_graph_features(env_fingerprint, goal_fingerprint));
        let query_features_bytes =
            advanced_ai_theorem_graph_query_features_canonical_bytes(&query_features).unwrap();
        let query_features_hash = query_features_hash_override.unwrap_or_else(|| {
            advanced_ai_theorem_graph_query_features_hash(&query_features_bytes).unwrap()
        });
        let query = AdvancedMachineTheoremGraphQuery {
            env_fingerprint,
            goal_fingerprint,
            goal,
            snapshot: AdvancedMachineTheoremGraphSnapshotRef {
                source_release_hash: snapshot.source_release_hash,
                extractor_version: AdvancedTheoremGraphExtractorVersion::MvpCertificateGraphV1,
                source: AdvancedMachineTheoremGraphSnapshotSource::Inline {
                    graph_snapshot_hash: snapshot_hash,
                    canonical_bytes: snapshot_bytes,
                },
            },
            query_features: AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
                query_features_hash,
                canonical_bytes: query_features_bytes,
            },
            ranking_profile: AdvancedTheoremGraphRankingProfile::MvpTupleOrder,
            limit,
        };
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::TheoremGraphQuery,
            target: AdvancedAiTarget {
                env_fingerprint,
                target_decl_hash: None,
                goal_fingerprint: Some(goal_fingerprint),
            },
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: advanced_ai_theorem_graph_query_canonical_bytes(&query).unwrap(),
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn smt_eq_type() -> Expr {
        Expr::pi(
            "_",
            Expr::sort(Level::param("u")),
            Expr::pi(
                "_",
                Expr::bvar(0),
                Expr::pi("_", Expr::bvar(1), Expr::sort(Level::zero())),
            ),
        )
    }

    fn verified_smt_import() -> VerifiedImportRef {
        let module = npa_cert::CoreModule {
            name: Name::from_dotted("S"),
            declarations: vec![
                npa_kernel::Decl::Axiom {
                    name: "S.Eq".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: smt_eq_type(),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.False".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.Not".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::pi("_", Expr::sort(Level::zero()), Expr::sort(Level::zero())),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.falseProof".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("S.False", vec![]),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.lemma".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("S.False", vec![]),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.Other".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.otherProof".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("S.Other", vec![]),
                },
                npa_kernel::Decl::Axiom {
                    name: "S.combinator".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("S.False", vec![]),
                },
            ],
        };
        let cert = npa_cert::build_module_cert(module, &[]).unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();
        let mut session = npa_cert::VerifierSession::new();
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .unwrap();
        VerifiedImportRef::from_verified_module(&verified).unwrap()
    }

    fn smt_global_ref_for(import: &VerifiedImportRef, name: &str) -> AdvancedAiGlobalRef {
        let export = import
            .exports()
            .iter()
            .find(|export| export.name == Name::from_dotted(name))
            .unwrap();
        AdvancedAiGlobalRef {
            module: import.module().clone(),
            export_hash: import.export_hash(),
            certificate_hash: import.certificate_hash(),
            name: export.name.clone(),
            decl_interface_hash: export.decl_interface_hash,
        }
    }

    fn smt_options(import: &VerifiedImportRef) -> AdvancedSmtOptions {
        AdvancedSmtOptions {
            eq: smt_global_ref_for(import, "S.Eq"),
            prop_false: Some(smt_global_ref_for(import, "S.False")),
            prop_not: Some(smt_global_ref_for(import, "S.Not")),
        }
    }

    fn smt_false() -> Expr {
        Expr::konst("S.False", vec![])
    }

    fn smt_false_proof() -> Expr {
        Expr::konst("S.falseProof", vec![])
    }

    fn smt_other() -> Expr {
        Expr::konst("S.Other", vec![])
    }

    fn smt_other_proof() -> Expr {
        Expr::konst("S.otherProof", vec![])
    }

    fn smt_symbol(name: &str) -> AdvancedSmtSymbol {
        AdvancedSmtSymbol {
            ascii: name.as_bytes().to_vec(),
        }
    }

    fn smt_command(
        phase: AdvancedSmtCommandPhase,
        payload: AdvancedSmtCommandPayload,
    ) -> AdvancedSmtEncodedCommand {
        let mut command = AdvancedSmtEncodedCommand {
            phase,
            command_id: hash(0),
            payload,
        };
        command.command_id = advanced_ai_smt_command_id(&command).unwrap();
        command
    }

    fn smt_target_command() -> AdvancedSmtEncodedCommand {
        smt_command(
            AdvancedSmtCommandPhase::TargetAssertion,
            AdvancedSmtCommandPayload::TargetAssertion {
                core_expr: smt_false(),
                encoded_expr: AdvancedSmtExpr::Not(Box::new(AdvancedSmtExpr::BoolLit(false))),
            },
        )
    }

    fn smt_final_check_command() -> AdvancedSmtEncodedCommand {
        smt_command(
            AdvancedSmtCommandPhase::FinalCheck,
            AdvancedSmtCommandPayload::FinalCheck,
        )
    }

    fn smt_problem(
        goal_fingerprint: Hash,
        logic: AdvancedSmtLogic,
        commands: Vec<AdvancedSmtEncodedCommand>,
    ) -> AdvancedMachineSmtEncodedProblem {
        AdvancedMachineSmtEncodedProblem {
            encoder_version: AdvancedSmtEncoderVersion::MvpNormalizedQfV1,
            goal_fingerprint,
            logic,
            command_profile: AdvancedSmtCommandProfile::MvpNormalizedQf,
            commands,
        }
    }

    fn smt_problem_ref(problem: AdvancedMachineSmtEncodedProblem) -> AdvancedMachineSmtProblemRef {
        let canonical_bytes = advanced_ai_smt_problem_canonical_bytes(&problem).unwrap();
        let problem_hash = advanced_ai_smt_problem_hash(&problem).unwrap();
        let encoding_hash = advanced_ai_smt_encoding_hash(&problem, problem_hash);
        AdvancedMachineSmtProblemRef::Inline {
            problem_hash,
            encoding_hash,
            canonical_bytes,
        }
    }

    fn smt_payload_ref(table: AdvancedSmtProofNodeTable) -> AdvancedMachineSmtProofPayloadRef {
        let canonical_bytes = advanced_ai_smt_proof_payload_canonical_bytes(&table).unwrap();
        let payload_hash = advanced_ai_smt_proof_payload_hash(&table).unwrap();
        AdvancedMachineSmtProofPayloadRef::Inline {
            payload_hash,
            canonical_bytes,
        }
    }

    fn smt_opaque_payload_ref(
        format: AdvancedSmtCertificateFormat,
        canonical_bytes: &[u8],
    ) -> AdvancedMachineSmtProofPayloadRef {
        let payload_hash =
            advanced_ai_smt_opaque_proof_payload_hash(format, canonical_bytes).unwrap();
        AdvancedMachineSmtProofPayloadRef::Inline {
            payload_hash,
            canonical_bytes: canonical_bytes.to_vec(),
        }
    }

    fn smt_rule_fingerprint(fragment: AdvancedSmtSupportedFragment) -> Hash {
        advanced_ai_smt_rule_descriptor_fingerprint(
            &advanced_ai_smt_mvp_payload_node_rule_descriptor_for_fragment(fragment),
        )
    }

    fn smt_propositional_rule_fingerprint() -> Hash {
        smt_rule_fingerprint(AdvancedSmtSupportedFragment::QfPropositional)
    }

    fn smt_solver_process_policy() -> AdvancedSmtSolverProcessPolicy {
        AdvancedSmtSolverProcessPolicy {
            network: AdvancedSmtSolverNetworkPolicy::NoNetwork,
            filesystem: AdvancedSmtSolverFilesystemPolicy::ReadOnlyInputsWritableOutput,
            max_output_bytes: 1_048_576,
            max_cpu_millis: 1_000,
            max_memory_bytes: 134_217_728,
            timeout_millis: 2_000,
            max_child_processes: 1,
            child_process_allowlist: vec![b"cvc5".to_vec()],
        }
    }

    fn smt_solver_process_profile(version: &[u8]) -> AdvancedSmtSolverProcessProfile {
        AdvancedSmtSolverProcessProfile {
            identity: AdvancedSmtPinnedSolverIdentity {
                solver: AdvancedSmtSolver::Cvc5,
                version_ascii: version.to_vec(),
                binary_hash: hash(210),
                container_digest_hash: Some(hash(211)),
            },
            arguments: vec![
                b"--produce-proofs".to_vec(),
                b"--lang=smt2".to_vec(),
                b"--incremental=false".to_vec(),
            ],
            policy: smt_solver_process_policy(),
        }
    }

    fn smt_solver_result(
        handoff: &AdvancedSmtSolverHandoff,
        output: AdvancedSmtSolverOutputRef,
    ) -> AdvancedSmtSolverProcessResult {
        AdvancedSmtSolverProcessResult {
            solver_process_profile_hash: handoff.solver_process_profile_hash,
            smtlib_hash: handoff.smtlib_hash,
            output,
            resource_usage: AdvancedSmtSolverResourceUsage {
                output_bytes: 128,
                cpu_millis: 10,
                memory_bytes: 4096,
                wall_clock_millis: 20,
                child_processes: 1,
            },
        }
    }

    fn smt_proof_table() -> AdvancedSmtProofNodeTable {
        AdvancedSmtProofNodeTable {
            certificate_format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
            nodes: vec![AdvancedSmtProofNode {
                node_id: 0,
                rule_fingerprint: smt_propositional_rule_fingerprint(),
                premises: Vec::new(),
                conclusion_encoding: AdvancedSmtConclusionEncoding {
                    encoder_version: AdvancedSmtEncoderVersion::MvpNormalizedQfV1,
                    logic: AdvancedSmtLogic::MvpQfUf,
                    command_profile: AdvancedSmtCommandProfile::MvpNormalizedQf,
                    core_expr: smt_false(),
                    encoded_expr: AdvancedSmtExpr::BoolLit(false),
                },
            }],
        }
    }

    fn smt_payload_binding() -> AdvancedMachineSmtPayloadBinding {
        smt_payload_binding_for(
            advanced_ai_smt_proof_payload_hash(&smt_proof_table()).unwrap(),
            0,
        )
    }

    fn smt_payload_binding_for(
        payload_hash: Hash,
        node_id: u32,
    ) -> AdvancedMachineSmtPayloadBinding {
        AdvancedMachineSmtPayloadBinding {
            payload_hash,
            node_id,
            rule_fingerprint: smt_propositional_rule_fingerprint(),
        }
    }

    fn smt_payload_node_step(step_id: u32) -> AdvancedMachineSmtReconstructionStep {
        AdvancedMachineSmtReconstructionStep {
            step_id,
            rule: AdvancedSmtReconstructionRule::PayloadNode {
                certificate_format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
                rule_fingerprint: smt_propositional_rule_fingerprint(),
            },
            payload_bindings: vec![smt_payload_binding()],
            premises: Vec::new(),
            conclusion: smt_false(),
            proof: smt_false_proof(),
        }
    }

    fn smt_base_plan() -> AdvancedMachineSmtReconstructionPlan {
        AdvancedMachineSmtReconstructionPlan {
            imported_theory_refs: Vec::new(),
            steps: vec![smt_payload_node_step(0)],
            final_step: 0,
            final_proof: smt_false_proof(),
        }
    }

    fn smt_valid_candidate(goal_fingerprint: Hash) -> AdvancedMachineSmtCertificateCandidate {
        AdvancedMachineSmtCertificateCandidate {
            goal: AdvancedAiGoal {
                universe_params: Vec::new(),
                local_context: Vec::new(),
                target: smt_false(),
            },
            solver: AdvancedSmtSolver::Cvc5,
            logic: AdvancedSmtLogic::MvpQfUf,
            encoded_problem: smt_problem_ref(smt_problem(
                goal_fingerprint,
                AdvancedSmtLogic::MvpQfUf,
                vec![smt_target_command(), smt_final_check_command()],
            )),
            certificate_format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
            rule_registry_profile: AdvancedSmtRuleRegistryProfile::MvpEmptyRegistryV1,
            proof_payload: smt_payload_ref(smt_proof_table()),
            reconstruction_plan: smt_base_plan(),
        }
    }

    fn smt_request(
        import: &VerifiedImportRef,
        mutate: impl FnOnce(&mut AdvancedMachineSmtCertificateCandidate),
    ) -> Vec<u8> {
        let options = AdvancedAiOptions {
            smt: Some(smt_options(import)),
            ..Default::default()
        };
        let options_bytes = advanced_ai_options_canonical_bytes(&options).unwrap();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let imports = vec![AdvancedImportIdentity::from_verified_import(import)];
        let env_fingerprint = advanced_ai_env_fingerprint(
            AdvancedAiProfileVersion::MvpV1,
            AdvancedAiTaskKind::SmtCertificate,
            &imports,
            options_hash,
        )
        .unwrap();
        let goal = AdvancedAiGoal {
            universe_params: Vec::new(),
            local_context: Vec::new(),
            target: smt_false(),
        };
        let goal_fingerprint = advanced_ai_goal_fingerprint(env_fingerprint, &goal);
        let mut candidate = smt_valid_candidate(goal_fingerprint);
        mutate(&mut candidate);
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::SmtCertificate,
            target: AdvancedAiTarget {
                env_fingerprint,
                target_decl_hash: None,
                goal_fingerprint: Some(goal_fingerprint),
            },
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: advanced_ai_smt_candidate_canonical_bytes(&candidate).unwrap(),
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn verified_typeclass_import() -> VerifiedImportRef {
        let obj = Expr::konst("TC.Obj", vec![]);
        let cls = |arg: Expr| Expr::app(Expr::konst("TC.Cls", vec![]), arg);
        let wrap = |arg: Expr| Expr::app(Expr::konst("TC.Wrap", vec![]), arg);
        let module = npa_cert::CoreModule {
            name: Name::from_dotted("TC"),
            declarations: vec![
                npa_kernel::Decl::Axiom {
                    name: "TC.Obj".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::succ(Level::zero())),
                },
                npa_kernel::Decl::Axiom {
                    name: "TC.Cls".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::pi("_", obj.clone(), Expr::sort(Level::succ(Level::zero()))),
                },
                npa_kernel::Decl::Axiom {
                    name: "TC.Base".to_owned(),
                    universe_params: Vec::new(),
                    ty: obj.clone(),
                },
                npa_kernel::Decl::Axiom {
                    name: "TC.Wrap".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::pi("_", obj.clone(), obj.clone()),
                },
                npa_kernel::Decl::Axiom {
                    name: "TC.instBase".to_owned(),
                    universe_params: Vec::new(),
                    ty: cls(Expr::konst("TC.Base", vec![])),
                },
                npa_kernel::Decl::Axiom {
                    name: "TC.instAlt".to_owned(),
                    universe_params: Vec::new(),
                    ty: cls(Expr::konst("TC.Base", vec![])),
                },
                npa_kernel::Decl::Axiom {
                    name: "TC.instWrap".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::pi(
                        "_",
                        obj,
                        Expr::pi("_", cls(Expr::bvar(0)), cls(wrap(Expr::bvar(1)))),
                    ),
                },
            ],
        };
        let cert = npa_cert::build_module_cert(module, &[]).unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();
        let mut session = npa_cert::VerifierSession::new();
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .unwrap();
        VerifiedImportRef::from_verified_module(&verified).unwrap()
    }

    fn typeclass_global_ref_for(import: &VerifiedImportRef, name: &str) -> AdvancedAiGlobalRef {
        let export = import
            .exports()
            .iter()
            .find(|export| export.name == Name::from_dotted(name))
            .unwrap();
        AdvancedAiGlobalRef {
            module: import.module().clone(),
            export_hash: import.export_hash(),
            certificate_hash: import.certificate_hash(),
            name: export.name.clone(),
            decl_interface_hash: export.decl_interface_hash,
        }
    }

    fn typeclass_candidate(
        import: &VerifiedImportRef,
        name: &str,
        priority_hint: Option<i32>,
    ) -> AdvancedMachineInstanceCandidateRef {
        AdvancedMachineInstanceCandidateRef {
            target: AdvancedMachineInstanceTargetRef::Imported {
                global_ref: typeclass_global_ref_for(import, name),
            },
            priority_hint,
        }
    }

    fn typeclass_goal(target: Expr) -> AdvancedAiGoal {
        AdvancedAiGoal {
            universe_params: Vec::new(),
            local_context: Vec::new(),
            target,
        }
    }

    fn typeclass_request(
        import: &VerifiedImportRef,
        goal: AdvancedAiGoal,
        ordered_candidates: Vec<AdvancedMachineInstanceCandidateRef>,
        max_depth: u32,
        max_nodes: u32,
        options_override: Option<AdvancedAiOptions>,
    ) -> Vec<u8> {
        let mut options = options_override.unwrap_or_default();
        if options.typeclass.class_declarations.is_empty() {
            options.typeclass.class_declarations = vec![typeclass_global_ref_for(import, "TC.Cls")];
        }
        let options_bytes = advanced_ai_options_canonical_bytes(&options).unwrap();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let imports = vec![AdvancedImportIdentity::from_verified_import(import)];
        let env_fingerprint = advanced_ai_env_fingerprint(
            AdvancedAiProfileVersion::MvpV1,
            AdvancedAiTaskKind::TypeclassResolution,
            &imports,
            options_hash,
        )
        .unwrap();
        let goal_fingerprint = advanced_ai_goal_fingerprint(env_fingerprint, &goal);
        let plan = AdvancedMachineTypeclassResolutionPlan {
            goal,
            ordered_candidates,
            max_depth,
            max_nodes,
        };
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::TypeclassResolution,
            target: AdvancedAiTarget {
                env_fingerprint,
                target_decl_hash: None,
                goal_fingerprint: Some(goal_fingerprint),
            },
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: advanced_ai_typeclass_resolution_plan_canonical_bytes(&plan).unwrap(),
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn typeclass_cls(arg: Expr) -> Expr {
        Expr::app(Expr::konst("TC.Cls", vec![]), arg)
    }

    fn typeclass_base() -> Expr {
        Expr::konst("TC.Base", vec![])
    }

    fn typeclass_wrap(arg: Expr) -> Expr {
        Expr::app(Expr::konst("TC.Wrap", vec![]), arg)
    }

    fn advanced_ai_unary_expr() -> Expr {
        Expr::konst("Unary", vec![])
    }

    fn valid_inductive_proposal() -> AdvancedMachineInductiveProposal {
        AdvancedMachineInductiveProposal {
            block_name: None,
            expected_decl_hash: None,
            universe_params: Vec::new(),
            inductives: vec![AdvancedMachineInductiveFamilyProposal {
                name: Name::from_dotted("Unary"),
                params: Vec::new(),
                indices: Vec::new(),
                result_sort: Level::succ(Level::zero()),
                constructors: vec![
                    AdvancedMachineConstructorProposal {
                        name: Name::from_dotted("zero"),
                        ty: advanced_ai_unary_expr(),
                    },
                    AdvancedMachineConstructorProposal {
                        name: Name::from_dotted("succ"),
                        ty: Expr::pi("_", advanced_ai_unary_expr(), advanced_ai_unary_expr()),
                    },
                ],
            }],
        }
    }

    fn inductive_request(proposal: AdvancedMachineInductiveProposal) -> Vec<u8> {
        inductive_request_with_imports(proposal, Vec::new())
    }

    fn inductive_request_with_imports(
        proposal: AdvancedMachineInductiveProposal,
        verified_imports: Vec<&VerifiedImportRef>,
    ) -> Vec<u8> {
        let options_bytes = empty_options_bytes();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let imports = verified_imports
            .iter()
            .map(|import| AdvancedImportIdentity::from_verified_import(import))
            .collect::<Vec<_>>();
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::AdvancedInductive,
            target: AdvancedAiTarget {
                env_fingerprint: advanced_ai_env_fingerprint(
                    AdvancedAiProfileVersion::MvpV1,
                    AdvancedAiTaskKind::AdvancedInductive,
                    &imports,
                    options_hash,
                )
                .unwrap(),
                target_decl_hash: None,
                goal_fingerprint: None,
            },
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: advanced_ai_inductive_proposal_canonical_bytes(&proposal).unwrap(),
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn universe_goal(target: Expr) -> AdvancedAiGoal {
        AdvancedAiGoal {
            universe_params: vec!["u".to_owned()],
            local_context: Vec::new(),
            target,
        }
    }

    fn valid_universe_candidate(import: &VerifiedImportRef) -> AdvancedUniverseRepairCandidate {
        let target = universe_target_expr();
        AdvancedUniverseRepairCandidate {
            goal: Some(universe_goal(target.clone())),
            target_expr: target,
            instantiations: vec![AdvancedUniverseInstantiationPatch {
                occurrence: AdvancedMachineExprOccurrence {
                    path: Vec::new(),
                    expected_ref: universe_global_ref(import),
                },
                explicit_level_args: vec![Level::succ(Level::param("u"))],
            }],
            constraint_hints: Vec::new(),
            minimization_hint: None,
        }
    }

    fn universe_request_with_target(
        import: &VerifiedImportRef,
        candidate: AdvancedUniverseRepairCandidate,
        target_decl_hash: Option<Hash>,
        goal_fingerprint: Option<Hash>,
    ) -> Vec<u8> {
        let options_bytes = empty_options_bytes();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let imports = vec![AdvancedImportIdentity::from_verified_import(import)];
        let env_fingerprint = advanced_ai_env_fingerprint(
            AdvancedAiProfileVersion::MvpV1,
            AdvancedAiTaskKind::UniverseRepair,
            &imports,
            options_hash,
        )
        .unwrap();
        let goal_fingerprint = if target_decl_hash.is_some() {
            goal_fingerprint
        } else {
            goal_fingerprint.or_else(|| {
                candidate
                    .goal
                    .as_ref()
                    .map(|goal| advanced_ai_goal_fingerprint(env_fingerprint, goal))
            })
        };
        let payload = advanced_ai_universe_repair_candidate_canonical_bytes(&candidate).unwrap();
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::UniverseRepair,
            target: AdvancedAiTarget {
                env_fingerprint,
                target_decl_hash,
                goal_fingerprint,
            },
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload,
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn valid_universe_request(import: &VerifiedImportRef) -> Vec<u8> {
        universe_request_with_target(import, valid_universe_candidate(import), None, None)
    }

    fn target_for(
        task_kind: AdvancedAiTaskKind,
        imports: &[AdvancedImportIdentity],
        options_hash: Hash,
        goal_fingerprint: Option<Hash>,
    ) -> AdvancedAiTarget {
        AdvancedAiTarget {
            env_fingerprint: advanced_ai_env_fingerprint(
                AdvancedAiProfileVersion::MvpV1,
                task_kind,
                imports,
                options_hash,
            )
            .unwrap(),
            target_decl_hash: None,
            goal_fingerprint,
        }
    }

    fn inline_request(
        task_kind: AdvancedAiTaskKind,
        options_bytes: Vec<u8>,
        imports: Vec<AdvancedImportIdentity>,
        goal_fingerprint: Option<Hash>,
    ) -> Vec<u8> {
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind,
            target: target_for(task_kind, &imports, options_hash, goal_fingerprint),
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: b"opaque-payload".to_vec(),
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn workspace_root() -> PathBuf {
        std::env::current_dir().unwrap()
    }

    fn assert_rejected(
        response: AdvancedAiEndpointResponse,
        expected_error: AdvancedAiValidationError,
        expected_feature_error: Option<AdvancedAiFeatureError>,
    ) -> Hash {
        match response {
            AdvancedAiEndpointResponse::Rejected {
                candidate_hash,
                validation_result_hash,
                error,
                feature_error,
            } => {
                assert_eq!(error, expected_error);
                assert_eq!(feature_error, expected_feature_error);
                assert_eq!(
                    validation_result_hash,
                    advanced_ai_validation_result_hash_for_rejection(
                        candidate_hash,
                        error,
                        feature_error
                    )
                );
                candidate_hash
            }
            other => panic!("expected rejected response, got {other:?}"),
        }
    }

    fn assert_success(response: AdvancedAiEndpointResponse) -> (Hash, AdvancedAiSuccessPayload) {
        match response {
            AdvancedAiEndpointResponse::Success {
                candidate_hash,
                validation_result_hash,
                payload,
            } => {
                let payload = *payload;
                assert_eq!(
                    validation_result_hash,
                    advanced_ai_validation_result_hash_for_success(candidate_hash, &payload)
                );
                (candidate_hash, payload)
            }
            other => panic!("expected success response, got {other:?}"),
        }
    }

    fn advanced_ai_m9_endpoint_token(endpoint: &str) -> &'static str {
        match endpoint {
            ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT => "inductive_check",
            ADVANCED_AI_UNIVERSE_REPAIR_CHECK_ENDPOINT => "universe_repair_check",
            ADVANCED_AI_TYPECLASS_RESOLVE_ENDPOINT => "typeclass_resolve",
            ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT => "smt_reconstruct",
            ADVANCED_AI_THEOREM_GRAPH_QUERY_ENDPOINT => "theorem_graph_query",
            ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT => "formalize_check",
            _ => panic!("unknown advanced AI endpoint {endpoint}"),
        }
    }

    fn assert_advanced_ai_m9_fixture_name(name: &str, endpoint: &str, outcome: &str) {
        assert!(name.starts_with("advanced_ai_m9_"), "{name}");
        assert!(
            name.contains(advanced_ai_m9_endpoint_token(endpoint)),
            "{name}"
        );
        assert!(name.contains(outcome), "{name}");
    }

    fn assert_advanced_ai_m9_success_fixture(
        name: &str,
        endpoint: &str,
        response: AdvancedAiEndpointResponse,
    ) -> (Hash, AdvancedAiSuccessPayload) {
        assert_advanced_ai_m9_fixture_name(name, endpoint, "success");
        assert_success(response)
    }

    fn assert_advanced_ai_m9_rejected_fixture(
        name: &str,
        endpoint: &str,
        response: AdvancedAiEndpointResponse,
        expected_error: AdvancedAiValidationError,
        expected_feature_error: Option<AdvancedAiFeatureError>,
    ) -> Hash {
        assert_advanced_ai_m9_fixture_name(name, endpoint, "rejected");
        assert_rejected(response, expected_error, expected_feature_error)
    }

    fn assert_advanced_ai_m9_error_fixture(
        name: &str,
        endpoint: &str,
        response: AdvancedAiEndpointResponse,
        expected_error: AdvancedAiEndpointError,
    ) {
        assert_advanced_ai_m9_fixture_name(name, endpoint, "error");
        assert_eq!(
            response,
            AdvancedAiEndpointResponse::Error {
                error: expected_error
            }
        );
    }

    #[test]
    fn common_candidate_hash_is_available_when_options_decode_fails() {
        let request = inline_request(
            AdvancedAiTaskKind::AdvancedInductive,
            b"not-options".to_vec(),
            Vec::new(),
            None,
        );
        let expected_candidate_hash = advanced_ai_candidate_hash(&request);

        let candidate_hash = assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );

        assert_eq!(candidate_hash, expected_candidate_hash);
    }

    #[test]
    fn top_level_decode_failure_is_endpoint_error_without_candidate_hash() {
        assert_eq!(
            run_advanced_ai_inductive_check_request(b"not-an-envelope", &[], &workspace_root()),
            AdvancedAiEndpointResponse::Error {
                error: AdvancedAiEndpointError::NonCanonicalRequestBytes
            }
        );
    }

    #[test]
    fn options_hash_mismatch_is_payload_hash_mismatch() {
        let options_bytes = empty_options_bytes();
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::AdvancedInductive,
            target: target_for(AdvancedAiTaskKind::AdvancedInductive, &[], hash(9), None),
            imports: Vec::new(),
            options: AdvancedAiOptionsRef::Inline {
                options_hash: hash(9),
                canonical_bytes: options_bytes,
            },
            payload: Vec::new(),
        };
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
    }

    #[test]
    fn formalization_options_preserve_nested_machine_tactic_bytes() {
        let options = AdvancedAiOptions {
            formalization: Some(AdvancedFormalizationOptions {
                tactic_options_canonical_bytes: b"machine-tactic-options".to_vec(),
                tactic_budget_canonical_bytes: b"machine-tactic-budget".to_vec(),
            }),
            ..Default::default()
        };
        let bytes = advanced_ai_options_canonical_bytes(&options).unwrap();

        assert_eq!(decode_options(&bytes).unwrap(), options);

        let mut changed = options.clone();
        changed
            .formalization
            .as_mut()
            .unwrap()
            .tactic_budget_canonical_bytes
            .push(0);
        assert_ne!(
            advanced_ai_options_canonical_bytes(&changed).unwrap(),
            bytes
        );
    }

    #[test]
    fn advanced_ai_domain_hashes_use_documented_tag_concatenation() {
        let payload = b"payload";
        let mut expected = Vec::new();
        expected.extend_from_slice(CANDIDATE_HASH_TAG.as_bytes());
        expected.extend_from_slice(payload);

        assert_eq!(advanced_ai_candidate_hash(payload), sha256(&expected));
    }

    #[test]
    fn artifact_hash_and_size_mismatch_is_candidate_rejection() {
        let root = std::env::temp_dir().join(format!("npa-advanced-ai-m1-{}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("options.bin"), empty_options_bytes()).unwrap();
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::AdvancedInductive,
            target: AdvancedAiTarget {
                env_fingerprint: hash(1),
                target_decl_hash: None,
                goal_fingerprint: None,
            },
            imports: Vec::new(),
            options: AdvancedAiOptionsRef::Artifact {
                path: "options.bin".to_owned(),
                file_hash: hash(2),
                options_hash: advanced_ai_options_hash(&empty_options_bytes()),
                size_bytes: empty_options_bytes().len() as u64,
            },
            payload: Vec::new(),
        };
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &root),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn artifact_path_shape_failure_is_candidate_rejection() {
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::AdvancedInductive,
            target: AdvancedAiTarget {
                env_fingerprint: hash(1),
                target_decl_hash: None,
                goal_fingerprint: None,
            },
            imports: Vec::new(),
            options: AdvancedAiOptionsRef::Artifact {
                path: "../options.bin".to_owned(),
                file_hash: hash(2),
                options_hash: advanced_ai_options_hash(&empty_options_bytes()),
                size_bytes: empty_options_bytes().len() as u64,
            },
            payload: Vec::new(),
        };
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    #[cfg(unix)]
    #[test]
    fn artifact_symlink_escape_is_candidate_rejection() {
        let root = std::env::temp_dir().join(format!(
            "npa-advanced-ai-symlink-root-{}",
            std::process::id()
        ));
        let outside = std::env::temp_dir().join(format!(
            "npa-advanced-ai-symlink-outside-{}",
            std::process::id()
        ));
        fs::create_dir_all(&root).unwrap();
        fs::write(&outside, empty_options_bytes()).unwrap();
        std::os::unix::fs::symlink(&outside, root.join("escaped-options.bin")).unwrap();
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::AdvancedInductive,
            target: AdvancedAiTarget {
                env_fingerprint: hash(1),
                target_decl_hash: None,
                goal_fingerprint: None,
            },
            imports: Vec::new(),
            options: AdvancedAiOptionsRef::Artifact {
                path: "escaped-options.bin".to_owned(),
                file_hash: advanced_ai_file_hash(&empty_options_bytes()),
                options_hash: advanced_ai_options_hash(&empty_options_bytes()),
                size_bytes: empty_options_bytes().len() as u64,
            },
            payload: Vec::new(),
        };
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &root),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
        let _ = fs::remove_dir_all(root);
        let _ = fs::remove_file(outside);
    }

    #[test]
    fn duplicate_import_identity_is_import_closure_mismatch() {
        let import = AdvancedImportIdentity {
            module: Name::from_dotted("A"),
            export_hash: hash(1),
            certificate_hash: hash(2),
        };
        let request = inline_request(
            AdvancedAiTaskKind::AdvancedInductive,
            empty_options_bytes(),
            vec![import.clone(), import],
            None,
        );

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        );
    }

    #[test]
    fn import_sort_order_uses_machine_api_name_canonical_bytes() {
        let import_b = AdvancedImportIdentity {
            module: Name::from_dotted("B"),
            export_hash: hash(1),
            certificate_hash: hash(2),
        };
        let import_aa = AdvancedImportIdentity {
            module: Name::from_dotted("AA"),
            export_hash: hash(3),
            certificate_hash: hash(4),
        };
        assert_eq!(
            compare_import_identities(&import_b, &import_aa).unwrap(),
            Ordering::Less
        );
        let request = inline_request(
            AdvancedAiTaskKind::AdvancedInductive,
            empty_options_bytes(),
            vec![import_aa, import_b],
            None,
        );

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    #[test]
    fn env_fingerprint_mismatch_is_target_fingerprint_mismatch() {
        let mut request = decode_candidate_envelope(&inline_request(
            AdvancedAiTaskKind::AdvancedInductive,
            empty_options_bytes(),
            Vec::new(),
            None,
        ))
        .unwrap();
        request.target.env_fingerprint = hash(7);
        let request = advanced_ai_candidate_envelope_canonical_bytes(&request).unwrap();

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }

    #[test]
    fn advanced_inductive_valid_candidate_returns_decl_hashes() {
        let request = inductive_request(valid_inductive_proposal());
        let expected_candidate_hash = advanced_ai_candidate_hash(&request);

        let response = run_advanced_ai_inductive_check_request(&request, &[], &workspace_root());

        let AdvancedAiEndpointResponse::Success {
            candidate_hash,
            validation_result_hash,
            payload,
        } = response
        else {
            panic!("expected success response");
        };
        assert_eq!(candidate_hash, expected_candidate_hash);
        let AdvancedAiSuccessPayload::AdvancedInductive {
            decl_interface_hash,
            decl_certificate_hash,
        } = *payload
        else {
            panic!("expected advanced inductive payload");
        };
        assert_ne!(decl_interface_hash, [0; 32]);
        assert_ne!(decl_certificate_hash, [0; 32]);
        let expected_payload = AdvancedAiSuccessPayload::AdvancedInductive {
            decl_interface_hash,
            decl_certificate_hash,
        };
        assert_eq!(
            validation_result_hash,
            advanced_ai_validation_result_hash_for_success(candidate_hash, &expected_payload)
        );
    }

    #[test]
    fn advanced_inductive_expected_decl_hash_mismatch_is_target_mismatch() {
        let mut proposal = valid_inductive_proposal();
        proposal.expected_decl_hash = Some(hash(77));
        let request = inductive_request(proposal);

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::TargetFingerprintMismatch,
            None,
        );
    }

    #[test]
    fn advanced_inductive_constructor_result_mismatch_is_target_ref_mismatch() {
        let mut proposal = valid_inductive_proposal();
        proposal.inductives[0].constructors[0].ty = Expr::sort(Level::zero());
        let request = inductive_request(proposal);

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::TargetRefMismatch,
            )),
        );
    }

    #[test]
    fn advanced_inductive_name_collision_is_feature_rejection() {
        let mut proposal = valid_inductive_proposal();
        proposal.inductives[0].constructors[0].name = Name::from_dotted("rec");
        let request = inductive_request(proposal);

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::NameCollision,
            )),
        );
    }

    #[test]
    fn advanced_inductive_bad_positivity_is_unsupported() {
        let mut proposal = valid_inductive_proposal();
        proposal.inductives[0]
            .constructors
            .push(AdvancedMachineConstructorProposal {
                name: Name::from_dotted("bad"),
                ty: Expr::pi(
                    "_",
                    Expr::pi("_", advanced_ai_unary_expr(), advanced_ai_unary_expr()),
                    advanced_ai_unary_expr(),
                ),
            });
        let request = inductive_request(proposal);

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        );
    }

    #[test]
    fn advanced_inductive_nested_recursive_occurrence_is_unsupported() {
        let import = verified_universe_import();
        let mut proposal = valid_inductive_proposal();
        proposal.inductives[0]
            .constructors
            .push(AdvancedMachineConstructorProposal {
                name: Name::from_dotted("boxed"),
                ty: Expr::pi(
                    "_",
                    Expr::app(
                        Expr::konst("Lib.F", vec![Level::succ(Level::zero())]),
                        advanced_ai_unary_expr(),
                    ),
                    advanced_ai_unary_expr(),
                ),
            });
        let request = inductive_request_with_imports(proposal, vec![&import]);

        assert_rejected(
            run_advanced_ai_inductive_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        );
    }

    #[test]
    fn advanced_inductive_mutual_block_is_unsupported_before_name_checks() {
        let mut proposal = valid_inductive_proposal();
        let mut second = proposal.inductives[0].clone();
        second.name = Name::from_dotted("Unary");
        proposal.inductives.push(second);
        let request = inductive_request(proposal);

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        );
    }

    #[test]
    fn advanced_inductive_indexed_family_candidate_returns_decl_hashes() {
        let proposal = AdvancedMachineInductiveProposal {
            block_name: None,
            expected_decl_hash: None,
            universe_params: Vec::new(),
            inductives: vec![AdvancedMachineInductiveFamilyProposal {
                name: Name::from_dotted("Ix"),
                params: Vec::new(),
                indices: vec![AdvancedMachineTelescopeBinder {
                    ty: Expr::sort(Level::zero()),
                }],
                result_sort: Level::succ(Level::zero()),
                constructors: vec![AdvancedMachineConstructorProposal {
                    name: Name::from_dotted("mk"),
                    ty: Expr::pi(
                        "_",
                        Expr::sort(Level::zero()),
                        Expr::app(Expr::konst("Ix", vec![]), Expr::bvar(0)),
                    ),
                }],
            }],
        };
        let request = inductive_request(proposal);

        let (_, payload) = assert_success(run_advanced_ai_inductive_check_request(
            &request,
            &[],
            &workspace_root(),
        ));
        let AdvancedAiSuccessPayload::AdvancedInductive {
            decl_interface_hash,
            decl_certificate_hash,
        } = payload
        else {
            panic!("expected advanced inductive payload");
        };
        assert_ne!(decl_interface_hash, [0; 32]);
        assert_ne!(decl_certificate_hash, [0; 32]);
    }

    #[test]
    fn smt_empty_registry_rejects_valid_preregistry_payload_node() {
        let import = verified_smt_import();
        let request = smt_request(&import, |_| {});

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );
    }

    #[test]
    fn smt_rule_registry_hashes_approved_euf_lia_and_bitblast_descriptors() {
        let empty =
            advanced_ai_smt_rule_registry(AdvancedSmtRuleRegistryProfile::MvpEmptyRegistryV1);
        let registry =
            advanced_ai_smt_rule_registry(AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1);
        assert!(empty.descriptors.is_empty());
        assert_eq!(registry.descriptors.len(), 5);
        assert_ne!(
            advanced_ai_smt_rule_registry_hash(&empty),
            advanced_ai_smt_rule_registry_hash(&registry)
        );
        assert_eq!(
            advanced_ai_smt_rule_registry_hash(&registry),
            advanced_ai_smt_rule_registry_hash(&registry)
        );

        let euf = registry
            .descriptors
            .iter()
            .find(|descriptor| descriptor.supported_fragment == AdvancedSmtSupportedFragment::QfEuf)
            .expect("EUF descriptor should be registered");
        assert_eq!(euf.logic, AdvancedSmtLogic::MvpQfUf);
        assert_eq!(
            euf.supported_sort_profile,
            AdvancedSmtSupportedSortProfile::BoolAndUninterpreted
        );
        assert_eq!(
            euf.supported_operator_profile,
            AdvancedSmtSupportedOperatorProfile::EufCore
        );
        assert_eq!(
            euf.checker_profile,
            AdvancedSmtCheckerProfile::KernelCheckedPayloadNodeV1
        );

        let lia = registry
            .descriptors
            .iter()
            .find(|descriptor| {
                descriptor.supported_fragment == AdvancedSmtSupportedFragment::QfSimpleLia
            })
            .expect("simple LIA descriptor should be registered");
        let euf_lia = registry
            .descriptors
            .iter()
            .find(|descriptor| {
                descriptor.supported_fragment == AdvancedSmtSupportedFragment::QfEufLia
            })
            .expect("EUF+LIA descriptor should be registered");
        assert_eq!(lia.logic, AdvancedSmtLogic::MvpQfLia);
        assert_eq!(euf_lia.logic, AdvancedSmtLogic::MvpQfLia);
        assert_ne!(
            advanced_ai_smt_rule_descriptor_hash(lia),
            advanced_ai_smt_rule_descriptor_hash(euf_lia)
        );
        assert_ne!(
            advanced_ai_smt_rule_descriptor_fingerprint(lia),
            advanced_ai_smt_rule_descriptor_fingerprint(euf_lia)
        );

        let bitblast = registry
            .descriptors
            .iter()
            .find(|descriptor| {
                descriptor.supported_fragment == AdvancedSmtSupportedFragment::QfBitVecBitblastLrat
            })
            .expect("bitblast/LRAT descriptor should be registered");
        assert_eq!(
            bitblast.kind,
            AdvancedSmtRuleDescriptorKind::BitblastLratSoundnessBridgeV1
        );
        assert_eq!(
            bitblast.checker_profile,
            AdvancedSmtCheckerProfile::BitblastLratBridgeV1
        );
        assert!(bitblast
            .soundness_requirements
            .contains(&AdvancedSmtSoundnessRequirement::BitblastLratSoundnessBridge));
    }

    #[test]
    fn smt_rule_registry_rejects_mixed_logic_mismatch_and_stale_descriptor_hash() {
        let import = verified_smt_import();
        let mixed_logic_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.logic = AdvancedSmtLogic::MvpQfLia;
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &mixed_logic_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::EncodingMismatch,
            )),
        );

        let stale_descriptor_request = smt_request(&import, |candidate| {
            let stale_fingerprint = smt_rule_fingerprint(AdvancedSmtSupportedFragment::QfSimpleLia);
            let mut table = smt_proof_table();
            table.nodes[0].rule_fingerprint = stale_fingerprint;
            candidate.proof_payload = smt_payload_ref(table);
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            if let AdvancedSmtReconstructionRule::PayloadNode {
                rule_fingerprint, ..
            } = &mut candidate.reconstruction_plan.steps[0].rule
            {
                *rule_fingerprint = stale_fingerprint;
            }
            candidate.reconstruction_plan.steps[0].payload_bindings[0].rule_fingerprint =
                stale_fingerprint;
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &stale_descriptor_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );
    }

    #[test]
    fn smt_nonempty_registry_accepts_kernel_checked_reconstruction() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
        });

        let (_, payload) = assert_success(run_advanced_ai_smt_reconstruct_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        ));
        assert_eq!(
            payload,
            AdvancedAiSuccessPayload::SmtCertificate {
                final_proof: smt_false_proof()
            }
        );
        let hashes = advanced_ai_smt_prove_hashes_from_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        )
        .unwrap();
        assert_eq!(
            hashes.npa_proof_hash,
            npa_tactic::core_expr_hash(&smt_false_proof())
        );
        let human = crate::run_human_smt_prove(crate::HumanSmtProveRequest {
            request_canonical_bytes: &request,
            verified_imports: std::slice::from_ref(&import),
            workspace_root: &workspace_root(),
            require_certificate: true,
        });
        match human {
            crate::HumanSmtProveResponse::Success(ok) => {
                assert!(ok.kernel_checked);
                assert_eq!(
                    ok.npa_proof_hash,
                    npa_tactic::core_expr_hash(&smt_false_proof())
                );
            }
            other => panic!("expected Human smt prove success, got {other:?}"),
        }
    }

    #[test]
    fn smt_nonempty_registry_rejects_payload_binding_and_premise_mismatch() {
        let import = verified_smt_import();
        let bad_binding_hash_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.steps[0].payload_bindings[0].payload_hash = hash(77);
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &bad_binding_hash_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );

        let binding_rule_mismatch_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.steps[0].payload_bindings[0].rule_fingerprint = hash(78);
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &binding_rule_mismatch_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::PayloadBindingMismatch,
            )),
        );

        let payload_conclusion_mismatch_request = smt_request(&import, |candidate| {
            let mut table = smt_proof_table();
            table.nodes[0].conclusion_encoding.core_expr = smt_other();
            let payload_hash = advanced_ai_smt_proof_payload_hash(&table).unwrap();
            candidate.proof_payload = smt_payload_ref(table);
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.steps[0].payload_bindings[0].payload_hash = payload_hash;
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &payload_conclusion_mismatch_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::ReconstructionConclusionMismatch,
            )),
        );

        let premise_mismatch_request = smt_request(&import, |candidate| {
            let mut table = smt_proof_table();
            table.nodes.push(AdvancedSmtProofNode {
                node_id: 1,
                rule_fingerprint: smt_propositional_rule_fingerprint(),
                premises: vec![0],
                conclusion_encoding: AdvancedSmtConclusionEncoding {
                    encoder_version: AdvancedSmtEncoderVersion::MvpNormalizedQfV1,
                    logic: AdvancedSmtLogic::MvpQfUf,
                    command_profile: AdvancedSmtCommandProfile::MvpNormalizedQf,
                    core_expr: smt_false(),
                    encoded_expr: AdvancedSmtExpr::BoolLit(false),
                },
            });
            let payload_hash = advanced_ai_smt_proof_payload_hash(&table).unwrap();
            candidate.proof_payload = smt_payload_ref(table);
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.steps = vec![
                AdvancedMachineSmtReconstructionStep {
                    payload_bindings: vec![smt_payload_binding_for(payload_hash, 0)],
                    ..smt_payload_node_step(0)
                },
                AdvancedMachineSmtReconstructionStep {
                    step_id: 1,
                    payload_bindings: vec![smt_payload_binding_for(payload_hash, 1)],
                    premises: Vec::new(),
                    ..smt_payload_node_step(1)
                },
            ];
            candidate.reconstruction_plan.final_step = 1;
            candidate.reconstruction_plan.final_proof = smt_false_proof();
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &premise_mismatch_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::ReconstructionPremiseMismatch,
            )),
        );
    }

    #[test]
    fn smt_nonempty_registry_rejects_unknown_rule_and_bad_final_target() {
        let import = verified_smt_import();
        let unknown_rule_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            if let AdvancedSmtReconstructionRule::PayloadNode {
                rule_fingerprint, ..
            } = &mut candidate.reconstruction_plan.steps[0].rule
            {
                *rule_fingerprint = hash(99);
            }
            candidate.reconstruction_plan.steps[0].payload_bindings[0].rule_fingerprint = hash(99);
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &unknown_rule_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );

        let bad_target_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.imported_theory_refs =
                vec![smt_global_ref_for(&import, "S.otherProof")];
            candidate
                .reconstruction_plan
                .steps
                .push(AdvancedMachineSmtReconstructionStep {
                    step_id: 1,
                    rule: AdvancedSmtReconstructionRule::LocalBookkeeping {
                        kind: AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
                            lemma: smt_global_ref_for(&import, "S.otherProof"),
                            level_args: Vec::new(),
                            term_args: Vec::new(),
                        },
                    },
                    payload_bindings: Vec::new(),
                    premises: Vec::new(),
                    conclusion: smt_other(),
                    proof: smt_other_proof(),
                });
            candidate.reconstruction_plan.final_step = 1;
            candidate.reconstruction_plan.final_proof = smt_other_proof();
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &bad_target_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::ReconstructionConclusionMismatch,
            )),
        );
    }

    #[test]
    fn smt_reconstruction_rejects_unresolved_unsorted_imports_and_bad_final_proofs() {
        let import = verified_smt_import();
        let unresolved_import_request = smt_request(&import, |candidate| {
            let mut missing_lemma = smt_global_ref_for(&import, "S.lemma");
            missing_lemma.name = Name::from_dotted("S.missing");
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.imported_theory_refs = vec![missing_lemma.clone()];
            candidate
                .reconstruction_plan
                .steps
                .push(AdvancedMachineSmtReconstructionStep {
                    step_id: 1,
                    rule: AdvancedSmtReconstructionRule::LocalBookkeeping {
                        kind: AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
                            lemma: missing_lemma,
                            level_args: Vec::new(),
                            term_args: Vec::new(),
                        },
                    },
                    payload_bindings: Vec::new(),
                    premises: Vec::new(),
                    conclusion: smt_false(),
                    proof: smt_false_proof(),
                });
            candidate.reconstruction_plan.final_step = 1;
            candidate.reconstruction_plan.final_proof = smt_false_proof();
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &unresolved_import_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::ImportClosureMismatch,
            None,
        );

        let unsorted_import_request = smt_request(&import, |candidate| {
            let mut refs = vec![
                smt_global_ref_for(&import, "S.lemma"),
                smt_global_ref_for(&import, "S.otherProof"),
            ];
            refs.sort_by(|left, right| {
                global_ref_sort_key(right)
                    .unwrap()
                    .cmp(&global_ref_sort_key(left).unwrap())
            });
            candidate.reconstruction_plan.imported_theory_refs = refs;
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &unsorted_import_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::NonCanonicalPayload,
            )),
        );

        let bad_step_proof_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.steps[0].proof = smt_other_proof();
            candidate.reconstruction_plan.final_proof = smt_other_proof();
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &bad_step_proof_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::ReconstructionProofMismatch,
            )),
        );

        let bad_final_proof_request = smt_request(&import, |candidate| {
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
            candidate.reconstruction_plan.final_proof = smt_other_proof();
        });
        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &bad_final_proof_request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::ReconstructionProofMismatch,
            )),
        );
    }

    #[test]
    fn smt_reconstruction_metadata_rejects_stale_reconstruction_plan_hash() {
        let candidate = smt_valid_candidate(hash(11));
        let problem = match &candidate.encoded_problem {
            AdvancedMachineSmtProblemRef::Inline {
                canonical_bytes, ..
            } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
            AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
        };
        let metadata = advanced_ai_smt_certificate_metadata(&candidate, &problem).unwrap();
        assert_eq!(
            advanced_ai_validate_smt_certificate_metadata(&candidate, &problem, &metadata),
            Ok(())
        );

        let mut changed_candidate = candidate.clone();
        changed_candidate.reconstruction_plan.final_proof = smt_other_proof();
        assert_eq!(
            advanced_ai_validate_smt_certificate_metadata(&changed_candidate, &problem, &metadata,),
            Err(AdvancedSmtCertificateError::ReconstructionPlanHashMismatch)
        );
    }

    #[test]
    fn smt_certificate_metadata_and_qf_propositional_smtlib_hash_are_stable() {
        let candidate = smt_valid_candidate(hash(11));
        let problem = match &candidate.encoded_problem {
            AdvancedMachineSmtProblemRef::Inline {
                canonical_bytes, ..
            } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
            AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
        };

        let smtlib = advanced_ai_smt_lib_problem_bytes(&problem).unwrap();
        assert_eq!(
            std::str::from_utf8(&smtlib).unwrap(),
            "(set-option :produce-proofs true)\n\
             (set-logic QF_UF)\n\
             (assert (not false))\n\
             (check-sat)\n\
             (get-proof)\n"
        );
        assert_eq!(
            advanced_ai_smt_classify_supported_fragment(&problem),
            Ok(AdvancedSmtSupportedFragment::QfPropositional)
        );
        assert_eq!(
            advanced_ai_smt_lib_problem_hash(&problem).unwrap(),
            advanced_ai_smt_lib_problem_hash(&problem).unwrap()
        );
        let encoded_problem_hash = advanced_ai_smt_problem_hash(&problem).unwrap();
        assert_eq!(
            advanced_ai_smt_encoding_hash(&problem, encoded_problem_hash),
            advanced_ai_smt_encoding_hash(&problem, encoded_problem_hash)
        );
        assert_eq!(
            advanced_ai_smt_classify_supported_fragment(&smt_problem(
                hash(12),
                AdvancedSmtLogic::MvpQfUf,
                vec![smt_target_command()],
            )),
            Err(AdvancedSmtEncodingError::NonCanonicalPayload)
        );

        let metadata = advanced_ai_smt_certificate_metadata(&candidate, &problem).unwrap();
        assert_eq!(
            metadata.format,
            AdvancedSmtCertificateFormat::MvpProofNodeTableV1
        );
        assert_eq!(metadata.solver, AdvancedSmtSolver::Cvc5);
        assert_eq!(metadata.logic, AdvancedSmtLogic::MvpQfUf);
        assert_eq!(metadata.encoded_goal_hash, problem.goal_fingerprint);
        assert_eq!(
            metadata.reconstruction.rule_registry_profile,
            AdvancedSmtRuleRegistryProfile::MvpEmptyRegistryV1
        );
        assert_eq!(
            advanced_ai_smt_certificate_metadata_hash(&metadata),
            advanced_ai_smt_certificate_metadata_hash(&metadata)
        );
        assert_eq!(
            advanced_ai_validate_smt_certificate_metadata(&candidate, &problem, &metadata),
            Ok(())
        );
    }

    #[test]
    fn smtlib_hash_handoff_binds_smtlib_environment_policy_and_solver_profile() {
        let candidate = smt_valid_candidate(hash(11));
        let problem = match &candidate.encoded_problem {
            AdvancedMachineSmtProblemRef::Inline {
                canonical_bytes, ..
            } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
            AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
        };
        let profile = smt_solver_process_profile(b"cvc5-1.1.2");
        let handoff = advanced_ai_smt_solver_handoff(&problem, &profile, hash(220)).unwrap();

        assert_eq!(handoff.solver, AdvancedSmtSolver::Cvc5);
        assert_eq!(
            handoff.supported_fragment,
            AdvancedSmtSupportedFragment::QfPropositional
        );
        assert_eq!(
            handoff.problem_canonical_bytes,
            advanced_ai_smt_problem_canonical_bytes(&problem).unwrap()
        );
        assert_eq!(
            handoff.smtlib_bytes,
            advanced_ai_smt_lib_problem_bytes(&problem).unwrap()
        );
        assert_eq!(
            handoff.problem_hash,
            advanced_ai_smt_problem_hash(&problem).unwrap()
        );
        assert_eq!(
            handoff.smtlib_hash,
            advanced_ai_smt_lib_problem_hash(&problem).unwrap()
        );
        assert_eq!(
            handoff.encoding_hash,
            advanced_ai_smt_encoding_hash(&problem, handoff.problem_hash)
        );
        assert_eq!(
            handoff.policy_hash,
            advanced_ai_smt_solver_process_policy_hash(&profile.policy).unwrap()
        );
        assert_eq!(
            handoff.solver_process_profile_hash,
            advanced_ai_smt_solver_process_profile_hash(&profile).unwrap()
        );
        assert_eq!(
            advanced_ai_smt_solver_handoff_hash(&handoff).unwrap(),
            advanced_ai_smt_solver_handoff_hash(&handoff).unwrap()
        );

        let changed_version_profile = smt_solver_process_profile(b"cvc5-1.1.3");
        let changed_version_handoff =
            advanced_ai_smt_solver_handoff(&problem, &changed_version_profile, hash(220)).unwrap();
        assert_eq!(handoff.policy_hash, changed_version_handoff.policy_hash);
        assert_ne!(
            handoff.solver_process_profile_hash,
            changed_version_handoff.solver_process_profile_hash
        );
        assert_ne!(
            advanced_ai_smt_solver_handoff_hash(&handoff).unwrap(),
            advanced_ai_smt_solver_handoff_hash(&changed_version_handoff).unwrap()
        );

        let mut tampered_policy_handoff = handoff.clone();
        tampered_policy_handoff.policy_hash = hash(225);
        assert_eq!(
            advanced_ai_validate_smt_solver_process_result(
                &tampered_policy_handoff,
                &profile,
                &smt_solver_result(
                    &tampered_policy_handoff,
                    AdvancedSmtSolverOutputRef::ProofNodeTable {
                        payload_hash: hash(226),
                        node_count: 1,
                        size_bytes: 64,
                    },
                ),
            ),
            Err(AdvancedSmtSolverHandoffError::PolicyHashMismatch {
                expected: handoff.policy_hash,
                actual: hash(225),
            })
        );

        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.solver = AdvancedSmtSolver::Cvc5;
            candidate.rule_registry_profile = AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1;
        });
        let first_hashes = advanced_ai_smt_prove_hashes_from_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        )
        .unwrap();
        let second_hashes = advanced_ai_smt_prove_hashes_from_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        )
        .unwrap();
        assert_eq!(first_hashes, second_hashes);

        let mut mismatched_smtlib = smt_solver_result(
            &handoff,
            AdvancedSmtSolverOutputRef::ProofNodeTable {
                payload_hash: hash(221),
                node_count: 1,
                size_bytes: 64,
            },
        );
        mismatched_smtlib.smtlib_hash = hash(222);
        assert_eq!(
            advanced_ai_validate_smt_solver_process_result(&handoff, &profile, &mismatched_smtlib),
            Err(AdvancedSmtSolverHandoffError::SmtLibHashMismatch {
                expected: handoff.smtlib_hash,
                actual: hash(222),
            })
        );
    }

    #[test]
    fn smt_solver_handoff_rejects_resource_exhaustion_version_mismatch_and_unsupported_fragment() {
        let candidate = smt_valid_candidate(hash(11));
        let problem = match &candidate.encoded_problem {
            AdvancedMachineSmtProblemRef::Inline {
                canonical_bytes, ..
            } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
            AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
        };
        let profile = smt_solver_process_profile(b"cvc5-1.1.2");
        let handoff = advanced_ai_smt_solver_handoff(&problem, &profile, hash(220)).unwrap();

        let changed_version_profile = smt_solver_process_profile(b"cvc5-1.1.3");
        assert_eq!(
            advanced_ai_validate_smt_solver_process_result(
                &handoff,
                &changed_version_profile,
                &smt_solver_result(
                    &handoff,
                    AdvancedSmtSolverOutputRef::ProofNodeTable {
                        payload_hash: hash(223),
                        node_count: 1,
                        size_bytes: 64,
                    },
                ),
            ),
            Err(
                AdvancedSmtSolverHandoffError::SolverVersionMetadataMismatch {
                    expected: handoff.solver_process_profile_hash,
                    actual: advanced_ai_smt_solver_process_profile_hash(&changed_version_profile)
                        .unwrap(),
                }
            )
        );

        let mut exhausted = smt_solver_result(
            &handoff,
            AdvancedSmtSolverOutputRef::ProofNodeTable {
                payload_hash: hash(223),
                node_count: 1,
                size_bytes: 64,
            },
        );
        exhausted.resource_usage.output_bytes = profile.policy.max_output_bytes + 1;
        assert_eq!(
            advanced_ai_validate_smt_solver_process_result(&handoff, &profile, &exhausted),
            Err(AdvancedSmtSolverHandoffError::ResourceLimitExceeded {
                field: AdvancedSmtSolverResourceField::OutputBytes,
                limit: profile.policy.max_output_bytes,
                actual: profile.policy.max_output_bytes + 1,
            })
        );

        let unsupported_bv = smt_problem(
            hash(223),
            AdvancedSmtLogic::MvpQfBv,
            vec![smt_target_command(), smt_final_check_command()],
        );
        assert_eq!(
            advanced_ai_smt_solver_handoff(&unsupported_bv, &profile, hash(220)),
            Err(AdvancedSmtSolverHandoffError::UnsupportedFragment)
        );
    }

    #[test]
    fn smt_euf_lia_and_nat_to_int_encoding_surface_is_deterministic() {
        let user_sort = AdvancedSmtSortExpr::User {
            symbol: smt_symbol("smt:U"),
            args: Vec::new(),
        };
        let euf_problem = smt_problem(
            hash(12),
            AdvancedSmtLogic::MvpQfUf,
            vec![
                smt_command(
                    AdvancedSmtCommandPhase::SortDecl,
                    AdvancedSmtCommandPayload::SortDecl {
                        symbol: smt_symbol("smt:U"),
                        arity: 0,
                    },
                ),
                smt_command(
                    AdvancedSmtCommandPhase::FunctionDecl,
                    AdvancedSmtCommandPayload::FunctionDecl {
                        symbol: smt_symbol("smt:f"),
                        args: vec![user_sort.clone()],
                        result: user_sort,
                    },
                ),
                smt_target_command(),
                smt_final_check_command(),
            ],
        );
        assert_eq!(
            advanced_ai_smt_classify_supported_fragment(&euf_problem),
            Ok(AdvancedSmtSupportedFragment::QfEuf)
        );
        let euf_smtlib =
            String::from_utf8(advanced_ai_smt_lib_problem_bytes(&euf_problem).unwrap()).unwrap();
        assert!(euf_smtlib.contains("(declare-sort |smt:U| 0)\n"));
        assert!(euf_smtlib.contains("(declare-fun |smt:f| (|smt:U|) |smt:U|)\n"));
        let undeclared_euf_problem = smt_problem(
            hash(14),
            AdvancedSmtLogic::MvpQfUf,
            vec![
                smt_command(
                    AdvancedSmtCommandPhase::FunctionDecl,
                    AdvancedSmtCommandPayload::FunctionDecl {
                        symbol: smt_symbol("smt:g"),
                        args: vec![AdvancedSmtSortExpr::User {
                            symbol: smt_symbol("smt:Undeclared"),
                            args: Vec::new(),
                        }],
                        result: AdvancedSmtSortExpr::Bool,
                    },
                ),
                smt_target_command(),
                smt_final_check_command(),
            ],
        );
        assert_eq!(
            advanced_ai_smt_classify_supported_fragment(&undeclared_euf_problem),
            Err(AdvancedSmtEncodingError::NonCanonicalPayload)
        );

        let lia_target = smt_command(
            AdvancedSmtCommandPhase::TargetAssertion,
            AdvancedSmtCommandPayload::TargetAssertion {
                core_expr: smt_false(),
                encoded_expr: AdvancedSmtExpr::BuiltinApp {
                    op: AdvancedSmtBuiltinOp::IntGe,
                    args: vec![AdvancedSmtExpr::IntLit(1), AdvancedSmtExpr::IntLit(0)],
                    result_sort: AdvancedSmtSortExpr::Bool,
                },
            },
        );
        let lia_problem = smt_problem(
            hash(13),
            AdvancedSmtLogic::MvpQfLia,
            vec![lia_target, smt_final_check_command()],
        );
        assert_eq!(
            advanced_ai_smt_classify_supported_fragment(&lia_problem),
            Ok(AdvancedSmtSupportedFragment::QfSimpleLia)
        );
        let lia_smtlib =
            String::from_utf8(advanced_ai_smt_lib_problem_bytes(&lia_problem).unwrap()).unwrap();
        assert!(lia_smtlib.contains("(set-logic QF_LIA)\n"));
        assert!(lia_smtlib.contains("(assert (>= 1 0))\n"));

        let side_condition = advanced_ai_smt_nat_to_int_side_condition(
            Expr::konst("Nat.n", vec![]),
            AdvancedSmtSymbol {
                ascii: b"lc:n_smt".to_vec(),
            },
        );
        assert_eq!(
            side_condition.nonnegative_assertion,
            AdvancedSmtExpr::BuiltinApp {
                op: AdvancedSmtBuiltinOp::IntGe,
                args: vec![
                    AdvancedSmtExpr::Var {
                        symbol: AdvancedSmtSymbol {
                            ascii: b"lc:n_smt".to_vec(),
                        },
                        sort: AdvancedSmtSortExpr::Int,
                    },
                    AdvancedSmtExpr::IntLit(0),
                ],
                result_sort: AdvancedSmtSortExpr::Bool,
            }
        );
        assert_eq!(
            advanced_ai_smt_nat_to_int_side_condition_hash(&side_condition),
            advanced_ai_smt_nat_to_int_side_condition_hash(&side_condition)
        );
    }

    #[test]
    fn smt_alethe_opaque_payload_is_schema_validated_but_not_trusted() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.certificate_format = AdvancedSmtCertificateFormat::AletheOpaqueV1;
            candidate.proof_payload = smt_opaque_payload_ref(
                AdvancedSmtCertificateFormat::AletheOpaqueV1,
                b"(alethe-proof)\n",
            );
            candidate.reconstruction_plan.steps[0].rule =
                AdvancedSmtReconstructionRule::PayloadNode {
                    certificate_format: AdvancedSmtCertificateFormat::AletheOpaqueV1,
                    rule_fingerprint: hash(42),
                };
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );
    }

    #[test]
    fn smt_solver_result_only_is_structured_rejection() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.certificate_format = AdvancedSmtCertificateFormat::SolverResultOnlyV1;
            candidate.proof_payload = smt_opaque_payload_ref(
                AdvancedSmtCertificateFormat::SolverResultOnlyV1,
                b"unsat\n",
            );
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::SolverResultOnly,
            )),
        );

        let candidate = smt_valid_candidate(hash(11));
        let problem = match &candidate.encoded_problem {
            AdvancedMachineSmtProblemRef::Inline {
                canonical_bytes, ..
            } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
            AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
        };
        let profile = smt_solver_process_profile(b"cvc5-1.1.2");
        let handoff = advanced_ai_smt_solver_handoff(&problem, &profile, hash(220)).unwrap();
        for output in [
            AdvancedSmtSolverOutputRef::BareResult {
                result: AdvancedSmtSolverBareResult::Sat,
            },
            AdvancedSmtSolverOutputRef::BareResult {
                result: AdvancedSmtSolverBareResult::Unsat,
            },
            AdvancedSmtSolverOutputRef::BareResult {
                result: AdvancedSmtSolverBareResult::Unknown,
            },
            AdvancedSmtSolverOutputRef::ExitStatus { code: 0 },
            AdvancedSmtSolverOutputRef::Logs {
                stdout_hash: hash(230),
                stderr_hash: hash(231),
                size_bytes: 64,
            },
            AdvancedSmtSolverOutputRef::UncheckedProofText {
                proof_text_hash: hash(232),
                size_bytes: 64,
            },
            AdvancedSmtSolverOutputRef::CertificatePayload {
                certificate_format: AdvancedSmtCertificateFormat::SolverResultOnlyV1,
                payload_hash: hash(233),
                size_bytes: 6,
            },
        ] {
            assert!(matches!(
                advanced_ai_validate_smt_solver_process_result(
                    &handoff,
                    &profile,
                    &smt_solver_result(&handoff, output),
                ),
                Err(AdvancedSmtSolverHandoffError::BareResultOnly
                    | AdvancedSmtSolverHandoffError::ExitStatusOnly
                    | AdvancedSmtSolverHandoffError::LogsOnly
                    | AdvancedSmtSolverHandoffError::UncheckedProofText)
            ));
        }
    }

    #[test]
    fn smt_opaque_payload_hash_mismatch_is_payload_hash_mismatch() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.certificate_format = AdvancedSmtCertificateFormat::LfscOpaqueV1;
            candidate.proof_payload = AdvancedMachineSmtProofPayloadRef::Inline {
                payload_hash: hash(99),
                canonical_bytes: b"(lfsc-proof)\n".to_vec(),
            };
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );

        let candidate = smt_valid_candidate(hash(11));
        let problem = match &candidate.encoded_problem {
            AdvancedMachineSmtProblemRef::Inline {
                canonical_bytes, ..
            } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
            AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
        };
        let profile = smt_solver_process_profile(b"cvc5-1.1.2");
        let handoff = advanced_ai_smt_solver_handoff(&problem, &profile, hash(220)).unwrap();
        assert_eq!(
            advanced_ai_validate_smt_solver_process_result(
                &handoff,
                &profile,
                &smt_solver_result(
                    &handoff,
                    AdvancedSmtSolverOutputRef::CertificatePayload {
                        certificate_format: AdvancedSmtCertificateFormat::AletheOpaqueV1,
                        payload_hash: hash(234),
                        size_bytes: 64,
                    },
                ),
            ),
            Err(AdvancedSmtSolverHandoffError::OpaquePayloadWithoutRegisteredChecker)
        );
        assert_eq!(
            advanced_ai_validate_smt_solver_process_result(
                &handoff,
                &profile,
                &smt_solver_result(
                    &handoff,
                    AdvancedSmtSolverOutputRef::CounterexampleModel {
                        model_hash: hash(235),
                        size_bytes: 64,
                    },
                ),
            ),
            Ok(AdvancedSmtSolverHandoffPayloadKind::CounterexampleModel)
        );
    }

    #[test]
    fn smt_encoded_problem_hash_mismatch_precedes_later_validation() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            if let AdvancedMachineSmtProblemRef::Inline { problem_hash, .. } =
                &mut candidate.encoded_problem
            {
                *problem_hash = hash(77);
            }
            candidate.proof_payload = AdvancedMachineSmtProofPayloadRef::Inline {
                payload_hash: hash(88),
                canonical_bytes: b"malformed".to_vec(),
            };
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
    }

    #[test]
    fn smt_unsupported_logic_operator_is_deterministic_rejection() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            let problem = match &candidate.encoded_problem {
                AdvancedMachineSmtProblemRef::Inline {
                    canonical_bytes, ..
                } => decode_smt_encoded_problem(canonical_bytes).unwrap(),
                AdvancedMachineSmtProblemRef::Artifact { .. } => unreachable!(),
            };
            candidate.encoded_problem = smt_problem_ref(smt_problem(
                problem.goal_fingerprint,
                AdvancedSmtLogic::MvpQfUf,
                vec![
                    smt_command(
                        AdvancedSmtCommandPhase::FunctionDecl,
                        AdvancedSmtCommandPayload::FunctionDecl {
                            symbol: smt_symbol("smt:int_fn"),
                            args: vec![AdvancedSmtSortExpr::Int],
                            result: AdvancedSmtSortExpr::Int,
                        },
                    ),
                    smt_target_command(),
                    smt_final_check_command(),
                ],
            ));
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::UnsupportedFragment,
            )),
        );

        let unsupported_operator = smt_command(
            AdvancedSmtCommandPhase::TargetAssertion,
            AdvancedSmtCommandPayload::TargetAssertion {
                core_expr: smt_false(),
                encoded_expr: AdvancedSmtExpr::BuiltinApp {
                    op: AdvancedSmtBuiltinOp::BvAnd,
                    args: vec![
                        AdvancedSmtExpr::BitVecLit {
                            width: 1,
                            value: vec![1],
                        },
                        AdvancedSmtExpr::BitVecLit {
                            width: 1,
                            value: vec![0],
                        },
                    ],
                    result_sort: AdvancedSmtSortExpr::BitVec { width: 1 },
                },
            },
        );
        assert_eq!(
            advanced_ai_smt_classify_supported_fragment(&smt_problem(
                hash(88),
                AdvancedSmtLogic::MvpQfLia,
                vec![unsupported_operator, smt_final_check_command()],
            )),
            Err(AdvancedSmtEncodingError::UnsupportedFragment)
        );
    }

    #[test]
    fn smt_proof_payload_malformed_is_noncanonical_payload() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.proof_payload = AdvancedMachineSmtProofPayloadRef::Inline {
                payload_hash: hash(88),
                canonical_bytes: b"malformed".to_vec(),
            };
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::MalformedProofPayload,
            )),
        );
    }

    #[test]
    fn smt_local_bookkeeping_payload_binding_mismatch_is_feature_rejected() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.reconstruction_plan = AdvancedMachineSmtReconstructionPlan {
                imported_theory_refs: vec![smt_global_ref_for(&import, "S.lemma")],
                steps: vec![AdvancedMachineSmtReconstructionStep {
                    step_id: 0,
                    rule: AdvancedSmtReconstructionRule::LocalBookkeeping {
                        kind: AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
                            lemma: smt_global_ref_for(&import, "S.lemma"),
                            level_args: Vec::new(),
                            term_args: Vec::new(),
                        },
                    },
                    payload_bindings: vec![AdvancedMachineSmtPayloadBinding {
                        payload_hash: hash(9),
                        node_id: 0,
                        rule_fingerprint: hash(42),
                    }],
                    premises: Vec::new(),
                    conclusion: smt_false(),
                    proof: smt_false_proof(),
                }],
                final_step: 0,
                final_proof: smt_false_proof(),
            };
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::PayloadBindingMismatch,
            )),
        );
    }

    #[test]
    fn smt_local_bookkeeping_premise_mismatch_precedes_empty_registry_rejection() {
        let import = verified_smt_import();
        let request = smt_request(&import, |candidate| {
            candidate.reconstruction_plan = AdvancedMachineSmtReconstructionPlan {
                imported_theory_refs: vec![smt_global_ref_for(&import, "S.lemma")],
                steps: vec![
                    smt_payload_node_step(0),
                    AdvancedMachineSmtReconstructionStep {
                        step_id: 1,
                        rule: AdvancedSmtReconstructionRule::LocalBookkeeping {
                            kind: AdvancedSmtLocalBookkeepingRule::IntroduceTheoryLemma {
                                lemma: smt_global_ref_for(&import, "S.lemma"),
                                level_args: Vec::new(),
                                term_args: Vec::new(),
                            },
                        },
                        payload_bindings: Vec::new(),
                        premises: vec![0],
                        conclusion: smt_false(),
                        proof: smt_false_proof(),
                    },
                ],
                final_step: 1,
                final_proof: smt_false_proof(),
            };
        });

        assert_rejected(
            run_advanced_ai_smt_reconstruct_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::ReconstructionPremiseMismatch,
            )),
        );
    }

    #[test]
    fn typeclass_resolution_direct_instance_returns_unique_proof() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![typeclass_candidate(&import, "TC.instBase", Some(10))],
            1,
            1,
            None,
        );

        let response = run_advanced_ai_typeclass_resolve_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        );

        let AdvancedAiEndpointResponse::Success { payload, .. } = response else {
            panic!("expected typeclass success");
        };
        let AdvancedAiSuccessPayload::TypeclassResolution { proof } = *payload else {
            panic!("expected typeclass payload");
        };
        assert_eq!(proof, Expr::konst("TC.instBase", vec![]));
    }

    #[test]
    fn typeclass_resolution_recursive_instance_returns_unique_proof() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_wrap(typeclass_base()))),
            vec![
                typeclass_candidate(&import, "TC.instWrap", None),
                typeclass_candidate(&import, "TC.instBase", None),
            ],
            2,
            8,
            None,
        );

        let response = run_advanced_ai_typeclass_resolve_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        );

        let AdvancedAiEndpointResponse::Success { payload, .. } = response else {
            panic!("expected typeclass success");
        };
        let AdvancedAiSuccessPayload::TypeclassResolution { proof } = *payload else {
            panic!("expected typeclass payload");
        };
        assert_eq!(
            proof,
            Expr::apps(
                Expr::konst("TC.instWrap", vec![]),
                vec![typeclass_base(), Expr::konst("TC.instBase", vec![])]
            )
        );
    }

    #[test]
    fn typeclass_resolution_no_solution_when_allowlist_cannot_solve_goal() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_wrap(typeclass_base()))),
            vec![typeclass_candidate(&import, "TC.instBase", None)],
            2,
            2,
            None,
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::NoSolution,
            Some(AdvancedAiFeatureError::TypeclassResolution(
                AdvancedTypeclassResolutionError::NoSolution,
            )),
        );
    }

    #[test]
    fn typeclass_resolution_ambiguous_when_two_distinct_proofs_exist() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![
                typeclass_candidate(&import, "TC.instBase", None),
                typeclass_candidate(&import, "TC.instAlt", None),
            ],
            1,
            2,
            None,
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::AmbiguousResolution,
            None,
        );
    }

    #[test]
    fn typeclass_resolution_ambiguity_precedes_later_budget_exhaustion() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![
                typeclass_candidate(&import, "TC.instBase", None),
                typeclass_candidate(&import, "TC.instAlt", None),
                typeclass_candidate(&import, "TC.instWrap", None),
            ],
            1,
            2,
            None,
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::AmbiguousResolution,
            None,
        );
    }

    #[test]
    fn typeclass_resolution_budget_exceeded_for_depth_zero_direct_instance() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![typeclass_candidate(&import, "TC.instBase", None)],
            0,
            1,
            None,
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::BudgetExceeded,
            None,
        );
    }

    #[test]
    fn typeclass_resolution_rejects_invalid_class_declaration() {
        let import = verified_typeclass_import();
        let mut options = AdvancedAiOptions::default();
        options.typeclass.class_declarations =
            vec![typeclass_global_ref_for(&import, "TC.instBase")];
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![typeclass_candidate(&import, "TC.instBase", None)],
            1,
            1,
            Some(options),
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::TypeclassResolution(
                AdvancedTypeclassResolutionError::ClassDeclarationMismatch,
            )),
        );
    }

    #[test]
    fn typeclass_resolution_rejects_unsupported_goal_head() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(Expr::konst("TC.Obj", vec![])),
            vec![typeclass_candidate(&import, "TC.instBase", None)],
            1,
            1,
            None,
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::TypeclassResolution(
                AdvancedTypeclassResolutionError::ClassHeadUnsupported,
            )),
        );
    }

    #[test]
    fn typeclass_resolution_duplicate_candidate_target_is_envelope_malformed() {
        let import = verified_typeclass_import();
        let request = typeclass_request(
            &import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![
                typeclass_candidate(&import, "TC.instBase", Some(1)),
                typeclass_candidate(&import, "TC.instBase", Some(2)),
            ],
            1,
            2,
            None,
        );

        assert_rejected(
            run_advanced_ai_typeclass_resolve_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    #[test]
    fn theorem_graph_query_returns_only_resolved_public_axiom_nodes_with_zero_score() {
        let import = verified_theorem_graph_import();
        let eligible = theorem_graph_node(&import, "GraphLib.P");
        let ineligible = theorem_graph_node(&import, "GraphLib.Type0");
        let missing = missing_theorem_graph_node();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![ineligible, missing, eligible.clone()]);
        let request = theorem_graph_inline_query_request(&import, None, None, snapshot, None, 16);

        let response = run_advanced_ai_theorem_graph_query_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        );

        let AdvancedAiEndpointResponse::Success { payload, .. } = response else {
            panic!("expected theorem graph success");
        };
        let AdvancedAiSuccessPayload::TheoremGraphQuery { result } = *payload else {
            panic!("expected theorem graph payload");
        };
        assert_eq!(result.entries.len(), 1);
        assert_eq!(result.entries[0].node, eligible);
        assert_eq!(result.entries[0].score.score_microunits, 0);
    }

    #[test]
    fn theorem_graph_snapshot_hash_mismatch_is_payload_hash_mismatch() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let request =
            theorem_graph_inline_query_request(&import, Some(hash(99)), None, snapshot, None, 16);

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
    }

    #[test]
    fn theorem_graph_query_features_hash_mismatch_is_payload_hash_mismatch() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let request =
            theorem_graph_inline_query_request(&import, None, Some(hash(98)), snapshot, None, 16);

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
    }

    #[test]
    fn theorem_graph_snapshot_metadata_mismatch_is_snapshot_malformed() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let mut request = decode_candidate_envelope(&theorem_graph_inline_query_request(
            &import, None, None, snapshot, None, 16,
        ))
        .unwrap();
        let mut query = decode_theorem_graph_query(&request.payload).unwrap();
        query.snapshot.source_release_hash = hash(42);
        request.payload = advanced_ai_theorem_graph_query_canonical_bytes(&query).unwrap();
        let request = advanced_ai_candidate_envelope_canonical_bytes(&request).unwrap();

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::TheoremGraphQuery(
                AdvancedTheoremGraphError::SnapshotMalformed,
            )),
        );
    }

    #[test]
    fn theorem_graph_query_features_metadata_mismatch_is_query_features_malformed() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let request_base =
            theorem_graph_inline_query_request(&import, None, None, snapshot, None, 16);
        let envelope = decode_candidate_envelope(&request_base).unwrap();
        let query = decode_theorem_graph_query(&envelope.payload).unwrap();
        let bad_features = theorem_graph_features(query.env_fingerprint, hash(77));
        let request = theorem_graph_inline_query_request(
            &import,
            None,
            None,
            decode_theorem_graph_snapshot(match &query.snapshot.source {
                AdvancedMachineTheoremGraphSnapshotSource::Inline {
                    canonical_bytes, ..
                } => canonical_bytes,
                AdvancedMachineTheoremGraphSnapshotSource::Artifact { .. } => unreachable!(),
            })
            .unwrap(),
            Some(bad_features),
            16,
        );

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::TheoremGraphQuery(
                AdvancedTheoremGraphError::QueryFeaturesMalformed,
            )),
        );
    }

    #[test]
    fn theorem_graph_node_hash_mismatch_is_node_resolution_mismatch() {
        let import = verified_theorem_graph_import();
        let mut node = theorem_graph_node(&import, "GraphLib.P");
        node.type_hash = hash(97);
        let snapshot = theorem_graph_snapshot(hash(41), vec![node]);
        let request = theorem_graph_inline_query_request(&import, None, None, snapshot, None, 16);

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::TheoremGraphQuery(
                AdvancedTheoremGraphError::NodeResolutionMismatch,
            )),
        );
    }

    #[test]
    fn theorem_graph_limit_is_checked_before_artifact_hashes() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let request =
            theorem_graph_inline_query_request(&import, Some(hash(99)), None, snapshot, None, 257);

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::TheoremGraphQuery(
                AdvancedTheoremGraphError::LimitOutOfRange,
            )),
        );
    }

    #[test]
    fn theorem_graph_inline_snapshot_raw_cap_is_snapshot_malformed() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let mut envelope = decode_candidate_envelope(&theorem_graph_inline_query_request(
            &import, None, None, snapshot, None, 16,
        ))
        .unwrap();
        let query = decode_theorem_graph_query(&envelope.payload).unwrap();
        let mut payload = Vec::new();
        encode_hash_to(&mut payload, &query.env_fingerprint);
        encode_hash_to(&mut payload, &query.goal_fingerprint);
        encode_goal_to(&mut payload, &query.goal).unwrap();
        encode_hash_to(&mut payload, &query.snapshot.source_release_hash);
        payload.push(query.snapshot.extractor_version.tag());
        payload.push(0);
        encode_hash_to(&mut payload, &hash(99));
        encode_u64_to(
            &mut payload,
            u64::try_from(MAX_ADVANCED_AI_THEOREM_GRAPH_SNAPSHOT_BYTES).unwrap() + 1,
        );
        encode_theorem_graph_query_features_ref_to(&mut payload, &query.query_features);
        payload.push(query.ranking_profile.tag());
        encode_u64_to(&mut payload, u64::from(query.limit));
        envelope.payload = payload;
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::TheoremGraphQuery(
                AdvancedTheoremGraphError::SnapshotMalformed,
            )),
        );
    }

    #[test]
    fn theorem_graph_inline_query_features_raw_cap_is_query_features_malformed() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let mut envelope = decode_candidate_envelope(&theorem_graph_inline_query_request(
            &import, None, None, snapshot, None, 16,
        ))
        .unwrap();
        let query = decode_theorem_graph_query(&envelope.payload).unwrap();
        let mut payload = Vec::new();
        encode_hash_to(&mut payload, &query.env_fingerprint);
        encode_hash_to(&mut payload, &query.goal_fingerprint);
        encode_goal_to(&mut payload, &query.goal).unwrap();
        encode_theorem_graph_snapshot_ref_to(&mut payload, &query.snapshot).unwrap();
        payload.push(0);
        encode_hash_to(&mut payload, &hash(98));
        encode_u64_to(
            &mut payload,
            u64::try_from(MAX_ADVANCED_AI_THEOREM_GRAPH_QUERY_FEATURES_BYTES).unwrap() + 1,
        );
        payload.push(query.ranking_profile.tag());
        encode_u64_to(&mut payload, u64::from(query.limit));
        envelope.payload = payload;
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            Some(AdvancedAiFeatureError::TheoremGraphQuery(
                AdvancedTheoremGraphError::QueryFeaturesMalformed,
            )),
        );
    }

    #[test]
    fn theorem_graph_snapshot_hash_mismatch_precedes_full_decode_failure() {
        let import = verified_theorem_graph_import();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let mut envelope = decode_candidate_envelope(&theorem_graph_inline_query_request(
            &import, None, None, snapshot, None, 16,
        ))
        .unwrap();
        let mut query = decode_theorem_graph_query(&envelope.payload).unwrap();
        query.snapshot.source = AdvancedMachineTheoremGraphSnapshotSource::Inline {
            graph_snapshot_hash: hash(99),
            canonical_bytes: theorem_graph_snapshot_bytes_with_noncanonical_node_name(hash(41)),
        };
        envelope.payload = advanced_ai_theorem_graph_query_canonical_bytes(&query).unwrap();
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
    }

    #[test]
    fn theorem_graph_snapshot_artifact_file_hash_mismatch_is_payload_hash_mismatch() {
        let import = verified_theorem_graph_import();
        let root = std::env::temp_dir().join(format!("npa-advanced-ai-m4-{}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let snapshot_bytes = advanced_ai_theorem_graph_snapshot_canonical_bytes(&snapshot).unwrap();
        fs::write(root.join("snapshot.bin"), &snapshot_bytes).unwrap();
        let query_features_env = {
            let options_bytes = empty_options_bytes();
            let options_hash = advanced_ai_options_hash(&options_bytes);
            let imports = vec![AdvancedImportIdentity::from_verified_import(&import)];
            advanced_ai_env_fingerprint(
                AdvancedAiProfileVersion::MvpV1,
                AdvancedAiTaskKind::TheoremGraphQuery,
                &imports,
                options_hash,
            )
            .unwrap()
        };
        let goal = theorem_graph_goal();
        let goal_fingerprint = advanced_ai_goal_fingerprint(query_features_env, &goal);
        let features = theorem_graph_features(query_features_env, goal_fingerprint);
        let feature_bytes =
            advanced_ai_theorem_graph_query_features_canonical_bytes(&features).unwrap();
        let query = AdvancedMachineTheoremGraphQuery {
            env_fingerprint: query_features_env,
            goal_fingerprint,
            goal,
            snapshot: AdvancedMachineTheoremGraphSnapshotRef {
                source_release_hash: snapshot.source_release_hash,
                extractor_version: snapshot.extractor_version,
                source: AdvancedMachineTheoremGraphSnapshotSource::Artifact {
                    path: "snapshot.bin".to_owned(),
                    file_hash: hash(1),
                    graph_snapshot_hash: advanced_ai_theorem_graph_snapshot_hash(&snapshot_bytes)
                        .unwrap(),
                    size_bytes: snapshot_bytes.len() as u64,
                },
            },
            query_features: AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
                query_features_hash: advanced_ai_theorem_graph_query_features_hash(&feature_bytes)
                    .unwrap(),
                canonical_bytes: feature_bytes,
            },
            ranking_profile: AdvancedTheoremGraphRankingProfile::MvpTupleOrder,
            limit: 16,
        };
        let options_bytes = empty_options_bytes();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::TheoremGraphQuery,
            target: AdvancedAiTarget {
                env_fingerprint: query_features_env,
                target_decl_hash: None,
                goal_fingerprint: Some(goal_fingerprint),
            },
            imports: vec![AdvancedImportIdentity::from_verified_import(&import)],
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: advanced_ai_theorem_graph_query_canonical_bytes(&query).unwrap(),
        };
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &root,
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn theorem_graph_query_features_artifact_file_hash_mismatch_is_payload_hash_mismatch() {
        let import = verified_theorem_graph_import();
        let root = std::env::temp_dir().join(format!(
            "npa-advanced-ai-m4-features-{}",
            std::process::id()
        ));
        fs::create_dir_all(&root).unwrap();
        let snapshot =
            theorem_graph_snapshot(hash(41), vec![theorem_graph_node(&import, "GraphLib.P")]);
        let mut envelope = decode_candidate_envelope(&theorem_graph_inline_query_request(
            &import, None, None, snapshot, None, 16,
        ))
        .unwrap();
        let mut query = decode_theorem_graph_query(&envelope.payload).unwrap();
        let (query_features_hash, feature_bytes) = match &query.query_features {
            AdvancedMachineTheoremGraphQueryFeaturesRef::Inline {
                query_features_hash,
                canonical_bytes,
            } => (*query_features_hash, canonical_bytes.clone()),
            AdvancedMachineTheoremGraphQueryFeaturesRef::Artifact { .. } => unreachable!(),
        };
        fs::write(root.join("features.bin"), &feature_bytes).unwrap();
        query.query_features = AdvancedMachineTheoremGraphQueryFeaturesRef::Artifact {
            path: "features.bin".to_owned(),
            file_hash: hash(2),
            query_features_hash,
            size_bytes: feature_bytes.len() as u64,
        };
        envelope.payload = advanced_ai_theorem_graph_query_canonical_bytes(&query).unwrap();
        let request = advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap();

        assert_rejected(
            run_advanced_ai_theorem_graph_query_request(
                &request,
                std::slice::from_ref(&import),
                &root,
            ),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn universe_repair_valid_patch_returns_repaired_expr_and_constraint_hash() {
        let import = verified_universe_import();
        let request = valid_universe_request(&import);
        let expected_candidate_hash = advanced_ai_candidate_hash(&request);

        let response = run_advanced_ai_universe_repair_check_request(
            &request,
            std::slice::from_ref(&import),
            &workspace_root(),
        );

        let AdvancedAiEndpointResponse::Success {
            candidate_hash,
            validation_result_hash,
            payload,
        } = response
        else {
            panic!("expected success response");
        };
        assert_eq!(candidate_hash, expected_candidate_hash);
        let expected_payload = AdvancedAiSuccessPayload::UniverseRepair {
            repaired_expr: Expr::konst("Lib.T", vec![Level::succ(Level::param("u"))]),
            constraint_set_hash: advanced_ai_universe_constraint_set_hash(&[]),
        };
        assert_eq!(*payload, expected_payload);
        assert_eq!(
            validation_result_hash,
            advanced_ai_validation_result_hash_for_success(candidate_hash, &expected_payload)
        );
    }

    #[test]
    fn universe_repair_target_decl_hash_mode_is_unsupported() {
        let import = verified_universe_import();
        let request = universe_request_with_target(
            &import,
            valid_universe_candidate(&import),
            Some(hash(88)),
            None,
        );

        assert_rejected(
            run_advanced_ai_universe_repair_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            None,
        );
    }

    #[test]
    fn universe_repair_invalid_path_is_feature_rejection() {
        let import = verified_universe_import();
        let mut candidate = valid_universe_candidate(&import);
        candidate.instantiations[0].occurrence.path = vec![AdvancedMachineExprPathStep::AppFun];
        let request = universe_request_with_target(&import, candidate, None, None);

        assert_rejected(
            run_advanced_ai_universe_repair_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::InvalidOccurrencePath,
            )),
        );
    }

    #[test]
    fn universe_repair_unknown_universe_param_is_feature_rejection() {
        let import = verified_universe_import();
        let mut candidate = valid_universe_candidate(&import);
        candidate.instantiations[0].explicit_level_args = vec![Level::param("v")];
        let request = universe_request_with_target(&import, candidate, None, None);

        assert_rejected(
            run_advanced_ai_universe_repair_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::UnknownUniverseParam,
            )),
        );
    }

    #[test]
    fn universe_repair_arity_mismatch_is_ill_formed_level_expr() {
        let import = verified_universe_import();
        let mut candidate = valid_universe_candidate(&import);
        candidate.instantiations[0].explicit_level_args = Vec::new();
        let request = universe_request_with_target(&import, candidate, None, None);

        assert_rejected(
            run_advanced_ai_universe_repair_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::IllFormedLevelExpr,
            )),
        );
    }

    #[test]
    fn universe_repair_unsatisfied_constraint_is_no_solution() {
        let import = verified_universe_import();
        let target = Expr::app(
            Expr::konst("Lib.F", vec![Level::succ(Level::param("u"))]),
            universe_target_expr(),
        );
        let candidate = AdvancedUniverseRepairCandidate {
            goal: Some(universe_goal(target.clone())),
            target_expr: target,
            instantiations: vec![AdvancedUniverseInstantiationPatch {
                occurrence: AdvancedMachineExprOccurrence {
                    path: vec![AdvancedMachineExprPathStep::AppFun],
                    expected_ref: universe_global_ref_for(&import, "Lib.F"),
                },
                explicit_level_args: vec![Level::param("u")],
            }],
            constraint_hints: Vec::new(),
            minimization_hint: None,
        };
        let request = universe_request_with_target(&import, candidate, None, None);

        assert_rejected(
            run_advanced_ai_universe_repair_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::NoSolution,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::UnsatisfiedConstraint,
            )),
        );
    }

    #[test]
    fn universe_repair_constraint_hint_cannot_add_solver_input() {
        let import = verified_universe_import();
        let mut candidate = valid_universe_candidate(&import);
        candidate.constraint_hints = vec![AdvancedUniverseConstraintHint {
            constraint: AdvancedUniverseConstraint {
                lhs: Level::param("u"),
                relation: AdvancedUniverseConstraintRelation::Le,
                rhs: Level::param("u"),
            },
            reason: AdvancedUniverseConstraintHintReason::RepairCandidate,
        }];
        let request = universe_request_with_target(&import, candidate, None, None);

        assert_rejected(
            run_advanced_ai_universe_repair_check_request(
                &request,
                std::slice::from_ref(&import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::UniverseRepair(
                AdvancedUniverseRepairError::ConstraintHintMismatch,
            )),
        );
    }

    #[test]
    fn universe_repair_minimization_hint_does_not_change_result_payload() {
        let import = verified_universe_import();
        let mut first_candidate = valid_universe_candidate(&import);
        first_candidate.minimization_hint = Some(AdvancedUniverseMinimizationHint::KernelDefault);
        let mut second_candidate = valid_universe_candidate(&import);
        second_candidate.minimization_hint =
            Some(AdvancedUniverseMinimizationHint::PreferLowerLevels);
        let first = run_advanced_ai_universe_repair_check_request(
            &universe_request_with_target(&import, first_candidate, None, None),
            std::slice::from_ref(&import),
            &workspace_root(),
        );
        let second = run_advanced_ai_universe_repair_check_request(
            &universe_request_with_target(&import, second_candidate, None, None),
            std::slice::from_ref(&import),
            &workspace_root(),
        );

        let AdvancedAiEndpointResponse::Success { payload: first, .. } = first else {
            panic!("expected first success");
        };
        let AdvancedAiEndpointResponse::Success {
            payload: second, ..
        } = second
        else {
            panic!("expected second success");
        };
        assert_eq!(first, second);
    }

    #[test]
    fn approved_nested_type_constructor_is_common_unsupported_feature() {
        let mut options = AdvancedAiOptions::default();
        options
            .advanced_inductive
            .approved_nested_type_constructors
            .push(AdvancedAiGlobalRef {
                module: Name::from_dotted("Std.List"),
                export_hash: hash(1),
                certificate_hash: hash(2),
                name: Name::from_dotted("List"),
                decl_interface_hash: hash(3),
            });
        let options_bytes = advanced_ai_options_canonical_bytes(&options).unwrap();
        let request = inline_request(
            AdvancedAiTaskKind::AdvancedInductive,
            options_bytes,
            Vec::new(),
            None,
        );

        assert_rejected(
            run_advanced_ai_inductive_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::AdvancedInductive(
                AdvancedInductiveError::PositivityProfileUnsupported,
            )),
        );
    }

    fn formalization_options_bytes_with(
        tactic_options: MachineTacticOptions,
        tactic_budget: TacticBudget,
    ) -> Vec<u8> {
        let options = AdvancedAiOptions {
            formalization: Some(AdvancedFormalizationOptions {
                tactic_options_canonical_bytes: machine_tactic_options_canonical_bytes(
                    &tactic_options,
                ),
                tactic_budget_canonical_bytes: tactic_budget_canonical_bytes(tactic_budget),
            }),
            ..Default::default()
        };
        advanced_ai_options_canonical_bytes(&options).unwrap()
    }

    fn formalization_options_bytes() -> Vec<u8> {
        formalization_options_bytes_with(MachineTacticOptions::default(), TacticBudget::default())
    }

    fn machine_term_canonical_bytes(source: &str) -> Vec<u8> {
        npa_frontend::canonicalize_machine_term_source(source)
            .unwrap()
            .canonical_bytes
    }

    fn formalization_statement(source: &str) -> AdvancedMachineSurfaceTerm {
        AdvancedMachineSurfaceTerm {
            universe_params: Vec::new(),
            term_canonical_bytes: machine_term_canonical_bytes(source),
        }
    }

    #[test]
    fn advanced_ai_formalization_statement_fixture_stays_machine_surface_canonical() {
        let statement = formalization_statement("Prop");
        let canonical = npa_frontend::canonicalize_machine_term_source("Prop").unwrap();

        assert_eq!(statement.term_canonical_bytes, canonical.canonical_bytes);
        npa_frontend::decode_machine_term_source_canonical(&statement.term_canonical_bytes).expect(
            "advanced AI fixture statement must decode as Machine Surface canonical source",
        );

        for source in [
            "def Test.x : Prop := Prop",
            "notation \"x\" => Prop",
            "Prop + Prop",
            "_",
        ] {
            assert!(
                npa_frontend::canonicalize_machine_term_source(source).is_err(),
                "advanced AI formalization fixtures must not accept Human syntax: {source}"
            );
        }
    }

    fn formalization_source(
        source_text: &str,
    ) -> (
        AdvancedMachineFormalizationSourceDocumentRef,
        AdvancedMachineFormalizationClaimSpan,
        Hash,
        Hash,
    ) {
        let bytes = source_text.as_bytes();
        let source_document_hash = advanced_ai_formalization_source_document_hash(bytes);
        let claim_span_hash = advanced_ai_formalization_claim_span_hash(
            source_document_hash,
            0,
            bytes.len() as u64,
            bytes,
        );
        (
            AdvancedMachineFormalizationSourceDocumentRef::Inline {
                source_document_hash,
                raw_utf8_bytes: bytes.to_vec(),
            },
            AdvancedMachineFormalizationClaimSpan {
                start_byte: 0,
                end_byte: bytes.len() as u64,
                claim_span_hash,
            },
            source_document_hash,
            claim_span_hash,
        )
    }

    fn formalization_request(
        payload: AdvancedMachineFormalizationCheckPayload,
        options_bytes: Vec<u8>,
    ) -> Vec<u8> {
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let imports = Vec::new();
        let envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::NaturalLanguageFormalization,
            target: target_for(
                AdvancedAiTaskKind::NaturalLanguageFormalization,
                &imports,
                options_hash,
                None,
            ),
            imports,
            options: AdvancedAiOptionsRef::Inline {
                options_hash,
                canonical_bytes: options_bytes,
            },
            payload: advanced_ai_formalization_payload_canonical_bytes(&payload).unwrap(),
        };
        advanced_ai_candidate_envelope_canonical_bytes(&envelope).unwrap()
    }

    fn formalization_payload_with(
        source_text: &str,
        statement_source: &str,
        intent_record: Option<AdvancedFormalizationIntentRecord>,
        optional_proof_candidate: Option<AdvancedMachineFormalizationProofCandidate>,
    ) -> AdvancedMachineFormalizationCheckPayload {
        let (source_document, claim_span, _, _) = formalization_source(source_text);
        AdvancedMachineFormalizationCheckPayload {
            candidate: AdvancedMachineFormalizationCandidate {
                source_document,
                claim_span,
                statement: formalization_statement(statement_source),
                optional_proof_candidate,
            },
            intent_record,
        }
    }

    fn accepted_statement_hash_for_options(options_bytes: &[u8], statement_source: &str) -> Hash {
        let imports = Vec::new();
        let options_hash = advanced_ai_options_hash(options_bytes);
        let env_fingerprint = advanced_ai_env_fingerprint(
            AdvancedAiProfileVersion::MvpV1,
            AdvancedAiTaskKind::NaturalLanguageFormalization,
            &imports,
            options_hash,
        )
        .unwrap();
        let statement = formalization_statement(statement_source);
        let ast =
            npa_frontend::decode_machine_term_source_canonical(&statement.term_canonical_bytes)
                .unwrap();
        let context = npa_frontend::MachineTermElabContext::from_verified_modules(
            &[],
            &[],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let options = npa_frontend::MachineCompileOptions {
            mode: npa_frontend::MachineSurfaceMode::Complete,
            allow_universe_meta: false,
        };
        let (accepted, _) =
            npa_frontend::elaborate_machine_term_infer_from_ast(&ast, &context, &options).unwrap();
        advanced_ai_formalization_accepted_statement_hash(env_fingerprint, &[], &accepted)
    }

    fn intent_record_for(
        source_text: &str,
        statement: &AdvancedMachineSurfaceTerm,
        status: AdvancedFormalizationIntentStatus,
    ) -> AdvancedFormalizationIntentRecord {
        let (_, _, source_document_hash, claim_span_hash) = formalization_source(source_text);
        AdvancedFormalizationIntentRecord {
            source_document_hash,
            claim_span_hash,
            candidate_statement_hash: advanced_ai_formalization_candidate_statement_hash(statement),
            status,
        }
    }

    fn exact_proof_candidate(
        statement: &AdvancedMachineSurfaceTerm,
        proof_source: &str,
    ) -> AdvancedMachineFormalizationProofCandidate {
        AdvancedMachineFormalizationProofCandidate {
            candidate_statement_hash: advanced_ai_formalization_candidate_statement_hash(statement),
            tactic: MachineTacticCandidate::Exact {
                term: RawMachineTerm::new(proof_source),
            },
        }
    }

    fn assert_formalization_success_kind(
        response: AdvancedAiEndpointResponse,
        expected_kind: AdvancedFormalizationSuccessKind,
    ) -> (Hash, Option<Hash>, Option<Hash>) {
        let AdvancedAiEndpointResponse::Success {
            candidate_hash,
            payload,
            ..
        } = response
        else {
            panic!("expected formalization success");
        };
        let AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind,
            accepted_statement_hash,
            formalization_proof_root_hash,
        } = *payload
        else {
            panic!("expected formalization payload");
        };
        assert_eq!(kind, expected_kind);
        (
            candidate_hash,
            accepted_statement_hash,
            formalization_proof_root_hash,
        )
    }

    #[test]
    fn formalization_source_and_rejection_reason_artifacts_are_validated() {
        let root = std::env::temp_dir().join(format!(
            "npa-advanced-ai-formalization-artifacts-{}",
            std::process::id()
        ));
        fs::create_dir_all(&root).unwrap();
        let source_bytes = b"claim: rejected artifact";
        let reason_bytes = b"reviewer rejected this claim";
        fs::write(root.join("source.txt"), source_bytes).unwrap();
        fs::write(root.join("reason.txt"), reason_bytes).unwrap();

        let source_document_hash = advanced_ai_formalization_source_document_hash(source_bytes);
        let claim_span_hash = advanced_ai_formalization_claim_span_hash(
            source_document_hash,
            0,
            source_bytes.len() as u64,
            source_bytes,
        );
        let statement = formalization_statement("MissingFormalizationName");
        let rejection_reason_hash = advanced_ai_formalization_rejection_reason_hash(reason_bytes);
        let payload = AdvancedMachineFormalizationCheckPayload {
            candidate: AdvancedMachineFormalizationCandidate {
                source_document: AdvancedMachineFormalizationSourceDocumentRef::Artifact {
                    path: "source.txt".to_owned(),
                    file_hash: advanced_ai_file_hash(source_bytes),
                    source_document_hash,
                    size_bytes: source_bytes.len() as u64,
                },
                claim_span: AdvancedMachineFormalizationClaimSpan {
                    start_byte: 0,
                    end_byte: source_bytes.len() as u64,
                    claim_span_hash,
                },
                statement: statement.clone(),
                optional_proof_candidate: None,
            },
            intent_record: Some(AdvancedFormalizationIntentRecord {
                source_document_hash,
                claim_span_hash,
                candidate_statement_hash: advanced_ai_formalization_candidate_statement_hash(
                    &statement,
                ),
                status: AdvancedFormalizationIntentStatus::Rejected {
                    reviewer: AdvancedReviewerId::Human {
                        stable_id_ascii: b"reviewer-1".to_vec(),
                    },
                    rejection_reason: AdvancedMachineFormalizationRejectionReasonRef::Artifact {
                        path: "reason.txt".to_owned(),
                        file_hash: advanced_ai_file_hash(reason_bytes),
                        rejection_reason_hash,
                        size_bytes: reason_bytes.len() as u64,
                    },
                    rejection_reason_hash,
                },
            }),
        };
        let request = formalization_request(payload.clone(), formalization_options_bytes());

        assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&request, &[], &root),
            AdvancedFormalizationSuccessKind::IntentRecordOnly,
        );

        let mut bad_payload = payload;
        if let AdvancedMachineFormalizationSourceDocumentRef::Artifact { file_hash, .. } =
            &mut bad_payload.candidate.source_document
        {
            *file_hash = hash(99);
        }
        let bad_request = formalization_request(bad_payload, formalization_options_bytes());
        assert_rejected(
            run_advanced_ai_formalize_check_request(&bad_request, &[], &root),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn formalization_rejected_intent_with_proof_candidate_is_rejected() {
        let statement = formalization_statement("Type");
        let reason = b"claim does not match the intended theorem".to_vec();
        let reason_hash = advanced_ai_formalization_rejection_reason_hash(&reason);
        let intent = intent_record_for(
            "claim: rejected",
            &statement,
            AdvancedFormalizationIntentStatus::Rejected {
                reviewer: AdvancedReviewerId::Human {
                    stable_id_ascii: b"reviewer@example.com".to_vec(),
                },
                rejection_reason: AdvancedMachineFormalizationRejectionReasonRef::Inline {
                    rejection_reason_hash: reason_hash,
                    raw_utf8_bytes: reason,
                },
                rejection_reason_hash: reason_hash,
            },
        );
        let proof = exact_proof_candidate(&statement, "Prop");
        let payload =
            formalization_payload_with("claim: rejected", "Type", Some(intent), Some(proof));
        let request = formalization_request(payload, formalization_options_bytes());

        assert_rejected(
            run_advanced_ai_formalize_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::Formalization(
                AdvancedFormalizationError::RejectedIntentHasProofCandidate,
            )),
        );
    }

    #[test]
    fn formalization_intent_status_fixtures_are_deterministic() {
        let options_bytes = formalization_options_bytes();
        let statement = formalization_statement("Prop");

        let unreviewed = intent_record_for(
            "claim: unreviewed",
            &statement,
            AdvancedFormalizationIntentStatus::Unreviewed,
        );
        let unreviewed_request = formalization_request(
            formalization_payload_with("claim: unreviewed", "Prop", Some(unreviewed), None),
            options_bytes.clone(),
        );
        let (_, unreviewed_accepted, unreviewed_root) = assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&unreviewed_request, &[], &workspace_root()),
            AdvancedFormalizationSuccessKind::CandidateStatementChecked,
        );
        assert!(unreviewed_accepted.is_some());
        assert_eq!(unreviewed_root, None);

        let reviewed_hash = accepted_statement_hash_for_options(&options_bytes, "Prop");
        let reviewed = intent_record_for(
            "claim: reviewed",
            &statement,
            AdvancedFormalizationIntentStatus::Reviewed {
                reviewer: AdvancedReviewerId::System {
                    system_id_ascii: b"review-ui".to_vec(),
                    actor_id_ascii: b"user-123".to_vec(),
                },
                accepted_statement_hash: reviewed_hash,
            },
        );
        let reviewed_request = formalization_request(
            formalization_payload_with("claim: reviewed", "Prop", Some(reviewed), None),
            options_bytes.clone(),
        );
        let (_, reviewed_accepted, reviewed_root) = assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&reviewed_request, &[], &workspace_root()),
            AdvancedFormalizationSuccessKind::CandidateStatementChecked,
        );
        assert_eq!(reviewed_accepted, Some(reviewed_hash));
        assert_eq!(reviewed_root, None);

        let rejected_statement = formalization_statement("MissingFormalizationName");
        let reason = b"not the theorem the reviewer intended".to_vec();
        let reason_hash = advanced_ai_formalization_rejection_reason_hash(&reason);
        let rejected = intent_record_for(
            "claim: rejected",
            &rejected_statement,
            AdvancedFormalizationIntentStatus::Rejected {
                reviewer: AdvancedReviewerId::Human {
                    stable_id_ascii: b"reviewer-1".to_vec(),
                },
                rejection_reason: AdvancedMachineFormalizationRejectionReasonRef::Inline {
                    rejection_reason_hash: reason_hash,
                    raw_utf8_bytes: reason,
                },
                rejection_reason_hash: reason_hash,
            },
        );
        let rejected_request = formalization_request(
            formalization_payload_with(
                "claim: rejected",
                "MissingFormalizationName",
                Some(rejected),
                None,
            ),
            options_bytes,
        );
        let (_, rejected_accepted, rejected_root) = assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&rejected_request, &[], &workspace_root()),
            AdvancedFormalizationSuccessKind::IntentRecordOnly,
        );
        assert_eq!(rejected_accepted, None);
        assert_eq!(rejected_root, None);
    }

    #[test]
    fn formalization_statement_and_proof_bridge_failures_are_distinct() {
        let bad_statement_request = formalization_request(
            formalization_payload_with("claim: unknown", "UnknownFormalizationName", None, None),
            formalization_options_bytes(),
        );
        assert_rejected(
            run_advanced_ai_formalize_check_request(&bad_statement_request, &[], &workspace_root()),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::Formalization(
                AdvancedFormalizationError::CandidateStatementElaborationFailed,
            )),
        );

        let statement = formalization_statement("Type");
        let proof = exact_proof_candidate(&statement, "Type");
        let bad_proof_request = formalization_request(
            formalization_payload_with("claim: type", "Type", None, Some(proof)),
            formalization_options_bytes(),
        );
        assert_rejected(
            run_advanced_ai_formalize_check_request(&bad_proof_request, &[], &workspace_root()),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::Formalization(
                AdvancedFormalizationError::ProofBridgeFailed,
            )),
        );
    }

    #[test]
    fn formalization_single_tactic_bridge_can_check_proof_candidate() {
        let statement = formalization_statement("Type");
        let proof = exact_proof_candidate(&statement, "Prop");
        let request = formalization_request(
            formalization_payload_with("claim: Type", "Type", None, Some(proof)),
            formalization_options_bytes(),
        );

        let (_, accepted_statement_hash, proof_root_hash) = assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&request, &[], &workspace_root()),
            AdvancedFormalizationSuccessKind::ProofBridgeChecked,
        );

        assert!(accepted_statement_hash.is_some());
        assert!(proof_root_hash.is_some());
    }

    #[test]
    fn formalization_source_text_does_not_define_theorem_statement() {
        let options_bytes = formalization_options_bytes();
        let first = formalization_request(
            formalization_payload_with("natural language confidence: 10%", "Prop", None, None),
            options_bytes.clone(),
        );
        let second = formalization_request(
            formalization_payload_with("natural language confidence: 99%", "Prop", None, None),
            options_bytes,
        );

        let (first_candidate, first_accepted, _) = assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&first, &[], &workspace_root()),
            AdvancedFormalizationSuccessKind::CandidateStatementChecked,
        );
        let (second_candidate, second_accepted, _) = assert_formalization_success_kind(
            run_advanced_ai_formalize_check_request(&second, &[], &workspace_root()),
            AdvancedFormalizationSuccessKind::CandidateStatementChecked,
        );

        assert_ne!(first_candidate, second_candidate);
        assert_eq!(first_accepted, second_accepted);
    }

    #[test]
    fn formalization_reviewer_id_regex_is_envelope_validation() {
        let statement = formalization_statement("Prop");
        let reviewed_hash =
            accepted_statement_hash_for_options(&formalization_options_bytes(), "Prop");
        let intent = intent_record_for(
            "claim: reviewed",
            &statement,
            AdvancedFormalizationIntentStatus::Reviewed {
                reviewer: AdvancedReviewerId::Human {
                    stable_id_ascii: b"bad reviewer".to_vec(),
                },
                accepted_statement_hash: reviewed_hash,
            },
        );
        let request = formalization_request(
            formalization_payload_with("claim: reviewed", "Prop", Some(intent), None),
            formalization_options_bytes(),
        );

        assert_rejected(
            run_advanced_ai_formalize_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    #[test]
    fn formalization_tactic_options_shape_is_required_without_proof_candidate() {
        let tactic_options = MachineTacticOptions {
            max_simp_rewrite_steps: 0,
            ..Default::default()
        };
        let request = formalization_request(
            formalization_payload_with("claim: Prop", "Prop", None, None),
            formalization_options_bytes_with(tactic_options, TacticBudget::default()),
        );

        assert_rejected(
            run_advanced_ai_formalize_check_request(&request, &[], &workspace_root()),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
    }

    #[test]
    fn advanced_ai_m9_endpoint_fixture_matrix_is_deterministic_without_ai() {
        type AdvancedRoute = fn(&[u8], &[VerifiedImportRef], &Path) -> AdvancedAiEndpointResponse;
        let routes: [(&str, AdvancedRoute); 6] = [
            (
                ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
                run_advanced_ai_inductive_check_request,
            ),
            (
                ADVANCED_AI_UNIVERSE_REPAIR_CHECK_ENDPOINT,
                run_advanced_ai_universe_repair_check_request,
            ),
            (
                ADVANCED_AI_TYPECLASS_RESOLVE_ENDPOINT,
                run_advanced_ai_typeclass_resolve_request,
            ),
            (
                ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT,
                run_advanced_ai_smt_reconstruct_request,
            ),
            (
                ADVANCED_AI_THEOREM_GRAPH_QUERY_ENDPOINT,
                run_advanced_ai_theorem_graph_query_request,
            ),
            (
                ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT,
                run_advanced_ai_formalize_check_request,
            ),
        ];

        for (endpoint, route) in routes {
            let fixture = format!(
                "advanced_ai_m9_{}_error_noncanonical_request",
                advanced_ai_m9_endpoint_token(endpoint)
            );
            assert_advanced_ai_m9_error_fixture(
                &fixture,
                endpoint,
                route(b"not-an-envelope", &[], &workspace_root()),
                AdvancedAiEndpointError::NonCanonicalRequestBytes,
            );
        }

        let inductive_request = inductive_request(valid_inductive_proposal());
        let inductive_first =
            run_advanced_ai_inductive_check_request(&inductive_request, &[], &workspace_root());
        let inductive_second =
            run_advanced_ai_inductive_check_request(&inductive_request, &[], &workspace_root());
        assert_eq!(inductive_first, inductive_second);
        let (_, inductive_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_inductive_check_success_advanced_inductive",
            ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
            inductive_first,
        );
        assert!(matches!(
            inductive_payload,
            AdvancedAiSuccessPayload::AdvancedInductive { .. }
        ));
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_inductive_check_rejected_envelope_malformed_payload",
            ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
            run_advanced_ai_inductive_check_request(
                &inline_request(
                    AdvancedAiTaskKind::AdvancedInductive,
                    empty_options_bytes(),
                    Vec::new(),
                    None,
                ),
                &[],
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );

        let universe_import = verified_universe_import();
        let universe_request = valid_universe_request(&universe_import);
        let universe_first = run_advanced_ai_universe_repair_check_request(
            &universe_request,
            std::slice::from_ref(&universe_import),
            &workspace_root(),
        );
        let universe_second = run_advanced_ai_universe_repair_check_request(
            &universe_request,
            std::slice::from_ref(&universe_import),
            &workspace_root(),
        );
        assert_eq!(universe_first, universe_second);
        let (_, universe_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_universe_repair_check_success_repaired_expr",
            ADVANCED_AI_UNIVERSE_REPAIR_CHECK_ENDPOINT,
            universe_first,
        );
        assert!(matches!(
            universe_payload,
            AdvancedAiSuccessPayload::UniverseRepair { .. }
        ));
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_universe_repair_check_rejected_envelope_malformed_payload",
            ADVANCED_AI_UNIVERSE_REPAIR_CHECK_ENDPOINT,
            run_advanced_ai_universe_repair_check_request(
                &inline_request(
                    AdvancedAiTaskKind::UniverseRepair,
                    empty_options_bytes(),
                    Vec::new(),
                    Some(hash(11)),
                ),
                &[],
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );

        let typeclass_import = verified_typeclass_import();
        let typeclass_request = typeclass_request(
            &typeclass_import,
            typeclass_goal(typeclass_cls(typeclass_base())),
            vec![typeclass_candidate(
                &typeclass_import,
                "TC.instBase",
                Some(10),
            )],
            1,
            1,
            None,
        );
        let typeclass_first = run_advanced_ai_typeclass_resolve_request(
            &typeclass_request,
            std::slice::from_ref(&typeclass_import),
            &workspace_root(),
        );
        let typeclass_second = run_advanced_ai_typeclass_resolve_request(
            &typeclass_request,
            std::slice::from_ref(&typeclass_import),
            &workspace_root(),
        );
        assert_eq!(typeclass_first, typeclass_second);
        let (_, typeclass_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_typeclass_resolve_success_direct_instance",
            ADVANCED_AI_TYPECLASS_RESOLVE_ENDPOINT,
            typeclass_first,
        );
        assert!(matches!(
            typeclass_payload,
            AdvancedAiSuccessPayload::TypeclassResolution { .. }
        ));
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_typeclass_resolve_rejected_envelope_malformed_payload",
            ADVANCED_AI_TYPECLASS_RESOLVE_ENDPOINT,
            run_advanced_ai_typeclass_resolve_request(
                &inline_request(
                    AdvancedAiTaskKind::TypeclassResolution,
                    empty_options_bytes(),
                    Vec::new(),
                    Some(hash(12)),
                ),
                &[],
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );

        let smt_import = verified_smt_import();
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_smt_reconstruct_rejected_empty_registry",
            ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT,
            run_advanced_ai_smt_reconstruct_request(
                &smt_request(&smt_import, |_| {}),
                std::slice::from_ref(&smt_import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );

        let graph_import = verified_theorem_graph_import();
        let graph_snapshot = theorem_graph_snapshot(
            hash(41),
            vec![theorem_graph_node(&graph_import, "GraphLib.P")],
        );
        let graph_request =
            theorem_graph_inline_query_request(&graph_import, None, None, graph_snapshot, None, 16);
        let graph_first = run_advanced_ai_theorem_graph_query_request(
            &graph_request,
            std::slice::from_ref(&graph_import),
            &workspace_root(),
        );
        let graph_second = run_advanced_ai_theorem_graph_query_request(
            &graph_request,
            std::slice::from_ref(&graph_import),
            &workspace_root(),
        );
        assert_eq!(graph_first, graph_second);
        let (_, graph_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_theorem_graph_query_success_public_axiom_node",
            ADVANCED_AI_THEOREM_GRAPH_QUERY_ENDPOINT,
            graph_first,
        );
        assert!(matches!(
            graph_payload,
            AdvancedAiSuccessPayload::TheoremGraphQuery { .. }
        ));
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_theorem_graph_query_rejected_envelope_malformed_payload",
            ADVANCED_AI_THEOREM_GRAPH_QUERY_ENDPOINT,
            run_advanced_ai_theorem_graph_query_request(
                &inline_request(
                    AdvancedAiTaskKind::TheoremGraphQuery,
                    empty_options_bytes(),
                    Vec::new(),
                    Some(hash(13)),
                ),
                &[],
                &workspace_root(),
            ),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );

        let formalization_statement = formalization_statement("Type");
        let formalization_success_request = formalization_request(
            formalization_payload_with(
                "claim: Type",
                "Type",
                None,
                Some(exact_proof_candidate(&formalization_statement, "Prop")),
            ),
            formalization_options_bytes(),
        );
        let formalization_first = run_advanced_ai_formalize_check_request(
            &formalization_success_request,
            &[],
            &workspace_root(),
        );
        let formalization_second = run_advanced_ai_formalize_check_request(
            &formalization_success_request,
            &[],
            &workspace_root(),
        );
        assert_eq!(formalization_first, formalization_second);
        let (_, formalization_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_formalize_check_success_proof_bridge_checked",
            ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT,
            formalization_first,
        );
        assert!(matches!(
            formalization_payload,
            AdvancedAiSuccessPayload::NaturalLanguageFormalization {
                kind: AdvancedFormalizationSuccessKind::ProofBridgeChecked,
                ..
            }
        ));
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_formalize_check_rejected_statement_elaboration_failed",
            ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT,
            run_advanced_ai_formalize_check_request(
                &formalization_request(
                    formalization_payload_with(
                        "claim: unknown",
                        "UnknownFormalizationName",
                        None,
                        None,
                    ),
                    formalization_options_bytes(),
                ),
                &[],
                &workspace_root(),
            ),
            AdvancedAiValidationError::FeatureRejected,
            Some(AdvancedAiFeatureError::Formalization(
                AdvancedFormalizationError::CandidateStatementElaborationFailed,
            )),
        );
    }

    #[test]
    fn advanced_ai_m9_artifact_replay_uses_exact_bytes_and_stable_hashes() {
        let root = std::env::temp_dir().join(format!(
            "npa-advanced-ai-m9-artifact-replay-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();

        let options_bytes = empty_options_bytes();
        fs::write(root.join("options.bin"), &options_bytes).unwrap();
        let options_hash = advanced_ai_options_hash(&options_bytes);
        let proposal = valid_inductive_proposal();
        let artifact_envelope = AdvancedAiCandidateEnvelope {
            profile_version: AdvancedAiProfileVersion::MvpV1,
            task_kind: AdvancedAiTaskKind::AdvancedInductive,
            target: AdvancedAiTarget {
                env_fingerprint: advanced_ai_env_fingerprint(
                    AdvancedAiProfileVersion::MvpV1,
                    AdvancedAiTaskKind::AdvancedInductive,
                    &[],
                    options_hash,
                )
                .unwrap(),
                target_decl_hash: None,
                goal_fingerprint: None,
            },
            imports: Vec::new(),
            options: AdvancedAiOptionsRef::Artifact {
                path: "options.bin".to_owned(),
                file_hash: advanced_ai_file_hash(&options_bytes),
                options_hash,
                size_bytes: options_bytes.len() as u64,
            },
            payload: advanced_ai_inductive_proposal_canonical_bytes(&proposal).unwrap(),
        };
        let artifact_request =
            advanced_ai_candidate_envelope_canonical_bytes(&artifact_envelope).unwrap();
        let inline_request = inductive_request(proposal);

        let artifact_first = run_advanced_ai_inductive_check_request(&artifact_request, &[], &root);
        let artifact_second =
            run_advanced_ai_inductive_check_request(&artifact_request, &[], &root);
        assert_eq!(artifact_first, artifact_second);
        let (_, artifact_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_inductive_check_success_artifact_options_replay",
            ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
            artifact_first,
        );
        let (_, inline_payload) = assert_success(run_advanced_ai_inductive_check_request(
            &inline_request,
            &[],
            &workspace_root(),
        ));
        assert_eq!(artifact_payload, inline_payload);

        fs::write(root.join("options.bin"), b"corrupt-options").unwrap();
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_inductive_check_rejected_artifact_payload_hash_mismatch",
            ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
            run_advanced_ai_inductive_check_request(&artifact_request, &[], &root),
            AdvancedAiValidationError::PayloadHashMismatch,
            None,
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn p9h00_advanced_ai_sidecars_scores_and_smt_outputs_stay_untrusted() {
        let graph_import = verified_theorem_graph_import();
        let graph_node = theorem_graph_node(&graph_import, "GraphLib.P");
        let graph_snapshot = theorem_graph_snapshot(hash(41), vec![graph_node.clone()]);
        let graph_request =
            theorem_graph_inline_query_request(&graph_import, None, None, graph_snapshot, None, 16);
        let (_, graph_payload) = assert_success(run_advanced_ai_theorem_graph_query_request(
            &graph_request,
            std::slice::from_ref(&graph_import),
            &workspace_root(),
        ));
        let AdvancedAiSuccessPayload::TheoremGraphQuery { result } = graph_payload else {
            panic!("expected theorem graph payload");
        };
        assert_eq!(result.entries.len(), 1);
        assert_eq!(result.entries[0].node, graph_node);
        assert_eq!(result.entries[0].score.score_microunits, 0);

        let smt_import = verified_smt_import();
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_smt_reconstruct_rejected_p9h00_solver_output_not_checker_verdict",
            ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT,
            run_advanced_ai_smt_reconstruct_request(
                &smt_request(&smt_import, |_| {}),
                std::slice::from_ref(&smt_import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );

        let statement = formalization_statement("Type");
        let first = formalization_request(
            formalization_payload_with(
                "AI sidecar text, confidence 10%",
                "Type",
                None,
                Some(exact_proof_candidate(&statement, "Prop")),
            ),
            formalization_options_bytes(),
        );
        let second = formalization_request(
            formalization_payload_with(
                "different sidecar text, confidence 99%",
                "Type",
                None,
                Some(exact_proof_candidate(&statement, "Prop")),
            ),
            formalization_options_bytes(),
        );
        let (first_candidate_hash, first_payload) = assert_success(
            run_advanced_ai_formalize_check_request(&first, &[], &workspace_root()),
        );
        let (second_candidate_hash, second_payload) = assert_success(
            run_advanced_ai_formalize_check_request(&second, &[], &workspace_root()),
        );
        assert_ne!(first_candidate_hash, second_candidate_hash);

        let AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind: first_kind,
            accepted_statement_hash: first_accepted,
            formalization_proof_root_hash: first_root,
        } = first_payload
        else {
            panic!("expected formalization payload");
        };
        let AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind: second_kind,
            accepted_statement_hash: second_accepted,
            formalization_proof_root_hash: second_root,
        } = second_payload
        else {
            panic!("expected formalization payload");
        };
        assert_eq!(
            first_kind,
            AdvancedFormalizationSuccessKind::ProofBridgeChecked
        );
        assert_eq!(
            second_kind,
            AdvancedFormalizationSuccessKind::ProofBridgeChecked
        );
        assert_eq!(first_accepted, second_accepted);
        assert_eq!(first_root, second_root);

        let proof_root = first_root.unwrap();
        let theorem_cert = npa_cert::build_module_cert(
            CoreModule {
                name: formalization_scratch_module(proof_root),
                declarations: vec![Decl::Theorem {
                    name: formalization_scratch_theorem(proof_root).as_dotted(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::succ(Level::zero())),
                    proof: Expr::sort(Level::zero()),
                }],
            },
            &[],
        )
        .unwrap();
        let theorem_bytes = npa_cert::encode_module_cert(&theorem_cert).unwrap();
        let mut verifier_session = VerifierSession::new();
        let verified = npa_cert::verify_module_cert(
            &theorem_bytes,
            &mut verifier_session,
            &AxiomPolicy::normal(),
        )
        .unwrap();
        assert_eq!(
            theorem_cert.hashes.certificate_hash,
            verified.certificate_hash()
        );
        assert!(verified.axiom_report().module_axioms.is_empty());
        assert!(verified
            .axiom_report()
            .per_declaration
            .iter()
            .all(|entry| { entry.direct_axioms.is_empty() && entry.transitive_axioms.is_empty() }));
    }

    #[test]
    fn advanced_ai_m9_independent_checker_support_matrix_and_sidecar_boundaries_are_pinned() {
        let inductive_request = inductive_request(valid_inductive_proposal());
        let (_, inductive_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_inductive_check_success_independent_checker_mvp_supported_certificate",
            ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
            run_advanced_ai_inductive_check_request(&inductive_request, &[], &workspace_root()),
        );
        assert!(matches!(
            inductive_payload,
            AdvancedAiSuccessPayload::AdvancedInductive { .. }
        ));

        let smt_import = verified_smt_import();
        assert_advanced_ai_m9_rejected_fixture(
            "advanced_ai_m9_smt_reconstruct_rejected_independent_checker_mvp_empty_registry",
            ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT,
            run_advanced_ai_smt_reconstruct_request(
                &smt_request(&smt_import, |_| {}),
                std::slice::from_ref(&smt_import),
                &workspace_root(),
            ),
            AdvancedAiValidationError::UnsupportedFeature,
            Some(AdvancedAiFeatureError::SmtCertificate(
                AdvancedSmtCertificateError::RuleRegistryMismatch,
            )),
        );

        let statement = formalization_statement("Type");
        let first = formalization_request(
            formalization_payload_with(
                "natural language explanation, confidence 10%",
                "Type",
                None,
                Some(exact_proof_candidate(&statement, "Prop")),
            ),
            formalization_options_bytes(),
        );
        let second = formalization_request(
            formalization_payload_with(
                "different AI sidecar text, confidence 99%",
                "Type",
                None,
                Some(exact_proof_candidate(&statement, "Prop")),
            ),
            formalization_options_bytes(),
        );
        let (first_candidate_hash, first_payload) = assert_advanced_ai_m9_success_fixture(
            "advanced_ai_m9_formalize_check_success_independent_checker_mvp_proof_bridge",
            ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT,
            run_advanced_ai_formalize_check_request(&first, &[], &workspace_root()),
        );
        let (second_candidate_hash, second_payload) = assert_success(
            run_advanced_ai_formalize_check_request(&second, &[], &workspace_root()),
        );
        assert_ne!(first_candidate_hash, second_candidate_hash);

        let AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind: first_kind,
            accepted_statement_hash: first_accepted,
            formalization_proof_root_hash: first_root,
        } = first_payload
        else {
            panic!("expected formalization payload");
        };
        let AdvancedAiSuccessPayload::NaturalLanguageFormalization {
            kind: second_kind,
            accepted_statement_hash: second_accepted,
            formalization_proof_root_hash: second_root,
        } = second_payload
        else {
            panic!("expected formalization payload");
        };
        assert_eq!(
            first_kind,
            AdvancedFormalizationSuccessKind::ProofBridgeChecked
        );
        assert_eq!(
            second_kind,
            AdvancedFormalizationSuccessKind::ProofBridgeChecked
        );
        assert_eq!(first_accepted, second_accepted);
        assert_eq!(first_root, second_root);

        let proof_root = first_root.unwrap();
        let theorem_cert = npa_cert::build_module_cert(
            CoreModule {
                name: formalization_scratch_module(proof_root),
                declarations: vec![Decl::Theorem {
                    name: formalization_scratch_theorem(proof_root).as_dotted(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::succ(Level::zero())),
                    proof: Expr::sort(Level::zero()),
                }],
            },
            &[],
        )
        .unwrap();
        let theorem_bytes = npa_cert::encode_module_cert(&theorem_cert).unwrap();
        let mut verifier_session = VerifierSession::new();
        let verified = npa_cert::verify_module_cert(
            &theorem_bytes,
            &mut verifier_session,
            &AxiomPolicy::normal(),
        )
        .unwrap();
        assert_eq!(
            theorem_cert.hashes.certificate_hash,
            verified.certificate_hash()
        );
        assert!(verified.axiom_report().module_axioms.is_empty());
        assert!(verified
            .axiom_report()
            .per_declaration
            .iter()
            .all(|entry| { entry.direct_axioms.is_empty() && entry.transitive_axioms.is_empty() }));
    }

    #[test]
    fn advanced_ai_m9_api_profile_and_error_tags_are_compatibility_pinned() {
        assert_eq!(AdvancedAiProfileVersion::MvpV1.tag(), 0);
        assert_eq!(
            AdvancedAiProfileVersion::from_tag(0),
            Some(AdvancedAiProfileVersion::MvpV1)
        );
        assert_eq!(AdvancedAiProfileVersion::from_tag(1), None);
        assert_eq!(AdvancedAiOptionsVersion::MvpV1.tag(), 0);
        assert_eq!(
            AdvancedAiOptionsVersion::from_tag(0),
            Some(AdvancedAiOptionsVersion::MvpV1)
        );
        assert_eq!(AdvancedAiOptionsVersion::from_tag(1), None);
        assert_eq!(
            AdvancedIndependentCheckerProfile::IndependentCheckerMvpReference.tag(),
            0
        );
        assert_eq!(
            AdvancedIndependentCheckerProfile::from_tag(0),
            Some(AdvancedIndependentCheckerProfile::IndependentCheckerMvpReference)
        );
        assert_eq!(AdvancedIndependentCheckerProfile::from_tag(1), None);
        assert_eq!(AdvancedIndependentCheckerProfile::from_tag(2), None);
        let smt_solvers = [
            AdvancedSmtSolver::Cvc5,
            AdvancedSmtSolver::Z3,
            AdvancedSmtSolver::VeriT,
            AdvancedSmtSolver::OpaqueExternal,
        ];
        for (expected_tag, solver) in (0u8..).zip(smt_solvers) {
            assert_eq!(solver.tag(), expected_tag);
            assert_eq!(AdvancedSmtSolver::from_tag(expected_tag), Some(solver));
        }
        assert_eq!(AdvancedSmtSolver::from_tag(4), None);
        let smt_fragments = [
            AdvancedSmtSupportedFragment::QfPropositional,
            AdvancedSmtSupportedFragment::QfEuf,
            AdvancedSmtSupportedFragment::QfSimpleLia,
            AdvancedSmtSupportedFragment::QfEufLia,
            AdvancedSmtSupportedFragment::QfBitVecBitblastLrat,
        ];
        for (expected_tag, fragment) in (0u8..).zip(smt_fragments) {
            assert_eq!(fragment.tag(), expected_tag);
            assert_eq!(
                AdvancedSmtSupportedFragment::from_tag(expected_tag),
                Some(fragment)
            );
        }
        assert_eq!(AdvancedSmtSupportedFragment::from_tag(5), None);
        assert_eq!(
            AdvancedSmtRuleDescriptorKind::MvpKernelCheckedPayloadNodeV1.tag(),
            0
        );
        assert_eq!(
            AdvancedSmtRuleDescriptorKind::BitblastLratSoundnessBridgeV1.tag(),
            1
        );
        let smt_formats = [
            AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
            AdvancedSmtCertificateFormat::AletheOpaqueV1,
            AdvancedSmtCertificateFormat::LfscOpaqueV1,
            AdvancedSmtCertificateFormat::SolverResultOnlyV1,
        ];
        for (expected_tag, format) in (0u8..).zip(smt_formats) {
            assert_eq!(format.tag(), expected_tag);
            assert_eq!(
                AdvancedSmtCertificateFormat::from_tag(expected_tag),
                Some(format)
            );
        }
        assert_eq!(AdvancedSmtCertificateFormat::from_tag(4), None);

        let task_kinds = [
            (0, AdvancedAiTaskKind::AdvancedInductive),
            (1, AdvancedAiTaskKind::UniverseRepair),
            (2, AdvancedAiTaskKind::TypeclassResolution),
            (4, AdvancedAiTaskKind::SmtCertificate),
            (5, AdvancedAiTaskKind::TheoremGraphQuery),
            (6, AdvancedAiTaskKind::NaturalLanguageFormalization),
        ];
        for (expected_tag, task_kind) in task_kinds {
            assert_eq!(task_kind.tag(), expected_tag);
            assert_eq!(AdvancedAiTaskKind::from_tag(expected_tag), Some(task_kind));
        }
        assert_eq!(AdvancedAiTaskKind::from_tag(3), None);
        assert_eq!(AdvancedAiTaskKind::from_tag(7), None);

        let validation_errors = [
            AdvancedAiValidationError::EnvelopeMalformed,
            AdvancedAiValidationError::TargetFingerprintMismatch,
            AdvancedAiValidationError::ImportClosureMismatch,
            AdvancedAiValidationError::PayloadHashMismatch,
            AdvancedAiValidationError::KernelRejected,
            AdvancedAiValidationError::IndependentCheckerRejected,
            AdvancedAiValidationError::NonDeterministicResult,
            AdvancedAiValidationError::BudgetExceeded,
            AdvancedAiValidationError::AmbiguousResolution,
            AdvancedAiValidationError::NoSolution,
            AdvancedAiValidationError::FeatureRejected,
            AdvancedAiValidationError::UnsupportedFeature,
        ];
        for (expected_tag, error) in (0u8..).zip(validation_errors) {
            assert_eq!(error.tag(), expected_tag);
        }

        let feature_error_tags = [
            (
                AdvancedAiFeatureError::AdvancedInductive(
                    AdvancedInductiveError::TargetRefMismatch,
                ),
                vec![0, 0],
            ),
            (
                AdvancedAiFeatureError::UniverseRepair(
                    AdvancedUniverseRepairError::UnknownUniverseParam,
                ),
                vec![1, 0],
            ),
            (
                AdvancedAiFeatureError::TypeclassResolution(
                    AdvancedTypeclassResolutionError::ClassDeclarationMismatch,
                ),
                vec![2, 0],
            ),
            (
                AdvancedAiFeatureError::SmtCertificate(
                    AdvancedSmtCertificateError::EncodingMismatch,
                ),
                vec![4, 0],
            ),
            (
                AdvancedAiFeatureError::SmtCertificate(
                    AdvancedSmtCertificateError::UnsupportedFragment,
                ),
                vec![4, 11],
            ),
            (
                AdvancedAiFeatureError::SmtCertificate(
                    AdvancedSmtCertificateError::SolverResultOnly,
                ),
                vec![4, 12],
            ),
            (
                AdvancedAiFeatureError::SmtCertificate(
                    AdvancedSmtCertificateError::MalformedProofPayload,
                ),
                vec![4, 13],
            ),
            (
                AdvancedAiFeatureError::TheoremGraphQuery(
                    AdvancedTheoremGraphError::SnapshotMalformed,
                ),
                vec![5, 0],
            ),
            (
                AdvancedAiFeatureError::Formalization(
                    AdvancedFormalizationError::IntentRecordMismatch,
                ),
                vec![6, 0],
            ),
        ];
        for (feature_error, expected) in feature_error_tags {
            let mut encoded = Vec::new();
            encode_feature_error_to(&mut encoded, feature_error);
            assert_eq!(encoded, expected);
        }
    }

    #[test]
    fn route_skeletons_bind_each_endpoint_to_its_task_kind() {
        type AdvancedRoute = fn(&[u8], &[VerifiedImportRef], &Path) -> AdvancedAiEndpointResponse;

        let routes: [(&str, AdvancedRoute); 6] = [
            (
                ADVANCED_AI_INDUCTIVE_CHECK_ENDPOINT,
                run_advanced_ai_inductive_check_request,
            ),
            (
                ADVANCED_AI_UNIVERSE_REPAIR_CHECK_ENDPOINT,
                run_advanced_ai_universe_repair_check_request,
            ),
            (
                ADVANCED_AI_TYPECLASS_RESOLVE_ENDPOINT,
                run_advanced_ai_typeclass_resolve_request,
            ),
            (
                ADVANCED_AI_SMT_RECONSTRUCT_ENDPOINT,
                run_advanced_ai_smt_reconstruct_request,
            ),
            (
                ADVANCED_AI_THEOREM_GRAPH_QUERY_ENDPOINT,
                run_advanced_ai_theorem_graph_query_request,
            ),
            (
                ADVANCED_AI_FORMALIZE_CHECK_ENDPOINT,
                run_advanced_ai_formalize_check_request,
            ),
        ];
        assert_eq!(routes.len(), 6);

        let import = verified_universe_import();
        let universe = valid_universe_request(&import);
        assert_rejected(
            run_advanced_ai_inductive_check_request(&universe, &[], &workspace_root()),
            AdvancedAiValidationError::EnvelopeMalformed,
            None,
        );
        assert!(matches!(
            run_advanced_ai_universe_repair_check_request(
                &universe,
                std::slice::from_ref(&import),
                &workspace_root()
            ),
            AdvancedAiEndpointResponse::Success { .. }
        ));
    }

    #[test]
    fn common_validation_success_is_deterministic_for_same_replay_input() {
        let request = inline_request(
            AdvancedAiTaskKind::AdvancedInductive,
            empty_options_bytes(),
            Vec::new(),
            None,
        );

        let first = run_advanced_ai_inductive_check_request(&request, &[], &workspace_root());
        let second = run_advanced_ai_inductive_check_request(&request, &[], &workspace_root());

        assert_eq!(first, second);
        assert_rejected(first, AdvancedAiValidationError::EnvelopeMalformed, None);
    }
}
