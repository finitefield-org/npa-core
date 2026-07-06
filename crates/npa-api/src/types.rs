use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use npa_cert::{CoreModule, Hash, ModuleCert, ModuleName, Name, VerifiedModule};
use npa_frontend::{
    ByteOffset, FileId, HumanCompileOptions, HumanDiagnostic, HumanExpr,
    HumanImportedSourceInterface, HumanName, HumanRewriteRuleSyntax, HumanSourceInterface,
    HumanTacticScript, HumanTypeclassSearchPolicy, MachineSurfaceCallableInterfaceTable, Span,
};
use npa_kernel::{Expr, InductiveDecl};
use npa_tactic::{
    GoalId, MachineProofDelta, MachineProofState, MachineTacticDiagnostic, MetaVarId, TacticBudget,
    VerifiedImportRef,
};

use crate::advanced_ai::{
    AdvancedAiEndpointResponse, AdvancedFormalizationSuccessKind, AdvancedReviewerId,
    AdvancedSmtProveHashes,
};
use crate::current::{MachineAxiomRefWire, MachineCheckedCurrentDeclContext};
use crate::json::{JsonMember, JsonValue, JsonValueKind};
use crate::projection::{MachineImportCertificateContext, VerifiedImportKey};
use crate::renderer::{
    LocalId, MachineDisplayRenderScope, MachineExprRendererError, MachineExprView,
};
use crate::snapshot::MachineSnapshotStore;
use crate::validation::{
    parse_strict_u64_token, JsonPath, MachineApiErrorKind, MachineApiRequestError,
    MachineApiRequestErrorReason, StrictUnsignedIntegerError,
};
use crate::{
    MachineApiDiagnosticCanonicalizationError, MachineApiDiagnosticPhase,
    MachineApiDiagnosticProjection, MachineApiTacticKind,
};

pub const MACHINE_API_VERSION: &str = "npa.machine-api.v1";
pub const MACHINE_DISPLAY_PROFILE_ID: &str = "npa.machine-api.display.v1";
pub const HUMAN_DISPLAY_PROFILE_ID: &str = "npa.human-api.display.v1";
pub const MACHINE_TACTIC_CANDIDATE_OUTPUT_SCHEMA: &str = "npa.machine_tactic_candidate.v1";
pub const KERNEL_CHECK_PROFILE_BUILTIN_NAT_EQ_REC: &str = "npa.kernel.v0.1.builtin-nat-eq-rec";
pub const KERNEL_CHECK_PROFILE_BUILTIN_NONE: &str = "npa.kernel.v0.1.builtin-none";
pub const HUMAN_INDUCTIVE_CHECK_ENDPOINT: &str = "/inductive/check";
pub const HUMAN_TYPECLASS_SEARCH_ENDPOINT: &str = "/typeclass/search";
pub const HUMAN_SMT_PROVE_ENDPOINT: &str = "/smt/prove";
pub const HUMAN_FORMALIZE_ENDPOINT: &str = "/formalize";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanApiCompileOptions {
    pub max_notation_candidates: usize,
    pub typeclass_search_policy: HumanTypeclassSearchPolicy,
    pub kernel_profile: npa_tactic::MachineKernelProfile,
    pub tactic_options: npa_tactic::MachineTacticOptions,
}

impl Default for HumanApiCompileOptions {
    fn default() -> Self {
        let frontend = HumanCompileOptions::default();
        Self {
            max_notation_candidates: frontend.max_notation_candidates,
            typeclass_search_policy: frontend.typeclass_search_policy,
            kernel_profile: npa_tactic::MachineKernelProfile::BuiltinNatEqRec,
            tactic_options: npa_tactic::MachineTacticOptions::default(),
        }
    }
}

impl From<&HumanApiCompileOptions> for HumanCompileOptions {
    fn from(value: &HumanApiCompileOptions) -> Self {
        Self {
            max_notation_candidates: value.max_notation_candidates,
            typeclass_search_policy: value.typeclass_search_policy,
            enable_equation_compiler: false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct HumanInductiveCheckRequest<'decl> {
    pub declaration: &'decl InductiveDecl,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanInductiveCheckResponse {
    pub status: HumanInductiveCheckStatus,
    pub constructors: Vec<String>,
    pub recursor: Option<String>,
    pub positivity: HumanInductivePositivityStatus,
    pub recursor_signature_hash: Option<Hash>,
    pub iota_rules_hash: Option<Hash>,
    pub diagnostic_only: bool,
    pub error: Option<HumanInductiveCheckError>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanInductiveCheckStatus {
    AcceptedByKernelAndCertificate,
    Rejected,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanInductivePositivityStatus {
    Passed,
    Failed,
    NotReached,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanInductiveCheckError {
    Kernel(npa_kernel::Error),
    Certificate(npa_cert::CertError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanCurrentModuleSource<'src> {
    pub file_id: FileId,
    pub source: &'src str,
}

#[derive(Clone, Debug)]
pub struct HumanCompileCoreRequest<'src, 'imports> {
    /// Current module identity supplied by the Human API caller.
    pub current_module: ModuleName,
    /// Full Human source for the current module, including any `by` blocks.
    pub current_source: HumanCurrentModuleSource<'src>,
    /// Explicit verified imports available to this Human compile request.
    pub verified_modules: &'imports [VerifiedModule],
    /// Human source metadata for the verified imports above.
    pub imported_source_interfaces: &'imports [HumanImportedSourceInterface],
    /// Frontend and tactic options for this request; no Machine session state is implied.
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug)]
pub struct HumanCompileCertificateRequest<'src, 'imports> {
    /// Current module identity supplied by the Human API caller.
    pub current_module: ModuleName,
    /// Full Human source for the current module, including any `by` blocks.
    pub current_source: HumanCurrentModuleSource<'src>,
    /// Explicit verified imports available to this Human compile request.
    pub verified_modules: &'imports [VerifiedModule],
    /// Human source metadata for the verified imports above.
    pub imported_source_interfaces: &'imports [HumanImportedSourceInterface],
    /// Frontend and tactic options for this request; no Machine session state is implied.
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug)]
pub struct HumanTypeclassSearchRequest<'src, 'imports> {
    pub current_module: ModuleName,
    pub current_source: HumanCurrentModuleSource<'src>,
    pub verified_modules: &'imports [VerifiedModule],
    pub imported_source_interfaces: &'imports [HumanImportedSourceInterface],
    pub goal_source: &'src str,
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTypeclassSearchOk {
    pub status: npa_frontend::HumanTypeclassSearchStatus,
    pub instance: Option<Name>,
    pub core_term: Option<Expr>,
    pub search_trace: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTypeclassSearchError {
    pub diagnostic: HumanDiagnostic,
}

impl From<HumanDiagnostic> for HumanTypeclassSearchError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self { diagnostic }
    }
}

#[derive(Clone, Debug)]
pub struct HumanSmtProveRequest<'req, 'imports> {
    pub request_canonical_bytes: &'req [u8],
    pub verified_imports: &'imports [VerifiedImportRef],
    pub workspace_root: &'imports Path,
    pub require_certificate: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanSmtProveOk {
    pub problem_hash: Hash,
    pub proof_hash: Hash,
    pub npa_proof_hash: Hash,
    pub kernel_checked: bool,
}

impl From<AdvancedSmtProveHashes> for HumanSmtProveOk {
    fn from(value: AdvancedSmtProveHashes) -> Self {
        Self {
            problem_hash: value.problem_hash,
            proof_hash: value.proof_hash,
            npa_proof_hash: value.npa_proof_hash,
            kernel_checked: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanSmtProveResponse {
    Success(HumanSmtProveOk),
    Diagnostic(AdvancedAiEndpointResponse),
}

#[derive(Clone, Debug)]
pub struct HumanFormalizeRequest<'imports> {
    pub candidates: Vec<HumanFormalizeCandidateRequest>,
    pub verified_imports: &'imports [VerifiedImportRef],
    pub workspace_root: &'imports Path,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanFormalizeCandidateRequest {
    pub request_canonical_bytes: Vec<u8>,
    pub reverse_translation: String,
    pub ambiguity_report: Vec<String>,
    pub confidence_microunits: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanFormalizeOk {
    pub candidates: Vec<HumanFormalizeCandidateReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanFormalizeCandidateReport {
    pub candidate_hash: Hash,
    pub candidate_statement_hash: Option<Hash>,
    pub formal_statement_hash: Option<Hash>,
    pub accepted_statement_hash: Option<Hash>,
    pub reverse_translation: String,
    pub ambiguity_report: Vec<String>,
    pub confidence_microunits: Option<u32>,
    pub review_status: HumanFormalizationReviewStatus,
    pub proof_search_status: HumanFormalizationProofSearchStatus,
    pub intent_certificate: Option<HumanFormalizationIntentCertificate>,
    pub validation_kind: Option<AdvancedFormalizationSuccessKind>,
    pub validation_response: AdvancedAiEndpointResponse,
    pub verified: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanFormalizationIntentCertificate {
    pub intent_certificate_hash: Hash,
    pub source_document_hash: Hash,
    pub claim_span_hash: Hash,
    pub candidate_statement_hash: Hash,
    pub reverse_translation_hash: Hash,
    pub ambiguity_report_hash: Hash,
    pub confidence_microunits: Option<u32>,
    pub status: HumanFormalizationReviewStatus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanFormalizationReviewStatus {
    MissingIntent,
    Unreviewed,
    Reviewed {
        reviewer: AdvancedReviewerId,
        accepted_statement_hash: Hash,
    },
    Rejected {
        reviewer: AdvancedReviewerId,
        rejection_reason_hash: Hash,
    },
    MalformedRequest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanFormalizationProofSearchStatus {
    NotRequested,
    BlockedUntilConfirmed,
    Checked,
    Rejected,
}

#[derive(Clone, Debug)]
pub struct HumanSessionCreateRequest<'src, 'imports> {
    /// Current module identity supplied by the Human API caller.
    pub current_module: ModuleName,
    /// Full Human source for the initial document snapshot.
    pub current_source: HumanCurrentModuleSource<'src>,
    /// Explicit verified imports available to this Human session.
    pub verified_modules: &'imports [VerifiedModule],
    /// Human source metadata for the verified imports above.
    pub imported_source_interfaces: &'imports [HumanImportedSourceInterface],
    /// Frontend and tactic options for this Human session; no Machine session state is implied.
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug)]
pub struct HumanDocumentUpdateRequest<'src, 'imports> {
    pub session_id: HumanSessionId,
    /// Current module identity supplied by the Human API caller for the new snapshot.
    pub current_module: ModuleName,
    /// Full Human source for the replacement document snapshot.
    pub current_source: HumanCurrentModuleSource<'src>,
    /// Explicit verified imports available to this Human session after the update.
    pub verified_modules: &'imports [VerifiedModule],
    /// Human source metadata for the verified imports above.
    pub imported_source_interfaces: &'imports [HumanImportedSourceInterface],
    /// Frontend and tactic options for the new document snapshot.
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateRequestHeader {
    pub session_id: HumanSessionId,
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanSourcePosition {
    pub file_id: FileId,
    pub offset: ByteOffset,
}

impl HumanSourcePosition {
    pub const fn new(file_id: FileId, offset: u32) -> Self {
        Self {
            file_id,
            offset: ByteOffset(offset),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateByIdRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateGoalsRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateCurrentRequest {
    pub header: HumanStateRequestHeader,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateAtRequest {
    pub header: HumanStateRequestHeader,
    pub position: HumanSourcePosition,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateLookupOk {
    pub state: StructuredProofState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateGoalsOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub document_version: HumanDocumentVersion,
    pub selected_goal: Option<HumanGoalId>,
    pub goals: Vec<HumanStateGoalSummary>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStateGoalSummary {
    pub goal_id: HumanGoalId,
    pub pretty: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanLspPosition {
    pub line: u32,
    pub character: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanLspRange {
    pub start: HumanLspPosition,
    pub end: HumanLspPosition,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanLspDiagnosticSeverity {
    Error,
    Warning,
}

impl HumanLspDiagnosticSeverity {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspDiagnostic {
    pub range: HumanLspRange,
    pub severity: HumanLspDiagnosticSeverity,
    pub code: String,
    pub source: &'static str,
    pub message: String,
    pub data: HumanLspDiagnosticData,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanLspDiagnosticData {
    pub kind: String,
    pub phase: Option<String>,
    pub detail: Option<String>,
    pub candidates: Vec<String>,
    pub hole_goals: Vec<HumanLspHoleGoal>,
    pub unsolved_meta: Option<HumanLspUnsolvedMeta>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspHoleGoal {
    pub hole: Option<String>,
    pub range: HumanLspRange,
    pub context: Vec<HumanLspHoleGoalLocal>,
    pub target: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspHoleGoalLocal {
    pub name: String,
    pub ty: String,
    pub value: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspUnsolvedMeta {
    pub kind: String,
    pub name: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspDiagnosticsRequest {
    pub header: HumanStateRequestHeader,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspDiagnosticsOk {
    pub session_id: HumanSessionId,
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
    pub diagnostics: Vec<HumanLspDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspHoverRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub name: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspHoverOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub hover: Option<HumanLspHover>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspHover {
    pub contents: String,
    pub theorem: HumanLspHoverTheorem,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspHoverTheorem {
    pub name: Name,
    pub module: ModuleName,
    pub kind: HumanTheoremIndexKind,
    pub statement_pretty: String,
    pub attributes: Vec<String>,
    pub axiom_info: HumanTheoremAxiomInfo,
    pub export_hash: Option<Hash>,
    pub certificate_hash: Option<Hash>,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCompletionRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub max_results: usize,
    pub include_search_command: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCompletionOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub items: Vec<HumanLspCompletionItem>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCompletionItem {
    pub label: String,
    pub kind: HumanLspCompletionItemKind,
    pub detail: String,
    pub insert_text: Option<String>,
    pub command: Option<HumanLspCommand>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanLspCompletionItemKind {
    Tactic,
    Command,
}

impl HumanLspCompletionItemKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Tactic => "tactic",
            Self::Command => "command",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCodeActionRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub max_tactic_suggestions: usize,
    pub include_search_command: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCodeActionOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub actions: Vec<HumanLspCodeAction>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCodeAction {
    pub title: String,
    pub kind: HumanLspCodeActionKind,
    pub tactic: Option<String>,
    pub command: Option<HumanLspCommand>,
    pub diagnostics: Vec<HumanLspDiagnostic>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanLspCodeActionKind {
    QuickFix,
    Command,
}

impl HumanLspCodeActionKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::QuickFix => "quickfix",
            Self::Command => "command",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspCommand {
    pub title: String,
    pub command: String,
    pub arguments: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspDocumentPayloadRequest {
    pub header: HumanStateRequestHeader,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspDocumentPayloadOk {
    pub session_id: HumanSessionId,
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
    pub semantic_tokens: Vec<HumanLspSemanticToken>,
    pub document_symbols: Vec<HumanLspDocumentSymbol>,
    pub inlay_hints: Vec<HumanLspInlayHint>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspSemanticToken {
    pub range: HumanLspRange,
    pub token_type: HumanLspSemanticTokenType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanLspSemanticTokenType {
    Function,
    Theorem,
    Type,
    Variable,
}

impl HumanLspSemanticTokenType {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Function => "function",
            Self::Theorem => "theorem",
            Self::Type => "type",
            Self::Variable => "variable",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspDocumentSymbol {
    pub name: String,
    pub kind: HumanLspSymbolKind,
    pub range: HumanLspRange,
    pub selection_range: HumanLspRange,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanLspSymbolKind {
    Function,
    Theorem,
    Type,
}

impl HumanLspSymbolKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Function => "function",
            Self::Theorem => "theorem",
            Self::Type => "type",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspInlayHint {
    pub position: HumanLspPosition,
    pub label: String,
    pub kind: HumanLspInlayHintKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanLspInlayHintKind {
    Type,
    Parameter,
}

impl HumanLspInlayHintKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Type => "type",
            Self::Parameter => "parameter",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspGoalViewRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub mode: HumanDisplayMode,
    pub context_options: HumanDisplayContextOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanLspGoalViewOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub document_version: HumanDocumentVersion,
    pub goals: Vec<HumanStateGoalSummary>,
    pub focused_goal: HumanDisplayTextOk,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanDisplayMode {
    Pretty,
    Explicit,
    Core,
    Json,
}

impl HumanDisplayMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pretty => "pretty",
            Self::Explicit => "explicit",
            Self::Core => "core",
            Self::Json => "json",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanDisplayContextOptions {
    pub max_context_items: Option<usize>,
    pub fold_local_def_values: bool,
    pub relevant_first: bool,
}

impl Default for HumanDisplayContextOptions {
    fn default() -> Self {
        Self {
            max_context_items: None,
            fold_local_def_values: false,
            relevant_first: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayGoalRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub mode: HumanDisplayMode,
    pub context_options: HumanDisplayContextOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayExprRequest {
    pub expr: StructuredExpr,
    pub mode: HumanDisplayMode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayDiffRequest {
    pub header: HumanStateRequestHeader,
    pub before_state_id: HumanStateId,
    pub after_state_id: HumanStateId,
    pub mode: HumanDisplayMode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayContextRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub mode: HumanDisplayMode,
    pub context_options: HumanDisplayContextOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayTextOk {
    pub display_profile: &'static str,
    pub mode: HumanDisplayMode,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayContextOk {
    pub display_profile: &'static str,
    pub mode: HumanDisplayMode,
    pub text: String,
    pub shown_count: usize,
    pub folded_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDisplayDiffOk {
    pub display_profile: &'static str,
    pub mode: HumanDisplayMode,
    pub items: Vec<HumanGoalDisplayDiffItem>,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanGoalDisplayDiffItem {
    pub kind: HumanGoalDisplayDiffKind,
    pub old_goal: Option<HumanGoalId>,
    pub new_goals: Vec<HumanGoalId>,
    pub text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanGoalDisplayDiffKind {
    GoalReplaced,
    GoalClosed,
    GoalAdded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticRunRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub tactic: String,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticRunResponse {
    pub status: HumanTacticRunStatus,
    pub session_id: HumanSessionId,
    pub parent_state_id: HumanStateId,
    pub new_state_id: Option<HumanStateId>,
    pub selected_goal: Option<HumanGoalId>,
    pub closed_goals: Vec<HumanGoalId>,
    pub new_goals: Vec<StructuredGoal>,
    pub proof_deltas: Vec<MachineProofDelta>,
    pub messages: Vec<HumanDiagnostic>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTacticRunStatus {
    Success,
    Closed,
    Partial,
    Error,
    Timeout,
    Unsafe,
}

impl HumanTacticRunStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Success => "success",
            Self::Closed => "closed",
            Self::Partial => "partial",
            Self::Error => "error",
            Self::Timeout => "timeout",
            Self::Unsafe => "unsafe",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticRunErrorReport {
    pub kind: HumanTacticRunErrorKind,
    pub old_state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub message: String,
    pub diagnostic: Option<HumanDiagnostic>,
    pub machine_diagnostic: Option<Box<MachineTacticDiagnostic>>,
    pub state_error: Option<Box<HumanStateApiError>>,
    pub expected_hash: Option<Hash>,
    pub actual_hash: Option<Hash>,
    pub span: Option<Span>,
    pub suggestions: Vec<HumanTacticRunSuggestion>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTacticRunErrorKind {
    StateValidation,
    UnknownGoal,
    ParseError,
    ExpectedPiType,
    TypeMismatch,
    Timeout,
    Unsafe,
    TacticExecution,
    StateRecord,
}

impl HumanTacticRunErrorKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StateValidation => "state_validation",
            Self::UnknownGoal => "unknown_goal",
            Self::ParseError => "parse_error",
            Self::ExpectedPiType => "expected_pi_type",
            Self::TypeMismatch => "type_mismatch",
            Self::Timeout => "timeout",
            Self::Unsafe => "unsafe",
            Self::TacticExecution => "tactic_execution",
            Self::StateRecord => "state_record",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticRunSuggestion {
    pub kind: HumanTacticRunSuggestionKind,
    pub tactic: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTacticRunSuggestionKind {
    TryTactic,
}

impl HumanTacticRunSuggestionKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TryTactic => "try_tactic",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticCheckRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub tactic: String,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticCheckResponse {
    pub status: HumanTacticRunStatus,
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub selected_goal: Option<HumanGoalId>,
    pub closed_goals: Vec<HumanGoalId>,
    pub expected_goals: Vec<StructuredGoal>,
    pub proof_deltas: Vec<MachineProofDelta>,
    pub messages: Vec<HumanDiagnostic>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticSuggestRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub max_results: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticSuggestResponse {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub suggestions: Vec<HumanTacticSuggestion>,
    pub messages: Vec<HumanDiagnostic>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticSuggestion {
    pub source: HumanTacticSuggestionSource,
    pub confidence: u8,
    pub reason: String,
    pub tactic: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantPayloadRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub max_tactic_suggestions: usize,
    pub max_nearby_theorems: usize,
    pub failed_tactics: Vec<HumanAssistantFailedTacticRequest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantFailedTacticRequest {
    pub tactic: String,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantPayloadOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub document_version: HumanDocumentVersion,
    pub goal_summary: HumanStateGoalSummary,
    pub structured_goal: StructuredGoal,
    pub available_tactics: Vec<HumanAssistantAvailableTactic>,
    pub tactic_suggestions: Vec<HumanAssistantCandidate>,
    pub nearby_theorems: Vec<HumanAssistantNearbyTheorem>,
    pub failed_tactics: Vec<HumanAssistantFailedTacticDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantAvailableTactic {
    pub tactic: String,
    pub description: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantCandidate {
    pub tactic: String,
    pub confidence: u8,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantNearbyTheorem {
    pub name: Name,
    pub statement_pretty: String,
    pub suggested_tactic: String,
    pub mode: HumanTheoremSearchMode,
    pub why: String,
    pub score: u64,
    pub axiom_info: HumanTheoremAxiomInfo,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantFailedTacticDiagnostic {
    pub tactic: String,
    pub status: HumanTacticRunStatus,
    pub messages: Vec<HumanDiagnostic>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanAssistantPayloadError {
    State(HumanStateApiError),
    Search(HumanTheoremSearchError),
    UnknownGoal {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        goal_id: HumanGoalId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantCandidateValidationRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub candidates: Vec<HumanAssistantCandidate>,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantCandidateValidationOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub accepted: Vec<HumanAssistantValidatedCandidate>,
    pub rejected: Vec<HumanAssistantRejectedCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantValidatedCandidate {
    pub candidate: HumanAssistantCandidate,
    pub status: HumanTacticRunStatus,
    pub selected_goal: Option<HumanGoalId>,
    pub closed_goals: Vec<HumanGoalId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanAssistantRejectedCandidate {
    pub candidate: HumanAssistantCandidate,
    pub status: HumanTacticRunStatus,
    pub messages: Vec<HumanDiagnostic>,
    pub error: Option<HumanTacticRunErrorReport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremIndex {
    pub fingerprint: Hash,
    pub entries: Vec<HumanTheoremIndexEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremIndexEntry {
    pub name: Name,
    pub module: ModuleName,
    pub source: HumanTheoremIndexSource,
    pub universe_params: Vec<String>,
    pub statement_core: Expr,
    pub statement: StructuredExpr,
    pub statement_pretty: String,
    pub head_symbol: Option<Name>,
    pub constants: Vec<Name>,
    pub attributes: Vec<String>,
    pub kind: HumanTheoremIndexKind,
    pub dependencies: Vec<HumanTheoremDependency>,
    pub axiom_dependencies: Vec<MachineAxiomRefWire>,
    pub export_hash: Option<Hash>,
    pub certificate_hash: Option<Hash>,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanTheoremIndexSource {
    VerifiedImport {
        export_hash: Hash,
        certificate_hash: Hash,
    },
    CheckedCurrentDecl {
        source_index: u64,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTheoremIndexKind {
    Axiom,
    Def,
    Theorem,
    Inductive,
    Constructor,
    Recursor,
}

impl HumanTheoremIndexKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Def => "def",
            Self::Theorem => "theorem",
            Self::Inductive => "inductive",
            Self::Constructor => "constructor",
            Self::Recursor => "recursor",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremDependency {
    pub kind: HumanTheoremDependencyKind,
    pub name: Name,
    pub module: Option<ModuleName>,
    pub export_hash: Option<Hash>,
    pub source_index: Option<u64>,
    pub decl_interface_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTheoremDependencyKind {
    Imported,
    Current,
    Builtin,
    UnknownConstant,
}

impl HumanTheoremDependencyKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Imported => "imported",
            Self::Current => "current",
            Self::Builtin => "builtin",
            Self::UnknownConstant => "unknown_constant",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanTheoremIndexError {
    MissingUniverseParam {
        module: ModuleName,
        name_index: usize,
    },
    MissingTerm {
        module: ModuleName,
        term_index: usize,
    },
    MissingLevel {
        module: ModuleName,
        level_index: usize,
    },
    MissingName {
        module: ModuleName,
        name_index: usize,
    },
    MissingDeclaration {
        module: ModuleName,
        decl_index: usize,
    },
    InvalidAxiomRef {
        module: ModuleName,
        name: Name,
    },
    ExpressionMetadata {
        name: Name,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremSearchOptions {
    pub limit: usize,
    pub axiom_policy: HumanTheoremSearchAxiomPolicy,
}

impl Default for HumanTheoremSearchOptions {
    fn default() -> Self {
        Self {
            limit: 20,
            axiom_policy: HumanTheoremSearchAxiomPolicy::Allow,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTheoremSearchAxiomPolicy {
    Allow,
    Penalize,
    Exclude,
}

impl HumanTheoremSearchAxiomPolicy {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Allow => "allow",
            Self::Penalize => "penalize",
            Self::Exclude => "exclude",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremNameSearchRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub query: String,
    pub options: HumanTheoremSearchOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremTypeSearchRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub pattern: String,
    pub options: HumanTheoremSearchOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremGoalSearchRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub modes: Vec<HumanTheoremSearchMode>,
    pub options: HumanTheoremSearchOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremRewriteSearchRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
    pub goal_id: HumanGoalId,
    pub options: HumanTheoremSearchOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremSearchOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub goal_id: Option<HumanGoalId>,
    pub theorem_index_fingerprint: Hash,
    pub results: Vec<HumanTheoremSearchResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremSearchResult {
    pub name: Name,
    pub module: ModuleName,
    pub source: HumanTheoremIndexSource,
    pub kind: HumanTheoremIndexKind,
    pub mode: HumanTheoremSearchMode,
    pub statement_core: Expr,
    pub statement_pretty: String,
    pub suggested_tactic: String,
    pub match_info: Vec<HumanTheoremMatchBinding>,
    pub why: String,
    pub score: u64,
    pub axiom_info: HumanTheoremAxiomInfo,
    pub export_hash: Option<Hash>,
    pub certificate_hash: Option<Hash>,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremMatchBinding {
    pub pattern: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTheoremAxiomInfo {
    pub uses_axioms: bool,
    pub axiom_dependencies: Vec<MachineAxiomRefWire>,
    pub score_penalty: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HumanTheoremSearchMode {
    Name,
    ByType,
    Exact,
    Apply,
    Rw,
    Simp,
}

impl HumanTheoremSearchMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Name => "name",
            Self::ByType => "by_type",
            Self::Exact => "exact",
            Self::Apply => "apply",
            Self::Rw => "rw",
            Self::Simp => "simp",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanTheoremSearchError {
    State(HumanStateApiError),
    UnknownGoal {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        goal_id: HumanGoalId,
    },
    InvalidGoalMode {
        mode: HumanTheoremSearchMode,
    },
    InvalidPattern {
        pattern: String,
        message: String,
    },
    Index(HumanTheoremIndexError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanSessionVerifyRequest {
    pub header: HumanStateRequestHeader,
    pub state_id: HumanStateId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanSessionVerifyOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub document_version: HumanDocumentVersion,
    pub theorem_name: Name,
    pub status: HumanSessionVerifyStatus,
    pub root_decl_interface_hash: Hash,
    pub root_decl_certificate_hash: Hash,
    pub certificate_hash: Hash,
    pub export_hash: Hash,
    pub root_axioms_used: Vec<MachineAxiomRefWire>,
    pub axioms_used: Vec<MachineAxiomRefWire>,
    pub contains_sorry: bool,
    pub certificate: HumanCertificatePayload,
    pub imports: Vec<HumanSessionVerifyImport>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanSessionVerifyStatus {
    Verified,
}

impl HumanSessionVerifyStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanCertificatePayload {
    pub encoding: &'static str,
    pub bytes: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanSessionVerifyImport {
    pub module: ModuleName,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub module_axioms: Vec<HumanSessionVerifyImportAxiom>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanSessionVerifyImportAxiom {
    pub name: Name,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanSessionVerifyError {
    State(HumanStateApiError),
    OpenGoals {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        open_goals: Vec<HumanGoalId>,
    },
    CertificateHandoff {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        message: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanTacticSuggestionSource {
    Builtin,
}

impl HumanTacticSuggestionSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Builtin => "builtin",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanSessionCreateOk {
    pub session_id: HumanSessionId,
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
    pub status: HumanProofSessionStatus,
    pub messages: Vec<HumanDiagnostic>,
    pub incremental_cache: HumanDocumentIncrementalCache,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDocumentUpdateOk {
    pub session_id: HumanSessionId,
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
    pub status: HumanProofSessionStatus,
    pub messages: Vec<HumanDiagnostic>,
    pub incremental_cache: HumanDocumentIncrementalCache,
}

#[derive(Clone, Debug)]
pub struct HumanProofSession {
    pub session_id: HumanSessionId,
    pub status: HumanProofSessionStatus,
    pub document: HumanDocumentSnapshot,
    pub source_interface: Option<HumanSourceInterface>,
    pub active_imported_source_interfaces: Vec<HumanImportedSourceInterface>,
    pub incremental_cache: HumanDocumentIncrementalCache,
    pub proof_states: HumanProofStateStore,
    pub current_state_id: Option<HumanStateId>,
    pub messages: Vec<HumanDiagnostic>,
}

/// Human document cache metadata for declaration-level incremental work.
///
/// These hashes are only cache keys for the Human document pipeline. They are
/// not Machine proof-state fingerprints and must not be used as proof
/// acceptance evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDocumentIncrementalCache {
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
    pub import_interface_hash: Hash,
    pub prior_document_version: Option<HumanDocumentVersion>,
    pub prior_import_interface_hash: Option<Hash>,
    pub reused_prefix_len: u64,
    pub recomputed_from: Option<u64>,
    pub declarations: Vec<HumanDocumentIncrementalDeclCacheEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDocumentIncrementalDeclCacheEntry {
    pub source_index: u64,
    pub source_decl_hash: Hash,
    pub resolved_decl_hash: Hash,
    pub core_decl_hash: Hash,
    pub reuse: HumanDocumentIncrementalDeclReuse,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanDocumentIncrementalDeclReuse {
    Fresh,
    Reused,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDocumentSnapshot {
    pub document_id: HumanDocumentId,
    pub document_version: HumanDocumentVersion,
    pub current_module: ModuleName,
    pub file_id: FileId,
    pub source: String,
    pub verified_modules: Vec<VerifiedModule>,
    pub imported_source_interfaces: Vec<HumanImportedSourceInterface>,
    pub options: HumanApiCompileOptions,
}

impl HumanDocumentSnapshot {
    pub fn current_source(&self) -> HumanCurrentModuleSource<'_> {
        HumanCurrentModuleSource {
            file_id: self.file_id,
            source: &self.source,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanProofSessionStatus {
    Open,
}

impl HumanProofSessionStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Open => "open",
        }
    }
}

#[derive(Clone, Debug)]
pub struct HumanProofSessionStore {
    sessions: BTreeMap<HumanSessionId, HumanProofSession>,
    next_session_index: u64,
    next_document_index: u64,
}

impl HumanProofSessionStore {
    pub fn new() -> Self {
        Self {
            sessions: BTreeMap::new(),
            next_session_index: 1,
            next_document_index: 1,
        }
    }

    pub fn session(&self, session_id: &HumanSessionId) -> Option<&HumanProofSession> {
        self.sessions.get(session_id)
    }

    pub fn session_count(&self) -> usize {
        self.sessions.len()
    }

    pub(crate) fn session_mut(
        &mut self,
        session_id: &HumanSessionId,
    ) -> Option<&mut HumanProofSession> {
        self.sessions.get_mut(session_id)
    }

    pub(crate) fn allocate_session_ids(
        &mut self,
    ) -> Result<(HumanSessionId, HumanDocumentId), HumanSessionCreateError> {
        let session_index = self
            .next_session_index
            .checked_add(1)
            .ok_or(HumanSessionCreateError::IdSpaceExhausted)?;
        let document_index = self
            .next_document_index
            .checked_add(1)
            .ok_or(HumanSessionCreateError::IdSpaceExhausted)?;
        let session_id =
            HumanSessionId::new_unchecked(format!("hsess_{}", self.next_session_index));
        let document_id =
            HumanDocumentId::new_unchecked(format!("hdoc_{}", self.next_document_index));
        self.next_session_index = session_index;
        self.next_document_index = document_index;
        Ok((session_id, document_id))
    }

    pub(crate) fn insert_session(&mut self, session: HumanProofSession) {
        self.sessions.insert(session.session_id.clone(), session);
    }
}

impl Default for HumanProofSessionStore {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanSessionId(String);

impl HumanSessionId {
    pub fn new_unchecked(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn wire(&self) -> &str {
        self.as_str()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanDocumentId(String);

impl HumanDocumentId {
    pub fn new_unchecked(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn wire(&self) -> &str {
        self.as_str()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanDocumentVersion(u64);

impl HumanDocumentVersion {
    pub const fn initial() -> Self {
        Self(1)
    }

    pub const fn new_unchecked(value: u64) -> Self {
        Self(value)
    }

    pub const fn as_u64(self) -> u64 {
        self.0
    }

    pub fn next(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }
}

#[derive(Clone, Debug)]
pub struct HumanProofStateStore {
    entries: BTreeMap<HumanStateId, HumanProofStateEntry>,
    next_state_index: u64,
    next_goal_index: u64,
}

impl HumanProofStateStore {
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
            next_state_index: 1,
            next_goal_index: 1,
        }
    }

    pub fn state(&self, state_id: &HumanStateId) -> Option<&HumanProofStateEntry> {
        self.entries.get(state_id)
    }

    pub fn state_count(&self) -> usize {
        self.entries.len()
    }

    pub fn states(&self) -> impl Iterator<Item = &HumanProofStateEntry> {
        self.entries.values()
    }

    pub(crate) fn insert_initial_state(
        &mut self,
        state: MachineProofState,
        document_version: HumanDocumentVersion,
        source_span: Option<Span>,
        selected_goal: Option<GoalId>,
        messages: Vec<HumanDiagnostic>,
    ) -> Result<HumanProofStateEntry, HumanProofStateStoreMutationError> {
        self.insert_state_entry(HumanProofStateEntryInput {
            parent_state_id: None,
            parent_goal_mappings: &[],
            state,
            document_version,
            source_span,
            selected_goal,
            messages,
        })
    }

    pub(crate) fn insert_transition_state(
        &mut self,
        parent_state_id: &HumanStateId,
        state: MachineProofState,
        source_span: Option<Span>,
        selected_goal: Option<GoalId>,
        messages: Vec<HumanDiagnostic>,
    ) -> Result<HumanProofStateEntry, HumanProofStateStoreMutationError> {
        let (parent_document_version, parent_goal_mappings) = {
            let parent = self
                .entries
                .get(parent_state_id)
                .ok_or(HumanProofStateStoreMutationError::UnknownParentState)?;
            (parent.document_version, parent.goal_mappings.clone())
        };
        self.insert_state_entry(HumanProofStateEntryInput {
            parent_state_id: Some(parent_state_id.clone()),
            parent_goal_mappings: &parent_goal_mappings,
            state,
            document_version: parent_document_version,
            source_span,
            selected_goal,
            messages,
        })
    }

    fn insert_state_entry(
        &mut self,
        input: HumanProofStateEntryInput<'_>,
    ) -> Result<HumanProofStateEntry, HumanProofStateStoreMutationError> {
        let goal_mappings =
            self.goal_mappings_for_state(&input.state, input.parent_goal_mappings)?;
        let selected_goal = selected_human_goal(input.selected_goal, &input.state, &goal_mappings);
        let state_id = self.allocate_state_id()?;
        let entry = HumanProofStateEntry {
            state_id: state_id.clone(),
            parent_state_id: input.parent_state_id,
            document_version: input.document_version,
            source_span: input.source_span,
            selected_goal,
            goal_mappings,
            state: input.state,
            messages: input.messages,
        };
        self.entries.insert(state_id, entry.clone());
        Ok(entry)
    }

    fn goal_mappings_for_state(
        &mut self,
        state: &MachineProofState,
        parent_goal_mappings: &[HumanGoalMapping],
    ) -> Result<Vec<HumanGoalMapping>, HumanProofStateStoreMutationError> {
        let mut mappings = Vec::with_capacity(state.open_goals.len());
        for machine_goal_id in &state.open_goals {
            if let Some(existing) = parent_goal_mappings
                .iter()
                .find(|mapping| mapping.machine_goal_id == *machine_goal_id)
            {
                mappings.push(existing.clone());
                continue;
            }
            mappings.push(HumanGoalMapping {
                human_goal_id: self.allocate_goal_id()?,
                machine_goal_id: *machine_goal_id,
            });
        }
        Ok(mappings)
    }

    fn allocate_state_id(&mut self) -> Result<HumanStateId, HumanProofStateStoreMutationError> {
        let next = self
            .next_state_index
            .checked_add(1)
            .ok_or(HumanProofStateStoreMutationError::IdSpaceExhausted)?;
        let state_id = HumanStateId::new_unchecked(format!("hst_{}", self.next_state_index));
        self.next_state_index = next;
        Ok(state_id)
    }

    fn allocate_goal_id(&mut self) -> Result<HumanGoalId, HumanProofStateStoreMutationError> {
        let next = self
            .next_goal_index
            .checked_add(1)
            .ok_or(HumanProofStateStoreMutationError::IdSpaceExhausted)?;
        let goal_id = HumanGoalId::new_unchecked(format!("hgoal_{}", self.next_goal_index));
        self.next_goal_index = next;
        Ok(goal_id)
    }
}

struct HumanProofStateEntryInput<'a> {
    parent_state_id: Option<HumanStateId>,
    parent_goal_mappings: &'a [HumanGoalMapping],
    state: MachineProofState,
    document_version: HumanDocumentVersion,
    source_span: Option<Span>,
    selected_goal: Option<GoalId>,
    messages: Vec<HumanDiagnostic>,
}

impl Default for HumanProofStateStore {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug)]
pub struct HumanProofStateEntry {
    pub state_id: HumanStateId,
    pub parent_state_id: Option<HumanStateId>,
    pub document_version: HumanDocumentVersion,
    pub source_span: Option<Span>,
    pub selected_goal: Option<HumanGoalId>,
    pub goal_mappings: Vec<HumanGoalMapping>,
    pub state: MachineProofState,
    pub messages: Vec<HumanDiagnostic>,
}

impl HumanProofStateEntry {
    pub fn human_goal_for_machine_goal(&self, goal_id: GoalId) -> Option<&HumanGoalId> {
        self.goal_mappings
            .iter()
            .find(|mapping| mapping.machine_goal_id == goal_id)
            .map(|mapping| &mapping.human_goal_id)
    }

    pub fn machine_goal_for_human_goal(&self, goal_id: &HumanGoalId) -> Option<GoalId> {
        self.goal_mappings
            .iter()
            .find(|mapping| &mapping.human_goal_id == goal_id)
            .map(|mapping| mapping.machine_goal_id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanGoalMapping {
    pub human_goal_id: HumanGoalId,
    pub machine_goal_id: GoalId,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanStateId(String);

impl HumanStateId {
    pub fn new_unchecked(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn wire(&self) -> &str {
        self.as_str()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanGoalId(String);

impl HumanGoalId {
    pub fn new_unchecked(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn wire(&self) -> &str {
        self.as_str()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HumanProofStateStoreMutationError {
    IdSpaceExhausted,
    UnknownParentState,
}

fn selected_human_goal(
    selected_goal: Option<GoalId>,
    state: &MachineProofState,
    goal_mappings: &[HumanGoalMapping],
) -> Option<HumanGoalId> {
    let selected_machine_goal = selected_goal.or_else(|| state.open_goals.first().copied())?;
    goal_mappings
        .iter()
        .find(|mapping| mapping.machine_goal_id == selected_machine_goal)
        .map(|mapping| mapping.human_goal_id.clone())
}

#[derive(Clone, Debug)]
pub struct HumanProofStateStartRequest {
    pub session_id: HumanSessionId,
    pub theorem_name: Name,
    pub source_span: Option<Span>,
    pub selected_goal: Option<GoalId>,
    pub messages: Vec<HumanDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanProofStateStartOk {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub document_version: HumanDocumentVersion,
    pub selected_goal: Option<HumanGoalId>,
    pub goal_mappings: Vec<HumanGoalMapping>,
    pub messages: Vec<HumanDiagnostic>,
}

#[derive(Clone, Debug)]
pub struct HumanTacticStateRecordRequest {
    pub session_id: HumanSessionId,
    pub parent_state_id: HumanStateId,
    pub state: MachineProofState,
    pub source_span: Option<Span>,
    pub selected_goal: Option<GoalId>,
    pub messages: Vec<HumanDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticStateRecordOk {
    pub session_id: HumanSessionId,
    pub parent_state_id: HumanStateId,
    pub state_id: HumanStateId,
    pub document_version: HumanDocumentVersion,
    pub selected_goal: Option<HumanGoalId>,
    pub goal_mappings: Vec<HumanGoalMapping>,
    pub messages: Vec<HumanDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredProofState {
    pub session_id: HumanSessionId,
    pub state_id: HumanStateId,
    pub document_version: HumanDocumentVersion,
    pub source_span: Option<Span>,
    pub selected_goal: Option<HumanGoalId>,
    pub goals: Vec<StructuredGoal>,
    pub messages: Vec<HumanDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredGoal {
    pub goal_id: HumanGoalId,
    pub machine_goal_id: GoalId,
    pub meta_id: MetaVarId,
    pub name: Option<String>,
    pub context_hash: Hash,
    pub context: Vec<StructuredHypothesis>,
    pub target: StructuredExpr,
    pub target_core_hash: Hash,
    pub source_span: Option<Span>,
    pub status: StructuredGoalStatus,
    pub pretty: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredHypothesis {
    pub local_id: LocalId,
    pub name: String,
    pub ty: StructuredExpr,
    pub value: Option<StructuredExpr>,
    pub is_local_def: bool,
    pub is_implicit: bool,
    pub depends_on: Vec<LocalId>,
    pub binder_index: u32,
    pub pretty: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuredExpr {
    pub core_hash: Hash,
    pub head: Option<Name>,
    pub constants: Vec<Name>,
    pub free_locals: Vec<LocalId>,
    pub size: u32,
    pub pretty: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructuredGoalStatus {
    Open,
}

#[derive(Clone, Debug)]
pub struct HumanStartProofRequest<'src, 'imports> {
    pub current_module: ModuleName,
    pub theorem_name: Name,
    pub current_source: HumanCurrentModuleSource<'src>,
    pub verified_modules: &'imports [VerifiedModule],
    pub imported_source_interfaces: &'imports [HumanImportedSourceInterface],
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanCompileCoreOk {
    pub core_module: CoreModule,
    pub source_interface: HumanSourceInterface,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanCompileCertificateOk {
    pub certificate: ModuleCert,
    pub source_interface: HumanSourceInterface,
}

#[derive(Clone, Debug)]
pub struct HumanStartProofOk {
    pub state: MachineProofState,
    pub source_interface: HumanSourceInterface,
}

#[derive(Clone, Debug)]
pub struct HumanTacticTermCheckRequest<'term, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub term: &'term HumanExpr,
    pub current_source_interface: &'ctx HumanSourceInterface,
    pub imported_source_interfaces: &'ctx [HumanImportedSourceInterface],
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanTacticTermCheckOk {
    pub expr: Expr,
    pub inferred_type: Expr,
}

#[derive(Clone, Debug)]
pub struct HumanExactTacticRequest<'term, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub term: &'term HumanExpr,
    pub current_source_interface: &'ctx HumanSourceInterface,
    pub imported_source_interfaces: &'ctx [HumanImportedSourceInterface],
    pub options: HumanApiCompileOptions,
}

#[derive(Clone, Debug)]
pub struct HumanExactTacticOk {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
    pub expr: Expr,
    pub inferred_type: Expr,
}

#[derive(Clone, Debug)]
pub struct HumanIntroTacticRequest<'name, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub name: &'name HumanName,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanIntroTacticOk {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
}

#[derive(Clone, Debug)]
pub struct HumanApplyTacticRequest<'term, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub term: &'term HumanExpr,
    pub current_source_interface: &'ctx HumanSourceInterface,
    pub imported_source_interfaces: &'ctx [HumanImportedSourceInterface],
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanApplyTacticOk {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
}

#[derive(Clone, Debug)]
pub struct HumanRewriteTacticRequest<'rules, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub rules: &'rules [HumanRewriteRuleSyntax],
    pub span: npa_frontend::Span,
    pub current_source_interface: &'ctx HumanSourceInterface,
    pub imported_source_interfaces: &'ctx [HumanImportedSourceInterface],
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanRewriteTacticOk {
    pub state: MachineProofState,
    pub deltas: Vec<MachineProofDelta>,
}

#[derive(Clone, Debug)]
pub struct HumanSimpLiteTacticRequest<'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub span: npa_frontend::Span,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanSimpLiteTacticOk {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
}

#[derive(Clone, Debug)]
pub struct HumanSmtTacticRequest<'lemmas, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub lemmas: &'lemmas [HumanExpr],
    pub span: npa_frontend::Span,
    pub current_source_interface: &'ctx HumanSourceInterface,
    pub imported_source_interfaces: &'ctx [HumanImportedSourceInterface],
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanSmtTacticOk {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
}

#[derive(Clone, Debug)]
pub struct HumanInductionTacticRequest<'name, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub goal_id: GoalId,
    pub name: &'name HumanName,
    pub span: npa_frontend::Span,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanInductionTacticOk {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
}

#[derive(Clone, Debug)]
pub struct HumanTacticScriptRunRequest<'script, 'ctx> {
    pub state: &'ctx MachineProofState,
    pub script: &'script HumanTacticScript,
    pub current_source_interface: &'ctx HumanSourceInterface,
    pub imported_source_interfaces: &'ctx [HumanImportedSourceInterface],
    pub options: HumanApiCompileOptions,
    pub budget: TacticBudget,
}

#[derive(Clone, Debug)]
pub struct HumanTacticScriptRunOk {
    pub state: MachineProofState,
    pub deltas: Vec<MachineProofDelta>,
    pub proof: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanSessionCreateError {
    IdSpaceExhausted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDocumentUpdateError {
    UnknownSession {
        session_id: HumanSessionId,
    },
    DocumentVersionOverflow {
        session_id: HumanSessionId,
        document_id: HumanDocumentId,
        current: HumanDocumentVersion,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanProofStateStartError {
    UnknownSession { session_id: HumanSessionId },
    IdSpaceExhausted,
    Start(HumanStartProofError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanTacticStateRecordError {
    UnknownSession {
        session_id: HumanSessionId,
    },
    UnknownParentState {
        session_id: HumanSessionId,
        parent_state_id: HumanStateId,
    },
    IdSpaceExhausted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanStructuredProofStateError {
    UnknownSession {
        session_id: HumanSessionId,
    },
    UnknownState {
        session_id: HumanSessionId,
        state_id: HumanStateId,
    },
    MissingGoalMapping {
        state_id: HumanStateId,
        machine_goal_id: GoalId,
    },
    MachineGoal {
        state_id: HumanStateId,
        machine_goal_id: GoalId,
        diagnostic: Box<MachineTacticDiagnostic>,
    },
    ExpressionMetadata {
        state_id: HumanStateId,
        error: Box<MachineExprRendererError>,
    },
    LocalIndexExhausted {
        state_id: HumanStateId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanStateRequestError {
    UnknownSession {
        session_id: HumanSessionId,
    },
    DocumentMismatch {
        session_id: HumanSessionId,
        requested: HumanDocumentId,
        current: HumanDocumentId,
    },
    StaleDocumentVersion {
        session_id: HumanSessionId,
        document_id: HumanDocumentId,
        requested: HumanDocumentVersion,
        current: HumanDocumentVersion,
    },
    FutureDocumentVersion {
        session_id: HumanSessionId,
        document_id: HumanDocumentId,
        requested: HumanDocumentVersion,
        current: HumanDocumentVersion,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanStateApiError {
    UnknownSession {
        session_id: HumanSessionId,
    },
    DocumentMismatch {
        session_id: HumanSessionId,
        requested: HumanDocumentId,
        current: HumanDocumentId,
    },
    StaleDocumentVersion {
        session_id: HumanSessionId,
        document_id: HumanDocumentId,
        requested: HumanDocumentVersion,
        current: HumanDocumentVersion,
    },
    FutureDocumentVersion {
        session_id: HumanSessionId,
        document_id: HumanDocumentId,
        requested: HumanDocumentVersion,
        current: HumanDocumentVersion,
    },
    UnknownState {
        session_id: HumanSessionId,
        state_id: HumanStateId,
    },
    StaleProofState {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        requested_document_version: HumanDocumentVersion,
        state_document_version: HumanDocumentVersion,
    },
    NoCurrentState {
        session_id: HumanSessionId,
        document_version: HumanDocumentVersion,
    },
    NoProofStateAtPosition {
        session_id: HumanSessionId,
        document_version: HumanDocumentVersion,
        position: HumanSourcePosition,
    },
    StateMaterialization {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        error: Box<HumanStructuredProofStateError>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDisplayError {
    State(HumanStateApiError),
    UnknownGoal {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        goal_id: HumanGoalId,
    },
    MachineGoal {
        session_id: HumanSessionId,
        state_id: HumanStateId,
        goal_id: HumanGoalId,
        diagnostic: Box<MachineTacticDiagnostic>,
    },
}

impl From<HumanStateApiError> for HumanDisplayError {
    fn from(error: HumanStateApiError) -> Self {
        Self::State(error)
    }
}

impl From<HumanStateRequestError> for HumanStateApiError {
    fn from(error: HumanStateRequestError) -> Self {
        match error {
            HumanStateRequestError::UnknownSession { session_id } => {
                Self::UnknownSession { session_id }
            }
            HumanStateRequestError::DocumentMismatch {
                session_id,
                requested,
                current,
            } => Self::DocumentMismatch {
                session_id,
                requested,
                current,
            },
            HumanStateRequestError::StaleDocumentVersion {
                session_id,
                document_id,
                requested,
                current,
            } => Self::StaleDocumentVersion {
                session_id,
                document_id,
                requested,
                current,
            },
            HumanStateRequestError::FutureDocumentVersion {
                session_id,
                document_id,
                requested,
                current,
            } => Self::FutureDocumentVersion {
                session_id,
                document_id,
                requested,
                current,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanCompileError {
    pub diagnostic: HumanDiagnostic,
}

impl From<HumanDiagnostic> for HumanCompileError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self { diagnostic }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanStartProofError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanStartProofError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanStartProofError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanTacticTermError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanTacticTermError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanTacticTermError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanIntroTacticError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanIntroTacticError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanIntroTacticError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanApplyTacticError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanApplyTacticError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanApplyTacticError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanRewriteTacticError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanRewriteTacticError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanRewriteTacticError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanSimpLiteTacticError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanSimpLiteTacticError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanSimpLiteTacticError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanInductionTacticError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanInductionTacticError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanInductionTacticError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanTacticScriptError {
    Human(HumanCompileError),
    Machine(MachineTacticDiagnostic),
}

impl From<HumanDiagnostic> for HumanTacticScriptError {
    fn from(diagnostic: HumanDiagnostic) -> Self {
        Self::Human(HumanCompileError::from(diagnostic))
    }
}

impl From<MachineTacticDiagnostic> for HumanTacticScriptError {
    fn from(diagnostic: MachineTacticDiagnostic) -> Self {
        Self::Machine(diagnostic)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineApiVersion {
    V1,
}

impl MachineApiVersion {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::V1 => MACHINE_API_VERSION,
        }
    }

    pub fn parse(value: &str) -> Result<Self, MachineWireGrammarError> {
        if value == MACHINE_API_VERSION {
            Ok(Self::V1)
        } else {
            Err(MachineWireGrammarError::new(
                MachineWireGrammarErrorKind::UnsupportedLiteral,
            ))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelCheckProfileId {
    BuiltinNone,
    BuiltinNatEqRec,
}

impl KernelCheckProfileId {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BuiltinNone => KERNEL_CHECK_PROFILE_BUILTIN_NONE,
            Self::BuiltinNatEqRec => KERNEL_CHECK_PROFILE_BUILTIN_NAT_EQ_REC,
        }
    }

    pub fn parse(value: &str) -> Result<Self, MachineWireGrammarError> {
        match value {
            KERNEL_CHECK_PROFILE_BUILTIN_NONE => Ok(Self::BuiltinNone),
            KERNEL_CHECK_PROFILE_BUILTIN_NAT_EQ_REC => Ok(Self::BuiltinNatEqRec),
            _ => Err(MachineWireGrammarError::new(
                MachineWireGrammarErrorKind::UnsupportedLiteral,
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MachineProofSession {
    pub session_id: SessionId,
    pub protocol_version: MachineApiVersion,
    pub session_root_hash: Hash,
    pub root: CheckedMachineProofRoot,
    pub imports: Vec<VerifiedImportKey>,
    pub import_certificate_context: MachineImportCertificateContext,
    pub machine_display_render_scope: MachineDisplayRenderScope,
    pub machine_surface_callable_interface_table: MachineSurfaceCallableInterfaceTable,
    pub checked_current_decls: MachineCheckedCurrentDeclContext,
    pub options: MachineApiOptions,
    pub initial_snapshot: MachineProofSnapshot,
    pub snapshots: MachineSnapshotStore,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedMachineProofRoot {
    pub module: ModuleName,
    pub theorem_name: Name,
    pub source_index: u64,
    pub universe_params: Vec<String>,
    pub theorem_type_source: MachineRootTermSource,
    pub theorem_type_core_hash: Hash,
}

impl CheckedMachineProofRoot {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_string(&mut out, "npa.machine-api.checked-machine-proof-root.v1");
        encode_name(&mut out, &self.module);
        encode_name(&mut out, &self.theorem_name);
        encode_uvar(&mut out, self.source_index);
        encode_list_len(&mut out, self.universe_params.len());
        for param in &self.universe_params {
            encode_string(&mut out, param);
        }
        encode_hash(&mut out, &self.theorem_type_source.frontend_canonical_hash);
        encode_hash(&mut out, &self.theorem_type_core_hash);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRootTermSource {
    pub source: String,
    pub frontend_canonical_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiOptions {
    pub kernel_check_profile: KernelCheckProfileId,
    pub allow_axioms: Vec<MachineAxiomRefWire>,
    pub tactic_options: MachineTacticOptionsRequest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticOptionsRequest {
    pub simp_rules: Vec<npa_tactic::SimpRuleRef>,
    pub eq_family: Option<npa_tactic::EqFamilyRef>,
    pub nat_family: Option<npa_tactic::NatFamilyRef>,
    pub max_simp_rewrite_steps: u64,
    pub max_open_goals: u64,
    pub max_metas: u64,
}

impl TryFrom<MachineTacticOptionsRequest> for npa_tactic::MachineTacticOptions {
    type Error = MachineTacticOptionsConversionError;

    fn try_from(value: MachineTacticOptionsRequest) -> Result<Self, Self::Error> {
        let max_open_goals = usize::try_from(value.max_open_goals)
            .map_err(|_| MachineTacticOptionsConversionError::ValueExceedsUsize)?;
        let max_metas = usize::try_from(value.max_metas)
            .map_err(|_| MachineTacticOptionsConversionError::ValueExceedsUsize)?;
        Ok(Self {
            simp_rules: value.simp_rules,
            max_simp_rewrite_steps: value.max_simp_rewrite_steps,
            max_open_goals,
            max_metas,
            eq_family: value.eq_family,
            nat_family: value.nat_family,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineTacticOptionsConversionError {
    ValueExceedsUsize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineProofSnapshot {
    pub snapshot_id: SnapshotId,
    pub session_id: SessionId,
    pub state_fingerprint: Hash,
    pub tactic_options_fingerprint: Hash,
    pub open_goals: Vec<GoalId>,
    pub goals: Vec<MachineGoalView>,
    pub proof_skeleton_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineGoalView {
    pub goal_id: GoalId,
    pub meta_id: MetaVarId,
    pub context_hash: Hash,
    pub local_name_map_hash: Hash,
    pub context: Vec<MachineLocalView>,
    pub target: MachineExprView,
    pub target_hash: Hash,
    pub goal_fingerprint: Hash,
    pub allowed_tactics: Vec<MachineApiTacticKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineLocalView {
    pub local_id: LocalId,
    pub machine_name: String,
    pub display_name: String,
    pub ty: MachineExprView,
    pub value: Option<MachineExprView>,
    pub depends_on: Vec<LocalId>,
    pub binder_index: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiErrorWire {
    pub kind: MachineApiErrorKind,
    pub phase: MachineApiDiagnosticPhase,
    pub diagnostic_hash: Hash,
    pub retryable: bool,
    pub goal_id: Option<GoalId>,
    pub tactic_kind: Option<MachineApiTacticKind>,
    pub primary_name: Option<Name>,
    pub primary_axiom_ref: Option<MachineAxiomRefWire>,
    pub expected_hash: Option<Hash>,
    pub actual_hash: Option<Hash>,
}

impl MachineApiErrorWire {
    pub fn from_projection(
        diagnostic: &MachineApiDiagnosticProjection,
    ) -> Result<Self, MachineApiDiagnosticCanonicalizationError> {
        Ok(Self {
            kind: diagnostic.kind,
            phase: diagnostic.phase,
            diagnostic_hash: diagnostic.diagnostic_hash()?,
            retryable: diagnostic.retryable,
            goal_id: diagnostic.goal_id,
            tactic_kind: diagnostic.tactic_kind,
            primary_name: diagnostic.primary_name.clone(),
            primary_axiom_ref: diagnostic.primary_axiom_ref.clone(),
            expected_hash: diagnostic.expected_hash,
            actual_hash: diagnostic.actual_hash,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiCompactErrorWire {
    pub error_kind: MachineApiErrorKind,
    pub phase: MachineApiDiagnosticPhase,
    pub diagnostic_hash: Hash,
    pub retryable: bool,
    pub goal_id: Option<GoalId>,
    pub tactic_kind: Option<MachineApiTacticKind>,
    pub primary_name: Option<Name>,
    pub primary_axiom_ref: Option<MachineAxiomRefWire>,
    pub expected_hash: Option<Hash>,
    pub actual_hash: Option<Hash>,
}

impl From<MachineApiErrorWire> for MachineApiCompactErrorWire {
    fn from(value: MachineApiErrorWire) -> Self {
        Self {
            error_kind: value.kind,
            phase: value.phase,
            diagnostic_hash: value.diagnostic_hash,
            retryable: value.retryable,
            goal_id: value.goal_id,
            tactic_kind: value.tactic_kind,
            primary_name: value.primary_name,
            primary_axiom_ref: value.primary_axiom_ref,
            expected_hash: value.expected_hash,
            actual_hash: value.actual_hash,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiErrorResponse<ErrorObject = MachineApiErrorWire, TopLevelFields = ()> {
    pub status: MachineApiResponseStatus,
    pub error: ErrorObject,
    pub endpoint_fields: TopLevelFields,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiOkResponse<TopLevelFields> {
    pub status: MachineApiResponseStatus,
    pub endpoint_fields: TopLevelFields,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiSchedulerResponse<TopLevelFields = ()> {
    pub status: MachineApiResponseStatus,
    pub scheduler_artifact: MachineSchedulerArtifact,
    pub endpoint_fields: TopLevelFields,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineApiResponseEnvelope<
    OkTopLevelFields,
    ErrorObject = MachineApiErrorWire,
    ErrorTopLevelFields = (),
    SchedulerTopLevelFields = (),
> {
    Ok(MachineApiOkResponse<OkTopLevelFields>),
    Error(Box<MachineApiErrorResponse<ErrorObject, ErrorTopLevelFields>>),
    SchedulerStopped(MachineApiSchedulerResponse<SchedulerTopLevelFields>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineApiResponseStatus {
    Ok,
    Deleted,
    Success,
    Error,
    SchedulerStopped,
    PartialTimeout,
    PartialResourceLimit,
    Verified,
}

impl MachineApiResponseStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Deleted => "deleted",
            Self::Success => "success",
            Self::Error => "error",
            Self::SchedulerStopped => "scheduler_stopped",
            Self::PartialTimeout => "partial_timeout",
            Self::PartialResourceLimit => "partial_resource_limit",
            Self::Verified => "verified",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSchedulerArtifact {
    pub kind: MachineSchedulerArtifactKind,
    pub scope: MachineSchedulerArtifactScope,
    pub retryable: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineSchedulerArtifactKind {
    Timeout,
    ResourceLimitExceeded,
}

impl MachineSchedulerArtifactKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Timeout => "timeout",
            Self::ResourceLimitExceeded => "resource_limit_exceeded",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineSchedulerArtifactScope {
    Candidate,
    Batch,
    Replay,
}

impl MachineSchedulerArtifactScope {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Candidate => "candidate",
            Self::Batch => "batch",
            Self::Replay => "replay",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SessionId(String);

impl SessionId {
    pub fn parse(value: &str) -> Result<Self, MachineWireGrammarError> {
        validate_session_id(value)?;
        Ok(Self(value.to_owned()))
    }

    pub fn new_unchecked(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn wire(&self) -> &str {
        self.as_str()
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_string(&mut out, self.as_str());
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SnapshotId {
    digest: Hash,
}

impl SnapshotId {
    pub fn parse(value: &str) -> Result<Self, MachineWireGrammarError> {
        let suffix = value.strip_prefix("mst_").ok_or_else(|| {
            MachineWireGrammarError::new(MachineWireGrammarErrorKind::InvalidPrefix)
        })?;
        let digest = parse_hex_digest(suffix)?;
        Ok(Self { digest })
    }

    pub const fn from_digest(digest: Hash) -> Self {
        Self { digest }
    }

    pub const fn from_state_fingerprint(state_fingerprint: Hash) -> Self {
        Self {
            digest: state_fingerprint,
        }
    }

    pub const fn digest(self) -> Hash {
        self.digest
    }

    pub fn wire(self) -> String {
        format!("mst_{}", lower_hex_hash(&self.digest))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HashString {
    digest: Hash,
}

impl HashString {
    pub fn parse(value: &str) -> Result<Self, MachineWireGrammarError> {
        parse_hash_string(value).map(Self::from_digest)
    }

    pub const fn from_digest(digest: Hash) -> Self {
        Self { digest }
    }

    pub const fn digest(self) -> Hash {
        self.digest
    }

    pub fn wire(self) -> String {
        format_hash_string(&self.digest)
    }
}

pub fn parse_hash_string(value: &str) -> Result<Hash, MachineWireGrammarError> {
    let suffix = value
        .strip_prefix("sha256:")
        .ok_or_else(|| MachineWireGrammarError::new(MachineWireGrammarErrorKind::InvalidPrefix))?;
    parse_hex_digest(suffix)
}

pub fn format_hash_string(hash: &Hash) -> String {
    format!("sha256:{}", lower_hex_hash(hash))
}

pub fn parse_goal_id_wire(value: &str) -> Result<GoalId, MachineWireGrammarError> {
    let suffix = strip_prefixed_decimal(value, 'g')?;
    Ok(GoalId(parse_decimal_u64(suffix)?))
}

pub fn format_goal_id_wire(id: GoalId) -> String {
    format!("g{}", id.0)
}

pub fn parse_meta_var_id_wire(value: &str) -> Result<MetaVarId, MachineWireGrammarError> {
    let suffix = strip_prefixed_decimal(value, 'm')?;
    Ok(MetaVarId(parse_decimal_u64(suffix)?))
}

pub fn format_meta_var_id_wire(id: MetaVarId) -> String {
    format!("m{}", id.0)
}

pub const EXPR_PATH_MAX_STEPS: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExprPath {
    steps: Vec<ExprPathStep>,
}

impl ExprPath {
    pub fn new(steps: Vec<ExprPathStep>) -> Result<Self, MachineWireGrammarError> {
        if steps.len() > EXPR_PATH_MAX_STEPS {
            return Err(MachineWireGrammarError::new(
                MachineWireGrammarErrorKind::Overflow,
            ));
        }
        Ok(Self { steps })
    }

    pub fn empty() -> Self {
        Self { steps: Vec::new() }
    }

    pub fn steps(&self) -> &[ExprPathStep] {
        &self.steps
    }

    pub fn wire_segments(&self) -> Vec<String> {
        self.steps.iter().map(ExprPathStep::wire).collect()
    }

    pub fn parse_wire_segments(segments: &[String]) -> Result<Self, MachineWireGrammarError> {
        let steps = segments
            .iter()
            .map(|segment| ExprPathStep::parse(segment))
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(steps)
    }

    pub fn expr_at<'a>(&self, expr: &'a Expr) -> Option<&'a Expr> {
        let mut current = expr;
        for step in &self.steps {
            current = step.expr_child(current)?;
        }
        Some(current)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExprPathStep {
    PiDomain,
    PiBody,
    AppFunction,
    AppArgument(u32),
    EqType,
    EqLhs,
    EqRhs,
    ConstructorArgument(u32),
    RewriteOccurrence(u32),
    CheckedNode {
        category: String,
        index: Option<u32>,
    },
}

impl ExprPathStep {
    pub fn wire(&self) -> String {
        match self {
            Self::PiDomain => "PiDomain".to_owned(),
            Self::PiBody => "PiBody".to_owned(),
            Self::AppFunction => "AppFunction".to_owned(),
            Self::AppArgument(index) => format!("AppArgument({index})"),
            Self::EqType => "EqType".to_owned(),
            Self::EqLhs => "EqLhs".to_owned(),
            Self::EqRhs => "EqRhs".to_owned(),
            Self::ConstructorArgument(index) => format!("ConstructorArgument({index})"),
            Self::RewriteOccurrence(index) => format!("RewriteOccurrence({index})"),
            Self::CheckedNode { category, index } => match index {
                Some(index) => format!("CheckedNode({category},{index})"),
                None => format!("CheckedNode({category})"),
            },
        }
    }

    pub fn parse(value: &str) -> Result<Self, MachineWireGrammarError> {
        let step = match value {
            "PiDomain" => Self::PiDomain,
            "PiBody" => Self::PiBody,
            "AppFunction" => Self::AppFunction,
            "EqType" => Self::EqType,
            "EqLhs" => Self::EqLhs,
            "EqRhs" => Self::EqRhs,
            _ if value.starts_with("AppArgument(") => {
                Self::AppArgument(parse_expr_path_index(value, "AppArgument(")?)
            }
            _ if value.starts_with("ConstructorArgument(") => {
                Self::ConstructorArgument(parse_expr_path_index(value, "ConstructorArgument(")?)
            }
            _ if value.starts_with("RewriteOccurrence(") => {
                Self::RewriteOccurrence(parse_expr_path_index(value, "RewriteOccurrence(")?)
            }
            _ if value.starts_with("CheckedNode(") => parse_checked_node_path_step(value)?,
            _ => {
                return Err(MachineWireGrammarError::new(
                    MachineWireGrammarErrorKind::InvalidPrefix,
                ))
            }
        };
        if step.wire() == value {
            Ok(step)
        } else {
            Err(MachineWireGrammarError::new(
                MachineWireGrammarErrorKind::InvalidDecimal,
            ))
        }
    }

    fn expr_child<'a>(&self, expr: &'a Expr) -> Option<&'a Expr> {
        match self {
            Self::PiDomain => match expr {
                Expr::Pi { ty, .. } => Some(ty),
                _ => None,
            },
            Self::PiBody => match expr {
                Expr::Pi { body, .. } => Some(body),
                _ => None,
            },
            Self::AppFunction => flattened_app(expr).map(|(head, _)| head),
            Self::AppArgument(index) => flattened_app(expr)
                .and_then(|(_, args)| args.get(usize::try_from(*index).ok()?).copied()),
            Self::EqType => eq_arg(expr, 0),
            Self::EqLhs => eq_arg(expr, 1),
            Self::EqRhs => eq_arg(expr, 2),
            Self::ConstructorArgument(index) | Self::RewriteOccurrence(index) => {
                flattened_app(expr)
                    .and_then(|(_, args)| args.get(usize::try_from(*index).ok()?).copied())
            }
            Self::CheckedNode { .. } => None,
        }
    }
}

pub fn parse_expr_path_wire_segments(
    segments: &[String],
) -> Result<ExprPath, MachineWireGrammarError> {
    ExprPath::parse_wire_segments(segments)
}

pub fn format_expr_path_wire_segments(path: &ExprPath) -> Vec<String> {
    path.wire_segments()
}

pub fn parse_local_id_wire(value: &str) -> Result<LocalId, MachineWireGrammarError> {
    let suffix = strip_prefixed_decimal(value, 'l')?;
    let value = parse_decimal_u64(suffix)?;
    let value = u32::try_from(value)
        .map_err(|_| MachineWireGrammarError::new(MachineWireGrammarErrorKind::Overflow))?;
    Ok(LocalId(value))
}

fn parse_expr_path_index(
    value: &str,
    prefix: &'static str,
) -> Result<u32, MachineWireGrammarError> {
    let raw = value
        .strip_prefix(prefix)
        .and_then(|value| value.strip_suffix(')'))
        .ok_or_else(|| MachineWireGrammarError::new(MachineWireGrammarErrorKind::InvalidPrefix))?;
    let parsed = parse_decimal_u64(raw)?;
    u32::try_from(parsed)
        .map_err(|_| MachineWireGrammarError::new(MachineWireGrammarErrorKind::Overflow))
}

fn parse_checked_node_path_step(value: &str) -> Result<ExprPathStep, MachineWireGrammarError> {
    let raw = value
        .strip_prefix("CheckedNode(")
        .and_then(|value| value.strip_suffix(')'))
        .ok_or_else(|| MachineWireGrammarError::new(MachineWireGrammarErrorKind::InvalidPrefix))?;
    let (category, index) = match raw.split_once(',') {
        Some((category, index)) => (category, Some(index)),
        None => (raw, None),
    };
    if !is_expr_path_extension_category(category) {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidName,
        ));
    }
    let index = index
        .map(|index| {
            let parsed = parse_decimal_u64(index)?;
            u32::try_from(parsed)
                .map_err(|_| MachineWireGrammarError::new(MachineWireGrammarErrorKind::Overflow))
        })
        .transpose()?;
    Ok(ExprPathStep::CheckedNode {
        category: category.to_owned(),
        index,
    })
}

fn is_expr_path_extension_category(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_alphabetic() && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

fn flattened_app(expr: &Expr) -> Option<(&Expr, Vec<&Expr>)> {
    let mut args = Vec::new();
    let head = flatten_app_to(expr, &mut args);
    if args.is_empty() {
        None
    } else {
        args.reverse();
        Some((head, args))
    }
}

fn flatten_app_to<'a>(expr: &'a Expr, args: &mut Vec<&'a Expr>) -> &'a Expr {
    match expr {
        Expr::App(fun, arg) => {
            args.push(arg);
            flatten_app_to(fun, args)
        }
        _ => expr,
    }
}

fn eq_arg(expr: &Expr, index: usize) -> Option<&Expr> {
    let (head, args) = flattened_app(expr)?;
    match head {
        Expr::Const { name, .. } if name == "Eq" => args.get(index).copied(),
        _ => None,
    }
}

pub fn parse_machine_api_name(value: &str) -> Result<Name, MachineWireGrammarError> {
    if value.is_empty() || value.starts_with('.') || value.ends_with('.') || value.contains("..") {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidName,
        ));
    }
    let components = value.split('.').map(ToOwned::to_owned).collect::<Vec<_>>();
    let name = Name(components);
    if name.is_canonical() {
        Ok(name)
    } else {
        Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidName,
        ))
    }
}

pub fn parse_module_name_wire(value: &str) -> Result<ModuleName, MachineWireGrammarError> {
    parse_machine_api_name(value)
}

pub fn parse_fully_qualified_name_wire(value: &str) -> Result<Name, MachineWireGrammarError> {
    parse_machine_api_name(value)
}

pub fn machine_api_name_canonical_bytes(name: &Name) -> Result<Vec<u8>, MachineWireGrammarError> {
    if !name.is_canonical() {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidName,
        ));
    }
    let mut out = Vec::new();
    encode_name(&mut out, name);
    Ok(out)
}

pub fn is_machine_surface_name_component(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.is_empty() || bytes.len() > 64 || value == "_" {
        return false;
    }
    matches!(bytes[0], b'A'..=b'Z' | b'a'..=b'z' | b'_')
        && bytes[1..]
            .iter()
            .all(|byte| matches!(byte, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'\''))
}

pub fn is_machine_surface_term_head_component(value: &str) -> bool {
    is_machine_surface_name_component(value) && !is_machine_surface_reserved(value)
}

pub fn is_machine_surface_renderable_name_wire(name: &Name) -> bool {
    let Some((head, tail)) = name.0.split_first() else {
        return false;
    };
    is_machine_surface_term_head_component(head)
        && tail
            .iter()
            .all(|component| is_machine_surface_name_component(component))
}

pub fn is_machine_universe_param_name(value: &str) -> bool {
    is_machine_surface_name_component(value) && !is_machine_surface_reserved(value)
}

pub fn is_machine_local_name(value: &str) -> bool {
    is_machine_surface_term_head_component(value)
}

pub fn parse_machine_surface_renderable_name_wire(
    value: &str,
) -> Result<Name, MachineWireGrammarError> {
    let name = parse_machine_api_name(value)?;
    if is_machine_surface_renderable_name_wire(&name) {
        Ok(name)
    } else {
        Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::NonRenderableName,
        ))
    }
}

pub fn parse_machine_universe_param_name(value: &str) -> Result<String, MachineWireGrammarError> {
    if is_machine_universe_param_name(value) {
        Ok(value.to_owned())
    } else {
        Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidName,
        ))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineApiEndpoint {
    CreateSession,
    DeleteSession,
    SnapshotGet,
    TacticRun,
    TacticBatch,
    SearchForGoal,
    PremisesSearch,
    ImportProposals,
    PromptPayload,
    Replay,
    Verify,
}

impl MachineApiEndpoint {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CreateSession => "POST /machine/sessions",
            Self::DeleteSession => "DELETE /machine/sessions/{id}",
            Self::SnapshotGet => "POST /machine/snapshots/get",
            Self::TacticRun => "POST /machine/tactics/run",
            Self::TacticBatch => "POST /machine/tactics/batch",
            Self::SearchForGoal => "POST /machine/search/for_goal",
            Self::PremisesSearch => "POST /v1/npa/premises/search",
            Self::ImportProposals => "POST /v1/npa/imports/propose",
            Self::PromptPayload => "POST /machine/prompt_payload",
            Self::Replay => "POST /machine/replay",
            Self::Verify => "POST /machine/verify",
        }
    }

    pub const fn envelope_error_kind(self) -> MachineApiErrorKind {
        match self {
            Self::CreateSession | Self::DeleteSession => MachineApiErrorKind::InvalidSessionRequest,
            Self::SnapshotGet => MachineApiErrorKind::InvalidSnapshotRequest,
            Self::TacticRun => MachineApiErrorKind::InvalidTacticRunRequest,
            Self::TacticBatch => MachineApiErrorKind::InvalidBatchPolicy,
            Self::SearchForGoal => MachineApiErrorKind::InvalidTheoremQuery,
            Self::PremisesSearch | Self::ImportProposals => {
                MachineApiErrorKind::InvalidTheoremQuery
            }
            Self::PromptPayload => MachineApiErrorKind::InvalidPromptPayloadRequest,
            Self::Replay => MachineApiErrorKind::InvalidReplayPlan,
            Self::Verify => MachineApiErrorKind::InvalidVerifyRequest,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineEndpointFieldType {
    Object,
    Array,
    String,
    Boolean,
    UnsignedInteger { min: u64, max: u64 },
    SessionId,
    SnapshotId,
    HashString,
    GoalId,
    ProtocolVersion,
    VerifyMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineEndpointFieldSpec {
    pub name: &'static str,
    pub required: bool,
    pub field_type: MachineEndpointFieldType,
    pub error_kind: MachineApiErrorKind,
}

impl MachineEndpointFieldSpec {
    pub const fn required(
        name: &'static str,
        field_type: MachineEndpointFieldType,
        error_kind: MachineApiErrorKind,
    ) -> Self {
        Self {
            name,
            required: true,
            field_type,
            error_kind,
        }
    }

    pub const fn optional(
        name: &'static str,
        field_type: MachineEndpointFieldType,
        error_kind: MachineApiErrorKind,
    ) -> Self {
        Self {
            name,
            required: false,
            field_type,
            error_kind,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineEndpointEnvelopeSpec {
    pub endpoint: MachineApiEndpoint,
    pub fields: &'static [MachineEndpointFieldSpec],
}

pub fn machine_endpoint_envelope_spec(endpoint: MachineApiEndpoint) -> MachineEndpointEnvelopeSpec {
    MachineEndpointEnvelopeSpec {
        endpoint,
        fields: endpoint_fields(endpoint),
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MachineValidatedEndpointEnvelope<'value, 'src> {
    members: &'value [JsonMember<'src>],
}

impl<'value, 'src> MachineValidatedEndpointEnvelope<'value, 'src> {
    pub fn field(&self, field_name: &str) -> Option<&'value JsonValue<'src>> {
        self.members
            .iter()
            .find(|member| member.key() == field_name)
            .map(|member| member.value())
    }

    pub const fn members(&self) -> &'value [JsonMember<'src>] {
        self.members
    }
}

pub fn validate_machine_endpoint_envelope<'value, 'src>(
    value: &'value JsonValue<'src>,
    endpoint: MachineApiEndpoint,
    path: &JsonPath,
) -> Result<MachineValidatedEndpointEnvelope<'value, 'src>, MachineApiRequestError> {
    let envelope_kind = endpoint.envelope_error_kind();
    let Some(members) = value.object_members() else {
        return Err(MachineApiRequestError::new(
            envelope_kind,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };

    let fields = endpoint_fields(endpoint);
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(MachineApiRequestError::new(
                envelope_kind,
                path.field(member.key()),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }

    for member in members {
        if !fields.iter().any(|field| field.name == member.key()) {
            return Err(MachineApiRequestError::new(
                envelope_kind,
                path.field(member.key()),
                MachineApiRequestErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
    }

    for field in fields {
        let Some(member) = members.iter().find(|member| member.key() == field.name) else {
            if field.required {
                return Err(MachineApiRequestError::new(
                    field.error_kind,
                    path.field(field.name),
                    MachineApiRequestErrorReason::MissingField { field: field.name },
                ));
            }
            continue;
        };
        validate_endpoint_field(endpoint, field, member.value(), &path.field(field.name))?;
    }

    Ok(MachineValidatedEndpointEnvelope { members })
}

pub fn validate_delete_session_request(
    session_id: &str,
    has_body: bool,
) -> Result<SessionId, MachineApiRequestError> {
    if has_body {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidSessionRequest,
            JsonPath::root(),
            MachineApiRequestErrorReason::UnknownField {
                field: "body".to_owned(),
            },
        ));
    }
    SessionId::parse(session_id).map_err(|_| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidSessionRequest,
            JsonPath::root().field("session_id"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "session_id",
                expected: crate::JsonFieldType::String,
                actual: JsonValueKind::String,
            },
        )
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineWireGrammarError {
    pub kind: MachineWireGrammarErrorKind,
}

impl MachineWireGrammarError {
    pub const fn new(kind: MachineWireGrammarErrorKind) -> Self {
        Self { kind }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineWireGrammarErrorKind {
    InvalidPrefix,
    InvalidLength,
    InvalidCharacter,
    InvalidHex,
    InvalidDecimal,
    LeadingZero,
    Overflow,
    InvalidName,
    NonRenderableName,
    UnsupportedLiteral,
}

const SESSION_CREATE_FIELDS: &[MachineEndpointFieldSpec] = &[
    MachineEndpointFieldSpec::required(
        "protocol_version",
        MachineEndpointFieldType::ProtocolVersion,
        MachineApiErrorKind::InvalidSessionRequest,
    ),
    MachineEndpointFieldSpec::required(
        "root",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidSessionRequest,
    ),
    MachineEndpointFieldSpec::required(
        "import_closure",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidSessionRequest,
    ),
    MachineEndpointFieldSpec::required(
        "imports",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidSessionRequest,
    ),
    MachineEndpointFieldSpec::required(
        "checked_current_decls",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidSessionRequest,
    ),
    MachineEndpointFieldSpec::required(
        "options",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidSessionRequest,
    ),
];

const SNAPSHOT_GET_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidSnapshotRequest,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidSnapshotRequest,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidSnapshotRequest,
    ),
    common_required(
        "include_pretty",
        MachineEndpointFieldType::Boolean,
        MachineApiErrorKind::InvalidSnapshotRequest,
    ),
];

const TACTIC_RUN_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidTacticRunRequest,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidTacticRunRequest,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTacticRunRequest,
    ),
    common_required(
        "goal_id",
        MachineEndpointFieldType::GoalId,
        MachineApiErrorKind::InvalidTacticRunRequest,
    ),
    common_required(
        "candidate",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidTacticRunRequest,
    ),
    common_required(
        "deterministic_budget",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidBudget,
    ),
    common_optional(
        "scheduler_limits",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidSchedulerLimits,
    ),
];

const TACTIC_BATCH_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidBatchPolicy,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidBatchPolicy,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidBatchPolicy,
    ),
    common_required(
        "goal_id",
        MachineEndpointFieldType::GoalId,
        MachineApiErrorKind::InvalidBatchPolicy,
    ),
    common_required(
        "candidates",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidBatchPolicy,
    ),
    common_required(
        "deterministic_budget",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidBudget,
    ),
    common_required(
        "batch_policy",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidBatchPolicy,
    ),
    common_optional(
        "scheduler_limits",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidSchedulerLimits,
    ),
];

const SEARCH_FOR_GOAL_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "goal_id",
        MachineEndpointFieldType::GoalId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "modes",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "limit",
        MachineEndpointFieldType::UnsignedInteger { min: 1, max: 256 },
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "filters",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
];

const PREMISES_SEARCH_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "goal_id",
        MachineEndpointFieldType::GoalId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "modes",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "limit",
        MachineEndpointFieldType::UnsignedInteger { min: 1, max: 256 },
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "filters",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_optional(
        "expected_theorem_index_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_optional(
        "graph_snapshot_hash",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
];

const IMPORT_PROPOSAL_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "goal_id",
        MachineEndpointFieldType::GoalId,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "proposed_for_tasks",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_required(
        "candidates",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
    common_optional(
        "expected_visible_imports_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidTheoremQuery,
    ),
];

const PROMPT_PAYLOAD_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "goal_id",
        MachineEndpointFieldType::GoalId,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "include_pretty",
        MachineEndpointFieldType::Boolean,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "include_failed_candidates",
        MachineEndpointFieldType::Boolean,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "premise_selection",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
    common_required(
        "failed_candidates",
        MachineEndpointFieldType::Array,
        MachineApiErrorKind::InvalidPromptPayloadRequest,
    ),
];

const REPLAY_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidReplayPlan,
    ),
    common_required(
        "plan",
        MachineEndpointFieldType::Object,
        MachineApiErrorKind::InvalidReplayPlan,
    ),
];

const VERIFY_FIELDS: &[MachineEndpointFieldSpec] = &[
    common_required(
        "session_id",
        MachineEndpointFieldType::SessionId,
        MachineApiErrorKind::InvalidVerifyRequest,
    ),
    common_required(
        "snapshot_id",
        MachineEndpointFieldType::SnapshotId,
        MachineApiErrorKind::InvalidVerifyRequest,
    ),
    common_required(
        "state_fingerprint",
        MachineEndpointFieldType::HashString,
        MachineApiErrorKind::InvalidVerifyRequest,
    ),
    common_required(
        "mode",
        MachineEndpointFieldType::VerifyMode,
        MachineApiErrorKind::InvalidVerifyRequest,
    ),
];

const fn common_required(
    name: &'static str,
    field_type: MachineEndpointFieldType,
    error_kind: MachineApiErrorKind,
) -> MachineEndpointFieldSpec {
    MachineEndpointFieldSpec::required(name, field_type, error_kind)
}

const fn common_optional(
    name: &'static str,
    field_type: MachineEndpointFieldType,
    error_kind: MachineApiErrorKind,
) -> MachineEndpointFieldSpec {
    MachineEndpointFieldSpec::optional(name, field_type, error_kind)
}

fn endpoint_fields(endpoint: MachineApiEndpoint) -> &'static [MachineEndpointFieldSpec] {
    match endpoint {
        MachineApiEndpoint::CreateSession => SESSION_CREATE_FIELDS,
        MachineApiEndpoint::DeleteSession => &[],
        MachineApiEndpoint::SnapshotGet => SNAPSHOT_GET_FIELDS,
        MachineApiEndpoint::TacticRun => TACTIC_RUN_FIELDS,
        MachineApiEndpoint::TacticBatch => TACTIC_BATCH_FIELDS,
        MachineApiEndpoint::SearchForGoal => SEARCH_FOR_GOAL_FIELDS,
        MachineApiEndpoint::PremisesSearch => PREMISES_SEARCH_FIELDS,
        MachineApiEndpoint::ImportProposals => IMPORT_PROPOSAL_FIELDS,
        MachineApiEndpoint::PromptPayload => PROMPT_PAYLOAD_FIELDS,
        MachineApiEndpoint::Replay => REPLAY_FIELDS,
        MachineApiEndpoint::Verify => VERIFY_FIELDS,
    }
}

fn validate_endpoint_field(
    _endpoint: MachineApiEndpoint,
    field: &MachineEndpointFieldSpec,
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<(), MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Err(MachineApiRequestError::new(
            field.error_kind,
            path.clone(),
            MachineApiRequestErrorReason::NullField { field: field.name },
        ));
    }

    if let MachineEndpointFieldType::UnsignedInteger { min, max } = field.field_type {
        let Some(raw) = value.number_raw() else {
            return Err(endpoint_type_mismatch(field, value, path));
        };
        return parse_strict_u64_token(raw, max)
            .and_then(|parsed| {
                if parsed >= min {
                    Ok(parsed)
                } else {
                    Err(StrictUnsignedIntegerError::InvalidGrammar)
                }
            })
            .map(|_| ())
            .map_err(|error| {
                MachineApiRequestError::new(
                    field.error_kind,
                    path.clone(),
                    MachineApiRequestErrorReason::InvalidUnsignedInteger {
                        field: field.name,
                        raw: raw.to_owned(),
                        error,
                    },
                )
            });
    }

    let grammar_result = match field.field_type {
        MachineEndpointFieldType::Object if value.kind() == JsonValueKind::Object => Ok(()),
        MachineEndpointFieldType::Array if value.kind() == JsonValueKind::Array => Ok(()),
        MachineEndpointFieldType::String if value.kind() == JsonValueKind::String => Ok(()),
        MachineEndpointFieldType::Boolean if value.kind() == JsonValueKind::Bool => Ok(()),
        MachineEndpointFieldType::SessionId => value
            .string_value()
            .ok_or(())
            .and_then(|text| SessionId::parse(text).map(|_| ()).map_err(|_| ())),
        MachineEndpointFieldType::SnapshotId => value
            .string_value()
            .ok_or(())
            .and_then(|text| SnapshotId::parse(text).map(|_| ()).map_err(|_| ())),
        MachineEndpointFieldType::HashString => value
            .string_value()
            .ok_or(())
            .and_then(|text| HashString::parse(text).map(|_| ()).map_err(|_| ())),
        MachineEndpointFieldType::GoalId => value
            .string_value()
            .ok_or(())
            .and_then(|text| parse_goal_id_wire(text).map(|_| ()).map_err(|_| ())),
        MachineEndpointFieldType::ProtocolVersion => value
            .string_value()
            .ok_or(())
            .and_then(|text| MachineApiVersion::parse(text).map(|_| ()).map_err(|_| ())),
        MachineEndpointFieldType::VerifyMode => value.string_value().ok_or(()).and_then(|text| {
            if text == "certificate" {
                Ok(())
            } else {
                Err(())
            }
        }),
        _ => Err(()),
    };

    grammar_result.map_err(|_| endpoint_type_mismatch(field, value, path))
}

fn endpoint_type_mismatch(
    field: &MachineEndpointFieldSpec,
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        field.error_kind,
        path.clone(),
        MachineApiRequestErrorReason::TypeMismatch {
            field: field.name,
            expected: json_field_type_for_endpoint_field(field.field_type),
            actual: value.kind(),
        },
    )
}

fn json_field_type_for_endpoint_field(
    field_type: MachineEndpointFieldType,
) -> crate::JsonFieldType {
    match field_type {
        MachineEndpointFieldType::Object => crate::JsonFieldType::Object,
        MachineEndpointFieldType::Array => crate::JsonFieldType::Array,
        MachineEndpointFieldType::String
        | MachineEndpointFieldType::SessionId
        | MachineEndpointFieldType::SnapshotId
        | MachineEndpointFieldType::HashString
        | MachineEndpointFieldType::GoalId
        | MachineEndpointFieldType::ProtocolVersion
        | MachineEndpointFieldType::VerifyMode => crate::JsonFieldType::String,
        MachineEndpointFieldType::UnsignedInteger { max, .. } => {
            crate::JsonFieldType::UnsignedInteger { max }
        }
        MachineEndpointFieldType::Boolean => crate::JsonFieldType::Boolean,
    }
}

fn validate_session_id(value: &str) -> Result<(), MachineWireGrammarError> {
    let suffix = value
        .strip_prefix("msess_")
        .ok_or_else(|| MachineWireGrammarError::new(MachineWireGrammarErrorKind::InvalidPrefix))?;
    if suffix.is_empty() || suffix.len() > 64 {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidLength,
        ));
    }
    if suffix
        .as_bytes()
        .iter()
        .all(|byte| matches!(byte, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'.' | b'_' | b'-'))
    {
        Ok(())
    } else {
        Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidCharacter,
        ))
    }
}

fn parse_hex_digest(value: &str) -> Result<Hash, MachineWireGrammarError> {
    if value.len() != 64 {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidLength,
        ));
    }
    let mut out = [0u8; 32];
    for (index, chunk) in value.as_bytes().chunks_exact(2).enumerate() {
        let high = lowercase_hex_value(chunk[0])?;
        let low = lowercase_hex_value(chunk[1])?;
        out[index] = (high << 4) | low;
    }
    Ok(out)
}

fn lowercase_hex_value(byte: u8) -> Result<u8, MachineWireGrammarError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidHex,
        )),
        _ => Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidHex,
        )),
    }
}

fn lower_hex_hash(hash: &Hash) -> String {
    let mut out = String::with_capacity(64);
    for byte in hash {
        out.push(hex_digit(byte >> 4));
        out.push(hex_digit(byte & 0x0f));
    }
    out
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + value - 10),
        _ => unreachable!("hex nybble is in range"),
    }
}

fn strip_prefixed_decimal(value: &str, prefix: char) -> Result<&str, MachineWireGrammarError> {
    value
        .strip_prefix(prefix)
        .ok_or_else(|| MachineWireGrammarError::new(MachineWireGrammarErrorKind::InvalidPrefix))
}

fn parse_decimal_u64(value: &str) -> Result<u64, MachineWireGrammarError> {
    if value.is_empty() {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::InvalidDecimal,
        ));
    }
    if value.len() > 1 && value.as_bytes()[0] == b'0' {
        return Err(MachineWireGrammarError::new(
            MachineWireGrammarErrorKind::LeadingZero,
        ));
    }
    let mut out = 0u64;
    for byte in value.as_bytes() {
        if !byte.is_ascii_digit() {
            return Err(MachineWireGrammarError::new(
                MachineWireGrammarErrorKind::InvalidDecimal,
            ));
        }
        out = out
            .checked_mul(10)
            .and_then(|prefix| prefix.checked_add(u64::from(byte - b'0')))
            .ok_or_else(|| MachineWireGrammarError::new(MachineWireGrammarErrorKind::Overflow))?;
    }
    Ok(out)
}

fn is_machine_surface_reserved(value: &str) -> bool {
    matches!(
        value,
        "import"
            | "def"
            | "theorem"
            | "forall"
            | "fun"
            | "let"
            | "in"
            | "Prop"
            | "Type"
            | "Sort"
            | "succ"
            | "max"
            | "imax"
            | "open"
            | "namespace"
            | "match"
            | "with"
    )
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_list_len(out: &mut Vec<u8>, len: usize) {
    encode_uvar(out, len as u64);
}

fn encode_hash(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_request_body, MachineApiRequestErrorReason, MachineApiUpstreamDiagnostic};

    #[test]
    fn hash_and_snapshot_wire_grammar_is_canonical_lowercase_sha256() {
        let mut hash = [0u8; 32];
        hash[0] = 0xab;
        hash[31] = 0x05;

        let wire = format_hash_string(&hash);
        assert_eq!(
            wire,
            "sha256:ab00000000000000000000000000000000000000000000000000000000000005"
        );
        assert_eq!(parse_hash_string(&wire), Ok(hash));
        assert_eq!(
            parse_hash_string(
                "sha256:AB00000000000000000000000000000000000000000000000000000000000005"
            )
            .unwrap_err()
            .kind,
            MachineWireGrammarErrorKind::InvalidHex
        );

        let snapshot = SnapshotId::from_state_fingerprint(hash);
        assert_eq!(
            snapshot.wire(),
            "mst_ab00000000000000000000000000000000000000000000000000000000000005"
        );
        assert_eq!(SnapshotId::parse(&snapshot.wire()).unwrap(), snapshot);
    }

    #[test]
    fn id_wire_grammar_rejects_noncanonical_decimal_forms() {
        assert_eq!(parse_goal_id_wire("g0"), Ok(GoalId(0)));
        assert_eq!(parse_meta_var_id_wire("m42"), Ok(MetaVarId(42)));
        assert_eq!(parse_local_id_wire("l7"), Ok(LocalId(7)));
        assert_eq!(
            parse_goal_id_wire("g01").unwrap_err().kind,
            MachineWireGrammarErrorKind::LeadingZero
        );
        assert_eq!(
            parse_goal_id_wire("x1").unwrap_err().kind,
            MachineWireGrammarErrorKind::InvalidPrefix
        );
        assert_eq!(
            parse_local_id_wire("l4294967296").unwrap_err().kind,
            MachineWireGrammarErrorKind::Overflow
        );
    }

    #[test]
    fn expr_path_wire_grammar_round_trips_all_design_steps() {
        let path = ExprPath::new(vec![
            ExprPathStep::PiDomain,
            ExprPathStep::PiBody,
            ExprPathStep::AppFunction,
            ExprPathStep::AppArgument(1),
            ExprPathStep::EqType,
            ExprPathStep::EqLhs,
            ExprPathStep::EqRhs,
            ExprPathStep::ConstructorArgument(2),
            ExprPathStep::RewriteOccurrence(3),
            ExprPathStep::CheckedNode {
                category: "FutureCheckedNode".to_owned(),
                index: Some(4),
            },
            ExprPathStep::CheckedNode {
                category: "FutureCheckedNode".to_owned(),
                index: None,
            },
        ])
        .unwrap();

        let wire = path.wire_segments();
        assert_eq!(
            wire,
            vec![
                "PiDomain",
                "PiBody",
                "AppFunction",
                "AppArgument(1)",
                "EqType",
                "EqLhs",
                "EqRhs",
                "ConstructorArgument(2)",
                "RewriteOccurrence(3)",
                "CheckedNode(FutureCheckedNode,4)",
                "CheckedNode(FutureCheckedNode)",
            ]
        );
        assert_eq!(ExprPath::parse_wire_segments(&wire).unwrap(), path);
        assert_eq!(format_expr_path_wire_segments(&path), wire);
        assert_eq!(parse_expr_path_wire_segments(&wire).unwrap(), path);
    }

    #[test]
    fn expr_path_wire_grammar_rejects_invalid_indices() {
        for value in [
            "AppArgument(-1)",
            "AppArgument(01)",
            "AppArgument(4294967296)",
            "ConstructorArgument(-1)",
            "ConstructorArgument(01)",
            "RewriteOccurrence(-1)",
            "RewriteOccurrence(01)",
            "CheckedNode(FutureCheckedNode,01)",
            "CheckedNode(,1)",
        ] {
            assert!(
                ExprPathStep::parse(value).is_err(),
                "{value} must not be accepted as a canonical path step"
            );
        }
    }

    #[test]
    fn expr_path_locates_nested_application_argument_structurally() {
        let head = Expr::konst("F", vec![]);
        let first = Expr::konst("A", vec![]);
        let second = Expr::konst("B", vec![]);
        let app = Expr::apps(head.clone(), vec![first, second.clone()]);

        let function_path = ExprPath::new(vec![ExprPathStep::AppFunction]).unwrap();
        assert_eq!(function_path.expr_at(&app).cloned(), Some(head));

        let argument_path = ExprPath::new(vec![ExprPathStep::AppArgument(1)]).unwrap();
        assert_eq!(argument_path.expr_at(&app).cloned(), Some(second.clone()));

        let equality = npa_kernel::eq(
            npa_kernel::type0(),
            Expr::konst("Nat", vec![]),
            Expr::bvar(0),
            second,
        );
        let rhs_path = ExprPath::new(vec![ExprPathStep::EqRhs]).unwrap();
        assert_eq!(
            rhs_path.expr_at(&equality).cloned(),
            Some(Expr::konst("B", vec![]))
        );
    }

    #[test]
    fn session_id_wire_grammar_matches_mvp_regex() {
        assert!(SessionId::parse("msess_aZ09._-").is_ok());
        assert!(SessionId::parse("msess_").is_err());
        assert!(SessionId::parse("msess_space bad").is_err());
        assert!(SessionId::parse("other_a").is_err());
    }

    #[test]
    fn machine_api_names_and_renderable_names_are_distinct() {
        assert_eq!(
            parse_machine_api_name("Std.Nat.Basic").unwrap().as_dotted(),
            "Std.Nat.Basic"
        );
        assert!(parse_machine_api_name("Std..Nat").is_err());
        assert!(parse_machine_surface_renderable_name_wire("Nat.succ").is_ok());
        assert!(parse_machine_surface_renderable_name_wire("Prop").is_err());
        assert!(is_machine_universe_param_name("u"));
        assert!(!is_machine_universe_param_name("forall"));
        assert!(is_machine_local_name("x'"));
        assert!(!is_machine_local_name("Nat.x"));
    }

    #[test]
    fn endpoint_envelope_classifies_tactic_run_budget_before_scheduler() {
        let doc = parse_request_body(
            r#"{
              "session_id":"msess_1",
              "snapshot_id":"mst_0000000000000000000000000000000000000000000000000000000000000000",
              "state_fingerprint":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
              "goal_id":"g0",
              "candidate":{},
              "scheduler_limits": null
            }"#,
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
        .unwrap();

        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::TacticRun,
            &JsonPath::root(),
        )
        .unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidBudget);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::MissingField {
                field: "deterministic_budget"
            }
        );
    }

    #[test]
    fn endpoint_envelope_classifies_scheduler_limits_with_scheduler_error_kind() {
        let doc = parse_request_body(
            r#"{
              "session_id":"msess_1",
              "snapshot_id":"mst_0000000000000000000000000000000000000000000000000000000000000000",
              "state_fingerprint":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
              "goal_id":"g0",
              "candidate":{},
              "deterministic_budget":{},
              "scheduler_limits": null
            }"#,
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
        .unwrap();

        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::TacticRun,
            &JsonPath::root(),
        )
        .unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidSchedulerLimits);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::NullField {
                field: "scheduler_limits"
            }
        );
    }

    #[test]
    fn endpoint_envelope_uses_endpoint_field_order_not_request_order() {
        let doc = parse_request_body(
            r#"{
              "session_id":"msess_1",
              "snapshot_id":"mst_0000000000000000000000000000000000000000000000000000000000000000",
              "state_fingerprint":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
              "scheduler_limits": null,
              "goal_id":"g01",
              "candidate":{},
              "deterministic_budget":{}
            }"#,
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
        .unwrap();

        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::TacticRun,
            &JsonPath::root(),
        )
        .unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidTacticRunRequest);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "goal_id",
                expected: crate::JsonFieldType::String,
                actual: JsonValueKind::String
            }
        );
    }

    #[test]
    fn endpoint_envelope_validates_early_id_grammar_before_later_missing_fields() {
        let doc = parse_request_body(
            r#"{
              "session_id":"msess_1",
              "snapshot_id":"mst_0000000000000000000000000000000000000000000000000000000000000000",
              "state_fingerprint":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
              "goal_id":"g01",
              "candidate":{}
            }"#,
            MachineApiErrorKind::InvalidTacticRunRequest,
        )
        .unwrap();

        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::TacticRun,
            &JsonPath::root(),
        )
        .unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidTacticRunRequest);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "goal_id",
                expected: crate::JsonFieldType::String,
                actual: JsonValueKind::String
            }
        );
    }

    #[test]
    fn endpoint_envelope_rejects_unknown_and_duplicate_keys_with_endpoint_kind() {
        let doc = parse_request_body(
            r#"{"session_id":"msess_1","session_id":"msess_2"}"#,
            MachineApiErrorKind::InvalidReplayPlan,
        )
        .unwrap();
        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::Replay,
            &JsonPath::root(),
        )
        .unwrap_err();
        assert_eq!(err.kind, MachineApiErrorKind::InvalidReplayPlan);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::DuplicateKey {
                key: "session_id".to_owned()
            }
        );

        let doc = parse_request_body(
            r#"{"extra":true}"#,
            MachineApiErrorKind::InvalidVerifyRequest,
        )
        .unwrap();
        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::Verify,
            &JsonPath::root(),
        )
        .unwrap_err();
        assert_eq!(err.kind, MachineApiErrorKind::InvalidVerifyRequest);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::UnknownField {
                field: "extra".to_owned()
            }
        );
    }

    #[test]
    fn endpoint_envelope_validates_hash_and_id_grammar_before_lookup() {
        let doc = parse_request_body(
            r#"{
              "session_id":"msess_1",
              "snapshot_id":"mst_0000000000000000000000000000000000000000000000000000000000000000",
              "state_fingerprint":"sha256:0000000000000000000000000000000000000000000000000000000000000000",
              "goal_id":"g01",
              "modes":["exact"],
              "limit":20,
              "filters":{}
            }"#,
            MachineApiErrorKind::InvalidTheoremQuery,
        )
        .unwrap();

        let err = validate_machine_endpoint_envelope(
            doc.root(),
            MachineApiEndpoint::SearchForGoal,
            &JsonPath::root(),
        )
        .unwrap_err();
        assert_eq!(err.kind, MachineApiErrorKind::InvalidTheoremQuery);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::TypeMismatch {
                field: "goal_id",
                expected: crate::JsonFieldType::String,
                actual: JsonValueKind::String
            }
        );
    }

    #[test]
    fn error_wire_projects_canonical_diagnostic_fields() {
        let diagnostic = MachineApiDiagnosticProjection {
            kind: MachineApiErrorKind::GoalNotOpen,
            phase: MachineApiDiagnosticPhase::SnapshotLookup,
            retryable: false,
            goal_id: Some(GoalId(7)),
            tactic_kind: None,
            primary_name: None,
            primary_axiom_ref: None,
            expected_hash: None,
            actual_hash: None,
            source_message: "goal is not open".to_owned(),
            upstream: MachineApiUpstreamDiagnostic::MachineTactic(
                npa_tactic::MachineTacticDiagnostic::new(
                    npa_tactic::MachineTacticDiagnosticKind::UnknownGoal,
                    "goal is not open",
                ),
            ),
        };

        let wire = MachineApiErrorWire::from_projection(&diagnostic).unwrap();
        assert_eq!(wire.kind, MachineApiErrorKind::GoalNotOpen);
        assert_eq!(wire.phase, MachineApiDiagnosticPhase::SnapshotLookup);
        assert_eq!(wire.goal_id, Some(GoalId(7)));
        assert_eq!(wire.diagnostic_hash, diagnostic.diagnostic_hash().unwrap());

        let compact: MachineApiCompactErrorWire = wire.into();
        assert_eq!(compact.error_kind, MachineApiErrorKind::GoalNotOpen);
        assert_eq!(compact.goal_id, Some(GoalId(7)));
    }

    #[test]
    fn response_envelope_allows_endpoint_specific_top_level_fields() {
        #[derive(Clone, Debug, PartialEq, Eq)]
        struct TacticRunErrorFields {
            unchanged_state_fingerprint: Hash,
        }

        #[derive(Clone, Debug, PartialEq, Eq)]
        struct TacticRunErrorObject {
            diagnostic: MachineApiErrorWire,
            candidate_hash: Hash,
            deterministic_budget_hash: Hash,
        }

        let zero = [0u8; 32];
        let diagnostic = MachineApiDiagnosticProjection {
            kind: MachineApiErrorKind::GoalNotOpen,
            phase: MachineApiDiagnosticPhase::SnapshotLookup,
            retryable: false,
            goal_id: Some(GoalId(7)),
            tactic_kind: None,
            primary_name: None,
            primary_axiom_ref: None,
            expected_hash: None,
            actual_hash: None,
            source_message: "goal is not open".to_owned(),
            upstream: MachineApiUpstreamDiagnostic::MachineTactic(
                npa_tactic::MachineTacticDiagnostic::new(
                    npa_tactic::MachineTacticDiagnosticKind::UnknownGoal,
                    "goal is not open",
                ),
            ),
        };
        let error = TacticRunErrorObject {
            diagnostic: MachineApiErrorWire::from_projection(&diagnostic).unwrap(),
            candidate_hash: zero,
            deterministic_budget_hash: zero,
        };
        let envelope: MachineApiResponseEnvelope<(), TacticRunErrorObject, TacticRunErrorFields> =
            MachineApiResponseEnvelope::Error(Box::new(MachineApiErrorResponse {
                status: MachineApiResponseStatus::Error,
                error,
                endpoint_fields: TacticRunErrorFields {
                    unchanged_state_fingerprint: zero,
                },
            }));

        match envelope {
            MachineApiResponseEnvelope::Error(response) => {
                assert_eq!(response.status, MachineApiResponseStatus::Error);
                assert_eq!(response.error.candidate_hash, zero);
                assert_eq!(response.endpoint_fields.unchanged_state_fingerprint, zero);
            }
            _ => panic!("expected an error response"),
        }
    }

    #[test]
    fn scheduler_response_envelope_allows_endpoint_specific_top_level_fields() {
        #[derive(Clone, Debug, PartialEq, Eq)]
        struct TacticRunSchedulerFields {
            previous_state_fingerprint: Hash,
            deterministic_budget_hash: Hash,
        }

        #[derive(Clone, Debug, PartialEq, Eq)]
        struct BatchPartialFields {
            previous_state_fingerprint: Hash,
            deterministic_budget_hash: Hash,
            completed_prefix_len: u32,
        }

        let zero = [0u8; 32];
        let artifact = MachineSchedulerArtifact {
            kind: MachineSchedulerArtifactKind::Timeout,
            scope: MachineSchedulerArtifactScope::Candidate,
            retryable: true,
        };
        let envelope: MachineApiResponseEnvelope<
            (),
            MachineApiErrorWire,
            (),
            TacticRunSchedulerFields,
        > = MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
            status: MachineApiResponseStatus::SchedulerStopped,
            scheduler_artifact: artifact.clone(),
            endpoint_fields: TacticRunSchedulerFields {
                previous_state_fingerprint: zero,
                deterministic_budget_hash: zero,
            },
        });

        match envelope {
            MachineApiResponseEnvelope::SchedulerStopped(response) => {
                assert_eq!(response.status, MachineApiResponseStatus::SchedulerStopped);
                assert_eq!(response.scheduler_artifact, artifact);
                assert_eq!(response.endpoint_fields.previous_state_fingerprint, zero);
                assert_eq!(response.endpoint_fields.deterministic_budget_hash, zero);
            }
            _ => panic!("expected a scheduler response"),
        }

        let batch_artifact = MachineSchedulerArtifact {
            kind: MachineSchedulerArtifactKind::ResourceLimitExceeded,
            scope: MachineSchedulerArtifactScope::Batch,
            retryable: true,
        };
        let envelope: MachineApiResponseEnvelope<(), MachineApiErrorWire, (), BatchPartialFields> =
            MachineApiResponseEnvelope::SchedulerStopped(MachineApiSchedulerResponse {
                status: MachineApiResponseStatus::PartialResourceLimit,
                scheduler_artifact: batch_artifact,
                endpoint_fields: BatchPartialFields {
                    previous_state_fingerprint: zero,
                    deterministic_budget_hash: zero,
                    completed_prefix_len: 1,
                },
            });

        match envelope {
            MachineApiResponseEnvelope::SchedulerStopped(response) => {
                assert_eq!(
                    response.status,
                    MachineApiResponseStatus::PartialResourceLimit
                );
                assert_eq!(response.endpoint_fields.completed_prefix_len, 1);
            }
            _ => panic!("expected a partial scheduler response"),
        }
    }
}
