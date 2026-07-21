use npa_cert::{Hash, Name};
use npa_kernel::Decl;
use npa_tactic::{
    extract_closed_machine_theorem_decl, machine_tactic_cache_key, machine_tactic_cache_key_hash,
    machine_tactic_candidate_kind, machine_tactic_goal_id, machine_tactic_hash,
    prepare_machine_tactic_snapshot, run_machine_tactic_for_prepared_snapshot,
    run_machine_tactic_with_budget, start_machine_proof_with_kernel_profile, tactic_budget_hash,
    validate_machine_proof_state, validate_machine_tactic_candidate,
    validate_machine_tactic_for_state, validate_normalized_machine_tactic_for_prepared_snapshot,
    CandidateApplyArg, CandidateRewriteRuleRef, CheckedCurrentDecl, GoalId, MachineKernelProfile,
    MachineProofDelta, MachineProofSpec, MachineProofState, MachineTactic, MachineTacticCacheKey,
    MachineTacticCandidate, MachineTacticDiagnostic, MachineTacticDiagnosticKind,
    MachineTacticFeature, MachineTacticOptions, MachineTacticProfileVersion,
    MachineTacticValidationBudget, PreparedMachineTacticSnapshot, RawMachineTerm, ResolvedEqFamily,
    ResolvedNatFamily, TacticBudget, TacticFuelKind, VerifiedImportRef,
};

use crate::current::MachineAxiomRefWire;
use crate::MachineApiErrorKind;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineApiDiagnosticPhase {
    RequestValidation,
    SessionLookup,
    SessionCreate,
    SnapshotLookup,
    CandidateValidation,
    MachineTermParse,
    MachineTermCheck,
    TacticExecution,
    TheoremSearch,
    PromptPayload,
    ReplayValidation,
    ReplayExecution,
    KernelCheck,
    CertificateGeneration,
    CertificateVerify,
}

impl MachineApiDiagnosticPhase {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RequestValidation => "request_validation",
            Self::SessionLookup => "session_lookup",
            Self::SessionCreate => "session_create",
            Self::SnapshotLookup => "snapshot_lookup",
            Self::CandidateValidation => "candidate_validation",
            Self::MachineTermParse => "machine_term_parse",
            Self::MachineTermCheck => "machine_term_check",
            Self::TacticExecution => "tactic_execution",
            Self::TheoremSearch => "theorem_search",
            Self::PromptPayload => "prompt_payload",
            Self::ReplayValidation => "replay_validation",
            Self::ReplayExecution => "replay_execution",
            Self::KernelCheck => "kernel_check",
            Self::CertificateGeneration => "certificate_generation",
            Self::CertificateVerify => "certificate_verify",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineApiTacticKind {
    Intro,
    Exact,
    Apply,
    Rw,
    SimpLite,
    Smt,
    InductionNat,
    Constructor,
    Cases,
    GeneralInduction,
    Refine,
    Have,
    Suffices,
    Specialize,
    Revert,
    Generalize,
    Change,
    Unfold,
    Congr,
    Subst,
    Contradiction,
    FiniteDecide,
    Omega,
    Ring,
    Bitblast,
}

impl MachineApiTacticKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Intro => "intro",
            Self::Exact => "exact",
            Self::Apply => "apply",
            Self::Rw => "rw",
            Self::SimpLite => "simp-lite",
            Self::Smt => "smt",
            Self::InductionNat => "induction-nat",
            Self::Constructor => "constructor",
            Self::Cases => "cases",
            Self::GeneralInduction => "general-induction",
            Self::Refine => "refine",
            Self::Have => "have",
            Self::Suffices => "suffices",
            Self::Specialize => "specialize",
            Self::Revert => "revert",
            Self::Generalize => "generalize",
            Self::Change => "change",
            Self::Unfold => "unfold",
            Self::Congr => "congr",
            Self::Subst => "subst",
            Self::Contradiction => "contradiction",
            Self::FiniteDecide => "finite-decide",
            Self::Omega => "omega",
            Self::Ring => "ring",
            Self::Bitblast => "bitblast",
        }
    }

    fn from_machine_tactic_kind(kind: &str) -> Option<Self> {
        match kind {
            "intro" => Some(Self::Intro),
            "exact" => Some(Self::Exact),
            "apply" => Some(Self::Apply),
            "rw" => Some(Self::Rw),
            "simp-lite" => Some(Self::SimpLite),
            "smt" => Some(Self::Smt),
            "induction-nat" => Some(Self::InductionNat),
            "constructor" => Some(Self::Constructor),
            "cases" => Some(Self::Cases),
            "general-induction" => Some(Self::GeneralInduction),
            "refine" => Some(Self::Refine),
            "have" => Some(Self::Have),
            "suffices" => Some(Self::Suffices),
            "specialize" => Some(Self::Specialize),
            "revert" => Some(Self::Revert),
            "generalize" => Some(Self::Generalize),
            "change" => Some(Self::Change),
            "unfold" => Some(Self::Unfold),
            "congr" => Some(Self::Congr),
            "subst" => Some(Self::Subst),
            "contradiction" => Some(Self::Contradiction),
            "finite-decide" => Some(Self::FiniteDecide),
            "omega" => Some(Self::Omega),
            "ring" => Some(Self::Ring),
            "bitblast" => Some(Self::Bitblast),
            _ => None,
        }
    }

    pub(crate) fn from_candidate(candidate: &MachineTacticCandidate) -> Self {
        Self::from_machine_tactic_kind(machine_tactic_candidate_kind(candidate))
            .expect("machine tactic exposes only MVP tactic candidate kinds")
    }

    fn from_tactic(tactic: &MachineTactic) -> Self {
        match tactic {
            MachineTactic::Exact { .. } => Self::Exact,
            MachineTactic::Intro { .. } => Self::Intro,
            MachineTactic::Apply { .. } => Self::Apply,
            MachineTactic::Rewrite { .. } => Self::Rw,
            MachineTactic::SimpLite { .. } => Self::SimpLite,
            MachineTactic::Smt { .. } => Self::Smt,
            MachineTactic::InductionNat { .. } => Self::InductionNat,
            MachineTactic::Constructor { .. } => Self::Constructor,
            MachineTactic::Cases { .. } => Self::Cases,
            MachineTactic::GeneralInduction { .. } => Self::GeneralInduction,
            MachineTactic::Refine { .. } => Self::Refine,
            MachineTactic::Have { .. } => Self::Have,
            MachineTactic::Suffices { .. } => Self::Suffices,
            MachineTactic::Specialize { .. } => Self::Specialize,
            MachineTactic::Revert { .. } => Self::Revert,
            MachineTactic::Generalize { .. } => Self::Generalize,
            MachineTactic::Change { .. } => Self::Change,
            MachineTactic::Unfold { .. } => Self::Unfold,
            MachineTactic::Congr { .. } => Self::Congr,
            MachineTactic::Subst { .. } => Self::Subst,
            MachineTactic::Contradiction { .. } => Self::Contradiction,
            MachineTactic::FiniteDecide { .. } => Self::FiniteDecide,
            MachineTactic::Omega { .. } => Self::Omega,
            MachineTactic::Ring { .. } => Self::Ring,
            MachineTactic::Bitblast { .. } => Self::Bitblast,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineApiUpstreamDiagnostic {
    Frontend(npa_frontend::MachineDiagnostic),
    MachineTactic(MachineTacticDiagnostic),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiDiagnosticProjection {
    pub kind: MachineApiErrorKind,
    pub phase: MachineApiDiagnosticPhase,
    pub retryable: bool,
    pub goal_id: Option<GoalId>,
    pub tactic_kind: Option<MachineApiTacticKind>,
    pub primary_name: Option<Name>,
    pub primary_axiom_ref: Option<MachineAxiomRefWire>,
    pub expected_hash: Option<Hash>,
    pub actual_hash: Option<Hash>,
    pub source_message: String,
    pub upstream: MachineApiUpstreamDiagnostic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticAdapterError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub candidate_hash: Option<Hash>,
    pub deterministic_budget_hash: Option<Hash>,
    pub cache_key_hash: Option<Hash>,
}

pub type MachineTacticAdapterResult<T> = Result<T, Box<MachineTacticAdapterError>>;

#[derive(Clone, Debug)]
pub struct MachineTacticStartProofOutput {
    pub state: MachineProofState,
    pub state_fingerprint: Hash,
    pub options: MachineTacticOptions,
    pub resolved_eq_family: Option<ResolvedEqFamily>,
    pub resolved_nat_family: Option<ResolvedNatFamily>,
    pub options_fingerprint: Hash,
    pub env_fingerprint: Hash,
    pub simp_registry_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedMachineTactic {
    pub tactic: MachineTactic,
    pub goal_id: GoalId,
    pub tactic_kind: MachineApiTacticKind,
    pub candidate_hash: Hash,
}

#[derive(Clone, Debug)]
pub struct MachineTacticRunOutput {
    pub state: MachineProofState,
    pub delta: MachineProofDelta,
    pub goal_id: GoalId,
    pub tactic_kind: MachineApiTacticKind,
    pub candidate_hash: Hash,
    pub deterministic_budget_hash: Hash,
    pub cache_key_hash: Hash,
    pub next_state_fingerprint: Hash,
    pub proof_delta_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTacticExtractedTheorem {
    pub theorem: Decl,
}

pub fn machine_tactic_start_machine_proof(
    spec: MachineProofSpec,
    imports: Vec<VerifiedImportRef>,
    checked_current_decls: Vec<CheckedCurrentDecl>,
    options: MachineTacticOptions,
) -> MachineTacticAdapterResult<MachineTacticStartProofOutput> {
    machine_tactic_start_machine_proof_with_kernel_profile(
        MachineKernelProfile::BuiltinNatEqRec,
        spec,
        imports,
        checked_current_decls,
        options,
    )
}

pub fn machine_tactic_start_machine_proof_with_kernel_profile(
    kernel_profile: MachineKernelProfile,
    spec: MachineProofSpec,
    imports: Vec<VerifiedImportRef>,
    checked_current_decls: Vec<CheckedCurrentDecl>,
    options: MachineTacticOptions,
) -> MachineTacticAdapterResult<MachineTacticStartProofOutput> {
    start_machine_proof_with_kernel_profile(
        kernel_profile,
        spec,
        imports,
        checked_current_decls,
        options,
    )
    .map(|state| MachineTacticStartProofOutput {
        state_fingerprint: state.fingerprint,
        options: state.env.options.clone(),
        resolved_eq_family: state.env.eq_family.clone(),
        resolved_nat_family: state.env.nat_family.clone(),
        options_fingerprint: state.env.options_fingerprint,
        env_fingerprint: state.env.env_fingerprint,
        simp_registry_hash: npa_tactic::simp_registry_hash(&state.env.simp_registry),
        state,
    })
    .map_err(|diagnostic| {
        let phase = machine_tactic_start_proof_phase(&diagnostic);
        machine_tactic_error(diagnostic, phase)
    })
}

pub fn machine_tactic_validate_machine_tactic_candidate(
    goal_id: GoalId,
    candidate: MachineTacticCandidate,
) -> MachineTacticAdapterResult<ValidatedMachineTactic> {
    let tactic_kind = MachineApiTacticKind::from_candidate(&candidate);
    prepass_candidate_terms(&candidate, goal_id, tactic_kind)?;
    validate_machine_tactic_candidate(goal_id, candidate)
        .map(|tactic| {
            let candidate_hash = machine_tactic_hash(&tactic);
            ValidatedMachineTactic {
                tactic,
                goal_id,
                tactic_kind,
                candidate_hash,
            }
        })
        .map_err(|diagnostic| {
            machine_tactic_candidate_validation_error(diagnostic, goal_id, tactic_kind)
        })
}

pub fn machine_tactic_validate_machine_tactic_candidate_for_state(
    state: &MachineProofState,
    goal_id: GoalId,
    candidate: MachineTacticCandidate,
    deterministic_budget: TacticBudget,
    profile_version: MachineTacticProfileVersion,
    required_features: &[MachineTacticFeature],
) -> MachineTacticAdapterResult<ValidatedMachineTactic> {
    let tactic_kind = MachineApiTacticKind::from_candidate(&candidate);
    prepass_candidate_terms(&candidate, goal_id, tactic_kind)?;
    let tactic = validate_machine_tactic_candidate(goal_id, candidate).map_err(|diagnostic| {
        machine_tactic_candidate_validation_error(diagnostic, goal_id, tactic_kind)
    })?;
    let candidate_hash = machine_tactic_hash(&tactic);
    validate_machine_tactic_for_state(
        state,
        &tactic,
        MachineTacticValidationBudget::from(deterministic_budget),
        profile_version,
        required_features,
    )
    .map(|_| ValidatedMachineTactic {
        tactic,
        goal_id,
        tactic_kind,
        candidate_hash,
    })
    .map_err(|diagnostic| {
        let mut error = machine_tactic_candidate_validation_error(diagnostic, goal_id, tactic_kind);
        error.candidate_hash = Some(candidate_hash);
        error.deterministic_budget_hash = Some(tactic_budget_hash(deterministic_budget));
        error
    })
}

pub fn machine_tactic_prepare_machine_tactic_snapshot(
    state: &MachineProofState,
    goal_id: GoalId,
    tactic_kind: MachineApiTacticKind,
    candidate_hash: Hash,
    deterministic_budget: TacticBudget,
) -> MachineTacticAdapterResult<PreparedMachineTacticSnapshot<'_>> {
    prepare_machine_tactic_snapshot(state, goal_id).map_err(|diagnostic| {
        let mut error = machine_tactic_candidate_validation_error(diagnostic, goal_id, tactic_kind);
        error.candidate_hash = Some(candidate_hash);
        error.deterministic_budget_hash = Some(tactic_budget_hash(deterministic_budget));
        error
    })
}

pub fn machine_tactic_validate_normalized_machine_tactic_for_prepared_snapshot(
    prepared: &PreparedMachineTacticSnapshot<'_>,
    validated: ValidatedMachineTactic,
    deterministic_budget: TacticBudget,
    profile_version: MachineTacticProfileVersion,
    required_features: &[MachineTacticFeature],
) -> MachineTacticAdapterResult<ValidatedMachineTactic> {
    if let Err(diagnostic) = validate_normalized_machine_tactic_for_prepared_snapshot(
        prepared,
        &validated.tactic,
        MachineTacticValidationBudget::from(deterministic_budget),
        profile_version,
        required_features,
    ) {
        let mut error = machine_tactic_candidate_validation_error(
            diagnostic,
            validated.goal_id,
            validated.tactic_kind,
        );
        error.candidate_hash = Some(validated.candidate_hash);
        error.deterministic_budget_hash = Some(tactic_budget_hash(deterministic_budget));
        return Err(error);
    }
    Ok(validated)
}

pub fn machine_tactic_run_machine_tactic(
    state: &MachineProofState,
    tactic: MachineTactic,
) -> MachineTacticAdapterResult<MachineTacticRunOutput> {
    machine_tactic_run_machine_tactic_with_budget(state, tactic, TacticBudget::default())
}

pub fn machine_tactic_run_machine_tactic_with_budget(
    state: &MachineProofState,
    tactic: MachineTactic,
    budget: TacticBudget,
) -> MachineTacticAdapterResult<MachineTacticRunOutput> {
    if matches!(&tactic, MachineTactic::Bitblast { .. }) {
        if let Err(diagnostic) = validate_machine_proof_state(state) {
            return Err(machine_tactic_error(
                diagnostic,
                MachineApiDiagnosticPhase::SnapshotLookup,
            ));
        }
        return machine_tactic_run_with_projection(state.fingerprint, tactic, budget, |tactic| {
            run_machine_tactic_with_budget(state, tactic, budget)
        });
    }
    let goal_id = machine_tactic_goal_id(&tactic);
    let prepared = prepare_machine_tactic_snapshot(state, goal_id).map_err(|diagnostic| {
        machine_tactic_error(diagnostic, MachineApiDiagnosticPhase::SnapshotLookup)
    })?;
    machine_tactic_run_machine_tactic_for_prepared_snapshot(&prepared, tactic, budget)
}

pub fn machine_tactic_run_machine_tactic_for_prepared_snapshot(
    prepared: &PreparedMachineTacticSnapshot<'_>,
    tactic: MachineTactic,
    budget: TacticBudget,
) -> MachineTacticAdapterResult<MachineTacticRunOutput> {
    machine_tactic_run_with_projection(prepared.state_fingerprint(), tactic, budget, |tactic| {
        run_machine_tactic_for_prepared_snapshot(prepared, tactic, budget)
    })
}

fn machine_tactic_run_with_projection(
    state_fingerprint: Hash,
    tactic: MachineTactic,
    budget: TacticBudget,
    execute: impl FnOnce(
        MachineTactic,
    ) -> Result<(MachineProofState, MachineProofDelta), MachineTacticDiagnostic>,
) -> MachineTacticAdapterResult<MachineTacticRunOutput> {
    let goal_id = machine_tactic_goal_id(&tactic);
    let tactic_kind = MachineApiTacticKind::from_tactic(&tactic);
    let candidate_hash = machine_tactic_hash(&tactic);
    let deterministic_budget_hash = tactic_budget_hash(budget);
    let cache_key_hash = machine_tactic_cache_key_hash(&MachineTacticCacheKey {
        state_fingerprint,
        goal_id,
        tactic_hash: candidate_hash,
        deterministic_budget_hash,
    });
    execute(tactic)
        .map(|(state, delta)| MachineTacticRunOutput {
            next_state_fingerprint: state.fingerprint,
            proof_delta_hash: delta.delta_hash,
            state,
            delta,
            goal_id,
            tactic_kind,
            candidate_hash,
            deterministic_budget_hash,
            cache_key_hash,
        })
        .map_err(|diagnostic| {
            let include_correlation_hashes = tactic_run_correlation_hashes_allowed(&diagnostic);
            let phase = machine_tactic_run_phase(&diagnostic);
            let mut error = machine_tactic_error(diagnostic, phase);
            if include_correlation_hashes {
                error.candidate_hash = Some(candidate_hash);
                error.deterministic_budget_hash = Some(deterministic_budget_hash);
                error.cache_key_hash = Some(cache_key_hash);
            }
            error
        })
}

pub fn machine_tactic_extract_closed_machine_theorem_decl(
    state: &MachineProofState,
    phase: MachineApiDiagnosticPhase,
) -> MachineTacticAdapterResult<MachineTacticExtractedTheorem> {
    extract_closed_machine_theorem_decl(state)
        .map(|theorem| MachineTacticExtractedTheorem { theorem })
        .map_err(|diagnostic| machine_tactic_error(diagnostic, phase))
}

pub fn machine_tactic_machine_tactic_result_error(
    state: &MachineProofState,
    tactic: MachineTactic,
    budget: TacticBudget,
) -> Option<Box<MachineTacticAdapterError>> {
    if let Err(diagnostic) = validate_machine_proof_state(state) {
        return Some(machine_tactic_error(
            diagnostic,
            MachineApiDiagnosticPhase::SnapshotLookup,
        ));
    }

    match run_machine_tactic_with_budget(state, tactic.clone(), budget) {
        Ok(_) => None,
        Err(diagnostic) => {
            let candidate_hash = machine_tactic_hash(&tactic);
            let deterministic_budget_hash = tactic_budget_hash(budget);
            let cache_key_hash =
                machine_tactic_cache_key_hash(&machine_tactic_cache_key(state, &tactic, budget));
            let include_correlation_hashes = tactic_run_correlation_hashes_allowed(&diagnostic);
            let phase = machine_tactic_run_phase(&diagnostic);
            let mut error = machine_tactic_error(diagnostic, phase);
            if include_correlation_hashes {
                error.candidate_hash = Some(candidate_hash);
                error.deterministic_budget_hash = Some(deterministic_budget_hash);
                error.cache_key_hash = Some(cache_key_hash);
            }
            Some(error)
        }
    }
}

pub fn map_machine_tactic_diagnostic_kind(
    diagnostic: &MachineTacticDiagnostic,
) -> MachineApiErrorKind {
    use MachineApiErrorKind as Api;
    use MachineTacticDiagnosticKind as MachineTactic;

    match &diagnostic.kind {
        MachineTactic::InvalidMachineProofState
        | MachineTactic::UnknownMeta
        | MachineTactic::InvalidMetaContext
        | MachineTactic::InvalidMetaDependency
        | MachineTactic::ProofExprScopeError
        | MachineTactic::UnresolvedGoal
        | MachineTactic::AmbiguousKernelEnvDecl
        | MachineTactic::KernelRejected
        | MachineTactic::InvalidMachineTermSource => Api::InvalidMachineProofState,
        MachineTactic::MachineTermElaborationError => Api::MachineTermElaborationError,
        MachineTactic::UnknownName => Api::UnknownName,
        MachineTactic::ImplicitArgumentRequired | MachineTactic::MissingExplicitArgument => {
            Api::ImplicitArgumentRequired
        }
        MachineTactic::InvalidMachineProofSpec => Api::InvalidSessionRequest,
        MachineTactic::InvalidMachineTactic => Api::InvalidCandidate,
        MachineTactic::InvalidBatchPolicy => Api::InvalidBatchPolicy,
        MachineTactic::UnknownGoal | MachineTactic::GoalAlreadyAssigned => Api::GoalNotOpen,
        MachineTactic::UnknownTacticHead
        | MachineTactic::AmbiguousTacticHead
        | MachineTactic::UnknownLocalName
        | MachineTactic::AmbiguousLocalName
        | MachineTactic::InvalidLocalHead
        | MachineTactic::UnknownSimpRule
        | MachineTactic::AmbiguousSimpRule
        | MachineTactic::InvalidSimpRule
        | MachineTactic::AmbiguousApplyArgument
        | MachineTactic::TooManyApplyArguments
        | MachineTactic::TooFewApplyArguments
        | MachineTactic::SubgoalDataArgument => Api::InvalidCandidate,
        MachineTactic::ExpectedFunctionType | MachineTactic::ExpectedPiTarget => {
            Api::ExpectedPiType
        }
        MachineTactic::ExpectedEqTarget | MachineTactic::AmbiguousRewriteRule => {
            Api::RewriteRuleInvalid
        }
        MachineTactic::UniverseArgumentMismatch
        | MachineTactic::TypeMismatch
        | MachineTactic::ProofExprTypeMismatch
            if has_expected_actual(diagnostic) =>
        {
            Api::TypeMismatch
        }
        MachineTactic::UniverseArgumentMismatch | MachineTactic::TypeMismatch => {
            Api::MachineTermElaborationError
        }
        MachineTactic::ProofExprTypeMismatch => Api::InvalidMachineProofState,
        MachineTactic::SimpNoProgress => Api::SimpNoProgress,
        MachineTactic::SimpStepLimitExceeded => Api::BudgetExceeded,
        MachineTactic::UnsupportedMachineTactic | MachineTactic::TacticPrimitiveUnavailable => {
            Api::UnsupportedTactic
        }
        MachineTactic::InvalidInductionTarget => Api::InductionTargetNotNat,
        MachineTactic::GoalLimitExceeded => Api::TooManyGoals,
        MachineTactic::MetaLimitExceeded => Api::BudgetExceeded,
        MachineTactic::TacticFuelExhausted {
            kind: TacticFuelKind::ExprNode,
        } => Api::TooLargeTerm,
        MachineTactic::TacticFuelExhausted { .. } => Api::BudgetExceeded,
        MachineTactic::InvalidCurrentDeclOrder
        | MachineTactic::UncheckedCurrentDecl
        | MachineTactic::CurrentDeclSignatureMismatch => Api::InvalidCheckedCurrentDecl,
        MachineTactic::InvalidVerifiedImport => Api::InvalidVerifiedImport,
        MachineTactic::InvalidTacticOption
        | MachineTactic::UnsupportedTacticOption
        | MachineTactic::InvalidEqFamily
        | MachineTactic::InvalidNatFamily => Api::InvalidMachineApiOptions,
    }
}

pub fn map_frontend_diagnostic_kind(
    diagnostic: &npa_frontend::MachineDiagnostic,
) -> MachineApiErrorKind {
    use npa_frontend::MachineDiagnosticKind as Frontend;
    use MachineApiErrorKind as Api;

    match diagnostic.kind {
        Frontend::ParseError => Api::MachineTermParseError,
        Frontend::UnsupportedSyntax
        | Frontend::UnsupportedItem
        | Frontend::ImportAfterItem
        | Frontend::ImportResolutionError
        | Frontend::MissingVerifiedImport
        | Frontend::DuplicateDeclaration
        | Frontend::DuplicateUniverseParam
        | Frontend::UnknownUniverseParam
        | Frontend::UniverseLevelTooLarge
        | Frontend::UnannotatedBinder
        | Frontend::UnannotatedLet
        | Frontend::HoleNotAllowed
        | Frontend::UnsolvedUniverseMeta
        | Frontend::KernelRejected
        | Frontend::ExpectedSort
        | Frontend::TooManyArguments
        | Frontend::TooFewArguments => Api::MachineTermElaborationError,
        Frontend::UnknownGlobalName
        | Frontend::ShortGlobalName
        | Frontend::AmbiguousGlobalName
        | Frontend::GlobalShadowedByLocal
        | Frontend::UnknownLocalName => Api::UnknownName,
        Frontend::ImplicitArgumentRequired | Frontend::MissingExplicitUniverse => {
            Api::ImplicitArgumentRequired
        }
        Frontend::ExpectedFunctionType => Api::ExpectedPiType,
        Frontend::TypeMismatch if frontend_has_expected_actual(diagnostic) => Api::TypeMismatch,
        Frontend::TypeMismatch => Api::MachineTermElaborationError,
        Frontend::CertificateRejected => Api::VerifyFailed,
    }
}

fn prepass_candidate_terms(
    candidate: &MachineTacticCandidate,
    goal_id: GoalId,
    tactic_kind: MachineApiTacticKind,
) -> MachineTacticAdapterResult<()> {
    match candidate {
        MachineTacticCandidate::Exact { term } => prepass_raw_term(term, goal_id, tactic_kind),
        MachineTacticCandidate::Intro { .. }
        | MachineTacticCandidate::SimpLite { .. }
        | MachineTacticCandidate::Smt { .. }
        | MachineTacticCandidate::InductionNat { .. }
        | MachineTacticCandidate::Constructor(_)
        | MachineTacticCandidate::Revert(_)
        | MachineTacticCandidate::Unfold(_)
        | MachineTacticCandidate::Congr(_)
        | MachineTacticCandidate::Subst(_)
        | MachineTacticCandidate::Contradiction(_)
        | MachineTacticCandidate::FiniteDecide
        | MachineTacticCandidate::Omega
        | MachineTacticCandidate::Ring
        | MachineTacticCandidate::Bitblast => Ok(()),
        MachineTacticCandidate::Apply { args, .. } => {
            for arg in args {
                if let CandidateApplyArg::Term(term) = arg {
                    prepass_raw_term(term, goal_id, tactic_kind)?;
                }
            }
            Ok(())
        }
        MachineTacticCandidate::Rewrite { rule, .. } => {
            prepass_rewrite_rule(rule, goal_id, tactic_kind)
        }
        MachineTacticCandidate::Cases(payload) => {
            if let Some(motive) = &payload.motive {
                prepass_raw_term(motive, goal_id, tactic_kind)?;
            }
            Ok(())
        }
        MachineTacticCandidate::GeneralInduction(payload) => {
            if let Some(motive) = &payload.motive {
                prepass_raw_term(motive, goal_id, tactic_kind)?;
            }
            Ok(())
        }
        MachineTacticCandidate::Refine(payload) => {
            prepass_raw_term(&payload.term, goal_id, tactic_kind)
        }
        MachineTacticCandidate::Have(payload) => {
            prepass_raw_term(&payload.ty, goal_id, tactic_kind)?;
            prepass_local_lemma_proof(&payload.proof, goal_id, tactic_kind)
        }
        MachineTacticCandidate::Suffices(payload) => {
            prepass_raw_term(&payload.target, goal_id, tactic_kind)?;
            prepass_local_lemma_proof(&payload.proof, goal_id, tactic_kind)
        }
        MachineTacticCandidate::Specialize(payload) => {
            for arg in &payload.args {
                if let CandidateApplyArg::Term(term) = arg {
                    prepass_raw_term(term, goal_id, tactic_kind)?;
                }
            }
            Ok(())
        }
        MachineTacticCandidate::Generalize(payload) => {
            prepass_raw_term(&payload.term, goal_id, tactic_kind)
        }
        MachineTacticCandidate::Change(payload) => {
            prepass_raw_term(&payload.replacement, goal_id, tactic_kind)
        }
    }
}

fn prepass_local_lemma_proof(
    proof: &npa_tactic::LocalLemmaProof<RawMachineTerm>,
    goal_id: GoalId,
    tactic_kind: MachineApiTacticKind,
) -> MachineTacticAdapterResult<()> {
    match proof {
        npa_tactic::LocalLemmaProof::ChildGoal => Ok(()),
        npa_tactic::LocalLemmaProof::Term(term) => prepass_raw_term(term, goal_id, tactic_kind),
    }
}

fn prepass_rewrite_rule(
    rule: &CandidateRewriteRuleRef,
    goal_id: GoalId,
    tactic_kind: MachineApiTacticKind,
) -> MachineTacticAdapterResult<()> {
    for arg in &rule.args {
        if let CandidateApplyArg::Term(term) = arg {
            prepass_raw_term(term, goal_id, tactic_kind)?;
        }
    }
    Ok(())
}

fn prepass_raw_term(
    term: &RawMachineTerm,
    goal_id: GoalId,
    tactic_kind: MachineApiTacticKind,
) -> MachineTacticAdapterResult<()> {
    npa_frontend::canonicalize_machine_term_source(&term.source)
        .map(|_| ())
        .map_err(|diagnostic| {
            let phase = frontend_term_phase(&diagnostic);
            Box::new(MachineTacticAdapterError {
                diagnostic: project_frontend_diagnostic(
                    diagnostic,
                    phase,
                    Some(goal_id),
                    Some(tactic_kind),
                ),
                candidate_hash: None,
                deterministic_budget_hash: None,
                cache_key_hash: None,
            })
        })
}

fn machine_tactic_candidate_validation_error(
    diagnostic: MachineTacticDiagnostic,
    goal_id: GoalId,
    tactic_kind: MachineApiTacticKind,
) -> Box<MachineTacticAdapterError> {
    let mut error =
        machine_tactic_error(diagnostic, MachineApiDiagnosticPhase::CandidateValidation);
    error.diagnostic.goal_id = Some(goal_id);
    error.diagnostic.tactic_kind = Some(tactic_kind);
    error
}

fn machine_tactic_error(
    diagnostic: MachineTacticDiagnostic,
    phase: MachineApiDiagnosticPhase,
) -> Box<MachineTacticAdapterError> {
    Box::new(MachineTacticAdapterError {
        diagnostic: project_machine_tactic_diagnostic(diagnostic, phase),
        candidate_hash: None,
        deterministic_budget_hash: None,
        cache_key_hash: None,
    })
}

pub(crate) fn project_machine_tactic_diagnostic(
    diagnostic: MachineTacticDiagnostic,
    phase: MachineApiDiagnosticPhase,
) -> MachineApiDiagnosticProjection {
    let kind = map_machine_tactic_diagnostic_kind(&diagnostic);
    let (expected_hash, actual_hash) = mismatch_hashes_for_api(kind, &diagnostic);
    let goal_id = diagnostic.goal_id;
    let tactic_kind = machine_tactic_kind_for_api(kind, &diagnostic);
    let primary_name = machine_tactic_primary_name_for_api(kind, &diagnostic);
    let source_message = diagnostic.message.to_string();
    MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id,
        tactic_kind,
        primary_name,
        primary_axiom_ref: None,
        expected_hash,
        actual_hash,
        source_message,
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(diagnostic),
    }
}

pub(crate) fn project_frontend_diagnostic(
    diagnostic: npa_frontend::MachineDiagnostic,
    phase: MachineApiDiagnosticPhase,
    goal_id: Option<GoalId>,
    tactic_kind: Option<MachineApiTacticKind>,
) -> MachineApiDiagnosticProjection {
    let kind = map_frontend_diagnostic_kind(&diagnostic);
    let (expected_hash, actual_hash) = frontend_mismatch_hashes_for_api(kind, &diagnostic);
    let source_message = diagnostic.message.clone();
    MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id,
        tactic_kind,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash,
        actual_hash,
        source_message,
        upstream: MachineApiUpstreamDiagnostic::Frontend(diagnostic),
    }
}

fn machine_tactic_start_proof_phase(
    diagnostic: &MachineTacticDiagnostic,
) -> MachineApiDiagnosticPhase {
    match map_machine_tactic_diagnostic_kind(diagnostic) {
        MachineApiErrorKind::MachineTermParseError => MachineApiDiagnosticPhase::MachineTermParse,
        MachineApiErrorKind::MachineTermElaborationError
        | MachineApiErrorKind::UnknownName
        | MachineApiErrorKind::ImplicitArgumentRequired
        | MachineApiErrorKind::TypeMismatch
        | MachineApiErrorKind::ExpectedPiType => MachineApiDiagnosticPhase::MachineTermCheck,
        _ => MachineApiDiagnosticPhase::SessionCreate,
    }
}

fn machine_tactic_run_phase(diagnostic: &MachineTacticDiagnostic) -> MachineApiDiagnosticPhase {
    match diagnostic.kind {
        MachineTacticDiagnosticKind::UnknownGoal
        | MachineTacticDiagnosticKind::GoalAlreadyAssigned => {
            return MachineApiDiagnosticPhase::SnapshotLookup;
        }
        MachineTacticDiagnosticKind::InvalidMachineTermSource => {
            return MachineApiDiagnosticPhase::CandidateValidation;
        }
        _ => {}
    }

    match map_machine_tactic_diagnostic_kind(diagnostic) {
        MachineApiErrorKind::InvalidCandidate => MachineApiDiagnosticPhase::CandidateValidation,
        MachineApiErrorKind::MachineTermParseError => MachineApiDiagnosticPhase::MachineTermParse,
        MachineApiErrorKind::MachineTermElaborationError
        | MachineApiErrorKind::UnknownName
        | MachineApiErrorKind::ImplicitArgumentRequired
        | MachineApiErrorKind::TypeMismatch
        | MachineApiErrorKind::ExpectedPiType => MachineApiDiagnosticPhase::MachineTermCheck,
        _ => MachineApiDiagnosticPhase::TacticExecution,
    }
}

fn tactic_run_correlation_hashes_allowed(diagnostic: &MachineTacticDiagnostic) -> bool {
    !matches!(
        diagnostic.kind,
        MachineTacticDiagnosticKind::UnknownGoal
            | MachineTacticDiagnosticKind::GoalAlreadyAssigned
            | MachineTacticDiagnosticKind::InvalidMachineTermSource
    )
}

fn machine_tactic_kind_for_api(
    kind: MachineApiErrorKind,
    diagnostic: &MachineTacticDiagnostic,
) -> Option<MachineApiTacticKind> {
    if kind == MachineApiErrorKind::GoalNotOpen {
        return None;
    }

    diagnostic
        .tactic_kind
        .as_deref()
        .and_then(MachineApiTacticKind::from_machine_tactic_kind)
}

fn machine_tactic_primary_name_for_api(
    kind: MachineApiErrorKind,
    diagnostic: &MachineTacticDiagnostic,
) -> Option<Name> {
    if !matches!(
        kind,
        MachineApiErrorKind::InvalidCandidate
            | MachineApiErrorKind::InvalidMachineApiOptions
            | MachineApiErrorKind::MachineTermElaborationError
            | MachineApiErrorKind::UnknownName
            | MachineApiErrorKind::ImplicitArgumentRequired
            | MachineApiErrorKind::RewriteRuleInvalid
    ) {
        return None;
    }

    diagnostic
        .primary_name
        .as_deref()
        .filter(|name| is_fully_qualified_name(name))
        .cloned()
}

fn frontend_term_phase(diagnostic: &npa_frontend::MachineDiagnostic) -> MachineApiDiagnosticPhase {
    if map_frontend_diagnostic_kind(diagnostic) == MachineApiErrorKind::MachineTermParseError {
        MachineApiDiagnosticPhase::MachineTermParse
    } else {
        MachineApiDiagnosticPhase::MachineTermCheck
    }
}

fn mismatch_hashes_for_api(
    kind: MachineApiErrorKind,
    diagnostic: &MachineTacticDiagnostic,
) -> (Option<Hash>, Option<Hash>) {
    if kind == MachineApiErrorKind::TypeMismatch && has_expected_actual(diagnostic) {
        (
            diagnostic.expected_hash.as_deref().copied(),
            diagnostic.actual_hash.as_deref().copied(),
        )
    } else {
        (None, None)
    }
}

fn frontend_mismatch_hashes_for_api(
    kind: MachineApiErrorKind,
    diagnostic: &npa_frontend::MachineDiagnostic,
) -> (Option<Hash>, Option<Hash>) {
    let payload = diagnostic.payload.as_deref();
    if kind == MachineApiErrorKind::TypeMismatch {
        (
            payload.and_then(|payload| payload.expected_hash),
            payload.and_then(|payload| payload.actual_hash),
        )
    } else {
        (None, None)
    }
}

fn has_expected_actual(diagnostic: &MachineTacticDiagnostic) -> bool {
    diagnostic.expected_hash.is_some() && diagnostic.actual_hash.is_some()
}

fn frontend_has_expected_actual(diagnostic: &npa_frontend::MachineDiagnostic) -> bool {
    diagnostic
        .payload
        .as_ref()
        .is_some_and(|payload| payload.expected_hash.is_some() && payload.actual_hash.is_some())
}

fn is_fully_qualified_name(name: &Name) -> bool {
    name.is_canonical()
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_kernel::{Expr, Level};
    use npa_tactic::RawMachineTerm;

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn trivial_spec(theorem_type: Expr) -> MachineProofSpec {
        MachineProofSpec {
            module: Name::from_dotted("Test"),
            theorem_name: Name::from_dotted("Test.thm"),
            source_index: 0,
            universe_params: Vec::new(),
            theorem_type,
        }
    }

    fn start_state(theorem_type: Expr) -> MachineProofState {
        machine_tactic_start_machine_proof(
            trivial_spec(theorem_type),
            Vec::new(),
            Vec::new(),
            MachineTacticOptions::default(),
        )
        .unwrap()
        .state
    }

    #[test]
    fn validates_candidate_and_returns_machine_tactic_candidate_hash() {
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("Prop"),
        };

        let validated =
            machine_tactic_validate_machine_tactic_candidate(GoalId(0), candidate).unwrap();

        assert_eq!(validated.goal_id, GoalId(0));
        assert_eq!(validated.tactic_kind, MachineApiTacticKind::Exact);
        assert_eq!(
            validated.candidate_hash,
            machine_tactic_hash(&validated.tactic)
        );
    }

    #[test]
    fn raw_machine_term_prepass_failure_has_no_candidate_hash() {
        let candidate = MachineTacticCandidate::Exact {
            term: RawMachineTerm::new("("),
        };

        let err =
            machine_tactic_validate_machine_tactic_candidate(GoalId(7), candidate).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::MachineTermParseError
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermParse
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(7)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Exact)
        );
        assert_eq!(err.candidate_hash, None);
        assert_eq!(err.deterministic_budget_hash, None);
    }

    #[test]
    fn start_proof_theorem_type_check_error_uses_machine_term_check_phase() {
        let spec = MachineProofSpec {
            theorem_type: Expr::lam("x", type0(), Expr::bvar(0)),
            ..trivial_spec(type0())
        };

        let err = machine_tactic_start_machine_proof(
            spec,
            Vec::new(),
            Vec::new(),
            MachineTacticOptions::default(),
        )
        .unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::MachineTermElaborationError
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_eq!(err.diagnostic.goal_id, None);
        assert_eq!(err.diagnostic.tactic_kind, None);
        assert_eq!(err.candidate_hash, None);
        assert_eq!(err.deterministic_budget_hash, None);
    }

    #[test]
    fn start_proof_theorem_type_expected_pi_uses_machine_term_check_phase() {
        let spec = MachineProofSpec {
            theorem_type: Expr::app(prop(), prop()),
            ..trivial_spec(type0())
        };

        let err = machine_tactic_start_machine_proof(
            spec,
            Vec::new(),
            Vec::new(),
            MachineTacticOptions::default(),
        )
        .unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::ExpectedPiType);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_eq!(err.diagnostic.goal_id, None);
        assert_eq!(err.diagnostic.tactic_kind, None);
        assert_eq!(err.diagnostic.expected_hash, None);
        assert_eq!(err.diagnostic.actual_hash, None);
    }

    #[test]
    fn start_proof_theorem_type_type_mismatch_keeps_hashes() {
        let spec = MachineProofSpec {
            theorem_type: Expr::let_in("x", prop(), type0(), Expr::bvar(0)),
            ..trivial_spec(type0())
        };

        let err = machine_tactic_start_machine_proof(
            spec,
            Vec::new(),
            Vec::new(),
            MachineTacticOptions::default(),
        )
        .unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::TypeMismatch);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_eq!(err.diagnostic.goal_id, None);
        assert_eq!(err.diagnostic.tactic_kind, None);
        assert!(err.diagnostic.expected_hash.is_some());
        assert!(err.diagnostic.actual_hash.is_some());
    }

    #[test]
    fn run_error_maps_machine_tactic_type_mismatch_with_correlation_hashes() {
        let state = start_state(prop());
        let validated = machine_tactic_validate_machine_tactic_candidate(
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Type"),
            },
        )
        .unwrap();
        let budget = TacticBudget::default();

        let err = machine_tactic_run_machine_tactic_with_budget(&state, validated.tactic, budget)
            .unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::TypeMismatch);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::MachineTermCheck
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(0)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Exact)
        );
        assert_eq!(err.candidate_hash, Some(validated.candidate_hash));
        assert_eq!(
            err.deterministic_budget_hash,
            Some(tactic_budget_hash(budget))
        );
        assert!(err.cache_key_hash.is_some());
        assert!(err.diagnostic.expected_hash.is_some());
        assert!(err.diagnostic.actual_hash.is_some());
    }

    #[test]
    fn run_goal_not_open_maps_to_snapshot_lookup_without_tactic_correlation() {
        let state = start_state(type0());
        let validated = machine_tactic_validate_machine_tactic_candidate(
            GoalId(99),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
        )
        .unwrap();

        let err = machine_tactic_run_machine_tactic(&state, validated.tactic).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::GoalNotOpen);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(99)));
        assert_eq!(err.diagnostic.tactic_kind, None);
        assert_eq!(err.candidate_hash, None);
        assert_eq!(err.deterministic_budget_hash, None);
        assert_eq!(err.cache_key_hash, None);
    }

    #[test]
    fn unsupported_bitblast_precedes_goal_lookup_in_state_taking_adapter() {
        let state = start_state(type0());
        let tactic = MachineTactic::Bitblast {
            goal_id: GoalId(99),
        };

        let err = machine_tactic_run_machine_tactic(&state, tactic).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::UnsupportedTactic);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::TacticExecution
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(99)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Bitblast)
        );
        assert!(err.candidate_hash.is_some());
        assert_eq!(
            err.deterministic_budget_hash,
            Some(tactic_budget_hash(TacticBudget::default()))
        );
        assert!(err.cache_key_hash.is_some());
    }

    #[test]
    fn run_stale_snapshot_maps_to_snapshot_lookup_without_correlation_hashes() {
        let mut state = start_state(type0());
        let validated = machine_tactic_validate_machine_tactic_candidate(
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
        )
        .unwrap();
        state.state_id = "stale".to_owned();

        let err = machine_tactic_run_machine_tactic(&state, validated.tactic.clone()).unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidMachineProofState
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
        assert_eq!(err.diagnostic.goal_id, None);
        assert_eq!(err.diagnostic.tactic_kind, None);
        assert_eq!(err.candidate_hash, None);
        assert_eq!(err.deterministic_budget_hash, None);
        assert_eq!(err.cache_key_hash, None);

        let result_err = machine_tactic_machine_tactic_result_error(
            &state,
            validated.tactic,
            TacticBudget::default(),
        )
        .unwrap();
        assert_eq!(
            result_err.diagnostic.kind,
            MachineApiErrorKind::InvalidMachineProofState
        );
        assert_eq!(
            result_err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
        assert_eq!(result_err.diagnostic.goal_id, None);
        assert_eq!(result_err.diagnostic.tactic_kind, None);
        assert_eq!(result_err.candidate_hash, None);
        assert_eq!(result_err.deterministic_budget_hash, None);
        assert_eq!(result_err.cache_key_hash, None);
    }

    #[test]
    fn run_intro_name_collision_is_post_canonical_candidate_error() {
        let state = start_state(Expr::pi("p", prop(), Expr::pi("q", prop(), prop())));
        let intro_p = machine_tactic_validate_machine_tactic_candidate(
            GoalId(0),
            MachineTacticCandidate::Intro {
                name: "p".to_owned(),
            },
        )
        .unwrap();
        let run = machine_tactic_run_machine_tactic(&state, intro_p.tactic).unwrap();
        let duplicate = machine_tactic_validate_machine_tactic_candidate(
            GoalId(1),
            MachineTacticCandidate::Intro {
                name: "p".to_owned(),
            },
        )
        .unwrap();

        let err = machine_tactic_run_machine_tactic(&run.state, duplicate.tactic).unwrap_err();

        assert_eq!(err.diagnostic.kind, MachineApiErrorKind::InvalidCandidate);
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::CandidateValidation
        );
        assert_eq!(err.diagnostic.goal_id, Some(GoalId(1)));
        assert_eq!(
            err.diagnostic.tactic_kind,
            Some(MachineApiTacticKind::Intro)
        );
        assert_eq!(err.candidate_hash, Some(duplicate.candidate_hash));
        assert_eq!(
            err.deterministic_budget_hash,
            Some(tactic_budget_hash(TacticBudget::default()))
        );
        assert!(err.cache_key_hash.is_some());
    }

    #[test]
    fn extract_closed_theorem_maps_open_goal_to_caller_phase() {
        let state = start_state(type0());

        let err = machine_tactic_extract_closed_machine_theorem_decl(
            &state,
            MachineApiDiagnosticPhase::SnapshotLookup,
        )
        .unwrap_err();

        assert_eq!(
            err.diagnostic.kind,
            MachineApiErrorKind::InvalidMachineProofState
        );
        assert_eq!(
            err.diagnostic.phase,
            MachineApiDiagnosticPhase::SnapshotLookup
        );
    }

    #[test]
    fn extract_closed_theorem_succeeds_after_exact() {
        let state = start_state(type0());
        let validated = machine_tactic_validate_machine_tactic_candidate(
            GoalId(0),
            MachineTacticCandidate::Exact {
                term: RawMachineTerm::new("Prop"),
            },
        )
        .unwrap();
        let run = machine_tactic_run_machine_tactic(&state, validated.tactic).unwrap();

        assert_eq!(run.next_state_fingerprint, run.state.fingerprint);
        assert_eq!(run.proof_delta_hash, run.delta.delta_hash);

        let closed = run.state;

        let extracted = machine_tactic_extract_closed_machine_theorem_decl(
            &closed,
            MachineApiDiagnosticPhase::KernelCheck,
        )
        .unwrap();

        assert_eq!(
            extracted.theorem,
            Decl::Theorem {
                name: "Test.thm".to_owned(),
                universe_params: Vec::new(),
                ty: type0(),
                proof: prop(),
            }
        );
    }

    #[test]
    fn machine_tactic_mapping_is_exhaustive_for_current_tactic_diagnostics() {
        let diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::TacticFuelExhausted {
                kind: TacticFuelKind::ExprNode,
            },
            "expr nodes exhausted",
        );

        assert_eq!(
            map_machine_tactic_diagnostic_kind(&diagnostic),
            MachineApiErrorKind::TooLargeTerm
        );
    }

    #[test]
    fn frontend_universe_level_too_large_is_mapped() {
        let diagnostic = npa_frontend::MachineDiagnostic::error(
            npa_frontend::MachineDiagnosticKind::UniverseLevelTooLarge,
            npa_frontend::Span::new(npa_frontend::FileId(0), 0, 1),
            "universe too large",
        );

        assert_eq!(
            map_frontend_diagnostic_kind(&diagnostic),
            MachineApiErrorKind::MachineTermElaborationError
        );
    }

    #[test]
    fn frontend_machine_diagnostic_payload_shape_is_unchanged_by_human_payloads() {
        let diagnostic = npa_frontend::MachineDiagnostic::parse(
            npa_frontend::Span::new(npa_frontend::FileId(0), 0, 1),
            "expected Machine Surface term",
        );

        assert_eq!(diagnostic.payload, None);
        assert_eq!(
            map_frontend_diagnostic_kind(&diagnostic),
            MachineApiErrorKind::MachineTermParseError
        );
    }

    #[test]
    fn single_component_primary_name_is_preserved() {
        let mut diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::MachineTermElaborationError,
            "elaboration failed",
        );
        diagnostic.primary_name = Some(Box::new(Name::from_dotted("Eq")));

        let projected = project_machine_tactic_diagnostic(
            diagnostic,
            MachineApiDiagnosticPhase::MachineTermCheck,
        );

        assert_eq!(projected.primary_name, Some(Name::from_dotted("Eq")));
    }

    #[test]
    fn noncanonical_primary_name_is_omitted() {
        let mut diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::MachineTermElaborationError,
            "elaboration failed",
        );
        diagnostic.primary_name = Some(Box::new(Name::from_dotted("Bad..Name")));

        let projected = project_machine_tactic_diagnostic(
            diagnostic,
            MachineApiDiagnosticPhase::MachineTermCheck,
        );

        assert_eq!(projected.primary_name, None);
    }

    #[test]
    fn proof_expr_type_mismatch_without_hashes_stays_proof_state_error() {
        let diagnostic = MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::ProofExprTypeMismatch,
            "proof expression mismatch",
        );

        assert_eq!(
            map_machine_tactic_diagnostic_kind(&diagnostic),
            MachineApiErrorKind::InvalidMachineProofState
        );
    }
}
