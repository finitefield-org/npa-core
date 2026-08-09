use crate::Span;

pub type HumanResult<T> = std::result::Result<T, HumanDiagnostic>;

/// Frontend-owned projection of one fuel-owning kernel operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelFuelOperationCounters {
    pub budget: u64,
    pub spent: u64,
    pub remaining: u64,
    pub exhausted: bool,
    pub overflowed: bool,
}

/// Frontend-owned declaration aggregate for one kernel fuel domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelFuelDomainTotals {
    pub calls: u64,
    pub logical_spent: u64,
    pub successful_operation_fuel: u64,
    pub exhausted_operation_fuel: u64,
    pub overflowed: bool,
}

/// Domain-separated declaration fuel totals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelFuelTotals {
    pub whnf: HumanKernelFuelDomainTotals,
    pub conversion: HumanKernelFuelDomainTotals,
}

/// Strict bounded work vocabulary copied from one kernel snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelWorkSnapshot {
    pub check_calls: u64,
    pub infer_calls: u64,
    pub whnf_calls: u64,
    pub defeq_calls: u64,
    pub quick_equality_hits: u64,
    pub beta_steps: u64,
    pub delta_steps: u64,
    pub iota_steps: u64,
    pub zeta_steps: u64,
    pub physical_reductions: u64,
    pub overflowed: bool,
}

/// Failed-operation fuel and work projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelOperationWork {
    pub fuel: HumanKernelFuelOperationCounters,
    pub work: HumanKernelWorkSnapshot,
}

/// Declaration-scope fuel and work projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelDeclarationWork {
    pub fuel: HumanKernelFuelTotals,
    pub work: HumanKernelWorkSnapshot,
    pub overflowed: bool,
}

/// Bounded structural comparison path with stable kernel spellings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelComparisonPath {
    pub steps: Vec<String>,
    pub truncated: bool,
}

/// One bounded retained delta-constant count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelDeltaHotsetEntry {
    pub constant: String,
    pub count: u64,
}

/// Bounded retained delta-constant projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelDeltaHotsetSummary {
    pub retained_names: u64,
    pub capacity: u64,
    pub entries: Vec<HumanKernelDeltaHotsetEntry>,
    pub emitted: u64,
    pub entry_limit: u64,
    pub unretained_name_observations: u64,
    pub overlong_name_observations: u64,
    pub output_truncated: bool,
    pub overflowed: bool,
}

/// Bounded, untrusted operational context for one kernel fuel exhaustion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelFuelDiagnostic {
    pub subsystem: String,
    pub resource: String,
    pub failed_operation: HumanKernelOperationWork,
    pub declaration: HumanKernelDeclarationWork,
    pub comparison_path: HumanKernelComparisonPath,
    pub retained_delta_constants: Option<HumanKernelDeltaHotsetSummary>,
    pub overflowed: bool,
}

impl HumanKernelFuelDiagnostic {
    pub fn from_kernel(diagnostic: &npa_kernel::KernelFuelDiagnostic) -> Self {
        Self {
            subsystem: diagnostic.subsystem.as_str().to_owned(),
            resource: diagnostic.resource.as_str().to_owned(),
            failed_operation: HumanKernelOperationWork::from_kernel(&diagnostic.failed_operation),
            declaration: HumanKernelDeclarationWork::from_kernel(&diagnostic.declaration),
            comparison_path: HumanKernelComparisonPath {
                steps: diagnostic
                    .comparison_path
                    .steps
                    .iter()
                    .map(|step| step.as_str().to_owned())
                    .collect(),
                truncated: diagnostic.comparison_path.truncated,
            },
            retained_delta_constants: diagnostic
                .retained_delta_constants
                .as_ref()
                .map(HumanKernelDeltaHotsetSummary::from_kernel),
            overflowed: diagnostic.overflowed,
        }
    }
}

/// Successful detailed declaration summary used by package observation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanKernelDeclarationSummary {
    pub subsystem: String,
    pub outcome: String,
    pub fuel: HumanKernelFuelTotals,
    pub work: HumanKernelWorkSnapshot,
    pub retained_delta_constants: HumanKernelDeltaHotsetSummary,
    pub overflowed: bool,
}

impl HumanKernelDeclarationSummary {
    pub fn from_admission(admission: &npa_kernel::KernelDiagnosedAdmission) -> Option<Self> {
        let declaration = admission.declaration_work()?;
        let retained_delta_constants =
            HumanKernelDeltaHotsetSummary::from_kernel(admission.retained_delta_constants()?);
        Some(Self {
            subsystem: npa_kernel::KernelDiagnosticSubsystem::FastKernel
                .as_str()
                .to_owned(),
            outcome: "accepted".to_owned(),
            fuel: HumanKernelFuelTotals::from_kernel(&declaration.fuel),
            work: HumanKernelWorkSnapshot::from_kernel(&declaration.work),
            overflowed: declaration.overflowed || retained_delta_constants.overflowed,
            retained_delta_constants,
        })
    }
}

impl HumanKernelFuelOperationCounters {
    fn from_kernel(counters: &npa_kernel::KernelFuelOperationCounters) -> Self {
        Self {
            budget: counters.budget,
            spent: counters.spent,
            remaining: counters.remaining,
            exhausted: counters.exhausted,
            overflowed: counters.overflowed,
        }
    }
}

impl HumanKernelFuelDomainTotals {
    fn from_kernel(counters: &npa_kernel::KernelFuelDomainTotals) -> Self {
        Self {
            calls: counters.calls,
            logical_spent: counters.logical_spent,
            successful_operation_fuel: counters.successful_operation_fuel,
            exhausted_operation_fuel: counters.exhausted_operation_fuel,
            overflowed: counters.overflowed,
        }
    }
}

impl HumanKernelFuelTotals {
    fn from_kernel(counters: &npa_kernel::KernelFuelTotals) -> Self {
        Self {
            whnf: HumanKernelFuelDomainTotals::from_kernel(&counters.whnf),
            conversion: HumanKernelFuelDomainTotals::from_kernel(&counters.conversion),
        }
    }
}

impl HumanKernelWorkSnapshot {
    fn from_kernel(work: &npa_kernel::KernelWorkSnapshot) -> Self {
        Self {
            check_calls: work.check_calls,
            infer_calls: work.infer_calls,
            whnf_calls: work.whnf_calls,
            defeq_calls: work.defeq_calls,
            quick_equality_hits: work.quick_equality_hits,
            beta_steps: work.beta_steps,
            delta_steps: work.delta_steps,
            iota_steps: work.iota_steps,
            zeta_steps: work.zeta_steps,
            physical_reductions: work.physical_reductions,
            overflowed: work.overflowed,
        }
    }
}

impl HumanKernelOperationWork {
    fn from_kernel(work: &npa_kernel::KernelOperationWork) -> Self {
        Self {
            fuel: HumanKernelFuelOperationCounters::from_kernel(&work.fuel),
            work: HumanKernelWorkSnapshot::from_kernel(&work.work),
        }
    }
}

impl HumanKernelDeclarationWork {
    fn from_kernel(work: &npa_kernel::KernelDeclarationWork) -> Self {
        Self {
            fuel: HumanKernelFuelTotals::from_kernel(&work.fuel),
            work: HumanKernelWorkSnapshot::from_kernel(&work.work),
            overflowed: work.overflowed,
        }
    }
}

impl HumanKernelDeltaHotsetSummary {
    fn from_kernel(summary: &npa_kernel::KernelDeltaHotsetSummary) -> Self {
        Self {
            retained_names: summary.retained_names,
            capacity: summary.capacity,
            entries: summary
                .entries
                .iter()
                .map(|entry| HumanKernelDeltaHotsetEntry {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDiagnosticSeverity {
    Error,
    Warning,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDiagnosticKind {
    NotImplemented,
    ParseError,
    OpaqueModifierNotFollowedByDef,
    DuplicateOpaqueModifier,
    UnsupportedOpaqueEquationDefinition,
    UnsupportedOpaqueDefinition,
    ImportAfterItem,
    UnsupportedSyntax,
    ImportResolutionError,
    MissingVerifiedImport,
    NamespaceMismatch,
    UnknownNamespace,
    DuplicateDeclaration,
    UnknownIdentifier,
    AmbiguousName,
    AmbiguousConstructor,
    ForwardReference,
    NotationConflict,
    AmbiguousNotation,
    TooManyNotationCandidates,
    TypeclassNoSolution,
    TypeclassAmbiguous,
    TypeclassBudgetExceeded,
    UnsupportedTactic,
    UnsupportedEquationGuard,
    UnsupportedViewPattern,
    EquationCompilerDisabled,
    NonExhaustivePatterns,
    RedundantEquation,
    ImpossibleBranchNotProvable,
    RecursiveCallNotDecreasing,
    MutualCycleWithoutDecrease,
    TerminationMeasureNotNat,
    MeasureDecreaseProofMissing,
    UnsolvedImplicit,
    UnsolvedMeta,
    UnsolvedUniverseMeta,
    UnsolvedHole,
    NamedHoleContextMismatch,
    OccursCheckFailed,
    ExpectedFunctionType,
    ExpectedSort,
    TypeMismatch,
    NoGoalsButTacticRemaining,
    UnresolvedGoal,
    KernelRejected,
    MachineElaborationError,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HumanDiagnosticPhase {
    Parser,
    Resolver,
    Elaborator,
    TacticParse,
    TacticValidation,
    TacticExecution,
    TacticUnresolvedGoal,
    KernelHandoff,
    CertificateHandoff,
}

impl HumanDiagnosticPhase {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Parser => "parser",
            Self::Resolver => "resolver",
            Self::Elaborator => "elaborator",
            Self::TacticParse => "tactic_parse",
            Self::TacticValidation => "tactic_validation",
            Self::TacticExecution => "tactic_execution",
            Self::TacticUnresolvedGoal => "tactic_unresolved_goal",
            Self::KernelHandoff => "kernel_handoff",
            Self::CertificateHandoff => "certificate_handoff",
        }
    }
}

#[non_exhaustive]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanDiagnosticPayload {
    pub phase: Option<HumanDiagnosticPhase>,
    pub detail: Option<String>,
    pub candidates: Vec<String>,
    /// Stable declaration names related to a conversion or elaboration failure.
    pub related_declarations: Vec<String>,
    pub hole_goals: Vec<HumanHoleGoal>,
    pub unsolved_meta: Option<HumanUnsolvedMeta>,
    pub conversion: Option<HumanDiagnosticConversionContext>,
    pub universe_mismatch: Option<HumanUniverseMismatchContext>,
    pub kernel_fuel: Option<HumanKernelFuelDiagnostic>,
}

impl HumanDiagnosticPayload {
    #[must_use]
    pub fn with_candidates(mut self, candidates: Vec<String>) -> Self {
        self.candidates = candidates;
        self
    }

    #[must_use]
    pub fn with_hole_goals(mut self, hole_goals: Vec<HumanHoleGoal>) -> Self {
        self.hole_goals = hole_goals;
        self
    }

    #[must_use]
    pub fn with_conversion(mut self, conversion: HumanDiagnosticConversionContext) -> Self {
        self.conversion = Some(conversion);
        self
    }

    #[must_use]
    pub fn with_universe_mismatch(mut self, mismatch: HumanUniverseMismatchContext) -> Self {
        self.universe_mismatch = Some(mismatch);
        self
    }

    #[must_use]
    pub fn with_kernel_fuel(mut self, kernel_fuel: HumanKernelFuelDiagnostic) -> Self {
        self.kernel_fuel = Some(kernel_fuel);
        self
    }
}

/// Bounded universe-level context for a kernel-rejected Human declaration.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanUniverseMismatchContext {
    declaration_name: String,
    type_path: String,
    declared_level: String,
    inferred_level: String,
    universe_params: Vec<String>,
}

impl HumanUniverseMismatchContext {
    pub fn new(
        declaration_name: impl Into<String>,
        type_path: impl Into<String>,
        declared_level: impl Into<String>,
        inferred_level: impl Into<String>,
        universe_params: Vec<String>,
    ) -> Option<Self> {
        let declaration_name = declaration_name.into();
        let type_path = type_path.into();
        let declared_level = declared_level.into();
        let inferred_level = inferred_level.into();
        if declaration_name.is_empty()
            || type_path.is_empty()
            || declared_level.is_empty()
            || inferred_level.is_empty()
        {
            return None;
        }
        Some(Self {
            declaration_name,
            type_path,
            declared_level,
            inferred_level,
            universe_params,
        })
    }

    pub fn declaration_name(&self) -> &str {
        &self.declaration_name
    }

    pub fn type_path(&self) -> &str {
        &self.type_path
    }

    pub fn declared_level(&self) -> &str {
        &self.declared_level
    }

    pub fn inferred_level(&self) -> &str {
        &self.inferred_level
    }

    pub fn universe_params(&self) -> &[String] {
        &self.universe_params
    }
}

/// Bounded kernel conversion context projected into a Human diagnostic.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDiagnosticConversionContext {
    phase: String,
    outcome: String,
    lhs_head: String,
    rhs_head: String,
    depth: u32,
}

impl HumanDiagnosticConversionContext {
    /// Build a bounded conversion projection when every stable field is nonempty.
    pub fn new(
        phase: impl Into<String>,
        outcome: impl Into<String>,
        lhs_head: impl Into<String>,
        rhs_head: impl Into<String>,
        depth: u32,
    ) -> Option<Self> {
        let phase = phase.into();
        let outcome = outcome.into();
        let lhs_head = lhs_head.into();
        let rhs_head = rhs_head.into();
        if phase.is_empty() || outcome.is_empty() || lhs_head.is_empty() || rhs_head.is_empty() {
            return None;
        }
        Some(Self {
            phase,
            outcome,
            lhs_head,
            rhs_head,
            depth,
        })
    }

    pub fn phase(&self) -> &str {
        &self.phase
    }

    pub fn outcome(&self) -> &str {
        &self.outcome
    }

    pub fn lhs_head(&self) -> &str {
        &self.lhs_head
    }

    pub fn rhs_head(&self) -> &str {
        &self.rhs_head
    }

    pub const fn depth(&self) -> u32 {
        self.depth
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanHoleGoal {
    pub hole: Option<String>,
    pub context: Vec<HumanHoleGoalLocal>,
    pub target: Option<String>,
    pub source_span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanHoleGoalLocal {
    pub name: String,
    pub ty: String,
    pub value: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanUnsolvedMeta {
    pub kind: HumanUnsolvedMetaKind,
    pub name: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanUnsolvedMetaKind {
    Hole,
    SyntheticImplicit,
    Universe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDiagnostic {
    pub kind: HumanDiagnosticKind,
    pub severity: HumanDiagnosticSeverity,
    pub primary_span: Span,
    pub message: String,
    pub payload: Option<Box<HumanDiagnosticPayload>>,
}

impl HumanDiagnostic {
    pub fn error(
        kind: HumanDiagnosticKind,
        primary_span: Span,
        message: impl Into<String>,
    ) -> Self {
        let payload = HumanDiagnosticPayload {
            detail: Some(message.into()),
            ..HumanDiagnosticPayload::default()
        };
        let message = render_human_diagnostic_message(&kind, &payload);
        Self {
            kind,
            severity: HumanDiagnosticSeverity::Error,
            primary_span,
            message,
            payload: Some(Box::new(payload)),
        }
    }

    pub fn not_implemented(primary_span: Span, operation: &str) -> Self {
        Self::error(
            HumanDiagnosticKind::NotImplemented,
            primary_span,
            format!("{operation} is reserved for the Human frontend frontend"),
        )
    }

    pub fn parse(primary_span: Span, message: impl Into<String>) -> Self {
        Self::error(HumanDiagnosticKind::ParseError, primary_span, message)
    }

    pub fn opaque_modifier_not_followed_by_def(
        primary_span: Span,
        following: impl Into<String>,
    ) -> Self {
        Self::error(
            HumanDiagnosticKind::OpaqueModifierNotFollowedByDef,
            primary_span,
            format!("`opaque` may only modify `def`; found {}", following.into()),
        )
    }

    pub fn duplicate_opaque_modifier(primary_span: Span) -> Self {
        Self::error(
            HumanDiagnosticKind::DuplicateOpaqueModifier,
            primary_span,
            "duplicate `opaque` modifier before `def`",
        )
    }

    pub fn unsupported_opaque_equation_definition(primary_span: Span) -> Self {
        Self::error(
            HumanDiagnosticKind::UnsupportedOpaqueEquationDefinition,
            primary_span,
            "opaque equation definitions require equation-compiler integration; use a term-bodied `opaque def ... := ...`, or keep the recursive definition reducible in a narrow implementation module",
        )
    }

    pub fn unsupported_opaque_definition(primary_span: Span) -> Self {
        Self::error(
            HumanDiagnosticKind::UnsupportedOpaqueDefinition,
            primary_span,
            "opaque definitions are parsed but not yet supported by Human Surface compilation",
        )
    }

    pub fn unsupported_syntax(primary_span: Span, syntax: impl Into<String>) -> Self {
        Self::error(
            HumanDiagnosticKind::UnsupportedSyntax,
            primary_span,
            format!("unsupported Human Surface syntax: {}", syntax.into()),
        )
    }

    pub fn unsupported_tactic(primary_span: Span, tactic: impl Into<String>) -> Self {
        Self::error(
            HumanDiagnosticKind::UnsupportedTactic,
            primary_span,
            format!("unsupported Human tactic syntax: {}", tactic.into()),
        )
    }

    pub fn unsupported_equation_guard(primary_span: Span) -> Self {
        Self::error(
            HumanDiagnosticKind::UnsupportedEquationGuard,
            primary_span,
            "guards are not supported in Human equation definitions",
        )
    }

    pub fn unsupported_view_pattern(primary_span: Span) -> Self {
        Self::error(
            HumanDiagnosticKind::UnsupportedViewPattern,
            primary_span,
            "view patterns are not supported in Human equation definitions",
        )
    }

    pub fn with_payload(mut self, payload: HumanDiagnosticPayload) -> Self {
        let existing = self.payload.take().map(|payload| *payload).or_else(|| {
            if self.message.is_empty() {
                None
            } else {
                Some(HumanDiagnosticPayload {
                    detail: Some(self.message.clone()),
                    ..HumanDiagnosticPayload::default()
                })
            }
        });
        let payload = merge_human_diagnostic_payload(existing, payload);
        self.message = render_human_diagnostic_message(&self.kind, &payload);
        self.payload = Some(Box::new(payload));
        self
    }

    pub fn with_phase(self, phase: HumanDiagnosticPhase) -> Self {
        self.with_payload(HumanDiagnosticPayload {
            phase: Some(phase),
            ..HumanDiagnosticPayload::default()
        })
    }

    pub fn with_default_phase(mut self, phase: HumanDiagnosticPhase) -> Self {
        let current_phase = self.payload.as_ref().and_then(|payload| payload.phase);
        if current_phase.is_none() {
            self = self.with_phase(phase);
        }
        self
    }
}

fn merge_human_diagnostic_payload(
    existing: Option<HumanDiagnosticPayload>,
    mut next: HumanDiagnosticPayload,
) -> HumanDiagnosticPayload {
    let Some(existing) = existing else {
        return next;
    };

    if next.phase.is_none() {
        next.phase = existing.phase;
    }
    if next.detail.is_none() {
        next.detail = existing.detail;
    }
    if next.candidates.is_empty() {
        next.candidates = existing.candidates;
    }
    if next.hole_goals.is_empty() {
        next.hole_goals = existing.hole_goals;
    }
    if next.unsolved_meta.is_none() {
        next.unsolved_meta = existing.unsolved_meta;
    }
    if next.conversion.is_none() {
        next.conversion = existing.conversion;
    }
    if next.universe_mismatch.is_none() {
        next.universe_mismatch = existing.universe_mismatch;
    }
    if next.kernel_fuel.is_none() {
        next.kernel_fuel = existing.kernel_fuel;
    }
    next
}

fn render_human_diagnostic_message(
    kind: &HumanDiagnosticKind,
    payload: &HumanDiagnosticPayload,
) -> String {
    let mut lines = Vec::new();
    lines.push(
        payload
            .detail
            .clone()
            .unwrap_or_else(|| human_diagnostic_kind_label(kind).to_owned()),
    );

    if !payload.candidates.is_empty() {
        lines.push("candidates:".to_owned());
        lines.extend(
            payload
                .candidates
                .iter()
                .map(|candidate| format!("  {candidate}")),
        );
    }

    for goal in &payload.hole_goals {
        let heading = goal
            .hole
            .as_deref()
            .map(|hole| format!("hole goal {hole}:"))
            .unwrap_or_else(|| "hole goal:".to_owned());
        lines.push(heading);
        if !goal.context.is_empty() {
            lines.push("context:".to_owned());
            for local in &goal.context {
                match &local.value {
                    Some(value) => {
                        lines.push(format!("  {} : {} := {}", local.name, local.ty, value))
                    }
                    None => lines.push(format!("  {} : {}", local.name, local.ty)),
                }
            }
        }
        if let Some(target) = &goal.target {
            lines.push(format!("target: {target}"));
        }
    }

    lines.join("\n")
}

fn human_diagnostic_kind_label(kind: &HumanDiagnosticKind) -> &'static str {
    match kind {
        HumanDiagnosticKind::NotImplemented => "not implemented",
        HumanDiagnosticKind::ParseError => "parse error",
        HumanDiagnosticKind::OpaqueModifierNotFollowedByDef => {
            "opaque modifier not followed by def"
        }
        HumanDiagnosticKind::DuplicateOpaqueModifier => "duplicate opaque modifier",
        HumanDiagnosticKind::UnsupportedOpaqueEquationDefinition => {
            "unsupported opaque equation definition"
        }
        HumanDiagnosticKind::UnsupportedOpaqueDefinition => "unsupported opaque definition",
        HumanDiagnosticKind::ImportAfterItem => "import after item",
        HumanDiagnosticKind::UnsupportedSyntax => "unsupported syntax",
        HumanDiagnosticKind::ImportResolutionError => "import resolution error",
        HumanDiagnosticKind::MissingVerifiedImport => "missing verified import",
        HumanDiagnosticKind::NamespaceMismatch => "namespace mismatch",
        HumanDiagnosticKind::UnknownNamespace => "unknown namespace",
        HumanDiagnosticKind::DuplicateDeclaration => "duplicate declaration",
        HumanDiagnosticKind::UnknownIdentifier => "unknown identifier",
        HumanDiagnosticKind::AmbiguousName => "ambiguous name",
        HumanDiagnosticKind::AmbiguousConstructor => "ambiguous constructor",
        HumanDiagnosticKind::ForwardReference => "forward reference",
        HumanDiagnosticKind::NotationConflict => "notation conflict",
        HumanDiagnosticKind::AmbiguousNotation => "ambiguous notation",
        HumanDiagnosticKind::TooManyNotationCandidates => "too many notation candidates",
        HumanDiagnosticKind::TypeclassNoSolution => "typeclass no solution",
        HumanDiagnosticKind::TypeclassAmbiguous => "ambiguous typeclass instance",
        HumanDiagnosticKind::TypeclassBudgetExceeded => "typeclass search budget exceeded",
        HumanDiagnosticKind::UnsupportedTactic => "unsupported tactic",
        HumanDiagnosticKind::UnsupportedEquationGuard => "unsupported equation guard",
        HumanDiagnosticKind::UnsupportedViewPattern => "unsupported view pattern",
        HumanDiagnosticKind::EquationCompilerDisabled => "equation compiler disabled",
        HumanDiagnosticKind::NonExhaustivePatterns => "non-exhaustive patterns",
        HumanDiagnosticKind::RedundantEquation => "redundant equation",
        HumanDiagnosticKind::ImpossibleBranchNotProvable => "impossible branch not provable",
        HumanDiagnosticKind::RecursiveCallNotDecreasing => "recursive call not decreasing",
        HumanDiagnosticKind::MutualCycleWithoutDecrease => "mutual cycle without decrease",
        HumanDiagnosticKind::TerminationMeasureNotNat => "termination measure is not Nat-valued",
        HumanDiagnosticKind::MeasureDecreaseProofMissing => "measure decrease proof is missing",
        HumanDiagnosticKind::UnsolvedImplicit => "unsolved implicit",
        HumanDiagnosticKind::UnsolvedMeta => "unsolved metavariable",
        HumanDiagnosticKind::UnsolvedUniverseMeta => "unsolved universe metavariable",
        HumanDiagnosticKind::UnsolvedHole => "unsolved hole",
        HumanDiagnosticKind::NamedHoleContextMismatch => "named hole context mismatch",
        HumanDiagnosticKind::OccursCheckFailed => "occurs check failed",
        HumanDiagnosticKind::ExpectedFunctionType => "expected function type",
        HumanDiagnosticKind::ExpectedSort => "expected sort",
        HumanDiagnosticKind::TypeMismatch => "type mismatch",
        HumanDiagnosticKind::NoGoalsButTacticRemaining => "no goals but tactic remaining",
        HumanDiagnosticKind::UnresolvedGoal => "unresolved goal",
        HumanDiagnosticKind::KernelRejected => "kernel rejected",
        HumanDiagnosticKind::MachineElaborationError => "machine elaboration error",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;

    #[test]
    fn human_diagnostic_is_separate_from_machine_diagnostic() {
        let diagnostic =
            HumanDiagnostic::not_implemented(Span::empty(FileId(2)), "parse_human_module");

        assert_eq!(diagnostic.kind, HumanDiagnosticKind::NotImplemented);
        assert_eq!(diagnostic.severity, HumanDiagnosticSeverity::Error);
        assert_eq!(diagnostic.primary_span, Span::empty(FileId(2)));
        assert!(diagnostic.message.contains("Human frontend"));
        assert_eq!(
            diagnostic
                .payload
                .as_ref()
                .and_then(|payload| payload.detail.as_deref()),
            Some("parse_human_module is reserved for the Human frontend frontend")
        );
    }

    #[test]
    fn human_diagnostic_message_is_derived_from_payload() {
        let diagnostic = HumanDiagnostic::error(
            HumanDiagnosticKind::AmbiguousName,
            Span::empty(FileId(0)),
            "ambiguous name add",
        )
        .with_phase(HumanDiagnosticPhase::Resolver)
        .with_payload(HumanDiagnosticPayload {
            candidates: vec!["Nat.add".to_owned(), "Int.add".to_owned()],
            ..HumanDiagnosticPayload::default()
        });

        let payload = diagnostic.payload.expect("payload should be present");
        assert_eq!(payload.phase, Some(HumanDiagnosticPhase::Resolver));
        assert_eq!(payload.candidates, vec!["Nat.add", "Int.add"]);
        assert_eq!(
            diagnostic.message,
            "ambiguous name add\ncandidates:\n  Nat.add\n  Int.add"
        );
    }

    #[test]
    fn unsupported_tactic_diagnostic_is_distinct_from_generic_parse_error() {
        let diagnostic = HumanDiagnostic::unsupported_tactic(Span::empty(FileId(4)), "constructor");

        assert_eq!(diagnostic.kind, HumanDiagnosticKind::UnsupportedTactic);
        assert_eq!(diagnostic.severity, HumanDiagnosticSeverity::Error);
        assert!(diagnostic.message.contains("unsupported Human tactic"));
    }

    #[test]
    fn human_diagnostic_phase_preserves_payloadless_external_message() {
        let diagnostic = HumanDiagnostic {
            kind: HumanDiagnosticKind::ParseError,
            severity: HumanDiagnosticSeverity::Error,
            primary_span: Span::empty(FileId(0)),
            message: "external parse error".to_owned(),
            payload: None,
        }
        .with_phase(HumanDiagnosticPhase::Parser);

        assert_eq!(diagnostic.message, "external parse error");
        assert_eq!(
            diagnostic
                .payload
                .as_ref()
                .and_then(|payload| payload.detail.as_deref()),
            Some("external parse error")
        );
    }
}
