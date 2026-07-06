use crate::Span;

pub type HumanResult<T> = std::result::Result<T, HumanDiagnostic>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDiagnosticSeverity {
    Error,
    Warning,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDiagnosticKind {
    NotImplemented,
    ParseError,
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HumanDiagnosticPayload {
    pub phase: Option<HumanDiagnosticPhase>,
    pub detail: Option<String>,
    pub candidates: Vec<String>,
    pub hole_goals: Vec<HumanHoleGoal>,
    pub unsolved_meta: Option<HumanUnsolvedMeta>,
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
