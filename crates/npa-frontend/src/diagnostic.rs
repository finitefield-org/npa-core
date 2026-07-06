use crate::Span;

pub type Result<T> = std::result::Result<T, MachineDiagnostic>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineDiagnosticSeverity {
    Error,
    Warning,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineDiagnosticKind {
    ParseError,
    UnsupportedItem,
    UnsupportedSyntax,
    ImportAfterItem,
    ImportResolutionError,
    MissingVerifiedImport,
    UnknownGlobalName,
    ShortGlobalName,
    AmbiguousGlobalName,
    GlobalShadowedByLocal,
    UnknownLocalName,
    DuplicateDeclaration,
    DuplicateUniverseParam,
    UnknownUniverseParam,
    UniverseLevelTooLarge,
    ImplicitArgumentRequired,
    MissingExplicitUniverse,
    UnannotatedBinder,
    UnannotatedLet,
    HoleNotAllowed,
    ExpectedFunctionType,
    ExpectedSort,
    TypeMismatch,
    TooManyArguments,
    TooFewArguments,
    UnsolvedUniverseMeta,
    KernelRejected,
    CertificateRejected,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineDiagnosticPayload {
    pub head_symbol: Option<String>,
    pub expected_hash: Option<npa_cert::Hash>,
    pub actual_hash: Option<npa_cert::Hash>,
    pub target_hash: Option<npa_cert::Hash>,
    pub expected_universe_args: Option<usize>,
    pub actual_universe_args: Option<usize>,
    pub candidates: Vec<MachineRepairCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachineRepairCandidate {
    pub name: npa_cert::Name,
    pub decl_interface_hash: Option<npa_cert::Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineRepairSuggestionKind {
    InsertExplicitArguments,
    InsertExplicitUniverseArguments,
    UseFullyQualifiedName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineRepairSuggestion {
    pub kind: MachineRepairSuggestionKind,
    pub replacement: Option<String>,
    pub candidates: Vec<MachineRepairCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDiagnostic {
    pub kind: MachineDiagnosticKind,
    pub severity: MachineDiagnosticSeverity,
    pub primary_span: Span,
    pub message: String,
    pub payload: Option<Box<MachineDiagnosticPayload>>,
    pub suggestions: Vec<MachineRepairSuggestion>,
}

impl MachineDiagnostic {
    pub fn error(
        kind: MachineDiagnosticKind,
        primary_span: Span,
        message: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            severity: MachineDiagnosticSeverity::Error,
            primary_span,
            message: message.into(),
            payload: None,
            suggestions: Vec::new(),
        }
    }

    pub fn warning(
        kind: MachineDiagnosticKind,
        primary_span: Span,
        message: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            severity: MachineDiagnosticSeverity::Warning,
            primary_span,
            message: message.into(),
            payload: None,
            suggestions: Vec::new(),
        }
    }

    pub fn parse(primary_span: Span, message: impl Into<String>) -> Self {
        Self::error(MachineDiagnosticKind::ParseError, primary_span, message)
    }

    pub fn unsupported_syntax(primary_span: Span, syntax: impl Into<String>) -> Self {
        Self::error(
            MachineDiagnosticKind::UnsupportedSyntax,
            primary_span,
            format!("unsupported Machine Surface syntax: {}", syntax.into()),
        )
    }

    pub fn with_payload(mut self, payload: MachineDiagnosticPayload) -> Self {
        self.payload = Some(Box::new(payload));
        self
    }

    pub fn with_suggestion(mut self, suggestion: MachineRepairSuggestion) -> Self {
        self.suggestions.push(suggestion);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;

    #[test]
    fn builds_simple_error_diagnostic() {
        let span = Span::new(FileId(1), 2, 3);
        let diagnostic = MachineDiagnostic::unsupported_syntax(span, "open");

        assert_eq!(diagnostic.kind, MachineDiagnosticKind::UnsupportedSyntax);
        assert_eq!(diagnostic.severity, MachineDiagnosticSeverity::Error);
        assert_eq!(diagnostic.primary_span, span);
        assert_eq!(diagnostic.payload, None);
        assert!(diagnostic.suggestions.is_empty());
    }
}
