//! Bounded, opt-in authoring diagnostics for kernel conversion failures.

use crate::{Error, Expr};

/// Kernel failure plus optional bounded authoring context.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosedKernelError {
    error: Box<Error>,
    context: Option<KernelDiagnosticContext>,
}

impl DiagnosedKernelError {
    /// Build a diagnosed error without additional context.
    pub fn new(error: Error) -> Self {
        Self {
            error: Box::new(error),
            context: None,
        }
    }

    /// Attach bounded diagnostic context.
    #[must_use]
    pub fn with_context(mut self, context: KernelDiagnosticContext) -> Self {
        self.context = Some(context);
        self
    }

    /// Return the unchanged kernel error.
    pub fn error(&self) -> &Error {
        &self.error
    }

    /// Consume the wrapper and return the unchanged kernel error.
    pub fn into_error(self) -> Error {
        *self.error
    }

    /// Return bounded authoring context when recorded.
    pub fn context(&self) -> Option<&KernelDiagnosticContext> {
        self.context.as_ref()
    }
}

/// Bounded context for one kernel checking phase.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelDiagnosticContext {
    phase: KernelDiagnosticPhase,
    conversion: Option<KernelConversionContext>,
}

impl KernelDiagnosticContext {
    /// Build context for a phase with no conversion record.
    pub fn new(phase: KernelDiagnosticPhase) -> Self {
        Self {
            phase,
            conversion: None,
        }
    }

    /// Attach one bounded conversion record.
    #[must_use]
    pub fn with_conversion(mut self, conversion: KernelConversionContext) -> Self {
        self.conversion = Some(conversion);
        self
    }

    /// Return the checking phase.
    pub const fn phase(&self) -> KernelDiagnosticPhase {
        self.phase
    }

    /// Return the conversion record when available.
    pub fn conversion(&self) -> Option<&KernelConversionContext> {
        self.conversion.as_ref()
    }
}

/// Stable phase for a bounded authoring diagnostic.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelDiagnosticPhase {
    /// Term checking against an expected type.
    TermCheck,
    /// Declaration type checking.
    DeclarationType,
    /// Declaration value or proof checking.
    DeclarationValue,
    /// Inductive constructor checking.
    InductiveConstructor,
    /// Inductive recursor checking.
    InductiveRecursor,
    /// A conversion with no narrower phase.
    DefinitionalEquality,
}

impl KernelDiagnosticPhase {
    /// Stable output spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TermCheck => "term_check",
            Self::DeclarationType => "declaration_type",
            Self::DeclarationValue => "declaration_value",
            Self::InductiveConstructor => "inductive_constructor",
            Self::InductiveRecursor => "inductive_recursor",
            Self::DefinitionalEquality => "definitional_equality",
        }
    }
}

/// Stable conversion outcome.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelComparisonOutcome {
    /// Compared expressions were not definitionally equal.
    NotDefEq,
    /// Conversion fuel was exhausted at the recorded comparison.
    FuelExhausted,
}

impl KernelComparisonOutcome {
    /// Stable output spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotDefEq => "not_defeq",
            Self::FuelExhausted => "fuel_exhausted",
        }
    }
}

/// Bounded expression head label.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelExprHead {
    /// Universe sort.
    Sort,
    /// Bound variable.
    BoundVariable,
    /// Named constant, capped by `from_expr`.
    Constant(String),
    /// Function application.
    Application,
    /// Lambda abstraction.
    Lambda,
    /// Dependent function type.
    Pi,
    /// Local let binding.
    Let,
    /// Unavailable or deliberately omitted head.
    Unknown,
}

impl KernelExprHead {
    /// Derive a bounded head without rendering the complete expression.
    pub fn from_expr(expression: &Expr) -> Self {
        match expression {
            Expr::Sort(_) => Self::Sort,
            Expr::BVar(_) => Self::BoundVariable,
            Expr::Const { name, .. } if name.len() <= 256 => Self::Constant(name.clone()),
            Expr::Const { .. } => Self::Constant("<truncated>".to_owned()),
            Expr::App(..) => Self::Application,
            Expr::Lam { .. } => Self::Lambda,
            Expr::Pi { .. } => Self::Pi,
            Expr::Let { .. } => Self::Let,
        }
    }

    /// Stable bounded output spelling.
    pub fn as_str(&self) -> String {
        match self {
            Self::Sort => "sort".to_owned(),
            Self::BoundVariable => "bound_variable".to_owned(),
            Self::Constant(name) => format!("constant:{name}"),
            Self::Application => "application".to_owned(),
            Self::Lambda => "lambda".to_owned(),
            Self::Pi => "pi".to_owned(),
            Self::Let => "let".to_owned(),
            Self::Unknown => "unknown".to_owned(),
        }
    }
}

/// One deepest bounded conversion comparison.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelConversionContext {
    outcome: KernelComparisonOutcome,
    lhs_head: KernelExprHead,
    rhs_head: KernelExprHead,
    depth: u32,
}

impl KernelConversionContext {
    /// Build a bounded comparison record.
    pub fn new(
        outcome: KernelComparisonOutcome,
        lhs_head: KernelExprHead,
        rhs_head: KernelExprHead,
        depth: u32,
    ) -> Self {
        Self {
            outcome,
            lhs_head,
            rhs_head,
            depth,
        }
    }

    /// Return the comparison outcome.
    pub const fn outcome(&self) -> KernelComparisonOutcome {
        self.outcome
    }

    /// Return the left expression head.
    pub fn lhs_head(&self) -> &KernelExprHead {
        &self.lhs_head
    }

    /// Return the right expression head.
    pub fn rhs_head(&self) -> &KernelExprHead {
        &self.rhs_head
    }

    /// Return conversion recursion depth.
    pub const fn depth(&self) -> u32 {
        self.depth
    }
}
