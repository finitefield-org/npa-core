use crate::expr::Expr;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceLimitKind {
    Whnf,
    Conversion,
    UniverseConstraints,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    UnknownConstant(String),
    UnknownUniverseParam(String),
    UnresolvedUniverseMeta(String),
    DuplicateUniverseParam(String),
    NonCanonicalUniverseParams(Vec<String>),
    NonCanonicalUniverseLevel {
        level: crate::level::Level,
    },
    NonCanonicalUniverseConstraints,
    DuplicateUniverseConstraint,
    UnsupportedUniverseConstraint {
        constraint: crate::level::UniverseConstraint,
    },
    UnsatisfiableUniverseConstraints,
    UniverseConstraintViolation {
        declaration: String,
        constraint: crate::level::UniverseConstraint,
    },
    BadUniverseArity {
        name: String,
        expected: usize,
        actual: usize,
    },
    InvalidBVar(u32),
    ExpectedSort {
        actual: Expr,
    },
    ExpectedPi {
        actual: Expr,
    },
    TypeMismatch {
        expected: Expr,
        actual: Expr,
    },
    NotDefEq {
        lhs: Expr,
        rhs: Expr,
    },
    InvalidDeclarationName(String),
    DuplicateDecl(String),
    InvalidInductive(String),
    NonPositiveOccurrence {
        inductive: String,
        constructor: String,
        ty: Expr,
    },
    BadConstructorResult {
        inductive: String,
        constructor: String,
        result: Expr,
    },
    ConstructorUniverseBoundViolation {
        inductive: String,
        constructor: String,
        field_index: usize,
        field_level: crate::level::Level,
        inductive_sort: crate::level::Level,
    },
    ResourceLimit {
        kind: ResourceLimitKind,
    },
}
