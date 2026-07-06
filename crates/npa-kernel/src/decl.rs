use crate::{
    expr::Expr,
    level::{Level, UniverseConstraint},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reducibility {
    Reducible,
    Opaque,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    Axiom {
        name: String,
        universe_params: Vec<String>,
        ty: Expr,
    },
    AxiomConstrained {
        name: String,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
    },
    Def {
        name: String,
        universe_params: Vec<String>,
        ty: Expr,
        value: Expr,
        reducibility: Reducibility,
    },
    DefConstrained {
        name: String,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
        value: Expr,
        reducibility: Reducibility,
    },
    Theorem {
        name: String,
        universe_params: Vec<String>,
        ty: Expr,
        proof: Expr,
    },
    TheoremConstrained {
        name: String,
        universe_params: Vec<String>,
        universe_constraints: Vec<UniverseConstraint>,
        ty: Expr,
        proof: Expr,
    },
    Inductive {
        name: String,
        universe_params: Vec<String>,
        ty: Expr,
        data: Box<InductiveDecl>,
    },
    Constructor {
        name: String,
        universe_params: Vec<String>,
        ty: Expr,
        inductive: String,
    },
    Recursor {
        name: String,
        universe_params: Vec<String>,
        ty: Expr,
        inductive: String,
        rules: RecursorRules,
    },
    MutualInductiveBlock {
        name: String,
        universe_params: Vec<String>,
        data: Box<MutualInductiveBlock>,
    },
}

impl Decl {
    pub fn name(&self) -> &str {
        match self {
            Self::Axiom { name, .. }
            | Self::AxiomConstrained { name, .. }
            | Self::Def { name, .. }
            | Self::DefConstrained { name, .. }
            | Self::Theorem { name, .. }
            | Self::TheoremConstrained { name, .. } => name,
            Self::Inductive { name, .. }
            | Self::Constructor { name, .. }
            | Self::Recursor { name, .. }
            | Self::MutualInductiveBlock { name, .. } => name,
        }
    }

    pub fn universe_params(&self) -> &[String] {
        match self {
            Self::Axiom {
                universe_params, ..
            }
            | Self::AxiomConstrained {
                universe_params, ..
            }
            | Self::Def {
                universe_params, ..
            }
            | Self::DefConstrained {
                universe_params, ..
            }
            | Self::Theorem {
                universe_params, ..
            }
            | Self::TheoremConstrained {
                universe_params, ..
            }
            | Self::Inductive {
                universe_params, ..
            }
            | Self::MutualInductiveBlock {
                universe_params, ..
            }
            | Self::Constructor {
                universe_params, ..
            }
            | Self::Recursor {
                universe_params, ..
            } => universe_params,
        }
    }

    pub fn universe_constraints(&self) -> &[UniverseConstraint] {
        match self {
            Self::AxiomConstrained {
                universe_constraints,
                ..
            }
            | Self::DefConstrained {
                universe_constraints,
                ..
            }
            | Self::TheoremConstrained {
                universe_constraints,
                ..
            } => universe_constraints,
            Self::Inductive { data, .. } => &data.universe_constraints,
            Self::MutualInductiveBlock { data, .. } => &data.universe_constraints,
            Self::Axiom { .. }
            | Self::Def { .. }
            | Self::Theorem { .. }
            | Self::Constructor { .. }
            | Self::Recursor { .. } => &[],
        }
    }

    pub fn ty(&self) -> &Expr {
        match self {
            Self::Axiom { ty, .. }
            | Self::AxiomConstrained { ty, .. }
            | Self::Def { ty, .. }
            | Self::DefConstrained { ty, .. }
            | Self::Theorem { ty, .. }
            | Self::TheoremConstrained { ty, .. } => ty,
            Self::Inductive { ty, .. }
            | Self::Constructor { ty, .. }
            | Self::Recursor { ty, .. } => ty,
            Self::MutualInductiveBlock { name, .. } => {
                panic!("mutual inductive block `{name}` has no singular type")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    pub name: String,
    pub ty: Expr,
}

impl Binder {
    pub fn new(name: impl Into<String>, ty: Expr) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: String,
    pub ty: Expr,
}

impl ConstructorDecl {
    pub fn new(name: impl Into<String>, ty: Expr) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorRules {
    pub minor_start: usize,
    pub major_index: usize,
}

impl RecursorRules {
    pub fn new(minor_start: usize, major_index: usize) -> Self {
        Self {
            minor_start,
            major_index,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorDecl {
    pub name: String,
    pub universe_params: Vec<String>,
    pub ty: Expr,
    pub rules: Option<RecursorRules>,
}

impl RecursorDecl {
    pub fn new(name: impl Into<String>, universe_params: Vec<String>, ty: Expr) -> Self {
        Self {
            name: name.into(),
            universe_params,
            ty,
            rules: None,
        }
    }

    pub fn with_rules(
        name: impl Into<String>,
        universe_params: Vec<String>,
        ty: Expr,
        rules: RecursorRules,
    ) -> Self {
        Self {
            name: name.into(),
            universe_params,
            ty,
            rules: Some(rules),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutualInductiveBlock {
    pub name: String,
    pub universe_params: Vec<String>,
    pub universe_constraints: Vec<UniverseConstraint>,
    pub inductives: Vec<InductiveDecl>,
}

impl MutualInductiveBlock {
    pub fn new(
        name: impl Into<String>,
        universe_params: Vec<String>,
        inductives: Vec<InductiveDecl>,
    ) -> Self {
        Self {
            name: name.into(),
            universe_params,
            universe_constraints: Vec::new(),
            inductives,
        }
    }

    pub fn with_universe_constraints(mut self, constraints: Vec<UniverseConstraint>) -> Self {
        self.universe_constraints = constraints;
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveDecl {
    pub name: String,
    pub universe_params: Vec<String>,
    pub universe_constraints: Vec<UniverseConstraint>,
    pub params: Vec<Binder>,
    pub indices: Vec<Binder>,
    pub sort: Level,
    pub constructors: Vec<ConstructorDecl>,
    pub recursor: Option<RecursorDecl>,
}

impl InductiveDecl {
    pub fn new(
        name: impl Into<String>,
        universe_params: Vec<String>,
        params: Vec<Binder>,
        indices: Vec<Binder>,
        sort: Level,
        constructors: Vec<ConstructorDecl>,
        recursor: Option<RecursorDecl>,
    ) -> Self {
        Self {
            name: name.into(),
            universe_params,
            universe_constraints: Vec::new(),
            params,
            indices,
            sort,
            constructors,
            recursor,
        }
    }

    pub fn with_universe_constraints(mut self, constraints: Vec<UniverseConstraint>) -> Self {
        self.universe_constraints = constraints;
        self
    }
}
