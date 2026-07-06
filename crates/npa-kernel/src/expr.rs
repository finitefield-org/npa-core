use std::sync::Arc;

use crate::level::Level;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Sort(Level),
    BVar(u32),
    Const {
        name: String,
        levels: Vec<Level>,
    },
    App(Arc<Expr>, Arc<Expr>),
    Lam {
        binder: String,
        ty: Arc<Expr>,
        body: Arc<Expr>,
    },
    Pi {
        binder: String,
        ty: Arc<Expr>,
        body: Arc<Expr>,
    },
    Let {
        binder: String,
        ty: Arc<Expr>,
        value: Arc<Expr>,
        body: Arc<Expr>,
    },
}

impl Expr {
    pub fn sort(level: Level) -> Self {
        Self::Sort(level)
    }

    pub fn bvar(index: u32) -> Self {
        Self::BVar(index)
    }

    pub fn konst(name: impl Into<String>, levels: Vec<Level>) -> Self {
        Self::Const {
            name: name.into(),
            levels,
        }
    }

    pub fn app(fun: Self, arg: Self) -> Self {
        Self::App(Arc::new(fun), Arc::new(arg))
    }

    pub fn apps(fun: Self, args: impl IntoIterator<Item = Self>) -> Self {
        args.into_iter().fold(fun, Self::app)
    }

    pub fn lam(binder: impl Into<String>, ty: Self, body: Self) -> Self {
        Self::Lam {
            binder: binder.into(),
            ty: Arc::new(ty),
            body: Arc::new(body),
        }
    }

    pub fn pi(binder: impl Into<String>, ty: Self, body: Self) -> Self {
        Self::Pi {
            binder: binder.into(),
            ty: Arc::new(ty),
            body: Arc::new(body),
        }
    }

    pub fn let_in(binder: impl Into<String>, ty: Self, value: Self, body: Self) -> Self {
        Self::Let {
            binder: binder.into(),
            ty: Arc::new(ty),
            value: Arc::new(value),
            body: Arc::new(body),
        }
    }
}

/// Conservative syntactic equality used as a definitional-equality fast path.
///
/// Returns `true` only for terms that are syntactically identical up to
/// binder display names, which are definitionally equal by reflexivity of
/// the de Bruijn representation. A `false` result carries no information;
/// callers must fall back to full conversion checking. Shared `Arc`
/// subtrees short-circuit by pointer identity, so copy-on-write reuse from
/// `subst`/`shift` makes this cheap on the common reflexive case.
pub fn quick_syntactic_eq(lhs: &Expr, rhs: &Expr) -> bool {
    match (lhs, rhs) {
        (Expr::Sort(lhs), Expr::Sort(rhs)) => lhs == rhs,
        (Expr::BVar(lhs), Expr::BVar(rhs)) => lhs == rhs,
        (
            Expr::Const {
                name: lhs_name,
                levels: lhs_levels,
            },
            Expr::Const {
                name: rhs_name,
                levels: rhs_levels,
            },
        ) => lhs_name == rhs_name && lhs_levels == rhs_levels,
        (Expr::App(lhs_fun, lhs_arg), Expr::App(rhs_fun, rhs_arg)) => {
            quick_syntactic_eq_rc(lhs_fun, rhs_fun) && quick_syntactic_eq_rc(lhs_arg, rhs_arg)
        }
        (
            Expr::Lam {
                ty: lhs_ty,
                body: lhs_body,
                ..
            },
            Expr::Lam {
                ty: rhs_ty,
                body: rhs_body,
                ..
            },
        )
        | (
            Expr::Pi {
                ty: lhs_ty,
                body: lhs_body,
                ..
            },
            Expr::Pi {
                ty: rhs_ty,
                body: rhs_body,
                ..
            },
        ) => quick_syntactic_eq_rc(lhs_ty, rhs_ty) && quick_syntactic_eq_rc(lhs_body, rhs_body),
        (
            Expr::Let {
                ty: lhs_ty,
                value: lhs_value,
                body: lhs_body,
                ..
            },
            Expr::Let {
                ty: rhs_ty,
                value: rhs_value,
                body: rhs_body,
                ..
            },
        ) => {
            quick_syntactic_eq_rc(lhs_ty, rhs_ty)
                && quick_syntactic_eq_rc(lhs_value, rhs_value)
                && quick_syntactic_eq_rc(lhs_body, rhs_body)
        }
        _ => false,
    }
}

fn quick_syntactic_eq_rc(lhs: &Arc<Expr>, rhs: &Arc<Expr>) -> bool {
    Arc::ptr_eq(lhs, rhs) || quick_syntactic_eq(lhs, rhs)
}

pub fn collect_apps(term: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = term;
    while let Expr::App(fun, arg) = head {
        args.push((**arg).clone());
        head = fun;
    }
    args.reverse();
    (head.clone(), args)
}
