use std::{collections::HashSet, sync::Arc};

use crate::level::Level;

#[derive(Clone, Debug)]
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
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        syntactic_eq_iterative(self, other, true)
    }
}

impl Eq for Expr {}

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
    syntactic_eq_iterative(lhs, rhs, false)
}

fn syntactic_eq_iterative(lhs: &Expr, rhs: &Expr, compare_binder_names: bool) -> bool {
    let pointer = |expr: &Expr| std::ptr::from_ref(expr) as usize;
    let mut pending = vec![(lhs, rhs)];
    let mut seen = HashSet::new();
    while let Some((lhs, rhs)) = pending.pop() {
        if std::ptr::eq(lhs, rhs) {
            continue;
        }
        if !seen.insert((pointer(lhs), pointer(rhs))) {
            continue;
        }
        match (lhs, rhs) {
            (Expr::Sort(lhs), Expr::Sort(rhs)) if lhs == rhs => {}
            (Expr::BVar(lhs), Expr::BVar(rhs)) if lhs == rhs => {}
            (
                Expr::Const {
                    name: lhs_name,
                    levels: lhs_levels,
                },
                Expr::Const {
                    name: rhs_name,
                    levels: rhs_levels,
                },
            ) if lhs_name == rhs_name && lhs_levels == rhs_levels => {}
            (Expr::App(lhs_fun, lhs_arg), Expr::App(rhs_fun, rhs_arg)) => {
                pending.push((lhs_arg, rhs_arg));
                pending.push((lhs_fun, rhs_fun));
            }
            (
                Expr::Lam {
                    binder: lhs_binder,
                    ty: lhs_ty,
                    body: lhs_body,
                },
                Expr::Lam {
                    binder: rhs_binder,
                    ty: rhs_ty,
                    body: rhs_body,
                },
            )
            | (
                Expr::Pi {
                    binder: lhs_binder,
                    ty: lhs_ty,
                    body: lhs_body,
                },
                Expr::Pi {
                    binder: rhs_binder,
                    ty: rhs_ty,
                    body: rhs_body,
                },
            ) => {
                if compare_binder_names && lhs_binder != rhs_binder {
                    return false;
                }
                pending.push((lhs_body, rhs_body));
                pending.push((lhs_ty, rhs_ty));
            }
            _ => return false,
        }
    }
    true
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expression_equality_is_stack_safe_and_memoizes_shared_dags() {
        let mut lhs = Arc::new(Expr::bvar(0));
        let mut rhs = Arc::new(Expr::bvar(0));
        for _ in 0..8_192 {
            lhs = Arc::new(Expr::App(Arc::clone(&lhs), Arc::clone(&lhs)));
            rhs = Arc::new(Expr::App(Arc::clone(&rhs), Arc::clone(&rhs)));
        }
        assert_eq!(lhs.as_ref(), rhs.as_ref());
        assert!(quick_syntactic_eq(&lhs, &rhs));
        std::mem::forget(lhs);
        std::mem::forget(rhs);

        let lhs = Expr::lam("lhs", Expr::sort(Level::zero()), Expr::bvar(0));
        let rhs = Expr::lam("rhs", Expr::sort(Level::zero()), Expr::bvar(0));
        assert_ne!(lhs, rhs);
        assert!(quick_syntactic_eq(&lhs, &rhs));
    }
}
