use std::sync::Arc;

use crate::{
    error::{Error, Result},
    expr::Expr,
    level::{normalize_level, Level},
};

/// Substitutes universe parameters in `expr`, sharing unchanged subtrees.
pub fn subst_levels_expr(expr: &Expr, params: &[String], levels: &[Level]) -> Expr {
    if params.is_empty() {
        return expr.clone();
    }
    subst_levels_expr_changed(expr, params, levels).unwrap_or_else(|| expr.clone())
}

fn subst_levels_expr_rc(
    expr: &Arc<Expr>,
    params: &[String],
    levels: &[Level],
) -> Option<Arc<Expr>> {
    subst_levels_expr_changed(expr, params, levels).map(Arc::new)
}

fn subst_levels_expr_changed(expr: &Expr, params: &[String], levels: &[Level]) -> Option<Expr> {
    match expr {
        Expr::Sort(level) => subst_level_changed(level, params, levels).map(Expr::sort),
        Expr::BVar(_) => None,
        Expr::Const { name, levels: us } => {
            let mut substituted: Option<Vec<Level>> = None;
            for (index, level) in us.iter().enumerate() {
                match subst_level_changed(level, params, levels) {
                    Some(level) => substituted
                        .get_or_insert_with(|| us[..index].to_vec())
                        .push(level),
                    None => {
                        if let Some(substituted) = substituted.as_mut() {
                            substituted.push(level.clone());
                        }
                    }
                }
            }
            substituted.map(|substituted| Expr::konst(name.clone(), substituted))
        }
        Expr::App(fun, arg) => {
            let new_fun = subst_levels_expr_rc(fun, params, levels);
            let new_arg = subst_levels_expr_rc(arg, params, levels);
            if new_fun.is_none() && new_arg.is_none() {
                return None;
            }
            Some(Expr::App(
                new_fun.unwrap_or_else(|| Arc::clone(fun)),
                new_arg.unwrap_or_else(|| Arc::clone(arg)),
            ))
        }
        Expr::Lam { binder, ty, body } => {
            let new_ty = subst_levels_expr_rc(ty, params, levels);
            let new_body = subst_levels_expr_rc(body, params, levels);
            if new_ty.is_none() && new_body.is_none() {
                return None;
            }
            Some(Expr::Lam {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            })
        }
        Expr::Pi { binder, ty, body } => {
            let new_ty = subst_levels_expr_rc(ty, params, levels);
            let new_body = subst_levels_expr_rc(body, params, levels);
            if new_ty.is_none() && new_body.is_none() {
                return None;
            }
            Some(Expr::Pi {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            })
        }
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => {
            let new_ty = subst_levels_expr_rc(ty, params, levels);
            let new_value = subst_levels_expr_rc(value, params, levels);
            let new_body = subst_levels_expr_rc(body, params, levels);
            if new_ty.is_none() && new_value.is_none() && new_body.is_none() {
                return None;
            }
            Some(Expr::Let {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                value: new_value.unwrap_or_else(|| Arc::clone(value)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            })
        }
    }
}

fn subst_level_changed(level: &Level, params: &[String], levels: &[Level]) -> Option<Level> {
    match level {
        Level::Zero => None,
        Level::Succ(inner) => subst_level_changed(inner, params, levels).map(Level::succ),
        Level::Max(lhs, rhs) => {
            let new_lhs = subst_level_changed(lhs, params, levels);
            let new_rhs = subst_level_changed(rhs, params, levels);
            if new_lhs.is_none() && new_rhs.is_none() {
                return None;
            }
            Some(Level::max(
                new_lhs.unwrap_or_else(|| (**lhs).clone()),
                new_rhs.unwrap_or_else(|| (**rhs).clone()),
            ))
        }
        Level::IMax(lhs, rhs) => {
            let new_lhs = subst_level_changed(lhs, params, levels);
            let new_rhs = subst_level_changed(rhs, params, levels);
            if new_lhs.is_none() && new_rhs.is_none() {
                return None;
            }
            Some(Level::imax(
                new_lhs.unwrap_or_else(|| (**lhs).clone()),
                new_rhs.unwrap_or_else(|| (**rhs).clone()),
            ))
        }
        Level::Param(name) => params
            .iter()
            .position(|param| param == name)
            .map(|index| levels[index].clone()),
    }
}

/// Shifts loose bound variables, sharing unchanged subtrees.
pub fn shift(expr: &Expr, amount: i32, cutoff: u32) -> Result<Expr> {
    if amount == 0 {
        return Ok(expr.clone());
    }
    Ok(shift_changed(expr, amount, cutoff)?.unwrap_or_else(|| expr.clone()))
}

fn shift_rc(expr: &Arc<Expr>, amount: i32, cutoff: u32) -> Result<Option<Arc<Expr>>> {
    Ok(shift_changed(expr, amount, cutoff)?.map(Arc::new))
}

fn shift_changed(expr: &Expr, amount: i32, cutoff: u32) -> Result<Option<Expr>> {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => Ok(None),
        Expr::BVar(index) => {
            if *index < cutoff {
                Ok(None)
            } else {
                let shifted = *index as i32 + amount;
                if shifted < 0 {
                    Err(Error::InvalidBVar(*index))
                } else {
                    Ok(Some(Expr::bvar(shifted as u32)))
                }
            }
        }
        Expr::App(fun, arg) => {
            let new_fun = shift_rc(fun, amount, cutoff)?;
            let new_arg = shift_rc(arg, amount, cutoff)?;
            if new_fun.is_none() && new_arg.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::App(
                new_fun.unwrap_or_else(|| Arc::clone(fun)),
                new_arg.unwrap_or_else(|| Arc::clone(arg)),
            )))
        }
        Expr::Lam { binder, ty, body } => {
            let new_ty = shift_rc(ty, amount, cutoff)?;
            let new_body = shift_rc(body, amount, cutoff + 1)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::Lam {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        Expr::Pi { binder, ty, body } => {
            let new_ty = shift_rc(ty, amount, cutoff)?;
            let new_body = shift_rc(body, amount, cutoff + 1)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::Pi {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => {
            let new_ty = shift_rc(ty, amount, cutoff)?;
            let new_value = shift_rc(value, amount, cutoff)?;
            let new_body = shift_rc(body, amount, cutoff + 1)?;
            if new_ty.is_none() && new_value.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::Let {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                value: new_value.unwrap_or_else(|| Arc::clone(value)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
    }
}

fn subst(expr: &Expr, target: u32, replacement: &Expr) -> Result<Expr> {
    Ok(subst_changed(expr, target, replacement)?.unwrap_or_else(|| expr.clone()))
}

fn subst_rc(expr: &Arc<Expr>, target: u32, replacement: &Expr) -> Result<Option<Arc<Expr>>> {
    Ok(subst_changed(expr, target, replacement)?.map(Arc::new))
}

fn subst_changed(expr: &Expr, target: u32, replacement: &Expr) -> Result<Option<Expr>> {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => Ok(None),
        Expr::BVar(index) if *index == target => shift(replacement, target as i32, 0).map(Some),
        Expr::BVar(index) if *index > target => Ok(Some(Expr::bvar(index - 1))),
        Expr::BVar(_) => Ok(None),
        Expr::App(fun, arg) => {
            let new_fun = subst_rc(fun, target, replacement)?;
            let new_arg = subst_rc(arg, target, replacement)?;
            if new_fun.is_none() && new_arg.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::App(
                new_fun.unwrap_or_else(|| Arc::clone(fun)),
                new_arg.unwrap_or_else(|| Arc::clone(arg)),
            )))
        }
        Expr::Lam { binder, ty, body } => {
            let new_ty = subst_rc(ty, target, replacement)?;
            let new_body = subst_rc(body, target + 1, replacement)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::Lam {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        Expr::Pi { binder, ty, body } => {
            let new_ty = subst_rc(ty, target, replacement)?;
            let new_body = subst_rc(body, target + 1, replacement)?;
            if new_ty.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::Pi {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => {
            let new_ty = subst_rc(ty, target, replacement)?;
            let new_value = subst_rc(value, target, replacement)?;
            let new_body = subst_rc(body, target + 1, replacement)?;
            if new_ty.is_none() && new_value.is_none() && new_body.is_none() {
                return Ok(None);
            }
            Ok(Some(Expr::Let {
                binder: binder.clone(),
                ty: new_ty.unwrap_or_else(|| Arc::clone(ty)),
                value: new_value.unwrap_or_else(|| Arc::clone(value)),
                body: new_body.unwrap_or_else(|| Arc::clone(body)),
            }))
        }
    }
}

pub fn instantiate(body: &Expr, value: &Expr) -> Result<Expr> {
    subst(body, 0, value)
}

#[allow(dead_code)]
fn _assert_level_normalization_is_linked(level: Level) -> Level {
    normalize_level(level)
}
