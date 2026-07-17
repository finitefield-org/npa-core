use std::collections::{BTreeMap, BTreeSet};

use crate::error::{Error, ResourceLimitKind, Result};

pub const MAX_UNIVERSE_CONTEXT_NODES: usize = 65;
pub const MAX_UNIVERSE_ATOM_INEQUALITIES: usize = 1024;

const HUMAN_UNIVERSE_META_PREFIX: &str = "__npa_internal_human_universe_meta#";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UniverseConstraintRelation {
    Le,
    Eq,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniverseConstraint {
    pub lhs: Level,
    pub relation: UniverseConstraintRelation,
    pub rhs: Level,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniverseContext {
    pub params: Vec<String>,
    pub constraints: Vec<UniverseConstraint>,
    closure: UniverseConstraintClosure,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct UniverseConstraintClosure {
    dist: Vec<Vec<Option<i128>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum AtomBase {
    Zero,
    Param(String),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Atom {
    base: AtomBase,
    offset: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AtomInequality {
    lhs: Atom,
    rhs: Atom,
}

impl UniverseConstraint {
    pub fn le(lhs: Level, rhs: Level) -> Self {
        Self {
            lhs,
            relation: UniverseConstraintRelation::Le,
            rhs,
        }
    }

    pub fn eq(lhs: Level, rhs: Level) -> Self {
        Self {
            lhs,
            relation: UniverseConstraintRelation::Eq,
            rhs,
        }
    }
}

impl UniverseContext {
    /// Builds a canonical, satisfiable universe context for the supported
    /// difference-constraint fragment. Unsupported forms fail closed.
    pub fn new(
        params: Vec<String>,
        constraints: Vec<UniverseConstraint>,
    ) -> Result<UniverseContext> {
        if constraints.is_empty() {
            return UniverseContext::from_params(params);
        }
        let params = validate_universe_params(&params)?;
        ensure_universe_constraints_wf(&params, &constraints)?;
        ensure_universe_node_limit(params.len())?;

        let param_indices = universe_param_indices(&params);
        let mut edge_count = params.len();
        let mut closure = UniverseConstraintClosure::with_lower_bounds(params.len());
        for constraint in &constraints {
            let inequalities = decompose_constraint(constraint)?;
            edge_count =
                edge_count
                    .checked_add(inequalities.len())
                    .ok_or(Error::ResourceLimit {
                        kind: ResourceLimitKind::UniverseConstraints,
                    })?;
            ensure_universe_edge_limit(edge_count)?;
            for inequality in inequalities {
                let from = atom_base_index(&inequality.rhs.base, &param_indices)?;
                let to = atom_base_index(&inequality.lhs.base, &param_indices)?;
                let weight = i128::from(offset_bound(&inequality.rhs)?)
                    - i128::from(offset_bound(&inequality.lhs)?);
                closure.add_edge(from, to, weight);
            }
        }
        closure.close()?;
        Ok(UniverseContext {
            params,
            constraints,
            closure,
        })
    }

    pub fn from_params(params: Vec<String>) -> Result<UniverseContext> {
        let params = validate_universe_params(&params)?;
        ensure_universe_node_limit(params.len())?;
        ensure_universe_edge_limit(params.len())?;
        let param_count = params.len();
        Ok(UniverseContext {
            params,
            constraints: Vec::new(),
            closure: UniverseConstraintClosure::with_lower_bounds(param_count),
        })
    }

    pub fn empty() -> UniverseContext {
        UniverseContext {
            params: Vec::new(),
            constraints: Vec::new(),
            closure: UniverseConstraintClosure::with_lower_bounds(0),
        }
    }

    pub fn ensure_satisfiable(&self) -> Result<()> {
        Ok(())
    }

    pub fn entails(&self, obligations: &[UniverseConstraint]) -> Result<()> {
        if obligations.is_empty() {
            return Ok(());
        }
        for obligation in obligations {
            let normalized = normalize_constraint(obligation);
            let entailed = match normalized.relation {
                UniverseConstraintRelation::Le => {
                    self.entails_level_le(&normalized.lhs, &normalized.rhs)?
                }
                UniverseConstraintRelation::Eq => {
                    self.entails_level_le(&normalized.lhs, &normalized.rhs)?
                        && self.entails_level_le(&normalized.rhs, &normalized.lhs)?
                }
            };
            if !entailed {
                return Err(Error::UniverseConstraintViolation {
                    declaration: String::new(),
                    constraint: normalized,
                });
            }
        }
        Ok(())
    }

    /// Checks whether the current context entails one level inequality.
    ///
    /// Unlike stored declaration constraints, proof obligations may have a
    /// finite `max` on the right. The check remains conservative: every atom
    /// on the left must be bounded by at least one atom on the right.
    pub fn entails_level_le(&self, lhs: &Level, rhs: &Level) -> Result<bool> {
        ensure_level_wf(&self.params, lhs)?;
        ensure_level_wf(&self.params, rhs)?;
        let lhs = normalize_level(lhs.clone());
        let rhs = normalize_level(rhs.clone());
        if lhs == rhs {
            return Ok(true);
        }
        let lhs_atoms = decompose_lhs_level_expr(&lhs)?;
        let rhs_atoms = decompose_level_expr(&rhs)?;
        let comparison_count =
            lhs_atoms
                .len()
                .checked_mul(rhs_atoms.len())
                .ok_or(Error::ResourceLimit {
                    kind: ResourceLimitKind::UniverseConstraints,
                })?;
        ensure_universe_edge_limit(comparison_count)?;
        let param_indices = universe_param_indices(&self.params);
        for lhs_atom in &lhs_atoms {
            let to = atom_base_index(&lhs_atom.base, &param_indices)?;
            let lhs_offset = i128::from(offset_bound(lhs_atom)?);
            let mut witnessed = false;
            for rhs_atom in &rhs_atoms {
                let from = atom_base_index(&rhs_atom.base, &param_indices)?;
                let bound = i128::from(offset_bound(rhs_atom)?) - lhs_offset;
                if self.closure.entails(from, to, bound) {
                    witnessed = true;
                    break;
                }
            }
            if !witnessed {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn substitute_constraints(
        &self,
        params: &[String],
        levels: &[Level],
        constraints: &[UniverseConstraint],
    ) -> Result<Vec<UniverseConstraint>> {
        if params.len() != levels.len() {
            return Err(Error::BadUniverseArity {
                name: "<universe-constraints>".to_owned(),
                expected: params.len(),
                actual: levels.len(),
            });
        }
        let params = validate_universe_params(params)?;
        ensure_universe_constraints_wf(&params, constraints)?;
        for level in levels {
            ensure_level_wf(&self.params, level)?;
        }
        let mut obligations = constraints
            .iter()
            .map(|constraint| UniverseConstraint {
                lhs: substitute_level(&constraint.lhs, &params, levels),
                relation: constraint.relation,
                rhs: substitute_level(&constraint.rhs, &params, levels),
            })
            .collect::<Vec<_>>();
        obligations.sort();
        obligations.dedup();
        Ok(obligations)
    }
}

impl UniverseConstraintClosure {
    fn with_lower_bounds(param_count: usize) -> Self {
        let node_count = param_count + 1;
        let mut dist = vec![vec![None; node_count]; node_count];
        for (index, row) in dist.iter_mut().enumerate() {
            row[index] = Some(0);
        }
        for row in dist.iter_mut().take(node_count).skip(1) {
            row[0] = Some(0);
        }
        Self { dist }
    }

    fn add_edge(&mut self, from: usize, to: usize, weight: i128) {
        let current = &mut self.dist[from][to];
        if current.is_none_or(|old| weight < old) {
            *current = Some(weight);
        }
    }

    fn close(&mut self) -> Result<()> {
        let len = self.dist.len();
        for k in 0..len {
            for i in 0..len {
                let Some(ik) = self.dist[i][k] else {
                    continue;
                };
                for j in 0..len {
                    let Some(kj) = self.dist[k][j] else {
                        continue;
                    };
                    let candidate = ik + kj;
                    if self.dist[i][j].is_none_or(|old| candidate < old) {
                        self.dist[i][j] = Some(candidate);
                    }
                }
            }
        }
        if (0..len).any(|index| self.dist[index][index].is_some_and(|bound| bound < 0)) {
            return Err(Error::UnsatisfiableUniverseConstraints);
        }
        Ok(())
    }

    fn entails(&self, from: usize, to: usize, bound: i128) -> bool {
        self.dist[from][to].is_some_and(|actual| actual <= bound)
    }
}

impl Level {
    pub fn zero() -> Self {
        Self::Zero
    }

    pub fn succ(level: Self) -> Self {
        Self::Succ(Box::new(level))
    }

    pub fn max(lhs: Self, rhs: Self) -> Self {
        normalize_level(Self::Max(Box::new(lhs), Box::new(rhs)))
    }

    pub fn imax(lhs: Self, rhs: Self) -> Self {
        normalize_level(Self::IMax(Box::new(lhs), Box::new(rhs)))
    }

    pub fn param(name: impl Into<String>) -> Self {
        Self::Param(name.into())
    }
}

pub fn validate_universe_params(params: &[String]) -> Result<Vec<String>> {
    let mut seen = BTreeSet::new();
    for param in params {
        if is_unresolved_universe_meta_param(param) {
            return Err(Error::UnresolvedUniverseMeta(param.clone()));
        }
        if !seen.insert(param.clone()) {
            return Err(Error::DuplicateUniverseParam(param.clone()));
        }
    }
    if !params.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(Error::NonCanonicalUniverseParams(params.to_vec()));
    }
    Ok(params.to_vec())
}

pub fn ensure_level_wf(delta: &[String], level: &Level) -> Result<()> {
    match level {
        Level::Zero => Ok(()),
        Level::Succ(level) => ensure_level_wf(delta, level),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            ensure_level_wf(delta, lhs)?;
            ensure_level_wf(delta, rhs)
        }
        Level::Param(name) => {
            if is_unresolved_universe_meta_param(name) {
                return Err(Error::UnresolvedUniverseMeta(name.clone()));
            }
            if delta.iter().any(|param| param == name) {
                Ok(())
            } else {
                Err(Error::UnknownUniverseParam(name.clone()))
            }
        }
    }
}

fn is_unresolved_universe_meta_param(param: &str) -> bool {
    param.starts_with(HUMAN_UNIVERSE_META_PREFIX) || param.contains('?')
}

pub fn ensure_universe_constraints_wf(
    delta: &[String],
    constraints: &[UniverseConstraint],
) -> Result<()> {
    let mut canonical = constraints.to_vec();
    canonical.sort();
    for constraint in &canonical {
        ensure_canonical_level(delta, &constraint.lhs)?;
        ensure_canonical_level(delta, &constraint.rhs)?;
    }
    if constraints != canonical.as_slice() {
        return Err(Error::NonCanonicalUniverseConstraints);
    }
    if canonical.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(Error::DuplicateUniverseConstraint);
    }
    Ok(())
}

pub fn normalize_level(level: Level) -> Level {
    match level {
        Level::Zero | Level::Param(_) => level,
        Level::Succ(level) => Level::Succ(Box::new(normalize_level(*level))),
        Level::Max(lhs, rhs) => {
            let lhs = normalize_level(*lhs);
            let rhs = normalize_level(*rhs);
            if lhs == rhs {
                return lhs;
            }
            if lhs == Level::Zero {
                return rhs;
            }
            if rhs == Level::Zero {
                return lhs;
            }
            match (level_as_nat(&lhs), level_as_nat(&rhs)) {
                (Some(lhs_nat), Some(rhs_nat)) => level_from_nat(lhs_nat.max(rhs_nat)),
                _ if rhs < lhs => Level::Max(Box::new(rhs), Box::new(lhs)),
                _ => Level::Max(Box::new(lhs), Box::new(rhs)),
            }
        }
        Level::IMax(lhs, rhs) => {
            let lhs = normalize_level(*lhs);
            let rhs = normalize_level(*rhs);
            match rhs {
                Level::Zero => Level::Zero,
                Level::Succ(inner) => {
                    normalize_level(Level::Max(Box::new(lhs), Box::new(Level::Succ(inner))))
                }
                rhs => Level::IMax(Box::new(lhs), Box::new(rhs)),
            }
        }
    }
}

fn ensure_canonical_level(delta: &[String], level: &Level) -> Result<()> {
    ensure_level_wf(delta, level)?;
    let normalized = normalize_level(level.clone());
    if normalized == *level {
        Ok(())
    } else {
        Err(Error::NonCanonicalUniverseLevel {
            level: level.clone(),
        })
    }
}

fn ensure_universe_node_limit(param_count: usize) -> Result<()> {
    if param_count + 1 > MAX_UNIVERSE_CONTEXT_NODES {
        return Err(Error::ResourceLimit {
            kind: ResourceLimitKind::UniverseConstraints,
        });
    }
    Ok(())
}

fn ensure_universe_edge_limit(edge_count: usize) -> Result<()> {
    if edge_count > MAX_UNIVERSE_ATOM_INEQUALITIES {
        return Err(Error::ResourceLimit {
            kind: ResourceLimitKind::UniverseConstraints,
        });
    }
    Ok(())
}

fn universe_param_indices(params: &[String]) -> BTreeMap<String, usize> {
    params
        .iter()
        .enumerate()
        .map(|(index, param)| (param.clone(), index + 1))
        .collect()
}

fn atom_base_index(base: &AtomBase, params: &BTreeMap<String, usize>) -> Result<usize> {
    match base {
        AtomBase::Zero => Ok(0),
        AtomBase::Param(name) => params
            .get(name)
            .copied()
            .ok_or_else(|| Error::UnknownUniverseParam(name.clone())),
    }
}

fn normalize_constraint(constraint: &UniverseConstraint) -> UniverseConstraint {
    UniverseConstraint {
        lhs: normalize_level(constraint.lhs.clone()),
        relation: constraint.relation,
        rhs: normalize_level(constraint.rhs.clone()),
    }
}

fn decompose_constraint(constraint: &UniverseConstraint) -> Result<Vec<AtomInequality>> {
    let normalized = normalize_constraint(constraint);
    match normalized.relation {
        UniverseConstraintRelation::Le => decompose_le_constraint(normalized.lhs, normalized.rhs),
        UniverseConstraintRelation::Eq => {
            if normalized.lhs == normalized.rhs {
                return Ok(Vec::new());
            }
            let mut inequalities =
                decompose_le_constraint(normalized.lhs.clone(), normalized.rhs.clone())?;
            inequalities.extend(decompose_le_constraint(normalized.rhs, normalized.lhs)?);
            Ok(inequalities)
        }
    }
}

fn decompose_le_constraint(lhs: Level, rhs: Level) -> Result<Vec<AtomInequality>> {
    let lhs = normalize_level(lhs);
    let rhs = normalize_level(rhs);
    if lhs == rhs {
        return Ok(Vec::new());
    }
    let lhs_atoms = decompose_lhs_level_expr(&lhs)?;
    let rhs_atoms = decompose_level_expr(&rhs)?;
    let [rhs_atom] = rhs_atoms.as_slice() else {
        return Err(Error::UnsupportedUniverseConstraint {
            constraint: UniverseConstraint::le(lhs, rhs),
        });
    };
    Ok(lhs_atoms
        .into_iter()
        .map(|lhs| AtomInequality {
            lhs,
            rhs: rhs_atom.clone(),
        })
        .collect())
}

fn decompose_level_expr(level: &Level) -> Result<Vec<Atom>> {
    match normalize_level(level.clone()) {
        Level::Max(lhs, rhs) => {
            let mut atoms = decompose_level_expr(&lhs)?;
            atoms.extend(decompose_level_expr(&rhs)?);
            atoms.sort();
            atoms.dedup();
            Ok(atoms)
        }
        level => Ok(vec![decompose_atom(&level)?]),
    }
}

/// Conservatively decomposes a universe expression used on the left of `<=`.
///
/// `imax(a, b) <= max(a, b)` holds for every universe valuation: when `b = 0`
/// the left side is `0`, and otherwise it is `max(a, b)`. Replacing a left-hand
/// `imax` by `max` can therefore only reject additional valid constraints; it
/// cannot admit an invalid one. The right-hand side deliberately continues to
/// use `decompose_level_expr` and fails closed on symbolic `imax`, where the
/// same replacement would be unsound.
fn decompose_lhs_level_expr(level: &Level) -> Result<Vec<Atom>> {
    match normalize_level(level.clone()) {
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            let mut atoms = decompose_lhs_level_expr(&lhs)?;
            atoms.extend(decompose_lhs_level_expr(&rhs)?);
            atoms.sort();
            atoms.dedup();
            Ok(atoms)
        }
        level => Ok(vec![decompose_atom(&level)?]),
    }
}

fn decompose_atom(level: &Level) -> Result<Atom> {
    match normalize_level(level.clone()) {
        Level::Zero => Ok(Atom {
            base: AtomBase::Zero,
            offset: 0,
        }),
        Level::Param(name) => Ok(Atom {
            base: AtomBase::Param(name),
            offset: 0,
        }),
        Level::Succ(inner) => {
            let mut atom = decompose_atom(&inner)?;
            atom.offset =
                atom.offset
                    .checked_add(1)
                    .ok_or_else(|| Error::UnsupportedUniverseConstraint {
                        constraint: UniverseConstraint::le(level.clone(), level.clone()),
                    })?;
            offset_bound(&atom)?;
            Ok(atom)
        }
        _ => Err(Error::UnsupportedUniverseConstraint {
            constraint: UniverseConstraint::le(level.clone(), level.clone()),
        }),
    }
}

fn offset_bound(atom: &Atom) -> Result<i64> {
    i64::try_from(atom.offset).map_err(|_| Error::UnsupportedUniverseConstraint {
        constraint: UniverseConstraint::le(Level::Zero, Level::Zero),
    })
}

fn substitute_level(level: &Level, params: &[String], levels: &[Level]) -> Level {
    match level {
        Level::Zero => Level::Zero,
        Level::Succ(inner) => normalize_level(Level::succ(substitute_level(inner, params, levels))),
        Level::Max(lhs, rhs) => Level::max(
            substitute_level(lhs, params, levels),
            substitute_level(rhs, params, levels),
        ),
        Level::IMax(lhs, rhs) => Level::imax(
            substitute_level(lhs, params, levels),
            substitute_level(rhs, params, levels),
        ),
        Level::Param(name) => params
            .iter()
            .position(|param| param == name)
            .map(|index| levels[index].clone())
            .unwrap_or_else(|| Level::Param(name.clone())),
    }
}

pub fn level_eq(lhs: &Level, rhs: &Level) -> bool {
    normalize_level(lhs.clone()) == normalize_level(rhs.clone())
}

pub fn levels_eq(lhs: &[Level], rhs: &[Level]) -> bool {
    lhs.len() == rhs.len() && lhs.iter().zip(rhs).all(|(lhs, rhs)| level_eq(lhs, rhs))
}

fn level_as_nat(level: &Level) -> Option<u32> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(level) => Some(level_as_nat(level)? + 1),
        _ => None,
    }
}

fn level_from_nat(n: u32) -> Level {
    (0..n).fold(Level::Zero, |level, _| Level::succ(level))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn max_zero_normalizes_to_other_level() {
        let u = Level::succ(Level::param("u"));

        assert!(level_eq(&Level::max(Level::zero(), u.clone()), &u));
        assert!(level_eq(&Level::max(u.clone(), Level::zero()), &u));
        assert!(level_eq(&Level::imax(Level::zero(), u.clone()), &u));
    }

    #[test]
    fn universe_constraints_accept_empty_and_max_le() {
        let delta =
            validate_universe_params(&["u".to_owned(), "v".to_owned(), "w".to_owned()]).unwrap();
        let constraint = UniverseConstraint::le(
            Level::max(Level::param("u"), Level::param("v")),
            Level::param("w"),
        );

        ensure_universe_constraints_wf(&delta, &[]).unwrap();
        ensure_universe_constraints_wf(&delta, &[constraint]).unwrap();
    }

    #[test]
    fn universe_context_accepts_supported_fragment_and_entails_transitively() {
        let context = UniverseContext::new(
            vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
            vec![
                UniverseConstraint::le(Level::param("u"), Level::param("v")),
                UniverseConstraint::le(Level::param("v"), Level::param("w")),
            ],
        )
        .unwrap();

        context
            .entails(&[UniverseConstraint::le(Level::param("u"), Level::param("w"))])
            .unwrap();
        context
            .entails(&[UniverseConstraint::le(
                Level::max(Level::param("u"), Level::param("v")),
                Level::param("w"),
            )])
            .unwrap();
    }

    #[test]
    fn universe_context_entails_obligations_with_max_on_the_right() {
        let context = UniverseContext::new(
            vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
            vec![UniverseConstraint::le(Level::param("u"), Level::param("v"))],
        )
        .unwrap();

        assert!(context
            .entails_level_le(
                &Level::param("u"),
                &Level::max(Level::param("v"), Level::param("w")),
            )
            .unwrap());
        context
            .entails(&[UniverseConstraint::le(
                Level::param("u"),
                Level::max(Level::param("v"), Level::param("w")),
            )])
            .unwrap();
        assert!(!context
            .entails_level_le(
                &Level::succ(Level::param("v")),
                &Level::max(Level::param("u"), Level::param("w")),
            )
            .unwrap());
    }

    #[test]
    fn universe_context_bounds_left_imax_by_corresponding_max() {
        let context = UniverseContext::from_params(vec!["u".to_owned()]).unwrap();
        let one = Level::succ(Level::zero());
        let u = Level::param("u");

        assert!(context
            .entails_level_le(&Level::imax(one.clone(), u.clone()), &Level::max(one, u),)
            .unwrap());
    }

    #[test]
    fn universe_context_keeps_symbolic_imax_on_right_fail_closed() {
        let context = UniverseContext::from_params(vec!["u".to_owned()]).unwrap();
        let one = Level::succ(Level::zero());
        let u = Level::param("u");
        let rhs = Level::IMax(Box::new(one.clone()), Box::new(u.clone()));

        assert_eq!(
            context.entails_level_le(&Level::max(one, u), &rhs),
            Err(Error::UnsupportedUniverseConstraint {
                constraint: UniverseConstraint::le(rhs.clone(), rhs),
            })
        );
    }

    #[test]
    fn universe_context_bounds_max_obligation_atom_pairs() {
        let params = (0..64)
            .map(|index| format!("u{index:03}"))
            .collect::<Vec<_>>();
        let context = UniverseContext::from_params(params.clone()).unwrap();
        let max_levels = |names: &[String]| {
            names.iter().fold(Level::zero(), |level, name| {
                Level::max(level, Level::param(name.clone()))
            })
        };
        let lhs = max_levels(&params[..32]);
        let rhs = max_levels(&params[31..]);

        assert_eq!(
            context.entails_level_le(&lhs, &rhs),
            Err(Error::ResourceLimit {
                kind: ResourceLimitKind::UniverseConstraints,
            })
        );
    }

    #[test]
    fn universe_context_rejects_unsatisfiable_constraints() {
        assert_eq!(
            UniverseContext::new(
                vec!["u".to_owned()],
                vec![UniverseConstraint::le(
                    Level::succ(Level::param("u")),
                    Level::param("u")
                )],
            ),
            Err(Error::UnsatisfiableUniverseConstraints)
        );
        assert_eq!(
            UniverseContext::new(
                Vec::new(),
                vec![UniverseConstraint::le(
                    Level::succ(Level::zero()),
                    Level::zero()
                )],
            ),
            Err(Error::UnsatisfiableUniverseConstraints)
        );
    }

    #[test]
    fn universe_context_rejects_unsupported_constraints_closed() {
        let unsupported = UniverseConstraint::le(
            Level::param("u"),
            Level::max(Level::param("v"), Level::param("w")),
        );
        assert_eq!(
            UniverseContext::new(
                vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                vec![unsupported.clone()],
            ),
            Err(Error::UnsupportedUniverseConstraint {
                constraint: unsupported
            })
        );
    }

    #[test]
    fn universe_context_entailment_reports_violation() {
        let context = UniverseContext::from_params(vec!["u".to_owned()]).unwrap();
        assert_eq!(
            context.entails(&[UniverseConstraint::le(
                Level::succ(Level::param("u")),
                Level::param("u"),
            )]),
            Err(Error::UniverseConstraintViolation {
                declaration: String::new(),
                constraint: UniverseConstraint::le(
                    Level::succ(Level::param("u")),
                    Level::param("u")
                ),
            })
        );
    }

    #[test]
    fn universe_context_fast_paths_and_resource_limits_are_deterministic() {
        UniverseContext::empty().entails(&[]).unwrap();
        UniverseContext::new(vec!["u".to_owned()], Vec::new())
            .unwrap()
            .entails(&[])
            .unwrap();

        let too_many_params = (0..MAX_UNIVERSE_CONTEXT_NODES)
            .map(|index| format!("u{index:03}"))
            .collect::<Vec<_>>();
        assert_eq!(
            UniverseContext::from_params(too_many_params),
            Err(Error::ResourceLimit {
                kind: ResourceLimitKind::UniverseConstraints,
            })
        );
    }

    #[test]
    fn universe_context_substitutes_and_canonicalizes_obligations() {
        let context = UniverseContext::empty();
        let mut constraints = vec![
            UniverseConstraint::le(Level::param("u"), Level::param("v")),
            UniverseConstraint::le(Level::param("v"), Level::param("u")),
        ];
        constraints.sort();

        let obligations = context
            .substitute_constraints(
                &["u".to_owned(), "v".to_owned()],
                &[Level::zero(), Level::zero()],
                &constraints,
            )
            .unwrap();
        assert_eq!(
            obligations,
            vec![UniverseConstraint::le(Level::zero(), Level::zero())]
        );
    }

    #[test]
    fn universe_params_reject_duplicate_and_noncanonical_order() {
        assert_eq!(
            validate_universe_params(&["u".to_owned(), "u".to_owned()]),
            Err(Error::DuplicateUniverseParam("u".to_owned()))
        );
        assert_eq!(
            validate_universe_params(&["v".to_owned(), "u".to_owned()]),
            Err(Error::NonCanonicalUniverseParams(vec![
                "v".to_owned(),
                "u".to_owned()
            ]))
        );
    }

    #[test]
    fn universe_params_reject_unresolved_meta_names() {
        assert_eq!(
            validate_universe_params(&["?u".to_owned()]),
            Err(Error::UnresolvedUniverseMeta("?u".to_owned()))
        );
        assert_eq!(
            ensure_level_wf(&["u".to_owned()], &Level::param("z?meta")),
            Err(Error::UnresolvedUniverseMeta("z?meta".to_owned()))
        );
        assert_eq!(
            validate_universe_params(&[format!("{HUMAN_UNIVERSE_META_PREFIX}0")]),
            Err(Error::UnresolvedUniverseMeta(format!(
                "{HUMAN_UNIVERSE_META_PREFIX}0"
            )))
        );
    }

    #[test]
    fn universe_constraints_reject_unknown_and_noncanonical_levels() {
        let delta = validate_universe_params(&["u".to_owned(), "v".to_owned()]).unwrap();
        let unknown = UniverseConstraint::le(Level::param("u"), Level::param("w"));
        assert_eq!(
            ensure_universe_constraints_wf(&delta, &[unknown]),
            Err(Error::UnknownUniverseParam("w".to_owned()))
        );

        let noncanonical = UniverseConstraint::le(
            Level::Max(Box::new(Level::param("v")), Box::new(Level::param("u"))),
            Level::param("v"),
        );
        assert_eq!(
            ensure_universe_constraints_wf(&delta, std::slice::from_ref(&noncanonical)),
            Err(Error::NonCanonicalUniverseLevel {
                level: noncanonical.lhs,
            })
        );
    }
}
