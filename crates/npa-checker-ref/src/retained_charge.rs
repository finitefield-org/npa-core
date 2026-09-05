//! Deterministic logical retained-size accounting for reference import stores.

use crate::{
    decode::ReferenceUniverseConstraint, ReferenceAxiomDependency, ReferenceCoreExpr,
    ReferenceCoreGlobalRef, ReferenceCoreLevel, ReferenceImportEntry, ReferenceImportStore,
    ReferenceModuleName, ReferencePublicEnvironment, ReferencePublicExport,
    ReferencePublicInductiveGroup, ReferencePublicInductiveLayout,
    ReferenceStructuralClosureSummary, ReferenceStructuralIdentity,
};

pub(crate) const CACHE_ENTRY_OVERHEAD_BYTES_V1: u64 = 128;
pub(crate) const ARC_METADATA_BYTES_V1: u64 = 64;
pub(crate) const PAYLOAD_CHARGE_METADATA_BYTES_V1: u64 = 16;
#[allow(dead_code)]
pub(crate) const CACHE_ENTRY_LIMIT_V1: usize = 1_024;
pub(crate) const CACHE_RETAINED_BYTE_LIMIT_V1: u64 = 536_870_912;

const STRING_INLINE: u64 = 24;
const VEC_INLINE: u64 = 24;
const MAP_INLINE: u64 = 24;
const ARC_INLINE: u64 = 8;
const ID_INLINE: u64 = 8;
const HASH_INLINE: u64 = 32;
const TAG_INLINE: u64 = 8;
const BOOL_INLINE: u64 = 1;
// `ReferenceCoreFeature` is currently uninhabited. Like the certificate-side
// profile, its `Vec` can report `usize::MAX` capacity as a zero-sized
// allocation and therefore carries no retained bytes.
const CORE_FEATURE_INLINE: u64 = 0;

const NAME_INLINE: u64 = VEC_INLINE;
const LEVEL_INLINE: u64 = TAG_INLINE + NAME_INLINE;
const GLOBAL_REF_INLINE: u64 = TAG_INLINE + ID_INLINE + NAME_INLINE + HASH_INLINE;
const EXPR_INLINE: u64 = TAG_INLINE + GLOBAL_REF_INLINE + VEC_INLINE;
const STRUCTURAL_IDENTITY_INLINE: u64 = NAME_INLINE + 2 * HASH_INLINE;
const PUBLIC_IMPORT_INLINE: u64 = NAME_INLINE + HASH_INLINE + TAG_INLINE + HASH_INLINE;
const AXIOM_DEP_INLINE: u64 = NAME_INLINE + HASH_INLINE + GLOBAL_REF_INLINE;
const PUBLIC_RECURSOR_INLINE: u64 = NAME_INLINE + 2 * ID_INLINE;
const OPTIONAL_PUBLIC_RECURSOR_INLINE: u64 = TAG_INLINE + PUBLIC_RECURSOR_INLINE;
const PUBLIC_INDUCTIVE_INLINE: u64 =
    NAME_INLINE + 2 * ID_INLINE + VEC_INLINE + OPTIONAL_PUBLIC_RECURSOR_INLINE;
const PUBLIC_GROUP_INLINE: u64 = HASH_INLINE + VEC_INLINE;
const UNIVERSE_CONSTRAINT_INLINE: u64 = 2 * LEVEL_INLINE + TAG_INLINE;
const PUBLIC_EXPORT_INLINE: u64 = NAME_INLINE
    + TAG_INLINE
    + HASH_INLINE
    + VEC_INLINE
    + VEC_INLINE
    + VEC_INLINE
    + EXPR_INLINE
    + TAG_INLINE
    + EXPR_INLINE;
const IMPORT_ENTRY_INLINE: u64 =
    NAME_INLINE + 3 * HASH_INLINE + ARC_INLINE + BOOL_INLINE + ID_INLINE + TAG_INLINE + MAP_INLINE;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Charge(u64);

impl Charge {
    fn add(&mut self, bytes: u64) {
        if self.saturated() {
            self.0 = u64::MAX;
            return;
        }
        self.0 = self
            .0
            .checked_add(bytes)
            .filter(|total| *total <= CACHE_RETAINED_BYTE_LIMIT_V1)
            .unwrap_or(u64::MAX);
    }

    fn add_capacity(&mut self, capacity: usize, inline: u64) {
        let capacity = u64::try_from(capacity).unwrap_or(u64::MAX);
        self.add(capacity.saturating_mul(inline));
    }

    fn saturated(self) -> bool {
        self.0 == u64::MAX || self.0 > CACHE_RETAINED_BYTE_LIMIT_V1
    }
}

fn name_owned(charge: &mut Charge, name: &ReferenceModuleName) {
    charge.add_capacity(name.components.capacity(), STRING_INLINE);
    if charge.saturated() {
        return;
    }
    for component in &name.components {
        charge.add_capacity(component.capacity(), 1);
        if charge.saturated() {
            return;
        }
    }
}

fn global_ref_owned(charge: &mut Charge, global_ref: &ReferenceCoreGlobalRef) {
    if charge.saturated() {
        return;
    }
    match global_ref {
        ReferenceCoreGlobalRef::Builtin { name, .. }
        | ReferenceCoreGlobalRef::Imported { name, .. }
        | ReferenceCoreGlobalRef::LocalGenerated { name, .. } => name_owned(charge, name),
        ReferenceCoreGlobalRef::Local { .. } => {}
    }
}

fn reserve_or_saturate<T>(stack: &mut Vec<T>, additional: usize, charge: &mut Charge) -> bool {
    if stack.try_reserve(additional).is_err() {
        charge.0 = u64::MAX;
        false
    } else {
        true
    }
}

fn level_owned(charge: &mut Charge, root: &ReferenceCoreLevel) {
    let mut stack = Vec::new();
    if !reserve_or_saturate(&mut stack, 1, charge) {
        return;
    }
    stack.push(root);
    while let Some(level) = stack.pop() {
        match level {
            ReferenceCoreLevel::Zero => {}
            ReferenceCoreLevel::Param(name) => name_owned(charge, name),
            ReferenceCoreLevel::Succ(child) => {
                charge.add(ARC_METADATA_BYTES_V1 + LEVEL_INLINE);
                if charge.saturated() {
                    return;
                }
                if !reserve_or_saturate(&mut stack, 1, charge) {
                    return;
                }
                stack.push(child.as_ref());
            }
            ReferenceCoreLevel::Max(lhs, rhs) | ReferenceCoreLevel::IMax(lhs, rhs) => {
                charge.add(2 * (ARC_METADATA_BYTES_V1 + LEVEL_INLINE));
                if charge.saturated() {
                    return;
                }
                if !reserve_or_saturate(&mut stack, 2, charge) {
                    return;
                }
                stack.push(rhs.as_ref());
                stack.push(lhs.as_ref());
            }
        }
        if charge.saturated() {
            charge.0 = u64::MAX;
            return;
        }
    }
}

fn expr_owned(charge: &mut Charge, root: &ReferenceCoreExpr) {
    let mut expr_stack = Vec::new();
    if !reserve_or_saturate(&mut expr_stack, 1, charge) {
        return;
    }
    expr_stack.push(root);
    while let Some(expr) = expr_stack.pop() {
        match expr {
            ReferenceCoreExpr::Sort(level) => level_owned(charge, level),
            ReferenceCoreExpr::BVar(_) => {}
            ReferenceCoreExpr::Const { global_ref, levels } => {
                global_ref_owned(charge, global_ref);
                if charge.saturated() {
                    return;
                }
                charge.add_capacity(levels.capacity(), LEVEL_INLINE);
                if charge.saturated() {
                    return;
                }
                for level in levels {
                    level_owned(charge, level);
                    if charge.saturated() {
                        return;
                    }
                }
            }
            ReferenceCoreExpr::App(fun, arg)
            | ReferenceCoreExpr::Lam { ty: fun, body: arg }
            | ReferenceCoreExpr::Pi { ty: fun, body: arg } => {
                charge.add(2 * (ARC_METADATA_BYTES_V1 + EXPR_INLINE));
                if charge.saturated() {
                    return;
                }
                if !reserve_or_saturate(&mut expr_stack, 2, charge) {
                    return;
                }
                expr_stack.push(arg.as_ref());
                expr_stack.push(fun.as_ref());
            }
        }
        if charge.saturated() {
            charge.0 = u64::MAX;
            return;
        }
    }
}

fn universe_constraint_owned(charge: &mut Charge, constraint: &ReferenceUniverseConstraint) {
    level_owned(charge, &constraint.lhs);
    if charge.saturated() {
        return;
    }
    level_owned(charge, &constraint.rhs);
}

fn axiom_owned(charge: &mut Charge, axiom: &ReferenceAxiomDependency) {
    name_owned(charge, &axiom.name);
    if charge.saturated() {
        return;
    }
    global_ref_owned(charge, &axiom.global_ref);
}

fn export_owned(charge: &mut Charge, export: &ReferencePublicExport) {
    name_owned(charge, &export.name);
    if charge.saturated() {
        return;
    }
    charge.add_capacity(export.axiom_dependencies.capacity(), AXIOM_DEP_INLINE);
    for axiom in &export.axiom_dependencies {
        axiom_owned(charge, axiom);
        if charge.saturated() {
            return;
        }
    }
    charge.add_capacity(export.universe_params.capacity(), NAME_INLINE);
    for name in &export.universe_params {
        name_owned(charge, name);
        if charge.saturated() {
            return;
        }
    }
    charge.add_capacity(
        export.universe_constraints.capacity(),
        UNIVERSE_CONSTRAINT_INLINE,
    );
    for constraint in &export.universe_constraints {
        universe_constraint_owned(charge, constraint);
        if charge.saturated() {
            return;
        }
    }
    expr_owned(charge, &export.ty);
    if charge.saturated() {
        return;
    }
    if let Some(body) = &export.body {
        expr_owned(charge, body);
    }
}

fn inductive_layout_owned(charge: &mut Charge, layout: &ReferencePublicInductiveLayout) {
    name_owned(charge, &layout.name);
    if charge.saturated() {
        return;
    }
    charge.add_capacity(layout.constructors.capacity(), NAME_INLINE);
    for constructor in &layout.constructors {
        name_owned(charge, constructor);
        if charge.saturated() {
            return;
        }
    }
    if let Some(recursor) = &layout.recursor {
        name_owned(charge, &recursor.name);
    }
}

fn inductive_group_owned(charge: &mut Charge, group: &ReferencePublicInductiveGroup) {
    charge.add_capacity(group.families.capacity(), PUBLIC_INDUCTIVE_INLINE);
    for family in &group.families {
        inductive_layout_owned(charge, family);
        if charge.saturated() {
            return;
        }
    }
}

fn environment_owned(charge: &mut Charge, environment: &ReferencePublicEnvironment) {
    charge.add_capacity(environment.imports.capacity(), PUBLIC_IMPORT_INLINE);
    if charge.saturated() {
        return;
    }
    for import in &environment.imports {
        name_owned(charge, &import.module);
        if charge.saturated() {
            return;
        }
    }

    charge.add_capacity(environment.exports.capacity(), PUBLIC_EXPORT_INLINE);
    if charge.saturated() {
        return;
    }
    for export in &environment.exports {
        export_owned(charge, export);
        if charge.saturated() {
            return;
        }
    }

    charge.add_capacity(environment.module_axioms.capacity(), AXIOM_DEP_INLINE);
    if charge.saturated() {
        return;
    }
    for axiom in &environment.module_axioms {
        axiom_owned(charge, axiom);
        if charge.saturated() {
            return;
        }
    }

    charge.add_capacity(environment.core_features.capacity(), CORE_FEATURE_INLINE);
    if charge.saturated() {
        return;
    }
    charge.add_capacity(environment.inductive_groups.capacity(), PUBLIC_GROUP_INLINE);
    if charge.saturated() {
        return;
    }
    for group in &environment.inductive_groups {
        inductive_group_owned(charge, group);
        if charge.saturated() {
            return;
        }
    }
}

fn structural_identity_owned(charge: &mut Charge, identity: &ReferenceStructuralIdentity) {
    name_owned(charge, &identity.module);
}

fn structural_closure_owned(charge: &mut Charge, closure: &ReferenceStructuralClosureSummary) {
    for identity in closure.modules.keys() {
        charge.add(CACHE_ENTRY_OVERHEAD_BYTES_V1);
        charge.add(STRUCTURAL_IDENTITY_INLINE + ID_INLINE);
        structural_identity_owned(charge, identity);
        if charge.saturated() {
            return;
        }
    }
}

fn entry_owned(charge: &mut Charge, entry: &ReferenceImportEntry) {
    name_owned(charge, &entry.module);
    if charge.saturated() {
        return;
    }
    charge.add(ARC_METADATA_BYTES_V1 + 5 * VEC_INLINE);
    if charge.saturated() {
        return;
    }
    environment_owned(charge, entry.public_environment.as_ref());
    if charge.saturated() {
        return;
    }
    if let Some(closure) = &entry.structural_closure {
        structural_closure_owned(charge, closure);
    }
}

impl ReferenceImportStore {
    /// Return the target-independent v1 logical retained-size charge.
    ///
    /// Shared expression and environment allocations are conservatively
    /// charged once for each retaining edge; pointer identity is never an input.
    pub fn logical_retained_bytes_v1(&self) -> u64 {
        let mut charge = store_base_charge(self.entries.capacity());
        if charge.saturated() {
            return u64::MAX;
        }
        for entry in &self.entries {
            entry_owned(&mut charge, entry);
            if charge.saturated() {
                return u64::MAX;
            }
        }
        charge.0
    }
}

fn store_base_charge(entries_capacity: usize) -> Charge {
    let mut charge = Charge(VEC_INLINE + PAYLOAD_CHARGE_METADATA_BYTES_V1);
    charge.add_capacity(entries_capacity, IMPORT_ENTRY_INLINE);
    charge
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, sync::Arc};

    use super::*;

    fn fixed_name(value: &str) -> ReferenceModuleName {
        let mut component = String::with_capacity(8);
        component.push_str(value);
        let components = vec![component];
        ReferenceModuleName::new(components).unwrap()
    }

    fn import_entry(
        module: &str,
        public_environment: Arc<ReferencePublicEnvironment>,
    ) -> ReferenceImportEntry {
        ReferenceImportEntry::new(
            crate::ReferenceModuleIdentity::new(fixed_name(module), [1; 32], [2; 32], [3; 32]),
            public_environment,
            true,
            0,
            Some(ReferenceStructuralClosureSummary::default()),
        )
    }

    #[test]
    fn retained_charge_golden_empty_store_is_target_independent() {
        let store = ReferenceImportStore::default();
        assert_eq!(store.logical_retained_bytes_v1(), 40);
    }

    #[test]
    fn logical_retained_bytes_v1() {
        let empty = ReferenceImportStore::default();
        assert_eq!(empty.logical_retained_bytes_v1(), 40);

        let environment = Arc::new(ReferencePublicEnvironment::new(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        ));
        let populated =
            ReferenceImportStore::from_entries(vec![import_entry("Contract", environment)])
                .unwrap();
        assert!(populated.logical_retained_bytes_v1() > empty.logical_retained_bytes_v1());
        assert_ne!(populated.logical_retained_bytes_v1(), u64::MAX);
    }

    #[test]
    fn charge_profile_matches_npa_cert() {
        assert_eq!(
            CACHE_ENTRY_OVERHEAD_BYTES_V1,
            npa_cert::PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1
        );
        assert_eq!(
            ARC_METADATA_BYTES_V1,
            npa_cert::PACKAGE_SHARED_ARC_METADATA_BYTES_V1
        );
        assert_eq!(
            PAYLOAD_CHARGE_METADATA_BYTES_V1,
            npa_cert::PACKAGE_SHARED_PAYLOAD_CHARGE_METADATA_BYTES_V1
        );
        assert_eq!(
            CACHE_ENTRY_LIMIT_V1,
            npa_cert::PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1
        );
        assert_eq!(
            CACHE_RETAINED_BYTE_LIMIT_V1,
            npa_cert::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1
        );
    }

    #[test]
    fn retained_charge_golden_counts_aliases_per_edge() {
        let leaf = Arc::new(ReferenceCoreExpr::BVar(0));
        let diamond = ReferenceCoreExpr::App(
            Arc::new(ReferenceCoreExpr::App(leaf.clone(), leaf.clone())),
            Arc::new(ReferenceCoreExpr::App(leaf.clone(), leaf)),
        );
        let mut charge = Charge::default();
        expr_owned(&mut charge, &diamond);
        assert_eq!(charge.0, 6 * (ARC_METADATA_BYTES_V1 + EXPR_INLINE));
    }

    #[test]
    fn retained_charge_golden_nested_expression_inductive_and_closure_shapes() {
        let leaf = Arc::new(ReferenceCoreExpr::BVar(0));
        let nested = ReferenceCoreExpr::Pi {
            ty: Arc::clone(&leaf),
            body: leaf,
        };
        let mut expression_charge = Charge::default();
        expr_owned(&mut expression_charge, &nested);
        assert_eq!(
            expression_charge.0,
            2 * (ARC_METADATA_BYTES_V1 + EXPR_INLINE)
        );

        let constructors = vec![fixed_name("Ctor")];
        let layout = ReferencePublicInductiveLayout {
            name: fixed_name("Family"),
            param_count: 0,
            index_count: 0,
            constructors,
            recursor: Some(crate::ReferencePublicRecursorLayout {
                name: fixed_name("rec"),
                minor_start: 0,
                major_index: 0,
            }),
        };
        let families = vec![layout];
        let group = ReferencePublicInductiveGroup {
            decl_interface_hash: [4; 32],
            families,
        };
        let mut inductive_charge = Charge::default();
        inductive_group_owned(&mut inductive_charge, &group);
        assert_eq!(inductive_charge.0, 232);

        let identity = ReferenceStructuralIdentity {
            module: fixed_name("Module"),
            export_hash: [5; 32],
            certificate_hash: [6; 32],
        };
        let closure = ReferenceStructuralClosureSummary {
            modules: BTreeMap::from([(identity, 0)]),
        };
        let mut closure_charge = Charge::default();
        structural_closure_owned(&mut closure_charge, &closure);
        assert_eq!(closure_charge.0, 256);
    }

    #[test]
    fn retained_charge_golden_public_environment_aliases_are_charged_per_edge() {
        let environment = Arc::new(ReferencePublicEnvironment::new(
            vec![(fixed_name("Import"), [7; 32], Some([8; 32]))],
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        ));
        let mut environment_charge = Charge::default();
        environment_owned(&mut environment_charge, &environment);
        assert_eq!(environment_charge.0, PUBLIC_IMPORT_INLINE + 32);

        let first = import_entry("First", Arc::clone(&environment));
        let second = import_entry("Other", Arc::clone(&environment));
        let mut first_charge = Charge::default();
        entry_owned(&mut first_charge, &first);
        let mut second_charge = Charge::default();
        entry_owned(&mut second_charge, &second);
        assert_eq!(first_charge, second_charge);

        let mut aliased_charge = Charge::default();
        entry_owned(&mut aliased_charge, &first);
        entry_owned(&mut aliased_charge, &second);
        assert_eq!(aliased_charge.0, first_charge.0.saturating_mul(2));
        assert_ne!(aliased_charge.0, u64::MAX);
    }

    #[test]
    fn retained_charge_golden_empty_over_limit_capacity_and_early_stop_saturate() {
        let over_limit_capacity =
            usize::try_from(CACHE_RETAINED_BYTE_LIMIT_V1 / IMPORT_ENTRY_INLINE + 1).unwrap();
        assert_eq!(store_base_charge(over_limit_capacity).0, u64::MAX);

        let environment = ReferencePublicEnvironment::new(
            vec![(fixed_name("Import"), [9; 32], None)],
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let mut charge = Charge(CACHE_RETAINED_BYTE_LIMIT_V1);
        environment_owned(&mut charge, &environment);
        assert_eq!(charge.0, u64::MAX);
    }

    #[test]
    fn shared_payload_differential() {
        let environment = Arc::new(ReferencePublicEnvironment::new(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        ));
        let first = import_entry("First", Arc::clone(&environment));
        let second = import_entry("Second", environment);
        let first_only = ReferenceImportStore::from_entries(vec![first.clone()]).unwrap();
        let independently_built = first_only.clone();
        assert_eq!(
            first_only.logical_retained_bytes_v1(),
            independently_built.logical_retained_bytes_v1()
        );

        let both = ReferenceImportStore::from_entries(vec![first, second]).unwrap();
        assert!(both.logical_retained_bytes_v1() > first_only.logical_retained_bytes_v1());
    }
}
