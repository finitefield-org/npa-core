//! Target-independent logical retained-size accounting for shared certificate payloads.

/// Logical bytes charged for one combined decode-cache entry's bookkeeping.
pub const PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1: u64 = 128;

/// Logical bytes charged for one retained `Arc` allocation and its metadata.
pub const PACKAGE_SHARED_ARC_METADATA_BYTES_V1: u64 = 64;

/// Logical bytes charged for cached retained-size metadata on a shared payload.
pub const PACKAGE_SHARED_PAYLOAD_CHARGE_METADATA_BYTES_V1: u64 = 16;

/// Maximum number of entries retained by the combined decoded/reference cache.
pub const PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1: usize = 1_024;

/// Maximum logical retained bytes held by the combined decoded/reference cache.
pub const PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1: u64 = 536_870_912;

/// Saturating accumulator used by the v1 logical retained-size profile.
///
/// The profile deliberately never converts a host-layout `size_of` result into
/// proof-adjacent policy.  Once saturated, an accumulator remains saturated so
/// callers can conservatively reject cache admission.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct LogicalRetainedChargeV1(u64);

impl LogicalRetainedChargeV1 {
    pub(crate) const fn new() -> Self {
        Self(0)
    }

    pub(crate) fn add(&mut self, bytes: u64) {
        self.0 = self.0.saturating_add(bytes);
    }

    pub(crate) fn add_usize(&mut self, count: usize, bytes_each: u64) {
        let count = u64::try_from(count).unwrap_or(u64::MAX);
        self.add(count.saturating_mul(bytes_each));
    }

    pub(crate) const fn get(self) -> u64 {
        self.0
    }
}

const STRING_INLINE_BYTES_V1: u64 = 24;
const VEC_INLINE_BYTES_V1: u64 = 24;
const ARC_INLINE_BYTES_V1: u64 = 8;
const ID_INLINE_BYTES_V1: u64 = 8;
const HASH_INLINE_BYTES_V1: u64 = 32;
const ENUM_TAG_BYTES_V1: u64 = 8;

const NAME_INLINE_BYTES_V1: u64 = VEC_INLINE_BYTES_V1;
const IMPORT_ENTRY_INLINE_BYTES_V1: u64 =
    NAME_INLINE_BYTES_V1 + HASH_INLINE_BYTES_V1 + ENUM_TAG_BYTES_V1 + HASH_INLINE_BYTES_V1;
const LEVEL_NODE_INLINE_BYTES_V1: u64 = ENUM_TAG_BYTES_V1 + 2 * ID_INLINE_BYTES_V1;
const GLOBAL_REF_INLINE_BYTES_V1: u64 =
    ENUM_TAG_BYTES_V1 + 2 * ID_INLINE_BYTES_V1 + HASH_INLINE_BYTES_V1;
const TERM_NODE_INLINE_BYTES_V1: u64 =
    ENUM_TAG_BYTES_V1 + GLOBAL_REF_INLINE_BYTES_V1 + VEC_INLINE_BYTES_V1;
const UNIVERSE_CONSTRAINT_INLINE_BYTES_V1: u64 =
    ID_INLINE_BYTES_V1 + ENUM_TAG_BYTES_V1 + ID_INLINE_BYTES_V1;
const BINDER_TYPE_INLINE_BYTES_V1: u64 = ID_INLINE_BYTES_V1;
const CONSTRUCTOR_SPEC_INLINE_BYTES_V1: u64 = 2 * ID_INLINE_BYTES_V1;
const RECURSOR_RULES_INLINE_BYTES_V1: u64 = 2 * ID_INLINE_BYTES_V1;
const RECURSOR_SPEC_INLINE_BYTES_V1: u64 =
    ID_INLINE_BYTES_V1 + VEC_INLINE_BYTES_V1 + ID_INLINE_BYTES_V1 + RECURSOR_RULES_INLINE_BYTES_V1;
const OPTIONAL_RECURSOR_INLINE_BYTES_V1: u64 = ENUM_TAG_BYTES_V1 + RECURSOR_SPEC_INLINE_BYTES_V1;
const MUTUAL_INDUCTIVE_SPEC_INLINE_BYTES_V1: u64 = ID_INLINE_BYTES_V1
    + VEC_INLINE_BYTES_V1
    + VEC_INLINE_BYTES_V1
    + ID_INLINE_BYTES_V1
    + VEC_INLINE_BYTES_V1
    + OPTIONAL_RECURSOR_INLINE_BYTES_V1;
const DECL_PAYLOAD_INLINE_BYTES_V1: u64 = ENUM_TAG_BYTES_V1
    + ID_INLINE_BYTES_V1
    + 5 * VEC_INLINE_BYTES_V1
    + ID_INLINE_BYTES_V1
    + OPTIONAL_RECURSOR_INLINE_BYTES_V1;
const DEPENDENCY_ENTRY_INLINE_BYTES_V1: u64 =
    ENUM_TAG_BYTES_V1 + GLOBAL_REF_INLINE_BYTES_V1 + 2 * HASH_INLINE_BYTES_V1;
const AXIOM_REF_INLINE_BYTES_V1: u64 =
    GLOBAL_REF_INLINE_BYTES_V1 + ID_INLINE_BYTES_V1 + HASH_INLINE_BYTES_V1;
const DECL_CERT_INLINE_BYTES_V1: u64 =
    DECL_PAYLOAD_INLINE_BYTES_V1 + 2 * VEC_INLINE_BYTES_V1 + 2 * HASH_INLINE_BYTES_V1;
const EXPORT_ENTRY_INLINE_BYTES_V1: u64 = 248;
const DECL_AXIOM_REPORT_INLINE_BYTES_V1: u64 = ID_INLINE_BYTES_V1 + 2 * VEC_INLINE_BYTES_V1;
// `CoreFeature` is currently uninhabited; its vector may report `usize::MAX`
// capacity as a zero-sized allocation and therefore carries no retained bytes.
const CORE_FEATURE_INLINE_BYTES_V1: u64 = 0;

use crate::{
    AxiomRef, DeclAxiomReport, DeclCert, DeclPayload, ExportEntry, ModuleCertParts,
    MutualInductiveSpec, Name, RecursorSpec, TermNode,
};

fn charge_vec_capacity(
    charge: &mut LogicalRetainedChargeV1,
    capacity: usize,
    element_inline_bytes: u64,
) {
    charge.add_usize(capacity, element_inline_bytes);
}

fn charge_name_owned(charge: &mut LogicalRetainedChargeV1, name: &Name) {
    charge_vec_capacity(charge, name.0.capacity(), STRING_INLINE_BYTES_V1);
    for component in &name.0 {
        charge.add_usize(component.capacity(), 1);
    }
}

fn charge_axiom_ref_owned(_charge: &mut LogicalRetainedChargeV1, _axiom: &AxiomRef) {}

fn charge_recursor_owned(charge: &mut LogicalRetainedChargeV1, recursor: &RecursorSpec) {
    charge_vec_capacity(
        charge,
        recursor.universe_params.capacity(),
        ID_INLINE_BYTES_V1,
    );
}

fn charge_mutual_inductive_owned(
    charge: &mut LogicalRetainedChargeV1,
    inductive: &MutualInductiveSpec,
) {
    charge_vec_capacity(
        charge,
        inductive.params.capacity(),
        BINDER_TYPE_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        charge,
        inductive.indices.capacity(),
        BINDER_TYPE_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        charge,
        inductive.constructors.capacity(),
        CONSTRUCTOR_SPEC_INLINE_BYTES_V1,
    );
    if let Some(recursor) = &inductive.recursor {
        charge_recursor_owned(charge, recursor);
    }
}

fn charge_decl_payload_owned(charge: &mut LogicalRetainedChargeV1, payload: &DeclPayload) {
    match payload {
        DeclPayload::Axiom {
            universe_params, ..
        }
        | DeclPayload::Def {
            universe_params, ..
        }
        | DeclPayload::Theorem {
            universe_params, ..
        } => charge_vec_capacity(charge, universe_params.capacity(), ID_INLINE_BYTES_V1),
        DeclPayload::AxiomConstrained {
            universe_params,
            universe_constraints,
            ..
        }
        | DeclPayload::DefConstrained {
            universe_params,
            universe_constraints,
            ..
        }
        | DeclPayload::TheoremConstrained {
            universe_params,
            universe_constraints,
            ..
        } => {
            charge_vec_capacity(charge, universe_params.capacity(), ID_INLINE_BYTES_V1);
            charge_vec_capacity(
                charge,
                universe_constraints.capacity(),
                UNIVERSE_CONSTRAINT_INLINE_BYTES_V1,
            );
        }
        DeclPayload::Inductive {
            universe_params,
            params,
            indices,
            constructors,
            recursor,
            ..
        } => {
            charge_vec_capacity(charge, universe_params.capacity(), ID_INLINE_BYTES_V1);
            charge_vec_capacity(charge, params.capacity(), BINDER_TYPE_INLINE_BYTES_V1);
            charge_vec_capacity(charge, indices.capacity(), BINDER_TYPE_INLINE_BYTES_V1);
            charge_vec_capacity(
                charge,
                constructors.capacity(),
                CONSTRUCTOR_SPEC_INLINE_BYTES_V1,
            );
            if let Some(recursor) = recursor {
                charge_recursor_owned(charge, recursor);
            }
        }
        DeclPayload::InductiveConstrained {
            universe_params,
            universe_constraints,
            params,
            indices,
            constructors,
            recursor,
            ..
        } => {
            charge_vec_capacity(charge, universe_params.capacity(), ID_INLINE_BYTES_V1);
            charge_vec_capacity(
                charge,
                universe_constraints.capacity(),
                UNIVERSE_CONSTRAINT_INLINE_BYTES_V1,
            );
            charge_vec_capacity(charge, params.capacity(), BINDER_TYPE_INLINE_BYTES_V1);
            charge_vec_capacity(charge, indices.capacity(), BINDER_TYPE_INLINE_BYTES_V1);
            charge_vec_capacity(
                charge,
                constructors.capacity(),
                CONSTRUCTOR_SPEC_INLINE_BYTES_V1,
            );
            if let Some(recursor) = recursor {
                charge_recursor_owned(charge, recursor);
            }
        }
        DeclPayload::MutualInductiveBlock {
            universe_params,
            universe_constraints,
            inductives,
            ..
        } => {
            charge_vec_capacity(charge, universe_params.capacity(), ID_INLINE_BYTES_V1);
            charge_vec_capacity(
                charge,
                universe_constraints.capacity(),
                UNIVERSE_CONSTRAINT_INLINE_BYTES_V1,
            );
            charge_vec_capacity(
                charge,
                inductives.capacity(),
                MUTUAL_INDUCTIVE_SPEC_INLINE_BYTES_V1,
            );
            for inductive in inductives {
                charge_mutual_inductive_owned(charge, inductive);
            }
        }
    }
}

fn charge_decl_owned(charge: &mut LogicalRetainedChargeV1, declaration: &DeclCert) {
    charge_decl_payload_owned(charge, &declaration.decl);
    charge_vec_capacity(
        charge,
        declaration.dependencies.capacity(),
        DEPENDENCY_ENTRY_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        charge,
        declaration.axiom_dependencies.capacity(),
        AXIOM_REF_INLINE_BYTES_V1,
    );
    for axiom in &declaration.axiom_dependencies {
        charge_axiom_ref_owned(charge, axiom);
    }
}

fn charge_export_owned(charge: &mut LogicalRetainedChargeV1, export: &ExportEntry) {
    charge_vec_capacity(
        charge,
        export.universe_params.capacity(),
        ID_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        charge,
        export.universe_constraints.capacity(),
        UNIVERSE_CONSTRAINT_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        charge,
        export.axiom_dependencies.capacity(),
        AXIOM_REF_INLINE_BYTES_V1,
    );
}

fn charge_decl_axiom_report_owned(charge: &mut LogicalRetainedChargeV1, report: &DeclAxiomReport) {
    charge_vec_capacity(
        charge,
        report.direct_axioms.capacity(),
        AXIOM_REF_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        charge,
        report.transitive_axioms.capacity(),
        AXIOM_REF_INLINE_BYTES_V1,
    );
}

pub(crate) fn module_cert_logical_retained_bytes_v1(parts: &ModuleCertParts) -> u64 {
    let mut charge = LogicalRetainedChargeV1::new();
    charge.add(PACKAGE_SHARED_ARC_METADATA_BYTES_V1);
    charge.add(PACKAGE_SHARED_PAYLOAD_CHARGE_METADATA_BYTES_V1);

    // Fixed inline logical shape of the nine ModuleCert fields.  No Rust ABI
    // layout participates in this value.
    charge.add(3 * STRING_INLINE_BYTES_V1); // header: two strings and one Name/Vec handle
    charge.add(6 * VEC_INLINE_BYTES_V1); // imports through export_block
    charge.add(3 * VEC_INLINE_BYTES_V1); // axiom report
    charge.add(3 * HASH_INLINE_BYTES_V1); // module hashes

    charge.add_usize(parts.header.format.capacity(), 1);
    charge.add_usize(parts.header.core_spec.capacity(), 1);
    charge_name_owned(&mut charge, &parts.header.module);

    charge_vec_capacity(
        &mut charge,
        parts.imports.capacity(),
        IMPORT_ENTRY_INLINE_BYTES_V1,
    );
    for import in &parts.imports {
        charge_name_owned(&mut charge, &import.module);
    }

    charge_vec_capacity(
        &mut charge,
        parts.name_table.capacity(),
        NAME_INLINE_BYTES_V1,
    );
    for name in &parts.name_table {
        charge_name_owned(&mut charge, name);
    }

    charge_vec_capacity(
        &mut charge,
        parts.level_table.capacity(),
        LEVEL_NODE_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        &mut charge,
        parts.term_table.capacity(),
        TERM_NODE_INLINE_BYTES_V1,
    );
    for term in &parts.term_table {
        if let TermNode::Const { levels, .. } = term {
            charge_vec_capacity(&mut charge, levels.capacity(), ID_INLINE_BYTES_V1);
        }
    }

    charge_vec_capacity(
        &mut charge,
        parts.declarations.capacity(),
        DECL_CERT_INLINE_BYTES_V1,
    );
    for declaration in &parts.declarations {
        charge_decl_owned(&mut charge, declaration);
    }

    charge_vec_capacity(
        &mut charge,
        parts.export_block.capacity(),
        EXPORT_ENTRY_INLINE_BYTES_V1,
    );
    for export in &parts.export_block {
        charge_export_owned(&mut charge, export);
    }

    charge_vec_capacity(
        &mut charge,
        parts.axiom_report.per_declaration.capacity(),
        DECL_AXIOM_REPORT_INLINE_BYTES_V1,
    );
    for report in &parts.axiom_report.per_declaration {
        charge_decl_axiom_report_owned(&mut charge, report);
    }
    charge_vec_capacity(
        &mut charge,
        parts.axiom_report.module_axioms.capacity(),
        AXIOM_REF_INLINE_BYTES_V1,
    );
    charge_vec_capacity(
        &mut charge,
        parts.axiom_report.core_features.capacity(),
        CORE_FEATURE_INLINE_BYTES_V1,
    );

    charge.get()
}

pub(crate) fn verified_module_logical_retained_bytes_v1(
    certificate_charge: u64,
    closure: &crate::structural::StructuralClosureSummary,
) -> u64 {
    let mut charge = LogicalRetainedChargeV1::new();
    // The certificate charge accounts for the ModuleCert payload Arc. The
    // VerifiedModule owns a separate verified-payload Arc and must charge it
    // independently.
    charge.add(certificate_charge);
    charge.add(PACKAGE_SHARED_ARC_METADATA_BYTES_V1);
    charge.add(ARC_INLINE_BYTES_V1); // ModuleCert Arc handle in VerifiedModulePayload
    charge.add(PACKAGE_SHARED_PAYLOAD_CHARGE_METADATA_BYTES_V1);
    charge.add(VEC_INLINE_BYTES_V1); // deterministic logical map handle
    for identity in closure.modules.keys() {
        charge.add(PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1);
        charge.add(2 * HASH_INLINE_BYTES_V1 + NAME_INLINE_BYTES_V1 + ID_INLINE_BYTES_V1);
        charge_name_owned(&mut charge, &identity.module);
    }
    charge.get()
}

#[cfg(test)]
mod tests {
    use crate::{AxiomReport, CertHeader, ModuleCert, ModuleCertParts, ModuleHashes, Name};

    use super::{
        verified_module_logical_retained_bytes_v1, LogicalRetainedChargeV1,
        PACKAGE_SHARED_ARC_METADATA_BYTES_V1,
    };

    #[test]
    fn logical_retained_charge_v1_saturates_deterministically() {
        let mut charge = LogicalRetainedChargeV1::new();
        charge.add(7);
        charge.add_usize(3, 11);
        assert_eq!(charge.get(), 40);

        charge.add(u64::MAX - 40);
        assert_eq!(charge.get(), u64::MAX);
        charge.add(1);
        charge.add_usize(usize::MAX, u64::MAX);
        assert_eq!(charge.get(), u64::MAX);
    }

    fn empty_certificate_parts() -> ModuleCertParts {
        ModuleCertParts {
            header: CertHeader {
                format: String::new(),
                core_spec: String::new(),
                module: Name(Vec::new()),
            },
            imports: Vec::new(),
            name_table: Vec::new(),
            level_table: Vec::new(),
            term_table: Vec::new(),
            declarations: Vec::new(),
            export_block: Vec::new(),
            axiom_report: AxiomReport {
                per_declaration: Vec::new(),
                module_axioms: Vec::new(),
                core_features: Vec::new(),
            },
            hashes: ModuleHashes {
                export_hash: [0; 32],
                axiom_report_hash: [0; 32],
                certificate_hash: [0; 32],
            },
        }
    }

    fn empty_certificate_with_name_capacity(name_capacity: usize) -> ModuleCert {
        let mut parts = empty_certificate_parts();
        parts.name_table = Vec::with_capacity(name_capacity);
        ModuleCert::from_parts(parts)
    }

    #[test]
    fn logical_retained_charge_v1_is_capacity_sensitive_but_value_neutral() {
        let compact = empty_certificate_with_name_capacity(0);
        let reserved = empty_certificate_with_name_capacity(1);
        assert_eq!(compact, reserved);
        assert_eq!(compact.logical_retained_bytes_v1(), 464);
        assert_eq!(reserved.logical_retained_bytes_v1(), 488);
    }

    #[test]
    fn verified_module_logical_retained_charge_v1_includes_payload_arc() {
        let certificate = empty_certificate_with_name_capacity(0);
        let certificate_charge = certificate.logical_retained_bytes_v1();
        assert_eq!(certificate_charge, 464);
        assert_eq!(PACKAGE_SHARED_ARC_METADATA_BYTES_V1, 64);
        assert_eq!(super::ARC_INLINE_BYTES_V1, 8);
        assert_eq!(
            verified_module_logical_retained_bytes_v1(
                certificate_charge,
                &crate::structural::StructuralClosureSummary::default(),
            ),
            576,
        );
    }

    #[test]
    fn retained_charge_golden_certificate_field_shapes_and_capacity_boundaries() {
        fn retained(parts: ModuleCertParts) -> (ModuleCert, u64) {
            let certificate = ModuleCert::from_parts(parts);
            let charge = certificate.logical_retained_bytes_v1();
            (certificate, charge)
        }

        let (empty, base) = retained(empty_certificate_parts());
        assert_eq!(base, 464);
        assert_eq!(super::PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1, 128);
        assert_eq!(super::PACKAGE_SHARED_ARC_METADATA_BYTES_V1, 64);
        assert_eq!(super::PACKAGE_SHARED_PAYLOAD_CHARGE_METADATA_BYTES_V1, 16);
        assert_eq!(super::PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1, 1_024);
        assert_eq!(
            super::PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1,
            536_870_912
        );

        let cases: Vec<(ModuleCertParts, u64)> = vec![
            {
                let mut parts = empty_certificate_parts();
                parts.header.format = String::with_capacity(8);
                (parts, 8)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.header.core_spec = String::with_capacity(8);
                (parts, 8)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.header.module = Name(Vec::with_capacity(1));
                (parts, super::NAME_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.imports = Vec::with_capacity(1);
                (parts, super::IMPORT_ENTRY_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.name_table = Vec::with_capacity(1);
                (parts, super::NAME_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.level_table = Vec::with_capacity(1);
                (parts, super::LEVEL_NODE_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.term_table = Vec::with_capacity(1);
                (parts, super::TERM_NODE_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.declarations = Vec::with_capacity(1);
                (parts, super::DECL_CERT_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.export_block = Vec::with_capacity(1);
                (parts, super::EXPORT_ENTRY_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.axiom_report.per_declaration = Vec::with_capacity(1);
                (parts, super::DECL_AXIOM_REPORT_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.axiom_report.module_axioms = Vec::with_capacity(1);
                (parts, super::AXIOM_REF_INLINE_BYTES_V1)
            },
            {
                let mut parts = empty_certificate_parts();
                parts.axiom_report.core_features = Vec::with_capacity(1);
                (parts, 0)
            },
        ];

        for (parts, expected_delta) in cases {
            let (certificate, charge) = retained(parts);
            assert_eq!(certificate, empty);
            assert_eq!(charge, base.saturating_add(expected_delta));
        }

        let mut saturation = LogicalRetainedChargeV1::new();
        saturation.add(u64::MAX - 1);
        saturation.add(2);
        assert_eq!(saturation.get(), u64::MAX);
    }
}
