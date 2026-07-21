//! Deterministic declaration dependency closure and semantic projection.
//!
//! This module operates only on verified certificate values. Frontends may
//! propose extraction-atomic source families, but callers must validate those
//! families before constructing [`ValidatedSourceDeclarationFamilies`].

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use sha2::{Digest, Sha256};

use crate::{
    BinderType, CertReducibility, ConstructorSpec, DeclPayload, ExportEntry, ExportKind, GlobalRef,
    Hash, LevelId, LevelNode, ModuleName, MutualInductiveSpec, Name, NameId, Opacity, RecursorSpec,
    TermId, TermNode, UniverseConstraintSpec, VerifiedModule,
};

const CLOSURE_DOMAIN: &[u8] = b"NPA-DECLARATION-CLOSURE-v1\0";
const EDGE_DOMAIN: &[u8] = b"NPA-DECLARATION-CLOSURE-EDGES-v1\0";
const PROJECTION_DOMAIN: &[u8] = b"NPA-DECLARATION-CLOSURE-PROJECTION-v1\0";
const PROJECTION_LEVEL_DOMAIN: &[u8] = b"NPA-DECLARATION-CLOSURE-PROJECTION-LEVEL-v1\0";
const PROJECTION_TERM_DOMAIN: &[u8] = b"NPA-DECLARATION-CLOSURE-PROJECTION-TERM-v1\0";

/// Stable certificate declaration kind used by declaration promotion.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DeclarationClosureKind {
    /// An assumed local axiom.
    Axiom,
    /// A definition, including a class-field projection or instance.
    Definition,
    /// An opaque theorem.
    Theorem,
    /// An inductive declaration or mutual inductive block.
    Inductive,
    /// A generated constructor export.
    Constructor,
    /// A generated recursor export.
    Recursor,
}

impl DeclarationClosureKind {
    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Definition => "definition",
            Self::Theorem => "theorem",
            Self::Inductive => "inductive",
            Self::Constructor => "constructor",
            Self::Recursor => "recursor",
        }
    }
}

/// Exact declaration identity resolved from a verified certificate.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GlobalDeclarationIdentity {
    /// Module containing or exporting the declaration.
    pub module: ModuleName,
    /// Public declaration name.
    pub name: Name,
    /// Certificate declaration kind.
    pub kind: DeclarationClosureKind,
    /// Public declaration-interface hash.
    pub decl_interface_hash: Hash,
}

/// One certificate declaration member of an extraction-atomic source family.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValidatedSourceDeclarationMember {
    /// Exact member identity.
    pub identity: GlobalDeclarationIdentity,
    /// Owning declaration-table index in the verified module.
    pub decl_index: usize,
}

/// One certificate-reconciled extraction-atomic source family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedSourceDeclarationFamily {
    /// Stable owner identity for the top-level source item.
    pub owner: GlobalDeclarationIdentity,
    /// Every certificate declaration emitted by the source item.
    pub members: Vec<ValidatedSourceDeclarationMember>,
}

/// Certificate-reconciled source families indexed by member identity.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ValidatedSourceDeclarationFamilies {
    families: Vec<ValidatedSourceDeclarationFamily>,
    member_owners: BTreeMap<GlobalDeclarationIdentity, usize>,
}

impl ValidatedSourceDeclarationFamilies {
    /// Validate canonical ordering, unique ownership, and module locality.
    pub fn new(
        mut families: Vec<ValidatedSourceDeclarationFamily>,
    ) -> Result<Self, DeclarationClosureError> {
        families.sort_by(|left, right| left.owner.cmp(&right.owner));
        let mut member_owners = BTreeMap::new();
        let mut previous_owner = None;
        for (family_index, family) in families.iter_mut().enumerate() {
            if previous_owner.as_ref() == Some(&family.owner) || family.members.is_empty() {
                return Err(DeclarationClosureError::invalid_source_family(
                    family.owner.clone(),
                ));
            }
            previous_owner = Some(family.owner.clone());
            family.members.sort();
            let mut previous_member = None;
            let owner_present = family.members.iter().any(|member| {
                member.identity == family.owner
                    || (member.identity.module == family.owner.module
                        && member.identity.name == family.owner.name)
            });
            if !owner_present {
                return Err(DeclarationClosureError::invalid_source_family(
                    family.owner.clone(),
                ));
            }
            for member in &family.members {
                if member.identity.module != family.owner.module
                    || previous_member.as_ref() == Some(&member.identity)
                    || member_owners
                        .insert(member.identity.clone(), family_index)
                        .is_some()
                {
                    return Err(DeclarationClosureError::invalid_source_family(
                        family.owner.clone(),
                    ));
                }
                previous_member = Some(member.identity.clone());
            }
        }
        Ok(Self {
            families,
            member_owners,
        })
    }

    /// Return all validated families in canonical owner order.
    pub fn families(&self) -> &[ValidatedSourceDeclarationFamily] {
        &self.families
    }

    fn family_for(
        &self,
        identity: &GlobalDeclarationIdentity,
    ) -> Option<&ValidatedSourceDeclarationFamily> {
        self.member_owners
            .get(identity)
            .and_then(|index| self.families.get(*index))
    }
}

/// Resolve one public export to its exact verified identity and owning declaration index.
///
/// Generated constructors and recursors resolve to the declaration-table row of their
/// source owner while retaining their own public identity.
pub fn resolve_verified_declaration_export(
    verified: &VerifiedModule,
    name: &Name,
) -> Result<ValidatedSourceDeclarationMember, DeclarationClosureError> {
    let index = module_index(verified.module(), verified)?;
    let (export, decl_index) = index.exports.get(name).ok_or_else(|| {
        DeclarationClosureError::for_identity(
            DeclarationClosureErrorReason::DeclarationMissing,
            unknown_identity(verified.module(), name),
        )
    })?;
    Ok(ValidatedSourceDeclarationMember {
        identity: GlobalDeclarationIdentity {
            module: verified.module().clone(),
            name: name.clone(),
            kind: export_kind(export.kind),
            decl_interface_hash: export.decl_interface_hash,
        },
        decl_index: *decl_index,
    })
}

/// Deterministic resource limits for declaration closure discovery.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DeclarationClosureLimits {
    /// Maximum requested root identities.
    pub requested_roots: usize,
    /// Maximum loaded verified modules.
    pub loaded_modules: usize,
    /// Maximum materialized declaration certificates.
    pub materialized_declarations: usize,
    /// Maximum generated exports owned by materialized declarations.
    pub generated_exports: usize,
    /// Maximum unique direct dependency edges.
    pub dependency_edges: usize,
}

/// Fixed resource limits for declaration closure discovery and its artifacts.
pub const DECLARATION_CLOSURE_LIMITS_V1: DeclarationClosureLimits = DeclarationClosureLimits {
    requested_roots: 4_096,
    loaded_modules: 4_096,
    materialized_declarations: 131_072,
    generated_exports: 262_144,
    dependency_edges: 1_048_576,
};

impl Default for DeclarationClosureLimits {
    fn default() -> Self {
        DECLARATION_CLOSURE_LIMITS_V1
    }
}

/// Root or transitive-support role of a materialized declaration.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DeclarationClosureRole {
    /// Explicit requested root owner.
    Root,
    /// Same-module proof or type dependency.
    Support,
}

impl DeclarationClosureRole {
    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::Support => "support",
        }
    }
}

/// One materialized certificate declaration in a closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationClosureDeclaration {
    /// Exact declaration identity.
    pub identity: GlobalDeclarationIdentity,
    /// Root or support role.
    pub role: DeclarationClosureRole,
    /// Source declaration-table index, retained for verified lookup only.
    pub decl_index: usize,
    /// Full declaration-certificate hash.
    pub decl_certificate_hash: Hash,
    /// Certificate hash of the containing verified source module.
    pub source_certificate_hash: Hash,
    /// Structural hash of the declaration's exported type.
    pub export_type_hash: Hash,
    /// Structural hash of the declaration's exported body when present.
    pub export_body_hash: Option<Hash>,
    /// Extraction-atomic source-family owner.
    pub family_owner: GlobalDeclarationIdentity,
    /// Complete family membership.
    pub family_members: Vec<GlobalDeclarationIdentity>,
    /// Generated constructor and recursor exports owned by this declaration.
    pub generated_exports: Vec<DeclarationClosureExport>,
}

/// One generated export with its normalized public content hashes.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DeclarationClosureExport {
    /// Exact generated declaration identity.
    pub identity: GlobalDeclarationIdentity,
    /// Structural hash of the exported type.
    pub type_hash: Hash,
    /// Structural hash of the exported body when present.
    pub body_hash: Option<Hash>,
}

/// One exact direct dependency edge reached during traversal.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DeclarationDependencyEdge {
    /// Materialized declaration containing the reference.
    pub source: GlobalDeclarationIdentity,
    /// Resolved referenced global.
    pub target: GlobalDeclarationIdentity,
    /// Whether traversal stopped at an explicit externalization mapping.
    pub externalized: bool,
}

/// Complete deterministic declaration dependency closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationClosure {
    /// Requested identities retained for auditability.
    pub requested_roots: Vec<GlobalDeclarationIdentity>,
    /// Canonical root owner identities.
    pub root_owners: Vec<GlobalDeclarationIdentity>,
    /// Materialized declaration certificates.
    pub declarations: Vec<DeclarationClosureDeclaration>,
    /// Explicit source-to-target externalizations actually reached.
    pub externalized: Vec<(GlobalDeclarationIdentity, GlobalDeclarationIdentity)>,
    /// Reached builtin identities.
    pub builtins: Vec<GlobalDeclarationIdentity>,
    /// Reached allowed imported axiom identities.
    pub allowed_axioms: Vec<GlobalDeclarationIdentity>,
    /// Direct dependency edges.
    pub edges: Vec<DeclarationDependencyEdge>,
    /// Domain-separated identity of every preceding semantic field.
    pub declaration_closure_hash: Hash,
}

/// Stable reason for declaration closure failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclarationClosureErrorReason {
    /// A root or dependency cannot be resolved exactly.
    DeclarationMissing,
    /// A requested identity does not match its verified certificate export.
    IdentityMismatch,
    /// A source-family proposal is inconsistent or multiply owned.
    SourceFamilyInvalid,
    /// One family would be split between materialized and externalized members.
    SourceFamilyPartialExternalization,
    /// A local/custom axiom was reached.
    CustomAxiomRejected,
    /// A reached imported dependency lacks an explicit mapping.
    DependencyMappingMissing,
    /// A deterministic resource cap was exceeded.
    LimitExceeded,
    /// A malformed verified value or invalid table reference was encountered.
    InvalidCertificateReference,
}

impl DeclarationClosureErrorReason {
    /// Stable promotion diagnostic reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DeclarationMissing => "promotion_declaration_dependency_unmaterialized",
            Self::IdentityMismatch => "promotion_declaration_root_invalid",
            Self::SourceFamilyInvalid => "promotion_declaration_source_family_invalid",
            Self::SourceFamilyPartialExternalization => {
                "promotion_declaration_source_family_partial_externalization"
            }
            Self::CustomAxiomRejected => "promotion_declaration_custom_axiom_rejected",
            Self::DependencyMappingMissing => "promotion_declaration_dependency_mapping_missing",
            Self::LimitExceeded => "promotion_declaration_closure_limit_exceeded",
            Self::InvalidCertificateReference => "promotion_declaration_certificate_invalid",
        }
    }
}

/// Structured declaration closure failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationClosureError {
    /// Stable reason.
    pub reason: DeclarationClosureErrorReason,
    /// Exact global involved when available.
    pub identity: Option<Box<GlobalDeclarationIdentity>>,
    /// Resource or certificate field involved.
    pub field: Option<&'static str>,
    /// Required or maximum numeric value.
    pub expected_value: Option<usize>,
    /// Observed numeric value.
    pub actual_value: Option<usize>,
}

impl DeclarationClosureError {
    fn invalid_source_family(identity: GlobalDeclarationIdentity) -> Self {
        Self {
            reason: DeclarationClosureErrorReason::SourceFamilyInvalid,
            identity: Some(Box::new(identity)),
            field: None,
            expected_value: None,
            actual_value: None,
        }
    }

    fn for_identity(
        reason: DeclarationClosureErrorReason,
        identity: GlobalDeclarationIdentity,
    ) -> Self {
        Self {
            reason,
            identity: Some(Box::new(identity)),
            field: None,
            expected_value: None,
            actual_value: None,
        }
    }

    fn invalid(field: &'static str) -> Self {
        Self {
            reason: DeclarationClosureErrorReason::InvalidCertificateReference,
            identity: None,
            field: Some(field),
            expected_value: None,
            actual_value: None,
        }
    }

    fn limit(field: &'static str, expected_value: usize, actual_value: usize) -> Self {
        Self {
            reason: DeclarationClosureErrorReason::LimitExceeded,
            identity: None,
            field: Some(field),
            expected_value: Some(expected_value),
            actual_value: Some(actual_value),
        }
    }
}

impl std::fmt::Display for DeclarationClosureError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}", self.reason.as_str())?;
        if let Some(identity) = &self.identity {
            write!(
                formatter,
                ": {}::{}",
                identity.module.as_dotted(),
                identity.name.as_dotted()
            )?;
        }
        if let (Some(field), Some(expected), Some(actual)) =
            (self.field, self.expected_value, self.actual_value)
        {
            write!(formatter, ": {field} <= {expected}, got {actual}")?;
        }
        Ok(())
    }
}

impl std::error::Error for DeclarationClosureError {}

/// Compute the exact bounded dependency closure of explicit verified roots.
pub fn declaration_dependency_closure(
    modules: &BTreeMap<ModuleName, VerifiedModule>,
    roots: &BTreeSet<GlobalDeclarationIdentity>,
    source_families: &ValidatedSourceDeclarationFamilies,
    externalized: &BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
    limits: DeclarationClosureLimits,
) -> Result<DeclarationClosure, DeclarationClosureError> {
    check_limit("requested_roots", limits.requested_roots, roots.len())?;
    check_limit("loaded_modules", limits.loaded_modules, modules.len())?;

    let indexes = modules
        .iter()
        .map(|(module, verified)| {
            module_index(module, verified).map(|index| (module.clone(), index))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let mut requested_owners = BTreeSet::new();
    let mut requested_roots = Vec::new();
    for root in roots {
        let resolved = resolve_export(modules, &indexes, &root.module, &root.name)?;
        if resolved.identity != *root {
            return Err(DeclarationClosureError::for_identity(
                DeclarationClosureErrorReason::IdentityMismatch,
                root.clone(),
            ));
        }
        reject_local_axiom(&resolved.identity)?;
        let owner = source_families
            .family_for(&resolved.identity)
            .map_or_else(|| resolved.identity.clone(), |family| family.owner.clone());
        requested_roots.push(root.clone());
        requested_owners.insert(owner);
    }

    let mut queue = VecDeque::new();
    for owner in &requested_owners {
        let resolved = resolve_export(modules, &indexes, &owner.module, &owner.name)?;
        queue.push_back((resolved.identity, DeclarationClosureRole::Root));
    }
    let mut roles = BTreeMap::new();
    let mut decl_rows = BTreeMap::new();
    let mut externalized_rows = BTreeSet::new();
    let mut builtins = BTreeSet::new();
    let mut allowed_axioms = BTreeSet::new();
    let mut edges = BTreeSet::new();
    let mut generated_count = 0usize;

    while let Some((identity, role)) = queue.pop_front() {
        let resolved = resolve_export(modules, &indexes, &identity.module, &identity.name)?;
        if resolved.identity != identity {
            return Err(DeclarationClosureError::for_identity(
                DeclarationClosureErrorReason::IdentityMismatch,
                identity,
            ));
        }
        reject_local_axiom(&resolved.identity)?;
        let family = source_families.family_for(&resolved.identity);
        let family_owner =
            family.map_or_else(|| resolved.identity.clone(), |value| value.owner.clone());
        let family_members = family.map_or_else(
            || {
                vec![ValidatedSourceDeclarationMember {
                    identity: resolved.identity.clone(),
                    decl_index: resolved.decl_index,
                }]
            },
            |value| value.members.clone(),
        );
        for family_member in family_members {
            if externalized.contains_key(&family_member.identity) {
                return Err(DeclarationClosureError::for_identity(
                    DeclarationClosureErrorReason::SourceFamilyPartialExternalization,
                    family_member.identity,
                ));
            }
            let member = resolve_export(
                modules,
                &indexes,
                &family_member.identity.module,
                &family_member.identity.name,
            )?;
            if member.identity != family_member.identity
                || member.decl_index != family_member.decl_index
            {
                return Err(DeclarationClosureError::for_identity(
                    DeclarationClosureErrorReason::SourceFamilyInvalid,
                    family_member.identity,
                ));
            }
            reject_local_axiom(&member.identity)?;
            let key = (member.identity.module.clone(), member.decl_index);
            let effective_role = if requested_owners.contains(&family_owner) {
                DeclarationClosureRole::Root
            } else {
                role
            };
            roles
                .entry(key.clone())
                .and_modify(|old| {
                    if effective_role == DeclarationClosureRole::Root {
                        *old = effective_role;
                    }
                })
                .or_insert(effective_role);
            if decl_rows.contains_key(&key) {
                continue;
            }
            check_limit(
                "materialized_declarations",
                limits.materialized_declarations,
                decl_rows.len() + 1,
            )?;
            let verified = modules.get(&member.identity.module).ok_or_else(|| {
                DeclarationClosureError::for_identity(
                    DeclarationClosureErrorReason::DeclarationMissing,
                    member.identity.clone(),
                )
            })?;
            let decl = verified
                .declarations()
                .get(member.decl_index)
                .ok_or_else(|| {
                    DeclarationClosureError::for_identity(
                        DeclarationClosureErrorReason::DeclarationMissing,
                        member.identity.clone(),
                    )
                })?;
            let primary = primary_identity(verified, member.decl_index)?;
            let index = indexes
                .get(&member.identity.module)
                .ok_or_else(|| DeclarationClosureError::invalid("module.index"))?;
            let primary_export = index
                .primary_exports
                .get(&member.decl_index)
                .ok_or_else(|| DeclarationClosureError::invalid("export_block.primary"))?;
            let generated_exports = index
                .generated_exports
                .get(&member.decl_index)
                .cloned()
                .unwrap_or_default();
            generated_count = generated_count.saturating_add(generated_exports.len());
            check_limit(
                "generated_exports",
                limits.generated_exports,
                generated_count,
            )?;
            let row = DeclarationClosureDeclaration {
                identity: primary,
                role: effective_role,
                decl_index: member.decl_index,
                decl_certificate_hash: decl.hashes.decl_certificate_hash,
                source_certificate_hash: verified.certificate_hash(),
                export_type_hash: primary_export.type_hash,
                export_body_hash: primary_export.body_hash,
                family_owner: family_owner.clone(),
                family_members: source_families.family_for(&member.identity).map_or_else(
                    || vec![member.identity.clone()],
                    |value| {
                        value
                            .members
                            .iter()
                            .map(|entry| entry.identity.clone())
                            .collect()
                    },
                ),
                generated_exports,
            };
            let edge_source = row.identity.clone();
            decl_rows.insert(key, row);

            for global in decl
                .dependencies
                .iter()
                .map(|dependency| &dependency.global_ref)
                .chain(
                    decl.axiom_dependencies
                        .iter()
                        .map(|axiom| &axiom.global_ref),
                )
            {
                let target = resolve_global(verified, modules, &indexes, global)?;
                let is_local = target.identity.module == member.identity.module;
                if is_local {
                    reject_local_axiom(&target.identity)?;
                }
                if matches!(global, GlobalRef::Builtin { .. }) {
                    insert_dependency_edge(
                        &mut edges,
                        DeclarationDependencyEdge {
                            source: edge_source.clone(),
                            target: target.identity.clone(),
                            externalized: false,
                        },
                        limits.dependency_edges,
                    )?;
                    builtins.insert(target.identity.clone());
                    continue;
                }
                let mapping = externalized.get(&target.identity);
                if let Some(mapped) = mapping {
                    if mapped.name != target.identity.name
                        || mapped.kind != target.identity.kind
                        || mapped.decl_interface_hash != target.identity.decl_interface_hash
                    {
                        return Err(DeclarationClosureError::for_identity(
                            DeclarationClosureErrorReason::IdentityMismatch,
                            target.identity,
                        ));
                    }
                    if requested_roots.contains(&target.identity)
                        || requested_owners.contains(&target.identity)
                    {
                        return Err(DeclarationClosureError::for_identity(
                            DeclarationClosureErrorReason::IdentityMismatch,
                            target.identity,
                        ));
                    }
                    insert_dependency_edge(
                        &mut edges,
                        DeclarationDependencyEdge {
                            source: edge_source.clone(),
                            target: target.identity.clone(),
                            externalized: true,
                        },
                        limits.dependency_edges,
                    )?;
                    externalized_rows.insert((target.identity.clone(), mapped.clone()));
                    if target.identity.kind == DeclarationClosureKind::Axiom {
                        allowed_axioms.insert(target.identity);
                    }
                    continue;
                }
                if !is_local {
                    return Err(DeclarationClosureError::for_identity(
                        DeclarationClosureErrorReason::DependencyMappingMissing,
                        target.identity,
                    ));
                }
                insert_dependency_edge(
                    &mut edges,
                    DeclarationDependencyEdge {
                        source: edge_source.clone(),
                        target: target.identity.clone(),
                        externalized: false,
                    },
                    limits.dependency_edges,
                )?;
                queue.push_back((target.identity, DeclarationClosureRole::Support));
            }
        }
    }

    let mut declarations = decl_rows
        .into_iter()
        .map(|(key, mut row)| {
            row.role = roles[&key];
            row
        })
        .collect::<Vec<_>>();
    declarations.sort_by(|left, right| left.identity.cmp(&right.identity));
    let mut closure = DeclarationClosure {
        requested_roots,
        root_owners: requested_owners.into_iter().collect(),
        declarations,
        externalized: externalized_rows.into_iter().collect(),
        builtins: builtins.into_iter().collect(),
        allowed_axioms: allowed_axioms.into_iter().collect(),
        edges: edges.into_iter().collect(),
        declaration_closure_hash: [0; 32],
    };
    closure.declaration_closure_hash = declaration_closure_hash(&closure);
    Ok(closure)
}

/// Compute the stable domain-separated hash of a declaration closure.
pub fn declaration_closure_hash(closure: &DeclarationClosure) -> Hash {
    let bytes = closure_bytes(closure, false);
    domain_hash(CLOSURE_DOMAIN, &bytes)
}

/// Compute the stable identity of the exact direct dependency edge projection.
pub fn declaration_dependency_edge_hash(closure: &DeclarationClosure) -> Hash {
    let mut out = Vec::new();
    put_u64(&mut out, closure.edges.len() as u64);
    for edge in &closure.edges {
        put_identity(&mut out, &edge.source);
        put_identity(&mut out, &edge.target);
        out.push(u8::from(edge.externalized));
    }
    domain_hash(EDGE_DOMAIN, &out)
}

/// Return a table-index-independent semantic projection for one closure.
///
/// `global_mapping` maps source identities to their normalized target
/// identities. Missing rows retain their original module and global names.
pub fn normalized_declaration_closure_projection(
    modules: &BTreeMap<ModuleName, VerifiedModule>,
    closure: &DeclarationClosure,
    global_mapping: &BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
) -> Result<Vec<u8>, DeclarationClosureError> {
    validate_projection_resource_limits(modules, closure, DECLARATION_CLOSURE_LIMITS_V1)?;
    let indexes = modules
        .iter()
        .map(|(module, verified)| {
            module_index(module, verified).map(|index| (module.clone(), index))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let mut declaration_indices_by_module = BTreeMap::<ModuleName, Vec<usize>>::new();
    for selected in &closure.declarations {
        if !modules.contains_key(&selected.identity.module) {
            return Err(DeclarationClosureError::for_identity(
                DeclarationClosureErrorReason::DeclarationMissing,
                selected.identity.clone(),
            ));
        }
        declaration_indices_by_module
            .entry(selected.identity.module.clone())
            .or_default()
            .push(selected.decl_index);
    }
    let mut tables_by_module = BTreeMap::new();
    for (module_name, declaration_indices) in declaration_indices_by_module {
        let module = modules
            .get(&module_name)
            .ok_or_else(|| DeclarationClosureError::invalid("projection.modules"))?;
        tables_by_module.insert(
            module_name,
            projection_tables(
                module,
                &declaration_indices,
                modules,
                &indexes,
                global_mapping,
            )?,
        );
    }
    let mut rows = Vec::new();
    for selected in &closure.declarations {
        let module = modules.get(&selected.identity.module).ok_or_else(|| {
            DeclarationClosureError::for_identity(
                DeclarationClosureErrorReason::DeclarationMissing,
                selected.identity.clone(),
            )
        })?;
        let declaration = module
            .declarations()
            .get(selected.decl_index)
            .ok_or_else(|| {
                DeclarationClosureError::for_identity(
                    DeclarationClosureErrorReason::DeclarationMissing,
                    selected.identity.clone(),
                )
            })?;
        let context = ProjectionContext {
            module,
            modules,
            indexes: &indexes,
            mapping: global_mapping,
            tables: tables_by_module
                .get(&selected.identity.module)
                .ok_or_else(|| DeclarationClosureError::invalid("projection.tables"))?,
        };
        let mut bytes = Vec::new();
        put_str(&mut bytes, selected.role.as_str());
        put_identity(
            &mut bytes,
            normalized_identity(global_mapping, &selected.family_owner),
        );
        let mut generated_exports = selected
            .generated_exports
            .iter()
            .map(|export| normalized_identity(global_mapping, &export.identity).clone())
            .collect::<Vec<_>>();
        generated_exports.sort();
        put_identities(&mut bytes, &generated_exports);
        context.declaration(&mut bytes, &declaration.decl)?;
        let mut dependencies = declaration
            .dependencies
            .iter()
            .map(|dependency| context.global_bytes(&dependency.global_ref))
            .collect::<Result<Vec<_>, _>>()?;
        dependencies.sort();
        put_vec_bytes(&mut bytes, &dependencies);
        let mut axioms = declaration
            .axiom_dependencies
            .iter()
            .map(|axiom| context.global_bytes(&axiom.global_ref))
            .collect::<Result<Vec<_>, _>>()?;
        axioms.sort();
        put_vec_bytes(&mut bytes, &axioms);
        let normalized = global_mapping
            .get(&selected.identity)
            .unwrap_or(&selected.identity);
        rows.push((normalized.module.clone(), normalized.name.clone(), bytes));
    }
    rows.sort();
    let mut out = Vec::new();
    put_u64(&mut out, rows.len() as u64);
    for (module, name, bytes) in rows {
        put_name(&mut out, &module);
        put_name(&mut out, &name);
        put_bytes(&mut out, &bytes);
    }
    let mut externalized = closure
        .externalized
        .iter()
        .map(|(source, target)| {
            (
                normalized_identity(global_mapping, source).clone(),
                normalized_identity(global_mapping, target).clone(),
            )
        })
        .collect::<Vec<_>>();
    externalized.sort();
    put_u64(&mut out, externalized.len() as u64);
    for (source, target) in externalized {
        put_identity(&mut out, &source);
        put_identity(&mut out, &target);
    }
    Ok(out)
}

/// Hash a normalized declaration closure projection.
pub fn normalized_declaration_closure_hash(projection: &[u8]) -> Hash {
    domain_hash(PROJECTION_DOMAIN, projection)
}

fn validate_projection_resource_limits(
    modules: &BTreeMap<ModuleName, VerifiedModule>,
    closure: &DeclarationClosure,
    limits: DeclarationClosureLimits,
) -> Result<(), DeclarationClosureError> {
    check_limit(
        "requested_roots",
        limits.requested_roots,
        closure.requested_roots.len(),
    )?;
    check_limit("loaded_modules", limits.loaded_modules, modules.len())?;
    check_limit(
        "materialized_declarations",
        limits.materialized_declarations,
        closure.declarations.len(),
    )?;
    let mut generated_exports = 0usize;
    for declaration in &closure.declarations {
        generated_exports = generated_exports.saturating_add(declaration.generated_exports.len());
        check_limit(
            "generated_exports",
            limits.generated_exports,
            generated_exports,
        )?;
    }
    for actual in [
        closure.externalized.len(),
        closure.builtins.len(),
        closure.allowed_axioms.len(),
        closure.edges.len(),
    ] {
        check_limit("dependency_edges", limits.dependency_edges, actual)?;
    }
    Ok(())
}

fn normalized_identity<'a>(
    mapping: &'a BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
    identity: &'a GlobalDeclarationIdentity,
) -> &'a GlobalDeclarationIdentity {
    mapping.get(identity).unwrap_or(identity)
}

#[derive(Clone)]
struct ResolvedDeclaration {
    identity: GlobalDeclarationIdentity,
    decl_index: usize,
}

struct ModuleIndex {
    exports: BTreeMap<Name, (ExportEntry, usize)>,
    primary_exports: BTreeMap<usize, ExportEntry>,
    generated_exports: BTreeMap<usize, Vec<DeclarationClosureExport>>,
}

fn module_index(
    expected_module: &Name,
    verified: &VerifiedModule,
) -> Result<ModuleIndex, DeclarationClosureError> {
    if verified.module() != expected_module {
        return Err(DeclarationClosureError::invalid("module"));
    }
    let owners = declaration_owner_indices(verified)?;
    let primary_names = verified
        .declarations()
        .iter()
        .enumerate()
        .map(|(index, declaration)| {
            table_name(verified, decl_name_id(&declaration.decl)).map(|name| (index, name))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let mut exports = BTreeMap::new();
    let mut primary_exports = BTreeMap::new();
    let mut generated_exports = BTreeMap::<usize, Vec<DeclarationClosureExport>>::new();
    for export in verified.export_block() {
        let name = verified
            .name_table()
            .get(export.name)
            .cloned()
            .ok_or_else(|| DeclarationClosureError::invalid("export_block.name"))?;
        let decl_index = owners
            .get(&name)
            .copied()
            .ok_or_else(|| DeclarationClosureError::invalid("export_block.owner"))?;
        if primary_names.get(&decl_index) == Some(&name)
            && primary_exports.insert(decl_index, export.clone()).is_some()
        {
            return Err(DeclarationClosureError::invalid(
                "export_block.primary_duplicate",
            ));
        }
        if matches!(export.kind, ExportKind::Constructor | ExportKind::Recursor) {
            generated_exports
                .entry(decl_index)
                .or_default()
                .push(DeclarationClosureExport {
                    identity: GlobalDeclarationIdentity {
                        module: verified.module().clone(),
                        name: name.clone(),
                        kind: export_kind(export.kind),
                        decl_interface_hash: export.decl_interface_hash,
                    },
                    type_hash: export.type_hash,
                    body_hash: export.body_hash,
                });
        }
        if exports.insert(name, (export.clone(), decl_index)).is_some() {
            return Err(DeclarationClosureError::invalid("export_block.duplicate"));
        }
    }
    for exports in generated_exports.values_mut() {
        exports.sort();
    }
    Ok(ModuleIndex {
        exports,
        primary_exports,
        generated_exports,
    })
}

fn resolve_export(
    modules: &BTreeMap<ModuleName, VerifiedModule>,
    indexes: &BTreeMap<ModuleName, ModuleIndex>,
    module: &Name,
    name: &Name,
) -> Result<ResolvedDeclaration, DeclarationClosureError> {
    let _verified = modules.get(module).ok_or_else(|| {
        DeclarationClosureError::for_identity(
            DeclarationClosureErrorReason::DeclarationMissing,
            unknown_identity(module, name),
        )
    })?;
    let (export, decl_index) = indexes
        .get(module)
        .and_then(|index| index.exports.get(name))
        .ok_or_else(|| {
            DeclarationClosureError::for_identity(
                DeclarationClosureErrorReason::DeclarationMissing,
                unknown_identity(module, name),
            )
        })?;
    Ok(ResolvedDeclaration {
        identity: GlobalDeclarationIdentity {
            module: module.clone(),
            name: name.clone(),
            kind: export_kind(export.kind),
            decl_interface_hash: export.decl_interface_hash,
        },
        decl_index: *decl_index,
    })
}

fn resolve_global(
    current: &VerifiedModule,
    modules: &BTreeMap<ModuleName, VerifiedModule>,
    indexes: &BTreeMap<ModuleName, ModuleIndex>,
    global: &GlobalRef,
) -> Result<ResolvedDeclaration, DeclarationClosureError> {
    match global {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => Ok(ResolvedDeclaration {
            identity: GlobalDeclarationIdentity {
                module: Name::from_dotted("$builtin"),
                name: table_name(current, *name)?,
                kind: DeclarationClosureKind::Definition,
                decl_interface_hash: *decl_interface_hash,
            },
            decl_index: 0,
        }),
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let module = current
                .imports()
                .get(*import_index)
                .ok_or_else(|| DeclarationClosureError::invalid("imports.index"))?
                .module
                .clone();
            let name = table_name(current, *name)?;
            let resolved = resolve_export(modules, indexes, &module, &name)?;
            if resolved.identity.decl_interface_hash != *decl_interface_hash {
                return Err(DeclarationClosureError::for_identity(
                    DeclarationClosureErrorReason::IdentityMismatch,
                    resolved.identity,
                ));
            }
            Ok(resolved)
        }
        GlobalRef::Local { decl_index } => {
            let identity = primary_identity(current, *decl_index)?;
            Ok(ResolvedDeclaration {
                identity,
                decl_index: *decl_index,
            })
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            let name = table_name(current, *name)?;
            let resolved = resolve_export(modules, indexes, current.module(), &name)?;
            if resolved.decl_index != *decl_index {
                return Err(DeclarationClosureError::for_identity(
                    DeclarationClosureErrorReason::IdentityMismatch,
                    resolved.identity,
                ));
            }
            Ok(resolved)
        }
    }
}

fn declaration_owner_indices(
    verified: &VerifiedModule,
) -> Result<BTreeMap<Name, usize>, DeclarationClosureError> {
    let mut owners = BTreeMap::new();
    for (index, declaration) in verified.declarations().iter().enumerate() {
        let mut names = vec![decl_name_id(&declaration.decl)];
        match &declaration.decl {
            DeclPayload::Inductive {
                constructors,
                recursor,
                ..
            }
            | DeclPayload::InductiveConstrained {
                constructors,
                recursor,
                ..
            } => {
                names.extend(constructors.iter().map(|constructor| constructor.name));
                names.extend(recursor.iter().map(|recursor| recursor.name));
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    names.push(inductive.name);
                    names.extend(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.name),
                    );
                    names.extend(inductive.recursor.iter().map(|recursor| recursor.name));
                }
            }
            _ => {}
        }
        for name in names {
            let name = table_name(verified, name)?;
            if owners.insert(name, index).is_some() {
                return Err(DeclarationClosureError::invalid("declarations.owner"));
            }
        }
    }
    Ok(owners)
}

fn primary_identity(
    verified: &VerifiedModule,
    decl_index: usize,
) -> Result<GlobalDeclarationIdentity, DeclarationClosureError> {
    let declaration = verified
        .declarations()
        .get(decl_index)
        .ok_or_else(|| DeclarationClosureError::invalid("declarations.index"))?;
    Ok(GlobalDeclarationIdentity {
        module: verified.module().clone(),
        name: table_name(verified, decl_name_id(&declaration.decl))?,
        kind: decl_kind(&declaration.decl),
        decl_interface_hash: declaration.hashes.decl_interface_hash,
    })
}

fn reject_local_axiom(identity: &GlobalDeclarationIdentity) -> Result<(), DeclarationClosureError> {
    if identity.kind == DeclarationClosureKind::Axiom {
        return Err(DeclarationClosureError::for_identity(
            DeclarationClosureErrorReason::CustomAxiomRejected,
            identity.clone(),
        ));
    }
    Ok(())
}

fn table_name(verified: &VerifiedModule, id: NameId) -> Result<Name, DeclarationClosureError> {
    verified
        .name_table()
        .get(id)
        .cloned()
        .ok_or_else(|| DeclarationClosureError::invalid("name_table.index"))
}

fn check_limit(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), DeclarationClosureError> {
    if actual > expected {
        Err(DeclarationClosureError::limit(field, expected, actual))
    } else {
        Ok(())
    }
}

fn insert_dependency_edge(
    edges: &mut BTreeSet<DeclarationDependencyEdge>,
    edge: DeclarationDependencyEdge,
    maximum: usize,
) -> Result<(), DeclarationClosureError> {
    if !edges.contains(&edge) {
        check_limit("dependency_edges", maximum, edges.len().saturating_add(1))?;
        edges.insert(edge);
    }
    Ok(())
}

fn unknown_identity(module: &Name, name: &Name) -> GlobalDeclarationIdentity {
    GlobalDeclarationIdentity {
        module: module.clone(),
        name: name.clone(),
        kind: DeclarationClosureKind::Definition,
        decl_interface_hash: [0; 32],
    }
}

fn decl_kind(payload: &DeclPayload) -> DeclarationClosureKind {
    match payload {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => {
            DeclarationClosureKind::Axiom
        }
        DeclPayload::Def { .. } | DeclPayload::DefConstrained { .. } => {
            DeclarationClosureKind::Definition
        }
        DeclPayload::Theorem { .. } | DeclPayload::TheoremConstrained { .. } => {
            DeclarationClosureKind::Theorem
        }
        DeclPayload::Inductive { .. }
        | DeclPayload::InductiveConstrained { .. }
        | DeclPayload::MutualInductiveBlock { .. } => DeclarationClosureKind::Inductive,
    }
}

fn export_kind(kind: ExportKind) -> DeclarationClosureKind {
    match kind {
        ExportKind::Axiom => DeclarationClosureKind::Axiom,
        ExportKind::Def => DeclarationClosureKind::Definition,
        ExportKind::Theorem => DeclarationClosureKind::Theorem,
        ExportKind::Inductive => DeclarationClosureKind::Inductive,
        ExportKind::Constructor => DeclarationClosureKind::Constructor,
        ExportKind::Recursor => DeclarationClosureKind::Recursor,
    }
}

fn decl_name_id(payload: &DeclPayload) -> NameId {
    match payload {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

fn closure_bytes(closure: &DeclarationClosure, include_hash: bool) -> Vec<u8> {
    let mut out = Vec::new();
    put_identities(&mut out, &closure.requested_roots);
    put_identities(&mut out, &closure.root_owners);
    put_u64(&mut out, closure.declarations.len() as u64);
    for declaration in &closure.declarations {
        put_identity(&mut out, &declaration.identity);
        put_str(&mut out, declaration.role.as_str());
        out.extend_from_slice(&declaration.decl_certificate_hash);
        out.extend_from_slice(&declaration.source_certificate_hash);
        out.extend_from_slice(&declaration.export_type_hash);
        put_optional_hash(&mut out, declaration.export_body_hash);
        put_identity(&mut out, &declaration.family_owner);
        put_identities(&mut out, &declaration.family_members);
        put_u64(&mut out, declaration.generated_exports.len() as u64);
        for export in &declaration.generated_exports {
            put_identity(&mut out, &export.identity);
            out.extend_from_slice(&export.type_hash);
            put_optional_hash(&mut out, export.body_hash);
        }
    }
    put_u64(&mut out, closure.externalized.len() as u64);
    for (source, target) in &closure.externalized {
        put_identity(&mut out, source);
        put_identity(&mut out, target);
    }
    put_identities(&mut out, &closure.builtins);
    put_identities(&mut out, &closure.allowed_axioms);
    put_u64(&mut out, closure.edges.len() as u64);
    for edge in &closure.edges {
        put_identity(&mut out, &edge.source);
        put_identity(&mut out, &edge.target);
        out.push(u8::from(edge.externalized));
    }
    if include_hash {
        out.extend_from_slice(&closure.declaration_closure_hash);
    }
    out
}

struct ProjectionTables {
    level_hashes: Vec<Hash>,
    term_hashes: Vec<Option<Hash>>,
}

fn projection_tables(
    module: &VerifiedModule,
    declaration_indices: &[usize],
    modules: &BTreeMap<ModuleName, VerifiedModule>,
    indexes: &BTreeMap<ModuleName, ModuleIndex>,
    mapping: &BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
) -> Result<ProjectionTables, DeclarationClosureError> {
    let mut level_hashes: Vec<Hash> = Vec::with_capacity(module.level_table().len());
    for level in module.level_table() {
        let mut payload = Vec::new();
        match level {
            LevelNode::Zero => payload.push(0),
            LevelNode::Succ(value) => {
                payload.push(1);
                payload.extend_from_slice(
                    level_hashes
                        .get(*value)
                        .ok_or_else(|| DeclarationClosureError::invalid("level_table.index"))?,
                );
            }
            LevelNode::Max(left, right) => {
                payload.push(2);
                for child in [left, right] {
                    payload.extend_from_slice(
                        level_hashes
                            .get(*child)
                            .ok_or_else(|| DeclarationClosureError::invalid("level_table.index"))?,
                    );
                }
            }
            LevelNode::IMax(left, right) => {
                payload.push(3);
                for child in [left, right] {
                    payload.extend_from_slice(
                        level_hashes
                            .get(*child)
                            .ok_or_else(|| DeclarationClosureError::invalid("level_table.index"))?,
                    );
                }
            }
            LevelNode::Param(name) => {
                payload.push(4);
                put_name(&mut payload, &table_name(module, *name)?);
            }
        }
        level_hashes.push(domain_hash(PROJECTION_LEVEL_DOMAIN, &payload));
    }

    let needed_terms = projection_term_ids(module, declaration_indices)?;
    let mut term_hashes: Vec<Option<Hash>> = vec![None; module.term_table().len()];
    for term_id in needed_terms {
        let term = module
            .term_table()
            .get(term_id)
            .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?;
        let mut payload = Vec::new();
        match term {
            TermNode::Sort(level) => {
                payload.push(0);
                payload.extend_from_slice(
                    level_hashes
                        .get(*level)
                        .ok_or_else(|| DeclarationClosureError::invalid("level_table.index"))?,
                );
            }
            TermNode::BVar(index) => {
                payload.push(1);
                put_u64(&mut payload, u64::from(*index));
            }
            TermNode::Const { global_ref, levels } => {
                payload.push(2);
                let resolved = resolve_global(module, modules, indexes, global_ref)?;
                let normalized = mapping
                    .get(&resolved.identity)
                    .unwrap_or(&resolved.identity);
                put_identity(&mut payload, normalized);
                put_u64(&mut payload, levels.len() as u64);
                for level in levels {
                    payload.extend_from_slice(
                        level_hashes
                            .get(*level)
                            .ok_or_else(|| DeclarationClosureError::invalid("level_table.index"))?,
                    );
                }
            }
            TermNode::App(function, argument) => {
                payload.push(3);
                for child in [function, argument] {
                    payload.extend_from_slice(
                        term_hashes
                            .get(*child)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?,
                    );
                }
            }
            TermNode::Lam { ty, body } => {
                payload.push(4);
                for child in [ty, body] {
                    payload.extend_from_slice(
                        term_hashes
                            .get(*child)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?,
                    );
                }
            }
            TermNode::Pi { ty, body } => {
                payload.push(5);
                for child in [ty, body] {
                    payload.extend_from_slice(
                        term_hashes
                            .get(*child)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?,
                    );
                }
            }
            TermNode::Let { ty, value, body } => {
                payload.push(6);
                for child in [ty, value, body] {
                    payload.extend_from_slice(
                        term_hashes
                            .get(*child)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?,
                    );
                }
            }
        }
        term_hashes[term_id] = Some(domain_hash(PROJECTION_TERM_DOMAIN, &payload));
    }
    Ok(ProjectionTables {
        level_hashes,
        term_hashes,
    })
}

fn projection_term_ids(
    module: &VerifiedModule,
    declaration_indices: &[usize],
) -> Result<BTreeSet<TermId>, DeclarationClosureError> {
    let mut pending = Vec::new();
    for declaration_index in declaration_indices {
        let declaration = module
            .declarations()
            .get(*declaration_index)
            .ok_or_else(|| DeclarationClosureError::invalid("declaration.index"))?;
        declaration_term_roots(&declaration.decl, &mut pending);
    }
    let mut needed = BTreeSet::new();
    while let Some(term_id) = pending.pop() {
        if !needed.insert(term_id) {
            continue;
        }
        match module
            .term_table()
            .get(term_id)
            .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?
        {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            TermNode::App(function, argument) => {
                pending.extend([*function, *argument]);
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                pending.extend([*ty, *body]);
            }
            TermNode::Let { ty, value, body } => {
                pending.extend([*ty, *value, *body]);
            }
        }
    }
    Ok(needed)
}

fn declaration_term_roots(declaration: &DeclPayload, out: &mut Vec<TermId>) {
    match declaration {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => out.push(*ty),
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            out.extend([*ty, *value]);
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => {
            out.extend([*ty, *proof]);
        }
        DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => inductive_term_roots(params, indices, constructors, recursor, out),
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                inductive_term_roots(
                    &inductive.params,
                    &inductive.indices,
                    &inductive.constructors,
                    &inductive.recursor,
                    out,
                );
            }
        }
    }
}

fn inductive_term_roots(
    params: &[BinderType],
    indices: &[BinderType],
    constructors: &[ConstructorSpec],
    recursor: &Option<RecursorSpec>,
    out: &mut Vec<TermId>,
) {
    out.extend(params.iter().map(|binder| binder.ty));
    out.extend(indices.iter().map(|binder| binder.ty));
    out.extend(constructors.iter().map(|constructor| constructor.ty));
    if let Some(recursor) = recursor {
        out.push(recursor.ty);
    }
}

struct ProjectionContext<'a> {
    module: &'a VerifiedModule,
    modules: &'a BTreeMap<ModuleName, VerifiedModule>,
    indexes: &'a BTreeMap<ModuleName, ModuleIndex>,
    mapping: &'a BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
    tables: &'a ProjectionTables,
}

impl ProjectionContext<'_> {
    fn name(&self, id: NameId) -> Result<Name, DeclarationClosureError> {
        table_name(self.module, id)
    }

    fn mapped_name(
        &self,
        module: &Name,
        name: &Name,
    ) -> Result<(Name, Name), DeclarationClosureError> {
        let resolved = resolve_export(self.modules, self.indexes, module, name)?;
        let mapped = self
            .mapping
            .get(&resolved.identity)
            .unwrap_or(&resolved.identity);
        Ok((mapped.module.clone(), mapped.name.clone()))
    }

    fn global_bytes(&self, global: &GlobalRef) -> Result<Vec<u8>, DeclarationClosureError> {
        let mut out = Vec::new();
        let resolved = resolve_global(self.module, self.modules, self.indexes, global)?;
        let mapped = self
            .mapping
            .get(&resolved.identity)
            .unwrap_or(&resolved.identity);
        put_identity(&mut out, mapped);
        Ok(out)
    }

    fn level(&self, out: &mut Vec<u8>, id: LevelId) -> Result<(), DeclarationClosureError> {
        out.extend_from_slice(
            self.tables
                .level_hashes
                .get(id)
                .ok_or_else(|| DeclarationClosureError::invalid("level_table.index"))?,
        );
        Ok(())
    }

    fn term(&self, out: &mut Vec<u8>, id: TermId) -> Result<(), DeclarationClosureError> {
        out.extend_from_slice(
            self.tables
                .term_hashes
                .get(id)
                .and_then(Option::as_ref)
                .ok_or_else(|| DeclarationClosureError::invalid("term_table.index"))?,
        );
        Ok(())
    }

    fn declaration(
        &self,
        out: &mut Vec<u8>,
        payload: &DeclPayload,
    ) -> Result<(), DeclarationClosureError> {
        match payload {
            DeclPayload::Axiom {
                name,
                universe_params,
                ty,
            } => self.basic_decl(out, 0, *name, universe_params, *ty, None)?,
            DeclPayload::AxiomConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
            } => {
                self.basic_decl(out, 1, *name, universe_params, *ty, None)?;
                self.constraints(out, universe_constraints)?;
            }
            DeclPayload::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility,
            } => {
                self.basic_decl(out, 2, *name, universe_params, *ty, Some(*value))?;
                out.push(reducibility_tag(*reducibility));
            }
            DeclPayload::DefConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                value,
                reducibility,
            } => {
                self.basic_decl(out, 3, *name, universe_params, *ty, Some(*value))?;
                self.constraints(out, universe_constraints)?;
                out.push(reducibility_tag(*reducibility));
            }
            DeclPayload::Theorem {
                name,
                universe_params,
                ty,
                proof,
                opacity,
            } => {
                self.basic_decl(out, 4, *name, universe_params, *ty, Some(*proof))?;
                out.push(opacity_tag(*opacity));
            }
            DeclPayload::TheoremConstrained {
                name,
                universe_params,
                universe_constraints,
                ty,
                proof,
                opacity,
            } => {
                self.basic_decl(out, 5, *name, universe_params, *ty, Some(*proof))?;
                self.constraints(out, universe_constraints)?;
                out.push(opacity_tag(*opacity));
            }
            DeclPayload::Inductive {
                name,
                universe_params,
                params,
                indices,
                sort,
                constructors,
                recursor,
            } => {
                out.push(6);
                self.names(out, universe_params)?;
                self.inductive(out, *name, params, indices, *sort, constructors, recursor)?;
            }
            DeclPayload::InductiveConstrained {
                name,
                universe_params,
                universe_constraints,
                params,
                indices,
                sort,
                constructors,
                recursor,
            } => {
                out.push(7);
                self.names(out, universe_params)?;
                self.constraints(out, universe_constraints)?;
                self.inductive(out, *name, params, indices, *sort, constructors, recursor)?;
            }
            DeclPayload::MutualInductiveBlock {
                name,
                universe_params,
                universe_constraints,
                inductives,
            } => {
                out.push(8);
                let raw = self.name(*name)?;
                let (_, mapped) = self.mapped_name(self.module.module(), &raw)?;
                put_name(out, &mapped);
                self.names(out, universe_params)?;
                self.constraints(out, universe_constraints)?;
                put_u64(out, inductives.len() as u64);
                for inductive in inductives {
                    self.mutual_inductive(out, inductive)?;
                }
            }
        }
        Ok(())
    }

    fn basic_decl(
        &self,
        out: &mut Vec<u8>,
        tag: u8,
        name: NameId,
        universe_params: &[NameId],
        ty: TermId,
        body: Option<TermId>,
    ) -> Result<(), DeclarationClosureError> {
        out.push(tag);
        let raw = self.name(name)?;
        let (_, mapped) = self.mapped_name(self.module.module(), &raw)?;
        put_name(out, &mapped);
        self.names(out, universe_params)?;
        self.term(out, ty)?;
        if let Some(body) = body {
            self.term(out, body)?;
        }
        Ok(())
    }

    fn names(&self, out: &mut Vec<u8>, names: &[NameId]) -> Result<(), DeclarationClosureError> {
        put_u64(out, names.len() as u64);
        for name in names {
            put_name(out, &self.name(*name)?);
        }
        Ok(())
    }

    fn constraints(
        &self,
        out: &mut Vec<u8>,
        constraints: &[UniverseConstraintSpec],
    ) -> Result<(), DeclarationClosureError> {
        put_u64(out, constraints.len() as u64);
        for constraint in constraints {
            self.level(out, constraint.lhs)?;
            put_str(out, &format!("{:?}", constraint.relation));
            self.level(out, constraint.rhs)?;
        }
        Ok(())
    }

    fn binders(
        &self,
        out: &mut Vec<u8>,
        binders: &[BinderType],
    ) -> Result<(), DeclarationClosureError> {
        put_u64(out, binders.len() as u64);
        for binder in binders {
            self.term(out, binder.ty)?;
        }
        Ok(())
    }

    fn constructors(
        &self,
        out: &mut Vec<u8>,
        constructors: &[ConstructorSpec],
    ) -> Result<(), DeclarationClosureError> {
        put_u64(out, constructors.len() as u64);
        for constructor in constructors {
            let raw = self.name(constructor.name)?;
            let (_, mapped) = self.mapped_name(self.module.module(), &raw)?;
            put_name(out, &mapped);
            self.term(out, constructor.ty)?;
        }
        Ok(())
    }

    fn recursor(
        &self,
        out: &mut Vec<u8>,
        recursor: &Option<RecursorSpec>,
    ) -> Result<(), DeclarationClosureError> {
        match recursor {
            None => out.push(0),
            Some(recursor) => {
                out.push(1);
                let raw = self.name(recursor.name)?;
                let (_, mapped) = self.mapped_name(self.module.module(), &raw)?;
                put_name(out, &mapped);
                self.names(out, &recursor.universe_params)?;
                self.term(out, recursor.ty)?;
                put_u64(out, recursor.rules.minor_start as u64);
                put_u64(out, recursor.rules.major_index as u64);
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn inductive(
        &self,
        out: &mut Vec<u8>,
        name: NameId,
        params: &[BinderType],
        indices: &[BinderType],
        sort: LevelId,
        constructors: &[ConstructorSpec],
        recursor: &Option<RecursorSpec>,
    ) -> Result<(), DeclarationClosureError> {
        let raw = self.name(name)?;
        let (_, mapped) = self.mapped_name(self.module.module(), &raw)?;
        put_name(out, &mapped);
        self.binders(out, params)?;
        self.binders(out, indices)?;
        self.level(out, sort)?;
        self.constructors(out, constructors)?;
        self.recursor(out, recursor)
    }

    fn mutual_inductive(
        &self,
        out: &mut Vec<u8>,
        inductive: &MutualInductiveSpec,
    ) -> Result<(), DeclarationClosureError> {
        self.inductive(
            out,
            inductive.name,
            &inductive.params,
            &inductive.indices,
            inductive.sort,
            &inductive.constructors,
            &inductive.recursor,
        )
    }
}

const fn reducibility_tag(value: CertReducibility) -> u8 {
    match value {
        CertReducibility::Reducible => 0,
        CertReducibility::Opaque => 1,
    }
}

const fn opacity_tag(value: Opacity) -> u8 {
    match value {
        Opacity::Opaque => 0,
    }
}

fn domain_hash(domain: &[u8], bytes: &[u8]) -> Hash {
    let mut digest = Sha256::new();
    digest.update(domain);
    digest.update(bytes);
    digest.finalize().into()
}

fn put_identity(out: &mut Vec<u8>, identity: &GlobalDeclarationIdentity) {
    put_name(out, &identity.module);
    put_name(out, &identity.name);
    put_str(out, identity.kind.as_str());
    out.extend_from_slice(&identity.decl_interface_hash);
}

fn put_optional_hash(out: &mut Vec<u8>, value: Option<Hash>) {
    match value {
        None => out.push(0),
        Some(hash) => {
            out.push(1);
            out.extend_from_slice(&hash);
        }
    }
}

fn put_identities(out: &mut Vec<u8>, identities: &[GlobalDeclarationIdentity]) {
    put_u64(out, identities.len() as u64);
    for identity in identities {
        put_identity(out, identity);
    }
}

fn put_vec_bytes(out: &mut Vec<u8>, values: &[Vec<u8>]) {
    put_u64(out, values.len() as u64);
    for value in values {
        put_bytes(out, value);
    }
}

fn put_name(out: &mut Vec<u8>, name: &Name) {
    put_u64(out, name.0.len() as u64);
    for component in &name.0 {
        put_str(out, component);
    }
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_bytes(out, value.as_bytes());
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_u64(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        build_module_cert, encode_module_cert, verify_module_cert, AxiomPolicy, CoreModule,
        VerifierSession,
    };
    use npa_kernel::{Decl, Expr, Level, Reducibility};

    fn identity_type() -> Expr {
        Expr::pi(
            "A",
            Expr::sort(Level::param("u")),
            Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
        )
    }

    fn identity_value() -> Expr {
        Expr::lam(
            "A",
            Expr::sort(Level::param("u")),
            Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
        )
    }

    fn fixture_module(module: &str) -> CoreModule {
        CoreModule {
            name: Name::from_dotted(module),
            declarations: vec![
                Decl::Def {
                    name: "id".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: identity_type(),
                    value: identity_value(),
                    reducibility: Reducibility::Reducible,
                },
                Decl::Def {
                    name: "alias".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: identity_type(),
                    value: Expr::konst("id", vec![Level::param("u")]),
                    reducibility: Reducibility::Reducible,
                },
                Decl::Def {
                    name: "unrelated".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: identity_type(),
                    value: identity_value(),
                    reducibility: Reducibility::Reducible,
                },
            ],
        }
    }

    fn fixture_module_with_unrelated_alias(module: &str) -> CoreModule {
        let mut module = fixture_module(module);
        module.declarations.push(Decl::Def {
            name: "unrelated_alias".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: identity_type(),
            value: Expr::konst("unrelated", vec![Level::param("u")]),
            reducibility: Reducibility::Reducible,
        });
        module
    }

    fn verify(module: CoreModule) -> VerifiedModule {
        let cert = build_module_cert(module, &[]).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        verify_module_cert(&bytes, &mut VerifierSession::new(), &AxiomPolicy::normal()).unwrap()
    }

    fn export_identity(module: &VerifiedModule, name: &str) -> GlobalDeclarationIdentity {
        let export = module
            .export_block()
            .iter()
            .find(|export| module.name_table()[export.name].as_dotted() == name)
            .unwrap();
        GlobalDeclarationIdentity {
            module: module.module().clone(),
            name: Name::from_dotted(name),
            kind: export_kind(export.kind),
            decl_interface_hash: export.decl_interface_hash,
        }
    }

    #[test]
    fn selected_definition_includes_support_and_excludes_unrelated_declaration() {
        let module = verify(fixture_module("Fixture.Source"));
        let root = export_identity(&module, "alias");
        let modules = BTreeMap::from([(module.module().clone(), module)]);
        let closure = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        let names = closure
            .declarations
            .iter()
            .map(|row| row.identity.name.as_dotted())
            .collect::<Vec<_>>();
        assert_eq!(names, vec!["alias", "id"]);
        assert_eq!(closure.declarations[0].role, DeclarationClosureRole::Root);
        assert_eq!(
            closure.declarations[1].role,
            DeclarationClosureRole::Support
        );
        assert_ne!(closure.declaration_closure_hash, [0; 32]);
    }

    #[test]
    fn source_family_expands_atomically_and_rejects_externalized_root_owner() {
        let module = verify(fixture_module("Fixture.Family"));
        let id = export_identity(&module, "id");
        let alias = export_identity(&module, "alias");
        let indexes = declaration_owner_indices(&module).unwrap();
        let families =
            ValidatedSourceDeclarationFamilies::new(vec![ValidatedSourceDeclarationFamily {
                owner: id.clone(),
                members: vec![
                    ValidatedSourceDeclarationMember {
                        identity: id.clone(),
                        decl_index: indexes[&id.name],
                    },
                    ValidatedSourceDeclarationMember {
                        identity: alias.clone(),
                        decl_index: indexes[&alias.name],
                    },
                ],
            }])
            .unwrap();
        let modules = BTreeMap::from([(module.module().clone(), module)]);
        let closure = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([alias.clone()]),
            &families,
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        assert_eq!(closure.declarations.len(), 2);
        assert!(closure
            .declarations
            .iter()
            .all(|row| row.role == DeclarationClosureRole::Root));

        let error = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([alias]),
            &families,
            &BTreeMap::from([(id.clone(), id)]),
            DeclarationClosureLimits::default(),
        )
        .unwrap_err();
        assert_eq!(
            error.reason,
            DeclarationClosureErrorReason::IdentityMismatch
        );
    }

    #[test]
    fn externalization_names_only_reached_family_members_and_rejects_materialized_split() {
        let module = verify(fixture_module_with_unrelated_alias(
            "Fixture.ExternalizedFamily",
        ));
        let root = export_identity(&module, "alias");
        let support = export_identity(&module, "id");
        let unrelated = export_identity(&module, "unrelated");
        let unrelated_root = export_identity(&module, "unrelated_alias");
        let indexes = declaration_owner_indices(&module).unwrap();
        let families =
            ValidatedSourceDeclarationFamilies::new(vec![ValidatedSourceDeclarationFamily {
                owner: support.clone(),
                members: vec![
                    ValidatedSourceDeclarationMember {
                        identity: support.clone(),
                        decl_index: indexes[&support.name],
                    },
                    ValidatedSourceDeclarationMember {
                        identity: unrelated.clone(),
                        decl_index: indexes[&unrelated.name],
                    },
                ],
            }])
            .unwrap();
        let modules = BTreeMap::from([(module.module().clone(), module)]);
        let closure = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root.clone()]),
            &families,
            &BTreeMap::from([(support.clone(), support.clone())]),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        assert_eq!(
            closure
                .declarations
                .iter()
                .map(|row| row.identity.name.as_dotted())
                .collect::<Vec<_>>(),
            vec!["alias"]
        );
        assert_eq!(
            closure.externalized,
            vec![(support.clone(), support.clone())]
        );

        let error = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root, unrelated_root]),
            &families,
            &BTreeMap::from([(support.clone(), support)]),
            DeclarationClosureLimits::default(),
        )
        .unwrap_err();
        assert_eq!(
            error.reason,
            DeclarationClosureErrorReason::SourceFamilyPartialExternalization
        );
    }

    #[test]
    fn normalized_projection_is_equal_after_exact_module_mapping() {
        let source = verify(fixture_module("Fixture.Source"));
        let target = verify(fixture_module("Mathlib.Target"));
        let source_root = export_identity(&source, "alias");
        let target_root = export_identity(&target, "alias");
        let source_modules = BTreeMap::from([(source.module().clone(), source)]);
        let target_modules = BTreeMap::from([(target.module().clone(), target)]);
        let source_closure = declaration_dependency_closure(
            &source_modules,
            &BTreeSet::from([source_root]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        let target_closure = declaration_dependency_closure(
            &target_modules,
            &BTreeSet::from([target_root]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        let mapping = ["alias", "id"]
            .into_iter()
            .map(|name| {
                let source =
                    export_identity(&source_modules[&Name::from_dotted("Fixture.Source")], name);
                let target =
                    export_identity(&target_modules[&Name::from_dotted("Mathlib.Target")], name);
                (source, target)
            })
            .collect::<BTreeMap<_, _>>();
        let source_projection =
            normalized_declaration_closure_projection(&source_modules, &source_closure, &mapping)
                .unwrap();
        let target_projection = normalized_declaration_closure_projection(
            &target_modules,
            &target_closure,
            &BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(source_projection, target_projection);
        assert_eq!(
            normalized_declaration_closure_hash(&source_projection),
            normalized_declaration_closure_hash(&target_projection)
        );

        let mut regrouped_target = target_closure.clone();
        regrouped_target.declarations[0].family_owner =
            regrouped_target.declarations[1].identity.clone();
        assert_ne!(
            source_projection,
            normalized_declaration_closure_projection(
                &target_modules,
                &regrouped_target,
                &BTreeMap::new(),
            )
            .unwrap()
        );

        let mut generated_target = target_closure.clone();
        let generated_identity = generated_target.declarations[1].identity.clone();
        generated_target.declarations[0]
            .generated_exports
            .push(DeclarationClosureExport {
                identity: generated_identity,
                type_hash: [0; 32],
                body_hash: None,
            });
        assert_ne!(
            source_projection,
            normalized_declaration_closure_projection(
                &target_modules,
                &generated_target,
                &BTreeMap::new(),
            )
            .unwrap()
        );
    }

    #[test]
    fn normalized_projection_sorts_externalizations_after_mapping() {
        fn identity(module: &str, name: &str, hash: u8) -> GlobalDeclarationIdentity {
            GlobalDeclarationIdentity {
                module: Name::from_dotted(module),
                name: Name::from_dotted(name),
                kind: DeclarationClosureKind::Definition,
                decl_interface_hash: [hash; 32],
            }
        }

        let source_a = identity("Source.A", "item", 1);
        let source_b = identity("Source.B", "item", 2);
        let target_y = identity("Target.Y", "item", 2);
        let target_z = identity("Target.Z", "item", 1);
        let empty_closure = || DeclarationClosure {
            requested_roots: Vec::new(),
            root_owners: Vec::new(),
            declarations: Vec::new(),
            externalized: Vec::new(),
            builtins: Vec::new(),
            allowed_axioms: Vec::new(),
            edges: Vec::new(),
            declaration_closure_hash: [0; 32],
        };
        let mut source_closure = empty_closure();
        source_closure.externalized = vec![
            (source_a.clone(), target_z.clone()),
            (source_b.clone(), target_y.clone()),
        ];
        let mut target_closure = empty_closure();
        target_closure.externalized = vec![
            (target_y.clone(), target_y.clone()),
            (target_z.clone(), target_z.clone()),
        ];
        let mapping = BTreeMap::from([(source_a, target_z), (source_b, target_y)]);

        assert_eq!(
            normalized_declaration_closure_projection(&BTreeMap::new(), &source_closure, &mapping,)
                .unwrap(),
            normalized_declaration_closure_projection(
                &BTreeMap::new(),
                &target_closure,
                &BTreeMap::new(),
            )
            .unwrap()
        );
    }

    #[test]
    fn normalized_projection_hashes_shared_dags_and_ignores_unselected_terms() {
        let module_name = Name::from_dotted("Fixture.SharedDag");
        let module = verify(fixture_module("Fixture.SharedDag"));
        let root = export_identity(&module, "alias");
        let mut modules = BTreeMap::from([(module_name.clone(), module)]);
        let closure = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        let alias_index = closure
            .declarations
            .iter()
            .find(|row| row.identity.name.as_dotted() == "alias")
            .unwrap()
            .decl_index;
        let module = modules.get_mut(&module_name).unwrap();
        let mut shared = match &module.declarations[alias_index].decl {
            DeclPayload::Def { ty, .. } => *ty,
            other => panic!("expected alias definition, got {other:?}"),
        };
        module.term_table.push(TermNode::Const {
            global_ref: GlobalRef::Local {
                decl_index: usize::MAX,
            },
            levels: Vec::new(),
        });
        for _ in 0..18 {
            let parent = module.term_table.len();
            module.term_table.push(TermNode::Pi {
                ty: shared,
                body: shared,
            });
            shared = parent;
        }
        match &mut module.declarations[alias_index].decl {
            DeclPayload::Def { ty, .. } => *ty = shared,
            other => panic!("expected alias definition, got {other:?}"),
        }

        let projection =
            normalized_declaration_closure_projection(&modules, &closure, &BTreeMap::new())
                .unwrap();
        assert!(projection.len() < 16_384);
        assert_eq!(
            projection,
            normalized_declaration_closure_projection(&modules, &closure, &BTreeMap::new(),)
                .unwrap()
        );
    }

    #[test]
    fn normalized_projection_enforces_closure_resource_limits() {
        let module = verify(fixture_module("Fixture.ProjectionLimit"));
        let root = export_identity(&module, "alias");
        let modules = BTreeMap::from([(module.module().clone(), module)]);
        let mut closure = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root.clone()]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap();
        closure.requested_roots = vec![root; DECLARATION_CLOSURE_LIMITS_V1.requested_roots + 1];

        let error = normalized_declaration_closure_projection(&modules, &closure, &BTreeMap::new())
            .unwrap_err();
        assert_eq!(error.reason, DeclarationClosureErrorReason::LimitExceeded);
        assert_eq!(error.field, Some("requested_roots"));
    }

    #[test]
    fn local_axiom_and_resource_limit_fail_closed() {
        let axiom = verify(CoreModule {
            name: Name::from_dotted("Fixture.Axiom"),
            declarations: vec![Decl::Axiom {
                name: "P".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            }],
        });
        let root = export_identity(&axiom, "P");
        let modules = BTreeMap::from([(axiom.module().clone(), axiom)]);
        let error = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits::default(),
        )
        .unwrap_err();
        assert_eq!(
            error.reason,
            DeclarationClosureErrorReason::CustomAxiomRejected
        );

        let ordinary = verify(fixture_module("Fixture.Limit"));
        let root = export_identity(&ordinary, "alias");
        let modules = BTreeMap::from([(ordinary.module().clone(), ordinary)]);
        let error = declaration_dependency_closure(
            &modules,
            &BTreeSet::from([root.clone()]),
            &ValidatedSourceDeclarationFamilies::default(),
            &BTreeMap::new(),
            DeclarationClosureLimits {
                requested_roots: 0,
                ..DeclarationClosureLimits::default()
            },
        )
        .unwrap_err();
        assert_eq!(error.reason, DeclarationClosureErrorReason::LimitExceeded);
        assert_eq!(error.field, Some("requested_roots"));

        let mut edges = BTreeSet::new();
        let edge = DeclarationDependencyEdge {
            source: root.clone(),
            target: root,
            externalized: false,
        };
        let error = insert_dependency_edge(&mut edges, edge, 0).unwrap_err();
        assert_eq!(error.reason, DeclarationClosureErrorReason::LimitExceeded);
        assert_eq!(error.field, Some("dependency_edges"));
        assert!(edges.is_empty());
    }
}
