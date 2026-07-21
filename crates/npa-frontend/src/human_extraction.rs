//! Deterministic, semantic extraction of selected Human Surface declarations.
//!
//! The result is untrusted authoring material. Callers must re-elaborate it
//! and compare verified certificate projections before accepting a promotion.

use std::collections::{BTreeMap, BTreeSet};

use npa_kernel::{Expr, Level};
use sha2::{Digest, Sha256};

use crate::{
    parse_human_module_with_source_interfaces, resolve_human_module_with_source_interfaces, FileId,
    HumanCompileOptions, HumanDiagnostic, HumanDiagnosticKind, HumanGlobalRef,
    HumanImportedSourceInterface, HumanItem, HumanName, HumanResolvedName, HumanResult, Span,
    VerifiedExport, VerifiedImport,
};

const EXTRACTION_DOMAIN: &[u8] = b"NPA-HUMAN-DECLARATION-EXTRACTION-v1\0";

/// Stable Human/source-family member kind.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum HumanDeclarationFamilyMemberKind {
    /// Definition or equation definition.
    Definition,
    /// Theorem.
    Theorem,
    /// Axiom.
    Axiom,
    /// Inductive owner.
    Inductive,
    /// Class owner.
    Class,
    /// Class-field projection.
    ClassField,
    /// Typeclass instance.
    Instance,
    /// Generated constructor.
    Constructor,
    /// Generated recursor.
    Recursor,
}

impl HumanDeclarationFamilyMemberKind {
    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::Theorem => "theorem",
            Self::Axiom => "axiom",
            Self::Inductive => "inductive",
            Self::Class => "class",
            Self::ClassField => "class_field",
            Self::Instance => "instance",
            Self::Constructor => "constructor",
            Self::Recursor => "recursor",
        }
    }
}

/// One proposed declaration emitted by a top-level Human item.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HumanDeclarationFamilyMember {
    /// Qualified declaration name.
    pub name: npa_cert::Name,
    /// Human/source role.
    pub kind: HumanDeclarationFamilyMemberKind,
    /// Exact source span that names or generates the member.
    pub span: Span,
}

/// One extraction-atomic top-level Human source item.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HumanSourceDeclarationFamily {
    /// Stable owner name.
    pub owner: npa_cert::Name,
    /// Human kind of the owner.
    pub owner_kind: HumanDeclarationFamilyMemberKind,
    /// Exact complete top-level item span.
    pub item_span: Span,
    /// Every explicit and generated declaration emitted by the item.
    pub members: Vec<HumanDeclarationFamilyMember>,
}

/// Canonically ordered source declaration family proposal.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct HumanSourceDeclarationFamilies {
    /// Families in source order.
    pub families: Vec<HumanSourceDeclarationFamily>,
}

/// Exact global identity used for semantic source rewriting.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HumanGlobalIdentity {
    /// Provider module.
    pub module: npa_cert::ModuleName,
    /// Public declaration name.
    pub name: npa_cert::Name,
    /// Verified declaration-interface hash.
    pub decl_interface_hash: npa_cert::Hash,
}

/// One exact semantic global rewrite.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HumanGlobalMappingRow {
    /// Resolved source identity.
    pub source: HumanGlobalIdentity,
    /// Required target identity.
    pub target: HumanGlobalIdentity,
}

/// Complete deterministic global mapping for extraction.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct HumanGlobalMapping {
    /// Strictly unique mapping rows.
    pub rows: Vec<HumanGlobalMappingRow>,
}

/// One declaration expected from the verified selected closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HumanSelectedDeclaration {
    /// Qualified source declaration name.
    pub name: npa_cert::Name,
    /// Reconciled Human/source kind.
    pub kind: HumanDeclarationFamilyMemberKind,
    /// Exact owning top-level item span.
    pub item_span: Span,
    /// Verified declaration-interface hash.
    pub decl_interface_hash: npa_cert::Hash,
}

/// Verified selection supplied by the promotion planner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HumanDeclarationSelection {
    /// Source certificate module.
    pub source_module: npa_cert::ModuleName,
    /// New target certificate module.
    pub target_module: npa_cert::ModuleName,
    /// Exact materialized declaration members.
    pub declarations: Vec<HumanSelectedDeclaration>,
}

/// Name-resolution mechanism recorded for a semantic rewrite.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum HumanRewriteResolution {
    /// A qualified global name was used.
    Qualified,
    /// An unqualified local global was used.
    Local,
    /// An unqualified imported global was used.
    Imported,
    /// A builtin global was used.
    Builtin,
}

impl HumanRewriteResolution {
    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Qualified => "qualified",
            Self::Local => "local",
            Self::Imported => "imported",
            Self::Builtin => "builtin",
        }
    }
}

/// One parser-owned span and its exact semantic rewrite provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HumanResolvedRewrite {
    /// Exact identifier span rewritten.
    pub span: Span,
    /// Resolved source identity.
    pub source: HumanGlobalIdentity,
    /// Required target identity.
    pub target: HumanGlobalIdentity,
    /// Resolution mechanism.
    pub resolution: HumanRewriteResolution,
}

/// Deterministic extracted Human module and audit metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExtractedHumanModule {
    /// Generated target source ending in exactly one newline.
    pub source: String,
    /// Retained materialized declaration identities.
    pub retained_declarations: Vec<npa_cert::Name>,
    /// Validated source-family proposal used by extraction.
    pub source_families: HumanSourceDeclarationFamilies,
    /// Retained import/open/namespace/notation directive spans.
    pub retained_context_directives: Vec<Span>,
    /// Ordered semantic rewrite provenance.
    pub rewrites: Vec<HumanResolvedRewrite>,
    /// Domain-separated deterministic untrusted source projection hash.
    pub source_projection_hash: npa_cert::Hash,
}

/// Discover extraction-atomic source declaration families without trusting them.
pub fn collect_human_source_declaration_families(
    file_id: FileId,
    source: &str,
    imported_interfaces: &[HumanImportedSourceInterface],
) -> HumanResult<HumanSourceDeclarationFamilies> {
    let module = parse_human_module_with_source_interfaces(file_id, source, imported_interfaces)?;
    let mut namespaces = Vec::<Vec<String>>::new();
    let mut families = Vec::new();
    for item in module.items {
        match item {
            HumanItem::NamespaceStart { name, .. } => namespaces.push(name.parts),
            HumanItem::NamespaceEnd { .. } => {
                namespaces.pop();
            }
            HumanItem::Def(decl) => families.push(single_family(
                qualify(&namespaces, &decl.name),
                HumanDeclarationFamilyMemberKind::Definition,
                decl.span,
            )),
            HumanItem::EquationDef(decl) => families.push(single_family(
                qualify(&namespaces, &decl.name),
                HumanDeclarationFamilyMemberKind::Definition,
                decl.span,
            )),
            HumanItem::Theorem(decl) => families.push(single_family(
                qualify(&namespaces, &decl.name),
                HumanDeclarationFamilyMemberKind::Theorem,
                decl.span,
            )),
            HumanItem::Axiom(decl) => families.push(single_family(
                qualify(&namespaces, &decl.name),
                HumanDeclarationFamilyMemberKind::Axiom,
                decl.span,
            )),
            HumanItem::Instance(decl) => families.push(single_family(
                qualify(&namespaces, &decl.name),
                HumanDeclarationFamilyMemberKind::Instance,
                decl.span,
            )),
            HumanItem::Inductive(decl) => {
                let owner = qualify(&namespaces, &decl.name);
                let mut members = vec![member(
                    owner.clone(),
                    HumanDeclarationFamilyMemberKind::Inductive,
                    decl.span,
                )];
                members.extend(decl.constructors.into_iter().map(|constructor| {
                    member(
                        child_name(&owner, &constructor.name),
                        HumanDeclarationFamilyMemberKind::Constructor,
                        constructor.span,
                    )
                }));
                members.push(member(
                    generated_child(&owner, "rec"),
                    HumanDeclarationFamilyMemberKind::Recursor,
                    decl.span,
                ));
                families.push(HumanSourceDeclarationFamily {
                    owner,
                    owner_kind: HumanDeclarationFamilyMemberKind::Inductive,
                    item_span: decl.span,
                    members,
                });
            }
            HumanItem::Class(decl) => {
                let owner = qualify(&namespaces, &decl.name);
                let mut members = vec![
                    member(
                        owner.clone(),
                        HumanDeclarationFamilyMemberKind::Class,
                        decl.span,
                    ),
                    member(
                        generated_child(&owner, "mk"),
                        HumanDeclarationFamilyMemberKind::Constructor,
                        decl.span,
                    ),
                    member(
                        generated_child(&owner, "rec"),
                        HumanDeclarationFamilyMemberKind::Recursor,
                        decl.span,
                    ),
                ];
                members.extend(decl.fields.into_iter().map(|field| {
                    member(
                        child_name(&owner, &field.name),
                        HumanDeclarationFamilyMemberKind::ClassField,
                        field.span,
                    )
                }));
                families.push(HumanSourceDeclarationFamily {
                    owner,
                    owner_kind: HumanDeclarationFamilyMemberKind::Class,
                    item_span: decl.span,
                    members,
                });
            }
            HumanItem::Import { .. } | HumanItem::Open { .. } | HumanItem::Notation(_) => {}
        }
    }
    Ok(HumanSourceDeclarationFamilies { families })
}

/// Extract selected Human declarations using only parser/resolver-owned spans.
pub fn extract_human_declaration_source(
    file_id: FileId,
    source: &str,
    imported_interfaces: &[HumanImportedSourceInterface],
    selection: &HumanDeclarationSelection,
    mapping: &HumanGlobalMapping,
) -> HumanResult<ExtractedHumanModule> {
    validate_mapping(mapping, file_id)?;
    let families = collect_human_source_declaration_families(file_id, source, imported_interfaces)?;
    let selected_spans = validate_selection(&families, selection, file_id)?;
    let module = parse_human_module_with_source_interfaces(file_id, source, imported_interfaces)?;
    let imports = extraction_imports(imported_interfaces, file_id)?;
    let resolved = resolve_human_module_with_source_interfaces(
        selection.source_module.clone(),
        module.clone(),
        &imports,
        imported_interfaces,
        &HumanCompileOptions::default(),
    )?;

    let mut rewrites = Vec::new();
    for name_use in &resolved.resolved_names {
        if !selected_spans
            .iter()
            .any(|span| span_contains(*span, name_use.source.span))
        {
            continue;
        }
        let HumanResolvedName::Global(global) = &name_use.resolved else {
            continue;
        };
        let (module, name, hash, base_resolution) = match global {
            HumanGlobalRef::Imported {
                module,
                name,
                decl_interface_hash,
            } => (
                module.clone(),
                name.clone(),
                *decl_interface_hash,
                HumanRewriteResolution::Imported,
            ),
            HumanGlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => (
                npa_cert::Name::from_dotted("$builtin"),
                name.clone(),
                *decl_interface_hash,
                HumanRewriteResolution::Builtin,
            ),
            HumanGlobalRef::Local { name, .. } | HumanGlobalRef::LocalGenerated { name, .. } => {
                let matching = mapping.rows.iter().find(|row| {
                    row.source.module == selection.source_module && row.source.name == *name
                });
                let Some(row) = matching else {
                    continue;
                };
                (
                    selection.source_module.clone(),
                    name.clone(),
                    row.source.decl_interface_hash,
                    HumanRewriteResolution::Local,
                )
            }
        };
        let source_identity = HumanGlobalIdentity {
            module,
            name,
            decl_interface_hash: hash,
        };
        let Some(row) = mapping
            .rows
            .iter()
            .find(|row| row.source == source_identity)
        else {
            continue;
        };
        let resolution = if name_use.source.parts.len() > 1 {
            HumanRewriteResolution::Qualified
        } else {
            base_resolution
        };
        if row.source != row.target {
            rewrites.push(HumanResolvedRewrite {
                span: name_use.source.span,
                source: row.source.clone(),
                target: row.target.clone(),
                resolution,
            });
        }
    }
    for item in &module.items {
        let HumanItem::Notation(decl) = item else {
            continue;
        };
        for entry in resolved
            .notation_table
            .iter()
            .filter(|entry| entry.span == decl.span)
            .filter(|entry| notation_entry_is_used(entry, &selected_spans, &resolved))
        {
            let (module, name, hash, base_resolution) = match &entry.target {
                HumanGlobalRef::Imported {
                    module,
                    name,
                    decl_interface_hash,
                } => (
                    module.clone(),
                    name.clone(),
                    *decl_interface_hash,
                    HumanRewriteResolution::Imported,
                ),
                HumanGlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                } => (
                    npa_cert::Name::from_dotted("$builtin"),
                    name.clone(),
                    *decl_interface_hash,
                    HumanRewriteResolution::Builtin,
                ),
                HumanGlobalRef::Local { name, .. }
                | HumanGlobalRef::LocalGenerated { name, .. } => {
                    let Some(row) = mapping.rows.iter().find(|row| {
                        row.source.module == selection.source_module && row.source.name == *name
                    }) else {
                        continue;
                    };
                    (
                        selection.source_module.clone(),
                        name.clone(),
                        row.source.decl_interface_hash,
                        HumanRewriteResolution::Local,
                    )
                }
            };
            let source_identity = HumanGlobalIdentity {
                module,
                name,
                decl_interface_hash: hash,
            };
            let Some(row) = mapping
                .rows
                .iter()
                .find(|row| row.source == source_identity)
            else {
                continue;
            };
            if row.source != row.target {
                rewrites.push(HumanResolvedRewrite {
                    span: decl.target.span,
                    source: row.source.clone(),
                    target: row.target.clone(),
                    resolution: if decl.target.parts.len() > 1 {
                        HumanRewriteResolution::Qualified
                    } else {
                        base_resolution
                    },
                });
            }
        }
    }
    rewrites.sort_by_key(|rewrite| (rewrite.span.start.0, rewrite.span.end.0));
    reject_overlapping_rewrites(&rewrites, file_id)?;

    let local_notation_spans = module
        .items
        .iter()
        .filter_map(|item| match item {
            HumanItem::Notation(decl) => Some(decl.span),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut notation_insertions = BTreeMap::<Span, Vec<String>>::new();
    let mut notation_required_imports = BTreeSet::new();
    for entry in resolved
        .notation_table
        .iter()
        .filter(|entry| !local_notation_spans.contains(&entry.span))
        .filter(|entry| notation_entry_is_used(entry, &selected_spans, &resolved))
    {
        let target_name = global_ref_name(&entry.target);
        let providers = imported_interfaces
            .iter()
            .filter(|interface| {
                interface.source_interface.notations.iter().any(|notation| {
                    notation.kind == entry.kind
                        && notation.associativity == entry.associativity
                        && notation.precedence == entry.precedence
                        && notation.token == entry.token
                        && notation.namespace == entry.namespace
                        && notation.span == entry.span
                        && npa_cert::Name(notation.target.parts.clone()) == *target_name
                })
            })
            .map(|interface| interface.module.clone())
            .collect::<BTreeSet<_>>();
        if providers.len() != 1 {
            return Err(extraction_error(
                file_id,
                "used imported notation has no unique source interface",
            ));
        }
        let provider = providers.iter().next().expect("one notation provider");
        let import_span = module
            .items
            .iter()
            .find_map(|item| match item {
                HumanItem::Import { module, span }
                    if npa_cert::Name(module.parts.clone()) == *provider =>
                {
                    Some(*span)
                }
                _ => None,
            })
            .ok_or_else(|| {
                extraction_error(file_id, "used imported notation has no source import")
            })?;
        notation_required_imports.insert(provider.clone());
        let target =
            global_identity_for_notation_target(&entry.target, &selection.source_module, mapping)?;
        notation_insertions
            .entry(import_span)
            .or_default()
            .push(render_synthesized_notation(entry, &target.name));
    }
    for insertions in notation_insertions.values_mut() {
        insertions.sort();
        insertions.dedup();
    }

    let imported_module_map = module_mapping(mapping, &selection.source_module);
    let mut import_rewrites = Vec::new();
    for item in &module.items {
        if let HumanItem::Import { module, .. } = item {
            let source_module = npa_cert::Name(module.parts.clone());
            if let Some(target_modules) = imported_module_map.get(&source_module) {
                if target_modules.len() != 1 || !target_modules.contains(&source_module) {
                    import_rewrites.push((
                        module.span,
                        target_modules
                            .iter()
                            .map(npa_cert::Name::as_dotted)
                            .collect::<Vec<_>>()
                            .join("\nimport "),
                    ));
                }
            }
        }
    }

    let required_imports = rewrites
        .iter()
        .filter(|rewrite| rewrite.source.module != selection.source_module)
        .map(|rewrite| rewrite.source.module.clone())
        .chain(notation_required_imports)
        .collect::<BTreeSet<_>>();
    let retained_item_spans = retained_item_spans(
        &module.items,
        &selected_spans,
        &required_imports,
        &imported_module_map,
        &resolved,
    );
    let mut retained_imports = BTreeSet::new();
    for item in &module.items {
        let HumanItem::Import { module, span } = item else {
            continue;
        };
        if !retained_item_spans.contains(span) {
            continue;
        }
        let source = npa_cert::Name(module.parts.clone());
        if let Some(targets) = imported_module_map.get(&source) {
            retained_imports.extend(targets.iter().cloned());
        } else {
            retained_imports.insert(source);
        }
    }
    let synthesized_imports = rewrites
        .iter()
        .map(|rewrite| rewrite.target.module.clone())
        .filter(|module| {
            module != &selection.target_module
                && module.as_dotted() != "$builtin"
                && !retained_imports.contains(module)
        })
        .collect::<BTreeSet<_>>();
    let retained_context_directives = module
        .items
        .iter()
        .filter(|item| is_context_item(item) && retained_item_spans.contains(&item.span()))
        .map(HumanItem::span)
        .collect::<Vec<_>>();
    let mut replacements = rewrites
        .iter()
        .map(|rewrite| (rewrite.span, rewrite.target.name.as_dotted()))
        .chain(import_rewrites)
        .collect::<Vec<_>>();
    replacements.sort_by_key(|(span, _)| (span.start.0, span.end.0));
    let mut extracted = render_retained_source(
        source,
        &retained_item_spans,
        &replacements,
        &notation_insertions,
        file_id,
    )?;
    if !synthesized_imports.is_empty() {
        let imports = synthesized_imports
            .iter()
            .map(|module| format!("import {}", module.as_dotted()))
            .collect::<Vec<_>>()
            .join("\n");
        extracted = format!("{imports}\n\n{extracted}");
    }
    let retained_declarations = selection
        .declarations
        .iter()
        .map(|declaration| declaration.name.clone())
        .collect::<Vec<_>>();
    let source_projection_hash = extraction_hash(
        &extracted,
        &selection.declarations,
        &retained_context_directives,
        &rewrites,
    );
    Ok(ExtractedHumanModule {
        source: extracted,
        retained_declarations,
        source_families: families,
        retained_context_directives,
        rewrites,
        source_projection_hash,
    })
}

fn validate_selection(
    families: &HumanSourceDeclarationFamilies,
    selection: &HumanDeclarationSelection,
    file_id: FileId,
) -> HumanResult<BTreeSet<SpanKey>> {
    if selection.declarations.is_empty() {
        return Err(extraction_error(file_id, "declaration selection is empty"));
    }
    let mut names = BTreeSet::new();
    let mut spans = BTreeSet::new();
    for selected in &selection.declarations {
        if !names.insert(selected.name.clone()) {
            return Err(extraction_error(file_id, "duplicate selected declaration"));
        }
        let matches = families
            .families
            .iter()
            .filter_map(|family| {
                family
                    .members
                    .iter()
                    .find(|member| member.name == selected.name)
                    .map(|member| (family, member))
            })
            .collect::<Vec<_>>();
        if matches.len() != 1
            || matches[0].1.kind != selected.kind
            || matches[0].0.item_span != selected.item_span
        {
            return Err(HumanDiagnostic::error(
                HumanDiagnosticKind::UnsupportedSyntax,
                selected.item_span,
                format!(
                    "promotion_declaration_source_family_invalid: {}",
                    selected.name.as_dotted()
                ),
            ));
        }
        spans.insert(SpanKey::from(matches[0].0.item_span));
    }
    Ok(spans)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SpanKey {
    start: u32,
    end: u32,
}

impl From<Span> for SpanKey {
    fn from(value: Span) -> Self {
        Self {
            start: value.start.0,
            end: value.end.0,
        }
    }
}

fn span_contains(outer: SpanKey, inner: Span) -> bool {
    outer.start <= inner.start.0 && inner.end.0 <= outer.end
}

fn retained_item_spans(
    items: &[HumanItem],
    selected: &BTreeSet<SpanKey>,
    required_imports: &BTreeSet<npa_cert::Name>,
    module_map: &BTreeMap<npa_cert::Name, BTreeSet<npa_cert::Name>>,
    resolved: &crate::ResolvedHumanModule,
) -> BTreeSet<Span> {
    #[derive(Clone, Copy)]
    struct NamespaceFrame {
        start: Span,
        retained: bool,
    }

    fn retain_in_current_namespaces(
        span: Span,
        namespace_stack: &mut [NamespaceFrame],
        retained: &mut BTreeSet<Span>,
    ) {
        retained.insert(span);
        for frame in namespace_stack {
            frame.retained = true;
        }
    }

    let mut retained = BTreeSet::new();
    let mut namespace_stack = Vec::<NamespaceFrame>::new();
    for item in items {
        match item {
            HumanItem::NamespaceStart { span, .. } => namespace_stack.push(NamespaceFrame {
                start: *span,
                retained: false,
            }),
            HumanItem::NamespaceEnd { span, .. } => {
                if let Some(frame) = namespace_stack.pop() {
                    if frame.retained {
                        retained.insert(frame.start);
                        retained.insert(*span);
                    }
                }
            }
            HumanItem::Import { module, span } => {
                let name = npa_cert::Name(module.parts.clone());
                if required_imports.contains(&name) || module_map.contains_key(&name) {
                    retain_in_current_namespaces(*span, &mut namespace_stack, &mut retained);
                }
            }
            HumanItem::Open { span, .. } => {
                let used = resolved.resolved_opens.iter().any(|open| {
                    open.span == *span
                        && resolved.resolved_names.iter().any(|name_use| {
                            selected
                                .iter()
                                .any(|outer| span_contains(*outer, name_use.source.span))
                                && name_use.source.parts.len() == 1
                                && match &name_use.resolved {
                                    HumanResolvedName::Global(HumanGlobalRef::Imported {
                                        name,
                                        ..
                                    })
                                    | HumanResolvedName::Global(HumanGlobalRef::Local {
                                        name,
                                        ..
                                    })
                                    | HumanResolvedName::Global(HumanGlobalRef::LocalGenerated {
                                        name,
                                        ..
                                    }) => {
                                        let mut opened_name = open.namespace.parts.clone();
                                        opened_name.extend(name_use.source.parts.iter().cloned());
                                        name.0 == opened_name
                                    }
                                    _ => false,
                                }
                        })
                        || resolved
                            .notation_table
                            .iter()
                            .filter(|entry| entry.namespace == open.namespace.parts)
                            .any(|entry| notation_entry_is_used(entry, selected, resolved))
                });
                if used {
                    retain_in_current_namespaces(*span, &mut namespace_stack, &mut retained);
                }
            }
            HumanItem::Notation(decl) => {
                let used = resolved
                    .notation_table
                    .iter()
                    .filter(|entry| entry.span == decl.span)
                    .any(|entry| notation_entry_is_used(entry, selected, resolved));
                if used {
                    retain_in_current_namespaces(decl.span, &mut namespace_stack, &mut retained);
                }
            }
            _ if selected.contains(&SpanKey::from(item.span())) => {
                retain_in_current_namespaces(item.span(), &mut namespace_stack, &mut retained);
            }
            _ => {}
        }
    }
    retained
}

fn notation_entry_is_used(
    entry: &crate::HumanResolvedNotationEntry,
    selected: &BTreeSet<SpanKey>,
    resolved: &crate::ResolvedHumanModule,
) -> bool {
    resolved.resolved_notations.iter().any(|notation| {
        selected
            .iter()
            .any(|outer| span_contains(*outer, notation.head.span))
            && notation.head.token == entry.token
            && notation.head.kind == entry.kind
            && notation.head.precedence == entry.precedence
            && notation.head.associativity == entry.associativity
            && notation.candidates.contains(&entry.target)
    })
}

fn global_ref_name(reference: &HumanGlobalRef) -> &npa_cert::Name {
    match reference {
        HumanGlobalRef::Imported { name, .. }
        | HumanGlobalRef::Builtin { name, .. }
        | HumanGlobalRef::Local { name, .. }
        | HumanGlobalRef::LocalGenerated { name, .. } => name,
    }
}

fn global_identity_for_notation_target(
    reference: &HumanGlobalRef,
    source_module: &npa_cert::Name,
    mapping: &HumanGlobalMapping,
) -> HumanResult<HumanGlobalIdentity> {
    let source = match reference {
        HumanGlobalRef::Imported {
            module,
            name,
            decl_interface_hash,
        } => HumanGlobalIdentity {
            module: module.clone(),
            name: name.clone(),
            decl_interface_hash: *decl_interface_hash,
        },
        HumanGlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => HumanGlobalIdentity {
            module: npa_cert::Name::from_dotted("$builtin"),
            name: name.clone(),
            decl_interface_hash: *decl_interface_hash,
        },
        HumanGlobalRef::Local { name, .. } | HumanGlobalRef::LocalGenerated { name, .. } => {
            let row = mapping
                .rows
                .iter()
                .find(|row| row.source.module == *source_module && row.source.name == *name)
                .ok_or_else(|| {
                    extraction_error(
                        FileId(0),
                        "used imported notation resolved to an unmapped local target",
                    )
                })?;
            row.source.clone()
        }
    };
    Ok(mapping
        .rows
        .iter()
        .find(|row| row.source == source)
        .map(|row| row.target.clone())
        .unwrap_or(source))
}

fn render_synthesized_notation(
    entry: &crate::HumanResolvedNotationEntry,
    target: &npa_cert::Name,
) -> String {
    use crate::HumanNotationKind;

    let declaration = match entry.kind {
        HumanNotationKind::Notation => {
            format!("notation {:?} => {}", entry.token, target.as_dotted())
        }
        kind => {
            let keyword = match kind {
                HumanNotationKind::Prefix => "prefix",
                HumanNotationKind::Postfix => "postfix",
                HumanNotationKind::Infix => "infix",
                HumanNotationKind::Infixl => "infixl",
                HumanNotationKind::Infixr => "infixr",
                HumanNotationKind::Notation => unreachable!(),
            };
            format!(
                "{keyword}:{} {:?} => {}",
                entry.precedence,
                format!(" {} ", entry.token),
                target.as_dotted()
            )
        }
    };
    if entry.namespace.is_empty() {
        declaration
    } else {
        let namespace = entry.namespace.join(".");
        format!("namespace {namespace}\n{declaration}\nend {namespace}")
    }
}

fn render_retained_source(
    source: &str,
    spans: &BTreeSet<Span>,
    replacements: &[(Span, String)],
    insertions_after: &BTreeMap<Span, Vec<String>>,
    file_id: FileId,
) -> HumanResult<String> {
    let mut ordered = spans.iter().copied().collect::<Vec<_>>();
    ordered.sort_by_key(|span| (span.start.0, span.end.0));
    let mut out = String::new();
    for span in ordered {
        let start = span.start.0 as usize;
        let end = span.end.0 as usize;
        let Some(item_source) = source.get(start..end) else {
            return Err(extraction_error(
                file_id,
                "source item span is not UTF-8 aligned",
            ));
        };
        if !out.is_empty() {
            out.push_str("\n\n");
        }
        let mut item = item_source.to_owned();
        let mut local_replacements = replacements
            .iter()
            .filter(|(rewrite_span, _)| {
                span.start.0 <= rewrite_span.start.0 && rewrite_span.end.0 <= span.end.0
            })
            .collect::<Vec<_>>();
        local_replacements.sort_by_key(|(rewrite_span, _)| std::cmp::Reverse(rewrite_span.start.0));
        for (rewrite_span, replacement) in local_replacements {
            let local_start = (rewrite_span.start.0 - span.start.0) as usize;
            let local_end = (rewrite_span.end.0 - span.start.0) as usize;
            if item.get(local_start..local_end).is_none() {
                return Err(extraction_error(
                    file_id,
                    "rewrite span is not UTF-8 aligned",
                ));
            }
            item.replace_range(local_start..local_end, replacement);
        }
        out.push_str(item.trim_end());
        if let Some(insertions) = insertions_after.get(&span) {
            for insertion in insertions {
                out.push_str("\n\n");
                out.push_str(insertion);
            }
        }
    }
    out.push('\n');
    Ok(out)
}

fn extraction_imports(
    interfaces: &[HumanImportedSourceInterface],
    file_id: FileId,
) -> HumanResult<Vec<VerifiedImport>> {
    interfaces
        .iter()
        .map(|interface| {
            let mut hashes = BTreeMap::new();
            for declaration in &interface.source_interface.declarations {
                let Some(hash) = declaration.decl_interface_hash else {
                    return Err(HumanDiagnostic::error(
                        HumanDiagnosticKind::UnsupportedSyntax,
                        declaration.span,
                        "imported source interface lacks a verified declaration hash",
                    ));
                };
                hashes.insert(npa_cert::Name(declaration.name.parts.clone()), hash);
            }
            for generated in &interface.source_interface.generated_declarations {
                let Some(hash) = generated.decl_interface_hash else {
                    return Err(HumanDiagnostic::error(
                        HumanDiagnosticKind::UnsupportedSyntax,
                        generated.span,
                        "imported generated source interface lacks a verified declaration hash",
                    ));
                };
                hashes.insert(npa_cert::Name(generated.name.parts.clone()), hash);
            }
            let exports = hashes
                .iter()
                .map(|(name, hash)| VerifiedExport {
                    name: name.clone(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                    decl_interface_hash: *hash,
                })
                .collect();
            Ok(VerifiedImport {
                module: interface.module.clone(),
                export_hash: interface.export_hash,
                certificate_hash: interface.certificate_hash,
                exports,
                decl_interface_hashes: hashes,
                kernel_decls: Vec::new(),
                kernel_decl_dependencies: BTreeMap::new(),
            })
        })
        .collect::<HumanResult<Vec<_>>>()
        .map_err(|error| {
            if error.primary_span.file_id == file_id {
                error
            } else {
                extraction_error(file_id, "invalid imported source interface")
            }
        })
}

fn validate_mapping(mapping: &HumanGlobalMapping, file_id: FileId) -> HumanResult<()> {
    let mut sources = BTreeSet::new();
    for row in &mapping.rows {
        if !sources.insert(row.source.clone()) {
            return Err(extraction_error(file_id, "duplicate global mapping source"));
        }
    }
    Ok(())
}

fn module_mapping(
    mapping: &HumanGlobalMapping,
    local_source_module: &npa_cert::Name,
) -> BTreeMap<npa_cert::Name, BTreeSet<npa_cert::Name>> {
    let mut modules = BTreeMap::<npa_cert::Name, BTreeSet<npa_cert::Name>>::new();
    for row in &mapping.rows {
        if &row.source.module == local_source_module {
            continue;
        }
        modules
            .entry(row.source.module.clone())
            .or_default()
            .insert(row.target.module.clone());
    }
    modules
}

fn reject_overlapping_rewrites(
    rewrites: &[HumanResolvedRewrite],
    file_id: FileId,
) -> HumanResult<()> {
    for pair in rewrites.windows(2) {
        if pair[1].span.start.0 < pair[0].span.end.0 {
            return Err(extraction_error(file_id, "semantic rewrite spans overlap"));
        }
    }
    Ok(())
}

fn extraction_hash(
    source: &str,
    declarations: &[HumanSelectedDeclaration],
    directives: &[Span],
    rewrites: &[HumanResolvedRewrite],
) -> npa_cert::Hash {
    let mut digest = Sha256::new();
    digest.update(EXTRACTION_DOMAIN);
    put_bytes(&mut digest, source.as_bytes());
    put_u64(&mut digest, declarations.len() as u64);
    for declaration in declarations {
        put_bytes(&mut digest, declaration.name.as_dotted().as_bytes());
        put_bytes(&mut digest, declaration.kind.as_str().as_bytes());
        put_u64(&mut digest, declaration.item_span.start.0 as u64);
        put_u64(&mut digest, declaration.item_span.end.0 as u64);
        digest.update(declaration.decl_interface_hash);
    }
    put_u64(&mut digest, directives.len() as u64);
    for directive in directives {
        put_u64(&mut digest, directive.start.0 as u64);
        put_u64(&mut digest, directive.end.0 as u64);
    }
    put_u64(&mut digest, rewrites.len() as u64);
    for rewrite in rewrites {
        put_u64(&mut digest, rewrite.span.start.0 as u64);
        put_u64(&mut digest, rewrite.span.end.0 as u64);
        put_global(&mut digest, &rewrite.source);
        put_global(&mut digest, &rewrite.target);
        put_bytes(&mut digest, rewrite.resolution.as_str().as_bytes());
    }
    digest.finalize().into()
}

fn put_global(digest: &mut Sha256, identity: &HumanGlobalIdentity) {
    put_bytes(digest, identity.module.as_dotted().as_bytes());
    put_bytes(digest, identity.name.as_dotted().as_bytes());
    digest.update(identity.decl_interface_hash);
}

fn put_bytes(digest: &mut Sha256, bytes: &[u8]) {
    put_u64(digest, bytes.len() as u64);
    digest.update(bytes);
}

fn put_u64(digest: &mut Sha256, value: u64) {
    digest.update(value.to_le_bytes());
}

fn single_family(
    owner: npa_cert::Name,
    kind: HumanDeclarationFamilyMemberKind,
    item_span: Span,
) -> HumanSourceDeclarationFamily {
    HumanSourceDeclarationFamily {
        owner: owner.clone(),
        owner_kind: kind,
        item_span,
        members: vec![member(owner, kind, item_span)],
    }
}

fn member(
    name: npa_cert::Name,
    kind: HumanDeclarationFamilyMemberKind,
    span: Span,
) -> HumanDeclarationFamilyMember {
    HumanDeclarationFamilyMember { name, kind, span }
}

fn qualify(namespaces: &[Vec<String>], name: &HumanName) -> npa_cert::Name {
    let mut parts = namespaces.iter().flatten().cloned().collect::<Vec<_>>();
    parts.extend(name.parts.iter().cloned());
    npa_cert::Name(parts)
}

fn child_name(parent: &npa_cert::Name, child: &HumanName) -> npa_cert::Name {
    let mut parts = parent.0.clone();
    parts.extend(child.parts.iter().cloned());
    npa_cert::Name(parts)
}

fn generated_child(parent: &npa_cert::Name, child: &str) -> npa_cert::Name {
    let mut parts = parent.0.clone();
    parts.push(child.to_owned());
    npa_cert::Name(parts)
}

fn is_context_item(item: &HumanItem) -> bool {
    matches!(
        item,
        HumanItem::Import { .. }
            | HumanItem::Open { .. }
            | HumanItem::NamespaceStart { .. }
            | HumanItem::NamespaceEnd { .. }
            | HumanItem::Notation(_)
    )
}

fn extraction_error(file_id: FileId, message: &str) -> HumanDiagnostic {
    HumanDiagnostic::error(
        HumanDiagnosticKind::UnsupportedSyntax,
        Span::empty(file_id),
        format!("promotion_declaration_source_extraction_unsupported: {message}"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        HumanNotationAssociativity, HumanNotationKind, HumanSourceDeclarationKind,
        HumanSourceDeclarationMetadata, HumanSourceInterface, HumanSourceNotationMetadata,
    };

    #[test]
    fn family_discovery_records_namespace_class_and_generated_members() {
        let source = "namespace Demo\nclass Add (A : Type) where\n  add : A -> A -> A\nend Demo\n";
        let families = collect_human_source_declaration_families(FileId(7), source, &[]).unwrap();
        assert_eq!(families.families.len(), 1);
        let family = &families.families[0];
        assert_eq!(family.owner.as_dotted(), "Demo.Add");
        assert_eq!(
            family
                .members
                .iter()
                .map(|member| (member.name.as_dotted(), member.kind))
                .collect::<Vec<_>>(),
            vec![
                (
                    "Demo.Add".to_owned(),
                    HumanDeclarationFamilyMemberKind::Class
                ),
                (
                    "Demo.Add.mk".to_owned(),
                    HumanDeclarationFamilyMemberKind::Constructor
                ),
                (
                    "Demo.Add.rec".to_owned(),
                    HumanDeclarationFamilyMemberKind::Recursor
                ),
                (
                    "Demo.Add.add".to_owned(),
                    HumanDeclarationFamilyMemberKind::ClassField
                ),
            ]
        );
    }

    #[test]
    fn extraction_rewrites_only_resolved_global_spans_and_drops_unrelated_items() {
        let file_id = FileId(9);
        let source = "import Std.Source\n\n-- Std.foo in a comment is inert\ndef keep (Std_foo : Prop) : Prop := Std.foo\n\ndef drop : Prop := Std.foo\n";
        let hash = [3; 32];
        let mut source_interface =
            HumanSourceInterface::new(npa_cert::Name::from_dotted("Std.Source"));
        source_interface
            .declarations
            .push(HumanSourceDeclarationMetadata {
                kind: HumanSourceDeclarationKind::Def,
                name: HumanName::new(
                    vec!["Std".to_owned(), "foo".to_owned()],
                    Span::empty(file_id),
                ),
                universe_params: Vec::new(),
                binders: Vec::new(),
                decl_interface_hash: Some(hash),
                span: Span::empty(file_id),
            });
        let imports = vec![HumanImportedSourceInterface {
            module: npa_cert::Name::from_dotted("Std.Source"),
            export_hash: [4; 32],
            certificate_hash: Some([5; 32]),
            source_interface,
        }];
        let families =
            collect_human_source_declaration_families(file_id, source, &imports).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "keep")
            .unwrap();
        let selection = HumanDeclarationSelection {
            source_module: npa_cert::Name::from_dotted("Fixture.Source"),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [7; 32],
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: vec![HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Std.Source"),
                    name: npa_cert::Name::from_dotted("Std.foo"),
                    decl_interface_hash: hash,
                },
                target: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Mathlib.Dependency"),
                    name: npa_cert::Name::from_dotted("Math.foo"),
                    decl_interface_hash: hash,
                },
            }],
        };
        let extracted =
            extract_human_declaration_source(file_id, source, &imports, &selection, &mapping)
                .unwrap();
        assert_eq!(
            extracted.source,
            "import Mathlib.Dependency\n\ndef keep (Std_foo : Prop) : Prop := Math.foo\n"
        );
        assert_eq!(extracted.rewrites.len(), 1);
        assert_eq!(
            extracted.rewrites[0].resolution,
            HumanRewriteResolution::Qualified
        );
        assert!(!extracted.source.contains("drop"));
        assert!(!extracted.source.contains("comment"));
        assert_ne!(extracted.source_projection_hash, [0; 32]);

        let repeated =
            extract_human_declaration_source(file_id, source, &imports, &selection, &mapping)
                .unwrap();
        assert_eq!(extracted, repeated);
    }

    #[test]
    fn extraction_splits_one_source_import_across_mapped_target_modules() {
        let file_id = FileId(10);
        let source = "import Std.Source\n\ndef keep : Prop := Std.left -> Std.right\n";
        let mut source_interface =
            HumanSourceInterface::new(npa_cert::Name::from_dotted("Std.Source"));
        for (name, hash) in [("Std.left", [8; 32]), ("Std.right", [9; 32])] {
            source_interface
                .declarations
                .push(HumanSourceDeclarationMetadata {
                    kind: HumanSourceDeclarationKind::Def,
                    name: HumanName::new(npa_cert::Name::from_dotted(name).0, Span::empty(file_id)),
                    universe_params: Vec::new(),
                    binders: Vec::new(),
                    decl_interface_hash: Some(hash),
                    span: Span::empty(file_id),
                });
        }
        let imports = vec![HumanImportedSourceInterface {
            module: npa_cert::Name::from_dotted("Std.Source"),
            export_hash: [10; 32],
            certificate_hash: Some([11; 32]),
            source_interface,
        }];
        let families =
            collect_human_source_declaration_families(file_id, source, &imports).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "keep")
            .unwrap();
        let selection = HumanDeclarationSelection {
            source_module: npa_cert::Name::from_dotted("Fixture.Source"),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [12; 32],
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: [
                ("Std.left", [8; 32], "Mathlib.Left"),
                ("Std.right", [9; 32], "Mathlib.Right"),
            ]
            .into_iter()
            .map(|(name, hash, target_module)| HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Std.Source"),
                    name: npa_cert::Name::from_dotted(name),
                    decl_interface_hash: hash,
                },
                target: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted(target_module),
                    name: npa_cert::Name::from_dotted(name),
                    decl_interface_hash: hash,
                },
            })
            .collect(),
        };

        let extracted =
            extract_human_declaration_source(file_id, source, &imports, &selection, &mapping)
                .unwrap();

        assert_eq!(
            extracted.source,
            "import Mathlib.Left\nimport Mathlib.Right\n\ndef keep : Prop := Std.left -> Std.right\n"
        );
        assert_eq!(extracted.rewrites.len(), 2);
    }

    #[test]
    fn extraction_synthesizes_import_for_externalized_local_support() {
        let file_id = FileId(10);
        let source =
            "def support (P : Prop) : Prop := P\n\ndef keep (P : Prop) : Prop := support P\n";
        let families = collect_human_source_declaration_families(file_id, source, &[]).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "keep")
            .unwrap();
        let source_module = npa_cert::Name::from_dotted("Fixture.Source");
        let target_module = npa_cert::Name::from_dotted("Mathlib.Target");
        let hash = [11; 32];
        let selection = HumanDeclarationSelection {
            source_module: source_module.clone(),
            target_module: target_module.clone(),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: hash,
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: vec![
                HumanGlobalMappingRow {
                    source: HumanGlobalIdentity {
                        module: source_module.clone(),
                        name: npa_cert::Name::from_dotted("keep"),
                        decl_interface_hash: hash,
                    },
                    target: HumanGlobalIdentity {
                        module: target_module,
                        name: npa_cert::Name::from_dotted("keep"),
                        decl_interface_hash: hash,
                    },
                },
                HumanGlobalMappingRow {
                    source: HumanGlobalIdentity {
                        module: source_module,
                        name: npa_cert::Name::from_dotted("support"),
                        decl_interface_hash: [12; 32],
                    },
                    target: HumanGlobalIdentity {
                        module: npa_cert::Name::from_dotted("Mathlib.Support"),
                        name: npa_cert::Name::from_dotted("support"),
                        decl_interface_hash: [12; 32],
                    },
                },
            ],
        };
        let extracted =
            extract_human_declaration_source(file_id, source, &[], &selection, &mapping).unwrap();
        assert_eq!(
            extracted.source,
            "import Mathlib.Support\n\ndef keep (P : Prop) : Prop := support P\n"
        );
        assert!(!extracted.source.contains("def support"));
    }

    #[test]
    fn extraction_retains_exact_nested_namespace_frames() {
        let file_id = FileId(11);
        let source = "namespace Outer\nnamespace Inner\ndef keep (P : Prop) : Prop := P\nend Inner\nend Outer\n\nnamespace Later\ndef drop (P : Prop) : Prop := P\nend Later\n";
        let families = collect_human_source_declaration_families(file_id, source, &[]).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "Outer.Inner.keep")
            .unwrap();
        let selection = HumanDeclarationSelection {
            source_module: npa_cert::Name::from_dotted("Fixture.Source"),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [13; 32],
            }],
        };
        let extracted = extract_human_declaration_source(
            file_id,
            source,
            &[],
            &selection,
            &HumanGlobalMapping { rows: Vec::new() },
        )
        .unwrap();

        let extracted_families =
            collect_human_source_declaration_families(file_id, &extracted.source, &[]).unwrap();
        assert_eq!(extracted_families.families.len(), 1);
        assert_eq!(
            extracted_families.families[0].owner.as_dotted(),
            "Outer.Inner.keep"
        );
        assert!(!extracted.source.contains("Later"));
        assert!(!extracted.source.contains("drop"));
    }

    #[test]
    fn extraction_retains_relative_open_using_resolved_namespace() {
        let file_id = FileId(12);
        let source =
            "import Std.Source\nnamespace Outer\nopen Inner\ndef keep : Prop := value\nend Outer\n";
        let hash = [14; 32];
        let mut source_interface =
            HumanSourceInterface::new(npa_cert::Name::from_dotted("Std.Source"));
        for name in ["Outer.Inner.value", "Else.value"] {
            source_interface
                .declarations
                .push(HumanSourceDeclarationMetadata {
                    kind: HumanSourceDeclarationKind::Def,
                    name: HumanName::new(npa_cert::Name::from_dotted(name).0, Span::empty(file_id)),
                    universe_params: Vec::new(),
                    binders: Vec::new(),
                    decl_interface_hash: Some(hash),
                    span: Span::empty(file_id),
                });
        }
        let imports = vec![HumanImportedSourceInterface {
            module: npa_cert::Name::from_dotted("Std.Source"),
            export_hash: [15; 32],
            certificate_hash: Some([16; 32]),
            source_interface,
        }];
        let families =
            collect_human_source_declaration_families(file_id, source, &imports).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "Outer.keep")
            .unwrap();
        let selection = HumanDeclarationSelection {
            source_module: npa_cert::Name::from_dotted("Fixture.Source"),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [17; 32],
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: vec![HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Std.Source"),
                    name: npa_cert::Name::from_dotted("Outer.Inner.value"),
                    decl_interface_hash: hash,
                },
                target: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Std.Source"),
                    name: npa_cert::Name::from_dotted("Outer.Inner.value"),
                    decl_interface_hash: hash,
                },
            }],
        };

        let extracted =
            extract_human_declaration_source(file_id, source, &imports, &selection, &mapping)
                .unwrap();

        assert_eq!(
            extracted.source,
            "import Std.Source\n\nnamespace Outer\n\nopen Inner\n\ndef keep : Prop := value\n\nend Outer\n"
        );
    }

    #[test]
    fn extraction_rewrites_used_notation_target_and_drops_same_token_other_fixity() {
        let file_id = FileId(13);
        let source = "def add (n m : Type) : Type := n\ninfixl:65 \" + \" => add\ndef positive (n : Type) : Type := n\nprefix:70 \" + \" => positive\ndef keep (n : Type) : Type := n + Type\n";
        let families = collect_human_source_declaration_families(file_id, source, &[]).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "keep")
            .unwrap();
        let source_module = npa_cert::Name::from_dotted("Fixture.Source");
        let selection = HumanDeclarationSelection {
            source_module: source_module.clone(),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [18; 32],
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: vec![HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: source_module,
                    name: npa_cert::Name::from_dotted("add"),
                    decl_interface_hash: [19; 32],
                },
                target: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Mathlib.Support"),
                    name: npa_cert::Name::from_dotted("Public.add"),
                    decl_interface_hash: [19; 32],
                },
            }],
        };

        let extracted =
            extract_human_declaration_source(file_id, source, &[], &selection, &mapping).unwrap();

        assert_eq!(
            extracted.source,
            "import Mathlib.Support\n\ninfixl:65 \" + \" => Public.add\n\ndef keep (n : Type) : Type := n + Type\n"
        );
        assert!(!extracted.source.contains("prefix"));
        assert!(!extracted.source.contains("positive"));
    }

    #[test]
    fn extraction_retains_open_that_activates_used_namespaced_notation() {
        let file_id = FileId(14);
        let source = "namespace Nat\ndef add (n m : Type) : Type := n\ninfixl:65 \" + \" => add\nend Nat\nopen Nat\ndef keep (n : Type) : Type := n + Type\n";
        let families = collect_human_source_declaration_families(file_id, source, &[]).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "keep")
            .unwrap();
        let source_module = npa_cert::Name::from_dotted("Fixture.Source");
        let selection = HumanDeclarationSelection {
            source_module: source_module.clone(),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [20; 32],
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: vec![HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: source_module,
                    name: npa_cert::Name::from_dotted("Nat.add"),
                    decl_interface_hash: [21; 32],
                },
                target: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Mathlib.Support"),
                    name: npa_cert::Name::from_dotted("Public.add"),
                    decl_interface_hash: [21; 32],
                },
            }],
        };

        let extracted =
            extract_human_declaration_source(file_id, source, &[], &selection, &mapping).unwrap();

        assert_eq!(
            extracted.source,
            "import Mathlib.Support\n\nnamespace Nat\n\ninfixl:65 \" + \" => Public.add\n\nend Nat\n\nopen Nat\n\ndef keep (n : Type) : Type := n + Type\n"
        );
    }

    #[test]
    fn extraction_synthesizes_used_imported_notation_from_checked_interface() {
        let file_id = FileId(15);
        let source = "import Std.Notation\nopen Std\ndef keep (n : Type) : Type := n + Type\n";
        let hash = [22; 32];
        let imported_span = Span::empty(FileId(99));
        let mut source_interface =
            HumanSourceInterface::new(npa_cert::Name::from_dotted("Std.Notation"));
        source_interface
            .declarations
            .push(HumanSourceDeclarationMetadata {
                kind: HumanSourceDeclarationKind::Def,
                name: HumanName::new(npa_cert::Name::from_dotted("Std.add").0, imported_span),
                universe_params: Vec::new(),
                binders: Vec::new(),
                decl_interface_hash: Some(hash),
                span: imported_span,
            });
        source_interface
            .notations
            .push(HumanSourceNotationMetadata {
                kind: HumanNotationKind::Infixl,
                associativity: HumanNotationAssociativity::Left,
                precedence: 65,
                token: "+".to_owned(),
                target: HumanName::new(npa_cert::Name::from_dotted("Std.add").0, imported_span),
                namespace: vec!["Std".to_owned()],
                span: imported_span,
            });
        let imports = vec![HumanImportedSourceInterface {
            module: npa_cert::Name::from_dotted("Std.Notation"),
            export_hash: [23; 32],
            certificate_hash: Some([24; 32]),
            source_interface,
        }];
        let families =
            collect_human_source_declaration_families(file_id, source, &imports).unwrap();
        let keep = families
            .families
            .iter()
            .find(|family| family.owner.as_dotted() == "keep")
            .unwrap();
        let selection = HumanDeclarationSelection {
            source_module: npa_cert::Name::from_dotted("Fixture.Source"),
            target_module: npa_cert::Name::from_dotted("Mathlib.Target"),
            declarations: vec![HumanSelectedDeclaration {
                name: keep.owner.clone(),
                kind: HumanDeclarationFamilyMemberKind::Definition,
                item_span: keep.item_span,
                decl_interface_hash: [25; 32],
            }],
        };
        let mapping = HumanGlobalMapping {
            rows: vec![HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Std.Notation"),
                    name: npa_cert::Name::from_dotted("Std.add"),
                    decl_interface_hash: hash,
                },
                target: HumanGlobalIdentity {
                    module: npa_cert::Name::from_dotted("Mathlib.Support"),
                    name: npa_cert::Name::from_dotted("Public.add"),
                    decl_interface_hash: hash,
                },
            }],
        };

        let extracted =
            extract_human_declaration_source(file_id, source, &imports, &selection, &mapping)
                .unwrap();

        assert_eq!(
            extracted.source,
            "import Mathlib.Support\n\nnamespace Std\ninfixl:65 \" + \" => Public.add\nend Std\n\nopen Std\n\ndef keep (n : Type) : Type := n + Type\n"
        );
    }
}
