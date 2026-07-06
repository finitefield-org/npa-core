use std::collections::{BTreeMap, BTreeSet};

use crate::{
    MachineBinder, MachineCompileOptions, MachineDecl, MachineDiagnostic, MachineDiagnosticKind,
    MachineDiagnosticPayload, MachineItem, MachineLevel, MachineModule, MachineName,
    MachineRepairCandidate, MachineRepairSuggestion, MachineRepairSuggestionKind,
    MachineSurfaceMode, MachineTerm, Result, Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedExport {
    pub name: npa_cert::Name,
    pub universe_params: Vec<String>,
    pub ty: npa_kernel::Expr,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VerifiedDependency {
    pub module: Option<npa_cert::ModuleName>,
    pub export_hash: Option<npa_cert::Hash>,
    pub name: npa_cert::Name,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedImport {
    pub module: npa_cert::ModuleName,
    pub export_hash: npa_cert::Hash,
    pub certificate_hash: Option<npa_cert::Hash>,
    pub exports: Vec<VerifiedExport>,
    pub decl_interface_hashes: BTreeMap<npa_cert::Name, npa_cert::Hash>,
    pub kernel_decls: Vec<npa_kernel::Decl>,
    pub kernel_decl_dependencies: BTreeMap<String, BTreeSet<VerifiedDependency>>,
}

impl From<&npa_cert::VerifiedModule> for VerifiedImport {
    fn from(module: &npa_cert::VerifiedModule) -> Self {
        let exports = module
            .export_block()
            .iter()
            .map(|entry| VerifiedExport {
                name: module.name_table()[entry.name].clone(),
                universe_params: entry
                    .universe_params
                    .iter()
                    .map(|name| module.name_table()[*name].as_dotted())
                    .collect(),
                ty: expr_from_verified_term(module, entry.ty),
                decl_interface_hash: entry.decl_interface_hash,
            })
            .collect();

        let kernel_decls = npa_cert::verified_module_to_kernel_decls(module)
            .expect("verified module must reconstruct kernel declarations");
        let kernel_decl_dependencies =
            kernel_decl_dependencies_from_verified_module(module, &kernel_decls)
                .expect("verified module dependencies must be readable");
        let decl_interface_hashes = module
            .declarations()
            .iter()
            .map(|decl| {
                (
                    module.name_table()[decl_payload_name(&decl.decl)].clone(),
                    decl.hashes.decl_interface_hash,
                )
            })
            .collect();

        Self {
            module: module.module().clone(),
            export_hash: module.export_hash(),
            certificate_hash: Some(module.certificate_hash()),
            exports,
            decl_interface_hashes,
            kernel_decls,
            kernel_decl_dependencies,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct VerifiedImportIdentity {
    pub module: npa_cert::ModuleName,
    pub export_hash: npa_cert::Hash,
    pub certificate_hash: Option<npa_cert::Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum VerifiedImportLookupError {
    Missing,
    Ambiguous,
}

pub(crate) fn verified_import_identity(import: &VerifiedImport) -> VerifiedImportIdentity {
    VerifiedImportIdentity {
        module: import.module.clone(),
        export_hash: import.export_hash,
        certificate_hash: import.certificate_hash,
    }
}

pub(crate) fn find_unique_verified_import_by_module<'a>(
    verified_imports: &'a [VerifiedImport],
    import_module: &npa_cert::ModuleName,
) -> std::result::Result<&'a VerifiedImport, VerifiedImportLookupError> {
    let mut matches = verified_imports
        .iter()
        .filter(|import| &import.module == import_module);
    let Some(first) = matches.next() else {
        return Err(VerifiedImportLookupError::Missing);
    };

    if matches.any(|import| import != first) {
        return Err(VerifiedImportLookupError::Ambiguous);
    }

    Ok(first)
}

fn decl_payload_name(decl: &npa_cert::DeclPayload) -> npa_cert::NameId {
    match decl {
        npa_cert::DeclPayload::Axiom { name, .. }
        | npa_cert::DeclPayload::AxiomConstrained { name, .. }
        | npa_cert::DeclPayload::Def { name, .. }
        | npa_cert::DeclPayload::DefConstrained { name, .. }
        | npa_cert::DeclPayload::Theorem { name, .. }
        | npa_cert::DeclPayload::TheoremConstrained { name, .. }
        | npa_cert::DeclPayload::Inductive { name, .. }
        | npa_cert::DeclPayload::InductiveConstrained { name, .. }
        | npa_cert::DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedMachineModule {
    pub module: MachineModule,
}

pub fn resolve_machine_module(
    module: MachineModule,
    verified_imports: &[VerifiedImport],
) -> Result<ResolvedMachineModule> {
    resolve_machine_module_with_repair(module, verified_imports, false)
}

pub fn resolve_machine_module_with_options(
    module: MachineModule,
    verified_imports: &[VerifiedImport],
    options: &MachineCompileOptions,
) -> Result<ResolvedMachineModule> {
    resolve_machine_module_with_repair(
        module,
        verified_imports,
        options.mode == MachineSurfaceMode::Repair,
    )
}

pub(crate) fn resolve_machine_module_with_repair(
    module: MachineModule,
    verified_imports: &[VerifiedImport],
    repair_mode: bool,
) -> Result<ResolvedMachineModule> {
    Resolver::new(verified_imports, repair_mode).resolve_module(module)
}

struct Resolver<'a> {
    verified_imports: &'a [VerifiedImport],
    globals: GlobalTable,
    repair_mode: bool,
}

impl<'a> Resolver<'a> {
    fn new(verified_imports: &'a [VerifiedImport], repair_mode: bool) -> Self {
        Self {
            verified_imports,
            globals: GlobalTable::default(),
            repair_mode,
        }
    }

    fn resolve_module(mut self, module: MachineModule) -> Result<ResolvedMachineModule> {
        let mut seen_imports = BTreeSet::new();
        for item in &module.items {
            if let MachineItem::Import {
                module: import_name,
                span,
            } = item
            {
                let import = self.find_verified_import(import_name, *span)?;
                let import_key = (
                    import.module.clone(),
                    import.export_hash,
                    import.certificate_hash,
                );
                if seen_imports.insert(import_key) {
                    self.globals.add_import(import)?;
                }
            }
        }
        for item in &module.items {
            match item {
                MachineItem::Def(decl) | MachineItem::Theorem(decl) => {
                    self.globals.add_decl_root(&decl.name);
                }
                MachineItem::Import { .. } => {}
            }
        }

        let mut resolved_items = Vec::with_capacity(module.items.len());
        for item in module.items {
            let resolved_item = match item {
                MachineItem::Import { .. } => item,
                MachineItem::Def(decl) => {
                    let resolved = self.resolve_decl(decl)?;
                    self.globals.add_local_decl(&resolved.name)?;
                    MachineItem::Def(resolved)
                }
                MachineItem::Theorem(decl) => {
                    let resolved = self.resolve_decl(decl)?;
                    self.globals.add_local_decl(&resolved.name)?;
                    MachineItem::Theorem(resolved)
                }
            };
            resolved_items.push(resolved_item);
        }

        Ok(ResolvedMachineModule {
            module: MachineModule {
                file_id: module.file_id,
                items: resolved_items,
                span: module.span,
            },
        })
    }

    fn find_verified_import(
        &self,
        import_name: &MachineName,
        span: Span,
    ) -> Result<&'a VerifiedImport> {
        let import_module = name_from_machine(import_name);
        match find_unique_verified_import_by_module(self.verified_imports, &import_module) {
            Ok(import) => Ok(import),
            Err(VerifiedImportLookupError::Missing) => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::MissingVerifiedImport,
                span,
                format!(
                    "import {} is not present in the verified import set",
                    import_name.as_dotted()
                ),
            )),
            Err(VerifiedImportLookupError::Ambiguous) => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::ImportResolutionError,
                span,
                format!(
                    "import {} has multiple verified interfaces",
                    import_name.as_dotted()
                ),
            )),
        }
    }

    fn resolve_decl(&self, decl: MachineDecl) -> Result<MachineDecl> {
        let universe_params = self.resolve_universe_params(decl.universe_params)?;
        let universe_param_names: BTreeSet<_> = universe_params
            .iter()
            .map(|param| param.name.clone())
            .collect();
        let mut locals = LocalScope::default();
        let mut binders = Vec::with_capacity(decl.binders.len());

        for binder in decl.binders {
            let binder = self.resolve_binder(binder, &mut locals, &universe_param_names)?;
            binders.push(binder);
        }

        let ty = self.resolve_term(decl.ty, &locals, &universe_param_names)?;
        let value = self.resolve_term(decl.value, &locals, &universe_param_names)?;

        Ok(MachineDecl {
            name: decl.name,
            universe_params,
            binders,
            ty,
            value,
            span: decl.span,
        })
    }

    fn resolve_universe_params(
        &self,
        params: Vec<crate::MachineUniverseParam>,
    ) -> Result<Vec<crate::MachineUniverseParam>> {
        let mut seen = BTreeSet::new();

        for param in &params {
            if !seen.insert(param.name.clone()) {
                return Err(MachineDiagnostic::error(
                    MachineDiagnosticKind::DuplicateUniverseParam,
                    param.span,
                    format!("duplicate universe parameter {}", param.name),
                ));
            }
        }

        Ok(params)
    }

    fn resolve_binder(
        &self,
        binder: MachineBinder,
        locals: &mut LocalScope,
        universe_params: &BTreeSet<String>,
    ) -> Result<MachineBinder> {
        self.ensure_local_does_not_shadow_global(&binder.name, binder.span)?;
        let ty = self.resolve_term(binder.ty, locals, universe_params)?;
        locals.push(binder.name.clone());

        Ok(MachineBinder {
            name: binder.name,
            ty,
            span: binder.span,
        })
    }

    fn resolve_term(
        &self,
        term: MachineTerm,
        locals: &LocalScope,
        universe_params: &BTreeSet<String>,
    ) -> Result<MachineTerm> {
        match term {
            MachineTerm::Ident {
                name,
                universe_args,
                explicit_mode,
                span,
            } => self.resolve_ident(
                name,
                universe_args,
                explicit_mode,
                span,
                locals,
                universe_params,
            ),
            MachineTerm::Local { .. } => Ok(term),
            MachineTerm::Prop { span } => Ok(MachineTerm::Prop { span }),
            MachineTerm::Type { level, span } => Ok(MachineTerm::Type {
                level: self.resolve_level(level, universe_params)?,
                span,
            }),
            MachineTerm::Sort { level, span } => Ok(MachineTerm::Sort {
                level: self.resolve_level(level, universe_params)?,
                span,
            }),
            MachineTerm::App { func, arg, span } => Ok(MachineTerm::App {
                func: Box::new(self.resolve_term(*func, locals, universe_params)?),
                arg: Box::new(self.resolve_term(*arg, locals, universe_params)?),
                span,
            }),
            MachineTerm::Lam {
                binders,
                body,
                span,
            } => {
                let mut nested_locals = locals.clone();
                let mut resolved_binders = Vec::with_capacity(binders.len());
                for binder in binders {
                    let binder =
                        self.resolve_binder(binder, &mut nested_locals, universe_params)?;
                    resolved_binders.push(binder);
                }
                Ok(MachineTerm::Lam {
                    binders: resolved_binders,
                    body: Box::new(self.resolve_term(*body, &nested_locals, universe_params)?),
                    span,
                })
            }
            MachineTerm::Pi {
                binders,
                body,
                span,
            } => {
                let mut nested_locals = locals.clone();
                let mut resolved_binders = Vec::with_capacity(binders.len());
                for binder in binders {
                    let binder =
                        self.resolve_binder(binder, &mut nested_locals, universe_params)?;
                    resolved_binders.push(binder);
                }
                Ok(MachineTerm::Pi {
                    binders: resolved_binders,
                    body: Box::new(self.resolve_term(*body, &nested_locals, universe_params)?),
                    span,
                })
            }
            MachineTerm::Let {
                name,
                ty,
                value,
                body,
                span,
            } => {
                self.ensure_local_does_not_shadow_global(&name, span)?;
                let ty = self.resolve_term(*ty, locals, universe_params)?;
                let value = self.resolve_term(*value, locals, universe_params)?;
                let mut nested_locals = locals.clone();
                nested_locals.push(name.clone());
                Ok(MachineTerm::Let {
                    name,
                    ty: Box::new(ty),
                    value: Box::new(value),
                    body: Box::new(self.resolve_term(*body, &nested_locals, universe_params)?),
                    span,
                })
            }
            MachineTerm::Annot { expr, ty, span } => Ok(MachineTerm::Annot {
                expr: Box::new(self.resolve_term(*expr, locals, universe_params)?),
                ty: Box::new(self.resolve_term(*ty, locals, universe_params)?),
                span,
            }),
        }
    }

    fn resolve_ident(
        &self,
        name: MachineName,
        universe_args: Option<Vec<MachineLevel>>,
        explicit_mode: bool,
        span: Span,
        locals: &LocalScope,
        universe_params: &BTreeSet<String>,
    ) -> Result<MachineTerm> {
        let force_global = explicit_mode || universe_args.is_some() || name.parts.len() > 1;
        if !force_global && name.parts.len() == 1 && locals.contains(&name.parts[0]) {
            return Ok(MachineTerm::Local {
                name: name.parts[0].clone(),
                span,
            });
        }

        let universe_args = universe_args
            .map(|args| {
                args.into_iter()
                    .map(|arg| self.resolve_level(arg, universe_params))
                    .collect::<Result<Vec<_>>>()
            })
            .transpose()?;

        match self.globals.lookup(&name, force_global) {
            GlobalLookup::Resolved => Ok(MachineTerm::Ident {
                name,
                universe_args,
                explicit_mode,
                span,
            }),
            GlobalLookup::Ambiguous => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::AmbiguousGlobalName,
                name.span,
                format!(
                    "global name {} is exported more than once",
                    name.as_dotted()
                ),
            )),
            GlobalLookup::ShortGlobal => Err(self.short_global_diagnostic(&name)),
            GlobalLookup::UnknownLocal => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnknownLocalName,
                name.span,
                format!("unknown local name {}", name.as_dotted()),
            )),
            GlobalLookup::UnknownGlobal => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnknownGlobalName,
                name.span,
                format!("unknown global name {}", name.as_dotted()),
            )),
        }
    }

    fn short_global_diagnostic(&self, name: &MachineName) -> MachineDiagnostic {
        let diagnostic = MachineDiagnostic::error(
            MachineDiagnosticKind::ShortGlobalName,
            name.span,
            format!(
                "global name {} must be written as a fully qualified exact name",
                name.as_dotted()
            ),
        );
        if !self.repair_mode {
            return diagnostic;
        }

        let suffix = name.parts.first().map(String::as_str).unwrap_or_default();
        let candidates = self.globals.repair_candidates_for_suffix(suffix);
        let replacement = match candidates.as_slice() {
            [candidate] if self.globals.has_resolved_name(&candidate.name) => {
                Some(candidate.name.as_dotted())
            }
            _ => None,
        };
        let payload = MachineDiagnosticPayload {
            candidates: candidates.clone(),
            ..MachineDiagnosticPayload::default()
        };
        let suggestion = MachineRepairSuggestion {
            kind: MachineRepairSuggestionKind::UseFullyQualifiedName,
            replacement,
            candidates,
        };

        diagnostic.with_payload(payload).with_suggestion(suggestion)
    }

    fn resolve_level(
        &self,
        level: MachineLevel,
        universe_params: &BTreeSet<String>,
    ) -> Result<MachineLevel> {
        match level {
            MachineLevel::Nat { .. } => Ok(level),
            MachineLevel::Param { name, span } => {
                if universe_params.contains(&name) {
                    Ok(MachineLevel::Param { name, span })
                } else {
                    Err(MachineDiagnostic::error(
                        MachineDiagnosticKind::UnknownUniverseParam,
                        span,
                        format!("unknown universe parameter {name}"),
                    ))
                }
            }
            MachineLevel::Succ { level, span } => Ok(MachineLevel::Succ {
                level: Box::new(self.resolve_level(*level, universe_params)?),
                span,
            }),
            MachineLevel::Max { lhs, rhs, span } => Ok(MachineLevel::Max {
                lhs: Box::new(self.resolve_level(*lhs, universe_params)?),
                rhs: Box::new(self.resolve_level(*rhs, universe_params)?),
                span,
            }),
            MachineLevel::IMax { lhs, rhs, span } => Ok(MachineLevel::IMax {
                lhs: Box::new(self.resolve_level(*lhs, universe_params)?),
                rhs: Box::new(self.resolve_level(*rhs, universe_params)?),
                span,
            }),
        }
    }

    fn ensure_local_does_not_shadow_global(&self, name: &str, span: Span) -> Result<()> {
        if self.globals.has_root(name) {
            return Err(MachineDiagnostic::error(
                MachineDiagnosticKind::GlobalShadowedByLocal,
                span,
                format!("local name {name} shadows a global namespace root"),
            ));
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
struct LocalScope {
    names: Vec<String>,
}

impl LocalScope {
    fn push(&mut self, name: String) {
        self.names.push(name);
    }

    fn contains(&self, name: &str) -> bool {
        self.names.iter().rev().any(|local| local == name)
    }
}

#[derive(Clone, Debug, Default)]
struct GlobalTable {
    names: BTreeMap<String, GlobalEntry>,
    roots: BTreeSet<String>,
    suffixes: BTreeSet<String>,
    suffix_candidates: BTreeMap<String, BTreeSet<MachineRepairCandidate>>,
}

impl GlobalTable {
    fn add_import(&mut self, import: &VerifiedImport) -> Result<()> {
        for export in &import.exports {
            self.add_global_name(&export.name, Some(export.decl_interface_hash), None)?;
        }

        Ok(())
    }

    fn add_local_decl(&mut self, name: &MachineName) -> Result<()> {
        self.add_global_name(&name_from_machine(name), None, Some(name.span))
    }

    fn add_decl_root(&mut self, name: &MachineName) {
        if let Some(root) = name.parts.first() {
            self.roots.insert(root.clone());
        }
    }

    fn add_global_name(
        &mut self,
        name: &npa_cert::Name,
        interface_hash: Option<npa_cert::Hash>,
        duplicate_span: Option<Span>,
    ) -> Result<()> {
        let dotted = name.as_dotted();
        let first = name.0.first().cloned();
        let last = name.0.last().cloned();

        match self.names.get_mut(&dotted) {
            Some(_) if duplicate_span.is_some() => {
                let span = duplicate_span.expect("local duplicate has a source span");
                return Err(MachineDiagnostic::error(
                    MachineDiagnosticKind::DuplicateDeclaration,
                    span,
                    format!("duplicate declaration {}", name.as_dotted()),
                ));
            }
            Some(GlobalEntry::Resolved { .. }) if duplicate_span.is_none() => {
                self.names.insert(dotted.clone(), GlobalEntry::Ambiguous);
            }
            Some(GlobalEntry::Resolved { .. } | GlobalEntry::Ambiguous) => {}
            None => {
                self.names
                    .insert(dotted, GlobalEntry::Resolved { interface_hash });
            }
        }

        if let Some(first) = first {
            self.roots.insert(first);
        }
        if let Some(last) = last {
            self.suffixes.insert(last.clone());
            self.suffix_candidates
                .entry(last)
                .or_default()
                .insert(MachineRepairCandidate {
                    name: name.clone(),
                    decl_interface_hash: interface_hash,
                });
        }

        Ok(())
    }

    fn lookup(&self, name: &MachineName, force_global: bool) -> GlobalLookup {
        let dotted = name.as_dotted();
        match self.names.get(&dotted) {
            Some(GlobalEntry::Resolved { .. }) => GlobalLookup::Resolved,
            Some(GlobalEntry::Ambiguous) => GlobalLookup::Ambiguous,
            None if name.parts.len() == 1 && self.suffixes.contains(&name.parts[0]) => {
                GlobalLookup::ShortGlobal
            }
            None if name.parts.len() == 1 && !force_global => GlobalLookup::UnknownLocal,
            None => GlobalLookup::UnknownGlobal,
        }
    }

    fn has_root(&self, name: &str) -> bool {
        self.roots.contains(name)
    }

    fn repair_candidates_for_suffix(&self, suffix: &str) -> Vec<MachineRepairCandidate> {
        self.suffix_candidates
            .get(suffix)
            .map(|candidates| candidates.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn has_resolved_name(&self, name: &npa_cert::Name) -> bool {
        matches!(
            self.names.get(&name.as_dotted()),
            Some(GlobalEntry::Resolved { .. })
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GlobalEntry {
    Resolved {
        interface_hash: Option<npa_cert::Hash>,
    },
    Ambiguous,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GlobalLookup {
    Resolved,
    Ambiguous,
    ShortGlobal,
    UnknownLocal,
    UnknownGlobal,
}

fn name_from_machine(name: &MachineName) -> npa_cert::Name {
    npa_cert::Name(name.parts.clone())
}

fn expr_from_verified_term(
    module: &npa_cert::VerifiedModule,
    term: npa_cert::TermId,
) -> npa_kernel::Expr {
    match &module.term_table()[term] {
        npa_cert::TermNode::Sort(level) => {
            npa_kernel::Expr::sort(level_from_verified_node(module, *level))
        }
        npa_cert::TermNode::BVar(index) => npa_kernel::Expr::bvar(*index),
        npa_cert::TermNode::Const { global_ref, levels } => npa_kernel::Expr::konst(
            global_ref_name(module, global_ref),
            levels
                .iter()
                .map(|level| level_from_verified_node(module, *level))
                .collect(),
        ),
        npa_cert::TermNode::App(func, arg) => npa_kernel::Expr::app(
            expr_from_verified_term(module, *func),
            expr_from_verified_term(module, *arg),
        ),
        npa_cert::TermNode::Lam { ty, body } => npa_kernel::Expr::lam(
            "_",
            expr_from_verified_term(module, *ty),
            expr_from_verified_term(module, *body),
        ),
        npa_cert::TermNode::Pi { ty, body } => npa_kernel::Expr::pi(
            "_",
            expr_from_verified_term(module, *ty),
            expr_from_verified_term(module, *body),
        ),
        npa_cert::TermNode::Let { ty, value, body } => npa_kernel::Expr::let_in(
            "_",
            expr_from_verified_term(module, *ty),
            expr_from_verified_term(module, *value),
            expr_from_verified_term(module, *body),
        ),
    }
}

fn level_from_verified_node(
    module: &npa_cert::VerifiedModule,
    level: npa_cert::LevelId,
) -> npa_kernel::Level {
    match &module.level_table()[level] {
        npa_cert::LevelNode::Zero => npa_kernel::Level::zero(),
        npa_cert::LevelNode::Succ(inner) => {
            npa_kernel::Level::succ(level_from_verified_node(module, *inner))
        }
        npa_cert::LevelNode::Max(lhs, rhs) => npa_kernel::Level::max(
            level_from_verified_node(module, *lhs),
            level_from_verified_node(module, *rhs),
        ),
        npa_cert::LevelNode::IMax(lhs, rhs) => npa_kernel::Level::imax(
            level_from_verified_node(module, *lhs),
            level_from_verified_node(module, *rhs),
        ),
        npa_cert::LevelNode::Param(name) => {
            npa_kernel::Level::param(module.name_table()[*name].as_dotted())
        }
    }
}

fn global_ref_name(module: &npa_cert::VerifiedModule, global_ref: &npa_cert::GlobalRef) -> String {
    match global_ref {
        npa_cert::GlobalRef::Builtin { name, .. }
        | npa_cert::GlobalRef::Imported { name, .. }
        | npa_cert::GlobalRef::LocalGenerated { name, .. } => {
            module.name_table()[*name].as_dotted()
        }
        npa_cert::GlobalRef::Local { decl_index } => decl_name(module, *decl_index),
    }
}

fn decl_name(module: &npa_cert::VerifiedModule, decl_index: usize) -> String {
    let decl = &module.declarations()[decl_index];
    let name = match &decl.decl {
        npa_cert::DeclPayload::Axiom { name, .. }
        | npa_cert::DeclPayload::AxiomConstrained { name, .. }
        | npa_cert::DeclPayload::Def { name, .. }
        | npa_cert::DeclPayload::DefConstrained { name, .. }
        | npa_cert::DeclPayload::Theorem { name, .. }
        | npa_cert::DeclPayload::TheoremConstrained { name, .. }
        | npa_cert::DeclPayload::Inductive { name, .. }
        | npa_cert::DeclPayload::InductiveConstrained { name, .. }
        | npa_cert::DeclPayload::MutualInductiveBlock { name, .. } => *name,
    };
    module.name_table()[name].as_dotted()
}

fn kernel_decl_dependencies_from_verified_module(
    module: &npa_cert::VerifiedModule,
    kernel_decls: &[npa_kernel::Decl],
) -> npa_cert::Result<BTreeMap<String, BTreeSet<VerifiedDependency>>> {
    if module.declarations().len() != kernel_decls.len() {
        return Err(npa_cert::CertError::DecodeError);
    }

    let mut dependencies = BTreeMap::new();
    for (decl_cert, decl) in module.declarations().iter().zip(kernel_decls) {
        let mut names = BTreeSet::new();
        collect_const_names_from_decl(&mut names, decl);
        let decl_dependencies = verified_dependencies_from_entries(
            module.imports(),
            module.name_table(),
            &names,
            &decl_cert.dependencies,
        )?;
        if !decl_dependencies.is_empty() {
            dependencies.insert(decl.name().to_owned(), decl_dependencies);
        }
    }
    Ok(dependencies)
}

fn verified_dependencies_from_entries(
    imports: &[npa_cert::ImportEntry],
    name_table: &[npa_cert::Name],
    referenced_names: &BTreeSet<String>,
    dependencies: &[npa_cert::DependencyEntry],
) -> npa_cert::Result<BTreeSet<VerifiedDependency>> {
    let mut verified_dependencies = BTreeSet::new();
    for dependency in dependencies {
        let Some(verified_dependency) =
            verified_dependency_from_entry(imports, name_table, dependency)?
        else {
            continue;
        };
        if referenced_names.contains(&verified_dependency.name.as_dotted()) {
            verified_dependencies.insert(verified_dependency);
        }
    }
    Ok(verified_dependencies)
}

fn verified_dependency_from_entry(
    imports: &[npa_cert::ImportEntry],
    name_table: &[npa_cert::Name],
    dependency: &npa_cert::DependencyEntry,
) -> npa_cert::Result<Option<VerifiedDependency>> {
    match &dependency.global_ref {
        npa_cert::GlobalRef::Builtin { name, .. } => {
            let name = name_table
                .get(*name)
                .ok_or(npa_cert::CertError::DecodeError)?
                .clone();
            Ok(Some(VerifiedDependency {
                module: None,
                export_hash: None,
                name,
                decl_interface_hash: dependency.decl_interface_hash,
            }))
        }
        npa_cert::GlobalRef::Imported {
            import_index, name, ..
        } => {
            let import = imports
                .get(*import_index)
                .ok_or(npa_cert::CertError::DecodeError)?;
            let name = name_table
                .get(*name)
                .ok_or(npa_cert::CertError::DecodeError)?
                .clone();
            Ok(Some(VerifiedDependency {
                module: Some(import.module.clone()),
                export_hash: Some(import.export_hash),
                name,
                decl_interface_hash: dependency.decl_interface_hash,
            }))
        }
        npa_cert::GlobalRef::Local { .. } | npa_cert::GlobalRef::LocalGenerated { .. } => Ok(None),
    }
}

fn collect_const_names_from_decl(names: &mut BTreeSet<String>, decl: &npa_kernel::Decl) {
    match decl {
        npa_kernel::Decl::Axiom { ty, .. } | npa_kernel::Decl::AxiomConstrained { ty, .. } => {
            collect_const_names_from_expr(names, ty)
        }
        npa_kernel::Decl::Def { ty, value, .. }
        | npa_kernel::Decl::DefConstrained { ty, value, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, value);
        }
        npa_kernel::Decl::Theorem { ty, proof, .. }
        | npa_kernel::Decl::TheoremConstrained { ty, proof, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, proof);
        }
        npa_kernel::Decl::Inductive { data, .. } => {
            for param in &data.params {
                collect_const_names_from_expr(names, &param.ty);
            }
            for index in &data.indices {
                collect_const_names_from_expr(names, &index.ty);
            }
            for constructor in &data.constructors {
                collect_const_names_from_expr(names, &constructor.ty);
            }
            if let Some(recursor) = &data.recursor {
                collect_const_names_from_expr(names, &recursor.ty);
            }
        }
        npa_kernel::Decl::MutualInductiveBlock { data, .. } => {
            for inductive in &data.inductives {
                for param in &inductive.params {
                    collect_const_names_from_expr(names, &param.ty);
                }
                for index in &inductive.indices {
                    collect_const_names_from_expr(names, &index.ty);
                }
                for constructor in &inductive.constructors {
                    collect_const_names_from_expr(names, &constructor.ty);
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_const_names_from_expr(names, &recursor.ty);
                }
            }
        }
        npa_kernel::Decl::Constructor { ty, .. } | npa_kernel::Decl::Recursor { ty, .. } => {
            collect_const_names_from_expr(names, ty);
        }
    }
}

fn collect_const_names_from_expr(names: &mut BTreeSet<String>, expr: &npa_kernel::Expr) {
    match expr {
        npa_kernel::Expr::Sort(_) | npa_kernel::Expr::BVar(_) => {}
        npa_kernel::Expr::Const { name, .. } => {
            names.insert(name.clone());
        }
        npa_kernel::Expr::App(func, arg) => {
            collect_const_names_from_expr(names, func);
            collect_const_names_from_expr(names, arg);
        }
        npa_kernel::Expr::Lam { ty, body, .. } | npa_kernel::Expr::Pi { ty, body, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, body);
        }
        npa_kernel::Expr::Let {
            ty, value, body, ..
        } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, value);
            collect_const_names_from_expr(names, body);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_machine_module, FileId, MachineCompileOptions, MachineSurfaceMode};

    fn hash(seed: u8) -> npa_cert::Hash {
        [seed; 32]
    }

    fn verified_import(module: &str, exports: &[&str]) -> VerifiedImport {
        let exports: Vec<_> = exports
            .iter()
            .enumerate()
            .map(|(index, name)| VerifiedExport {
                name: npa_cert::Name::from_dotted(name),
                universe_params: Vec::new(),
                ty: npa_kernel::Expr::sort(npa_kernel::Level::zero()),
                decl_interface_hash: hash(index as u8 + 2),
            })
            .collect();
        let kernel_decls = exports
            .iter()
            .map(|export| npa_kernel::Decl::Axiom {
                name: export.name.as_dotted(),
                universe_params: export.universe_params.clone(),
                ty: export.ty.clone(),
            })
            .collect();

        VerifiedImport {
            module: npa_cert::Name::from_dotted(module),
            export_hash: hash(1),
            certificate_hash: None,
            decl_interface_hashes: exports
                .iter()
                .map(|export| (export.name.clone(), export.decl_interface_hash))
                .collect(),
            exports,
            kernel_decls,
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    fn resolve_source(source: &str, imports: &[VerifiedImport]) -> Result<ResolvedMachineModule> {
        let module = parse_machine_module(FileId(0), source).expect("source should parse");
        resolve_machine_module(module, imports)
    }

    fn resolve_source_with_options(
        source: &str,
        imports: &[VerifiedImport],
        options: &MachineCompileOptions,
    ) -> Result<ResolvedMachineModule> {
        let module = parse_machine_module(FileId(0), source).expect("source should parse");
        resolve_machine_module_with_options(module, imports, options)
    }

    fn resolve_err(source: &str, imports: &[VerifiedImport]) -> MachineDiagnosticKind {
        resolve_source(source, imports)
            .expect_err("source should fail resolution")
            .kind
    }

    fn nat_import() -> VerifiedImport {
        verified_import("Std.Nat.Basic", &["Nat", "Nat.zero", "Nat.add"])
    }

    #[test]
    fn dependency_entries_keep_same_name_import_identities_per_decl() {
        let imports = vec![
            npa_cert::ImportEntry {
                module: npa_cert::Name::from_dotted("Left.Module"),
                export_hash: hash(11),
                certificate_hash: None,
            },
            npa_cert::ImportEntry {
                module: npa_cert::Name::from_dotted("Right.Module"),
                export_hash: hash(12),
                certificate_hash: None,
            },
        ];
        let shared_name = npa_cert::Name::from_dotted("Shared.Foo");
        let name_table = vec![shared_name.clone()];
        let referenced_names = BTreeSet::from([shared_name.as_dotted()]);
        let decl_interface_hash = hash(21);
        let left_dependency = npa_cert::DependencyEntry {
            global_ref: npa_cert::GlobalRef::Imported {
                import_index: 0,
                name: 0,
                decl_interface_hash,
            },
            decl_interface_hash,
        };
        let right_dependency = npa_cert::DependencyEntry {
            global_ref: npa_cert::GlobalRef::Imported {
                import_index: 1,
                name: 0,
                decl_interface_hash,
            },
            decl_interface_hash,
        };

        let left_dependencies = verified_dependencies_from_entries(
            &imports,
            &name_table,
            &referenced_names,
            std::slice::from_ref(&left_dependency),
        )
        .expect("left dependency should decode");
        assert_eq!(
            left_dependencies,
            BTreeSet::from([VerifiedDependency {
                module: Some(imports[0].module.clone()),
                export_hash: Some(imports[0].export_hash),
                name: shared_name.clone(),
                decl_interface_hash,
            }])
        );

        let right_dependencies = verified_dependencies_from_entries(
            &imports,
            &name_table,
            &referenced_names,
            std::slice::from_ref(&right_dependency),
        )
        .expect("right dependency should decode");
        assert_eq!(
            right_dependencies,
            BTreeSet::from([VerifiedDependency {
                module: Some(imports[1].module.clone()),
                export_hash: Some(imports[1].export_hash),
                name: shared_name,
                decl_interface_hash,
            }])
        );
    }

    #[test]
    fn resolves_imported_globals_and_locals() {
        let imports = [nat_import()];
        let resolved = resolve_source(
            "import Std.Nat.Basic\ndef Test.use (n : Nat) : Nat := Nat.add n Nat.zero",
            &imports,
        )
        .expect("source should resolve");

        let MachineItem::Def(decl) = &resolved.module.items[1] else {
            panic!("expected resolved def");
        };
        let MachineTerm::App { func, arg, .. } = &decl.value else {
            panic!("expected outer application");
        };
        let MachineTerm::Ident { name, .. } = arg.as_ref() else {
            panic!("expected Nat.zero global");
        };
        assert_eq!(name.as_dotted(), "Nat.zero");

        let MachineTerm::App { func, arg, .. } = func.as_ref() else {
            panic!("expected inner application");
        };
        let MachineTerm::Local { name, .. } = arg.as_ref() else {
            panic!("expected local n");
        };
        assert_eq!(name, "n");

        let MachineTerm::Ident { name, .. } = func.as_ref() else {
            panic!("expected Nat.add global");
        };
        assert_eq!(name.as_dotted(), "Nat.add");
    }

    #[test]
    fn resolve_with_repair_options_suggests_short_global_replacement() {
        let imports = [nat_import()];
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = resolve_source_with_options(
            "import Std.Nat.Basic\ndef Test.bad : Nat := zero",
            &imports,
            &options,
        )
        .expect_err("short global suffix should be rejected with a repair suggestion");

        assert_eq!(err.kind, MachineDiagnosticKind::ShortGlobalName);
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(err.suggestions[0].replacement.as_deref(), Some("Nat.zero"));
    }

    #[test]
    fn resolve_with_repair_options_omits_replacement_for_ambiguous_exact_name() {
        let imports = [
            verified_import("Left.Module", &["Shared.X"]),
            verified_import("Right.Module", &["Shared.X"]),
        ];
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = resolve_source_with_options(
            "\
import Left.Module
import Right.Module
def Test.bad : X := X",
            &imports,
            &options,
        )
        .expect_err("short suffix should be rejected without suggesting an ambiguous exact name");

        assert_eq!(err.kind, MachineDiagnosticKind::ShortGlobalName);
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(err.suggestions[0].replacement, None);
        assert_eq!(
            err.suggestions[0].candidates,
            vec![MachineRepairCandidate {
                name: npa_cert::Name::from_dotted("Shared.X"),
                decl_interface_hash: Some(hash(2)),
            }]
        );
    }

    #[test]
    fn resolves_previous_declaration_by_exact_name() {
        let resolved = resolve_source(
            "\
def Test.id (A : Type) (x : A) : A := x
def Test.use (A : Type) (x : A) : A := Test.id A x",
            &[],
        )
        .expect("source should resolve");

        let MachineItem::Def(decl) = &resolved.module.items[1] else {
            panic!("expected second def");
        };
        let MachineTerm::App { func, .. } = &decl.value else {
            panic!("expected application");
        };
        let MachineTerm::App { func, .. } = func.as_ref() else {
            panic!("expected application");
        };
        let MachineTerm::Ident { name, .. } = func.as_ref() else {
            panic!("expected Test.id global");
        };
        assert_eq!(name.as_dotted(), "Test.id");
    }

    #[test]
    fn rejects_missing_verified_import() {
        assert_eq!(
            resolve_err("import Std.Nat.Basic", &[]),
            MachineDiagnosticKind::MissingVerifiedImport
        );
    }

    #[test]
    fn rejects_short_global_suffix() {
        let imports = [nat_import()];
        assert_eq!(
            resolve_err(
                "import Std.Nat.Basic\ndef Test.bad (n : Nat) : Nat := add n Nat.zero",
                &imports,
            ),
            MachineDiagnosticKind::ShortGlobalName
        );
    }

    #[test]
    fn rejects_unknown_global_name() {
        let imports = [nat_import()];
        assert_eq!(
            resolve_err(
                "import Std.Nat.Basic\ndef Test.bad (n : Nat) : Nat := Nat.mul n Nat.zero",
                &imports,
            ),
            MachineDiagnosticKind::UnknownGlobalName
        );
    }

    #[test]
    fn at_or_universe_args_force_global_lookup_before_local_lookup() {
        assert_eq!(
            resolve_err("def Test.bad (x : Type) : Type := @x", &[]),
            MachineDiagnosticKind::UnknownGlobalName
        );
        assert_eq!(
            resolve_err("def Test.bad.{u} (x : Type) : Type := x.{u}", &[]),
            MachineDiagnosticKind::UnknownGlobalName
        );
    }

    #[test]
    fn rejects_ambiguous_imported_exact_name() {
        let imports = [
            verified_import("Std.Nat.Left", &["Nat", "Nat.zero"]),
            verified_import("Std.Nat.Right", &["Nat", "Nat.zero"]),
        ];
        assert_eq!(
            resolve_err(
                "\
import Std.Nat.Left
import Std.Nat.Right
def Test.bad : Nat := Nat.zero",
                &imports,
            ),
            MachineDiagnosticKind::AmbiguousGlobalName
        );
    }

    #[test]
    fn repeated_same_import_does_not_make_exports_ambiguous() {
        let imports = [nat_import()];
        resolve_source(
            "\
import Std.Nat.Basic
import Std.Nat.Basic
def Test.ok : Nat := Nat.zero",
            &imports,
        )
        .expect("duplicate source import should resolve to the same verified import");
    }

    #[test]
    fn repeated_identical_verified_import_is_accepted() {
        let import = nat_import();
        let imports = [import.clone(), import];
        resolve_source(
            "\
import Std.Nat.Basic
def Test.ok : Nat := Nat.zero",
            &imports,
        )
        .expect("identical verified imports should be order independent");
    }

    #[test]
    fn rejects_duplicate_verified_import_interfaces_for_one_module() {
        let first = nat_import();
        let mut second = verified_import("Std.Nat.Basic", &["Nat", "Nat.succ"]);
        second.export_hash = hash(9);
        let imports = [first, second];

        assert_eq!(
            resolve_err("import Std.Nat.Basic", &imports),
            MachineDiagnosticKind::ImportResolutionError
        );
    }

    #[test]
    fn rejects_global_shadowed_by_local() {
        let imports = [nat_import()];
        assert_eq!(
            resolve_err(
                "import Std.Nat.Basic\ndef Test.bad (Nat : Type) : Nat := Nat",
                &imports,
            ),
            MachineDiagnosticKind::GlobalShadowedByLocal
        );
    }

    #[test]
    fn rejects_current_declaration_root_shadowed_by_local() {
        assert_eq!(
            resolve_err("def Test.bad (Test : Type) : Test := Test", &[]),
            MachineDiagnosticKind::GlobalShadowedByLocal
        );
    }

    #[test]
    fn rejects_current_declaration_root_shadowed_by_let() {
        assert_eq!(
            resolve_err(
                "def Test.bad : Type := let Test : Type := Type in Test",
                &[],
            ),
            MachineDiagnosticKind::GlobalShadowedByLocal
        );
    }

    #[test]
    fn rejects_future_declaration_root_shadowed_by_local() {
        assert_eq!(
            resolve_err(
                "\
def A.f (B : Type) : B := B
def B.g : Type := Type",
                &[],
            ),
            MachineDiagnosticKind::GlobalShadowedByLocal
        );
    }

    #[test]
    fn rejects_duplicate_declaration() {
        assert_eq!(
            resolve_err(
                "\
def Test.x : Type := Type
def Test.x : Type := Type",
                &[],
            ),
            MachineDiagnosticKind::DuplicateDeclaration
        );
    }

    #[test]
    fn rejects_duplicate_universe_param() {
        assert_eq!(
            resolve_err("def Test.bad.{u,u} : Sort u := Sort u", &[]),
            MachineDiagnosticKind::DuplicateUniverseParam
        );
    }

    #[test]
    fn rejects_unknown_universe_param() {
        assert_eq!(
            resolve_err("def Test.bad.{u} : Sort v := Sort u", &[]),
            MachineDiagnosticKind::UnknownUniverseParam
        );
    }
}
