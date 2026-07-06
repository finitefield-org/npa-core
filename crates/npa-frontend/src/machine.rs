use std::collections::{BTreeMap, BTreeSet};

use crate::MachineSurfaceCallableInterfaceTable;
use crate::{FileId, Span};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineModule {
    pub file_id: FileId,
    pub items: Vec<MachineItem>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineItem {
    Import { module: MachineName, span: Span },
    Def(MachineDecl),
    Theorem(MachineDecl),
}

impl MachineItem {
    pub fn span(&self) -> Span {
        match self {
            Self::Import { span, .. } => *span,
            Self::Def(decl) | Self::Theorem(decl) => decl.span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDecl {
    pub name: MachineName,
    pub universe_params: Vec<MachineUniverseParam>,
    pub binders: Vec<MachineBinder>,
    pub ty: MachineTerm,
    pub value: MachineTerm,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineUniverseParam {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineName {
    pub parts: Vec<String>,
    pub span: Span,
}

impl MachineName {
    pub fn new(parts: Vec<String>, span: Span) -> Self {
        Self { parts, span }
    }

    pub fn as_dotted(&self) -> String {
        self.parts.join(".")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineBinder {
    pub name: String,
    pub ty: MachineTerm,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineLevel {
    Nat {
        value: u64,
        span: Span,
    },
    Param {
        name: String,
        span: Span,
    },
    Succ {
        level: Box<MachineLevel>,
        span: Span,
    },
    Max {
        lhs: Box<MachineLevel>,
        rhs: Box<MachineLevel>,
        span: Span,
    },
    IMax {
        lhs: Box<MachineLevel>,
        rhs: Box<MachineLevel>,
        span: Span,
    },
}

impl MachineLevel {
    pub fn span(&self) -> Span {
        match self {
            Self::Nat { span, .. }
            | Self::Param { span, .. }
            | Self::Succ { span, .. }
            | Self::Max { span, .. }
            | Self::IMax { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineTerm {
    Ident {
        name: MachineName,
        universe_args: Option<Vec<MachineLevel>>,
        explicit_mode: bool,
        span: Span,
    },
    Local {
        name: String,
        span: Span,
    },
    Prop {
        span: Span,
    },
    Type {
        level: MachineLevel,
        span: Span,
    },
    Sort {
        level: MachineLevel,
        span: Span,
    },
    App {
        func: Box<MachineTerm>,
        arg: Box<MachineTerm>,
        span: Span,
    },
    Lam {
        binders: Vec<MachineBinder>,
        body: Box<MachineTerm>,
        span: Span,
    },
    Pi {
        binders: Vec<MachineBinder>,
        body: Box<MachineTerm>,
        span: Span,
    },
    Let {
        name: String,
        ty: Box<MachineTerm>,
        value: Box<MachineTerm>,
        body: Box<MachineTerm>,
        span: Span,
    },
    Annot {
        expr: Box<MachineTerm>,
        ty: Box<MachineTerm>,
        span: Span,
    },
}

impl MachineTerm {
    pub fn span(&self) -> Span {
        match self {
            Self::Ident { span, .. }
            | Self::Local { span, .. }
            | Self::Prop { span }
            | Self::Type { span, .. }
            | Self::Sort { span, .. }
            | Self::App { span, .. }
            | Self::Lam { span, .. }
            | Self::Pi { span, .. }
            | Self::Let { span, .. }
            | Self::Annot { span, .. } => *span,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineSurfaceMode {
    Complete,
    Repair,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineCompileOptions {
    pub mode: MachineSurfaceMode,
    pub allow_universe_meta: bool,
}

impl Default for MachineCompileOptions {
    fn default() -> Self {
        Self {
            mode: MachineSurfaceMode::Complete,
            allow_universe_meta: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineLocalDecl {
    pub name: String,
    pub ty: npa_kernel::Expr,
    pub value: Option<npa_kernel::Expr>,
}

#[derive(Clone, Debug)]
pub struct MachineTermElabContext {
    pub(crate) global_scope: MachineGlobalScope,
    pub(crate) local_context: Vec<MachineLocalDecl>,
    pub(crate) universe_params: Vec<String>,
    pub(crate) kernel_env: MachineKernelEnvView,
    pub(crate) callable_interface_table: MachineSurfaceCallableInterfaceTable,
    pub(crate) current_module: Option<npa_cert::ModuleName>,
    pub(crate) direct_imports: Vec<MachineDirectImportRef>,
    pub(crate) loaded_available_decls: Vec<MachineLoadedAvailableDeclRef>,
    pub(crate) verified_imports: Vec<MachineVerifiedImportRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MachineDirectImportRef {
    pub module: npa_cert::ModuleName,
    pub export_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MachineLoadedAvailableDeclRef {
    pub module: npa_cert::ModuleName,
    pub export_hash: npa_cert::Hash,
    pub name: npa_cert::Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MachineVerifiedImportRef {
    pub module: npa_cert::ModuleName,
    pub export_hash: npa_cert::Hash,
    pub decls: Vec<MachineVerifiedImportDeclRef>,
    pub exports: Vec<MachineVerifiedImportExportRef>,
    pub generated_decls: Vec<MachineVerifiedImportGeneratedDeclRef>,
    pub generated_exports: Vec<MachineVerifiedImportGeneratedExportRef>,
    pub dependencies: Vec<MachineVerifiedImportDependencyRef>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MachineVerifiedImportDeclRef {
    pub name: npa_cert::Name,
    pub decl_interface_hash: npa_cert::Hash,
    pub public_export: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MachineVerifiedImportExportRef {
    pub name: npa_cert::Name,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MachineVerifiedImportGeneratedDeclRef {
    pub parent_name: npa_cert::Name,
    pub name: npa_cert::Name,
    pub parent_decl_interface_hash: npa_cert::Hash,
    pub decl_interface_hash: npa_cert::Hash,
    pub public_export: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MachineVerifiedImportGeneratedExportRef {
    pub parent_name: npa_cert::Name,
    pub name: npa_cert::Name,
    pub parent_decl_interface_hash: npa_cert::Hash,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MachineVerifiedImportDependencyRef {
    pub module: npa_cert::ModuleName,
    pub export_hash: npa_cert::Hash,
    pub name: npa_cert::Name,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineCheckedCurrentDecl {
    pub name: npa_cert::Name,
    pub source_index: u64,
    pub decl_interface_hash: npa_cert::Hash,
    pub decl: npa_kernel::Decl,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineCheckedCurrentGeneratedDecl {
    pub name: npa_cert::Name,
    pub parent_source_index: u64,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineGlobalScope {
    pub(crate) entries: Vec<MachineGlobalScopeEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineGlobalScopeEntry {
    Imported {
        name: npa_cert::Name,
        import_index: u32,
        decl_interface_hash: npa_cert::Hash,
    },
    CurrentModule {
        name: npa_cert::Name,
        source_index: u64,
        decl_interface_hash: npa_cert::Hash,
    },
    CurrentGenerated {
        name: npa_cert::Name,
        parent_source_index: u64,
        decl_interface_hash: npa_cert::Hash,
    },
}

impl MachineGlobalScopeEntry {
    pub fn name(&self) -> &npa_cert::Name {
        match self {
            Self::Imported { name, .. }
            | Self::CurrentModule { name, .. }
            | Self::CurrentGenerated { name, .. } => name,
        }
    }

    pub fn decl_interface_hash(&self) -> &npa_cert::Hash {
        match self {
            Self::Imported {
                decl_interface_hash,
                ..
            }
            | Self::CurrentModule {
                decl_interface_hash,
                ..
            }
            | Self::CurrentGenerated {
                decl_interface_hash,
                ..
            } => decl_interface_hash,
        }
    }
}

impl MachineTermElabContext {
    pub fn local_context(&self) -> &[MachineLocalDecl] {
        &self.local_context
    }

    pub fn universe_params(&self) -> &[String] {
        &self.universe_params
    }

    pub fn kernel_env(&self) -> &MachineKernelEnvView {
        &self.kernel_env
    }

    pub fn global_scope_entries(&self) -> &[MachineGlobalScopeEntry] {
        &self.global_scope.entries
    }

    pub fn callable_interface_table(&self) -> &MachineSurfaceCallableInterfaceTable {
        &self.callable_interface_table
    }

    pub fn direct_import_identity(
        &self,
        import_index: u32,
    ) -> Option<(&npa_cert::ModuleName, npa_cert::Hash)> {
        let index = usize::try_from(import_index).ok()?;
        self.direct_imports
            .get(index)
            .map(|import| (&import.module, import.export_hash))
    }

    pub fn is_direct_import(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
    ) -> bool {
        self.direct_imports
            .iter()
            .any(|import| &import.module == module && &import.export_hash == export_hash)
    }

    pub fn import_decl_loaded_in_kernel_env(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        name: &npa_cert::Name,
    ) -> bool {
        self.is_direct_import(module, export_hash)
            || exactly_one(self.loaded_available_decls.iter().filter(|decl| {
                &decl.module == module && &decl.export_hash == export_hash && &decl.name == name
            }))
    }

    pub fn has_verified_import(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
    ) -> bool {
        exactly_one(
            self.verified_imports
                .iter()
                .filter(|import| &import.module == module && &import.export_hash == export_hash),
        )
    }

    pub fn verified_import_depends_on_export(
        &self,
        owner_module: &npa_cert::ModuleName,
        owner_export_hash: &npa_cert::Hash,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        name: &npa_cert::Name,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        let matching_imports: Vec<_> = self
            .verified_imports
            .iter()
            .filter(|import| {
                &import.module == owner_module && &import.export_hash == owner_export_hash
            })
            .collect();
        let [import] = matching_imports.as_slice() else {
            return false;
        };

        exactly_one(import.dependencies.iter().filter(|dependency| {
            &dependency.module == module
                && &dependency.export_hash == export_hash
                && &dependency.name == name
                && &dependency.decl_interface_hash == decl_interface_hash
        }))
    }

    pub fn current_module_is(&self, module: &npa_cert::ModuleName) -> bool {
        self.current_module
            .as_ref()
            .is_some_and(|current_module| current_module == module)
    }

    pub fn direct_import_export_matches(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        name: &npa_cert::Name,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        self.is_direct_import(module, export_hash)
            && self.verified_import_export_matches(module, export_hash, name, decl_interface_hash)
    }

    pub fn verified_import_export_matches(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        name: &npa_cert::Name,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        let matching_imports: Vec<_> = self
            .verified_imports
            .iter()
            .filter(|import| &import.module == module && &import.export_hash == export_hash)
            .collect();
        let [import] = matching_imports.as_slice() else {
            return false;
        };

        exactly_one(import.exports.iter().filter(|export| {
            &export.name == name && &export.decl_interface_hash == decl_interface_hash
        }))
    }

    pub fn verified_import_decl_matches(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        name: &npa_cert::Name,
        decl_interface_hash: &npa_cert::Hash,
        public_export: bool,
    ) -> bool {
        let matching_imports: Vec<_> = self
            .verified_imports
            .iter()
            .filter(|import| &import.module == module && &import.export_hash == export_hash)
            .collect();
        let [import] = matching_imports.as_slice() else {
            return false;
        };

        exactly_one(import.decls.iter().filter(|decl| {
            &decl.name == name
                && &decl.decl_interface_hash == decl_interface_hash
                && decl.public_export == public_export
        }))
    }

    pub fn direct_import_generated_export_matches(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        parent_name: &npa_cert::Name,
        name: &npa_cert::Name,
        parent_decl_interface_hash: &npa_cert::Hash,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        self.is_direct_import(module, export_hash)
            && self.verified_import_generated_export_matches(
                module,
                export_hash,
                parent_name,
                name,
                parent_decl_interface_hash,
                decl_interface_hash,
            )
    }

    pub fn verified_import_generated_export_matches(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        parent_name: &npa_cert::Name,
        name: &npa_cert::Name,
        parent_decl_interface_hash: &npa_cert::Hash,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        let matching_imports: Vec<_> = self
            .verified_imports
            .iter()
            .filter(|import| &import.module == module && &import.export_hash == export_hash)
            .collect();
        let [import] = matching_imports.as_slice() else {
            return false;
        };

        exactly_one(import.generated_exports.iter().filter(|export| {
            &export.parent_name == parent_name
                && &export.name == name
                && &export.parent_decl_interface_hash == parent_decl_interface_hash
                && &export.decl_interface_hash == decl_interface_hash
        }))
    }

    pub fn verified_import_generated_decl_matches(
        &self,
        module: &npa_cert::ModuleName,
        export_hash: &npa_cert::Hash,
        parent_name: &npa_cert::Name,
        name: &npa_cert::Name,
        decl_interface_hash: &npa_cert::Hash,
        public_export: bool,
    ) -> bool {
        let matching_imports: Vec<_> = self
            .verified_imports
            .iter()
            .filter(|import| &import.module == module && &import.export_hash == export_hash)
            .collect();
        let [import] = matching_imports.as_slice() else {
            return false;
        };

        exactly_one(import.generated_decls.iter().filter(|decl| {
            &decl.parent_name == parent_name
                && &decl.name == name
                && &decl.parent_decl_interface_hash == decl_interface_hash
                && &decl.decl_interface_hash == decl_interface_hash
                && decl.public_export == public_export
        }))
    }

    pub fn current_module_entry_matches(
        &self,
        module: &npa_cert::ModuleName,
        name: &npa_cert::Name,
        source_index: u64,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        let Some(current_module) = &self.current_module else {
            return false;
        };
        if current_module != module || !name_is_in_module(name, current_module) {
            return false;
        }
        exactly_one(self.global_scope.entries.iter().filter(|entry| {
            matches!(
                entry,
                MachineGlobalScopeEntry::CurrentModule {
                    name: entry_name,
                    source_index: entry_source_index,
                    decl_interface_hash: entry_decl_interface_hash,
                } if entry_name == name
                    && *entry_source_index == source_index
                    && entry_decl_interface_hash == decl_interface_hash
            )
        }))
    }

    pub fn current_generated_entry_matches(
        &self,
        module: &npa_cert::ModuleName,
        name: &npa_cert::Name,
        parent_source_index: u64,
        decl_interface_hash: &npa_cert::Hash,
    ) -> bool {
        let Some(current_module) = &self.current_module else {
            return false;
        };
        if current_module != module || !name_is_in_module(name, current_module) {
            return false;
        }
        exactly_one(self.global_scope.entries.iter().filter(|entry| {
            matches!(
                entry,
                MachineGlobalScopeEntry::CurrentGenerated {
                    name: entry_name,
                    parent_source_index: entry_parent_source_index,
                    decl_interface_hash: entry_decl_interface_hash,
                } if entry_name == name
                    && *entry_parent_source_index == parent_source_index
                    && entry_decl_interface_hash == decl_interface_hash
            )
        }))
    }

    pub fn with_callable_interface_table(
        mut self,
        table: MachineSurfaceCallableInterfaceTable,
    ) -> Self {
        self.callable_interface_table = table;
        self
    }

    pub fn with_additional_global_scope_entries(
        mut self,
        entries: impl IntoIterator<Item = MachineGlobalScopeEntry>,
    ) -> Self {
        for entry in entries {
            let exists = self.global_scope.entries.iter().any(|existing| {
                existing.name() == entry.name()
                    && existing.decl_interface_hash() == entry.decl_interface_hash()
            });
            if !exists {
                self.global_scope.entries.push(entry);
            }
        }
        self
    }
}

fn exactly_one<T>(iter: impl Iterator<Item = T>) -> bool {
    iter.take(2).count() == 1
}

fn name_is_in_module(name: &npa_cert::Name, module: &npa_cert::ModuleName) -> bool {
    name.0.len() > module.0.len() && name.0.starts_with(&module.0)
}

#[derive(Clone, Debug)]
pub struct MachineKernelEnvView {
    pub(crate) env: npa_kernel::Env,
    decl_interface_hashes: BTreeMap<String, BTreeSet<npa_cert::Hash>>,
}

impl MachineKernelEnvView {
    pub(crate) fn new(env: npa_kernel::Env) -> Self {
        Self {
            env,
            decl_interface_hashes: BTreeMap::new(),
        }
    }

    pub(crate) fn with_decl_interface_hashes(
        env: npa_kernel::Env,
        hashes: impl IntoIterator<Item = (npa_cert::Name, npa_cert::Hash)>,
    ) -> Self {
        let mut view = Self::new(env);
        for (name, hash) in hashes {
            view.add_decl_interface_hash(name, hash);
        }
        view
    }

    pub fn empty() -> Self {
        Self {
            env: npa_kernel::Env::new(),
            decl_interface_hashes: BTreeMap::new(),
        }
    }

    pub fn env(&self) -> &npa_kernel::Env {
        &self.env
    }

    pub(crate) fn add_decl_interface_hash(&mut self, name: npa_cert::Name, hash: npa_cert::Hash) {
        self.decl_interface_hashes
            .entry(name.as_dotted())
            .or_default()
            .insert(hash);
    }

    pub(crate) fn has_decl_interface_hash(&self, name: &str, hash: &npa_cert::Hash) -> bool {
        self.decl_interface_hashes
            .get(name)
            .is_some_and(|hashes| hashes.contains(hash))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTermSourceCanonical {
    pub source: String,
    pub canonical_bytes: Vec<u8>,
    pub canonical_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTermAst {
    pub(crate) term: MachineTerm,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachineResolvedConstant {
    pub name: npa_cert::Name,
    pub decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineTermCheckResult {
    pub expr: npa_kernel::Expr,
    pub inferred_type: npa_kernel::Expr,
    pub core_hash: npa_cert::Hash,
    pub contextual_core_hash: npa_cert::Hash,
    pub constants: Vec<MachineResolvedConstant>,
}
