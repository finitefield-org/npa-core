use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{Hash, Name};
use npa_frontend::{
    canonicalize_machine_term_source, elaborate_machine_term_check,
    is_machine_surface_renderable_name, MachineCallableBinderVisibility, MachineCompileOptions,
    MachineDiagnostic, MachineGlobalScopeEntry, MachineLocalDecl,
    MachineSurfaceCallableInterfaceTable, MachineSurfaceCallableRef, MachineSurfaceMode,
    MachineTermCheckResult, MachineTermElabContext,
};
use npa_kernel::{Expr, Level};

const GLOBAL_REF_VIEW_TAG: &str = "npa.machine-api.global-ref-view.v2";
const LOCAL_ID_TAG: &str = "npa.machine-api.local-id.v1";
const PREC_BINDER: u8 = 10;
const PREC_APP: u8 = 80;
const PREC_ATOM: u8 = 100;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineExprRendererContext<'a> {
    pub display_scope: &'a MachineDisplayRenderScope,
    pub callable_interface_table: &'a MachineSurfaceCallableInterfaceTable,
    pub base_context: &'a [MachineLocalDecl],
    pub universe_params: &'a [String],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineExprView {
    pub core_hash: Hash,
    pub head: Option<MachineGlobalRefView>,
    pub constants: Vec<MachineGlobalRefView>,
    pub free_locals: Vec<LocalId>,
    pub size: u32,
    pub machine: String,
    pub pretty: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreExprMetadata {
    pub core_hash: Hash,
    pub head: Option<Name>,
    pub constants: Vec<Name>,
    pub free_locals: Vec<LocalId>,
    pub size: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(pub u32);

impl LocalId {
    pub fn wire(self) -> String {
        format!("l{}", self.0)
    }

    pub fn canonical_bytes(self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_string(&mut out, LOCAL_ID_TAG);
        encode_uvar(&mut out, self.0 as u64);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDisplayRenderScope {
    entries: Vec<MachineDisplayRenderScopeEntry>,
    entries_by_name: BTreeMap<String, MachineDisplayRenderScopeEntry>,
    global_roots: BTreeSet<String>,
}

impl MachineDisplayRenderScope {
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
            entries_by_name: BTreeMap::new(),
            global_roots: BTreeSet::new(),
        }
    }

    pub fn from_entries(
        entries: impl IntoIterator<Item = MachineDisplayRenderScopeEntry>,
    ) -> Result<Self, MachineExprRendererError> {
        let mut scope = Self::empty();
        for entry in entries {
            scope.push_entry(entry)?;
        }
        Ok(scope)
    }

    pub fn with_candidate_global_roots(
        mut self,
        roots: impl IntoIterator<Item = String>,
    ) -> Result<Self, MachineExprRendererError> {
        for root in roots {
            validate_local_name(&root)?;
            self.global_roots.insert(root);
        }
        Ok(self)
    }

    pub fn entries(&self) -> &[MachineDisplayRenderScopeEntry] {
        &self.entries
    }

    pub fn entry_for_name(&self, name: &str) -> Option<&MachineDisplayRenderScopeEntry> {
        self.entries_by_name.get(name)
    }

    pub fn global_roots(&self) -> &BTreeSet<String> {
        &self.global_roots
    }

    fn push_entry(
        &mut self,
        entry: MachineDisplayRenderScopeEntry,
    ) -> Result<(), MachineExprRendererError> {
        validate_display_scope_entry(&entry)?;
        if entry.name != *entry.view.name() {
            return Err(MachineExprRendererError::DisplayScopeNameMismatch {
                entry_name: entry.name.clone(),
                view_name: entry.view.name().clone(),
            });
        }
        if !is_machine_surface_renderable_name(&entry.name) {
            return Err(MachineExprRendererError::GlobalNameNotRenderable {
                name: entry.name.clone(),
            });
        }

        let dotted = entry.name.as_dotted();
        if self.entries_by_name.contains_key(&dotted) {
            return Err(MachineExprRendererError::DuplicateDisplayName {
                name: entry.name.clone(),
            });
        }
        if let Some(root) = entry.name.0.first() {
            self.global_roots.insert(root.clone());
        }
        self.entries_by_name.insert(dotted, entry.clone());
        self.entries.push(entry);
        self.entries.sort_by_key(|entry| entry.name.as_dotted());
        Ok(())
    }
}

impl Default for MachineDisplayRenderScope {
    fn default() -> Self {
        Self::empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDisplayRenderScopeEntry {
    pub name: Name,
    pub view: MachineGlobalRefView,
    pub owner_context: MachineApiResolvedDisplayCoreRefOwner,
    pub candidate_resolution: Option<MachineGlobalScopeEntry>,
    pub callable_ref: MachineSurfaceCallableRef,
}

impl MachineDisplayRenderScopeEntry {
    pub fn new(
        view: MachineGlobalRefView,
        owner_context: MachineApiResolvedDisplayCoreRefOwner,
        callable_ref: MachineSurfaceCallableRef,
    ) -> Self {
        Self {
            name: view.name().clone(),
            view,
            owner_context,
            candidate_resolution: None,
            callable_ref,
        }
    }

    pub fn with_candidate_resolution(mut self, resolution: MachineGlobalScopeEntry) -> Self {
        self.candidate_resolution = Some(resolution);
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MachineApiResolvedDisplayCoreRefOwner {
    CurrentSessionRootModule {
        module: Name,
    },
    VerifiedImportedModule {
        owner_module: Name,
        owner_export_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineGlobalRefView {
    Imported {
        module: Name,
        name: Name,
        export_hash: Hash,
        decl_interface_hash: Hash,
        public_export: bool,
        tactic_head_visible: bool,
    },
    CurrentModule {
        module: Name,
        name: Name,
        decl_interface_hash: Hash,
        source_index: u64,
    },
    LocalGenerated {
        module: Name,
        export_hash: Option<Hash>,
        parent_name: Name,
        name: Name,
        parent_decl_interface_hash: Hash,
        decl_interface_hash: Hash,
        public_export: bool,
        tactic_head_visible: bool,
    },
}

impl MachineGlobalRefView {
    pub fn name(&self) -> &Name {
        match self {
            Self::Imported { name, .. }
            | Self::CurrentModule { name, .. }
            | Self::LocalGenerated { name, .. } => name,
        }
    }

    pub fn decl_interface_hash(&self) -> Hash {
        match self {
            Self::Imported {
                decl_interface_hash,
                ..
            }
            | Self::CurrentModule {
                decl_interface_hash,
                ..
            }
            | Self::LocalGenerated {
                decl_interface_hash,
                ..
            } => *decl_interface_hash,
        }
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_string(&mut out, GLOBAL_REF_VIEW_TAG);
        match self {
            Self::Imported {
                module,
                name,
                export_hash,
                decl_interface_hash,
                public_export,
                tactic_head_visible,
            } => {
                out.push(0x00);
                encode_name(&mut out, module);
                encode_name(&mut out, name);
                out.extend(export_hash);
                out.extend(decl_interface_hash);
                encode_bool(&mut out, *public_export);
                encode_bool(&mut out, *tactic_head_visible);
            }
            Self::CurrentModule {
                module,
                name,
                decl_interface_hash,
                source_index,
            } => {
                out.push(0x01);
                encode_name(&mut out, module);
                encode_name(&mut out, name);
                out.extend(decl_interface_hash);
                encode_uvar(&mut out, *source_index);
            }
            Self::LocalGenerated {
                module,
                export_hash,
                parent_name,
                name,
                parent_decl_interface_hash,
                decl_interface_hash,
                public_export,
                tactic_head_visible,
            } => {
                out.push(0x02);
                encode_name(&mut out, module);
                encode_option_hash(&mut out, export_hash.as_ref());
                encode_name(&mut out, parent_name);
                encode_name(&mut out, name);
                out.extend(parent_decl_interface_hash);
                out.extend(decl_interface_hash);
                encode_bool(&mut out, *public_export);
                encode_bool(&mut out, *tactic_head_visible);
            }
        }
        out
    }
}

impl Ord for MachineGlobalRefView {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.canonical_bytes().cmp(&other.canonical_bytes())
    }
}

impl PartialOrd for MachineGlobalRefView {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineExprRendererError {
    DuplicateDisplayName {
        name: Name,
    },
    DisplayScopeNameMismatch {
        entry_name: Name,
        view_name: Name,
    },
    GlobalNameNotRenderable {
        name: Name,
    },
    InvalidGlobalRefViewInvariant {
        name: Name,
        reason: &'static str,
    },
    DisplayScopeOwnerContextMismatch {
        name: Name,
    },
    DisplayScopeCallableRefMismatch {
        name: Name,
    },
    DisplayScopeCandidateResolutionRequired {
        name: Name,
    },
    DisplayScopeCandidateResolutionMismatch {
        name: Name,
    },
    GlobalNameMissingFromDisplayScope {
        name: String,
    },
    GlobalShadowedByLocal {
        name: Name,
        local_name: String,
    },
    LocalNameInvalid {
        name: String,
    },
    LocalNameShadowsGlobalRoot {
        name: String,
    },
    BVarOutOfScope {
        index: u32,
        binder_depth: usize,
        base_context_len: usize,
    },
    UniverseParamNotRenderable {
        name: String,
    },
    UnknownUniverseParam {
        name: String,
    },
    ExpressionTooLarge,
    FreshBinderNameExhausted,
    CanonicalizationFailed {
        diagnostic: Box<MachineDiagnostic>,
    },
    ElaborationFailed {
        diagnostic: Box<MachineDiagnostic>,
    },
    QAGlobalResolutionMissing {
        name: Name,
        decl_interface_hash: Hash,
    },
    QAGlobalResolutionAmbiguous {
        name: Name,
        decl_interface_hash: Hash,
    },
    QAGlobalResolutionMismatch {
        name: Name,
    },
    QAContextBaseContextMismatch,
    QAContextUniverseParamMismatch,
    RoundTripMismatch,
}

pub fn render_machine_expr_view(
    expr: &Expr,
    context: &MachineExprRendererContext<'_>,
) -> Result<MachineExprView, MachineExprRendererError> {
    validate_base_context(context)?;
    let mut renderer = MachineExprRenderer::new(context);
    let rendered = renderer.render_expr(expr, 0)?;
    canonicalize_machine_term_source(&rendered.source).map_err(|diagnostic| {
        MachineExprRendererError::CanonicalizationFailed {
            diagnostic: Box::new(diagnostic),
        }
    })?;

    let mut constants = BTreeSet::new();
    collect_constants(expr, context, &mut constants)?;

    Ok(MachineExprView {
        core_hash: hash_core_expr(expr),
        head: syntactic_head(expr)
            .map(|head| resolve_global_view(head, context).map(|entry| entry.view.clone()))
            .transpose()?,
        constants: constants.into_iter().collect(),
        free_locals: free_locals(expr, context.base_context.len())?,
        size: expr_size(expr)?,
        machine: rendered.source,
        pretty: None,
    })
}

pub fn core_expr_metadata(
    expr: &Expr,
    base_context_len: usize,
) -> Result<CoreExprMetadata, MachineExprRendererError> {
    let mut constants = BTreeSet::new();
    collect_constant_names(expr, &mut constants);
    Ok(CoreExprMetadata {
        core_hash: hash_core_expr(expr),
        head: syntactic_head_name(expr),
        constants: constants.into_iter().collect(),
        free_locals: free_locals(expr, base_context_len)?,
        size: expr_size(expr)?,
    })
}

pub fn render_kernel_core_expr(expr: &Expr) -> String {
    match expr {
        Expr::Sort(level) => format!("Sort({})", render_kernel_core_level(level)),
        Expr::BVar(index) => format!("BVar({index})"),
        Expr::Const { name, levels } => {
            if levels.is_empty() {
                format!("Const({name})")
            } else {
                format!(
                    "Const({}.{{{}}})",
                    name,
                    levels
                        .iter()
                        .map(render_kernel_core_level)
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
        }
        Expr::App(func, arg) => format!(
            "App({}, {})",
            render_kernel_core_expr(func),
            render_kernel_core_expr(arg)
        ),
        Expr::Lam { binder, ty, body } => format!(
            "Lam({}, {}, {})",
            binder,
            render_kernel_core_expr(ty),
            render_kernel_core_expr(body)
        ),
        Expr::Pi { binder, ty, body } => format!(
            "Pi({}, {}, {})",
            binder,
            render_kernel_core_expr(ty),
            render_kernel_core_expr(body)
        ),
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => format!(
            "Let({}, {}, {}, {})",
            binder,
            render_kernel_core_expr(ty),
            render_kernel_core_expr(value),
            render_kernel_core_expr(body)
        ),
    }
}

pub fn render_machine_expr_source(
    expr: &Expr,
    context: &MachineExprRendererContext<'_>,
) -> Result<String, MachineExprRendererError> {
    render_machine_expr_view(expr, context).map(|view| view.machine)
}

pub fn renderer_qa_round_trip(
    expr: &Expr,
    render_context: &MachineExprRendererContext<'_>,
    elab_context: &MachineTermElabContext,
    expected_type: &Expr,
) -> Result<(), MachineExprRendererError> {
    validate_qa_elab_context_matches_renderer(render_context, elab_context)?;
    let view = render_machine_expr_view(expr, render_context)?;
    let options = MachineCompileOptions {
        mode: MachineSurfaceMode::Complete,
        allow_universe_meta: false,
    };
    let display_import_index_offset = display_projection_import_index_offset(elab_context)?;
    validate_display_scope_against_qa_context(render_context, elab_context)?;
    let qa_context = elab_context
        .clone()
        .with_additional_global_scope_entries(display_scope_frontend_projection(
            render_context,
            display_import_index_offset,
        )?)
        .with_callable_interface_table(render_context.callable_interface_table.clone());
    let checked = elaborate_machine_term_check(&view.machine, &qa_context, expected_type, &options)
        .map_err(|diagnostic| MachineExprRendererError::ElaborationFailed {
            diagnostic: Box::new(diagnostic),
        })?;
    validate_frontend_round_trip_resolution(
        &checked,
        render_context,
        &qa_context,
        display_import_index_offset,
    )?;
    let original = owner_aware_expr(expr, render_context)?;
    let round_tripped = owner_aware_expr(&checked.expr, render_context)?;
    if original != round_tripped {
        return Err(MachineExprRendererError::RoundTripMismatch);
    }
    Ok(())
}

fn validate_qa_elab_context_matches_renderer(
    render_context: &MachineExprRendererContext<'_>,
    elab_context: &MachineTermElabContext,
) -> Result<(), MachineExprRendererError> {
    if elab_context.local_context() != render_context.base_context {
        return Err(MachineExprRendererError::QAContextBaseContextMismatch);
    }
    if elab_context.universe_params() != render_context.universe_params {
        return Err(MachineExprRendererError::QAContextUniverseParamMismatch);
    }
    Ok(())
}

struct MachineExprRenderer<'ctx> {
    context: &'ctx MachineExprRendererContext<'ctx>,
    binder_stack: Vec<String>,
}

impl<'ctx> MachineExprRenderer<'ctx> {
    fn new(context: &'ctx MachineExprRendererContext<'ctx>) -> Self {
        Self {
            context,
            binder_stack: Vec::new(),
        }
    }

    fn render_expr(
        &mut self,
        expr: &Expr,
        required_prec: u8,
    ) -> Result<RenderedExpr, MachineExprRendererError> {
        let rendered = match expr {
            Expr::Sort(level) => RenderedExpr {
                source: self.render_sort(level)?,
                precedence: PREC_ATOM,
            },
            Expr::BVar(index) => RenderedExpr {
                source: self.render_bvar(*index)?,
                precedence: PREC_ATOM,
            },
            Expr::Const { name, levels } => {
                let entry = resolve_global_name(name, self.context)?;
                self.ensure_global_not_shadowed(entry.view.name())?;
                RenderedExpr {
                    source: self.render_global(entry, levels, false)?,
                    precedence: PREC_ATOM,
                }
            }
            Expr::App(_, _) => self.render_app(expr)?,
            Expr::Lam { binder, ty, body } => {
                self.render_binder_expr("fun", "=>", binder, ty, body)?
            }
            Expr::Pi { binder, ty, body } => {
                self.render_binder_expr("forall", ",", binder, ty, body)?
            }
            Expr::Let {
                binder,
                ty,
                value,
                body,
            } => self.render_let_expr(binder, ty, value, body)?,
        };

        if rendered.precedence < required_prec {
            Ok(RenderedExpr {
                source: parenthesize(rendered.source),
                precedence: PREC_ATOM,
            })
        } else {
            Ok(rendered)
        }
    }

    fn render_app(&mut self, expr: &Expr) -> Result<RenderedExpr, MachineExprRendererError> {
        let (head, args) = flatten_app(expr);
        let head_source = match head {
            Expr::Const { name, levels } => {
                let entry = resolve_global_name(name, self.context)?;
                self.ensure_global_not_shadowed(entry.view.name())?;
                let explicit_marker = self.explicit_head_marker_required(entry, args.len());
                self.render_global(entry, levels, explicit_marker)?
            }
            _ => self.render_expr(head, PREC_APP)?.source,
        };

        let mut parts = Vec::with_capacity(args.len() + 1);
        parts.push(head_source);
        for arg in args {
            parts.push(self.render_expr(arg, PREC_ATOM)?.source);
        }

        Ok(RenderedExpr {
            source: parts.join(" "),
            precedence: PREC_APP,
        })
    }

    fn render_binder_expr(
        &mut self,
        keyword: &'static str,
        separator: &'static str,
        debug_name: &str,
        ty: &Expr,
        body: &Expr,
    ) -> Result<RenderedExpr, MachineExprRendererError> {
        let binder_name = self.fresh_binder_name(debug_name)?;
        let ty = self.render_annotation_type(ty)?;
        self.binder_stack.push(binder_name.clone());
        let body = self.render_expr(body, 0)?.source;
        self.binder_stack.pop();

        let source = if keyword == "fun" {
            format!("{keyword} ({binder_name} : {ty}) {separator} {body}")
        } else {
            format!("{keyword} ({binder_name} : {ty}){separator} {body}")
        };
        Ok(RenderedExpr {
            source,
            precedence: PREC_BINDER,
        })
    }

    fn render_let_expr(
        &mut self,
        debug_name: &str,
        ty: &Expr,
        value: &Expr,
        body: &Expr,
    ) -> Result<RenderedExpr, MachineExprRendererError> {
        let binder_name = self.fresh_binder_name(debug_name)?;
        let ty = self.render_annotation_type(ty)?;
        let value = self.render_expr(value, PREC_APP)?.source;
        self.binder_stack.push(binder_name.clone());
        let body = self.render_expr(body, 0)?.source;
        self.binder_stack.pop();

        Ok(RenderedExpr {
            source: format!("let {binder_name} : {ty} := {value} in {body}"),
            precedence: PREC_BINDER,
        })
    }

    fn render_annotation_type(&mut self, ty: &Expr) -> Result<String, MachineExprRendererError> {
        let rendered = self.render_expr(ty, 0)?;
        if rendered.precedence == PREC_BINDER {
            Ok(parenthesize(rendered.source))
        } else {
            Ok(rendered.source)
        }
    }

    fn render_global(
        &self,
        entry: &MachineDisplayRenderScopeEntry,
        levels: &[Level],
        explicit_marker: bool,
    ) -> Result<String, MachineExprRendererError> {
        let mut source = String::new();
        if explicit_marker {
            source.push('@');
        }
        source.push_str(&entry.name.as_dotted());
        if !levels.is_empty() {
            source.push_str(".{");
            for (index, level) in levels.iter().enumerate() {
                if index > 0 {
                    source.push(',');
                }
                source.push_str(&render_level(level, self.context.universe_params)?);
            }
            source.push('}');
        }
        Ok(source)
    }

    fn render_sort(&self, level: &Level) -> Result<String, MachineExprRendererError> {
        match level {
            Level::Zero => Ok("Prop".to_owned()),
            Level::Succ(inner) => Ok(format!(
                "Type {}",
                render_level(inner, self.context.universe_params)?
            )),
            _ => Ok(format!(
                "Sort {}",
                render_level(level, self.context.universe_params)?
            )),
        }
    }

    fn render_bvar(&self, index: u32) -> Result<String, MachineExprRendererError> {
        let index = index as usize;
        let binder_depth = self.binder_stack.len();
        if index < binder_depth {
            return Ok(self.binder_stack[binder_depth - 1 - index].clone());
        }
        let base_index_from_inner = index - binder_depth;
        let Some(base_index) = self
            .context
            .base_context
            .len()
            .checked_sub(base_index_from_inner + 1)
        else {
            return Err(MachineExprRendererError::BVarOutOfScope {
                index: index as u32,
                binder_depth,
                base_context_len: self.context.base_context.len(),
            });
        };
        let local = &self.context.base_context[base_index].name;
        validate_local_name(local)?;
        Ok(local.clone())
    }

    fn explicit_head_marker_required(
        &self,
        entry: &MachineDisplayRenderScopeEntry,
        arg_count: usize,
    ) -> bool {
        let Some(callable) = self
            .context
            .callable_interface_table
            .entry_for_ref(&entry.callable_ref)
        else {
            return false;
        };
        callable
            .implicit_profile()
            .iter()
            .take(arg_count)
            .any(|visibility| *visibility == MachineCallableBinderVisibility::Implicit)
    }

    fn fresh_binder_name(&self, debug_name: &str) -> Result<String, MachineExprRendererError> {
        let occupied = occupied_local_names(&self.binder_stack, self.context);
        if is_usable_local_name(debug_name, &occupied) {
            return Ok(debug_name.to_owned());
        }
        if is_usable_local_name("x", &occupied) {
            return Ok("x".to_owned());
        }
        let mut suffix = 0u64;
        loop {
            let candidate = format!("x_{suffix}");
            if !is_machine_local_name(&candidate) {
                break;
            }
            if is_usable_local_name(&candidate, &occupied) {
                return Ok(candidate);
            }
            suffix = suffix
                .checked_add(1)
                .ok_or(MachineExprRendererError::FreshBinderNameExhausted)?;
        }
        Err(MachineExprRendererError::FreshBinderNameExhausted)
    }

    fn ensure_global_not_shadowed(&self, name: &Name) -> Result<(), MachineExprRendererError> {
        let Some(root) = name.0.first() else {
            return Err(MachineExprRendererError::GlobalNameNotRenderable { name: name.clone() });
        };
        if self.binder_stack.iter().any(|local| local == root)
            || self
                .context
                .base_context
                .iter()
                .any(|local| &local.name == root)
        {
            return Err(MachineExprRendererError::GlobalShadowedByLocal {
                name: name.clone(),
                local_name: root.clone(),
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct RenderedExpr {
    source: String,
    precedence: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum OwnerAwareExpr {
    Sort(Level),
    BVar(u32),
    Const {
        owner_context: Box<MachineApiResolvedDisplayCoreRefOwner>,
        view: Box<MachineGlobalRefView>,
        levels: Vec<Level>,
    },
    App(Box<OwnerAwareExpr>, Box<OwnerAwareExpr>),
    Lam {
        ty: Box<OwnerAwareExpr>,
        body: Box<OwnerAwareExpr>,
    },
    Pi {
        ty: Box<OwnerAwareExpr>,
        body: Box<OwnerAwareExpr>,
    },
    Let {
        ty: Box<OwnerAwareExpr>,
        value: Box<OwnerAwareExpr>,
        body: Box<OwnerAwareExpr>,
    },
}

fn owner_aware_expr(
    expr: &Expr,
    context: &MachineExprRendererContext<'_>,
) -> Result<OwnerAwareExpr, MachineExprRendererError> {
    Ok(match expr {
        Expr::Sort(level) => OwnerAwareExpr::Sort(normalize_level_for_qa(level)),
        Expr::BVar(index) => OwnerAwareExpr::BVar(*index),
        Expr::Const { name, levels } => {
            let entry = resolve_global_name(name, context)?;
            OwnerAwareExpr::Const {
                owner_context: Box::new(entry.owner_context.clone()),
                view: Box::new(entry.view.clone()),
                levels: normalize_levels_for_qa(levels),
            }
        }
        Expr::App(func, arg) => OwnerAwareExpr::App(
            Box::new(owner_aware_expr(func, context)?),
            Box::new(owner_aware_expr(arg, context)?),
        ),
        Expr::Lam { ty, body, .. } => OwnerAwareExpr::Lam {
            ty: Box::new(owner_aware_expr(ty, context)?),
            body: Box::new(owner_aware_expr(body, context)?),
        },
        Expr::Pi { ty, body, .. } => OwnerAwareExpr::Pi {
            ty: Box::new(owner_aware_expr(ty, context)?),
            body: Box::new(owner_aware_expr(body, context)?),
        },
        Expr::Let {
            ty, value, body, ..
        } => OwnerAwareExpr::Let {
            ty: Box::new(owner_aware_expr(ty, context)?),
            value: Box::new(owner_aware_expr(value, context)?),
            body: Box::new(owner_aware_expr(body, context)?),
        },
    })
}

fn normalize_levels_for_qa(levels: &[Level]) -> Vec<Level> {
    levels.iter().map(normalize_level_for_qa).collect()
}

fn normalize_level_for_qa(level: &Level) -> Level {
    npa_kernel::level::normalize_level(level.clone())
}

fn validate_display_scope_entry(
    entry: &MachineDisplayRenderScopeEntry,
) -> Result<(), MachineExprRendererError> {
    validate_global_ref_view_invariants(&entry.view)?;
    validate_owner_context(entry)?;
    if !display_callable_ref_matches_view(&entry.callable_ref, &entry.view) {
        return Err(MachineExprRendererError::DisplayScopeCallableRefMismatch {
            name: entry.view.name().clone(),
        });
    }
    validate_candidate_resolution(entry)
}

fn validate_global_ref_view_invariants(
    view: &MachineGlobalRefView,
) -> Result<(), MachineExprRendererError> {
    match view {
        MachineGlobalRefView::Imported {
            name,
            public_export,
            tactic_head_visible,
            ..
        } => {
            if !*public_export && *tactic_head_visible {
                return Err(MachineExprRendererError::InvalidGlobalRefViewInvariant {
                    name: name.clone(),
                    reason: "non-public imported view cannot be tactic-head-visible",
                });
            }
        }
        MachineGlobalRefView::LocalGenerated {
            export_hash,
            name,
            public_export,
            tactic_head_visible,
            ..
        } => {
            if export_hash.is_none() && (*public_export || *tactic_head_visible) {
                return Err(MachineExprRendererError::InvalidGlobalRefViewInvariant {
                    name: name.clone(),
                    reason: "current generated view cannot be public or tactic-head-visible",
                });
            }
            if !*public_export && *tactic_head_visible {
                return Err(MachineExprRendererError::InvalidGlobalRefViewInvariant {
                    name: name.clone(),
                    reason: "non-public generated view cannot be tactic-head-visible",
                });
            }
        }
        MachineGlobalRefView::CurrentModule { .. } => {}
    }
    Ok(())
}

fn validate_owner_context(
    entry: &MachineDisplayRenderScopeEntry,
) -> Result<(), MachineExprRendererError> {
    let matches = match (&entry.owner_context, &entry.view) {
        (
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: owner_module,
            },
            MachineGlobalRefView::CurrentModule { module, .. }
            | MachineGlobalRefView::LocalGenerated {
                module,
                export_hash: None,
                ..
            },
        ) => owner_module == module,
        (
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule { .. },
            MachineGlobalRefView::CurrentModule { .. }
            | MachineGlobalRefView::LocalGenerated {
                export_hash: None, ..
            },
        ) => false,
        (_, MachineGlobalRefView::Imported { .. })
        | (
            _,
            MachineGlobalRefView::LocalGenerated {
                export_hash: Some(_),
                ..
            },
        ) => true,
    };
    if matches {
        Ok(())
    } else {
        Err(MachineExprRendererError::DisplayScopeOwnerContextMismatch {
            name: entry.view.name().clone(),
        })
    }
}

fn display_callable_ref_matches_view(
    callable_ref: &MachineSurfaceCallableRef,
    view: &MachineGlobalRefView,
) -> bool {
    match (callable_ref, view) {
        (
            MachineSurfaceCallableRef::Imported {
                module: callable_module,
                name: callable_name,
                export_hash: callable_export_hash,
                decl_interface_hash: callable_decl_hash,
            },
            MachineGlobalRefView::Imported {
                module,
                name,
                export_hash,
                decl_interface_hash,
                ..
            },
        ) => {
            callable_module == module
                && callable_name == name
                && callable_export_hash == export_hash
                && callable_decl_hash == decl_interface_hash
        }
        (
            MachineSurfaceCallableRef::CurrentModule {
                module: callable_module,
                name: callable_name,
                source_index: callable_source_index,
                decl_interface_hash: callable_decl_hash,
            },
            MachineGlobalRefView::CurrentModule {
                module,
                name,
                source_index,
                decl_interface_hash,
            },
        ) => {
            callable_module == module
                && callable_name == name
                && callable_source_index == source_index
                && callable_decl_hash == decl_interface_hash
        }
        (
            MachineSurfaceCallableRef::Imported {
                module: callable_module,
                name: callable_name,
                export_hash: callable_export_hash,
                decl_interface_hash: callable_decl_hash,
            },
            MachineGlobalRefView::LocalGenerated {
                module,
                export_hash: Some(export_hash),
                name,
                decl_interface_hash,
                ..
            },
        ) => {
            callable_module == module
                && callable_name == name
                && callable_export_hash == export_hash
                && callable_decl_hash == decl_interface_hash
        }
        (
            MachineSurfaceCallableRef::CurrentGenerated {
                module: callable_module,
                name: callable_name,
                decl_interface_hash: callable_decl_hash,
                ..
            },
            MachineGlobalRefView::LocalGenerated {
                module,
                export_hash: None,
                name,
                decl_interface_hash,
                ..
            },
        ) => {
            callable_module == module
                && callable_name == name
                && callable_decl_hash == decl_interface_hash
        }
        _ => false,
    }
}

fn validate_candidate_resolution(
    entry: &MachineDisplayRenderScopeEntry,
) -> Result<(), MachineExprRendererError> {
    let Some(candidate_resolution) = &entry.candidate_resolution else {
        return match entry.callable_ref {
            MachineSurfaceCallableRef::CurrentGenerated { .. } => Err(
                MachineExprRendererError::DisplayScopeCandidateResolutionRequired {
                    name: entry.name.clone(),
                },
            ),
            _ => Ok(()),
        };
    };
    if frontend_entry_matches_callable_ref(candidate_resolution, &entry.callable_ref) {
        Ok(())
    } else {
        Err(
            MachineExprRendererError::DisplayScopeCandidateResolutionMismatch {
                name: entry.name.clone(),
            },
        )
    }
}

fn validate_frontend_round_trip_resolution(
    checked: &MachineTermCheckResult,
    render_context: &MachineExprRendererContext<'_>,
    elab_context: &MachineTermElabContext,
    display_import_index_offset: u32,
) -> Result<(), MachineExprRendererError> {
    for constant in &checked.constants {
        let (display_index, display_entry) =
            resolve_global_name_with_index(&constant.name.as_dotted(), render_context)?;
        if display_entry.view.decl_interface_hash() != constant.decl_interface_hash {
            return Err(MachineExprRendererError::QAGlobalResolutionMismatch {
                name: constant.name.clone(),
            });
        }
        validate_candidate_resolution_in_qa_context(display_entry, elab_context)?;
        let mut matching = elab_context.global_scope_entries().iter().filter(|entry| {
            entry.name() == &constant.name
                && *entry.decl_interface_hash() == constant.decl_interface_hash
        });
        let Some(frontend_entry) = matching.next() else {
            return Err(MachineExprRendererError::QAGlobalResolutionMissing {
                name: constant.name.clone(),
                decl_interface_hash: constant.decl_interface_hash,
            });
        };
        if matching.next().is_some() {
            return Err(MachineExprRendererError::QAGlobalResolutionAmbiguous {
                name: constant.name.clone(),
                decl_interface_hash: constant.decl_interface_hash,
            });
        }
        let expected_frontend_entry = expected_frontend_entry_for_display_entry(
            display_entry,
            display_index,
            display_import_index_offset,
            frontend_entry,
            elab_context,
        )?;
        if frontend_entry != &expected_frontend_entry {
            return Err(MachineExprRendererError::QAGlobalResolutionMismatch {
                name: constant.name.clone(),
            });
        }
    }
    Ok(())
}

fn validate_candidate_resolution_in_qa_context(
    display_entry: &MachineDisplayRenderScopeEntry,
    elab_context: &MachineTermElabContext,
) -> Result<(), MachineExprRendererError> {
    let Some(candidate_resolution) = &display_entry.candidate_resolution else {
        return Ok(());
    };
    if frontend_entry_matches_callable_ref_in_context(
        candidate_resolution,
        &display_entry.callable_ref,
        elab_context,
    ) {
        Ok(())
    } else {
        Err(
            MachineExprRendererError::DisplayScopeCandidateResolutionMismatch {
                name: display_entry.name.clone(),
            },
        )
    }
}

fn validate_display_scope_against_qa_context(
    render_context: &MachineExprRendererContext<'_>,
    elab_context: &MachineTermElabContext,
) -> Result<(), MachineExprRendererError> {
    for entry in render_context.display_scope.entries() {
        if !display_entry_is_backed_by_qa_context(entry, elab_context) {
            return Err(MachineExprRendererError::DisplayScopeOwnerContextMismatch {
                name: entry.name.clone(),
            });
        }
    }
    Ok(())
}

fn display_entry_is_backed_by_qa_context(
    entry: &MachineDisplayRenderScopeEntry,
    elab_context: &MachineTermElabContext,
) -> bool {
    match &entry.view {
        MachineGlobalRefView::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
            public_export,
            tactic_head_visible,
        } => {
            let direct_tactic_visible = elab_context.direct_import_export_matches(
                module,
                export_hash,
                name,
                decl_interface_hash,
            );
            let decl_loaded =
                elab_context.import_decl_loaded_in_kernel_env(module, export_hash, name);
            match &entry.owner_context {
                MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                    module: owner_module,
                } => {
                    *public_export
                        && decl_loaded
                        && *tactic_head_visible == direct_tactic_visible
                        && direct_tactic_visible
                        && elab_context.current_module_is(owner_module)
                }
                MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                    owner_module,
                    owner_export_hash,
                } if owner_module == module && owner_export_hash == export_hash => {
                    decl_loaded
                        && elab_context.verified_import_decl_matches(
                            module,
                            export_hash,
                            name,
                            decl_interface_hash,
                            *public_export,
                        )
                        && *tactic_head_visible == (*public_export && direct_tactic_visible)
                }
                MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                    owner_module,
                    owner_export_hash,
                } => {
                    *public_export
                        && decl_loaded
                        && *tactic_head_visible == direct_tactic_visible
                        && elab_context.verified_import_depends_on_export(
                            owner_module,
                            owner_export_hash,
                            module,
                            export_hash,
                            name,
                            decl_interface_hash,
                        )
                }
            }
        }
        MachineGlobalRefView::LocalGenerated {
            module,
            export_hash: Some(export_hash),
            parent_name,
            name,
            parent_decl_interface_hash,
            decl_interface_hash,
            public_export,
            tactic_head_visible,
        } => {
            let direct_tactic_visible = elab_context.direct_import_generated_export_matches(
                module,
                export_hash,
                parent_name,
                name,
                parent_decl_interface_hash,
                decl_interface_hash,
            );
            let decl_loaded =
                elab_context.import_decl_loaded_in_kernel_env(module, export_hash, name);
            match &entry.owner_context {
                MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                    module: owner_module,
                } => {
                    *public_export
                        && decl_loaded
                        && *tactic_head_visible == direct_tactic_visible
                        && direct_tactic_visible
                        && elab_context.current_module_is(owner_module)
                }
                MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                    owner_module,
                    owner_export_hash,
                } if owner_module == module && owner_export_hash == export_hash => {
                    decl_loaded
                        && parent_decl_interface_hash == decl_interface_hash
                        && elab_context.verified_import_generated_decl_matches(
                            module,
                            export_hash,
                            parent_name,
                            name,
                            decl_interface_hash,
                            *public_export,
                        )
                        && *tactic_head_visible == (*public_export && direct_tactic_visible)
                }
                MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                    owner_module,
                    owner_export_hash,
                } => {
                    *public_export
                        && decl_loaded
                        && *tactic_head_visible == direct_tactic_visible
                        && elab_context.verified_import_depends_on_export(
                            owner_module,
                            owner_export_hash,
                            module,
                            export_hash,
                            name,
                            decl_interface_hash,
                        )
                }
            }
        }
        MachineGlobalRefView::CurrentModule {
            module,
            name,
            source_index,
            decl_interface_hash,
            ..
        } => elab_context.current_module_entry_matches(
            module,
            name,
            *source_index,
            decl_interface_hash,
        ),
        MachineGlobalRefView::LocalGenerated {
            module,
            export_hash: None,
            parent_name,
            name,
            parent_decl_interface_hash,
            decl_interface_hash,
            ..
        } => {
            let Some(MachineGlobalScopeEntry::CurrentGenerated {
                name: candidate_name,
                parent_source_index,
                decl_interface_hash: candidate_decl_interface_hash,
            }) = &entry.candidate_resolution
            else {
                return false;
            };
            candidate_name == name
                && candidate_decl_interface_hash == decl_interface_hash
                && elab_context.current_generated_entry_matches(
                    module,
                    name,
                    *parent_source_index,
                    decl_interface_hash,
                )
                && elab_context.current_module_entry_matches(
                    module,
                    parent_name,
                    *parent_source_index,
                    parent_decl_interface_hash,
                )
        }
    }
}

fn expected_frontend_entry_for_display_entry(
    display_entry: &MachineDisplayRenderScopeEntry,
    display_index: usize,
    display_import_index_offset: u32,
    frontend_entry: &MachineGlobalScopeEntry,
    elab_context: &MachineTermElabContext,
) -> Result<MachineGlobalScopeEntry, MachineExprRendererError> {
    if let Some(candidate_resolution) = &display_entry.candidate_resolution {
        return Ok(candidate_resolution.clone());
    }
    if frontend_entry_matches_callable_ref_in_context(
        frontend_entry,
        &display_entry.callable_ref,
        elab_context,
    ) {
        return Ok(frontend_entry.clone());
    }
    display_entry_frontend_projection(display_entry, display_index, display_import_index_offset)
}

fn display_scope_frontend_projection(
    context: &MachineExprRendererContext<'_>,
    display_import_index_offset: u32,
) -> Result<Vec<MachineGlobalScopeEntry>, MachineExprRendererError> {
    context
        .display_scope
        .entries()
        .iter()
        .enumerate()
        .map(|(index, entry)| {
            entry.candidate_resolution.clone().map_or_else(
                || display_entry_frontend_projection(entry, index, display_import_index_offset),
                Ok,
            )
        })
        .collect()
}

fn display_entry_frontend_projection(
    entry: &MachineDisplayRenderScopeEntry,
    index: usize,
    import_index_offset: u32,
) -> Result<MachineGlobalScopeEntry, MachineExprRendererError> {
    match &entry.view {
        MachineGlobalRefView::Imported {
            name,
            decl_interface_hash,
            ..
        }
        | MachineGlobalRefView::LocalGenerated {
            export_hash: Some(_),
            name,
            decl_interface_hash,
            ..
        } => Ok(MachineGlobalScopeEntry::Imported {
            name: name.clone(),
            import_index: display_projection_import_index(index, import_index_offset)?,
            decl_interface_hash: *decl_interface_hash,
        }),
        MachineGlobalRefView::CurrentModule {
            name,
            source_index,
            decl_interface_hash,
            ..
        } => Ok(MachineGlobalScopeEntry::CurrentModule {
            name: name.clone(),
            source_index: *source_index,
            decl_interface_hash: *decl_interface_hash,
        }),
        MachineGlobalRefView::LocalGenerated {
            export_hash: None, ..
        } => Err(
            MachineExprRendererError::DisplayScopeCandidateResolutionRequired {
                name: entry.name.clone(),
            },
        ),
    }
}

fn display_projection_import_index_offset(
    elab_context: &MachineTermElabContext,
) -> Result<u32, MachineExprRendererError> {
    let max_existing = elab_context
        .global_scope_entries()
        .iter()
        .filter_map(|entry| match entry {
            MachineGlobalScopeEntry::Imported { import_index, .. } => Some(*import_index),
            MachineGlobalScopeEntry::CurrentModule { .. }
            | MachineGlobalScopeEntry::CurrentGenerated { .. } => None,
        })
        .max();
    max_existing.map_or(Ok(0), |import_index| {
        import_index
            .checked_add(1)
            .ok_or(MachineExprRendererError::ExpressionTooLarge)
    })
}

fn display_projection_import_index(
    index: usize,
    import_index_offset: u32,
) -> Result<u32, MachineExprRendererError> {
    let index = u32::try_from(index).map_err(|_| MachineExprRendererError::ExpressionTooLarge)?;
    import_index_offset
        .checked_add(index)
        .ok_or(MachineExprRendererError::ExpressionTooLarge)
}

fn frontend_entry_matches_callable_ref(
    frontend_entry: &MachineGlobalScopeEntry,
    callable_ref: &MachineSurfaceCallableRef,
) -> bool {
    match (frontend_entry, callable_ref) {
        (
            MachineGlobalScopeEntry::Imported {
                name,
                decl_interface_hash,
                ..
            },
            MachineSurfaceCallableRef::Imported {
                name: callable_name,
                decl_interface_hash: callable_decl_hash,
                ..
            },
        ) => name == callable_name && decl_interface_hash == callable_decl_hash,
        (
            MachineGlobalScopeEntry::CurrentModule {
                name,
                source_index,
                decl_interface_hash,
            },
            MachineSurfaceCallableRef::CurrentModule {
                name: callable_name,
                source_index: callable_source_index,
                decl_interface_hash: callable_decl_hash,
                ..
            },
        ) => {
            name == callable_name
                && source_index == callable_source_index
                && decl_interface_hash == callable_decl_hash
        }
        (
            MachineGlobalScopeEntry::CurrentGenerated {
                name,
                parent_source_index,
                decl_interface_hash,
            },
            MachineSurfaceCallableRef::CurrentGenerated {
                name: callable_name,
                parent_source_index: callable_parent_source_index,
                decl_interface_hash: callable_decl_hash,
                ..
            },
        ) => {
            name == callable_name
                && parent_source_index == callable_parent_source_index
                && decl_interface_hash == callable_decl_hash
        }
        _ => false,
    }
}

fn frontend_entry_matches_callable_ref_in_context(
    frontend_entry: &MachineGlobalScopeEntry,
    callable_ref: &MachineSurfaceCallableRef,
    elab_context: &MachineTermElabContext,
) -> bool {
    if !frontend_entry_matches_callable_ref(frontend_entry, callable_ref) {
        return false;
    }
    match (frontend_entry, callable_ref) {
        (
            MachineGlobalScopeEntry::Imported { import_index, .. },
            MachineSurfaceCallableRef::Imported {
                module,
                export_hash,
                ..
            },
        ) => elab_context
            .direct_import_identity(*import_index)
            .is_some_and(|(direct_module, direct_export_hash)| {
                direct_module == module && direct_export_hash == *export_hash
            }),
        _ => true,
    }
}

fn validate_base_context(
    context: &MachineExprRendererContext<'_>,
) -> Result<(), MachineExprRendererError> {
    let mut seen = BTreeSet::new();
    for local in context.base_context {
        validate_local_name(&local.name)?;
        if context.display_scope.global_roots.contains(&local.name) {
            return Err(MachineExprRendererError::LocalNameShadowsGlobalRoot {
                name: local.name.clone(),
            });
        }
        if !seen.insert(local.name.clone()) {
            return Err(MachineExprRendererError::LocalNameInvalid {
                name: local.name.clone(),
            });
        }
    }
    for param in context.universe_params {
        validate_universe_param(param)?;
    }
    Ok(())
}

fn validate_universe_param(name: &str) -> Result<(), MachineExprRendererError> {
    if is_machine_local_name(name) {
        Ok(())
    } else {
        Err(MachineExprRendererError::UniverseParamNotRenderable {
            name: name.to_owned(),
        })
    }
}

fn validate_local_name(name: &str) -> Result<(), MachineExprRendererError> {
    if is_machine_local_name(name) {
        Ok(())
    } else {
        Err(MachineExprRendererError::LocalNameInvalid {
            name: name.to_owned(),
        })
    }
}

fn occupied_local_names(
    binder_stack: &[String],
    context: &MachineExprRendererContext<'_>,
) -> BTreeSet<String> {
    binder_stack
        .iter()
        .cloned()
        .chain(context.base_context.iter().map(|local| local.name.clone()))
        .chain(context.display_scope.global_roots.iter().cloned())
        .collect()
}

fn is_usable_local_name(name: &str, occupied: &BTreeSet<String>) -> bool {
    is_machine_local_name(name) && !occupied.contains(name)
}

fn is_machine_local_name(value: &str) -> bool {
    if value.is_empty() || value.len() > 64 || is_machine_surface_reserved(value) {
        return false;
    }
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
}

fn is_machine_surface_reserved(value: &str) -> bool {
    matches!(
        value,
        "import"
            | "def"
            | "theorem"
            | "fun"
            | "forall"
            | "let"
            | "in"
            | "Prop"
            | "Type"
            | "Sort"
            | "open"
            | "namespace"
            | "match"
            | "with"
            | "notation"
            | "infix"
            | "infixl"
            | "infixr"
            | "axiom"
            | "inductive"
            | "succ"
            | "max"
            | "imax"
    )
}

fn render_kernel_core_level(level: &Level) -> String {
    match level {
        Level::Zero => "0".to_owned(),
        Level::Succ(inner) => format!("succ({})", render_kernel_core_level(inner)),
        Level::Max(lhs, rhs) => format!(
            "max({}, {})",
            render_kernel_core_level(lhs),
            render_kernel_core_level(rhs)
        ),
        Level::IMax(lhs, rhs) => format!(
            "imax({}, {})",
            render_kernel_core_level(lhs),
            render_kernel_core_level(rhs)
        ),
        Level::Param(name) => format!("param({name})"),
    }
}

fn render_level(
    level: &Level,
    universe_params: &[String],
) -> Result<String, MachineExprRendererError> {
    if let Some(n) = closed_level_numeral(level) {
        return Ok(n.to_string());
    }
    match level {
        Level::Zero => Ok("0".to_owned()),
        Level::Succ(inner) => Ok(format!("succ {}", render_level(inner, universe_params)?)),
        Level::Max(lhs, rhs) => Ok(format!(
            "max {} {}",
            render_level(lhs, universe_params)?,
            render_level(rhs, universe_params)?
        )),
        Level::IMax(lhs, rhs) => Ok(format!(
            "imax {} {}",
            render_level(lhs, universe_params)?,
            render_level(rhs, universe_params)?
        )),
        Level::Param(name) => {
            if !universe_params.iter().any(|param| param == name) {
                return Err(MachineExprRendererError::UnknownUniverseParam { name: name.clone() });
            }
            validate_universe_param(name)?;
            Ok(name.clone())
        }
    }
}

fn closed_level_numeral(level: &Level) -> Option<u64> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(inner) => closed_level_numeral(inner)?.checked_add(1),
        _ => None,
    }
}

fn flatten_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(func, arg) = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();
    (head, args)
}

fn parenthesize(source: String) -> String {
    format!("({source})")
}

fn syntactic_head(expr: &Expr) -> Option<&str> {
    let mut current = expr;
    while let Expr::App(func, _) = current {
        current = func;
    }
    match current {
        Expr::Const { name, .. } => Some(name.as_str()),
        _ => None,
    }
}

fn syntactic_head_name(expr: &Expr) -> Option<Name> {
    let mut current = expr;
    while let Expr::App(func, _) = current {
        current = func;
    }
    match current {
        Expr::Const { name, .. } => Some(Name::from_dotted(name)),
        _ => None,
    }
}

fn resolve_global_name<'a>(
    name: &str,
    context: &'a MachineExprRendererContext<'_>,
) -> Result<&'a MachineDisplayRenderScopeEntry, MachineExprRendererError> {
    context.display_scope.entry_for_name(name).ok_or_else(|| {
        MachineExprRendererError::GlobalNameMissingFromDisplayScope {
            name: name.to_owned(),
        }
    })
}

fn resolve_global_name_with_index<'a>(
    name: &str,
    context: &'a MachineExprRendererContext<'_>,
) -> Result<(usize, &'a MachineDisplayRenderScopeEntry), MachineExprRendererError> {
    context
        .display_scope
        .entries()
        .iter()
        .enumerate()
        .find(|(_, entry)| entry.name.as_dotted() == name)
        .ok_or_else(
            || MachineExprRendererError::GlobalNameMissingFromDisplayScope {
                name: name.to_owned(),
            },
        )
}

fn resolve_global_view<'a>(
    name: &str,
    context: &'a MachineExprRendererContext<'_>,
) -> Result<&'a MachineDisplayRenderScopeEntry, MachineExprRendererError> {
    resolve_global_name(name, context)
}

fn collect_constants(
    expr: &Expr,
    context: &MachineExprRendererContext<'_>,
    out: &mut BTreeSet<MachineGlobalRefView>,
) -> Result<(), MachineExprRendererError> {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            out.insert(resolve_global_view(name, context)?.view.clone());
        }
        Expr::App(func, arg) => {
            collect_constants(func, context, out)?;
            collect_constants(arg, context, out)?;
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_constants(ty, context, out)?;
            collect_constants(body, context, out)?;
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_constants(ty, context, out)?;
            collect_constants(value, context, out)?;
            collect_constants(body, context, out)?;
        }
    }
    Ok(())
}

fn collect_constant_names(expr: &Expr, out: &mut BTreeSet<Name>) {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            out.insert(Name::from_dotted(name));
        }
        Expr::App(func, arg) => {
            collect_constant_names(func, out);
            collect_constant_names(arg, out);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_constant_names(ty, out);
            collect_constant_names(body, out);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_constant_names(ty, out);
            collect_constant_names(value, out);
            collect_constant_names(body, out);
        }
    }
}

fn free_locals(
    expr: &Expr,
    base_context_len: usize,
) -> Result<Vec<LocalId>, MachineExprRendererError> {
    let mut out = BTreeSet::new();
    collect_free_locals(expr, base_context_len, 0, &mut out)?;
    Ok(out.into_iter().map(LocalId).collect())
}

fn collect_free_locals(
    expr: &Expr,
    base_context_len: usize,
    binder_depth: usize,
    out: &mut BTreeSet<u32>,
) -> Result<(), MachineExprRendererError> {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => {}
        Expr::BVar(index) => {
            let index = *index as usize;
            if index >= binder_depth {
                let base_index_from_inner = index - binder_depth;
                let Some(base_index) = base_context_len.checked_sub(base_index_from_inner + 1)
                else {
                    return Err(MachineExprRendererError::BVarOutOfScope {
                        index: index as u32,
                        binder_depth,
                        base_context_len,
                    });
                };
                out.insert(base_index as u32);
            }
        }
        Expr::App(func, arg) => {
            collect_free_locals(func, base_context_len, binder_depth, out)?;
            collect_free_locals(arg, base_context_len, binder_depth, out)?;
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_free_locals(ty, base_context_len, binder_depth, out)?;
            collect_free_locals(body, base_context_len, binder_depth + 1, out)?;
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_free_locals(ty, base_context_len, binder_depth, out)?;
            collect_free_locals(value, base_context_len, binder_depth, out)?;
            collect_free_locals(body, base_context_len, binder_depth + 1, out)?;
        }
    }
    Ok(())
}

fn expr_size(expr: &Expr) -> Result<u32, MachineExprRendererError> {
    let mut size = 0u32;
    count_expr_nodes(expr, &mut size)?;
    Ok(size)
}

fn count_expr_nodes(expr: &Expr, size: &mut u32) -> Result<(), MachineExprRendererError> {
    *size = size
        .checked_add(1)
        .ok_or(MachineExprRendererError::ExpressionTooLarge)?;
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => {}
        Expr::App(func, arg) => {
            count_expr_nodes(func, size)?;
            count_expr_nodes(arg, size)?;
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            count_expr_nodes(ty, size)?;
            count_expr_nodes(body, size)?;
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            count_expr_nodes(ty, size)?;
            count_expr_nodes(value, size)?;
            count_expr_nodes(body, size)?;
        }
    }
    Ok(())
}

fn hash_core_expr(expr: &Expr) -> Hash {
    npa_tactic::core_expr_hash(expr)
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_bool(out: &mut Vec<u8>, value: bool) {
    out.push(if value { 0x01 } else { 0x00 });
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_frontend::{
        MachineCheckedCurrentDecl, MachineSurfaceCallableInterfaceEntry, MachineSurfaceCallableRef,
    };
    use npa_kernel::{ConstructorDecl, Decl, InductiveDecl};

    fn h(byte: u8) -> Hash {
        [byte; 32]
    }

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn raw_max_zero_zero() -> Level {
        Level::Max(Box::new(Level::zero()), Box::new(Level::zero()))
    }

    fn local(name: &str, ty: Expr) -> MachineLocalDecl {
        MachineLocalDecl {
            name: name.to_owned(),
            ty,
            value: None,
        }
    }

    fn imported_entry(
        module: &str,
        name: &str,
        export_hash: Hash,
        decl_hash: Hash,
    ) -> MachineDisplayRenderScopeEntry {
        let module = Name::from_dotted(module);
        let name = Name::from_dotted(name);
        MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: module.clone(),
                name: name.clone(),
                export_hash,
                decl_interface_hash: decl_hash,
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: module.clone(),
                owner_export_hash: export_hash,
            },
            MachineSurfaceCallableRef::Imported {
                module,
                name,
                export_hash,
                decl_interface_hash: decl_hash,
            },
        )
    }

    fn current_axiom(name: &str, decl_interface_hash: Hash, ty: Expr) -> MachineCheckedCurrentDecl {
        MachineCheckedCurrentDecl {
            name: Name::from_dotted(name),
            source_index: 0,
            decl_interface_hash,
            decl: Decl::Axiom {
                name: name.to_owned(),
                universe_params: Vec::new(),
                ty,
            },
        }
    }

    fn verified_core_module(
        module: npa_cert::CoreModule,
        imports: &[npa_cert::VerifiedModule],
    ) -> npa_cert::VerifiedModule {
        let cert = npa_cert::build_module_cert(module, imports).unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();
        let mut session = npa_cert::VerifierSession::new();
        for import in imports {
            session.register_verified_module(import.clone());
        }
        npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
            .unwrap()
    }

    fn unary_expr() -> Expr {
        Expr::konst("Unary", Vec::new())
    }

    fn unary_import() -> npa_cert::VerifiedModule {
        verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Test.Unary"),
                declarations: vec![Decl::Inductive {
                    name: "Unary".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                    data: Box::new(InductiveDecl::new(
                        "Unary",
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                        Level::succ(Level::zero()),
                        vec![ConstructorDecl::new("Unary.zero", unary_expr())],
                        None,
                    )),
                }],
            },
            &[],
        )
    }

    fn hidden_thing_import() -> npa_cert::VerifiedModule {
        verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Hidden"),
                declarations: vec![Decl::Axiom {
                    name: "Hidden.Thing".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        )
    }

    fn private_hidden_import() -> npa_frontend::VerifiedImport {
        npa_frontend::VerifiedImport {
            module: Name::from_dotted("Hidden"),
            export_hash: h(70),
            certificate_hash: None,
            exports: vec![npa_frontend::VerifiedExport {
                name: Name::from_dotted("Hidden.Public"),
                universe_params: Vec::new(),
                ty: type0(),
                decl_interface_hash: h(71),
            }],
            decl_interface_hashes: BTreeMap::from([
                (Name::from_dotted("Hidden.Public"), h(71)),
                (Name::from_dotted("Hidden.Private"), h(72)),
            ]),
            kernel_decls: vec![
                Decl::Axiom {
                    name: "Hidden.Public".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                },
                Decl::Axiom {
                    name: "Hidden.Private".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                },
            ],
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    fn private_unary_import() -> npa_frontend::VerifiedImport {
        npa_frontend::VerifiedImport {
            module: Name::from_dotted("Test.Unary"),
            export_hash: h(80),
            certificate_hash: None,
            exports: Vec::new(),
            decl_interface_hashes: BTreeMap::from([(Name::from_dotted("Unary"), h(81))]),
            kernel_decls: vec![Decl::Inductive {
                name: "Unary".to_owned(),
                universe_params: Vec::new(),
                ty: type0(),
                data: Box::new(InductiveDecl::new(
                    "Unary",
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    Level::succ(Level::zero()),
                    vec![ConstructorDecl::new("Unary.zero", unary_expr())],
                    None,
                )),
            }],
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    fn direct_using_hidden_import(hidden: &npa_cert::VerifiedModule) -> npa_cert::VerifiedModule {
        verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Direct"),
                declarations: vec![Decl::Axiom {
                    name: "Direct.use_hidden".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Hidden.Thing", Vec::new()),
                }],
            },
            std::slice::from_ref(hidden),
        )
    }

    fn shared_foo_import(module: &str) -> npa_cert::VerifiedModule {
        verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted(module),
                declarations: vec![Decl::Axiom {
                    name: "Shared.Foo".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        )
    }

    fn direct_using_shared_import(hidden: &npa_cert::VerifiedModule) -> npa_cert::VerifiedModule {
        verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Direct"),
                declarations: vec![Decl::Axiom {
                    name: "Direct.use_shared".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Shared.Foo", Vec::new()),
                }],
            },
            std::slice::from_ref(hidden),
        )
    }

    fn export_decl_hash(module: &npa_cert::VerifiedModule, name: &str) -> Hash {
        let name = Name::from_dotted(name);
        module
            .export_block()
            .iter()
            .find_map(|entry| {
                if module.name_table()[entry.name] == name {
                    Some(entry.decl_interface_hash)
                } else {
                    None
                }
            })
            .unwrap()
    }

    #[test]
    fn renders_binders_with_fresh_machine_names() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let expr = Expr::pi("_", prop(), Expr::bvar(0));

        let view = render_machine_expr_view(&expr, &context).unwrap();

        assert_eq!(view.machine, "forall (x : Prop), x");
        assert_eq!(view.free_locals, Vec::<LocalId>::new());
        assert_eq!(view.size, 3);
    }

    #[test]
    fn fresh_binder_name_searches_until_machine_name_exhaustion() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let mut base = Vec::with_capacity(100_002);
        base.push(local("x", prop()));
        for suffix in 0..=100_000 {
            base.push(local(&format!("x_{suffix}"), prop()));
        }
        let context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };
        let renderer = MachineExprRenderer::new(&context);

        assert_eq!(
            renderer.fresh_binder_name("x").unwrap(),
            "x_100001".to_owned()
        );
    }

    #[test]
    fn renders_base_context_locals_and_free_local_ids() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let base = vec![local("A", type0()), local("n", Expr::bvar(0))];
        let context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };

        let view = render_machine_expr_view(&Expr::bvar(0), &context).unwrap();

        assert_eq!(view.machine, "n");
        assert_eq!(view.free_locals, vec![LocalId(1)]);
    }

    #[test]
    fn renders_global_application_with_explicit_head_marker_from_callable_table() {
        let eq_refl = imported_entry("Std.Logic", "Eq.refl", h(1), h(2));
        let nat = imported_entry("Std.Nat", "Nat", h(3), h(4));
        let scope = MachineDisplayRenderScope::from_entries(vec![eq_refl.clone(), nat]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::from_entries(vec![
            MachineSurfaceCallableInterfaceEntry::new(
                eq_refl.callable_ref.clone(),
                vec![
                    MachineCallableBinderVisibility::Implicit,
                    MachineCallableBinderVisibility::Explicit,
                ],
            ),
        ])
        .unwrap();
        let base = vec![local("n", Expr::konst("Nat", Vec::new()))];
        let context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };
        let expr = Expr::apps(
            Expr::konst("Eq.refl", vec![Level::succ(Level::zero())]),
            vec![Expr::konst("Nat", Vec::new()), Expr::bvar(0)],
        );

        let view = render_machine_expr_view(&expr, &context).unwrap();

        assert_eq!(view.machine, "@Eq.refl.{1} Nat n");
        assert_eq!(view.head, Some(eq_refl.view));
        assert_eq!(view.free_locals, vec![LocalId(0)]);
        assert_eq!(view.constants.len(), 2);
    }

    #[test]
    fn rejects_display_scope_entry_with_mismatched_callable_ref() {
        let mut entry = imported_entry("Std.Logic", "Eq.refl", h(1), h(2));
        entry.callable_ref = MachineSurfaceCallableRef::Imported {
            module: Name::from_dotted("Std.Logic"),
            name: Name::from_dotted("Eq.refl"),
            export_hash: h(1),
            decl_interface_hash: h(9),
        };

        let err = MachineDisplayRenderScope::from_entries(vec![entry])
            .expect_err("display scope must reject mismatched callable refs");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeCallableRefMismatch { .. }
        ));
    }

    #[test]
    fn rejects_invalid_imported_tactic_visibility_combo() {
        let module = Name::from_dotted("Hidden.Module");
        let name = Name::from_dotted("Hidden.Foo");
        let entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: module.clone(),
                name: name.clone(),
                export_hash: h(1),
                decl_interface_hash: h(2),
                public_export: false,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: module.clone(),
                owner_export_hash: h(1),
            },
            MachineSurfaceCallableRef::Imported {
                module,
                name,
                export_hash: h(1),
                decl_interface_hash: h(2),
            },
        );

        let err = MachineDisplayRenderScope::from_entries(vec![entry])
            .expect_err("non-public imported view cannot be tactic-head-visible");

        assert!(matches!(
            err,
            MachineExprRendererError::InvalidGlobalRefViewInvariant { .. }
        ));
    }

    #[test]
    fn rejects_display_scope_entry_with_mismatched_owner_context() {
        let module = Name::from_dotted("Root");
        let name = Name::from_dotted("Root.id");
        let entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: module.clone(),
                name: name.clone(),
                decl_interface_hash: h(2),
                source_index: 0,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: Name::from_dotted("Std.Logic"),
                owner_export_hash: h(1),
            },
            MachineSurfaceCallableRef::CurrentModule {
                module,
                name,
                source_index: 0,
                decl_interface_hash: h(2),
            },
        );

        let err = MachineDisplayRenderScope::from_entries(vec![entry])
            .expect_err("current-module display refs must use the current-session owner context");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn accepts_current_session_owner_for_direct_imported_display_ref() {
        let module = Name::from_dotted("Std.Logic");
        let name = Name::from_dotted("Eq.refl");
        let entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: module.clone(),
                name: name.clone(),
                export_hash: h(1),
                decl_interface_hash: h(2),
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: Name::from_dotted("Root"),
            },
            MachineSurfaceCallableRef::Imported {
                module,
                name,
                export_hash: h(1),
                decl_interface_hash: h(2),
            },
        );

        MachineDisplayRenderScope::from_entries(vec![entry])
            .expect("current sessions can render direct imported declarations");
    }

    #[test]
    fn rejects_current_generated_without_candidate_resolution() {
        let module = Name::from_dotted("Root");
        let parent_name = Name::from_dotted("Root.I");
        let generated_name = Name::from_dotted("Root.I.mk");
        let entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::LocalGenerated {
                module: module.clone(),
                export_hash: None,
                parent_name,
                name: generated_name.clone(),
                parent_decl_interface_hash: h(2),
                decl_interface_hash: h(2),
                public_export: false,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: module.clone(),
            },
            MachineSurfaceCallableRef::CurrentGenerated {
                module,
                name: generated_name,
                parent_source_index: 0,
                decl_interface_hash: h(2),
            },
        );

        let err = MachineDisplayRenderScope::from_entries(vec![entry])
            .expect_err("current generated callable needs source-indexed candidate resolution");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeCandidateResolutionRequired { .. }
        ));
    }

    #[test]
    fn rejects_global_roots_shadowed_by_base_locals() {
        let nat = imported_entry("Std.Nat", "Nat", h(3), h(4));
        let scope = MachineDisplayRenderScope::from_entries(vec![nat]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let base = vec![local("Nat", type0())];
        let context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };

        let err = render_machine_expr_view(&Expr::konst("Nat", Vec::new()), &context)
            .expect_err("global root shadowing must be rejected");

        assert!(matches!(
            err,
            MachineExprRendererError::LocalNameShadowsGlobalRoot { .. }
        ));
    }

    #[test]
    fn rejects_candidate_only_global_roots_shadowed_by_base_locals() {
        let scope = MachineDisplayRenderScope::empty()
            .with_candidate_global_roots(["Nat".to_owned()])
            .unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let base = vec![local("Nat", type0())];
        let context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };

        let err = render_machine_expr_view(&Expr::bvar(0), &context)
            .expect_err("candidate-only global roots must participate in local collision checks");

        assert!(matches!(
            err,
            MachineExprRendererError::LocalNameShadowsGlobalRoot { .. }
        ));
    }

    #[test]
    fn qa_round_trips_local_expression_through_frontend_elaboration() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let base = vec![local("A", type0())];
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules(&[], &[], base.clone(), Vec::new())
                .unwrap();
        let expr = Expr::pi("x", Expr::bvar(0), Expr::bvar(1));

        renderer_qa_round_trip(&expr, &render_context, &elab_context, &type0()).unwrap();
    }

    #[test]
    fn qa_rejects_elab_context_with_stale_base_context() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let base = vec![local("A", type0())];
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &base,
            universe_params: &[],
        };
        let stale_base = vec![local("B", type0())];
        let elab_context =
            MachineTermElabContext::from_verified_modules(&[], &[], stale_base, Vec::new())
                .unwrap();

        let err = renderer_qa_round_trip(&Expr::bvar(0), &render_context, &elab_context, &type0())
            .expect_err("renderer QA must use the same base context as rendering");

        assert_eq!(err, MachineExprRendererError::QAContextBaseContextMismatch);
    }

    #[test]
    fn qa_rejects_elab_context_with_stale_universe_params() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let renderer_params = vec!["u".to_owned()];
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &renderer_params,
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            &[],
            &[],
            Vec::new(),
            vec!["v".to_owned()],
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::sort(Level::param("u")),
            &render_context,
            &elab_context,
            &Expr::sort(Level::succ(Level::param("u"))),
        )
        .expect_err("renderer QA must use the same universe params as rendering");

        assert_eq!(
            err,
            MachineExprRendererError::QAContextUniverseParamMismatch
        );
    }

    #[test]
    fn qa_round_trips_levels_after_frontend_normalization() {
        let scope = MachineDisplayRenderScope::empty();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules(&[], &[], Vec::new(), Vec::new())
                .unwrap();

        renderer_qa_round_trip(
            &Expr::sort(raw_max_zero_zero()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect("renderer QA should compare levels after frontend normalization");
    }

    #[test]
    fn qa_round_trips_constant_levels_after_frontend_normalization() {
        let module = Name::from_dotted("Root");
        let name = Name::from_dotted("Root.A");
        let decl_hash = h(7);
        let callable_ref = MachineSurfaceCallableRef::CurrentModule {
            module: module.clone(),
            name: name.clone(),
            source_index: 0,
            decl_interface_hash: decl_hash,
        };
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: module.clone(),
                name: name.clone(),
                decl_interface_hash: decl_hash,
                source_index: 0,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: module.clone(),
            },
            callable_ref,
        )
        .with_candidate_resolution(MachineGlobalScopeEntry::CurrentModule {
            name: name.clone(),
            source_index: 0,
            decl_interface_hash: decl_hash,
        });
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let current = MachineCheckedCurrentDecl {
            name: name.clone(),
            source_index: 0,
            decl_interface_hash: decl_hash,
            decl: Decl::Axiom {
                name: name.as_dotted(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::sort(Level::succ(Level::param("u"))),
            },
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                &[],
                module,
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Root.A", vec![raw_max_zero_zero()]),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect("renderer QA should compare constant universe levels after normalization");
    }

    #[test]
    fn qa_uses_renderer_callable_table_over_stale_elab_context_table() {
        let module = Name::from_dotted("Root");
        let id_name = Name::from_dotted("Root.id");
        let id_hash = h(7);
        let callable_ref = MachineSurfaceCallableRef::CurrentModule {
            module: module.clone(),
            name: id_name.clone(),
            source_index: 0,
            decl_interface_hash: id_hash,
        };
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: module.clone(),
                name: id_name.clone(),
                decl_interface_hash: id_hash,
                source_index: 0,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: module.clone(),
            },
            callable_ref.clone(),
        )
        .with_candidate_resolution(MachineGlobalScopeEntry::CurrentModule {
            name: id_name.clone(),
            source_index: 0,
            decl_interface_hash: id_hash,
        });
        let scope = MachineDisplayRenderScope::from_entries(vec![display_entry]).unwrap();
        let renderer_table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &renderer_table,
            base_context: &[],
            universe_params: &[],
        };
        let id_ty = Expr::pi("A", type0(), Expr::pi("x", Expr::bvar(0), Expr::bvar(1)));
        let current = MachineCheckedCurrentDecl {
            name: id_name.clone(),
            source_index: 0,
            decl_interface_hash: id_hash,
            decl: Decl::Axiom {
                name: id_name.as_dotted(),
                universe_params: Vec::new(),
                ty: id_ty,
            },
        };
        let stale_table = MachineSurfaceCallableInterfaceTable::from_entries([
            MachineSurfaceCallableInterfaceEntry::new(
                callable_ref,
                vec![
                    MachineCallableBinderVisibility::Implicit,
                    MachineCallableBinderVisibility::Explicit,
                ],
            ),
        ])
        .unwrap();
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                &[],
                module,
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap()
            .with_callable_interface_table(stale_table);

        renderer_qa_round_trip(
            &Expr::app(Expr::konst("Root.id", Vec::new()), prop()),
            &render_context,
            &elab_context,
            &Expr::pi("x", prop(), prop()),
        )
        .expect("renderer QA must elaborate with the renderer callable table");
    }

    #[test]
    fn qa_round_trips_display_only_loaded_available_import() {
        let hidden = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Hidden"),
                declarations: vec![Decl::Axiom {
                    name: "Hidden.Thing".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        );
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Direct"),
                declarations: vec![Decl::Axiom {
                    name: "Direct.use_hidden".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Hidden.Thing", Vec::new()),
                }],
            },
            std::slice::from_ref(&hidden),
        );
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        assert!(
            !elab_context
                .global_scope_entries()
                .iter()
                .any(|entry| entry.name() == &hidden_name),
            "available dependency should not be candidate-scope visible before renderer QA projection"
        );
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: direct.module().clone(),
                owner_export_hash: direct.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect("renderer QA should use display scope for loaded available imports");
    }

    #[test]
    fn qa_rejects_display_only_unloaded_available_import_with_same_name_and_hash() {
        let loaded = shared_foo_import("Loaded");
        let unloaded = shared_foo_import("Other");
        let foo_name = Name::from_dotted("Shared.Foo");
        let foo_hash = export_decl_hash(&loaded, "Shared.Foo");
        assert_eq!(foo_hash, export_decl_hash(&unloaded, "Shared.Foo"));
        let direct = direct_using_shared_import(&loaded);
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), loaded, unloaded.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: unloaded.module().clone(),
                name: foo_name.clone(),
                export_hash: unloaded.export_hash(),
                decl_interface_hash: foo_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unloaded.module().clone(),
                owner_export_hash: unloaded.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: unloaded.module().clone(),
                name: foo_name,
                export_hash: unloaded.export_hash(),
                decl_interface_hash: foo_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Shared.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("display-only QA must reject available imports that were not loaded");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_round_trips_private_imported_display_ref_with_owner_module() {
        let hidden = private_hidden_import();
        let private_name = Name::from_dotted("Hidden.Private");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module.clone(),
                name: private_name.clone(),
                export_hash: hidden.export_hash,
                decl_interface_hash: h(72),
                public_export: false,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: hidden.module.clone(),
                owner_export_hash: hidden.export_hash,
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module.clone(),
                name: private_name.clone(),
                export_hash: hidden.export_hash,
                decl_interface_hash: h(72),
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_imports(
            std::slice::from_ref(&hidden),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Hidden.Private", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect("owner modules should be able to display their private ordinary declarations");
    }

    #[test]
    fn qa_rejects_transitive_imported_display_ref_with_current_session_owner() {
        let hidden = hidden_thing_import();
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = direct_using_hidden_import(&hidden);
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: Name::from_dotted("Root"),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("transitive imports must not use the current-session owner context");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_imported_display_ref_with_unknown_verified_owner() {
        let hidden = hidden_thing_import();
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: Name::from_dotted("Forged.Owner"),
                owner_export_hash: h(99),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name,
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&hidden),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("verified owner context must exist in the QA import context");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_imported_display_ref_with_unrelated_verified_owner() {
        let hidden = hidden_thing_import();
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = direct_using_hidden_import(&hidden);
        let unrelated = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Unrelated"),
                declarations: vec![Decl::Axiom {
                    name: "Unrelated.value".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        );
        let elab_context = MachineTermElabContext::from_verified_modules(
            &[direct.clone(), unrelated.clone()],
            &[direct.clone(), unrelated.clone(), hidden.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unrelated.module().clone(),
                owner_export_hash: unrelated.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("verified owner must depend on the displayed import");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_imported_display_ref_with_owner_dependency_from_other_module() {
        let hidden_a = shared_foo_import("HiddenA");
        let hidden_b = shared_foo_import("HiddenB");
        let foo_name = Name::from_dotted("Shared.Foo");
        let foo_hash = export_decl_hash(&hidden_a, "Shared.Foo");
        assert_eq!(foo_hash, export_decl_hash(&hidden_b, "Shared.Foo"));
        let direct = direct_using_shared_import(&hidden_a);
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden_a, hidden_b.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden_b.module().clone(),
                name: foo_name.clone(),
                export_hash: hidden_b.export_hash(),
                decl_interface_hash: foo_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: direct.module().clone(),
                owner_export_hash: direct.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden_b.module().clone(),
                name: foo_name.clone(),
                export_hash: hidden_b.export_hash(),
                decl_interface_hash: foo_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Shared.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("verified owner dependency must match module and export hash");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_transitive_imported_display_ref_marked_tactic_visible() {
        let hidden = hidden_thing_import();
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = direct_using_hidden_import(&hidden);
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry =
            imported_entry("Hidden", "Hidden.Thing", hidden.export_hash(), hidden_hash);
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("transitive imports must not be marked as tactic-head-visible");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_public_imported_display_ref_marked_non_public() {
        let hidden = hidden_thing_import();
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let mut display_entry =
            imported_entry("Hidden", "Hidden.Thing", hidden.export_hash(), hidden_hash);
        if let MachineGlobalRefView::Imported {
            public_export,
            tactic_head_visible,
            ..
        } = &mut display_entry.view
        {
            *public_export = false;
            *tactic_head_visible = false;
        }
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&hidden),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("export-block-backed imported refs must be marked public");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_direct_imported_display_ref_without_tactic_visibility() {
        let hidden = hidden_thing_import();
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let mut display_entry =
            imported_entry("Hidden", "Hidden.Thing", hidden.export_hash(), hidden_hash);
        if let MachineGlobalRefView::Imported {
            tactic_head_visible,
            ..
        } = &mut display_entry.view
        {
            *tactic_head_visible = false;
        }
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&hidden),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("direct public imported refs must be tactic-head-visible");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_round_trips_direct_imported_display_ref_with_current_session_owner() {
        let hidden = hidden_thing_import();
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: Name::from_dotted("Root"),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        )
        .with_candidate_resolution(MachineGlobalScopeEntry::Imported {
            name: hidden_name,
            import_index: 0,
            decl_interface_hash: hidden_hash,
        });
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                std::slice::from_ref(&hidden),
                std::slice::from_ref(&hidden),
                Name::from_dotted("Root"),
                &[],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect("direct imports can use the current session owner for the session root module");
    }

    #[test]
    fn qa_round_trips_direct_imported_display_ref_without_candidate_resolution() {
        let hidden = hidden_thing_import();
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: Name::from_dotted("Root"),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                std::slice::from_ref(&hidden),
                std::slice::from_ref(&hidden),
                Name::from_dotted("Root"),
                &[],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect("direct imported refs may resolve through the existing frontend import entry");
    }

    #[test]
    fn qa_rejects_direct_imported_display_ref_with_wrong_current_session_owner_module() {
        let hidden = hidden_thing_import();
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: Name::from_dotted("Forged"),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name,
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                std::slice::from_ref(&hidden),
                std::slice::from_ref(&hidden),
                Name::from_dotted("Root"),
                &[],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("current-session owner module must match the QA session root module");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_imported_display_ref_with_wrong_owner_export_without_candidate_resolution() {
        let hidden = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Hidden"),
                declarations: vec![Decl::Axiom {
                    name: "Hidden.Thing".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        );
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Direct"),
                declarations: vec![Decl::Axiom {
                    name: "Direct.use_hidden".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Hidden.Thing", Vec::new()),
                }],
            },
            std::slice::from_ref(&hidden),
        );
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let forged_module = Name::from_dotted("Forged");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: forged_module.clone(),
                name: hidden_name.clone(),
                export_hash: h(99),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: forged_module.clone(),
                owner_export_hash: h(99),
            },
            MachineSurfaceCallableRef::Imported {
                module: forged_module,
                name: hidden_name,
                export_hash: h(99),
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("display-only imported refs must be backed by a verified module/export");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_current_module_display_ref_missing_from_current_scope() {
        let hidden = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Hidden"),
                declarations: vec![Decl::Axiom {
                    name: "Hidden.Thing".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        );
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Direct"),
                declarations: vec![Decl::Axiom {
                    name: "Direct.use_hidden".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Hidden.Thing", Vec::new()),
                }],
            },
            std::slice::from_ref(&hidden),
        );
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let root = Name::from_dotted("Root");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: root.clone(),
                name: hidden_name.clone(),
                decl_interface_hash: hidden_hash,
                source_index: 42,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: root.clone(),
            },
            MachineSurfaceCallableRef::CurrentModule {
                module: root,
                name: hidden_name,
                source_index: 42,
                decl_interface_hash: hidden_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("display-only current-module refs must be backed by checked current decls");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_current_module_display_ref_with_wrong_root_module() {
        let name = Name::from_dotted("Root.Foo");
        let decl_hash = h(7);
        let current = current_axiom("Root.Foo", decl_hash, prop());
        let forged_module = Name::from_dotted("Forged");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: forged_module.clone(),
                name: name.clone(),
                decl_interface_hash: decl_hash,
                source_index: 0,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: forged_module.clone(),
            },
            MachineSurfaceCallableRef::CurrentModule {
                module: forged_module,
                name: name.clone(),
                source_index: 0,
                decl_interface_hash: decl_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                &[],
                Name::from_dotted("Root"),
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Root.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &prop(),
        )
        .expect_err("current-module display refs must use the current declaration module");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_round_trips_current_module_display_ref_with_nested_name_and_root_module() {
        let name = Name::from_dotted("Root.Sub.Foo");
        let decl_hash = h(7);
        let current = current_axiom("Root.Sub.Foo", decl_hash, prop());
        let root_module = Name::from_dotted("Root");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: root_module.clone(),
                name: name.clone(),
                decl_interface_hash: decl_hash,
                source_index: 0,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: root_module.clone(),
            },
            MachineSurfaceCallableRef::CurrentModule {
                module: root_module.clone(),
                name: name.clone(),
                source_index: 0,
                decl_interface_hash: decl_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                &[],
                root_module,
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Root.Sub.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &prop(),
        )
        .expect("nested current declaration names should use the session root module");
    }

    #[test]
    fn qa_rejects_current_module_display_ref_with_inner_module() {
        let name = Name::from_dotted("Root.Sub.Foo");
        let decl_hash = h(7);
        let current = current_axiom("Root.Sub.Foo", decl_hash, prop());
        let inner_module = Name::from_dotted("Root.Sub");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::CurrentModule {
                module: inner_module.clone(),
                name: name.clone(),
                decl_interface_hash: decl_hash,
                source_index: 0,
            },
            MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                module: inner_module.clone(),
            },
            MachineSurfaceCallableRef::CurrentModule {
                module: inner_module,
                name: name.clone(),
                source_index: 0,
                decl_interface_hash: decl_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                &[],
                Name::from_dotted("Root"),
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Root.Sub.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &prop(),
        )
        .expect_err("current-module display refs must use the session root module");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_round_trips_imported_generated_display_ref() {
        let unary = unary_import();
        let unary_hash = export_decl_hash(&unary, "Unary");
        let zero_name = Name::from_dotted("Unary.zero");
        let zero_hash = export_decl_hash(&unary, "Unary.zero");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::LocalGenerated {
                module: unary.module().clone(),
                export_hash: Some(unary.export_hash()),
                parent_name: Name::from_dotted("Unary"),
                name: zero_name.clone(),
                parent_decl_interface_hash: unary_hash,
                decl_interface_hash: zero_hash,
                public_export: true,
                tactic_head_visible: true,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unary.module().clone(),
                owner_export_hash: unary.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: unary.module().clone(),
                name: zero_name.clone(),
                export_hash: unary.export_hash(),
                decl_interface_hash: zero_hash,
            },
        )
        .with_candidate_resolution(MachineGlobalScopeEntry::Imported {
            name: zero_name,
            import_index: 0,
            decl_interface_hash: zero_hash,
        });
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&unary),
            std::slice::from_ref(&unary),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Unary.zero", Vec::new()),
            &render_context,
            &elab_context,
            &unary_expr(),
        )
        .expect("imported generated display refs should be backed by generated export metadata");
    }

    #[test]
    fn qa_round_trips_private_imported_generated_display_ref_with_owner_module() {
        let unary = private_unary_import();
        let zero_name = Name::from_dotted("Unary.zero");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::LocalGenerated {
                module: unary.module.clone(),
                export_hash: Some(unary.export_hash),
                parent_name: Name::from_dotted("Unary"),
                name: zero_name.clone(),
                parent_decl_interface_hash: h(81),
                decl_interface_hash: h(81),
                public_export: false,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unary.module.clone(),
                owner_export_hash: unary.export_hash,
            },
            MachineSurfaceCallableRef::Imported {
                module: unary.module.clone(),
                name: zero_name.clone(),
                export_hash: unary.export_hash,
                decl_interface_hash: h(81),
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_imports(
            std::slice::from_ref(&unary),
            std::slice::from_ref(&unary),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        renderer_qa_round_trip(
            &Expr::konst("Unary.zero", Vec::new()),
            &render_context,
            &elab_context,
            &unary_expr(),
        )
        .expect("owner modules should be able to display private generated declarations");
    }

    #[test]
    fn qa_rejects_imported_generated_display_ref_with_wrong_parent() {
        let unary = unary_import();
        let zero_name = Name::from_dotted("Unary.zero");
        let zero_hash = export_decl_hash(&unary, "Unary.zero");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::LocalGenerated {
                module: unary.module().clone(),
                export_hash: Some(unary.export_hash()),
                parent_name: Name::from_dotted("Unary.Forged"),
                name: zero_name.clone(),
                parent_decl_interface_hash: h(99),
                decl_interface_hash: zero_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unary.module().clone(),
                owner_export_hash: unary.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: unary.module().clone(),
                name: zero_name,
                export_hash: unary.export_hash(),
                decl_interface_hash: zero_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&unary),
            std::slice::from_ref(&unary),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Unary.zero", Vec::new()),
            &render_context,
            &elab_context,
            &unary_expr(),
        )
        .expect_err("imported generated refs must validate parent generated metadata");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_imported_generated_display_ref_with_unrelated_verified_owner() {
        let unary = unary_import();
        let unary_hash = export_decl_hash(&unary, "Unary");
        let zero_name = Name::from_dotted("Unary.zero");
        let zero_hash = export_decl_hash(&unary, "Unary.zero");
        let unrelated = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Unrelated"),
                declarations: vec![Decl::Axiom {
                    name: "Unrelated.value".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        );
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::LocalGenerated {
                module: unary.module().clone(),
                export_hash: Some(unary.export_hash()),
                parent_name: Name::from_dotted("Unary"),
                name: zero_name.clone(),
                parent_decl_interface_hash: unary_hash,
                decl_interface_hash: zero_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unrelated.module().clone(),
                owner_export_hash: unrelated.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: unary.module().clone(),
                name: zero_name.clone(),
                export_hash: unary.export_hash(),
                decl_interface_hash: zero_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&unrelated),
            &[unrelated.clone(), unary.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Unary.zero", Vec::new()),
            &render_context,
            &elab_context,
            &unary_expr(),
        )
        .expect_err("verified owner must depend on the displayed generated import");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_generated_export_displayed_as_imported() {
        let unary = unary_import();
        let zero_name = Name::from_dotted("Unary.zero");
        let zero_hash = export_decl_hash(&unary, "Unary.zero");
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: unary.module().clone(),
                name: zero_name.clone(),
                export_hash: unary.export_hash(),
                decl_interface_hash: zero_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: unary.module().clone(),
                owner_export_hash: unary.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: unary.module().clone(),
                name: zero_name,
                export_hash: unary.export_hash(),
                decl_interface_hash: zero_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&unary),
            std::slice::from_ref(&unary),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Unary.zero", Vec::new()),
            &render_context,
            &elab_context,
            &unary_expr(),
        )
        .expect_err("generated exports must use LocalGenerated display refs");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_imported_candidate_resolution_with_wrong_owner_export() {
        let hidden = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Hidden"),
                declarations: vec![Decl::Axiom {
                    name: "Hidden.Thing".to_owned(),
                    universe_params: Vec::new(),
                    ty: type0(),
                }],
            },
            &[],
        );
        let hidden_name = Name::from_dotted("Hidden.Thing");
        let hidden_hash = export_decl_hash(&hidden, "Hidden.Thing");
        let direct = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Direct"),
                declarations: vec![Decl::Axiom {
                    name: "Direct.use_hidden".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Hidden.Thing", Vec::new()),
                }],
            },
            std::slice::from_ref(&hidden),
        );
        let elab_context = MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&direct),
            &[direct.clone(), hidden.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: direct.module().clone(),
                owner_export_hash: direct.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: hidden.module().clone(),
                name: hidden_name.clone(),
                export_hash: hidden.export_hash(),
                decl_interface_hash: hidden_hash,
            },
        )
        .with_candidate_resolution(MachineGlobalScopeEntry::Imported {
            name: hidden_name,
            import_index: 0,
            decl_interface_hash: hidden_hash,
        });
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Hidden.Thing", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("candidate import index must point at the displayed module/export");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeCandidateResolutionMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_display_projection_import_index_collision_with_direct_import() {
        let direct_export = shared_foo_import("DirectExport");
        let other = shared_foo_import("Other");
        let direct_user = direct_using_shared_import(&other);
        let foo_name = Name::from_dotted("Shared.Foo");
        let foo_hash = export_decl_hash(&direct_export, "Shared.Foo");
        assert_eq!(foo_hash, export_decl_hash(&other, "Shared.Foo"));
        let elab_context = MachineTermElabContext::from_verified_modules(
            &[direct_export.clone(), direct_user.clone()],
            &[direct_export, direct_user, other.clone()],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let display_entry = MachineDisplayRenderScopeEntry::new(
            MachineGlobalRefView::Imported {
                module: other.module().clone(),
                name: foo_name.clone(),
                export_hash: other.export_hash(),
                decl_interface_hash: foo_hash,
                public_export: true,
                tactic_head_visible: false,
            },
            MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: other.module().clone(),
                owner_export_hash: other.export_hash(),
            },
            MachineSurfaceCallableRef::Imported {
                module: other.module().clone(),
                name: foo_name,
                export_hash: other.export_hash(),
                decl_interface_hash: foo_hash,
            },
        );
        let scope = MachineDisplayRenderScope::from_entries([display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };

        let err = renderer_qa_round_trip(
            &Expr::konst("Shared.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &type0(),
        )
        .expect_err("display-only QA must reject names that resolve to a different import");

        assert!(matches!(
            err,
            MachineExprRendererError::QAGlobalResolutionMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_display_only_resolution_shadowed_by_candidate_scope() {
        let other = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Other.Module"),
                declarations: vec![Decl::Axiom {
                    name: "Root.Foo".to_owned(),
                    universe_params: Vec::new(),
                    ty: prop(),
                }],
            },
            &[],
        );
        let foo_hash = export_decl_hash(&other, "Root.Foo");
        let mut display_entry =
            imported_entry("Other.Module", "Root.Foo", other.export_hash(), foo_hash);
        if let MachineGlobalRefView::Imported {
            tactic_head_visible,
            ..
        } = &mut display_entry.view
        {
            *tactic_head_visible = false;
        }
        let scope = MachineDisplayRenderScope::from_entries(vec![display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let current = current_axiom("Root.Foo", foo_hash, prop());
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                std::slice::from_ref(&other),
                Name::from_dotted("Root"),
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Root.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &prop(),
        )
        .expect_err("display-only QA must reject imports that were not loaded");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }

    #[test]
    fn qa_rejects_frontend_resolution_that_differs_from_display_scope() {
        let other = verified_core_module(
            npa_cert::CoreModule {
                name: Name::from_dotted("Other.Module"),
                declarations: vec![Decl::Axiom {
                    name: "Root.Foo".to_owned(),
                    universe_params: Vec::new(),
                    ty: prop(),
                }],
            },
            &[],
        );
        let foo_hash = export_decl_hash(&other, "Root.Foo");
        let mut display_entry =
            imported_entry("Other.Module", "Root.Foo", other.export_hash(), foo_hash);
        if let MachineGlobalRefView::Imported {
            tactic_head_visible,
            ..
        } = &mut display_entry.view
        {
            *tactic_head_visible = false;
        }
        let scope = MachineDisplayRenderScope::from_entries(vec![display_entry]).unwrap();
        let table = MachineSurfaceCallableInterfaceTable::empty();
        let render_context = MachineExprRendererContext {
            display_scope: &scope,
            callable_interface_table: &table,
            base_context: &[],
            universe_params: &[],
        };
        let current = current_axiom("Root.Foo", foo_hash, prop());
        let elab_context =
            MachineTermElabContext::from_verified_modules_and_current_decls_in_module(
                &[],
                std::slice::from_ref(&other),
                Name::from_dotted("Root"),
                &[current],
                &[],
                Vec::new(),
                Vec::new(),
            )
            .unwrap();

        let err = renderer_qa_round_trip(
            &Expr::konst("Root.Foo", Vec::new()),
            &render_context,
            &elab_context,
            &prop(),
        )
        .expect_err("display-only QA must reject imports that were not loaded");

        assert!(matches!(
            err,
            MachineExprRendererError::DisplayScopeOwnerContextMismatch { .. }
        ));
    }
}
