use std::collections::{BTreeMap, BTreeSet};

use crate::{
    machine::{
        MachineDirectImportRef, MachineLoadedAvailableDeclRef, MachineVerifiedImportDeclRef,
        MachineVerifiedImportDependencyRef, MachineVerifiedImportExportRef,
        MachineVerifiedImportGeneratedDeclRef, MachineVerifiedImportGeneratedExportRef,
        MachineVerifiedImportRef,
    },
    parse_machine_module, parse_machine_term,
    resolver::resolve_machine_module_with_options,
    MachineBinder, MachineCallableBinderVisibility, MachineCheckedCurrentDecl,
    MachineCheckedCurrentGeneratedDecl, MachineCompileOptions, MachineDecl, MachineDiagnostic,
    MachineDiagnosticKind, MachineDiagnosticPayload, MachineGlobalScope, MachineGlobalScopeEntry,
    MachineItem, MachineLevel, MachineLocalDecl, MachineRepairCandidate, MachineRepairSuggestion,
    MachineRepairSuggestionKind, MachineResolvedConstant, MachineSurfaceMode, MachineTerm,
    MachineTermAst, MachineTermCheckResult, MachineTermElabContext, ResolvedMachineModule, Result,
    VerifiedDependency, VerifiedExport, VerifiedImport,
};
use npa_kernel::{
    eq_inductive, eq_rec_type, nat_inductive, Ctx, Decl, Env, Expr, Level, Reducibility,
};
use sha2::{Digest, Sha256};

pub fn elaborate_machine_module(
    module_name: npa_cert::ModuleName,
    module: ResolvedMachineModule,
    verified_imports: &[VerifiedImport],
    options: &MachineCompileOptions,
) -> Result<npa_cert::CoreModule> {
    elaborate_machine_module_with_available_imports(
        module_name,
        module,
        verified_imports,
        verified_imports,
        options,
    )
}

pub(crate) fn elaborate_machine_module_with_available_imports(
    module_name: npa_cert::ModuleName,
    module: ResolvedMachineModule,
    direct_imports: &[VerifiedImport],
    available_imports: &[VerifiedImport],
    options: &MachineCompileOptions,
) -> Result<npa_cert::CoreModule> {
    let active_imports = active_verified_imports(&module.module.items, direct_imports)?;
    let kernel_env = kernel_env_from_imports(
        active_imports.iter().copied(),
        available_imports,
        true,
        module.module.span,
    )?
    .env;
    let mut elaborator = Elaborator::new(
        active_imports.iter().copied(),
        kernel_env,
        options.mode == MachineSurfaceMode::Repair,
    );
    let mut declarations = Vec::new();

    for item in module.module.items {
        match item {
            MachineItem::Import { .. } => {}
            MachineItem::Def(decl) => {
                let span = decl.span;
                let decl = elaborator.elaborate_decl(decl, DeclKind::Def)?;
                elaborator.add_decl_to_kernel_env(&decl, span)?;
                elaborator.add_decl_signature(&decl);
                declarations.push(decl);
            }
            MachineItem::Theorem(decl) => {
                let span = decl.span;
                let decl = elaborator.elaborate_decl(decl, DeclKind::Theorem)?;
                elaborator.add_decl_to_kernel_env(&decl, span)?;
                elaborator.add_decl_signature(&decl);
                declarations.push(decl);
            }
        }
    }

    Ok(npa_cert::CoreModule {
        name: module_name,
        declarations,
    })
}

pub fn compile_machine_source_to_core(
    file_id: crate::FileId,
    module_name: npa_cert::ModuleName,
    source: &str,
    verified_imports: &[VerifiedImport],
    options: &MachineCompileOptions,
) -> Result<npa_cert::CoreModule> {
    let module = parse_machine_module(file_id, source)?;
    let resolved = resolve_machine_module_with_options(module, verified_imports, options)?;
    elaborate_machine_module(module_name, resolved, verified_imports, options)
}

pub fn compile_machine_source_to_certificate(
    file_id: crate::FileId,
    module_name: npa_cert::ModuleName,
    source: &str,
    verified_modules: &[npa_cert::VerifiedModule],
    options: &MachineCompileOptions,
) -> Result<npa_cert::ModuleCert> {
    compile_machine_source_to_certificate_with_available_imports(
        file_id,
        module_name,
        source,
        verified_modules,
        verified_modules,
        options,
    )
}

pub fn compile_machine_source_to_certificate_with_available_imports(
    file_id: crate::FileId,
    module_name: npa_cert::ModuleName,
    source: &str,
    direct_verified_modules: &[npa_cert::VerifiedModule],
    available_verified_modules: &[npa_cert::VerifiedModule],
    options: &MachineCompileOptions,
) -> Result<npa_cert::ModuleCert> {
    let direct_imports: Vec<_> = direct_verified_modules
        .iter()
        .map(VerifiedImport::from)
        .collect();
    let available_imports: Vec<_> = available_verified_modules
        .iter()
        .map(VerifiedImport::from)
        .collect();
    let parsed = parse_machine_module(file_id, source)?;
    let resolved = resolve_machine_module_with_options(parsed, &direct_imports, options)?;
    let active_import_indices =
        active_verified_import_indices(&resolved.module.items, &direct_imports)?;
    let module = elaborate_machine_module_with_available_imports(
        module_name,
        resolved,
        &direct_imports,
        &available_imports,
        options,
    )?;
    let direct_refs = direct_verified_modules.iter().collect::<Vec<_>>();
    let available_refs = available_verified_modules.iter().collect::<Vec<_>>();
    let verified_modules = combined_verified_module_refs(&direct_refs, &available_refs);
    let (certificate_imports, preferred_imports) =
        certificate_import_refs_and_providers_for_module_refs(
            &module,
            &active_import_indices,
            &verified_modules,
            file_id,
        )?;
    let certificate_imports = certificate_imports.into_iter().cloned().collect::<Vec<_>>();
    let certificate_import_refs = certificate_imports.iter().collect::<Vec<_>>();
    let cert = npa_cert::build_module_cert_from_import_refs_with_preferred_imports(
        module,
        &certificate_import_refs,
        &preferred_imports,
    )
    .map_err(|err| {
        MachineDiagnostic::error(
            MachineDiagnosticKind::CertificateRejected,
            crate::Span::empty(file_id),
            format!("certificate construction failed: {err:?}"),
        )
    })?;
    let bytes = npa_cert::encode_module_cert(&cert).map_err(|err| {
        MachineDiagnostic::error(
            MachineDiagnosticKind::CertificateRejected,
            crate::Span::empty(file_id),
            format!("certificate encoding failed: {err:?}"),
        )
    })?;
    let mut session = npa_cert::VerifierSession::new();
    for import in certificate_imports {
        session.register_verified_module(import);
    }
    npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal()).map_err(
        |err| {
            MachineDiagnostic::error(
                MachineDiagnosticKind::CertificateRejected,
                crate::Span::empty(file_id),
                format!("certificate verification failed: {err:?}"),
            )
        },
    )?;
    Ok(cert)
}

pub fn elaborate_machine_term_check(
    source: &str,
    context: &MachineTermElabContext,
    expected: &npa_kernel::Expr,
    options: &MachineCompileOptions,
) -> Result<MachineTermCheckResult> {
    let parsed = parse_machine_term(crate::FileId(0), source)?;
    let span = crate::Span::new(crate::FileId(0), 0, source.len() as u32);
    let (expr, inferred_type, elaborator, locals, constants) = elaborate_machine_term_infer(
        parsed,
        span,
        context,
        options.mode == MachineSurfaceMode::Repair,
    )?;
    elaborator.check_expr(&expr, expected, &locals, &context.universe_params, span)?;

    Ok(MachineTermCheckResult {
        core_hash: hash_owner_free_core_expr(&expr),
        contextual_core_hash: hash_contextual_core_expr(&expr, context, &constants, span)?,
        constants,
        expr,
        inferred_type,
    })
}

pub fn elaborate_machine_term_infer_from_ast(
    ast: &MachineTermAst,
    context: &MachineTermElabContext,
    options: &MachineCompileOptions,
) -> Result<(npa_kernel::Expr, npa_kernel::Expr)> {
    let span = ast.term.span();
    let (expr, inferred_type, _, _, _) = elaborate_machine_term_infer(
        ast.term.clone(),
        span,
        context,
        options.mode == MachineSurfaceMode::Repair,
    )?;
    Ok((expr, inferred_type))
}

impl MachineTermElabContext {
    pub fn from_verified_modules(
        direct_verified_modules: &[npa_cert::VerifiedModule],
        available_verified_modules: &[npa_cert::VerifiedModule],
        local_context: Vec<MachineLocalDecl>,
        universe_params: Vec<String>,
    ) -> Result<Self> {
        let direct_imports: Vec<_> = direct_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        let available_imports: Vec<_> = available_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        machine_term_context_from_verified_imports(
            &direct_imports,
            &available_imports,
            local_context,
            universe_params,
            crate::Span::empty(crate::FileId(0)),
        )
    }

    pub fn from_verified_imports(
        direct_imports: &[VerifiedImport],
        available_imports: &[VerifiedImport],
        local_context: Vec<MachineLocalDecl>,
        universe_params: Vec<String>,
    ) -> Result<Self> {
        machine_term_context_from_verified_imports(
            direct_imports,
            available_imports,
            local_context,
            universe_params,
            crate::Span::empty(crate::FileId(0)),
        )
    }

    pub fn from_verified_modules_and_current_decls(
        direct_verified_modules: &[npa_cert::VerifiedModule],
        available_verified_modules: &[npa_cert::VerifiedModule],
        checked_current_decls: &[MachineCheckedCurrentDecl],
        current_generated_decls: &[MachineCheckedCurrentGeneratedDecl],
        local_context: Vec<MachineLocalDecl>,
        universe_params: Vec<String>,
    ) -> Result<Self> {
        let direct_imports: Vec<_> = direct_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        let available_imports: Vec<_> = available_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        machine_term_context_from_parts(MachineTermContextParts {
            direct_imports: &direct_imports,
            available_imports: &available_imports,
            checked_current_decls,
            current_generated_decls,
            local_context,
            universe_params,
            current_module: None,
            allow_builtin_kernel_decls: true,
            span: crate::Span::empty(crate::FileId(0)),
        })
    }

    pub fn from_verified_modules_and_current_decls_in_module(
        direct_verified_modules: &[npa_cert::VerifiedModule],
        available_verified_modules: &[npa_cert::VerifiedModule],
        current_module: npa_cert::ModuleName,
        checked_current_decls: &[MachineCheckedCurrentDecl],
        current_generated_decls: &[MachineCheckedCurrentGeneratedDecl],
        local_context: Vec<MachineLocalDecl>,
        universe_params: Vec<String>,
    ) -> Result<Self> {
        let direct_imports: Vec<_> = direct_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        let available_imports: Vec<_> = available_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        machine_term_context_from_parts(MachineTermContextParts {
            direct_imports: &direct_imports,
            available_imports: &available_imports,
            checked_current_decls,
            current_generated_decls,
            local_context,
            universe_params,
            current_module: Some(current_module),
            allow_builtin_kernel_decls: true,
            span: crate::Span::empty(crate::FileId(0)),
        })
    }

    pub fn from_verified_modules_and_current_decls_in_module_request(
        request: MachineTermElabContextInModuleRequest<'_>,
    ) -> Result<Self> {
        let direct_imports: Vec<_> = request
            .direct_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        let available_imports: Vec<_> = request
            .available_verified_modules
            .iter()
            .map(VerifiedImport::from)
            .collect();
        machine_term_context_from_parts(MachineTermContextParts {
            direct_imports: &direct_imports,
            available_imports: &available_imports,
            checked_current_decls: request.checked_current_decls,
            current_generated_decls: request.current_generated_decls,
            local_context: request.local_context,
            universe_params: request.universe_params,
            current_module: Some(request.current_module),
            allow_builtin_kernel_decls: request.allow_builtin_kernel_decls,
            span: crate::Span::empty(crate::FileId(0)),
        })
    }

    pub fn from_verified_imports_and_current_decls_in_module(
        direct_imports: &[VerifiedImport],
        available_imports: &[VerifiedImport],
        current_module: npa_cert::ModuleName,
        checked_current_decls: &[MachineCheckedCurrentDecl],
        current_generated_decls: &[MachineCheckedCurrentGeneratedDecl],
        local_context: Vec<MachineLocalDecl>,
        universe_params: Vec<String>,
    ) -> Result<Self> {
        machine_term_context_from_parts(MachineTermContextParts {
            direct_imports,
            available_imports,
            checked_current_decls,
            current_generated_decls,
            local_context,
            universe_params,
            current_module: Some(current_module),
            allow_builtin_kernel_decls: true,
            span: crate::Span::empty(crate::FileId(0)),
        })
    }
}

pub struct MachineTermElabContextInModuleRequest<'a> {
    pub direct_verified_modules: &'a [npa_cert::VerifiedModule],
    pub available_verified_modules: &'a [npa_cert::VerifiedModule],
    pub current_module: npa_cert::ModuleName,
    pub checked_current_decls: &'a [MachineCheckedCurrentDecl],
    pub current_generated_decls: &'a [MachineCheckedCurrentGeneratedDecl],
    pub local_context: Vec<MachineLocalDecl>,
    pub universe_params: Vec<String>,
    pub allow_builtin_kernel_decls: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclKind {
    Def,
    Theorem,
}

const MAX_NUMERIC_UNIVERSE_LEVEL: u64 = 1024;

#[derive(Clone, Debug)]
struct ElaboratedBinder {
    name: String,
    ty: Expr,
}

#[derive(Clone, Debug)]
struct GlobalSignature {
    universe_params: Vec<String>,
    implicit_profile: Vec<MachineCallableBinderVisibility>,
}

#[derive(Clone, Debug)]
struct LocalDecl {
    name: String,
    ty: Expr,
    value: Option<Expr>,
}

#[derive(Clone, Debug, Default)]
struct LocalContext {
    locals: Vec<LocalDecl>,
}

impl LocalContext {
    fn push_assumption(&mut self, name: String, ty: Expr) {
        self.locals.push(LocalDecl {
            name,
            ty,
            value: None,
        });
    }

    fn push_definition(&mut self, name: String, ty: Expr, value: Expr) {
        self.locals.push(LocalDecl {
            name,
            ty,
            value: Some(value),
        });
    }

    fn lookup_bvar(&self, name: &str) -> Option<u32> {
        self.locals
            .iter()
            .rev()
            .position(|local| local.name == name)
            .map(|index| index as u32)
    }

    fn name_for_bvar(&self, index: u32) -> Option<&str> {
        let index = usize::try_from(index).ok()?;
        self.locals
            .len()
            .checked_sub(index + 1)
            .and_then(|local_index| self.locals.get(local_index))
            .map(|local| local.name.as_str())
    }

    fn contains_name(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|local| local.name == name)
    }

    fn to_kernel_ctx(&self) -> Ctx {
        let mut ctx = Ctx::new();
        for local in &self.locals {
            match &local.value {
                Some(value) => {
                    ctx.push_definition(local.name.clone(), local.ty.clone(), value.clone())
                }
                None => ctx.push_assumption(local.name.clone(), local.ty.clone()),
            }
        }
        ctx
    }
}

#[derive(Clone, Debug, Default)]
struct LocalScope {
    names: Vec<String>,
}

impl LocalScope {
    fn from_machine_locals(locals: &[MachineLocalDecl]) -> Self {
        Self {
            names: locals.iter().map(|local| local.name.clone()).collect(),
        }
    }

    fn push(&mut self, name: String) {
        self.names.push(name);
    }

    fn contains(&self, name: &str) -> bool {
        self.names.iter().rev().any(|local| local == name)
    }
}

struct Elaborator {
    globals: BTreeMap<String, GlobalSignature>,
    kernel_env: Env,
    repair_mode: bool,
}

impl Elaborator {
    fn new<'a>(
        verified_imports: impl IntoIterator<Item = &'a VerifiedImport>,
        kernel_env: Env,
        repair_mode: bool,
    ) -> Self {
        let mut elaborator = Self {
            globals: BTreeMap::new(),
            kernel_env,
            repair_mode,
        };

        for import in verified_imports {
            for export in &import.exports {
                elaborator.add_global_signature(
                    export.name.as_dotted(),
                    export.universe_params.clone(),
                    Vec::new(),
                );
            }
        }

        elaborator
    }

    fn from_term_context(
        context: &MachineTermElabContext,
        constants: &[MachineResolvedConstant],
        span: crate::Span,
        repair_mode: bool,
    ) -> Result<Self> {
        let kernel_env = context.kernel_env.env().clone();
        let mut elaborator = Self {
            globals: BTreeMap::new(),
            kernel_env,
            repair_mode,
        };

        for constant in constants {
            let name = constant.name.as_dotted();
            if !context
                .kernel_env
                .has_decl_interface_hash(&name, &constant.decl_interface_hash)
            {
                return Err(MachineDiagnostic::error(
                    MachineDiagnosticKind::ImportResolutionError,
                    span,
                    format!(
                        "resolved global {name} is not backed by a matching declaration interface hash"
                    ),
                ));
            }

            let Some(decl) = elaborator.kernel_env.decl(&name) else {
                return Err(MachineDiagnostic::error(
                    MachineDiagnosticKind::UnknownGlobalName,
                    span,
                    format!("resolved global {name} is missing from kernel environment"),
                ));
            };
            let universe_params = decl.universe_params().to_vec();
            let implicit_profile = match context
                .callable_interface_table
                .entries_for_decl(&constant.name, &constant.decl_interface_hash)
                .as_slice()
            {
                [] => Vec::new(),
                [entry] => entry.implicit_profile().to_vec(),
                _ => {
                    return Err(MachineDiagnostic::error(
                        MachineDiagnosticKind::ImportResolutionError,
                        span,
                        format!("resolved global {name} has multiple callable interface entries"),
                    ));
                }
            };
            elaborator.add_global_signature(name, universe_params, implicit_profile);
        }

        Ok(elaborator)
    }

    fn add_decl_signature(&mut self, decl: &Decl) {
        self.add_global_signature(
            decl.name().to_owned(),
            decl.universe_params().to_vec(),
            Vec::new(),
        );
    }

    fn add_global_signature(
        &mut self,
        name: String,
        universe_params: Vec<String>,
        implicit_profile: Vec<MachineCallableBinderVisibility>,
    ) {
        self.globals.insert(
            name,
            GlobalSignature {
                universe_params,
                implicit_profile,
            },
        );
    }

    fn elaborate_decl(&self, decl: MachineDecl, kind: DeclKind) -> Result<Decl> {
        let name = decl.name.as_dotted();
        let universe_params: Vec<_> = decl
            .universe_params
            .into_iter()
            .map(|param| param.name)
            .collect();
        let mut locals = LocalContext::default();
        let mut binders = Vec::with_capacity(decl.binders.len());

        for binder in decl.binders {
            let binder = self.elaborate_binder(binder, &mut locals, &universe_params)?;
            binders.push(binder);
        }

        let ty = close_pi(
            &binders,
            self.elaborate_term(decl.ty, &mut locals, &universe_params)?,
        );
        let value = close_lam(
            &binders,
            self.elaborate_term(decl.value, &mut locals, &universe_params)?,
        );

        match kind {
            DeclKind::Def => Ok(Decl::Def {
                name,
                universe_params,
                ty,
                value,
                reducibility: Reducibility::Reducible,
            }),
            DeclKind::Theorem => Ok(Decl::Theorem {
                name,
                universe_params,
                ty,
                proof: value,
            }),
        }
    }

    fn elaborate_binder(
        &self,
        binder: MachineBinder,
        locals: &mut LocalContext,
        delta: &[String],
    ) -> Result<ElaboratedBinder> {
        let ty = self.elaborate_term(binder.ty, locals, delta)?;
        locals.push_assumption(binder.name.clone(), ty.clone());

        Ok(ElaboratedBinder {
            name: binder.name,
            ty,
        })
    }

    fn elaborate_term(
        &self,
        term: MachineTerm,
        locals: &mut LocalContext,
        delta: &[String],
    ) -> Result<Expr> {
        match term {
            MachineTerm::Ident {
                name,
                universe_args,
                explicit_mode,
                span,
            } => {
                let name = name.as_dotted();
                let universe_param_count = self.universe_param_count(&name);
                let levels = self.elaborate_universe_args(
                    universe_args,
                    universe_param_count,
                    explicit_mode,
                    span,
                    &name,
                    delta,
                )?;

                Ok(Expr::konst(name, levels))
            }
            MachineTerm::Local { name, span } => {
                locals.lookup_bvar(&name).map(Expr::bvar).ok_or_else(|| {
                    MachineDiagnostic::error(
                        MachineDiagnosticKind::UnknownLocalName,
                        span,
                        format!("unknown local name {name}"),
                    )
                })
            }
            MachineTerm::Prop { .. } => Ok(Expr::sort(Level::zero())),
            MachineTerm::Type { level, .. } => Ok(Expr::sort(Level::succ(elaborate_level(level)?))),
            MachineTerm::Sort { level, .. } => Ok(Expr::sort(elaborate_level(level)?)),
            MachineTerm::App { func, arg, .. } => {
                if let Some(diagnostic) =
                    self.application_repair_diagnostic(&func, &arg, locals, delta)
                {
                    return Err(diagnostic);
                }
                if let Some(diagnostic) = self.implicit_application_diagnostic(&func, &arg) {
                    return Err(diagnostic);
                }

                Ok(Expr::app(
                    self.elaborate_term(*func, locals, delta)?,
                    self.elaborate_term(*arg, locals, delta)?,
                ))
            }
            MachineTerm::Lam { binders, body, .. } => {
                let mut nested_locals = locals.clone();
                let mut elaborated_binders = Vec::with_capacity(binders.len());
                for binder in binders {
                    elaborated_binders.push(self.elaborate_binder(
                        binder,
                        &mut nested_locals,
                        delta,
                    )?);
                }
                let body = self.elaborate_term(*body, &mut nested_locals, delta)?;
                Ok(close_lam(&elaborated_binders, body))
            }
            MachineTerm::Pi { binders, body, .. } => {
                let mut nested_locals = locals.clone();
                let mut elaborated_binders = Vec::with_capacity(binders.len());
                for binder in binders {
                    elaborated_binders.push(self.elaborate_binder(
                        binder,
                        &mut nested_locals,
                        delta,
                    )?);
                }
                let body = self.elaborate_term(*body, &mut nested_locals, delta)?;
                Ok(close_pi(&elaborated_binders, body))
            }
            MachineTerm::Let {
                name,
                ty,
                value,
                body,
                ..
            } => {
                let ty = self.elaborate_term(*ty, locals, delta)?;
                let value = self.elaborate_term(*value, locals, delta)?;
                let mut nested_locals = locals.clone();
                nested_locals.push_definition(name.clone(), ty.clone(), value.clone());
                let body = self.elaborate_term(*body, &mut nested_locals, delta)?;
                Ok(Expr::let_in(name, ty, value, body))
            }
            MachineTerm::Annot { expr, ty, span } => {
                let expr = self.elaborate_term(*expr, locals, delta)?;
                let ty = self.elaborate_term(*ty, locals, delta)?;
                self.ensure_type(&ty, locals, delta, span)?;
                self.check_expr(&expr, &ty, locals, delta, span)?;
                Ok(expr)
            }
        }
    }

    fn universe_param_count(&self, name: &str) -> usize {
        self.globals
            .get(name)
            .map(|signature| signature.universe_params.len())
            .unwrap_or(0)
    }

    fn implicit_profile(&self, name: &str) -> &[MachineCallableBinderVisibility] {
        self.globals
            .get(name)
            .map(|signature| signature.implicit_profile.as_slice())
            .unwrap_or(&[])
    }

    fn ensure_type(
        &self,
        expr: &Expr,
        locals: &LocalContext,
        delta: &[String],
        span: crate::Span,
    ) -> Result<Level> {
        let ctx = locals.to_kernel_ctx();
        let inferred = self
            .kernel_env
            .infer(&ctx, delta, expr)
            .map_err(|err| kernel_expr_diagnostic(span, err))?;
        match self
            .kernel_env
            .whnf(&ctx, delta, &inferred)
            .map_err(|err| kernel_expr_diagnostic(span, err))?
        {
            Expr::Sort(level) => Ok(level),
            actual => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::ExpectedSort,
                span,
                format!("expected a type annotation, got {actual:?}"),
            )),
        }
    }

    fn check_expr(
        &self,
        expr: &Expr,
        expected: &Expr,
        locals: &LocalContext,
        delta: &[String],
        span: crate::Span,
    ) -> Result<()> {
        let ctx = locals.to_kernel_ctx();
        self.kernel_env
            .check(&ctx, delta, expr, expected)
            .map_err(|err| kernel_expr_diagnostic(span, err))
    }

    fn infer_expr(
        &self,
        expr: &Expr,
        locals: &LocalContext,
        delta: &[String],
        span: crate::Span,
    ) -> Result<Expr> {
        let ctx = locals.to_kernel_ctx();
        self.kernel_env
            .infer(&ctx, delta, expr)
            .map_err(|err| kernel_expr_diagnostic(span, err))
    }

    fn add_decl_to_kernel_env(&mut self, decl: &Decl, span: crate::Span) -> Result<()> {
        add_kernel_decl_to_env(&mut self.kernel_env, decl.clone()).map_err(|err| {
            MachineDiagnostic::error(
                MachineDiagnosticKind::KernelRejected,
                span,
                format!("kernel rejected elaborated declaration: {err:?}"),
            )
        })
    }

    fn elaborate_universe_args(
        &self,
        args: Option<Vec<MachineLevel>>,
        expected: usize,
        explicit_mode: bool,
        span: crate::Span,
        name: &str,
        delta: &[String],
    ) -> Result<Vec<Level>> {
        match args {
            Some(args) => {
                if args.len() != expected {
                    let actual = args.len();
                    return Err(self.universe_arg_diagnostic(
                        MachineDiagnosticKind::MissingExplicitUniverse,
                        span,
                        name,
                        UniverseArgCounts { expected, actual },
                        explicit_universe_replacement(name, expected, delta),
                        format!(
                            "global name {name} expects {expected} explicit universe arguments"
                        ),
                    ));
                }

                args.into_iter().map(elaborate_level).collect()
            }
            None if expected == 0 => Ok(Vec::new()),
            None if explicit_mode => Err(self.universe_arg_diagnostic(
                MachineDiagnosticKind::MissingExplicitUniverse,
                span,
                name,
                UniverseArgCounts {
                    expected,
                    actual: 0,
                },
                explicit_universe_replacement(name, expected, delta),
                format!("global name {name} requires explicit universe arguments"),
            )),
            None => Err(self.universe_arg_diagnostic(
                MachineDiagnosticKind::ImplicitArgumentRequired,
                span,
                name,
                UniverseArgCounts {
                    expected,
                    actual: 0,
                },
                explicit_universe_replacement(name, expected, delta),
                format!("global name {name} requires explicit arguments"),
            )),
        }
    }

    fn universe_arg_diagnostic(
        &self,
        kind: MachineDiagnosticKind,
        span: crate::Span,
        name: &str,
        counts: UniverseArgCounts,
        replacement: Option<String>,
        message: String,
    ) -> MachineDiagnostic {
        let diagnostic = MachineDiagnostic::error(kind.clone(), span, message);
        if !self.repair_mode {
            return diagnostic;
        }

        let payload = MachineDiagnosticPayload {
            head_symbol: Some(name.to_owned()),
            expected_universe_args: Some(counts.expected),
            actual_universe_args: Some(counts.actual),
            ..MachineDiagnosticPayload::default()
        };
        let suggestion_kind = match kind {
            MachineDiagnosticKind::ImplicitArgumentRequired => {
                MachineRepairSuggestionKind::InsertExplicitArguments
            }
            MachineDiagnosticKind::MissingExplicitUniverse => {
                MachineRepairSuggestionKind::InsertExplicitUniverseArguments
            }
            _ => return diagnostic.with_payload(payload),
        };
        let suggestion = MachineRepairSuggestion {
            kind: suggestion_kind,
            replacement,
            candidates: Vec::new(),
        };

        diagnostic.with_payload(payload).with_suggestion(suggestion)
    }

    fn application_repair_diagnostic(
        &self,
        func: &MachineTerm,
        arg: &MachineTerm,
        locals: &LocalContext,
        delta: &[String],
    ) -> Option<MachineDiagnostic> {
        if !self.repair_mode {
            return None;
        }

        let (head, args) = machine_app_spine(func, arg);
        let MachineTerm::Ident {
            name,
            universe_args: None,
            explicit_mode,
            span,
        } = head
        else {
            return None;
        };
        let name = name.as_dotted();
        let expected = self.universe_param_count(&name);
        if expected == 0 {
            return None;
        }

        let level_args =
            self.repair_universe_level_sources(expected, args.first()?, locals, delta)?;
        let level_sources: Vec<_> = level_args
            .iter()
            .map(|level| level.source.clone())
            .collect();
        let inserted_arg =
            self.repair_inserted_type_argument(&name, &level_args, args.first()?, locals, delta);
        let supplied_args = args
            .iter()
            .map(|arg| machine_term_repair_source(arg))
            .collect::<Option<Vec<_>>>();
        let replacement = match (inserted_arg, supplied_args) {
            (InsertedTypeArgumentRepair::Unavailable, _) | (_, None) => None,
            (inserted_arg, Some(supplied_args)) => {
                let mut replacement_parts =
                    vec![format!("@{}.{{{}}}", name, level_sources.join(", "))];
                if let InsertedTypeArgumentRepair::Source(inserted_arg) = inserted_arg {
                    replacement_parts.push(inserted_arg);
                }
                replacement_parts.extend(supplied_args);
                Some(replacement_parts.join(" "))
            }
        }
        .and_then(|replacement| self.validated_repair_replacement(replacement, locals, delta));

        let kind = if *explicit_mode {
            MachineDiagnosticKind::MissingExplicitUniverse
        } else {
            MachineDiagnosticKind::ImplicitArgumentRequired
        };
        let message = if *explicit_mode {
            format!("global name {name} requires explicit universe arguments")
        } else {
            format!("global name {name} requires explicit arguments")
        };

        Some(self.universe_arg_diagnostic(
            kind,
            *span,
            &name,
            UniverseArgCounts {
                expected,
                actual: 0,
            },
            replacement,
            message,
        ))
    }

    fn implicit_application_diagnostic(
        &self,
        func: &MachineTerm,
        arg: &MachineTerm,
    ) -> Option<MachineDiagnostic> {
        let (head, args) = machine_app_spine(func, arg);
        let MachineTerm::Ident {
            name,
            universe_args,
            explicit_mode,
            span,
        } = head
        else {
            return None;
        };
        if *explicit_mode {
            return None;
        }

        let name = name.as_dotted();
        let expected_universes = self.universe_param_count(&name);
        match universe_args {
            None if expected_universes != 0 => return None,
            Some(args) if args.len() != expected_universes => return None,
            _ => {}
        }

        let implicit_profile = self.implicit_profile(&name);
        if !implicit_profile
            .iter()
            .take(args.len())
            .any(|visibility| *visibility == MachineCallableBinderVisibility::Implicit)
        {
            return None;
        }

        Some(MachineDiagnostic::error(
            MachineDiagnosticKind::ImplicitArgumentRequired,
            *span,
            format!("global name {name} requires explicit arguments"),
        ))
    }

    fn repair_universe_level_sources(
        &self,
        expected: usize,
        first_arg: &MachineTerm,
        locals: &LocalContext,
        delta: &[String],
    ) -> Option<Vec<RepairUniverseLevel>> {
        if expected == 1 {
            if let Some(first_arg_ty) = self.repair_first_arg_type(first_arg, locals, delta) {
                if let Expr::Sort(level) = &first_arg_ty {
                    return Some(vec![RepairUniverseLevel::new(level.clone())?]);
                }

                let ctx = locals.to_kernel_ctx();
                if let Ok(Expr::Sort(level)) = self.kernel_env.infer(&ctx, delta, &first_arg_ty) {
                    return Some(vec![RepairUniverseLevel::new(level)?]);
                }
            }
        }

        explicit_universe_level_args(expected, delta)
    }

    fn repair_inserted_type_argument(
        &self,
        name: &str,
        level_args: &[RepairUniverseLevel],
        first_arg: &MachineTerm,
        locals: &LocalContext,
        delta: &[String],
    ) -> InsertedTypeArgumentRepair {
        let Some(first_arg_expr) = self.repair_elaborate_arg(first_arg, locals, delta) else {
            return InsertedTypeArgumentRepair::Unavailable;
        };
        let Some(first_arg_ty) = self.repair_first_arg_type(first_arg, locals, delta) else {
            return InsertedTypeArgumentRepair::Unavailable;
        };
        if self.first_supplied_arg_matches_first_binder(
            name,
            level_args,
            &first_arg_expr,
            locals,
            delta,
        ) {
            return InsertedTypeArgumentRepair::NotNeeded;
        }

        match expr_repair_source(&first_arg_ty, locals) {
            Some(source) => InsertedTypeArgumentRepair::Source(source),
            None => InsertedTypeArgumentRepair::Unavailable,
        }
    }

    fn repair_elaborate_arg(
        &self,
        arg: &MachineTerm,
        locals: &LocalContext,
        delta: &[String],
    ) -> Option<Expr> {
        let mut arg_locals = locals.clone();
        self.elaborate_term(arg.clone(), &mut arg_locals, delta)
            .ok()
    }

    fn repair_first_arg_type(
        &self,
        arg: &MachineTerm,
        locals: &LocalContext,
        delta: &[String],
    ) -> Option<Expr> {
        let arg_expr = self.repair_elaborate_arg(arg, locals, delta)?;
        self.kernel_env
            .infer(&locals.to_kernel_ctx(), delta, &arg_expr)
            .ok()
    }

    fn first_supplied_arg_matches_first_binder(
        &self,
        name: &str,
        level_args: &[RepairUniverseLevel],
        first_arg_expr: &Expr,
        locals: &LocalContext,
        delta: &[String],
    ) -> bool {
        let ctx = locals.to_kernel_ctx();
        let levels = level_args.iter().map(|level| level.level.clone()).collect();
        let head = Expr::konst(name, levels);
        let Ok(head_ty) = self.kernel_env.infer(&ctx, delta, &head) else {
            return false;
        };
        let Ok(head_ty) = self.kernel_env.whnf(&ctx, delta, &head_ty) else {
            return false;
        };
        let Expr::Pi { ty, .. } = head_ty else {
            return false;
        };

        self.kernel_env
            .check(&ctx, delta, first_arg_expr, &ty)
            .is_ok()
    }

    fn validated_repair_replacement(
        &self,
        replacement: String,
        locals: &LocalContext,
        delta: &[String],
    ) -> Option<String> {
        let parsed = parse_machine_term(crate::FileId(0), &replacement).ok()?;
        let parsed = localize_repair_term(parsed, locals);
        let mut validation_locals = locals.clone();
        let expr = self
            .elaborate_term(parsed, &mut validation_locals, delta)
            .ok()?;
        self.kernel_env
            .infer(&validation_locals.to_kernel_ctx(), delta, &expr)
            .ok()?;
        Some(replacement)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct UniverseArgCounts {
    expected: usize,
    actual: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RepairUniverseLevel {
    level: Level,
    source: String,
}

impl RepairUniverseLevel {
    fn new(level: Level) -> Option<Self> {
        Some(Self {
            source: level_repair_source(&level)?,
            level,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum InsertedTypeArgumentRepair {
    NotNeeded,
    Source(String),
    Unavailable,
}

fn machine_app_spine<'a>(
    func: &'a MachineTerm,
    arg: &'a MachineTerm,
) -> (&'a MachineTerm, Vec<&'a MachineTerm>) {
    let mut head = func;
    let mut args = vec![arg];
    while let MachineTerm::App {
        func: nested_func,
        arg: nested_arg,
        ..
    } = head
    {
        args.push(nested_arg);
        head = nested_func;
    }
    args.reverse();
    (head, args)
}

fn explicit_universe_replacement(name: &str, expected: usize, delta: &[String]) -> Option<String> {
    let levels = explicit_universe_level_args(expected, delta)?;
    let levels: Vec<_> = levels.into_iter().map(|level| level.source).collect();
    Some(format!("@{}.{{{}}}", name, levels.join(", ")))
}

fn explicit_universe_level_args(
    expected: usize,
    delta: &[String],
) -> Option<Vec<RepairUniverseLevel>> {
    if expected == 0 || delta.len() < expected {
        return None;
    }

    Some(
        delta[..expected]
            .iter()
            .map(|name| RepairUniverseLevel {
                level: Level::param(name.clone()),
                source: name.clone(),
            })
            .collect(),
    )
}

fn machine_term_repair_source(term: &MachineTerm) -> Option<String> {
    match term {
        MachineTerm::Ident {
            name,
            universe_args,
            explicit_mode,
            ..
        } => {
            let mut source = if *explicit_mode {
                format!("@{}", name.as_dotted())
            } else {
                name.as_dotted()
            };
            if let Some(universe_args) = universe_args {
                let levels = universe_args
                    .iter()
                    .map(machine_level_repair_source)
                    .collect::<Option<Vec<_>>>()?;
                source.push_str(&format!(".{{{}}}", levels.join(", ")));
            }
            Some(source)
        }
        MachineTerm::Local { name, .. } => Some(name.clone()),
        MachineTerm::Prop { .. } => Some("Prop".to_owned()),
        MachineTerm::Type { level, .. } => Some(type_repair_source(level)),
        MachineTerm::Sort { level, .. } => {
            Some(format!("Sort {}", machine_level_repair_source(level)?))
        }
        MachineTerm::App { .. } => {
            let (head, args) = collect_machine_term_apps(term);
            let mut parts = vec![machine_term_repair_source(head)?];
            for arg in args {
                parts.push(machine_term_atom_repair_source(arg)?);
            }
            Some(parts.join(" "))
        }
        MachineTerm::Lam { .. } | MachineTerm::Pi { .. } | MachineTerm::Let { .. } => None,
        MachineTerm::Annot { expr, ty, .. } => Some(format!(
            "({} : {})",
            machine_term_repair_source(expr)?,
            machine_term_repair_source(ty)?
        )),
    }
}

fn machine_term_atom_repair_source(term: &MachineTerm) -> Option<String> {
    match term {
        MachineTerm::Ident { .. }
        | MachineTerm::Local { .. }
        | MachineTerm::Prop { .. }
        | MachineTerm::Type { .. }
        | MachineTerm::Sort { .. }
        | MachineTerm::Annot { .. } => machine_term_repair_source(term),
        MachineTerm::App { .. } => Some(format!("({})", machine_term_repair_source(term)?)),
        MachineTerm::Lam { .. } | MachineTerm::Pi { .. } | MachineTerm::Let { .. } => None,
    }
}

fn localize_repair_term(term: MachineTerm, locals: &LocalContext) -> MachineTerm {
    match term {
        MachineTerm::Ident {
            name,
            universe_args: None,
            explicit_mode: false,
            span,
        } if name.parts.len() == 1 && locals.contains_name(&name.parts[0]) => MachineTerm::Local {
            name: name.parts[0].clone(),
            span,
        },
        MachineTerm::App { func, arg, span } => MachineTerm::App {
            func: Box::new(localize_repair_term(*func, locals)),
            arg: Box::new(localize_repair_term(*arg, locals)),
            span,
        },
        MachineTerm::Annot { expr, ty, span } => MachineTerm::Annot {
            expr: Box::new(localize_repair_term(*expr, locals)),
            ty: Box::new(localize_repair_term(*ty, locals)),
            span,
        },
        term => term,
    }
}

fn collect_machine_term_apps(term: &MachineTerm) -> (&MachineTerm, Vec<&MachineTerm>) {
    let mut args = Vec::new();
    let mut head = term;
    while let MachineTerm::App { func, arg, .. } = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();
    (head, args)
}

fn expr_repair_source(expr: &Expr, locals: &LocalContext) -> Option<String> {
    match expr {
        Expr::Sort(level) => Some(sort_level_repair_source(level)),
        Expr::BVar(index) => locals.name_for_bvar(*index).map(str::to_owned),
        Expr::Const { name, levels } => {
            if levels.is_empty() {
                Some(name.clone())
            } else {
                let levels = levels
                    .iter()
                    .map(level_repair_source)
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("@{}.{{{}}}", name, levels.join(", ")))
            }
        }
        Expr::App(_, _) => {
            let (head, args) = npa_kernel::expr::collect_apps(expr);
            let mut parts = vec![expr_repair_source(&head, locals)?];
            for arg in args {
                parts.push(expr_atom_repair_source(&arg, locals)?);
            }
            Some(parts.join(" "))
        }
        Expr::Lam { .. } | Expr::Pi { .. } | Expr::Let { .. } => None,
    }
}

fn expr_atom_repair_source(expr: &Expr, locals: &LocalContext) -> Option<String> {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => expr_repair_source(expr, locals),
        Expr::App(_, _) => Some(format!("({})", expr_repair_source(expr, locals)?)),
        Expr::Lam { .. } | Expr::Pi { .. } | Expr::Let { .. } => None,
    }
}

fn type_repair_source(level: &MachineLevel) -> String {
    match machine_level_repair_source(level).as_deref() {
        Some("0") => "Type".to_owned(),
        Some(level) => format!("Type {level}"),
        None => "Type 0".to_owned(),
    }
}

fn sort_level_repair_source(level: &Level) -> String {
    match level_repair_source(level).as_deref() {
        Some("0") => "Prop".to_owned(),
        Some("1") => "Type".to_owned(),
        Some(level) => format!("Sort {level}"),
        None => "Sort 0".to_owned(),
    }
}

fn machine_level_repair_source(level: &MachineLevel) -> Option<String> {
    match level {
        MachineLevel::Nat { value, .. } => Some(value.to_string()),
        MachineLevel::Param { name, .. } => Some(name.clone()),
        MachineLevel::Succ { level, .. } => Some(format!(
            "succ {}",
            machine_level_atom_repair_source(level.as_ref())?
        )),
        MachineLevel::Max { lhs, rhs, .. } => Some(format!(
            "max {} {}",
            machine_level_atom_repair_source(lhs.as_ref())?,
            machine_level_atom_repair_source(rhs.as_ref())?
        )),
        MachineLevel::IMax { lhs, rhs, .. } => Some(format!(
            "imax {} {}",
            machine_level_atom_repair_source(lhs.as_ref())?,
            machine_level_atom_repair_source(rhs.as_ref())?
        )),
    }
}

fn machine_level_atom_repair_source(level: &MachineLevel) -> Option<String> {
    match level {
        MachineLevel::Nat { .. } | MachineLevel::Param { .. } => machine_level_repair_source(level),
        MachineLevel::Succ { .. } | MachineLevel::Max { .. } | MachineLevel::IMax { .. } => {
            Some(machine_level_repair_source(level)?)
        }
    }
}

fn level_repair_source(level: &Level) -> Option<String> {
    let level = npa_kernel::level::normalize_level(level.clone());
    if let Some(value) = level_as_u64(&level) {
        return Some(value.to_string());
    }

    match level {
        Level::Zero => Some("0".to_owned()),
        Level::Param(name) => Some(name),
        Level::Succ(level) => Some(format!("succ {}", level_repair_source(&level)?)),
        Level::Max(lhs, rhs) => Some(format!(
            "max {} {}",
            level_repair_source(&lhs)?,
            level_repair_source(&rhs)?
        )),
        Level::IMax(lhs, rhs) => Some(format!(
            "imax {} {}",
            level_repair_source(&lhs)?,
            level_repair_source(&rhs)?
        )),
    }
}

fn level_as_u64(level: &Level) -> Option<u64> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(level) => Some(level_as_u64(level)? + 1),
        _ => None,
    }
}

fn elaborate_machine_term_infer(
    term: MachineTerm,
    span: crate::Span,
    context: &MachineTermElabContext,
    repair_mode: bool,
) -> Result<(
    Expr,
    Expr,
    Elaborator,
    LocalContext,
    Vec<MachineResolvedConstant>,
)> {
    let resolver = TermResolver::new(&context.global_scope, repair_mode);
    let mut local_scope = LocalScope::from_machine_locals(&context.local_context);
    for local in &context.local_context {
        resolver.ensure_local_does_not_shadow_global(&local.name, span)?;
    }
    let universe_params: BTreeSet<_> = context.universe_params.iter().cloned().collect();
    let resolved = resolver.resolve_term(term, &mut local_scope, &universe_params)?;
    let constants = resolver.constants_from_resolved_term(&resolved)?;
    let mut locals = local_context_from_machine(&context.local_context);
    let elaborator = Elaborator::from_term_context(context, &constants, span, repair_mode)?;
    let expr = elaborator.elaborate_term(resolved, &mut locals, &context.universe_params)?;
    let inferred_type = elaborator.infer_expr(&expr, &locals, &context.universe_params, span)?;
    Ok((expr, inferred_type, elaborator, locals, constants))
}

struct TermResolver {
    globals: TermGlobalTable,
    repair_mode: bool,
}

impl TermResolver {
    fn new(scope: &MachineGlobalScope, repair_mode: bool) -> Self {
        Self {
            globals: TermGlobalTable::new(scope),
            repair_mode,
        }
    }

    fn resolve_term(
        &self,
        term: MachineTerm,
        locals: &mut LocalScope,
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
                    resolved_binders.push(self.resolve_binder(
                        binder,
                        &mut nested_locals,
                        universe_params,
                    )?);
                }
                Ok(MachineTerm::Lam {
                    binders: resolved_binders,
                    body: Box::new(self.resolve_term(
                        *body,
                        &mut nested_locals,
                        universe_params,
                    )?),
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
                    resolved_binders.push(self.resolve_binder(
                        binder,
                        &mut nested_locals,
                        universe_params,
                    )?);
                }
                Ok(MachineTerm::Pi {
                    binders: resolved_binders,
                    body: Box::new(self.resolve_term(
                        *body,
                        &mut nested_locals,
                        universe_params,
                    )?),
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
                    body: Box::new(self.resolve_term(
                        *body,
                        &mut nested_locals,
                        universe_params,
                    )?),
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

    fn resolve_ident(
        &self,
        name: crate::MachineName,
        universe_args: Option<Vec<MachineLevel>>,
        explicit_mode: bool,
        span: crate::Span,
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
            TermGlobalLookup::Resolved => Ok(MachineTerm::Ident {
                name,
                universe_args,
                explicit_mode,
                span,
            }),
            TermGlobalLookup::Ambiguous => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::AmbiguousGlobalName,
                name.span,
                format!(
                    "global name {} is exported more than once",
                    name.as_dotted()
                ),
            )),
            TermGlobalLookup::ShortGlobal => Err(self.short_global_diagnostic(&name)),
            TermGlobalLookup::UnknownLocal => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnknownLocalName,
                name.span,
                format!("unknown local name {}", name.as_dotted()),
            )),
            TermGlobalLookup::UnknownGlobal => Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnknownGlobalName,
                name.span,
                format!("unknown global name {}", name.as_dotted()),
            )),
        }
    }

    fn short_global_diagnostic(&self, name: &crate::MachineName) -> MachineDiagnostic {
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

    fn constants_from_resolved_term(
        &self,
        term: &MachineTerm,
    ) -> Result<Vec<MachineResolvedConstant>> {
        let mut constants = BTreeSet::new();
        self.collect_constants_from_resolved_term(term, &mut constants)?;
        Ok(constants.into_iter().collect())
    }

    fn collect_constants_from_resolved_term(
        &self,
        term: &MachineTerm,
        constants: &mut BTreeSet<MachineResolvedConstant>,
    ) -> Result<()> {
        match term {
            MachineTerm::Ident { name, span, .. } => {
                let Some(constant) = self.globals.resolved_constant(name) else {
                    return Err(MachineDiagnostic::error(
                        MachineDiagnosticKind::UnknownGlobalName,
                        *span,
                        format!(
                            "resolved global name {} lost its declaration hash",
                            name.as_dotted()
                        ),
                    ));
                };
                constants.insert(constant);
            }
            MachineTerm::Local { .. }
            | MachineTerm::Prop { .. }
            | MachineTerm::Type { .. }
            | MachineTerm::Sort { .. } => {}
            MachineTerm::App { func, arg, .. } => {
                self.collect_constants_from_resolved_term(func, constants)?;
                self.collect_constants_from_resolved_term(arg, constants)?;
            }
            MachineTerm::Lam { binders, body, .. } | MachineTerm::Pi { binders, body, .. } => {
                for binder in binders {
                    self.collect_constants_from_resolved_term(&binder.ty, constants)?;
                }
                self.collect_constants_from_resolved_term(body, constants)?;
            }
            MachineTerm::Let {
                ty, value, body, ..
            } => {
                self.collect_constants_from_resolved_term(ty, constants)?;
                self.collect_constants_from_resolved_term(value, constants)?;
                self.collect_constants_from_resolved_term(body, constants)?;
            }
            MachineTerm::Annot { expr, ty, .. } => {
                self.collect_constants_from_resolved_term(expr, constants)?;
                self.collect_constants_from_resolved_term(ty, constants)?;
            }
        }
        Ok(())
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

    fn ensure_local_does_not_shadow_global(&self, name: &str, span: crate::Span) -> Result<()> {
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
struct TermGlobalTable {
    names: BTreeMap<String, TermGlobalEntry>,
    roots: BTreeSet<String>,
    suffixes: BTreeSet<String>,
    suffix_candidates: BTreeMap<String, BTreeSet<MachineRepairCandidate>>,
}

impl TermGlobalTable {
    fn new(scope: &MachineGlobalScope) -> Self {
        let mut table = Self::default();
        for entry in &scope.entries {
            table.add_name(entry);
        }
        table
    }

    fn add_name(&mut self, entry: &crate::MachineGlobalScopeEntry) {
        let name = entry.name();
        let dotted = name.as_dotted();
        match self.names.get_mut(&dotted) {
            Some(entry) => *entry = TermGlobalEntry::Ambiguous,
            None => {
                self.names.insert(
                    dotted,
                    TermGlobalEntry::Resolved {
                        decl_interface_hash: *entry.decl_interface_hash(),
                    },
                );
            }
        }

        if let Some(first) = name.0.first() {
            self.roots.insert(first.clone());
        }
        if let Some(last) = name.0.last() {
            self.suffixes.insert(last.clone());
            self.suffix_candidates
                .entry(last.clone())
                .or_default()
                .insert(MachineRepairCandidate {
                    name: name.clone(),
                    decl_interface_hash: Some(*entry.decl_interface_hash()),
                });
        }
    }

    fn lookup(&self, name: &crate::MachineName, force_global: bool) -> TermGlobalLookup {
        let dotted = name.as_dotted();
        match self.names.get(&dotted) {
            Some(TermGlobalEntry::Resolved {
                decl_interface_hash: _,
            }) => TermGlobalLookup::Resolved,
            Some(TermGlobalEntry::Ambiguous) => TermGlobalLookup::Ambiguous,
            None if name.parts.len() == 1 && self.suffixes.contains(&name.parts[0]) => {
                TermGlobalLookup::ShortGlobal
            }
            None if name.parts.len() == 1 && !force_global => TermGlobalLookup::UnknownLocal,
            None => TermGlobalLookup::UnknownGlobal,
        }
    }

    fn has_root(&self, name: &str) -> bool {
        self.roots.contains(name)
    }

    fn resolved_constant(&self, name: &crate::MachineName) -> Option<MachineResolvedConstant> {
        let dotted = name.as_dotted();
        match self.names.get(&dotted) {
            Some(TermGlobalEntry::Resolved {
                decl_interface_hash,
            }) => Some(MachineResolvedConstant {
                name: npa_cert::Name::from_dotted(&dotted),
                decl_interface_hash: *decl_interface_hash,
            }),
            Some(TermGlobalEntry::Ambiguous) | None => None,
        }
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
            Some(TermGlobalEntry::Resolved { .. })
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TermGlobalEntry {
    Resolved { decl_interface_hash: npa_cert::Hash },
    Ambiguous,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TermGlobalLookup {
    Resolved,
    Ambiguous,
    ShortGlobal,
    UnknownLocal,
    UnknownGlobal,
}

#[derive(Clone, Debug)]
enum CoreHashGlobalRef {
    Imported {
        import_index: u32,
        name: npa_cert::Name,
        decl_interface_hash: npa_cert::Hash,
    },
    CurrentModule {
        name: npa_cert::Name,
        source_index: u64,
        decl_interface_hash: npa_cert::Hash,
    },
    CurrentGenerated {
        parent_source_index: u64,
        name: npa_cert::Name,
        decl_interface_hash: npa_cert::Hash,
    },
}

fn hash_owner_free_core_expr(expr: &Expr) -> npa_cert::Hash {
    let mut payload = Vec::new();
    match expr {
        Expr::Sort(level) => {
            payload.push(0x00);
            payload.extend(hash_core_level(&npa_kernel::level::normalize_level(
                level.clone(),
            )));
        }
        Expr::BVar(index) => {
            payload.push(0x01);
            encode_uvar_to(&mut payload, *index as u64);
        }
        Expr::Const { name, levels } => {
            payload.push(0x02);
            encode_string_to(&mut payload, name);
            encode_uvar_to(&mut payload, levels.len() as u64);
            for level in levels {
                payload.extend(hash_core_level(&npa_kernel::level::normalize_level(
                    level.clone(),
                )));
            }
        }
        Expr::App(func, arg) => {
            payload.push(0x03);
            payload.extend(hash_owner_free_core_expr(func));
            payload.extend(hash_owner_free_core_expr(arg));
        }
        Expr::Lam { ty, body, .. } => {
            payload.push(0x04);
            payload.extend(hash_owner_free_core_expr(ty));
            payload.extend(hash_owner_free_core_expr(body));
        }
        Expr::Pi { ty, body, .. } => {
            payload.push(0x05);
            payload.extend(hash_owner_free_core_expr(ty));
            payload.extend(hash_owner_free_core_expr(body));
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            payload.push(0x06);
            payload.extend(hash_owner_free_core_expr(ty));
            payload.extend(hash_owner_free_core_expr(value));
            payload.extend(hash_owner_free_core_expr(body));
        }
    }

    hash_with_domain(b"NPA-KERNEL-CORE-EXPR-0.1", &payload)
}

fn hash_contextual_core_expr(
    expr: &Expr,
    context: &MachineTermElabContext,
    constants: &[MachineResolvedConstant],
    span: crate::Span,
) -> Result<npa_cert::Hash> {
    let mut refs = BTreeMap::new();
    for constant in constants {
        let name = constant.name.as_dotted();
        let Some(entry) = context.global_scope.entries.iter().find(|entry| {
            entry.name() == &constant.name
                && entry.decl_interface_hash() == &constant.decl_interface_hash
        }) else {
            return Err(import_resolution_diagnostic(
                span,
                format!("resolved global {name} is missing from the hash context"),
            ));
        };
        let global_ref = match entry {
            MachineGlobalScopeEntry::Imported {
                name,
                import_index,
                decl_interface_hash,
            } => CoreHashGlobalRef::Imported {
                import_index: *import_index,
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
            MachineGlobalScopeEntry::CurrentModule {
                name,
                source_index,
                decl_interface_hash,
            } => CoreHashGlobalRef::CurrentModule {
                name: name.clone(),
                source_index: *source_index,
                decl_interface_hash: *decl_interface_hash,
            },
            MachineGlobalScopeEntry::CurrentGenerated {
                name,
                parent_source_index,
                decl_interface_hash,
            } => CoreHashGlobalRef::CurrentGenerated {
                parent_source_index: *parent_source_index,
                name: name.clone(),
                decl_interface_hash: *decl_interface_hash,
            },
        };
        refs.insert(name, global_ref);
    }

    hash_contextual_core_expr_with_refs(expr, &refs, span)
}

fn hash_contextual_core_expr_with_refs(
    expr: &Expr,
    refs: &BTreeMap<String, CoreHashGlobalRef>,
    span: crate::Span,
) -> Result<npa_cert::Hash> {
    let mut payload = Vec::new();
    match expr {
        Expr::Sort(level) => {
            payload.push(0x00);
            payload.extend(hash_core_level(&npa_kernel::level::normalize_level(
                level.clone(),
            )));
        }
        Expr::BVar(index) => {
            payload.push(0x01);
            encode_uvar_to(&mut payload, *index as u64);
        }
        Expr::Const { name, levels } => {
            let Some(global_ref) = refs.get(name) else {
                return Err(import_resolution_diagnostic(
                    span,
                    format!("constant {name} is missing from the hash context"),
                ));
            };
            payload.push(0x02);
            encode_core_hash_global_ref_to(&mut payload, global_ref);
            encode_uvar_to(&mut payload, levels.len() as u64);
            for level in levels {
                payload.extend(hash_core_level(&npa_kernel::level::normalize_level(
                    level.clone(),
                )));
            }
        }
        Expr::App(func, arg) => {
            payload.push(0x03);
            payload.extend(hash_contextual_core_expr_with_refs(func, refs, span)?);
            payload.extend(hash_contextual_core_expr_with_refs(arg, refs, span)?);
        }
        Expr::Lam { ty, body, .. } => {
            payload.push(0x04);
            payload.extend(hash_contextual_core_expr_with_refs(ty, refs, span)?);
            payload.extend(hash_contextual_core_expr_with_refs(body, refs, span)?);
        }
        Expr::Pi { ty, body, .. } => {
            payload.push(0x05);
            payload.extend(hash_contextual_core_expr_with_refs(ty, refs, span)?);
            payload.extend(hash_contextual_core_expr_with_refs(body, refs, span)?);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            payload.push(0x06);
            payload.extend(hash_contextual_core_expr_with_refs(ty, refs, span)?);
            payload.extend(hash_contextual_core_expr_with_refs(value, refs, span)?);
            payload.extend(hash_contextual_core_expr_with_refs(body, refs, span)?);
        }
    }

    Ok(hash_with_domain(
        b"NPA-FRONTEND-MACHINE-TERM-CONTEXT-0.1",
        &payload,
    ))
}

fn hash_core_level(level: &Level) -> npa_cert::Hash {
    let mut payload = Vec::new();
    match level {
        Level::Zero => payload.push(0x00),
        Level::Succ(inner) => {
            payload.push(0x01);
            payload.extend(hash_core_level(inner));
        }
        Level::Max(lhs, rhs) => {
            payload.push(0x02);
            payload.extend(hash_core_level(lhs));
            payload.extend(hash_core_level(rhs));
        }
        Level::IMax(lhs, rhs) => {
            payload.push(0x03);
            payload.extend(hash_core_level(lhs));
            payload.extend(hash_core_level(rhs));
        }
        Level::Param(name) => {
            payload.push(0x04);
            encode_string_to(&mut payload, name);
        }
    }

    hash_with_domain(b"NPA-LEVEL-0.1", &payload)
}

fn encode_core_hash_global_ref_to(out: &mut Vec<u8>, global_ref: &CoreHashGlobalRef) {
    match global_ref {
        CoreHashGlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar_to(out, *import_index as u64);
            encode_name_to(out, name);
            out.extend(decl_interface_hash);
        }
        CoreHashGlobalRef::CurrentModule {
            name,
            source_index,
            decl_interface_hash,
        } => {
            out.push(0x01);
            encode_name_to(out, name);
            encode_uvar_to(out, *source_index);
            out.extend(decl_interface_hash);
        }
        CoreHashGlobalRef::CurrentGenerated {
            parent_source_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x02);
            encode_uvar_to(out, *parent_source_index);
            encode_name_to(out, name);
            out.extend(decl_interface_hash);
        }
    }
}

fn encode_name_to(out: &mut Vec<u8>, name: &npa_cert::Name) {
    encode_uvar_to(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string_to(out, component);
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_uvar_to(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_uvar_to(out: &mut Vec<u8>, mut value: u64) {
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

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> npa_cert::Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn local_context_from_machine(locals: &[MachineLocalDecl]) -> LocalContext {
    let mut context = LocalContext::default();
    for local in locals {
        match &local.value {
            Some(value) => {
                context.push_definition(local.name.clone(), local.ty.clone(), value.clone())
            }
            None => context.push_assumption(local.name.clone(), local.ty.clone()),
        }
    }
    context
}

fn active_verified_imports<'a>(
    items: &[MachineItem],
    verified_imports: &'a [VerifiedImport],
) -> Result<Vec<&'a VerifiedImport>> {
    active_verified_import_indices(items, verified_imports).map(|indices| {
        indices
            .into_iter()
            .map(|index| &verified_imports[index])
            .collect()
    })
}

fn active_verified_import_indices(
    items: &[MachineItem],
    verified_imports: &[VerifiedImport],
) -> Result<Vec<usize>> {
    let mut seen = BTreeSet::new();
    let mut imports = Vec::new();

    for item in items {
        let MachineItem::Import { module, span } = item else {
            continue;
        };
        let module_name = npa_cert::Name(module.parts.clone());
        if seen.insert(module_name.clone()) {
            imports.push(find_verified_import_index(
                verified_imports,
                &module_name,
                *span,
            )?);
        }
    }

    Ok(imports)
}

fn find_verified_import_index(
    verified_imports: &[VerifiedImport],
    module_name: &npa_cert::ModuleName,
    span: crate::Span,
) -> Result<usize> {
    let mut matches = verified_imports
        .iter()
        .enumerate()
        .filter(|(_, import)| &import.module == module_name);
    let Some((first_index, first)) = matches.next() else {
        return Err(MachineDiagnostic::error(
            MachineDiagnosticKind::MissingVerifiedImport,
            span,
            format!(
                "import {} is not present in the verified import set",
                module_name.as_dotted()
            ),
        ));
    };

    if matches.any(|(_, import)| import != first) {
        return Err(MachineDiagnostic::error(
            MachineDiagnosticKind::ImportResolutionError,
            span,
            format!(
                "import {} has multiple verified interfaces",
                module_name.as_dotted()
            ),
        ));
    }

    Ok(first_index)
}

#[cfg(test)]
pub(crate) fn certificate_imports_for_module(
    module: &npa_cert::CoreModule,
    active_import_indices: &[usize],
    verified_modules: &[npa_cert::VerifiedModule],
    file_id: crate::FileId,
) -> Result<Vec<npa_cert::VerifiedModule>> {
    certificate_import_refs_for_module(module, active_import_indices, verified_modules, file_id)
        .map(|imports| imports.into_iter().cloned().collect())
}

pub(crate) fn certificate_import_refs_for_module<'a>(
    module: &npa_cert::CoreModule,
    active_import_indices: &[usize],
    verified_modules: &'a [npa_cert::VerifiedModule],
    file_id: crate::FileId,
) -> Result<Vec<&'a npa_cert::VerifiedModule>> {
    let verified_module_refs = verified_modules.iter().collect::<Vec<_>>();
    certificate_import_refs_for_module_refs(
        module,
        active_import_indices,
        &verified_module_refs,
        file_id,
    )
}

pub(crate) fn certificate_import_refs_for_module_refs<'a>(
    module: &npa_cert::CoreModule,
    active_import_indices: &[usize],
    verified_modules: &[&'a npa_cert::VerifiedModule],
    file_id: crate::FileId,
) -> Result<Vec<&'a npa_cert::VerifiedModule>> {
    certificate_import_selection_for_module_refs(
        module,
        active_import_indices,
        verified_modules,
        file_id,
    )
    .map(|selection| {
        selection
            .indices
            .into_iter()
            .map(|index| verified_modules[index])
            .collect()
    })
}

pub(crate) fn certificate_import_refs_and_providers_for_module_refs<'a>(
    module: &npa_cert::CoreModule,
    active_import_indices: &[usize],
    verified_modules: &[&'a npa_cert::VerifiedModule],
    file_id: crate::FileId,
) -> Result<(
    Vec<&'a npa_cert::VerifiedModule>,
    BTreeMap<npa_cert::Name, npa_cert::ImportEntry>,
)> {
    certificate_import_selection_for_module_refs(
        module,
        active_import_indices,
        verified_modules,
        file_id,
    )
    .map(|selection| {
        (
            selection
                .indices
                .into_iter()
                .map(|index| verified_modules[index])
                .collect(),
            selection.preferred_imports,
        )
    })
}

pub(crate) fn combined_verified_module_refs<'a>(
    direct_modules: &[&'a npa_cert::VerifiedModule],
    available_modules: &[&'a npa_cert::VerifiedModule],
) -> Vec<&'a npa_cert::VerifiedModule> {
    let mut seen = BTreeSet::new();
    let mut combined = Vec::new();
    for module in direct_modules
        .iter()
        .chain(available_modules.iter())
        .copied()
    {
        let key = (
            module.module().clone(),
            module.export_hash(),
            module.certificate_hash(),
        );
        if seen.insert(key) {
            combined.push(module);
        }
    }
    combined
}

struct CertificateImportSelection {
    indices: Vec<usize>,
    preferred_imports: BTreeMap<npa_cert::Name, npa_cert::ImportEntry>,
}

fn certificate_import_selection_for_module_refs(
    module: &npa_cert::CoreModule,
    active_import_indices: &[usize],
    verified_modules: &[&npa_cert::VerifiedModule],
    file_id: crate::FileId,
) -> Result<CertificateImportSelection> {
    let span = crate::Span::empty(file_id);
    let referenced_exports = referenced_import_names(module);
    let mut selected = BTreeSet::new();
    let mut pending = Vec::new();
    let mut scanned_exports = BTreeSet::new();
    let mut preferred_imports = BTreeMap::new();

    for index in active_import_indices.iter().copied() {
        selected.insert(index);
        let import = verified_modules.get(index).copied().ok_or_else(|| {
            import_resolution_diagnostic(span, "verified import index is out of bounds")
        })?;
        enqueue_referenced_import_exports(
            index,
            import,
            &referenced_exports,
            &mut pending,
            &mut preferred_imports,
            span,
        )?;
    }

    while let Some(export) = pending.pop() {
        selected.insert(export.import_index);
        if !scanned_exports.insert(export.clone()) {
            continue;
        }

        let import = verified_modules
            .get(export.import_index)
            .copied()
            .ok_or_else(|| {
                import_resolution_diagnostic(span, "verified import index is out of bounds")
            })?;
        let entry = find_verified_module_export_entry(import, &export, span)?;
        for dependency in export_interface_dependency_targets(import, entry, span)? {
            let dependency_index =
                find_verified_module_export_ref(verified_modules, &dependency, span)?;
            let dependency_import = verified_modules[dependency_index];
            record_preferred_import(
                &mut preferred_imports,
                dependency.name.clone(),
                dependency_import,
                false,
                span,
            )?;
            pending.push(PendingCertificateImportExport {
                import_index: dependency_index,
                name: dependency.name.clone(),
                hash: dependency.hash,
            });
        }

        for dependency in export_axiom_dependency_targets(import, entry, span)? {
            let dependency_index =
                find_verified_module_axiom_export_ref(verified_modules, &dependency, span)?;
            let dependency_import = verified_modules[dependency_index];
            record_preferred_import(
                &mut preferred_imports,
                dependency.name.clone(),
                dependency_import,
                false,
                span,
            )?;
            pending.push(PendingCertificateImportExport {
                import_index: dependency_index,
                name: dependency.name.clone(),
                hash: dependency.hash,
            });
        }
    }

    Ok(CertificateImportSelection {
        indices: selected.into_iter().collect(),
        preferred_imports,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PendingCertificateImportExport {
    import_index: usize,
    name: npa_cert::Name,
    hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportDependencyTarget {
    import: Option<ImportDependencySource>,
    name: npa_cert::Name,
    hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportDependencySource {
    module: npa_cert::ModuleName,
    export_hash: npa_cert::Hash,
    certificate_hash: Option<npa_cert::Hash>,
}

fn enqueue_referenced_import_exports(
    index: usize,
    module: &npa_cert::VerifiedModule,
    referenced_exports: &BTreeSet<npa_cert::Name>,
    pending: &mut Vec<PendingCertificateImportExport>,
    preferred_imports: &mut BTreeMap<npa_cert::Name, npa_cert::ImportEntry>,
    span: crate::Span,
) -> Result<()> {
    for entry in module.export_block() {
        let entry_name = module.name_table().get(entry.name).ok_or_else(|| {
            import_resolution_diagnostic(span, "verified import export name is missing")
        })?;
        if referenced_exports.contains(entry_name) {
            record_preferred_import(preferred_imports, entry_name.clone(), module, false, span)?;
            pending.push(PendingCertificateImportExport {
                import_index: index,
                name: entry_name.clone(),
                hash: entry.decl_interface_hash,
            });
        }
    }
    Ok(())
}

fn record_preferred_import(
    preferred_imports: &mut BTreeMap<npa_cert::Name, npa_cert::ImportEntry>,
    name: npa_cert::Name,
    module: &npa_cert::VerifiedModule,
    reject_conflict: bool,
    span: crate::Span,
) -> Result<()> {
    let entry = npa_cert::ImportEntry {
        module: module.module().clone(),
        export_hash: module.export_hash(),
        certificate_hash: Some(module.certificate_hash()),
    };
    match preferred_imports.entry(name.clone()) {
        std::collections::btree_map::Entry::Vacant(slot) => {
            slot.insert(entry);
            Ok(())
        }
        std::collections::btree_map::Entry::Occupied(existing) if existing.get() == &entry => {
            Ok(())
        }
        std::collections::btree_map::Entry::Occupied(_) if !reject_conflict => Ok(()),
        std::collections::btree_map::Entry::Occupied(_) => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {} has multiple selected providers",
                name.as_dotted()
            ),
        )),
    }
}

fn find_verified_module_export_entry<'a>(
    module: &'a npa_cert::VerifiedModule,
    export: &PendingCertificateImportExport,
    span: crate::Span,
) -> Result<&'a npa_cert::ExportEntry> {
    let matches = module
        .export_block()
        .iter()
        .filter(|entry| {
            entry.decl_interface_hash == export.hash
                && module
                    .name_table()
                    .get(entry.name)
                    .is_some_and(|entry_name| entry_name == &export.name)
        })
        .collect::<Vec<_>>();

    match matches.as_slice() {
        [entry] => Ok(*entry),
        [] => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {} is missing from the selected import",
                export.name.as_dotted()
            ),
        )),
        _ => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {} has multiple matching exports in the selected import",
                export.name.as_dotted()
            ),
        )),
    }
}

fn export_interface_dependency_targets(
    module: &npa_cert::VerifiedModule,
    entry: &npa_cert::ExportEntry,
    span: crate::Span,
) -> Result<BTreeSet<ImportDependencyTarget>> {
    let mut dependencies = BTreeSet::new();
    let mut scanned_exports = BTreeSet::new();
    collect_export_interface_dependency_targets(
        module,
        entry,
        &mut dependencies,
        &mut scanned_exports,
        span,
    )?;
    Ok(dependencies)
}

fn collect_export_interface_dependency_targets(
    module: &npa_cert::VerifiedModule,
    entry: &npa_cert::ExportEntry,
    dependencies: &mut BTreeSet<ImportDependencyTarget>,
    scanned_exports: &mut BTreeSet<(npa_cert::NameId, npa_cert::Hash)>,
    span: crate::Span,
) -> Result<()> {
    if !scanned_exports.insert((entry.name, entry.decl_interface_hash)) {
        return Ok(());
    }

    match entry.kind {
        npa_cert::ExportKind::Inductive
        | npa_cert::ExportKind::Constructor
        | npa_cert::ExportKind::Recursor => {
            let decl_index = source_decl_index_for_verified_export(module, entry, span)?;
            let decl = module.declarations().get(decl_index).ok_or_else(|| {
                import_resolution_diagnostic(span, "verified import declaration is missing")
            })?;
            for term in verified_decl_term_ids(&decl.decl) {
                collect_imported_dependency_targets_from_term(
                    module,
                    term,
                    dependencies,
                    scanned_exports,
                    Some(decl_index),
                    span,
                )?;
            }
        }
        npa_cert::ExportKind::Axiom | npa_cert::ExportKind::Theorem | npa_cert::ExportKind::Def => {
            collect_imported_dependency_targets_from_term(
                module,
                entry.ty,
                dependencies,
                scanned_exports,
                None,
                span,
            )?;
            if let Some(body) = entry.body {
                collect_imported_dependency_targets_from_term(
                    module,
                    body,
                    dependencies,
                    scanned_exports,
                    None,
                    span,
                )?;
            }
        }
    }
    Ok(())
}

fn collect_imported_dependency_targets_from_term(
    module: &npa_cert::VerifiedModule,
    term: npa_cert::TermId,
    dependencies: &mut BTreeSet<ImportDependencyTarget>,
    scanned_exports: &mut BTreeSet<(npa_cert::NameId, npa_cert::Hash)>,
    skip_local_decl_index: Option<usize>,
    span: crate::Span,
) -> Result<()> {
    match module
        .term_table()
        .get(term)
        .ok_or_else(|| import_resolution_diagnostic(span, "verified import term is missing"))?
    {
        npa_cert::TermNode::Sort(_) | npa_cert::TermNode::BVar(_) => {}
        npa_cert::TermNode::Const { global_ref, .. } => match global_ref {
            npa_cert::GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
                ..
            } => {
                let import = module.imports().get(*import_index).ok_or_else(|| {
                    import_resolution_diagnostic(
                        span,
                        "verified import dependency index is missing",
                    )
                })?;
                dependencies.insert(ImportDependencyTarget {
                    import: Some(ImportDependencySource {
                        module: import.module.clone(),
                        export_hash: import.export_hash,
                        certificate_hash: import.certificate_hash,
                    }),
                    name: module
                        .name_table()
                        .get(*name)
                        .ok_or_else(|| {
                            import_resolution_diagnostic(span, "verified import name is missing")
                        })?
                        .clone(),
                    hash: *decl_interface_hash,
                });
            }
            npa_cert::GlobalRef::Builtin { .. } => {}
            npa_cert::GlobalRef::Local { decl_index } => {
                if Some(*decl_index) != skip_local_decl_index {
                    let local_entry =
                        find_verified_module_local_export_entry(module, *decl_index, span)?;
                    collect_export_interface_dependency_targets(
                        module,
                        local_entry,
                        dependencies,
                        scanned_exports,
                        span,
                    )?;
                }
            }
            npa_cert::GlobalRef::LocalGenerated {
                decl_index, name, ..
            } => {
                if Some(*decl_index) != skip_local_decl_index {
                    let local_entry = find_verified_module_local_generated_export_entry(
                        module,
                        *decl_index,
                        *name,
                        span,
                    )?;
                    collect_export_interface_dependency_targets(
                        module,
                        local_entry,
                        dependencies,
                        scanned_exports,
                        span,
                    )?;
                }
            }
        },
        npa_cert::TermNode::App(func, arg) => {
            collect_imported_dependency_targets_from_term(
                module,
                *func,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
            collect_imported_dependency_targets_from_term(
                module,
                *arg,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
        }
        npa_cert::TermNode::Lam { ty, body } | npa_cert::TermNode::Pi { ty, body } => {
            collect_imported_dependency_targets_from_term(
                module,
                *ty,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
            collect_imported_dependency_targets_from_term(
                module,
                *body,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
        }
        npa_cert::TermNode::Let { ty, value, body } => {
            collect_imported_dependency_targets_from_term(
                module,
                *ty,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
            collect_imported_dependency_targets_from_term(
                module,
                *value,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
            collect_imported_dependency_targets_from_term(
                module,
                *body,
                dependencies,
                scanned_exports,
                skip_local_decl_index,
                span,
            )?;
        }
    }
    Ok(())
}

fn source_decl_index_for_verified_export(
    module: &npa_cert::VerifiedModule,
    entry: &npa_cert::ExportEntry,
    span: crate::Span,
) -> Result<usize> {
    let matches = module
        .declarations()
        .iter()
        .enumerate()
        .filter_map(|(index, decl)| {
            verified_decl_export_name_ids(&decl.decl)
                .contains(&entry.name)
                .then_some(index)
        })
        .collect::<Vec<_>>();

    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(import_resolution_diagnostic(
            span,
            "verified import export source declaration is missing",
        )),
        _ => Err(import_resolution_diagnostic(
            span,
            "verified import export has multiple source declarations",
        )),
    }
}

fn find_verified_module_local_export_entry(
    module: &npa_cert::VerifiedModule,
    decl_index: usize,
    span: crate::Span,
) -> Result<&npa_cert::ExportEntry> {
    let decl = module.declarations().get(decl_index).ok_or_else(|| {
        import_resolution_diagnostic(span, "verified import local declaration is missing")
    })?;
    let name = verified_decl_primary_name(&decl.decl);
    let hash = decl.hashes.decl_interface_hash;
    module
        .export_block()
        .iter()
        .find(|entry| entry.name == name && entry.decl_interface_hash == hash)
        .ok_or_else(|| {
            import_resolution_diagnostic(span, "verified import local export is missing")
        })
}

fn find_verified_module_local_generated_export_entry(
    module: &npa_cert::VerifiedModule,
    _decl_index: usize,
    name: npa_cert::NameId,
    span: crate::Span,
) -> Result<&npa_cert::ExportEntry> {
    let matches = module
        .export_block()
        .iter()
        .filter(|entry| entry.name == name)
        .collect::<Vec<_>>();

    match matches.as_slice() {
        [entry] => Ok(*entry),
        [] => Err(import_resolution_diagnostic(
            span,
            "verified import local generated export is missing",
        )),
        _ => Err(import_resolution_diagnostic(
            span,
            "verified import local generated export is ambiguous",
        )),
    }
}

fn verified_decl_primary_name(decl: &npa_cert::DeclPayload) -> npa_cert::NameId {
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

fn verified_decl_export_name_ids(decl: &npa_cert::DeclPayload) -> Vec<npa_cert::NameId> {
    let mut names = vec![verified_decl_primary_name(decl)];
    match decl {
        npa_cert::DeclPayload::Inductive {
            constructors,
            recursor,
            ..
        }
        | npa_cert::DeclPayload::InductiveConstrained {
            constructors,
            recursor,
            ..
        } => {
            names.extend(constructors.iter().map(|constructor| constructor.name));
            if let Some(recursor) = recursor {
                names.push(recursor.name);
            }
        }
        npa_cert::DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                names.push(inductive.name);
                names.extend(
                    inductive
                        .constructors
                        .iter()
                        .map(|constructor| constructor.name),
                );
                if let Some(recursor) = &inductive.recursor {
                    names.push(recursor.name);
                }
            }
        }
        _ => {}
    }
    names
}

fn verified_decl_term_ids(decl: &npa_cert::DeclPayload) -> Vec<npa_cert::TermId> {
    match decl {
        npa_cert::DeclPayload::Axiom { ty, .. }
        | npa_cert::DeclPayload::AxiomConstrained { ty, .. } => vec![*ty],
        npa_cert::DeclPayload::Def { ty, value, .. }
        | npa_cert::DeclPayload::DefConstrained { ty, value, .. } => vec![*ty, *value],
        npa_cert::DeclPayload::Theorem { ty, proof, .. }
        | npa_cert::DeclPayload::TheoremConstrained { ty, proof, .. } => vec![*ty, *proof],
        npa_cert::DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | npa_cert::DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => params
            .iter()
            .map(|param| param.ty)
            .chain(indices.iter().map(|index| index.ty))
            .chain(constructors.iter().map(|constructor| constructor.ty))
            .chain(recursor.iter().map(|recursor| recursor.ty))
            .collect(),
        npa_cert::DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
            .iter()
            .flat_map(|inductive| {
                inductive
                    .params
                    .iter()
                    .map(|param| param.ty)
                    .chain(inductive.indices.iter().map(|index| index.ty))
                    .chain(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.ty),
                    )
                    .chain(inductive.recursor.iter().map(|recursor| recursor.ty))
            })
            .collect(),
    }
}

fn export_axiom_dependency_targets(
    module: &npa_cert::VerifiedModule,
    entry: &npa_cert::ExportEntry,
    span: crate::Span,
) -> Result<BTreeSet<ImportDependencyTarget>> {
    let mut dependencies = BTreeSet::new();
    for axiom in &entry.axiom_dependencies {
        if matches!(axiom.global_ref, npa_cert::GlobalRef::Builtin { .. }) {
            continue;
        }
        let import = match &axiom.global_ref {
            npa_cert::GlobalRef::Imported { import_index, .. } => {
                let import = module.imports().get(*import_index).ok_or_else(|| {
                    import_resolution_diagnostic(
                        span,
                        "verified import axiom dependency index is missing",
                    )
                })?;
                Some(ImportDependencySource {
                    module: import.module.clone(),
                    export_hash: import.export_hash,
                    certificate_hash: import.certificate_hash,
                })
            }
            npa_cert::GlobalRef::Builtin { .. } => None,
            npa_cert::GlobalRef::Local { .. } | npa_cert::GlobalRef::LocalGenerated { .. } => {
                Some(ImportDependencySource {
                    module: module.module().clone(),
                    export_hash: module.export_hash(),
                    certificate_hash: Some(module.certificate_hash()),
                })
            }
        };
        dependencies.insert(ImportDependencyTarget {
            import,
            name: module
                .name_table()
                .get(axiom.name)
                .ok_or_else(|| {
                    import_resolution_diagnostic(span, "verified import axiom name is missing")
                })?
                .clone(),
            hash: axiom.decl_interface_hash,
        });
    }
    Ok(dependencies)
}

fn find_verified_module_export_ref(
    verified_modules: &[&npa_cert::VerifiedModule],
    dependency: &ImportDependencyTarget,
    span: crate::Span,
) -> Result<usize> {
    find_verified_module_export_by(verified_modules, dependency, None, span)
}

fn find_verified_module_axiom_export_ref(
    verified_modules: &[&npa_cert::VerifiedModule],
    dependency: &ImportDependencyTarget,
    span: crate::Span,
) -> Result<usize> {
    find_verified_module_export_by(
        verified_modules,
        dependency,
        Some(npa_cert::ExportKind::Axiom),
        span,
    )
}

fn find_verified_module_export_by(
    verified_modules: &[&npa_cert::VerifiedModule],
    dependency: &ImportDependencyTarget,
    kind: Option<npa_cert::ExportKind>,
    span: crate::Span,
) -> Result<usize> {
    let matches = verified_modules
        .iter()
        .enumerate()
        .filter_map(|(index, module)| {
            if !dependency_source_matches_module(dependency.import.as_ref(), module) {
                return None;
            }
            module
                .export_block()
                .iter()
                .any(|entry| {
                    kind.is_none_or(|kind| entry.kind == kind)
                        && entry.decl_interface_hash == dependency.hash
                        && module
                            .name_table()
                            .get(entry.name)
                            .is_some_and(|entry_name| entry_name == &dependency.name)
                })
                .then_some(index)
        })
        .collect::<Vec<_>>();

    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {} is not present in the verified import set",
                dependency.name.as_dotted()
            ),
        )),
        _ => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {} has multiple matching providers in the verified import set",
                dependency.name.as_dotted()
            ),
        )),
    }
}

fn dependency_source_matches_module(
    source: Option<&ImportDependencySource>,
    module: &npa_cert::VerifiedModule,
) -> bool {
    let Some(source) = source else {
        return true;
    };
    module.module() == &source.module
        && module.export_hash() == source.export_hash
        && source
            .certificate_hash
            .is_none_or(|hash| module.certificate_hash() == hash)
}

fn referenced_import_names(module: &npa_cert::CoreModule) -> BTreeSet<npa_cert::Name> {
    let mut names = BTreeSet::new();
    for decl in &module.declarations {
        collect_const_names_from_decl(&mut names, decl);
    }

    for name in local_public_names(module) {
        names.remove(&name);
    }

    names
}

fn local_public_names(module: &npa_cert::CoreModule) -> Vec<npa_cert::Name> {
    let mut names = Vec::new();
    for decl in &module.declarations {
        names.push(npa_cert::Name::from_dotted(decl.name()));
        match decl {
            Decl::Inductive { data, .. } => {
                names.extend(
                    data.constructors
                        .iter()
                        .map(|constructor| npa_cert::Name::from_dotted(&constructor.name)),
                );
                if let Some(recursor) = &data.recursor {
                    names.push(npa_cert::Name::from_dotted(&recursor.name));
                }
            }
            Decl::MutualInductiveBlock { data, .. } => {
                for inductive in &data.inductives {
                    names.push(npa_cert::Name::from_dotted(&inductive.name));
                    names.extend(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| npa_cert::Name::from_dotted(&constructor.name)),
                    );
                    if let Some(recursor) = &inductive.recursor {
                        names.push(npa_cert::Name::from_dotted(&recursor.name));
                    }
                }
            }
            _ => {}
        }
    }
    names
}

fn collect_const_names_from_decl(names: &mut BTreeSet<npa_cert::Name>, decl: &Decl) {
    match decl {
        Decl::Axiom { ty, .. } | Decl::AxiomConstrained { ty, .. } => {
            collect_const_names_from_expr(names, ty)
        }
        Decl::Def { ty, value, .. } | Decl::DefConstrained { ty, value, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, value);
        }
        Decl::Theorem { ty, proof, .. } | Decl::TheoremConstrained { ty, proof, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, proof);
        }
        Decl::Inductive { data, .. } => {
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
        Decl::MutualInductiveBlock { data, .. } => {
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
        Decl::Constructor { ty, .. } | Decl::Recursor { ty, .. } => {
            collect_const_names_from_expr(names, ty);
        }
    }
}

fn collect_const_names_from_expr(names: &mut BTreeSet<npa_cert::Name>, expr: &Expr) {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            names.insert(npa_cert::Name::from_dotted(name));
        }
        Expr::App(func, arg) => {
            collect_const_names_from_expr(names, func);
            collect_const_names_from_expr(names, arg);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, body);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, value);
            collect_const_names_from_expr(names, body);
        }
    }
}

fn import_resolution_diagnostic(
    span: crate::Span,
    message: impl Into<String>,
) -> MachineDiagnostic {
    MachineDiagnostic::error(MachineDiagnosticKind::ImportResolutionError, span, message)
}

struct KernelEnvBuild {
    env: Env,
    loaded_available_interfaces: BTreeSet<DeclInterfaceKey>,
    loaded_available_decl_keys: BTreeSet<LoadedImportDeclKey>,
}

#[derive(Clone, Debug)]
struct ImportKernelDecl {
    decl: Decl,
    dependencies: BTreeMap<String, BTreeSet<VerifiedDependency>>,
    interfaces: BTreeSet<DeclInterfaceKey>,
    loaded_decl_keys: BTreeSet<LoadedImportDeclKey>,
}

impl PartialEq for ImportKernelDecl {
    fn eq(&self, other: &Self) -> bool {
        self.decl == other.decl
            && self.dependencies == other.dependencies
            && self.interfaces == other.interfaces
    }
}

impl Eq for ImportKernelDecl {}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DeclInterfaceKey {
    name: String,
    decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportDeclInterfaceKey {
    import_key: ImportKey,
    name: String,
    decl_interface_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportKey {
    module: npa_cert::ModuleName,
    export_hash: npa_cert::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LoadedImportDeclKey {
    import_key: ImportKey,
    name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum KernelDeclSource {
    Direct,
    Available,
}

#[derive(Clone, Debug)]
struct PendingKernelDecl {
    decl: Decl,
    source: KernelDeclSource,
    dependencies: BTreeMap<String, BTreeSet<VerifiedDependency>>,
    interfaces: BTreeSet<DeclInterfaceKey>,
    loaded_decl_keys: BTreeSet<LoadedImportDeclKey>,
}

pub(crate) fn kernel_env_from_verified_imports<'a>(
    active_imports: impl IntoIterator<Item = &'a VerifiedImport>,
    available_imports: &'a [VerifiedImport],
    allow_builtin_kernel_decls: bool,
    span: crate::Span,
) -> Result<Env> {
    kernel_env_from_imports(
        active_imports,
        available_imports,
        allow_builtin_kernel_decls,
        span,
    )
    .map(|build| build.env)
}

fn kernel_env_from_imports<'a>(
    active_imports: impl IntoIterator<Item = &'a VerifiedImport>,
    available_imports: &'a [VerifiedImport],
    allow_builtin_kernel_decls: bool,
    span: crate::Span,
) -> Result<KernelEnvBuild> {
    let active_imports: Vec<_> = active_imports.into_iter().collect();
    let available_decls = collect_import_decl_infos(available_imports);
    let available_decl_interfaces = collect_import_decl_interface_infos(available_imports);
    let available_decl_import_interfaces =
        collect_import_decl_import_interface_infos(available_imports);
    let mut pending: Vec<_> = collect_import_decl_infos(active_imports.iter().copied())
        .into_values()
        .flatten()
        .map(|info| PendingKernelDecl {
            decl: info.decl,
            source: KernelDeclSource::Direct,
            dependencies: info.dependencies,
            interfaces: info.interfaces,
            loaded_decl_keys: info.loaded_decl_keys,
        })
        .collect();
    let mut queued: BTreeSet<_> = pending
        .iter()
        .map(|pending_decl| pending_decl.decl.name().to_owned())
        .collect();
    let mut queued_dependencies = BTreeSet::new();
    let mut env = Env::new();
    let mut loaded_available_interfaces = BTreeSet::new();
    let mut loaded_available_decl_keys = BTreeSet::new();
    let mut loaded_dependency_refs: BTreeMap<String, BTreeSet<VerifiedDependency>> =
        BTreeMap::new();

    while !pending.is_empty() {
        let mut progressed = false;
        let mut remaining = Vec::new();

        for pending_decl in pending {
            let PendingKernelDecl {
                decl,
                source,
                dependencies,
                interfaces,
                loaded_decl_keys,
            } = pending_decl;
            record_available_dependencies_backed_by_env(
                &dependencies,
                &env,
                &available_decl_import_interfaces,
                &mut loaded_dependency_refs,
                &mut loaded_available_interfaces,
                &mut loaded_available_decl_keys,
                span,
            )?;
            validate_dependencies_against_loaded_refs(
                &dependencies,
                &loaded_dependency_refs,
                &env,
                span,
            )?;
            if let Some(existing) = env.decl(decl.name()) {
                if !kernel_decl_matches_env(existing, &decl) {
                    return Err(import_resolution_diagnostic(
                        span,
                        format!(
                            "verified dependency {} conflicts with an existing kernel declaration",
                            decl.name()
                        ),
                    ));
                }
                if source == KernelDeclSource::Available {
                    loaded_available_interfaces.extend(interfaces.clone());
                    loaded_available_decl_keys.extend(loaded_decl_keys.clone());
                }
                record_loaded_import_decl_refs(
                    &mut loaded_dependency_refs,
                    &interfaces,
                    &loaded_decl_keys,
                );
                progressed = true;
                continue;
            }

            match add_kernel_decl_to_env(&mut env, decl.clone()) {
                Ok(()) => {
                    if source == KernelDeclSource::Available {
                        loaded_available_interfaces.extend(interfaces.clone());
                        loaded_available_decl_keys.extend(loaded_decl_keys.clone());
                    }
                    record_loaded_import_decl_refs(
                        &mut loaded_dependency_refs,
                        &interfaces,
                        &loaded_decl_keys,
                    );
                    progressed = true;
                }
                Err(npa_kernel::Error::UnknownConstant(name)) => {
                    let explicit_dependency =
                        single_dependency_for_name(&name, &dependencies, span)?.cloned();
                    let has_explicit_dependency_hash = explicit_dependency.is_some();
                    if allow_builtin_kernel_decls
                        && dependency_matches_builtin_interface(&name, &dependencies, span)?
                        && add_builtin_decl_for_unknown_constant(&mut env, &name, span)?
                    {
                        record_loaded_builtin_dependency_ref(&mut loaded_dependency_refs, &name);
                        remaining.push(PendingKernelDecl {
                            decl,
                            source,
                            dependencies,
                            interfaces,
                            loaded_decl_keys,
                        });
                        progressed = true;
                        continue;
                    }
                    let should_resolve_available = explicit_dependency.as_ref().map_or_else(
                        || queued.insert(name.clone()),
                        |dependency| queued_dependencies.insert(dependency.clone()),
                    );
                    if should_resolve_available {
                        if let Some(dependency) = resolve_available_dependency(
                            &name,
                            &dependencies,
                            &available_decls,
                            &available_decl_interfaces,
                            &available_decl_import_interfaces,
                            span,
                        )? {
                            queued.insert(name.clone());
                            remaining.push(PendingKernelDecl {
                                decl: dependency.decl,
                                source: KernelDeclSource::Available,
                                dependencies: dependency.dependencies,
                                interfaces: dependency.interfaces,
                                loaded_decl_keys: dependency.loaded_decl_keys,
                            });
                            progressed = true;
                        }
                    }
                    if allow_builtin_kernel_decls
                        && !has_explicit_dependency_hash
                        && add_builtin_decl_for_unknown_constant(&mut env, &name, span)?
                    {
                        record_loaded_builtin_dependency_ref(&mut loaded_dependency_refs, &name);
                        remaining.push(PendingKernelDecl {
                            decl,
                            source,
                            dependencies,
                            interfaces,
                            loaded_decl_keys,
                        });
                        progressed = true;
                        continue;
                    }
                    remaining.push(PendingKernelDecl {
                        decl,
                        source,
                        dependencies,
                        interfaces,
                        loaded_decl_keys,
                    });
                }
                Err(err) => {
                    return Err(MachineDiagnostic::error(
                        MachineDiagnosticKind::KernelRejected,
                        span,
                        format!("kernel rejected verified import interface: {err:?}"),
                    ));
                }
            }
        }

        if !progressed {
            break;
        }

        pending = remaining;
    }

    if allow_builtin_kernel_decls {
        add_builtin_eq_rec_for_generated_import_exports(
            &mut env,
            active_imports.iter().copied(),
            span,
        )?;
    }

    Ok(KernelEnvBuild {
        env,
        loaded_available_interfaces,
        loaded_available_decl_keys,
    })
}

fn record_available_dependencies_backed_by_env(
    dependencies: &BTreeMap<String, BTreeSet<VerifiedDependency>>,
    env: &Env,
    available_decl_import_interfaces: &BTreeMap<ImportDeclInterfaceKey, Option<ImportKernelDecl>>,
    loaded_refs: &mut BTreeMap<String, BTreeSet<VerifiedDependency>>,
    loaded_available_interfaces: &mut BTreeSet<DeclInterfaceKey>,
    loaded_available_decl_keys: &mut BTreeSet<LoadedImportDeclKey>,
    span: crate::Span,
) -> Result<()> {
    let mut materializer = AvailableDependencyMaterializer {
        env,
        available_decl_import_interfaces,
        loaded_refs,
        loaded_available_interfaces,
        loaded_available_decl_keys,
        span,
        materializing: BTreeSet::new(),
    };
    materializer.record(dependencies)
}

struct AvailableDependencyMaterializer<'a> {
    env: &'a Env,
    available_decl_import_interfaces:
        &'a BTreeMap<ImportDeclInterfaceKey, Option<ImportKernelDecl>>,
    loaded_refs: &'a mut BTreeMap<String, BTreeSet<VerifiedDependency>>,
    loaded_available_interfaces: &'a mut BTreeSet<DeclInterfaceKey>,
    loaded_available_decl_keys: &'a mut BTreeSet<LoadedImportDeclKey>,
    span: crate::Span,
    materializing: BTreeSet<VerifiedDependency>,
}

impl AvailableDependencyMaterializer<'_> {
    fn record(
        &mut self,
        dependencies: &BTreeMap<String, BTreeSet<VerifiedDependency>>,
    ) -> Result<()> {
        for (name, dependencies) in dependencies {
            let Some(expected) = single_dependency(name, dependencies, self.span)? else {
                continue;
            };
            let Some(loaded) = self.loaded_refs.get(name) else {
                continue;
            };
            if loaded.contains(expected) {
                continue;
            }
            let Some(dependency) = available_dependency_for_explicit_ref(
                name,
                expected,
                self.available_decl_import_interfaces,
                self.span,
            )?
            .cloned() else {
                continue;
            };
            if !import_kernel_decl_backed_by_env(self.env, &dependency) {
                continue;
            }
            if !self.materializing.insert(expected.clone()) {
                continue;
            }
            self.record(&dependency.dependencies)?;
            validate_dependencies_against_loaded_refs(
                &dependency.dependencies,
                self.loaded_refs,
                self.env,
                self.span,
            )?;
            self.loaded_available_interfaces
                .extend(dependency.interfaces.clone());
            self.loaded_available_decl_keys
                .extend(dependency.loaded_decl_keys.clone());
            record_loaded_import_decl_refs(
                self.loaded_refs,
                &dependency.interfaces,
                &dependency.loaded_decl_keys,
            );
            self.materializing.remove(expected);
        }
        Ok(())
    }
}

fn available_dependency_for_explicit_ref<'a>(
    name: &str,
    dependency: &VerifiedDependency,
    available_decl_import_interfaces: &'a BTreeMap<
        ImportDeclInterfaceKey,
        Option<ImportKernelDecl>,
    >,
    span: crate::Span,
) -> Result<Option<&'a ImportKernelDecl>> {
    let (Some(module), Some(export_hash)) = (&dependency.module, dependency.export_hash) else {
        if dependency.module.is_none() && dependency.export_hash.is_none() {
            return Ok(None);
        }
        return Err(import_resolution_diagnostic(
            span,
            format!("verified dependency {name} has incomplete import identity"),
        ));
    };
    let key = ImportDeclInterfaceKey {
        import_key: ImportKey {
            module: module.clone(),
            export_hash,
        },
        name: name.to_owned(),
        decl_interface_hash: dependency.decl_interface_hash,
    };
    match available_decl_import_interfaces.get(&key) {
        Some(Some(dependency)) => Ok(Some(dependency)),
        Some(None) => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {name} has multiple available declarations with the same import and interface hash"
            ),
        )),
        None => Ok(None),
    }
}

fn import_kernel_decl_backed_by_env(env: &Env, dependency: &ImportKernelDecl) -> bool {
    env.decl(dependency.decl.name())
        .is_some_and(|existing| kernel_decl_matches_env(existing, &dependency.decl))
}

fn kernel_decl_matches_env(existing: &Decl, candidate: &Decl) -> bool {
    if existing == candidate {
        return true;
    }
    match (existing, candidate) {
        (
            Decl::Inductive {
                name: existing_name,
                universe_params: existing_universe_params,
                data: existing_data,
                ..
            },
            Decl::Inductive {
                name: candidate_name,
                universe_params: candidate_universe_params,
                data: candidate_data,
                ..
            },
        ) => {
            existing_name == candidate_name
                && existing_universe_params == candidate_universe_params
                && existing_data == candidate_data
        }
        _ => false,
    }
}

fn kernel_decl_matches_export(decl: &Decl, export: &VerifiedExport) -> bool {
    decl.name() == export.name.as_dotted()
        && decl.universe_params() == export.universe_params.as_slice()
        && npa_cert::core_expr_hash(decl.ty()) == npa_cert::core_expr_hash(&export.ty)
}

fn validate_dependencies_against_loaded_refs(
    dependencies: &BTreeMap<String, BTreeSet<VerifiedDependency>>,
    loaded_refs: &BTreeMap<String, BTreeSet<VerifiedDependency>>,
    env: &Env,
    span: crate::Span,
) -> Result<()> {
    for (name, dependencies) in dependencies {
        let Some(expected) = single_dependency(name, dependencies, span)? else {
            continue;
        };
        let Some(loaded) = loaded_refs.get(name) else {
            continue;
        };
        if !loaded.contains(expected)
            && !builtin_eq_dependency_is_backed_by_env(name, expected, env)
        {
            return Err(import_resolution_diagnostic(
                span,
                format!(
                    "verified dependency {name} is already loaded with a different declaration interface hash or import identity: expected={expected:?}; loaded={loaded:?}"
                ),
            ));
        }
    }
    Ok(())
}

fn builtin_eq_dependency_is_backed_by_env(
    name: &str,
    dependency: &VerifiedDependency,
    env: &Env,
) -> bool {
    if !matches!(name, "Eq" | "Eq.refl" | "Eq.rec")
        || dependency.module.is_some()
        || dependency.export_hash.is_some()
    {
        return false;
    }
    let name = npa_cert::Name::from_dotted(name);
    npa_cert::builtin_decl_interface_hash(&name) == Some(dependency.decl_interface_hash)
        && env.decl(&name.as_dotted()).is_some()
}

fn single_dependency_for_name<'a>(
    name: &str,
    dependencies: &'a BTreeMap<String, BTreeSet<VerifiedDependency>>,
    span: crate::Span,
) -> Result<Option<&'a VerifiedDependency>> {
    let Some(dependencies) = dependencies.get(name) else {
        return Ok(None);
    };
    single_dependency(name, dependencies, span)
}

fn single_dependency<'a>(
    name: &str,
    dependencies: &'a BTreeSet<VerifiedDependency>,
    span: crate::Span,
) -> Result<Option<&'a VerifiedDependency>> {
    let mut dependencies = dependencies.iter();
    let Some(first_dependency) = dependencies.next() else {
        return Ok(None);
    };
    if dependencies.next().is_some() {
        return Err(import_resolution_diagnostic(
            span,
            format!("verified dependency {name} has multiple declaration interface hashes"),
        ));
    }
    Ok(Some(first_dependency))
}

fn record_loaded_import_decl_refs(
    loaded_refs: &mut BTreeMap<String, BTreeSet<VerifiedDependency>>,
    interfaces: &BTreeSet<DeclInterfaceKey>,
    loaded_decl_keys: &BTreeSet<LoadedImportDeclKey>,
) {
    for loaded_key in loaded_decl_keys {
        for interface in interfaces
            .iter()
            .filter(|interface| interface.name == loaded_key.name)
        {
            let name = npa_cert::Name::from_dotted(&loaded_key.name);
            loaded_refs
                .entry(loaded_key.name.clone())
                .or_default()
                .insert(VerifiedDependency {
                    module: Some(loaded_key.import_key.module.clone()),
                    export_hash: Some(loaded_key.import_key.export_hash),
                    name,
                    decl_interface_hash: interface.decl_interface_hash,
                });
        }
    }
}

fn record_loaded_builtin_dependency_ref(
    loaded_refs: &mut BTreeMap<String, BTreeSet<VerifiedDependency>>,
    name: &str,
) {
    let name = npa_cert::Name::from_dotted(name);
    let Some(decl_interface_hash) = npa_cert::builtin_decl_interface_hash(&name) else {
        return;
    };
    loaded_refs
        .entry(name.as_dotted())
        .or_default()
        .insert(VerifiedDependency {
            module: None,
            export_hash: None,
            name,
            decl_interface_hash,
        });
}

fn dependency_matches_builtin_interface(
    name: &str,
    dependencies: &BTreeMap<String, BTreeSet<VerifiedDependency>>,
    span: crate::Span,
) -> Result<bool> {
    let Some(first_dependency) = single_dependency_for_name(name, dependencies, span)? else {
        return Ok(false);
    };
    let Some(builtin_hash) =
        npa_cert::builtin_decl_interface_hash(&npa_cert::Name::from_dotted(name))
    else {
        return Ok(false);
    };
    Ok(first_dependency.module.is_none()
        && first_dependency.export_hash.is_none()
        && first_dependency.decl_interface_hash == builtin_hash)
}

fn resolve_available_dependency(
    name: &str,
    dependencies: &BTreeMap<String, BTreeSet<VerifiedDependency>>,
    available_decls: &BTreeMap<String, Option<ImportKernelDecl>>,
    available_decl_interfaces: &BTreeMap<DeclInterfaceKey, Option<ImportKernelDecl>>,
    available_decl_import_interfaces: &BTreeMap<ImportDeclInterfaceKey, Option<ImportKernelDecl>>,
    span: crate::Span,
) -> Result<Option<ImportKernelDecl>> {
    let Some(first_dependency) = single_dependency_for_name(name, dependencies, span)? else {
        return Ok(available_decls.get(name).cloned().flatten());
    };

    match (&first_dependency.module, first_dependency.export_hash) {
        (Some(module), Some(export_hash)) => {
            let key = ImportDeclInterfaceKey {
                import_key: ImportKey {
                    module: module.clone(),
                    export_hash,
                },
                name: name.to_owned(),
                decl_interface_hash: first_dependency.decl_interface_hash,
            };
            return match available_decl_import_interfaces.get(&key) {
                Some(Some(dependency)) => Ok(Some(dependency.clone())),
                Some(None) => Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "verified dependency {name} has multiple available declarations with the same import and interface hash"
                    ),
                )),
                None => Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "verified dependency {name} with import and declaration interface hash is not present in the verified import set"
                    ),
                )),
            };
        }
        (None, None) => {}
        _ => {
            return Err(import_resolution_diagnostic(
                span,
                format!("verified dependency {name} has incomplete import identity"),
            ));
        }
    }

    let key = DeclInterfaceKey {
        name: name.to_owned(),
        decl_interface_hash: first_dependency.decl_interface_hash,
    };
    match available_decl_interfaces.get(&key) {
        Some(Some(dependency)) => Ok(Some(dependency.clone())),
        Some(None) => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {name} has multiple available declarations with the same interface hash"
            ),
        )),
        None => Err(import_resolution_diagnostic(
            span,
            format!(
                "verified dependency {name} with declaration interface hash is not present in the verified import set"
            ),
        )),
    }
}

fn machine_term_context_from_verified_imports(
    direct_imports: &[VerifiedImport],
    available_imports: &[VerifiedImport],
    local_context: Vec<MachineLocalDecl>,
    universe_params: Vec<String>,
    span: crate::Span,
) -> Result<MachineTermElabContext> {
    machine_term_context_from_parts(MachineTermContextParts {
        direct_imports,
        available_imports,
        checked_current_decls: &[],
        current_generated_decls: &[],
        local_context,
        universe_params,
        current_module: None,
        allow_builtin_kernel_decls: true,
        span,
    })
}

struct MachineTermContextParts<'a> {
    direct_imports: &'a [VerifiedImport],
    available_imports: &'a [VerifiedImport],
    checked_current_decls: &'a [MachineCheckedCurrentDecl],
    current_generated_decls: &'a [MachineCheckedCurrentGeneratedDecl],
    local_context: Vec<MachineLocalDecl>,
    universe_params: Vec<String>,
    current_module: Option<npa_cert::ModuleName>,
    allow_builtin_kernel_decls: bool,
    span: crate::Span,
}

fn machine_term_context_from_parts(
    parts: MachineTermContextParts<'_>,
) -> Result<MachineTermElabContext> {
    let MachineTermContextParts {
        direct_imports,
        available_imports,
        checked_current_decls,
        current_generated_decls,
        local_context,
        universe_params,
        current_module,
        allow_builtin_kernel_decls,
        span,
    } = parts;
    validate_checked_current_decls_belong_to_module(
        current_module.as_ref(),
        checked_current_decls,
        span,
    )?;
    let direct_decls = collect_import_decls(direct_imports);
    let mut build = kernel_env_from_imports(
        direct_imports.iter(),
        available_imports,
        allow_builtin_kernel_decls,
        span,
    )?;
    validate_direct_kernel_env_matches_import_exports(
        &build.env,
        direct_imports,
        &direct_decls,
        span,
    )?;
    validate_loaded_available_kernel_env_matches_import_exports(
        &build.env,
        available_imports,
        &build.loaded_available_interfaces,
        span,
    )?;
    if allow_builtin_kernel_decls {
        add_referenced_builtin_decls_to_env(&mut build.env, checked_current_decls, span)?;
    }
    let mut entries: Vec<_> = direct_imports
        .iter()
        .enumerate()
        .flat_map(|(import_index, import)| {
            import
                .exports
                .iter()
                .map(move |export| MachineGlobalScopeEntry::Imported {
                    name: export.name.clone(),
                    import_index: import_index as u32,
                    decl_interface_hash: export.decl_interface_hash,
                })
        })
        .collect();
    let mut decl_interface_hashes: Vec<_> = entries
        .iter()
        .map(|entry| (entry.name().clone(), *entry.decl_interface_hash()))
        .collect();
    append_checked_current_decls_to_context(
        &mut build.env,
        &mut entries,
        &mut decl_interface_hashes,
        checked_current_decls,
        current_generated_decls,
        span,
    )?;
    append_loaded_available_decl_interface_hashes(
        &mut decl_interface_hashes,
        &build.loaded_available_interfaces,
    );
    append_verified_import_decl_interface_hashes(&mut decl_interface_hashes, direct_imports.iter());
    append_loaded_available_import_decl_interface_hashes(
        &mut decl_interface_hashes,
        available_imports.iter(),
        &build.loaded_available_decl_keys,
    );
    let loaded_available_decls =
        machine_loaded_available_decl_refs(&build.loaded_available_decl_keys);

    Ok(MachineTermElabContext {
        global_scope: MachineGlobalScope { entries },
        local_context,
        universe_params,
        kernel_env: crate::MachineKernelEnvView::with_decl_interface_hashes(
            build.env,
            decl_interface_hashes,
        ),
        callable_interface_table: crate::MachineSurfaceCallableInterfaceTable::empty(),
        current_module,
        direct_imports: direct_imports
            .iter()
            .map(|import| MachineDirectImportRef {
                module: import.module.clone(),
                export_hash: import.export_hash,
            })
            .collect(),
        loaded_available_decls,
        verified_imports: collect_machine_verified_import_refs(
            direct_imports.iter().chain(available_imports.iter()),
        ),
    })
}

fn validate_checked_current_decls_belong_to_module(
    current_module: Option<&npa_cert::ModuleName>,
    checked_current_decls: &[MachineCheckedCurrentDecl],
    span: crate::Span,
) -> Result<()> {
    let Some(current_module) = current_module else {
        return Ok(());
    };
    for checked in checked_current_decls {
        if !name_is_in_module(&checked.name, current_module) {
            return Err(import_resolution_diagnostic(
                span,
                format!(
                    "checked current declaration {} is outside current module {}",
                    checked.name.as_dotted(),
                    current_module.as_dotted()
                ),
            ));
        }
    }
    Ok(())
}

fn name_is_in_module(name: &npa_cert::Name, module: &npa_cert::ModuleName) -> bool {
    name.0.len() > module.0.len() && name.0.starts_with(&module.0)
}

fn collect_machine_verified_import_refs<'a>(
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
) -> Vec<MachineVerifiedImportRef> {
    let mut seen = BTreeSet::new();
    let mut refs = Vec::new();
    for import in imports {
        if seen.insert((import.module.clone(), import.export_hash)) {
            refs.push(machine_verified_import_ref(import));
        }
    }
    refs
}

fn machine_verified_import_ref(import: &VerifiedImport) -> MachineVerifiedImportRef {
    let generated_decls = machine_verified_import_generated_decl_refs(import);
    let generated_exports: Vec<_> = generated_decls
        .iter()
        .filter(|decl| decl.public_export)
        .map(|decl| MachineVerifiedImportGeneratedExportRef {
            parent_name: decl.parent_name.clone(),
            name: decl.name.clone(),
            parent_decl_interface_hash: decl.parent_decl_interface_hash,
            decl_interface_hash: decl.decl_interface_hash,
        })
        .collect();
    let generated_export_names: BTreeSet<_> = generated_exports
        .iter()
        .map(|export| export.name.clone())
        .collect();
    MachineVerifiedImportRef {
        module: import.module.clone(),
        export_hash: import.export_hash,
        decls: machine_verified_import_decl_refs(import),
        exports: import
            .exports
            .iter()
            .filter(|export| !generated_export_names.contains(&export.name))
            .map(|export| MachineVerifiedImportExportRef {
                name: export.name.clone(),
                decl_interface_hash: export.decl_interface_hash,
            })
            .collect(),
        generated_decls,
        generated_exports,
        dependencies: machine_verified_import_dependency_refs(import),
    }
}

fn machine_verified_import_decl_refs(import: &VerifiedImport) -> Vec<MachineVerifiedImportDeclRef> {
    let public_exports: BTreeSet<_> = import
        .exports
        .iter()
        .map(|export| (export.name.clone(), export.decl_interface_hash))
        .collect();
    let mut decls = BTreeSet::new();

    for decl in kernel_decls_for_import(import) {
        if matches!(decl, Decl::Constructor { .. } | Decl::Recursor { .. }) {
            continue;
        }
        let name = npa_cert::Name::from_dotted(decl.name());
        let Some(decl_interface_hash) = import_decl_interface_hash(import, &name) else {
            continue;
        };
        decls.insert(MachineVerifiedImportDeclRef {
            public_export: public_exports.contains(&(name.clone(), decl_interface_hash)),
            name,
            decl_interface_hash,
        });
    }

    decls.into_iter().collect()
}

fn machine_verified_import_dependency_refs(
    import: &VerifiedImport,
) -> Vec<MachineVerifiedImportDependencyRef> {
    let dependencies: BTreeSet<_> = import
        .kernel_decl_dependencies
        .values()
        .flat_map(|dependencies| dependencies.iter())
        .filter_map(|dependency| {
            let (Some(module), Some(export_hash)) = (&dependency.module, dependency.export_hash)
            else {
                return None;
            };
            Some(MachineVerifiedImportDependencyRef {
                module: module.clone(),
                export_hash,
                name: dependency.name.clone(),
                decl_interface_hash: dependency.decl_interface_hash,
            })
        })
        .collect();

    dependencies.into_iter().collect()
}

fn machine_verified_import_generated_decl_refs(
    import: &VerifiedImport,
) -> Vec<MachineVerifiedImportGeneratedDeclRef> {
    let public_exports_by_name: BTreeMap<_, _> = import
        .exports
        .iter()
        .map(|export| (export.name.as_dotted(), export))
        .collect();
    let mut generated_decls = BTreeSet::new();

    for decl in kernel_decls_for_import(import) {
        let Decl::Inductive { name, data, .. } = decl else {
            continue;
        };
        let parent_name = npa_cert::Name::from_dotted(&name);
        let Some(parent_decl_interface_hash) = import_decl_interface_hash(import, &parent_name)
        else {
            continue;
        };

        for generated_name in data
            .constructors
            .iter()
            .map(|constructor| constructor.name.as_str())
            .chain(data.recursor.iter().map(|recursor| recursor.name.as_str()))
        {
            let public_export = public_exports_by_name
                .get(generated_name)
                .is_some_and(|export| export.decl_interface_hash == parent_decl_interface_hash);
            generated_decls.insert(MachineVerifiedImportGeneratedDeclRef {
                parent_name: parent_name.clone(),
                name: npa_cert::Name::from_dotted(generated_name),
                parent_decl_interface_hash,
                decl_interface_hash: parent_decl_interface_hash,
                public_export,
            });
        }
    }

    generated_decls.into_iter().collect()
}

fn import_decl_interface_hash(
    import: &VerifiedImport,
    name: &npa_cert::Name,
) -> Option<npa_cert::Hash> {
    import.decl_interface_hashes.get(name).copied().or_else(|| {
        let mut matches = import
            .exports
            .iter()
            .filter(|export| &export.name == name)
            .map(|export| export.decl_interface_hash);
        let first = matches.next()?;
        matches.next().is_none().then_some(first)
    })
}

fn append_loaded_available_decl_interface_hashes(
    decl_interface_hashes: &mut Vec<(npa_cert::Name, npa_cert::Hash)>,
    loaded_available_interfaces: &BTreeSet<DeclInterfaceKey>,
) {
    for interface in loaded_available_interfaces {
        decl_interface_hashes.push((
            npa_cert::Name::from_dotted(&interface.name),
            interface.decl_interface_hash,
        ));
    }
}

fn append_verified_import_decl_interface_hashes<'a>(
    decl_interface_hashes: &mut Vec<(npa_cert::Name, npa_cert::Hash)>,
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
) {
    let mut seen_imports = BTreeSet::new();
    for import in imports {
        if !seen_imports.insert((import.module.clone(), import.export_hash)) {
            continue;
        }
        for (name, decl_interface_hash) in &import.decl_interface_hashes {
            decl_interface_hashes.push((name.clone(), *decl_interface_hash));
        }
        for generated in machine_verified_import_generated_decl_refs(import) {
            decl_interface_hashes.push((generated.name, generated.decl_interface_hash));
        }
    }
}

fn append_loaded_available_import_decl_interface_hashes<'a>(
    decl_interface_hashes: &mut Vec<(npa_cert::Name, npa_cert::Hash)>,
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
    loaded_decl_keys: &BTreeSet<LoadedImportDeclKey>,
) {
    let mut seen_imports = BTreeSet::new();
    for import in imports {
        let import_key = import_key_for_import(import);
        if !seen_imports.insert(import_key.clone()) {
            continue;
        }
        for (name, decl_interface_hash) in &import.decl_interface_hashes {
            if loaded_decl_keys.contains(&LoadedImportDeclKey {
                import_key: import_key.clone(),
                name: name.as_dotted(),
            }) {
                decl_interface_hashes.push((name.clone(), *decl_interface_hash));
            }
        }
        for generated in machine_verified_import_generated_decl_refs(import) {
            if loaded_decl_keys.contains(&LoadedImportDeclKey {
                import_key: import_key.clone(),
                name: generated.name.as_dotted(),
            }) {
                decl_interface_hashes.push((generated.name, generated.decl_interface_hash));
            }
        }
    }
}

fn machine_loaded_available_decl_refs(
    loaded_decl_keys: &BTreeSet<LoadedImportDeclKey>,
) -> Vec<MachineLoadedAvailableDeclRef> {
    loaded_decl_keys
        .iter()
        .map(|key| MachineLoadedAvailableDeclRef {
            module: key.import_key.module.clone(),
            export_hash: key.import_key.export_hash,
            name: npa_cert::Name::from_dotted(&key.name),
        })
        .collect()
}

fn add_referenced_builtin_decls_to_env(
    env: &mut Env,
    checked_current_decls: &[MachineCheckedCurrentDecl],
    span: crate::Span,
) -> Result<()> {
    let mut names = BTreeSet::new();
    for checked in checked_current_decls {
        collect_const_names_from_decl(&mut names, &checked.decl);
    }
    add_builtin_decls_for_names(env, &names, span)
}

fn add_builtin_decl_for_unknown_constant(
    env: &mut Env,
    name: &str,
    span: crate::Span,
) -> Result<bool> {
    if !matches!(
        name,
        "Nat" | "Nat.zero" | "Nat.succ" | "Nat.rec" | "Eq" | "Eq.refl" | "Eq.rec"
    ) {
        return Ok(false);
    }
    let mut names = BTreeSet::new();
    names.insert(npa_cert::Name::from_dotted(name));
    add_builtin_decls_for_names(env, &names, span)?;
    Ok(true)
}

fn add_builtin_eq_rec_for_generated_import_exports<'a>(
    env: &mut Env,
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
    span: crate::Span,
) -> Result<()> {
    let needs_eq_rec = imports.into_iter().any(|import| {
        import
            .exports
            .iter()
            .any(|export| import_export_uses_builtin_eq_rec(import, export))
    });
    if !needs_eq_rec || env.decl("Eq.rec").is_some() {
        return Ok(());
    }

    env.add_axiom(
        "Eq.rec",
        vec!["u".to_owned(), "v".to_owned()],
        eq_rec_type(Level::param("u"), Level::param("v")),
    )
    .map_err(|err| builtin_kernel_diagnostic(span, err))
}

fn import_export_uses_builtin_eq_rec(import: &VerifiedImport, export: &VerifiedExport) -> bool {
    export.name.as_dotted() == "Eq.rec"
        && import
            .kernel_decls
            .iter()
            .any(|decl| matches!(decl, Decl::Inductive { name, .. } if name == "Eq"))
}

fn add_builtin_decls_for_names(
    env: &mut Env,
    names: &BTreeSet<npa_cert::Name>,
    span: crate::Span,
) -> Result<()> {
    let needs_nat = names.iter().any(|name| {
        let name = name.as_dotted();
        matches!(name.as_str(), "Nat" | "Nat.zero" | "Nat.succ" | "Nat.rec")
    });
    let needs_eq = names.iter().any(|name| {
        let name = name.as_dotted();
        matches!(name.as_str(), "Eq" | "Eq.refl" | "Eq.rec")
    });
    let needs_eq_rec = names.iter().any(|name| name.as_dotted() == "Eq.rec");
    if needs_nat && env.decl("Nat").is_none() {
        env.add_inductive(nat_inductive())
            .map_err(|err| builtin_kernel_diagnostic(span, err))?;
    }
    if needs_eq && env.decl("Eq").is_none() {
        env.add_inductive(eq_inductive())
            .map_err(|err| builtin_kernel_diagnostic(span, err))?;
    }
    if needs_eq_rec && env.decl("Eq.rec").is_none() {
        env.add_axiom(
            "Eq.rec",
            vec!["u".to_owned(), "v".to_owned()],
            eq_rec_type(Level::param("u"), Level::param("v")),
        )
        .map_err(|err| builtin_kernel_diagnostic(span, err))?;
    }
    Ok(())
}

fn builtin_kernel_diagnostic(span: crate::Span, err: npa_kernel::Error) -> MachineDiagnostic {
    MachineDiagnostic::error(
        MachineDiagnosticKind::KernelRejected,
        span,
        format!("kernel rejected builtin environment: {err:?}"),
    )
}

fn append_checked_current_decls_to_context(
    env: &mut Env,
    entries: &mut Vec<MachineGlobalScopeEntry>,
    decl_interface_hashes: &mut Vec<(npa_cert::Name, npa_cert::Hash)>,
    checked_current_decls: &[MachineCheckedCurrentDecl],
    current_generated_decls: &[MachineCheckedCurrentGeneratedDecl],
    span: crate::Span,
) -> Result<()> {
    let mut current_parents_by_source_index = BTreeMap::new();
    for checked in checked_current_decls {
        let name = checked.name.as_dotted();
        if checked.decl.name() != name {
            return Err(import_resolution_diagnostic(
                span,
                format!("checked current declaration {name} does not match its kernel name"),
            ));
        }
        if current_parents_by_source_index
            .insert(
                checked.source_index,
                (name.clone(), checked.decl_interface_hash),
            )
            .is_some()
        {
            return Err(import_resolution_diagnostic(
                span,
                format!(
                    "checked current declaration source_index {} is duplicated",
                    checked.source_index
                ),
            ));
        }
        add_kernel_decl_to_env(env, checked.decl.clone()).map_err(|err| {
            MachineDiagnostic::error(
                MachineDiagnosticKind::KernelRejected,
                span,
                format!("kernel rejected checked current declaration {name}: {err:?}"),
            )
        })?;
        entries.push(MachineGlobalScopeEntry::CurrentModule {
            name: checked.name.clone(),
            source_index: checked.source_index,
            decl_interface_hash: checked.decl_interface_hash,
        });
        decl_interface_hashes.push((checked.name.clone(), checked.decl_interface_hash));
    }

    for generated in current_generated_decls {
        let Some((parent_name, parent_decl_interface_hash)) =
            current_parents_by_source_index.get(&generated.parent_source_index)
        else {
            return Err(import_resolution_diagnostic(
                span,
                format!(
                    "current generated declaration {} has no checked parent source_index {}",
                    generated.name.as_dotted(),
                    generated.parent_source_index
                ),
            ));
        };
        let name = generated.name.as_dotted();
        if generated.decl_interface_hash != *parent_decl_interface_hash {
            return Err(import_resolution_diagnostic(
                span,
                format!(
                    "current generated declaration {name} has a declaration interface hash that does not match checked parent {parent_name}"
                ),
            ));
        }
        match env.decl(&name) {
            Some(Decl::Constructor { inductive, .. } | Decl::Recursor { inductive, .. })
                if inductive == parent_name => {}
            Some(_) => {
                return Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "current generated declaration {name} is not generated by checked parent {parent_name}"
                    ),
                ));
            }
            None => {
                return Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "current generated declaration {name} is missing from kernel environment"
                    ),
                ));
            }
        }
        entries.push(MachineGlobalScopeEntry::CurrentGenerated {
            name: generated.name.clone(),
            parent_source_index: generated.parent_source_index,
            decl_interface_hash: generated.decl_interface_hash,
        });
        decl_interface_hashes.push((generated.name.clone(), generated.decl_interface_hash));
    }

    Ok(())
}

fn validate_direct_kernel_env_matches_import_exports(
    env: &Env,
    imports: &[VerifiedImport],
    direct_decls: &BTreeMap<String, Option<Decl>>,
    span: crate::Span,
) -> Result<()> {
    for import in imports {
        for export in &import.exports {
            let name = export.name.as_dotted();
            if direct_decls.get(&name).is_some_and(Option::is_none) {
                continue;
            }
            let Some(decl) = env.decl(&name) else {
                return Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "verified import {} exports {name}, but the kernel environment has no matching declaration",
                        import.module.as_dotted()
                    ),
                ));
            };

            if !import_export_uses_builtin_eq_rec(import, export)
                && !kernel_decl_matches_export(decl, export)
            {
                return Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "verified import {} export {name} does not match its kernel declaration",
                        import.module.as_dotted()
                    ),
                ));
            }
        }
    }

    Ok(())
}

fn validate_loaded_available_kernel_env_matches_import_exports(
    env: &Env,
    imports: &[VerifiedImport],
    loaded_interfaces: &BTreeSet<DeclInterfaceKey>,
    span: crate::Span,
) -> Result<()> {
    for import in imports {
        for export in &import.exports {
            let name = export.name.as_dotted();
            let key = DeclInterfaceKey {
                name: name.clone(),
                decl_interface_hash: export.decl_interface_hash,
            };
            if !loaded_interfaces.contains(&key) {
                continue;
            }
            let Some(decl) = env.decl(&name) else {
                return Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "verified import {} exports {name}, but the kernel environment has no matching declaration",
                        import.module.as_dotted()
                    ),
                ));
            };

            if !import_export_uses_builtin_eq_rec(import, export)
                && !kernel_decl_matches_export(decl, export)
            {
                return Err(import_resolution_diagnostic(
                    span,
                    format!(
                        "verified import {} export {name} does not match its kernel declaration",
                        import.module.as_dotted()
                    ),
                ));
            }
        }
    }

    Ok(())
}

fn collect_import_decls<'a>(
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
) -> BTreeMap<String, Option<Decl>> {
    collect_import_decl_infos(imports)
        .into_iter()
        .map(|(name, info)| (name, info.map(|info| info.decl)))
        .collect()
}

fn collect_import_decl_infos<'a>(
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
) -> BTreeMap<String, Option<ImportKernelDecl>> {
    let mut decls: BTreeMap<String, Option<ImportKernelDecl>> = BTreeMap::new();

    for import in imports {
        let import_key = import_key_for_import(import);
        for decl in kernel_decls_for_import(import) {
            let lookup_names = kernel_decl_lookup_names(&decl);
            let interfaces = import
                .exports
                .iter()
                .filter_map(|export| {
                    let name = export.name.as_dotted();
                    if lookup_names.iter().any(|lookup_name| lookup_name == &name) {
                        Some(DeclInterfaceKey {
                            name,
                            decl_interface_hash: export.decl_interface_hash,
                        })
                    } else {
                        None
                    }
                })
                .collect();
            let loaded_decl_keys = lookup_names
                .iter()
                .map(|name| LoadedImportDeclKey {
                    import_key: import_key.clone(),
                    name: name.clone(),
                })
                .collect();
            let info = ImportKernelDecl {
                dependencies: dependencies_for_import_decl(import, decl.name()),
                decl: decl.clone(),
                interfaces,
                loaded_decl_keys,
            };
            for name in lookup_names {
                match decls.get_mut(&name) {
                    Some(existing) if existing.as_ref() == Some(&info) => {
                        if let Some(existing) = existing.as_mut() {
                            existing.interfaces.extend(info.interfaces.clone());
                            existing
                                .loaded_decl_keys
                                .extend(info.loaded_decl_keys.clone());
                        }
                    }
                    Some(existing) => {
                        *existing = None;
                    }
                    None => {
                        decls.insert(name, Some(info.clone()));
                    }
                }
            }
        }
    }

    decls
}

fn import_key_for_import(import: &VerifiedImport) -> ImportKey {
    ImportKey {
        module: import.module.clone(),
        export_hash: import.export_hash,
    }
}

fn collect_import_decl_interface_infos<'a>(
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
) -> BTreeMap<DeclInterfaceKey, Option<ImportKernelDecl>> {
    let mut decls: BTreeMap<DeclInterfaceKey, Option<ImportKernelDecl>> = BTreeMap::new();

    for import in imports {
        let import_decls = collect_import_decl_infos(std::iter::once(import));
        for export in &import.exports {
            let name = export.name.as_dotted();
            let key = DeclInterfaceKey {
                name: name.clone(),
                decl_interface_hash: export.decl_interface_hash,
            };
            let Some(info) = import_decls.get(&name).cloned().flatten() else {
                continue;
            };
            match decls.get_mut(&key) {
                Some(existing) if existing.as_ref() == Some(&info) => {}
                Some(existing) => {
                    *existing = None;
                }
                None => {
                    decls.insert(key, Some(info));
                }
            }
        }
    }

    decls
}

fn collect_import_decl_import_interface_infos<'a>(
    imports: impl IntoIterator<Item = &'a VerifiedImport>,
) -> BTreeMap<ImportDeclInterfaceKey, Option<ImportKernelDecl>> {
    let mut decls: BTreeMap<ImportDeclInterfaceKey, Option<ImportKernelDecl>> = BTreeMap::new();

    for import in imports {
        let import_key = import_key_for_import(import);
        let import_decls = collect_import_decl_infos(std::iter::once(import));
        for export in &import.exports {
            let name = export.name.as_dotted();
            let key = ImportDeclInterfaceKey {
                import_key: import_key.clone(),
                name: name.clone(),
                decl_interface_hash: export.decl_interface_hash,
            };
            let Some(info) = import_decls.get(&name).cloned().flatten() else {
                continue;
            };
            match decls.get_mut(&key) {
                Some(existing) if existing.as_ref() == Some(&info) => {}
                Some(existing) => {
                    *existing = None;
                }
                None => {
                    decls.insert(key, Some(info));
                }
            }
        }
    }

    decls
}

fn dependencies_for_import_decl(
    import: &VerifiedImport,
    decl_name: &str,
) -> BTreeMap<String, BTreeSet<VerifiedDependency>> {
    let mut dependencies: BTreeMap<String, BTreeSet<VerifiedDependency>> = BTreeMap::new();
    if let Some(decl_dependencies) = import.kernel_decl_dependencies.get(decl_name) {
        for dependency in decl_dependencies {
            dependencies
                .entry(dependency.name.as_dotted())
                .or_default()
                .insert(dependency.clone());
        }
    }
    dependencies
}

fn kernel_decl_lookup_names(decl: &Decl) -> Vec<String> {
    let mut names = vec![decl.name().to_owned()];

    if let Decl::Inductive { data, .. } = decl {
        names.extend(
            data.constructors
                .iter()
                .map(|constructor| constructor.name.clone()),
        );
        if let Some(recursor) = &data.recursor {
            names.push(recursor.name.clone());
        }
    }

    names
}

fn kernel_decls_for_import(import: &VerifiedImport) -> Vec<Decl> {
    if import.kernel_decls.is_empty() {
        return fallback_kernel_decls_for_import(import);
    }

    import.kernel_decls.clone()
}

fn fallback_kernel_decls_for_import(import: &VerifiedImport) -> Vec<Decl> {
    import
        .exports
        .iter()
        .map(|export| Decl::Axiom {
            name: export.name.as_dotted(),
            universe_params: export.universe_params.clone(),
            ty: export.ty.clone(),
        })
        .collect()
}

fn add_kernel_decl_to_env(env: &mut Env, decl: Decl) -> npa_kernel::Result<()> {
    match decl {
        Decl::Axiom {
            name,
            universe_params,
            ty,
        } => env.add_axiom(name, universe_params, ty),
        Decl::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => {
            env.add_axiom_with_universe_constraints(name, universe_params, universe_constraints, ty)
        }
        Decl::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => env.add_def(name, universe_params, ty, value, reducibility),
        Decl::DefConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => env.add_def_with_universe_constraints(
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        ),
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        } => env.add_theorem(name, universe_params, ty, proof),
        Decl::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
        } => env.add_theorem_with_universe_constraints(
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
        ),
        Decl::Inductive { data, .. } => env.add_inductive(*data),
        Decl::MutualInductiveBlock { data, .. } => env.add_mutual_inductive(*data),
        Decl::Constructor { .. } | Decl::Recursor { .. } => {
            Err(npa_kernel::Error::InvalidInductive(
                "generated declarations cannot be added directly".to_owned(),
            ))
        }
    }
}

fn kernel_expr_diagnostic(span: crate::Span, err: npa_kernel::Error) -> MachineDiagnostic {
    match err {
        npa_kernel::Error::ExpectedPi { actual } => MachineDiagnostic::error(
            MachineDiagnosticKind::ExpectedFunctionType,
            span,
            format!("application head is not a function: {actual:?}"),
        ),
        npa_kernel::Error::ExpectedSort { actual } => MachineDiagnostic::error(
            MachineDiagnosticKind::ExpectedSort,
            span,
            format!("expected a type annotation, got {actual:?}"),
        ),
        npa_kernel::Error::TypeMismatch { expected, actual } => {
            let expected_hash = hash_owner_free_core_expr(&expected);
            let actual_hash = hash_owner_free_core_expr(&actual);
            MachineDiagnostic::error(
                MachineDiagnosticKind::TypeMismatch,
                span,
                format!("type annotation mismatch: expected {expected:?}, got {actual:?}"),
            )
            .with_payload(MachineDiagnosticPayload {
                expected_hash: Some(expected_hash),
                actual_hash: Some(actual_hash),
                ..MachineDiagnosticPayload::default()
            })
        }
        err => MachineDiagnostic::error(
            MachineDiagnosticKind::KernelRejected,
            span,
            format!("kernel rejected elaborated expression: {err:?}"),
        ),
    }
}

fn close_lam(binders: &[ElaboratedBinder], mut body: Expr) -> Expr {
    for binder in binders.iter().rev() {
        body = Expr::lam(binder.name.clone(), binder.ty.clone(), body);
    }
    body
}

fn close_pi(binders: &[ElaboratedBinder], mut body: Expr) -> Expr {
    for binder in binders.iter().rev() {
        body = Expr::pi(binder.name.clone(), binder.ty.clone(), body);
    }
    body
}

fn elaborate_level(level: MachineLevel) -> Result<Level> {
    match level {
        MachineLevel::Nat { value, span } => level_from_nat(value, span),
        MachineLevel::Param { name, .. } => Ok(Level::param(name)),
        MachineLevel::Succ { level, .. } => Ok(Level::succ(elaborate_level(*level)?)),
        MachineLevel::Max { lhs, rhs, .. } => {
            Ok(Level::max(elaborate_level(*lhs)?, elaborate_level(*rhs)?))
        }
        MachineLevel::IMax { lhs, rhs, .. } => {
            Ok(Level::imax(elaborate_level(*lhs)?, elaborate_level(*rhs)?))
        }
    }
}

fn level_from_nat(value: u64, span: crate::Span) -> Result<Level> {
    if value > MAX_NUMERIC_UNIVERSE_LEVEL {
        return Err(MachineDiagnostic::error(
            MachineDiagnosticKind::UniverseLevelTooLarge,
            span,
            format!(
                "numeric universe level {value} exceeds the maximum supported level {MAX_NUMERIC_UNIVERSE_LEVEL}"
            ),
        ));
    }

    Ok((0..value).fold(Level::zero(), |level, _| Level::succ(level)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;

    fn hash(seed: u8) -> npa_cert::Hash {
        [seed; 32]
    }

    #[test]
    fn imported_eq_satisfies_a_verified_builtin_eq_dependency() {
        let name = npa_cert::Name::from_dotted("Eq");
        let builtin_hash =
            npa_cert::builtin_decl_interface_hash(&name).expect("Eq is a builtin declaration");
        let expected = VerifiedDependency {
            module: None,
            export_hash: None,
            name: name.clone(),
            decl_interface_hash: builtin_hash,
        };
        let loaded = VerifiedDependency {
            module: Some(npa_cert::Name::from_dotted("Std.Logic.Eq")),
            export_hash: Some(hash(1)),
            name,
            decl_interface_hash: hash(2),
        };
        let dependencies = BTreeMap::from([("Eq".to_owned(), BTreeSet::from([expected]))]);
        let loaded_refs = BTreeMap::from([("Eq".to_owned(), BTreeSet::from([loaded]))]);
        let mut env = Env::new();
        env.add_inductive(eq_inductive())
            .expect("canonical Eq should load into the test environment");

        validate_dependencies_against_loaded_refs(
            &dependencies,
            &loaded_refs,
            &env,
            crate::Span::empty(FileId(0)),
        )
        .expect("an imported global Eq should back a builtin Eq dependency");
    }

    #[test]
    fn imported_non_eq_does_not_satisfy_a_verified_builtin_dependency() {
        let name = npa_cert::Name::from_dotted("Nat");
        let builtin_hash =
            npa_cert::builtin_decl_interface_hash(&name).expect("Nat is a builtin declaration");
        let expected = VerifiedDependency {
            module: None,
            export_hash: None,
            name: name.clone(),
            decl_interface_hash: builtin_hash,
        };
        let loaded = VerifiedDependency {
            module: Some(npa_cert::Name::from_dotted("Std.Data.Nat")),
            export_hash: Some(hash(1)),
            name,
            decl_interface_hash: hash(2),
        };
        let dependencies = BTreeMap::from([("Nat".to_owned(), BTreeSet::from([expected]))]);
        let loaded_refs = BTreeMap::from([("Nat".to_owned(), BTreeSet::from([loaded]))]);
        let mut env = Env::new();
        env.add_inductive(nat_inductive())
            .expect("canonical Nat should load into the test environment");

        let error = validate_dependencies_against_loaded_refs(
            &dependencies,
            &loaded_refs,
            &env,
            crate::Span::empty(FileId(0)),
        )
        .expect_err("non-Eq builtin providers must retain exact import identity checks");

        assert_eq!(error.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn frontend_compile_boundary_stays_separate_from_certificate_producer_candidates() {
        let _: fn(
            FileId,
            npa_cert::ModuleName,
            &str,
            &[VerifiedImport],
            &MachineCompileOptions,
        ) -> Result<npa_cert::CoreModule> = compile_machine_source_to_core;
        let _: fn(
            FileId,
            npa_cert::ModuleName,
            &str,
            &[npa_cert::VerifiedModule],
            &MachineCompileOptions,
        ) -> Result<npa_cert::ModuleCert> = compile_machine_source_to_certificate;

        assert_ne!(
            std::any::TypeId::of::<npa_cert::CoreModule>(),
            std::any::TypeId::of::<npa_cert::CoreDeclCandidate>()
        );
    }

    fn type0() -> Level {
        Level::succ(Level::zero())
    }

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn nat() -> Expr {
        Expr::konst("Nat", vec![])
    }

    fn verified_import(module: &str, exports: &[(&str, &[&str])]) -> VerifiedImport {
        let exports: Vec<_> = exports
            .iter()
            .enumerate()
            .map(|(index, (name, universe_params))| crate::VerifiedExport {
                name: npa_cert::Name::from_dotted(name),
                universe_params: universe_params
                    .iter()
                    .map(|param| param.to_string())
                    .collect(),
                ty: export_ty(name),
                decl_interface_hash: hash(index as u8 + 2),
            })
            .collect();
        let kernel_decls = exports
            .iter()
            .map(|export| Decl::Axiom {
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

    fn nat_import() -> VerifiedImport {
        verified_import("Std.Nat.Basic", &[("Nat", &[])])
    }

    fn eq_import() -> VerifiedImport {
        verified_import("Std.Logic.Eq", &[("Eq", &["u"]), ("Eq.refl", &["u"])])
    }

    fn poly_import() -> VerifiedImport {
        let u = Level::param("u");
        let k_ty = Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "B",
                Expr::sort(u),
                Expr::pi("x", Expr::bvar(1), Expr::bvar(2)),
            ),
        );

        VerifiedImport {
            module: npa_cert::Name::from_dotted("Std.Poly"),
            export_hash: hash(21),
            certificate_hash: None,
            decl_interface_hashes: BTreeMap::from([(
                npa_cert::Name::from_dotted("Poly.K"),
                hash(22),
            )]),
            exports: vec![crate::VerifiedExport {
                name: npa_cert::Name::from_dotted("Poly.K"),
                universe_params: vec!["u".to_owned()],
                ty: k_ty.clone(),
                decl_interface_hash: hash(22),
            }],
            kernel_decls: vec![Decl::Axiom {
                name: "Poly.K".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: k_ty,
            }],
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    fn hidden_import() -> VerifiedImport {
        verified_import("Hidden.Module", &[("Hidden.Thing", &[])])
    }

    fn direct_using_hidden_import() -> VerifiedImport {
        direct_using_hidden_dependency(
            "Direct.Module",
            hash(41),
            "Direct.x",
            hash(42),
            "Hidden.Module",
            hash(1),
            hash(2),
        )
    }

    fn direct_using_hidden_dependency(
        module: &str,
        export_hash: npa_cert::Hash,
        decl_name: &str,
        decl_interface_hash: npa_cert::Hash,
        dependency_module: &str,
        dependency_export_hash: npa_cert::Hash,
        dependency_decl_interface_hash: npa_cert::Hash,
    ) -> VerifiedImport {
        let ty = Expr::konst("Hidden.Thing", vec![]);
        let mut kernel_decl_dependencies = BTreeMap::new();
        kernel_decl_dependencies.insert(
            decl_name.to_owned(),
            BTreeSet::from([VerifiedDependency {
                module: Some(npa_cert::Name::from_dotted(dependency_module)),
                export_hash: Some(dependency_export_hash),
                name: npa_cert::Name::from_dotted("Hidden.Thing"),
                decl_interface_hash: dependency_decl_interface_hash,
            }]),
        );

        VerifiedImport {
            module: npa_cert::Name::from_dotted(module),
            export_hash,
            certificate_hash: None,
            decl_interface_hashes: BTreeMap::from([(
                npa_cert::Name::from_dotted(decl_name),
                decl_interface_hash,
            )]),
            exports: vec![crate::VerifiedExport {
                name: npa_cert::Name::from_dotted(decl_name),
                universe_params: Vec::new(),
                ty: ty.clone(),
                decl_interface_hash,
            }],
            kernel_decls: vec![Decl::Axiom {
                name: decl_name.to_owned(),
                universe_params: Vec::new(),
                ty,
            }],
            kernel_decl_dependencies,
        }
    }

    fn direct_using_imported_nat_dependency(decl_interface_hash: npa_cert::Hash) -> VerifiedImport {
        let ty = nat();
        let mut kernel_decl_dependencies = BTreeMap::new();
        kernel_decl_dependencies.insert(
            "Direct.nat_ty".to_owned(),
            BTreeSet::from([VerifiedDependency {
                module: None,
                export_hash: None,
                name: npa_cert::Name::from_dotted("Nat"),
                decl_interface_hash,
            }]),
        );

        VerifiedImport {
            module: npa_cert::Name::from_dotted("Direct.NatUser"),
            export_hash: hash(51),
            certificate_hash: None,
            decl_interface_hashes: BTreeMap::from([(
                npa_cert::Name::from_dotted("Direct.nat_ty"),
                hash(52),
            )]),
            exports: vec![crate::VerifiedExport {
                name: npa_cert::Name::from_dotted("Direct.nat_ty"),
                universe_params: Vec::new(),
                ty: ty.clone(),
                decl_interface_hash: hash(52),
            }],
            kernel_decls: vec![Decl::Axiom {
                name: "Direct.nat_ty".to_owned(),
                universe_params: Vec::new(),
                ty,
            }],
            kernel_decl_dependencies,
        }
    }

    fn set_single_axiom_ty(import: &mut VerifiedImport, ty: Expr) {
        import.exports[0].ty = ty.clone();
        let Decl::Axiom { ty: decl_ty, .. } = &mut import.kernel_decls[0] else {
            panic!("test import should contain a single axiom declaration");
        };
        *decl_ty = ty;
    }

    fn term_context(
        imports: &[VerifiedImport],
        locals: Vec<MachineLocalDecl>,
        universe_params: Vec<String>,
    ) -> crate::MachineTermElabContext {
        let span = crate::Span::empty(FileId(0));
        machine_term_context_from_verified_imports(imports, imports, locals, universe_params, span)
            .expect("term context imports should build a consistent kernel env")
    }

    #[test]
    fn callable_table_implicit_profile_requires_explicit_mode_for_app() {
        let mut import = verified_import("Std.Id", &[("id", &[])]);
        set_single_axiom_ty(
            &mut import,
            Expr::pi(
                "A",
                Expr::sort(type0()),
                Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
            ),
        );
        let callable_ref = crate::MachineSurfaceCallableRef::Imported {
            module: import.module.clone(),
            name: import.exports[0].name.clone(),
            export_hash: import.export_hash,
            decl_interface_hash: import.exports[0].decl_interface_hash,
        };
        let table = crate::MachineSurfaceCallableInterfaceTable::from_entries([
            crate::MachineSurfaceCallableInterfaceEntry::new(
                callable_ref,
                vec![
                    crate::MachineCallableBinderVisibility::Implicit,
                    crate::MachineCallableBinderVisibility::Explicit,
                ],
            ),
        ])
        .unwrap();
        let imports = [import];
        let context =
            term_context(&imports, Vec::new(), Vec::new()).with_callable_interface_table(table);
        let expected = Expr::pi("x", prop(), prop());

        let err = elaborate_machine_term_check(
            "id Prop",
            &context,
            &expected,
            &MachineCompileOptions::default(),
        )
        .expect_err("implicit binder application should require explicit mode");
        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);

        elaborate_machine_term_check(
            "@id Prop",
            &context,
            &expected,
            &MachineCompileOptions::default(),
        )
        .expect("explicit mode should allow supplying an implicit binder");
    }

    #[test]
    fn callable_table_all_explicit_profile_allows_plain_app() {
        let mut import = verified_import("Std.Id", &[("id", &[])]);
        set_single_axiom_ty(
            &mut import,
            Expr::pi(
                "A",
                Expr::sort(type0()),
                Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
            ),
        );
        let callable_ref = crate::MachineSurfaceCallableRef::Imported {
            module: import.module.clone(),
            name: import.exports[0].name.clone(),
            export_hash: import.export_hash,
            decl_interface_hash: import.exports[0].decl_interface_hash,
        };
        let table = crate::MachineSurfaceCallableInterfaceTable::from_entries([
            crate::MachineSurfaceCallableInterfaceEntry::all_explicit(callable_ref, 2),
        ])
        .unwrap();
        let imports = [import];
        let context =
            term_context(&imports, Vec::new(), Vec::new()).with_callable_interface_table(table);

        elaborate_machine_term_check(
            "id Prop",
            &context,
            &Expr::pi("x", prop(), prop()),
            &MachineCompileOptions::default(),
        )
        .expect("all-explicit profile should preserve the existing application behavior");
    }

    fn export_ty(name: &str) -> Expr {
        match name {
            "Nat" => Expr::sort(type0()),
            "Eq" => npa_kernel::eq_type(Level::param("u")),
            "Eq.refl" => npa_kernel::eq_refl_type(Level::param("u")),
            _ => Expr::sort(Level::zero()),
        }
    }

    fn verified_core_module(module: npa_cert::CoreModule) -> npa_cert::VerifiedModule {
        let cert = npa_cert::build_module_cert(module, &[]).expect("core module should certify");
        let bytes = npa_cert::encode_module_cert(&cert).expect("certificate should encode");
        let mut session = npa_cert::VerifierSession::new();
        npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
            .expect("certificate should verify")
    }

    fn verified_core_module_in_session(
        module: npa_cert::CoreModule,
        imports: &[npa_cert::VerifiedModule],
        session: &mut npa_cert::VerifierSession,
    ) -> npa_cert::VerifiedModule {
        let cert =
            npa_cert::build_module_cert(module, imports).expect("core module should certify");
        let bytes = npa_cert::encode_module_cert(&cert).expect("certificate should encode");
        npa_cert::verify_module_cert(&bytes, session, &npa_cert::AxiomPolicy::normal())
            .expect("certificate should verify")
    }

    fn eq_rec_alias_verified_module() -> npa_cert::VerifiedModule {
        let u = Level::param("u");
        let v = Level::param("v");
        verified_core_module(npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Std.EqRecAlias"),
            declarations: vec![Decl::Theorem {
                name: "eq_rec_alias".to_owned(),
                universe_params: vec!["u".to_owned(), "v".to_owned()],
                ty: npa_kernel::eq_rec_type(u.clone(), v.clone()),
                proof: Expr::konst("Eq.rec", vec![u, v]),
            }],
        })
    }

    fn alias_import() -> VerifiedImport {
        let u = Level::param("u");
        let module = verified_core_module(npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Std.Alias"),
            declarations: vec![
                Decl::Def {
                    name: "Alias.IdTy".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::sort(Level::imax(u.clone(), u.clone())),
                    ),
                    value: Expr::lam(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
                    ),
                    reducibility: Reducibility::Reducible,
                },
                Decl::Def {
                    name: "Alias.id".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::app(Expr::konst("Alias.IdTy", vec![u.clone()]), Expr::bvar(0)),
                    ),
                    value: Expr::lam(
                        "A",
                        Expr::sort(u),
                        Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
                    ),
                    reducibility: Reducibility::Reducible,
                },
            ],
        });

        VerifiedImport::from(&module)
    }

    fn unary_expr() -> Expr {
        Expr::konst("Unary", vec![])
    }

    fn unary_zero_expr() -> Expr {
        Expr::konst("Unary.zero", vec![])
    }

    fn unary_succ_expr(arg: Expr) -> Expr {
        Expr::app(Expr::konst("Unary.succ", vec![]), arg)
    }

    fn unary_rec_type_expr(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", unary_expr(), Expr::sort(level));
        let z_ty = Expr::app(Expr::bvar(0), unary_zero_expr());
        let s_ty = Expr::pi(
            "n",
            unary_expr(),
            Expr::pi(
                "ih",
                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                Expr::app(Expr::bvar(3), unary_succ_expr(Expr::bvar(1))),
            ),
        );

        Expr::pi(
            "motive",
            motive_ty,
            Expr::pi(
                "z",
                z_ty,
                Expr::pi(
                    "s",
                    s_ty,
                    Expr::pi("n", unary_expr(), Expr::app(Expr::bvar(3), Expr::bvar(0))),
                ),
            ),
        )
    }

    fn unary_rec_core_module() -> npa_cert::CoreModule {
        let data = npa_kernel::InductiveDecl::new(
            "Unary",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![
                npa_kernel::ConstructorDecl::new("Unary.zero", unary_expr()),
                npa_kernel::ConstructorDecl::new(
                    "Unary.succ",
                    Expr::pi("_", unary_expr(), unary_expr()),
                ),
            ],
            Some(npa_kernel::RecursorDecl::new(
                "Unary.rec",
                vec!["u".to_owned()],
                unary_rec_type_expr(Level::param("u")),
            )),
        );
        npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Test.Unary"),
            declarations: vec![Decl::Inductive {
                name: "Unary".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(type0()),
                data: Box::new(data),
            }],
        }
    }

    fn unary_rec_import() -> VerifiedImport {
        VerifiedImport {
            module: npa_cert::Name::from_dotted("Test.Unary"),
            export_hash: hash(30),
            certificate_hash: None,
            exports: Vec::new(),
            decl_interface_hashes: BTreeMap::from([(
                npa_cert::Name::from_dotted("Unary"),
                hash(30),
            )]),
            kernel_decls: unary_rec_core_module().declarations,
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    fn recursor_generated_type() -> Expr {
        let motive_level = Level::succ(type0());
        let motive = Expr::lam("_", unary_expr(), Expr::sort(type0()));
        let zero_case = Expr::sort(Level::zero());
        let succ_case = Expr::lam(
            "n",
            unary_expr(),
            Expr::lam("ih", Expr::sort(type0()), Expr::sort(Level::zero())),
        );

        Expr::apps(
            Expr::konst("Unary.rec", vec![motive_level]),
            vec![motive, zero_case, succ_case, unary_zero_expr()],
        )
    }

    fn generated_dependency_core_module() -> npa_cert::CoreModule {
        let p_ty = recursor_generated_type();

        npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Test.UseRec"),
            declarations: vec![
                Decl::Axiom {
                    name: "UseRec.P".to_owned(),
                    universe_params: Vec::new(),
                    ty: p_ty,
                },
                Decl::Axiom {
                    name: "UseRec.w".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("UseRec.P", vec![]),
                },
            ],
        }
    }

    fn generated_dependency_import() -> VerifiedImport {
        let p_ty = recursor_generated_type();

        VerifiedImport {
            module: npa_cert::Name::from_dotted("Test.UseRec"),
            export_hash: hash(31),
            certificate_hash: None,
            decl_interface_hashes: BTreeMap::from([
                (npa_cert::Name::from_dotted("UseRec.P"), hash(32)),
                (npa_cert::Name::from_dotted("UseRec.w"), hash(33)),
            ]),
            exports: vec![
                crate::VerifiedExport {
                    name: npa_cert::Name::from_dotted("UseRec.P"),
                    universe_params: Vec::new(),
                    ty: p_ty.clone(),
                    decl_interface_hash: hash(32),
                },
                crate::VerifiedExport {
                    name: npa_cert::Name::from_dotted("UseRec.w"),
                    universe_params: Vec::new(),
                    ty: Expr::konst("UseRec.P", vec![]),
                    decl_interface_hash: hash(33),
                },
            ],
            kernel_decls: vec![
                Decl::Axiom {
                    name: "UseRec.P".to_owned(),
                    universe_params: Vec::new(),
                    ty: p_ty,
                },
                Decl::Axiom {
                    name: "UseRec.w".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("UseRec.P", vec![]),
                },
            ],
            kernel_decl_dependencies: BTreeMap::new(),
        }
    }

    #[test]
    fn compiles_empty_machine_module_to_empty_core_module() {
        let module = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test.Empty"),
            "",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("empty module should compile in M1");

        assert_eq!(module.name, npa_cert::Name::from_dotted("Test.Empty"));
        assert!(module.declarations.is_empty());
    }

    #[test]
    fn loads_transitive_import_needed_by_generated_inductive_name() {
        let imports = [generated_dependency_import(), unary_rec_import()];
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Test.UseRec
def Test.copy : UseRec.P := UseRec.w",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect("generated inductive dependency should queue its wrapper declaration");
    }

    #[test]
    fn certificate_ignores_unimported_verified_modules() {
        let mut session = npa_cert::VerifierSession::new();
        let unused = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Unused.Module"),
                declarations: vec![Decl::Axiom {
                    name: "Test.ok".to_owned(),
                    universe_params: vec![],
                    ty: Expr::sort(type0()),
                }],
            },
            &[],
            &mut session,
        );

        compile_machine_source_to_certificate(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "def Test.ok : Sort 2 := Type",
            &[unused],
            &MachineCompileOptions::default(),
        )
        .expect("unimported verified modules should not be passed to certificate construction");
    }

    #[test]
    fn certificate_includes_transitive_import_needed_by_generated_inductive_name() {
        let mut session = npa_cert::VerifierSession::new();
        let unary = verified_core_module_in_session(unary_rec_core_module(), &[], &mut session);
        let use_rec = verified_core_module_in_session(
            generated_dependency_core_module(),
            std::slice::from_ref(&unary),
            &mut session,
        );

        let cert = compile_machine_source_to_certificate(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Test.UseRec
def Test.copy : UseRec.P := UseRec.w",
            &[use_rec, unary],
            &MachineCompileOptions::default(),
        )
        .expect("certificate construction should receive transitive import dependencies");

        assert!(cert
            .imports
            .iter()
            .any(|import| import.module == npa_cert::Name::from_dotted("Test.UseRec")));
        assert!(cert
            .imports
            .iter()
            .any(|import| import.module == npa_cert::Name::from_dotted("Test.Unary")));
    }

    #[test]
    fn certificate_import_closure_ignores_unused_export_dependencies() {
        let mut session = npa_cert::VerifierSession::new();
        let direct_unit = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.DirectUnit"),
                declarations: vec![Decl::Axiom {
                    name: "Unit".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0()),
                }],
            },
            &[],
            &mut session,
        );
        let collision = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.Collision"),
                declarations: vec![Decl::Axiom {
                    name: "Unit".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0()),
                }],
            },
            &[],
            &mut session,
        );
        let wide = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.Wide"),
                declarations: vec![
                    Decl::Axiom {
                        name: "Wide.Needed".to_owned(),
                        universe_params: Vec::new(),
                        ty: Expr::sort(type0()),
                    },
                    Decl::Axiom {
                        name: "Wide.Unused".to_owned(),
                        universe_params: Vec::new(),
                        ty: Expr::konst("Unit", vec![]),
                    },
                ],
            },
            std::slice::from_ref(&collision),
            &mut session,
        );
        let module = npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Test.UseWide"),
            declarations: vec![
                Decl::Axiom {
                    name: "UseWide.uses_unit".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Unit", vec![]),
                },
                Decl::Axiom {
                    name: "UseWide.uses_needed".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Wide.Needed", vec![]),
                },
            ],
        };
        let imports = [&direct_unit, &wide, &collision];

        let certificate_imports =
            certificate_import_refs_for_module_refs(&module, &[0, 1], &imports, FileId(0))
                .expect("unused export dependencies should not enter the certificate closure");

        assert_eq!(certificate_imports.len(), 2);
        assert!(certificate_imports
            .iter()
            .any(|import| import.module() == direct_unit.module()));
        assert!(certificate_imports
            .iter()
            .any(|import| import.module() == wide.module()));
        assert!(!certificate_imports
            .iter()
            .any(|import| import.module() == collision.module()));
        npa_cert::build_module_cert_from_import_refs(module, &certificate_imports)
            .expect("filtered certificate imports should avoid duplicate imported names");
    }

    #[test]
    fn certificate_provider_map_resolves_referenced_duplicate_export() {
        let mut session = npa_cert::VerifierSession::new();
        let direct_unit = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.DirectUnit"),
                declarations: vec![Decl::Axiom {
                    name: "Unit".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0()),
                }],
            },
            &[],
            &mut session,
        );
        let collision = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.Collision"),
                declarations: vec![
                    Decl::Axiom {
                        name: "Unit".to_owned(),
                        universe_params: Vec::new(),
                        ty: Expr::sort(type0()),
                    },
                    Decl::Axiom {
                        name: "Collision.Needed".to_owned(),
                        universe_params: Vec::new(),
                        ty: Expr::sort(type0()),
                    },
                ],
            },
            &[],
            &mut session,
        );
        let wide = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.Wide"),
                declarations: vec![Decl::Def {
                    name: "Wide.Needed".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0()),
                    value: Expr::konst("Collision.Needed", vec![]),
                    reducibility: Reducibility::Reducible,
                }],
            },
            std::slice::from_ref(&collision),
            &mut session,
        );
        let module = npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Test.UseWide"),
            declarations: vec![
                Decl::Axiom {
                    name: "UseWide.uses_unit".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Unit", vec![]),
                },
                Decl::Axiom {
                    name: "UseWide.uses_needed".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Wide.Needed", vec![]),
                },
            ],
        };
        let imports = [&direct_unit, &wide, &collision];

        let (certificate_imports, preferred_imports) =
            certificate_import_refs_and_providers_for_module_refs(
                &module,
                &[0, 1],
                &imports,
                FileId(0),
            )
            .expect("interface dependency should add the collision module");

        assert_eq!(certificate_imports.len(), 3);
        assert!(certificate_imports
            .iter()
            .any(|import| import.module() == collision.module()));
        assert_eq!(
            preferred_imports
                .get(&npa_cert::Name::from_dotted("Unit"))
                .map(|entry| &entry.module),
            Some(direct_unit.module())
        );
        npa_cert::build_module_cert_from_import_refs_with_preferred_imports(
            module,
            &certificate_imports,
            &preferred_imports,
        )
        .expect("preferred source provider should suppress duplicate exported names");
    }

    #[test]
    fn certificate_import_closure_rejects_ambiguous_available_dependency_provider() {
        let mut session = npa_cert::VerifierSession::new();
        let a = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.A"),
                declarations: vec![Decl::Axiom {
                    name: "A.Carrier".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0()),
                }],
            },
            &[],
            &mut session,
        );
        let b = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Test.B"),
                declarations: vec![Decl::Def {
                    name: "B.Surface".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(type0()),
                    value: Expr::konst("A.Carrier", vec![]),
                    reducibility: Reducibility::Reducible,
                }],
            },
            std::slice::from_ref(&a),
            &mut session,
        );
        let c = npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Test.C"),
            declarations: vec![Decl::Def {
                name: "C.SurfaceAlias".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(type0()),
                value: Expr::konst("B.Surface", vec![]),
                reducibility: Reducibility::Reducible,
            }],
        };
        let imports = [&b, &a, &a];

        let err = certificate_import_refs_for_module_refs(&c, &[0], &imports, FileId(0))
            .expect_err("duplicate available dependency providers must be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
        assert!(err
            .message
            .contains("multiple matching providers in the verified import set"));
    }

    #[test]
    fn certificate_import_closure_ignores_builtin_axiom_dependencies() {
        let import = eq_rec_alias_verified_module();
        let u = Level::param("u");
        let v = Level::param("v");
        let module = npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Test"),
            declarations: vec![Decl::Def {
                name: "Test.copy_eq_rec".to_owned(),
                universe_params: vec!["u".to_owned(), "v".to_owned()],
                ty: npa_kernel::eq_rec_type(u.clone(), v.clone()),
                value: Expr::konst("eq_rec_alias", vec![u, v]),
                reducibility: Reducibility::Reducible,
            }],
        };

        let imports =
            certificate_imports_for_module(&module, &[0], std::slice::from_ref(&import), FileId(0))
                .expect("builtin Eq.rec axiom dependency should not require a verified import");

        assert_eq!(imports.len(), 1);
        assert_eq!(imports[0].module(), import.module());
    }

    #[test]
    fn machine_source_certificate_verifies_from_source_free_bytes() {
        let cert = compile_machine_source_to_certificate(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "def Test.id.{u} (A : Sort u) (x : A) : A := x",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("machine source should compile to a certificate");
        let bytes = npa_cert::encode_module_cert(&cert).expect("certificate should encode");
        let decoded = npa_cert::decode_module_cert(&bytes).expect("certificate should decode");
        assert_eq!(decoded, cert);

        let mut session = npa_cert::VerifierSession::new();
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &npa_cert::AxiomPolicy::normal())
                .expect("encoded certificate should verify without source");

        assert_eq!(verified.module(), &npa_cert::Name::from_dotted("Test"));
    }

    #[test]
    fn machine_source_certificate_hash_is_deterministic() {
        let source = "def Test.id.{u} (A : Sort u) (x : A) : A := x";
        let first = compile_machine_source_to_certificate(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            source,
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("first certificate should compile");
        let second = compile_machine_source_to_certificate(
            FileId(99),
            npa_cert::Name::from_dotted("Test"),
            source,
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("second certificate should compile");

        assert_eq!(
            first.hashes.certificate_hash,
            second.hashes.certificate_hash
        );
        assert_eq!(
            npa_cert::encode_module_cert(&first).expect("first certificate should encode"),
            npa_cert::encode_module_cert(&second).expect("second certificate should encode")
        );
    }

    #[test]
    fn machine_source_certificate_uses_verified_import_hashes() {
        let mut import_session = npa_cert::VerifierSession::new();
        let nat = verified_core_module_in_session(
            npa_cert::CoreModule {
                name: npa_cert::Name::from_dotted("Std.Nat.Basic"),
                declarations: vec![Decl::Axiom {
                    name: "Nat".to_owned(),
                    universe_params: vec![],
                    ty: Expr::sort(type0()),
                }],
            },
            &[],
            &mut import_session,
        );

        let cert = compile_machine_source_to_certificate(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Nat.Basic
def Test.id_nat (n : Nat) : Nat := n",
            std::slice::from_ref(&nat),
            &MachineCompileOptions::default(),
        )
        .expect("imported machine source should compile to a certificate");

        assert_eq!(cert.imports.len(), 1);
        assert_eq!(cert.imports[0].module, nat.module().clone());
        assert_eq!(cert.imports[0].export_hash, nat.export_hash());
        assert_eq!(
            cert.imports[0].certificate_hash,
            Some(nat.certificate_hash())
        );

        let bytes = npa_cert::encode_module_cert(&cert).expect("certificate should encode");
        let mut verify_session = npa_cert::VerifierSession::new();
        verify_session.register_verified_module(nat);
        npa_cert::verify_module_cert(
            &bytes,
            &mut verify_session,
            &npa_cert::AxiomPolicy::normal(),
        )
        .expect("encoded certificate should verify against registered verified import");
    }

    #[test]
    fn ignores_unimported_verified_interfaces_when_checking_local_decls() {
        let imports = [verified_import("Unused.Module", &[("Test.ok", &[])])];
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "def Test.ok : Sort 2 := Type",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect("unimported verified interfaces should not populate the kernel env");
    }

    #[test]
    fn elaborates_explicit_id_to_core_def() {
        let module = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "def Test.id.{u} (A : Sort u) (x : A) : A := x",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("explicit id should elaborate");

        let u = Level::param("u");
        assert_eq!(
            module.declarations,
            vec![Decl::Def {
                name: "Test.id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
                ),
                value: Expr::lam(
                    "A",
                    Expr::sort(u),
                    Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
                ),
                reducibility: Reducibility::Reducible,
            }]
        );
    }

    #[test]
    fn elaborates_explicit_eq_refl_to_core_theorem() {
        let imports = [nat_import(), eq_import()];
        let module = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem Test.self_eq (n : Nat) : Eq.{1} Nat n n := @Eq.refl.{1} Nat n",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect("explicit Eq.refl theorem should elaborate");

        let eq_nn = Expr::apps(
            Expr::konst("Eq", vec![type0()]),
            vec![nat(), Expr::bvar(0), Expr::bvar(0)],
        );
        let proof = Expr::apps(
            Expr::konst("Eq.refl", vec![type0()]),
            vec![nat(), Expr::bvar(0)],
        );

        assert_eq!(
            module.declarations,
            vec![Decl::Theorem {
                name: "Test.self_eq".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::pi("n", nat(), eq_nn),
                proof: Expr::lam("n", nat(), proof),
            }]
        );
    }

    #[test]
    fn term_level_api_checks_exact_eq_refl_against_expected_type() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "n".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );
        let expected = Expr::apps(
            Expr::konst("Eq", vec![type0()]),
            vec![nat(), Expr::bvar(0), Expr::bvar(0)],
        );

        let checked = elaborate_machine_term_check(
            "@Eq.refl.{1} Nat n",
            &context,
            &expected,
            &MachineCompileOptions::default(),
        )
        .expect("explicit Eq.refl should close the goal");

        assert_eq!(
            checked.expr,
            Expr::apps(
                Expr::konst("Eq.refl", vec![type0()]),
                vec![nat(), Expr::bvar(0)]
            )
        );
        assert_eq!(
            checked.constants,
            vec![
                crate::MachineResolvedConstant {
                    name: npa_cert::Name::from_dotted("Eq.refl"),
                    decl_interface_hash: hash(3),
                },
                crate::MachineResolvedConstant {
                    name: npa_cert::Name::from_dotted("Nat"),
                    decl_interface_hash: hash(2),
                },
            ]
        );
        assert_ne!(checked.core_hash, [0; 32]);
    }

    #[test]
    fn term_level_check_result_is_deterministic_for_same_input() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "n".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );
        let expected = Expr::apps(
            Expr::konst("Eq", vec![type0()]),
            vec![nat(), Expr::bvar(0), Expr::bvar(0)],
        );

        let first = elaborate_machine_term_check(
            "@Eq.refl.{1} Nat n",
            &context,
            &expected,
            &MachineCompileOptions::default(),
        )
        .expect("first term should check");
        let second = elaborate_machine_term_check(
            "@Eq.refl.{1} Nat n",
            &context,
            &expected,
            &MachineCompileOptions::default(),
        )
        .expect("second term should check");

        assert_eq!(first, second);
    }

    #[test]
    fn term_level_api_rejects_global_scope_decl_hash_mismatch() {
        let imports = [nat_import()];
        let mut context = term_context(&imports, Vec::new(), Vec::new());
        match &mut context.global_scope.entries[0] {
            crate::MachineGlobalScopeEntry::Imported {
                decl_interface_hash,
                ..
            }
            | crate::MachineGlobalScopeEntry::CurrentModule {
                decl_interface_hash,
                ..
            }
            | crate::MachineGlobalScopeEntry::CurrentGenerated {
                decl_interface_hash,
                ..
            } => *decl_interface_hash = hash(99),
        }

        let err = elaborate_machine_term_check(
            "Nat",
            &context,
            &Expr::sort(type0()),
            &MachineCompileOptions::default(),
        )
        .expect_err("term context declaration hash mismatch should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_rejects_import_export_kernel_type_mismatch() {
        let mut import = nat_import();
        import.exports[0].ty = Expr::sort(Level::zero());
        let imports = [import];

        let err = machine_term_context_from_verified_imports(
            &imports,
            &imports,
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect_err("verified import export metadata must match the kernel environment");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_rejects_inductive_export_sort_without_full_kernel_type() {
        let u = Level::param("u");
        let data = npa_kernel::InductiveDecl::new(
            "Param.Box",
            vec!["u".to_owned()],
            vec![npa_kernel::Binder::new("A", Expr::sort(u.clone()))],
            Vec::new(),
            u.clone(),
            Vec::new(),
            None,
        );
        let import = VerifiedImport {
            module: npa_cert::Name::from_dotted("Test.Param"),
            export_hash: hash(61),
            certificate_hash: None,
            decl_interface_hashes: BTreeMap::from([(
                npa_cert::Name::from_dotted("Param.Box"),
                hash(62),
            )]),
            exports: vec![crate::VerifiedExport {
                name: npa_cert::Name::from_dotted("Param.Box"),
                universe_params: vec!["u".to_owned()],
                ty: Expr::sort(u),
                decl_interface_hash: hash(62),
            }],
            kernel_decls: vec![Decl::Inductive {
                name: "Param.Box".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::sort(type0()),
                data: Box::new(data),
            }],
            kernel_decl_dependencies: BTreeMap::new(),
        };
        let imports = [import];

        let err = machine_term_context_from_verified_imports(
            &imports,
            &imports,
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect_err("inductive exports must match the full kernel declaration type");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_allows_unused_ambiguous_direct_exports() {
        let left = verified_import("Left.Module", &[("Shared.X", &[]), ("Direct.y", &[])]);
        let mut right = verified_import("Right.Module", &[("Shared.X", &[])]);
        set_single_axiom_ty(&mut right, Expr::sort(type0()));
        let imports = [left, right];

        let context = machine_term_context_from_verified_imports(
            &imports,
            &imports,
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect("unused ambiguous direct exports should not poison the context");

        elaborate_machine_term_check(
            "Direct.y",
            &context,
            &Expr::sort(Level::zero()),
            &MachineCompileOptions::default(),
        )
        .expect("unambiguous direct export should remain usable");

        let err = elaborate_machine_term_check(
            "Shared.X",
            &context,
            &Expr::sort(Level::zero()),
            &MachineCompileOptions::default(),
        )
        .expect_err("ambiguous exact direct export should still be rejected when referenced");

        assert_eq!(err.kind, MachineDiagnosticKind::AmbiguousGlobalName);
    }

    #[test]
    fn term_context_ignores_unused_available_export_collision() {
        let direct = verified_import("Direct.Module", &[("Common.X", &[])]);
        let mut available = verified_import("Available.Module", &[("Common.X", &[])]);
        set_single_axiom_ty(&mut available, Expr::sort(type0()));

        let context = machine_term_context_from_verified_imports(
            std::slice::from_ref(&direct),
            std::slice::from_ref(&available),
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect("unused available export collision should not reject the context");

        elaborate_machine_term_check(
            "Common.X",
            &context,
            &Expr::sort(Level::zero()),
            &MachineCompileOptions::default(),
        )
        .expect("direct export should remain usable");
    }

    #[test]
    fn term_context_rejects_loaded_available_export_kernel_type_mismatch() {
        let direct = direct_using_hidden_import();
        let mut hidden = hidden_import();
        hidden.exports[0].ty = Expr::sort(type0());

        let err = machine_term_context_from_verified_imports(
            std::slice::from_ref(&direct),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect_err("loaded available export metadata must match its kernel declaration");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_rejects_available_dependency_hash_mismatch() {
        let direct = direct_using_hidden_import();
        let mut hidden = hidden_import();
        hidden.exports[0].decl_interface_hash = hash(99);

        let err = machine_term_context_from_verified_imports(
            std::slice::from_ref(&direct),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect_err("available dependency must match the direct import dependency hash");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_rejects_existing_env_dependency_hash_mismatch() {
        let hidden = hidden_import();
        let mismatched = direct_using_hidden_dependency(
            "ZDirect.Module",
            hash(61),
            "ZDirect.x",
            hash(62),
            "Hidden.Other",
            hash(63),
            hash(99),
        );

        let err = machine_term_context_from_verified_imports(
            &[hidden, mismatched],
            &[],
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect_err("existing env declaration must satisfy explicit dependency identity and hash");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_accepts_existing_env_dependency_when_matching_direct_import_loaded() {
        let hidden = hidden_import();
        let hidden_other = verified_import("Hidden.Other", &[("Hidden.Thing", &[])]);
        let direct = direct_using_hidden_dependency(
            "ZDirect.Module",
            hash(61),
            "ZDirect.x",
            hash(62),
            "Hidden.Other",
            hash(1),
            hash(2),
        );
        let imports = [hidden, hidden_other, direct];

        machine_term_context_from_verified_imports(
            &imports,
            &[],
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect("matching direct import identity should satisfy explicit dependency");
    }

    #[test]
    fn term_context_accepts_existing_env_dependency_when_matching_available_import_is_backed_by_env(
    ) {
        let hidden = hidden_import();
        let hidden_other = verified_import("Hidden.Other", &[("Hidden.Thing", &[])]);
        let direct = direct_using_hidden_dependency(
            "ZDirect.Module",
            hash(61),
            "ZDirect.x",
            hash(62),
            "Hidden.Other",
            hash(1),
            hash(2),
        );

        machine_term_context_from_verified_imports(
            &[hidden, direct],
            std::slice::from_ref(&hidden_other),
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect("matching available import identity should be recorded when Env already has the same declaration");
    }

    #[test]
    fn term_context_records_only_loaded_available_interface_hashes() {
        let direct = direct_using_hidden_import();
        let hidden = hidden_import();
        let mut colliding = hidden_import();
        colliding.exports[0].decl_interface_hash = hash(99);
        let context = machine_term_context_from_verified_imports(
            std::slice::from_ref(&direct),
            &[hidden, colliding],
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect("exact dependency hash should select the matching available import");

        assert!(context
            .kernel_env
            .has_decl_interface_hash("Hidden.Thing", &hash(2)));
        assert!(!context
            .kernel_env
            .has_decl_interface_hash("Hidden.Thing", &hash(99)));
    }

    #[test]
    fn term_context_rejects_imported_builtin_name_dependency_hash_mismatch() {
        let direct = direct_using_imported_nat_dependency(hash(99));

        let err = machine_term_context_from_verified_imports(
            std::slice::from_ref(&direct),
            std::slice::from_ref(&direct),
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect_err("non-builtin dependency hash for Nat must not be satisfied by builtin Nat");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_context_does_not_expose_available_transitive_imports() {
        let direct = direct_using_hidden_import();
        let hidden = hidden_import();
        let context = machine_term_context_from_verified_imports(
            std::slice::from_ref(&direct),
            std::slice::from_ref(&hidden),
            Vec::new(),
            Vec::new(),
            crate::Span::empty(FileId(0)),
        )
        .expect("available transitive import should be usable by the kernel env");

        elaborate_machine_term_check(
            "Direct.x",
            &context,
            &Expr::konst("Hidden.Thing", vec![]),
            &MachineCompileOptions::default(),
        )
        .expect("direct import should remain usable");

        let err = elaborate_machine_term_check(
            "Hidden.Thing",
            &context,
            &Expr::sort(type0()),
            &MachineCompileOptions::default(),
        )
        .expect_err("available transitive import should not enter the direct lookup scope");

        assert_eq!(err.kind, MachineDiagnosticKind::UnknownGlobalName);
    }

    #[test]
    fn term_context_loads_import_with_builtin_eq_rec_dependency() {
        let import = eq_rec_alias_verified_module();
        let context = crate::MachineTermElabContext::from_verified_modules(
            std::slice::from_ref(&import),
            std::slice::from_ref(&import),
            Vec::new(),
            vec!["u".to_owned(), "v".to_owned()],
        )
        .expect("verified import that references builtin Eq.rec should load");
        let expected = npa_kernel::eq_rec_type(Level::param("u"), Level::param("v"));
        let checked = elaborate_machine_term_check(
            "@eq_rec_alias.{u, v}",
            &context,
            &expected,
            &MachineCompileOptions::default(),
        )
        .expect("imported theorem with builtin dependency should elaborate");

        assert_eq!(
            checked.expr,
            Expr::konst("eq_rec_alias", vec![Level::param("u"), Level::param("v")])
        );
    }

    #[test]
    fn term_level_api_infers_from_decoded_canonical_ast() {
        let imports = [nat_import()];
        let context = term_context(&imports, Vec::new(), Vec::new());
        let canonical = crate::canonicalize_machine_term_source("Nat")
            .expect("term source should canonicalize");
        let ast = crate::decode_machine_term_source_canonical(&canonical.canonical_bytes)
            .expect("canonical term source should decode");

        let (expr, inferred_type) = elaborate_machine_term_infer_from_ast(
            &ast,
            &context,
            &MachineCompileOptions::default(),
        )
        .expect("decoded term AST should infer");

        assert_eq!(expr, nat());
        assert_eq!(inferred_type, Expr::sort(type0()));
    }

    #[test]
    fn term_level_contextual_hash_commits_to_import_decl_interface_hash() {
        let imports = [nat_import()];
        let context = term_context(&imports, Vec::new(), Vec::new());
        let first = elaborate_machine_term_check(
            "Nat",
            &context,
            &Expr::sort(type0()),
            &MachineCompileOptions::default(),
        )
        .expect("Nat should check");

        let mut changed = nat_import();
        changed.exports[0].decl_interface_hash = hash(99);
        let changed_imports = [changed];
        let changed_context = term_context(&changed_imports, Vec::new(), Vec::new());
        let second = elaborate_machine_term_check(
            "Nat",
            &changed_context,
            &Expr::sort(type0()),
            &MachineCompileOptions::default(),
        )
        .expect("Nat should still check with a different verified interface hash");

        assert_eq!(first.core_hash, second.core_hash);
        assert_ne!(first.contextual_core_hash, second.contextual_core_hash);
    }

    #[test]
    fn term_level_contextual_hash_commits_to_current_decl_interface_hash() {
        let checked = crate::MachineCheckedCurrentDecl {
            name: npa_cert::Name::from_dotted("Current.T"),
            source_index: 0,
            decl_interface_hash: hash(10),
            decl: Decl::Axiom {
                name: "Current.T".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(type0()),
            },
        };
        let context = crate::MachineTermElabContext::from_verified_modules_and_current_decls(
            &[],
            &[],
            std::slice::from_ref(&checked),
            &[],
            Vec::new(),
            Vec::new(),
        )
        .expect("checked current declaration should build a term context");
        let first = elaborate_machine_term_check(
            "Current.T",
            &context,
            &Expr::sort(type0()),
            &MachineCompileOptions::default(),
        )
        .expect("checked current declaration should elaborate");

        let mut changed = checked;
        changed.decl_interface_hash = hash(11);
        let changed_context =
            crate::MachineTermElabContext::from_verified_modules_and_current_decls(
                &[],
                &[],
                std::slice::from_ref(&changed),
                &[],
                Vec::new(),
                Vec::new(),
            )
            .expect("changed checked current declaration should build a term context");
        let second = elaborate_machine_term_check(
            "Current.T",
            &changed_context,
            &Expr::sort(type0()),
            &MachineCompileOptions::default(),
        )
        .expect("changed checked current declaration should elaborate");

        assert_eq!(first.core_hash, second.core_hash);
        assert_ne!(first.contextual_core_hash, second.contextual_core_hash);
    }

    #[test]
    fn term_level_contextual_hash_uses_current_generated_parent_decl_interface_hash() {
        let checked = crate::MachineCheckedCurrentDecl {
            name: npa_cert::Name::from_dotted("Unary"),
            source_index: 0,
            decl_interface_hash: hash(10),
            decl: unary_rec_core_module().declarations[0].clone(),
        };
        let generated = crate::MachineCheckedCurrentGeneratedDecl {
            name: npa_cert::Name::from_dotted("Unary.zero"),
            parent_source_index: 0,
            decl_interface_hash: hash(10),
        };
        let context = crate::MachineTermElabContext::from_verified_modules_and_current_decls(
            &[],
            &[],
            std::slice::from_ref(&checked),
            std::slice::from_ref(&generated),
            Vec::new(),
            Vec::new(),
        )
        .expect("checked current generated declaration should build a term context");
        let first = elaborate_machine_term_check(
            "Unary.zero",
            &context,
            &unary_expr(),
            &MachineCompileOptions::default(),
        )
        .expect("checked current generated declaration should elaborate");

        let mut changed_checked = checked;
        changed_checked.decl_interface_hash = hash(12);
        let mut changed_generated = generated;
        changed_generated.decl_interface_hash = hash(12);
        let changed_context =
            crate::MachineTermElabContext::from_verified_modules_and_current_decls(
                &[],
                &[],
                std::slice::from_ref(&changed_checked),
                std::slice::from_ref(&changed_generated),
                Vec::new(),
                Vec::new(),
            )
            .expect("changed checked current generated declaration should build a term context");
        let second = elaborate_machine_term_check(
            "Unary.zero",
            &changed_context,
            &unary_expr(),
            &MachineCompileOptions::default(),
        )
        .expect("changed checked current generated declaration should elaborate");

        assert_eq!(first.core_hash, second.core_hash);
        assert_ne!(first.contextual_core_hash, second.contextual_core_hash);
    }

    #[test]
    fn term_context_rejects_current_generated_decl_hash_mismatch() {
        let checked = crate::MachineCheckedCurrentDecl {
            name: npa_cert::Name::from_dotted("Unary"),
            source_index: 0,
            decl_interface_hash: hash(10),
            decl: unary_rec_core_module().declarations[0].clone(),
        };
        let generated = crate::MachineCheckedCurrentGeneratedDecl {
            name: npa_cert::Name::from_dotted("Unary.zero"),
            parent_source_index: 0,
            decl_interface_hash: hash(11),
        };

        let err = crate::MachineTermElabContext::from_verified_modules_and_current_decls(
            &[],
            &[],
            std::slice::from_ref(&checked),
            std::slice::from_ref(&generated),
            Vec::new(),
            Vec::new(),
        )
        .expect_err("current generated declarations must use the checked parent interface hash");

        assert_eq!(err.kind, MachineDiagnosticKind::ImportResolutionError);
    }

    #[test]
    fn term_level_api_returns_structured_error_for_type_mismatch() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "n".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );

        let err = elaborate_machine_term_check(
            "@Eq.refl.{1} Nat n",
            &context,
            &nat(),
            &MachineCompileOptions::default(),
        )
        .expect_err("Eq.refl should not check against Nat");

        assert_eq!(err.kind, MachineDiagnosticKind::TypeMismatch);
        let payload = err
            .payload
            .expect("type mismatch should include expected/actual hashes");
        assert_eq!(
            payload.expected_hash,
            Some(hash_owner_free_core_expr(&nat()))
        );
        assert!(payload.actual_hash.is_some());
        assert!(err.suggestions.is_empty());
    }

    #[test]
    fn term_level_api_uses_closed_global_scope_for_short_name_rejection() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(&imports, Vec::new(), Vec::new());

        let err = elaborate_machine_term_check(
            "refl",
            &context,
            &nat(),
            &MachineCompileOptions::default(),
        )
        .expect_err("short global suffix should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::ShortGlobalName);
        assert_eq!(err.payload, None);
        assert!(err.suggestions.is_empty());
    }

    #[test]
    fn repair_mode_suggests_fully_qualified_name_for_short_global() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(&imports, Vec::new(), Vec::new());
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("refl", &context, &nat(), &options)
            .expect_err("short global suffix should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::ShortGlobalName);
        let payload = err.payload.expect("short global should include candidates");
        assert_eq!(
            payload.candidates,
            vec![MachineRepairCandidate {
                name: npa_cert::Name::from_dotted("Eq.refl"),
                decl_interface_hash: Some(hash(3)),
            }]
        );
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(
            err.suggestions[0].kind,
            MachineRepairSuggestionKind::UseFullyQualifiedName
        );
        assert_eq!(err.suggestions[0].replacement.as_deref(), Some("Eq.refl"));
    }

    #[test]
    fn repair_mode_failed_candidate_diagnostic_is_deterministic() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "n".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let first = elaborate_machine_term_check("Eq.refl n", &context, &nat(), &options)
            .expect_err("first failed candidate should return a repair diagnostic");
        let second = elaborate_machine_term_check("Eq.refl n", &context, &nat(), &options)
            .expect_err("second failed candidate should return the same repair diagnostic");

        // M9 fixes the structured repair output, not human-facing messages or spans.
        assert_eq!(first.kind, second.kind);
        assert_eq!(first.payload, second.payload);
        assert_eq!(first.suggestions, second.suggestions);
    }

    #[test]
    fn repair_mode_omits_short_name_replacement_for_ambiguous_exact_name() {
        let left = verified_import("Left.Module", &[("Shared.X", &[]), ("Direct.y", &[])]);
        let mut right = verified_import("Right.Module", &[("Shared.X", &[])]);
        set_single_axiom_ty(&mut right, Expr::sort(type0()));
        let imports = [left, right];
        let context = term_context(&imports, Vec::new(), Vec::new());
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("X", &context, &Expr::sort(type0()), &options)
            .expect_err("short suffix should be rejected without an ambiguous replacement");

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
    fn repair_mode_suggests_explicit_arguments_for_implicit_global_use() {
        let imports = [eq_import()];
        let context = term_context(&imports, Vec::new(), vec!["u".to_owned()]);
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("Eq.refl", &context, &Expr::sort(type0()), &options)
            .expect_err("implicit global use should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);
        let payload = err.payload.expect("implicit error should include payload");
        assert_eq!(payload.head_symbol.as_deref(), Some("Eq.refl"));
        assert_eq!(payload.expected_universe_args, Some(1));
        assert_eq!(payload.actual_universe_args, Some(0));
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(
            err.suggestions[0].kind,
            MachineRepairSuggestionKind::InsertExplicitArguments
        );
        assert_eq!(
            err.suggestions[0].replacement.as_deref(),
            Some("@Eq.refl.{u}")
        );
    }

    #[test]
    fn repair_mode_suggests_inserted_type_argument_for_eq_refl_app() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "n".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("Eq.refl n", &context, &nat(), &options)
            .expect_err("implicit Eq.refl app should be rejected with a repair suggestion");

        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(
            err.suggestions[0].kind,
            MachineRepairSuggestionKind::InsertExplicitArguments
        );
        assert_eq!(
            err.suggestions[0].replacement.as_deref(),
            Some("@Eq.refl.{1} Nat n")
        );
    }

    #[test]
    fn repair_mode_omits_replacement_when_type_argument_cannot_be_printed() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "f".to_owned(),
                ty: Expr::pi("x", nat(), nat()),
                value: None,
            }],
            Vec::new(),
        );
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("Eq.refl f", &context, &nat(), &options).expect_err(
            "non-printable inserted type argument should not produce a bad replacement",
        );

        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(err.suggestions[0].replacement, None);
    }

    #[test]
    fn repair_mode_omits_replacement_when_generated_candidate_does_not_elaborate() {
        let imports = [nat_import(), poly_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "x".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("Poly.K x", &context, &nat(), &options)
            .expect_err("incomplete generated repair should not be offered as a replacement");

        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(err.suggestions[0].replacement, None);
    }

    #[test]
    fn repair_mode_uses_level_value_for_first_binder_match() {
        let imports = [eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "A".to_owned(),
                ty: Expr::sort(Level::max(Level::param("u"), Level::param("v"))),
                value: None,
            }],
            vec!["u".to_owned(), "v".to_owned()],
        );
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err =
            elaborate_machine_term_check("Eq.refl A", &context, &Expr::sort(type0()), &options)
                .expect_err("repair mode should still reject missing explicit arguments");

        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);
        assert_eq!(
            err.suggestions[0].replacement.as_deref(),
            Some("@Eq.refl.{max u v} A")
        );
    }

    #[test]
    fn repair_mode_suggests_missing_universe_arguments() {
        let imports = [eq_import()];
        let context = term_context(&imports, Vec::new(), vec!["u".to_owned()]);
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err =
            elaborate_machine_term_check("@Eq.refl", &context, &Expr::sort(type0()), &options)
                .expect_err("explicit global use should require universe arguments");

        assert_eq!(err.kind, MachineDiagnosticKind::MissingExplicitUniverse);
        let payload = err.payload.expect("universe error should include payload");
        assert_eq!(payload.head_symbol.as_deref(), Some("Eq.refl"));
        assert_eq!(payload.expected_universe_args, Some(1));
        assert_eq!(payload.actual_universe_args, Some(0));
        assert_eq!(err.suggestions.len(), 1);
        assert_eq!(
            err.suggestions[0].kind,
            MachineRepairSuggestionKind::InsertExplicitUniverseArguments
        );
        assert_eq!(
            err.suggestions[0].replacement.as_deref(),
            Some("@Eq.refl.{u}")
        );
    }

    #[test]
    fn repair_mode_suggests_universe_for_explicit_eq_refl_app() {
        let imports = [nat_import(), eq_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "n".to_owned(),
                ty: nat(),
                value: None,
            }],
            Vec::new(),
        );
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = elaborate_machine_term_check("@Eq.refl Nat n", &context, &nat(), &options)
            .expect_err("missing universe arguments should be rejected with a repair suggestion");

        assert_eq!(err.kind, MachineDiagnosticKind::MissingExplicitUniverse);
        assert_eq!(
            err.suggestions[0].replacement.as_deref(),
            Some("@Eq.refl.{1} Nat n")
        );
    }

    #[test]
    fn repair_mode_module_compile_suggests_fully_qualified_short_name() {
        let imports = [nat_import(), eq_import()];
        let options = MachineCompileOptions {
            mode: MachineSurfaceMode::Repair,
            ..MachineCompileOptions::default()
        };

        let err = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem Test.bad (n : Nat) : Eq.{1} Nat n n := refl",
            &imports,
            &options,
        )
        .expect_err("module resolver should attach repair suggestions in Repair mode");

        assert_eq!(err.kind, MachineDiagnosticKind::ShortGlobalName);
        assert_eq!(err.suggestions[0].replacement.as_deref(), Some("Eq.refl"));
    }

    #[test]
    fn term_level_api_rejects_local_name_shadowing_global_root() {
        let imports = [nat_import()];
        let context = term_context(
            &imports,
            vec![MachineLocalDecl {
                name: "Nat".to_owned(),
                ty: Expr::sort(type0()),
                value: None,
            }],
            Vec::new(),
        );

        let err = elaborate_machine_term_check(
            "Nat",
            &context,
            &nat(),
            &MachineCompileOptions::default(),
        )
        .expect_err("local/global root collision should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::GlobalShadowedByLocal);
    }

    #[test]
    fn core_module_erases_machine_surface_import_items() {
        let imports = [nat_import()];
        let module = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Nat.Basic
def Test.id_nat (n : Nat) : Nat := n",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect("imported Nat declaration should elaborate and kernel-check");

        assert_eq!(module.name, npa_cert::Name::from_dotted("Test"));
        assert_eq!(
            module.declarations,
            vec![Decl::Def {
                name: "Test.id_nat".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::pi("n", nat(), nat()),
                value: Expr::lam("n", nat(), Expr::bvar(0)),
                reducibility: Reducibility::Reducible,
            }]
        );
    }

    #[test]
    fn rejects_eq_refl_without_explicit_arguments() {
        let imports = [nat_import(), eq_import()];
        let err = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Nat.Basic
import Std.Logic.Eq
theorem Test.bad (n : Nat) : Eq.{1} Nat n n := Eq.refl n",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect_err("implicit Eq.refl should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::ImplicitArgumentRequired);
    }

    #[test]
    fn rejects_ill_typed_theorem_during_kernel_handoff() {
        let err = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
theorem Test.bad (A : Type) (x : A) : A := fun (y : A) => y",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect_err("kernel handoff should reject an ill-typed theorem proof");

        assert_eq!(err.kind, MachineDiagnosticKind::KernelRejected);
    }

    #[test]
    fn elaborates_lambda_pi_let_and_annotation() {
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
def Test.term.{u} (A : Sort u) : (forall (x : A), A) :=
  fun (x : A) => let y : A := x in (y : A)",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("lambda, Pi, let, and annotation should elaborate");
    }

    #[test]
    fn accepts_alpha_equivalent_annotation() {
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
def Test.alpha.{u} (A : Sort u) : (forall (z : A), A) :=
  ((fun (x : A) => x) : forall (y : A), A)",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("alpha-equivalent annotation should elaborate");
    }

    #[test]
    fn accepts_beta_equivalent_annotation() {
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
def Test.beta.{u} (A : Sort u) (x : A) : A :=
  (x : (fun (T : Sort u) => T) A)",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("beta-equivalent annotation should elaborate");
    }

    #[test]
    fn generalized_statement_typechecks() {
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
def Test.generalized.{u} (A : Sort u) (x : A) : (forall (y : A), A) :=
  fun (y : A) => x",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("generalized statement should typecheck before proof task creation");
    }

    #[test]
    fn rejects_large_numeric_universe_before_expansion() {
        let err = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "def Test.bad : Sort 1025 := Sort 0",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect_err("oversized numeric universe should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::UniverseLevelTooLarge);
    }

    #[test]
    fn elaborates_application_through_reducible_function_type_alias() {
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
def Test.IdTy.{u} (A : Sort u) : Sort imax u u := forall (x : A), A
def Test.id.{u} (A : Sort u) : Test.IdTy.{u} A := fun (x : A) => x
def Test.use.{u} (A : Sort u) (x : A) : A := Test.id.{u} A x",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect("reducible function type alias should expose the Pi");
    }

    #[test]
    fn elaborates_application_through_reducible_imported_function_type_alias() {
        let imports = [alias_import()];
        compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Alias
def Test.use.{u} (A : Sort u) (x : A) : A := Alias.id.{u} A x",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect("imported reducible definitions should remain reducible");
    }

    #[test]
    fn rejects_incorrect_annotation_before_erasing_it() {
        let imports = [nat_import()];
        let err = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
import Std.Nat.Basic
def Test.bad.{u} (A : Sort u) (x : A) : A := (x : Nat)",
            &imports,
            &MachineCompileOptions::default(),
        )
        .expect_err("incorrect annotation should be rejected");

        assert_eq!(err.kind, MachineDiagnosticKind::TypeMismatch);
    }

    #[test]
    fn rejects_kernel_invalid_declaration_before_exporting_signature() {
        let err = compile_machine_source_to_core(
            FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
def Test.bad (A : Type) (x : A) : A := x x
def Test.use (A : Type) (x : A) : A := Test.bad A x",
            &[],
            &MachineCompileOptions::default(),
        )
        .expect_err("ill-typed declaration should be rejected before it is exported");

        assert_eq!(err.kind, MachineDiagnosticKind::KernelRejected);
    }
}
