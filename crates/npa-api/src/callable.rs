use std::collections::BTreeMap;

use npa_cert::{ExportEntry, Name, TermNode};
use npa_frontend::{
    is_machine_surface_renderable_name, MachineSurfaceCallableInterfaceEntry,
    MachineSurfaceCallableInterfaceTable, MachineSurfaceCallableRef,
};
use npa_kernel::{Decl, Expr};

use crate::{
    CurrentDeclIndexEntry, CurrentGeneratedDeclEntry, CurrentGeneratedDeclKind,
    MachineCheckedCurrentDeclContext, MachineImportCertificateContext, VerifiedModuleContextEntry,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineSurfaceCallableInterfaceBuildError {
    ImportedCallable {
        name: Name,
        reason: &'static str,
    },
    CheckedCurrentCallable {
        name: Name,
        reason: &'static str,
    },
    DuplicateImportedCallable {
        callable_ref: MachineSurfaceCallableRef,
    },
    DuplicateCheckedCurrentCallable {
        callable_ref: MachineSurfaceCallableRef,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CallableOrigin {
    Imported,
    CheckedCurrent,
}

pub fn build_machine_surface_callable_interface_table(
    root_module: &Name,
    imports: &MachineImportCertificateContext,
    checked_current: &MachineCheckedCurrentDeclContext,
) -> Result<MachineSurfaceCallableInterfaceTable, MachineSurfaceCallableInterfaceBuildError> {
    build_machine_surface_callable_interface_table_from_parts(
        root_module,
        imports,
        checked_current.decl_index_table(),
        checked_current.generated_decl_table(),
    )
}

pub fn build_machine_surface_callable_interface_table_from_parts(
    root_module: &Name,
    imports: &MachineImportCertificateContext,
    current_decls: &[CurrentDeclIndexEntry],
    current_generated_decls: &[CurrentGeneratedDeclEntry],
) -> Result<MachineSurfaceCallableInterfaceTable, MachineSurfaceCallableInterfaceBuildError> {
    let mut builder = CallableTableBuilder::default();
    let current_decl_interfaces: BTreeMap<_, _> = current_decls
        .iter()
        .map(|current| {
            (
                current.source_index,
                CurrentDeclCallableInterface {
                    name: &current.signature.name,
                    decl_interface_hash: current.signature.decl_interface_hash,
                    core_decl: &current.core_decl,
                },
            )
        })
        .collect();
    for import in imports.direct_import_entries() {
        builder.add_direct_import(import)?;
    }
    for current in current_decls {
        builder.add_current_decl(root_module, current)?;
    }
    for generated in current_generated_decls {
        builder.add_current_generated(root_module, generated, &current_decl_interfaces)?;
    }
    builder.finish()
}

#[derive(Default)]
struct CallableTableBuilder {
    entries: Vec<MachineSurfaceCallableInterfaceEntry>,
    origins_by_ref: BTreeMap<Vec<u8>, CallableOrigin>,
}

#[derive(Clone, Copy)]
struct CurrentDeclCallableInterface<'a> {
    name: &'a Name,
    decl_interface_hash: npa_cert::Hash,
    core_decl: &'a Decl,
}

impl CallableTableBuilder {
    fn add_direct_import(
        &mut self,
        import: &VerifiedModuleContextEntry,
    ) -> Result<(), MachineSurfaceCallableInterfaceBuildError> {
        for export in &import.export_block {
            let name = export_name(import, export)?;
            ensure_renderable_import_name(&name)?;
            let term_binders = import_export_pi_telescope_len(import, export)?;
            let callable_ref = MachineSurfaceCallableRef::Imported {
                module: import.key.module.clone(),
                name,
                export_hash: import.key.export_hash,
                decl_interface_hash: export.decl_interface_hash,
            };
            self.push_entry(
                CallableOrigin::Imported,
                MachineSurfaceCallableInterfaceEntry::all_explicit(callable_ref, term_binders),
            )?;
        }
        Ok(())
    }

    fn add_current_decl(
        &mut self,
        root_module: &Name,
        current: &CurrentDeclIndexEntry,
    ) -> Result<(), MachineSurfaceCallableInterfaceBuildError> {
        if !has_strict_module_prefix(root_module, &current.signature.name) {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: current.signature.name.clone(),
                    reason: "current declaration name is outside the root module",
                },
            );
        }
        ensure_renderable_current_name(&current.signature.name)?;
        let callable_ref = MachineSurfaceCallableRef::CurrentModule {
            module: root_module.clone(),
            name: current.signature.name.clone(),
            source_index: current.source_index,
            decl_interface_hash: current.signature.decl_interface_hash,
        };
        self.push_entry(
            CallableOrigin::CheckedCurrent,
            MachineSurfaceCallableInterfaceEntry::all_explicit(
                callable_ref,
                expr_pi_telescope_len(&current.signature.ty),
            ),
        )
    }

    fn add_current_generated(
        &mut self,
        root_module: &Name,
        generated: &CurrentGeneratedDeclEntry,
        current_decl_interfaces: &BTreeMap<u64, CurrentDeclCallableInterface<'_>>,
    ) -> Result<(), MachineSurfaceCallableInterfaceBuildError> {
        if generated.module != *root_module {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration is outside the root module",
                },
            );
        }
        if !has_strict_module_prefix(root_module, &generated.generated_name) {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration name is outside the root module",
                },
            );
        }
        let Some(parent) = current_decl_interfaces.get(&generated.parent_source_index) else {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration parent source index is missing",
                },
            );
        };
        if parent.name != &generated.parent_name {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration parent name does not match checked current declaration",
                },
            );
        }
        if parent.decl_interface_hash != generated.parent_decl_interface_hash {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration parent hash does not match checked current declaration",
                },
            );
        }
        if parent.core_decl.name() != parent.name.as_dotted() {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration parent core declaration does not match checked current declaration",
                },
            );
        }
        if generated.parent_decl_interface_hash != generated.generated_decl_interface_hash {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration hash does not match its parent",
                },
            );
        }
        if !current_generated_decl_matches_parent(generated, parent.core_decl) {
            return Err(
                MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                    name: generated.generated_name.clone(),
                    reason: "current generated declaration is not generated by its checked parent",
                },
            );
        }
        ensure_renderable_current_name(&generated.generated_name)?;
        let callable_ref = MachineSurfaceCallableRef::CurrentGenerated {
            module: root_module.clone(),
            name: generated.generated_name.clone(),
            parent_source_index: generated.parent_source_index,
            decl_interface_hash: generated.generated_decl_interface_hash,
        };
        self.push_entry(
            CallableOrigin::CheckedCurrent,
            MachineSurfaceCallableInterfaceEntry::all_explicit(
                callable_ref,
                expr_pi_telescope_len(&generated.ty),
            ),
        )
    }

    fn push_entry(
        &mut self,
        origin: CallableOrigin,
        entry: MachineSurfaceCallableInterfaceEntry,
    ) -> Result<(), MachineSurfaceCallableInterfaceBuildError> {
        let ref_bytes = entry.callable_ref().canonical_bytes();
        if self.origins_by_ref.insert(ref_bytes, origin).is_some() {
            return match origin {
                CallableOrigin::Imported => Err(
                    MachineSurfaceCallableInterfaceBuildError::DuplicateImportedCallable {
                        callable_ref: entry.callable_ref().clone(),
                    },
                ),
                CallableOrigin::CheckedCurrent => Err(
                    MachineSurfaceCallableInterfaceBuildError::DuplicateCheckedCurrentCallable {
                        callable_ref: entry.callable_ref().clone(),
                    },
                ),
            };
        }
        self.entries.push(entry);
        Ok(())
    }

    fn finish(
        self,
    ) -> Result<MachineSurfaceCallableInterfaceTable, MachineSurfaceCallableInterfaceBuildError>
    {
        MachineSurfaceCallableInterfaceTable::from_entries(self.entries).map_err(|err| match err {
            npa_frontend::MachineSurfaceCallableInterfaceError::DuplicateCallableRef {
                callable_ref,
            } => MachineSurfaceCallableInterfaceBuildError::DuplicateCheckedCurrentCallable {
                callable_ref,
            },
        })
    }
}

fn current_generated_decl_matches_parent(
    generated: &CurrentGeneratedDeclEntry,
    parent: &Decl,
) -> bool {
    let generated_name = generated.generated_name.as_dotted();
    let Decl::Inductive { data, .. } = parent else {
        return false;
    };

    match generated.kind {
        CurrentGeneratedDeclKind::Constructor => data.constructors.iter().any(|constructor| {
            constructor.name == generated_name && constructor.ty == generated.ty
        }),
        CurrentGeneratedDeclKind::Recursor => data
            .recursor
            .as_ref()
            .is_some_and(|recursor| recursor.name == generated_name && recursor.ty == generated.ty),
    }
}

fn export_name(
    import: &VerifiedModuleContextEntry,
    export: &ExportEntry,
) -> Result<Name, MachineSurfaceCallableInterfaceBuildError> {
    import
        .decoded_name_table
        .get(export.name)
        .cloned()
        .ok_or_else(
            || MachineSurfaceCallableInterfaceBuildError::ImportedCallable {
                name: import.key.module.clone(),
                reason: "export name is missing from decoded name table",
            },
        )
}

fn import_export_pi_telescope_len(
    import: &VerifiedModuleContextEntry,
    export: &ExportEntry,
) -> Result<usize, MachineSurfaceCallableInterfaceBuildError> {
    let mut len = 0;
    let mut term = export.ty;
    let max_steps = import.verified_module.term_table().len().saturating_add(1);
    for _ in 0..max_steps {
        match import
            .verified_module
            .term_table()
            .get(term)
            .ok_or_else(
                || MachineSurfaceCallableInterfaceBuildError::ImportedCallable {
                    name: import.key.module.clone(),
                    reason: "export type term is missing from verified term table",
                },
            )? {
            TermNode::Pi { body, .. } => {
                len += 1;
                term = *body;
            }
            _ => return Ok(len),
        }
    }
    Err(
        MachineSurfaceCallableInterfaceBuildError::ImportedCallable {
            name: import.key.module.clone(),
            reason: "export type Pi telescope is cyclic",
        },
    )
}

fn expr_pi_telescope_len(expr: &Expr) -> usize {
    let mut len = 0;
    let mut current = expr;
    while let Expr::Pi { body, .. } = current {
        len += 1;
        current = body;
    }
    len
}

fn ensure_renderable_import_name(
    name: &Name,
) -> Result<(), MachineSurfaceCallableInterfaceBuildError> {
    if is_machine_surface_renderable_name(name) {
        Ok(())
    } else {
        Err(
            MachineSurfaceCallableInterfaceBuildError::ImportedCallable {
                name: name.clone(),
                reason: "export name is not Machine Surface renderable",
            },
        )
    }
}

fn ensure_renderable_current_name(
    name: &Name,
) -> Result<(), MachineSurfaceCallableInterfaceBuildError> {
    if is_machine_surface_renderable_name(name) {
        Ok(())
    } else {
        Err(
            MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable {
                name: name.clone(),
                reason: "current declaration name is not Machine Surface renderable",
            },
        )
    }
}

fn has_strict_module_prefix(module: &Name, name: &Name) -> bool {
    name.0.starts_with(&module.0) && name.0.len() > module.0.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        project_import_certificate_context, CurrentDeclDependencyReport,
        MachineCheckedDeclSignature, VerifiedImportKey, VerifiedModuleCertificateInput,
    };
    use npa_cert::{
        build_module_cert, encode_module_cert, AxiomPolicy, CoreModule, Hash, VerifiedModule,
    };
    use npa_kernel::{ConstructorDecl, Decl, InductiveDecl, Level, Reducibility};

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn id_type() -> Expr {
        Expr::pi("A", type0(), Expr::pi("x", Expr::bvar(0), Expr::bvar(1)))
    }

    fn id_value() -> Expr {
        Expr::lam("A", type0(), Expr::lam("x", Expr::bvar(0), Expr::bvar(0)))
    }

    fn id_module(module: &str, decl: &str) -> CoreModule {
        CoreModule {
            name: Name::from_dotted(module),
            declarations: vec![Decl::Def {
                name: decl.to_owned(),
                universe_params: Vec::new(),
                ty: id_type(),
                value: id_value(),
                reducibility: Reducibility::Reducible,
            }],
        }
    }

    fn unary() -> Expr {
        Expr::konst("Unary", Vec::new())
    }

    fn unary_module() -> CoreModule {
        let data = InductiveDecl::new(
            "Unary",
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Level::succ(Level::zero()),
            vec![
                ConstructorDecl::new("Unary.zero", unary()),
                ConstructorDecl::new("Unary.succ", Expr::pi("_", unary(), unary())),
            ],
            None,
        );
        CoreModule {
            name: Name::from_dotted("Test.Unary"),
            declarations: vec![Decl::Inductive {
                name: "Unary".to_owned(),
                universe_params: Vec::new(),
                ty: type0(),
                data: Box::new(data),
            }],
        }
    }

    fn cert_bytes(module: CoreModule, imports: &[VerifiedModule]) -> (Vec<u8>, VerifiedModule) {
        let cert = build_module_cert(module, imports).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut session = npa_cert::VerifierSession::new();
        for import in imports {
            session.register_verified_module(import.clone());
        }
        let verified =
            npa_cert::verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
        (bytes, verified)
    }

    fn input_from_verified<'a>(
        verified: &'a VerifiedModule,
        bytes: &'a [u8],
    ) -> VerifiedModuleCertificateInput<'a> {
        VerifiedModuleCertificateInput {
            module: verified.module(),
            expected_export_hash: verified.export_hash(),
            expected_certificate_hash: verified.certificate_hash(),
            certificate_bytes: bytes,
        }
    }

    fn key_from_verified(verified: &VerifiedModule) -> VerifiedImportKey {
        VerifiedImportKey::new(
            verified.module().clone(),
            verified.export_hash(),
            verified.certificate_hash(),
        )
    }

    fn import_context(bytes: &[u8], verified: &VerifiedModule) -> MachineImportCertificateContext {
        let key = key_from_verified(verified);
        project_import_certificate_context(
            &[input_from_verified(verified, bytes)],
            std::slice::from_ref(&key),
            &AxiomPolicy::high_trust(),
        )
        .unwrap()
    }

    fn dummy_current_entry(
        source_index: u64,
        name: &str,
        decl_interface_hash: Hash,
        ty: Expr,
    ) -> CurrentDeclIndexEntry {
        CurrentDeclIndexEntry {
            source_index,
            package_bytes: Vec::new(),
            signature: MachineCheckedDeclSignature {
                name: Name::from_dotted(name),
                universe_params: Vec::new(),
                ty: ty.clone(),
                decl_interface_hash,
            },
            core_decl: Decl::Def {
                name: name.to_owned(),
                universe_params: Vec::new(),
                ty,
                value: prop(),
                reducibility: Reducibility::Reducible,
            },
            core_decl_hash: [0x11; 32],
            dependency_report: CurrentDeclDependencyReport {
                direct_dependency_entries: Vec::new(),
                axiom_dependencies: Vec::new(),
            },
        }
    }

    fn dummy_inductive_current_entry(
        source_index: u64,
        name: &str,
        decl_interface_hash: Hash,
    ) -> CurrentDeclIndexEntry {
        let ty = type0();
        let inductive = Expr::konst(name, Vec::new());
        CurrentDeclIndexEntry {
            source_index,
            package_bytes: Vec::new(),
            signature: MachineCheckedDeclSignature {
                name: Name::from_dotted(name),
                universe_params: Vec::new(),
                ty: ty.clone(),
                decl_interface_hash,
            },
            core_decl: Decl::Inductive {
                name: name.to_owned(),
                universe_params: Vec::new(),
                ty,
                data: Box::new(InductiveDecl::new(
                    name,
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    Level::succ(Level::zero()),
                    vec![ConstructorDecl::new(format!("{name}.zero"), inductive)],
                    None,
                )),
            },
            core_decl_hash: [0x12; 32],
            dependency_report: CurrentDeclDependencyReport {
                direct_dependency_entries: Vec::new(),
                axiom_dependencies: Vec::new(),
            },
        }
    }

    fn dummy_generated_entry(
        root: &Name,
        parent_source_index: u64,
        parent_name: &str,
        parent_decl_interface_hash: Hash,
        generated_name: &str,
    ) -> CurrentGeneratedDeclEntry {
        CurrentGeneratedDeclEntry {
            module: root.clone(),
            parent_source_index,
            parent_name: Name::from_dotted(parent_name),
            parent_decl_interface_hash,
            generated_name: Name::from_dotted(generated_name),
            generated_decl_interface_hash: parent_decl_interface_hash,
            kind: crate::CurrentGeneratedDeclKind::Recursor,
            ty: Expr::pi("p", prop(), prop()),
        }
    }

    #[test]
    fn builds_all_explicit_profiles_for_direct_import_exports() {
        let (bytes, verified) = cert_bytes(id_module("Test.Id", "id"), &[]);
        let imports = import_context(&bytes, &verified);

        let table = build_machine_surface_callable_interface_table_from_parts(
            &Name::from_dotted("Root"),
            &imports,
            &[],
            &[],
        )
        .unwrap();

        assert_eq!(table.entries().len(), 1);
        let entry = &table.entries()[0];
        assert_eq!(
            entry.callable_ref(),
            &MachineSurfaceCallableRef::Imported {
                module: Name::from_dotted("Test.Id"),
                name: Name::from_dotted("id"),
                export_hash: verified.export_hash(),
                decl_interface_hash: verified.declarations()[0].hashes.decl_interface_hash,
            }
        );
        assert_eq!(entry.implicit_profile().len(), 2);
        assert_ne!(table.table_hash(), [0; 32]);
        assert_eq!(table.table_hash(), table.table_hash());
    }

    #[test]
    fn direct_import_generated_exports_use_imported_callable_refs() {
        let (bytes, verified) = cert_bytes(unary_module(), &[]);
        let imports = import_context(&bytes, &verified);

        let table = build_machine_surface_callable_interface_table_from_parts(
            &Name::from_dotted("Root"),
            &imports,
            &[],
            &[],
        )
        .unwrap();

        let unary_succ = table
            .entries()
            .iter()
            .find(|entry| {
                matches!(
                    entry.callable_ref(),
                    MachineSurfaceCallableRef::Imported { name, .. }
                        if name == &Name::from_dotted("Unary.succ")
                )
            })
            .expect("public constructor should be callable");
        assert_eq!(unary_succ.implicit_profile().len(), 1);
        assert!(matches!(
            unary_succ.callable_ref(),
            MachineSurfaceCallableRef::Imported { .. }
        ));
    }

    #[test]
    fn builds_current_and_current_generated_entries() {
        let imports = MachineImportCertificateContext::empty();
        let root = Name::from_dotted("Root");
        let parent_hash = [0x22; 32];
        let current = dummy_inductive_current_entry(0, "Root.Unary", parent_hash);
        let generated = CurrentGeneratedDeclEntry {
            module: root.clone(),
            parent_source_index: 0,
            parent_name: Name::from_dotted("Root.Unary"),
            parent_decl_interface_hash: parent_hash,
            generated_name: Name::from_dotted("Root.Unary.zero"),
            generated_decl_interface_hash: parent_hash,
            kind: crate::CurrentGeneratedDeclKind::Constructor,
            ty: Expr::konst("Root.Unary", Vec::new()),
        };

        let table = build_machine_surface_callable_interface_table_from_parts(
            &root,
            &imports,
            &[current],
            &[generated],
        )
        .unwrap();

        assert_eq!(table.entries().len(), 2);
        assert!(table.entries().iter().any(|entry| matches!(
            entry.callable_ref(),
            MachineSurfaceCallableRef::CurrentModule { name, .. }
                if name == &Name::from_dotted("Root.Unary")
        )));
        assert!(table.entries().iter().any(|entry| matches!(
            entry.callable_ref(),
            MachineSurfaceCallableRef::CurrentGenerated { name, .. }
                if name == &Name::from_dotted("Root.Unary.zero")
        )));
    }

    #[test]
    fn rejects_duplicate_current_callable_refs() {
        let imports = MachineImportCertificateContext::empty();
        let root = Name::from_dotted("Root");
        let hash = [0x33; 32];
        let left = dummy_current_entry(0, "Root.id", hash, prop());
        let right = dummy_current_entry(0, "Root.id", hash, prop());

        let err = build_machine_surface_callable_interface_table_from_parts(
            &root,
            &imports,
            &[left, right],
            &[],
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineSurfaceCallableInterfaceBuildError::DuplicateCheckedCurrentCallable { .. }
        ));
    }

    #[test]
    fn rejects_current_generated_without_parent() {
        let imports = MachineImportCertificateContext::empty();
        let root = Name::from_dotted("Root");
        let generated = dummy_generated_entry(&root, 7, "Root.id", [0x44; 32], "Root.id.rec");

        let err = build_machine_surface_callable_interface_table_from_parts(
            &root,
            &imports,
            &[],
            &[generated],
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable { .. }
        ));
    }

    #[test]
    fn rejects_current_generated_parent_mismatch() {
        let imports = MachineImportCertificateContext::empty();
        let root = Name::from_dotted("Root");
        let parent_hash = [0x55; 32];
        let current = dummy_current_entry(0, "Root.actual", parent_hash, prop());
        let generated =
            dummy_generated_entry(&root, 0, "Root.claimed", parent_hash, "Root.actual.rec");

        let err = build_machine_surface_callable_interface_table_from_parts(
            &root,
            &imports,
            &[current],
            &[generated],
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable { .. }
        ));
    }

    #[test]
    fn rejects_current_generated_not_emitted_by_parent() {
        let imports = MachineImportCertificateContext::empty();
        let root = Name::from_dotted("Root");
        let parent_hash = [0x66; 32];
        let current = dummy_current_entry(0, "Root.id", parent_hash, prop());
        let generated = dummy_generated_entry(&root, 0, "Root.id", parent_hash, "Root.id.rec");

        let err = build_machine_surface_callable_interface_table_from_parts(
            &root,
            &imports,
            &[current],
            &[generated],
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable { .. }
        ));
    }

    #[test]
    fn rejects_current_callable_name_that_machine_surface_cannot_parse() {
        let imports = MachineImportCertificateContext::empty();
        let root = Name::from_dotted("Root");
        let current = dummy_current_entry(0, "Root._hidden", [0x77; 32], prop());

        let err = build_machine_surface_callable_interface_table_from_parts(
            &root,
            &imports,
            &[current],
            &[],
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable { .. }
        ));
    }
}
