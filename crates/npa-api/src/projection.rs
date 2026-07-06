use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

use npa_cert::{
    decode_module_cert, verify_module_cert, AxiomPolicy, AxiomRef, AxiomReport, CertError,
    CertReducibility, ConstructorSpec, DeclHashes, DeclPayload, DependencyEntry, ExportEntry,
    ExportKind, GlobalRef, Hash, ModuleCert, Name, NameId, Opacity, RecursorSpec, TrustMode,
    VerifiedModule, VerifierSession,
};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedImportKey {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
}

impl VerifiedImportKey {
    pub fn new(module: Name, export_hash: Hash, certificate_hash: Hash) -> Self {
        Self {
            module,
            export_hash,
            certificate_hash,
        }
    }

    fn from_verified_module(module: &VerifiedModule) -> Self {
        Self {
            module: module.module().clone(),
            export_hash: module.export_hash(),
            certificate_hash: module.certificate_hash(),
        }
    }
}

impl PartialOrd for VerifiedImportKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VerifiedImportKey {
    fn cmp(&self, other: &Self) -> Ordering {
        verified_import_key_canonical_bytes(self).cmp(&verified_import_key_canonical_bytes(other))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedModuleCertificateInput<'bytes> {
    pub module: &'bytes Name,
    pub expected_export_hash: Hash,
    pub expected_certificate_hash: Hash,
    pub certificate_bytes: &'bytes [u8],
}

impl<'bytes> VerifiedModuleCertificateInput<'bytes> {
    fn key(&self) -> VerifiedImportKey {
        VerifiedImportKey::new(
            self.module.clone(),
            self.expected_export_hash,
            self.expected_certificate_hash,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineImportCertificateContext {
    verified_modules: Vec<VerifiedModuleContextEntry>,
    direct_import_keys: Vec<VerifiedImportKey>,
}

impl MachineImportCertificateContext {
    pub fn empty() -> Self {
        Self {
            verified_modules: Vec::new(),
            direct_import_keys: Vec::new(),
        }
    }

    pub fn verified_modules(&self) -> &[VerifiedModuleContextEntry] {
        &self.verified_modules
    }

    pub fn direct_import_keys(&self) -> &[VerifiedImportKey] {
        &self.direct_import_keys
    }

    pub fn direct_import_entries(&self) -> Vec<&VerifiedModuleContextEntry> {
        self.direct_import_keys
            .iter()
            .map(|key| {
                self.verified_modules
                    .iter()
                    .find(|entry| &entry.key == key)
                    .expect("direct import keys are validated when the context is built")
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedModuleContextEntry {
    pub key: VerifiedImportKey,
    pub certificate_bytes: Vec<u8>,
    pub certificate_import_table: Vec<VerifiedImportKey>,
    pub decoded_name_table: Vec<Name>,
    pub decl_index_table: Vec<VerifiedImportDeclIndexEntry>,
    pub generated_decl_table: Vec<VerifiedImportGeneratedDeclEntry>,
    pub export_block: Vec<ExportEntry>,
    pub axiom_report: npa_cert::AxiomReport,
    pub decoded_name_table_hash: Hash,
    pub decl_index_table_hash: Hash,
    pub generated_decl_table_hash: Hash,
    pub export_signature_summary_hash: Hash,
    pub certified_env_decl_hashes_summary_hash: Hash,
    pub axiom_report_hash: Hash,
    pub verified_module: VerifiedModule,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedImportDeclIndexEntry {
    pub decl_index: usize,
    pub name: Name,
    pub decl: DeclPayload,
    pub dependencies: Vec<DependencyEntry>,
    pub axiom_dependencies: Vec<AxiomRef>,
    pub hashes: DeclHashes,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedImportGeneratedDeclEntry {
    pub parent_decl_index: usize,
    pub name: Name,
    pub kind: GeneratedDeclKind,
    pub payload: VerifiedImportGeneratedDeclPayload,
    pub export: ExportEntry,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedDeclKind {
    Constructor,
    Recursor,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifiedImportGeneratedDeclPayload {
    Constructor(ConstructorSpec),
    Recursor(RecursorSpec),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportProjectionError {
    NonHighTrustPolicy,
    DecodeFailed {
        key: Box<VerifiedImportKey>,
        source: Box<CertError>,
    },
    VerifyFailed {
        key: Box<VerifiedImportKey>,
        source: Box<CertError>,
    },
    DuplicateClosureKey {
        key: Box<VerifiedImportKey>,
    },
    ConflictingModuleKey {
        module: Name,
    },
    MissingDirectImport {
        key: Box<VerifiedImportKey>,
    },
    MissingClosureDependency {
        owner: Box<VerifiedImportKey>,
        missing: Box<VerifiedImportKey>,
    },
    UnreachableClosureEntry {
        key: Box<VerifiedImportKey>,
    },
    MissingImportCertificateHash {
        owner: Box<VerifiedImportKey>,
        imported_module: Name,
    },
    ImportCycle {
        key: Box<VerifiedImportKey>,
    },
    CertificateIdentityMismatch {
        expected: Box<VerifiedImportKey>,
        actual: Box<VerifiedImportKey>,
    },
    ModuleNameMismatch {
        expected: Name,
        actual: Name,
    },
    MissingName {
        key: Box<VerifiedImportKey>,
        name_id: NameId,
    },
    MissingGeneratedExport {
        key: Box<VerifiedImportKey>,
        parent_decl_index: usize,
        generated_name: Name,
    },
    InvalidUniverseParamName {
        key: Box<VerifiedImportKey>,
        export_name: Name,
        name: Name,
    },
}

pub fn project_import_certificate_context(
    import_closure: &[VerifiedModuleCertificateInput<'_>],
    direct_import_keys: &[VerifiedImportKey],
    policy: &AxiomPolicy,
) -> Result<MachineImportCertificateContext, ImportProjectionError> {
    if policy.mode != TrustMode::HighTrust {
        return Err(ImportProjectionError::NonHighTrustPolicy);
    }

    let records = decode_closure(import_closure)?;
    let direct_import_keys = canonical_direct_import_keys(direct_import_keys, &records)?;
    let verification_order = reachable_verification_order(&direct_import_keys, &records)?;
    reject_unreachable_closure_entries(&records, &verification_order)?;

    let mut session = VerifierSession::new();
    let mut verified_by_key = BTreeMap::new();
    for key in &verification_order {
        let record = records
            .get(key)
            .expect("verification order only contains decoded closure entries");
        let verified =
            verify_module_cert(record.certificate_bytes.as_slice(), &mut session, policy).map_err(
                |source| ImportProjectionError::VerifyFailed {
                    key: Box::new(key.clone()),
                    source: Box::new(source),
                },
            )?;
        let actual = VerifiedImportKey::from_verified_module(&verified);
        if &actual != key {
            return Err(ImportProjectionError::CertificateIdentityMismatch {
                expected: Box::new(key.clone()),
                actual: Box::new(actual),
            });
        }
        verified_by_key.insert(key.clone(), verified);
    }

    let mut verified_modules = Vec::new();
    for key in records.keys() {
        let record = records
            .get(key)
            .expect("record key came from the decoded closure map");
        let verified_module = verified_by_key
            .remove(key)
            .expect("reachable closure entries are all verified");
        verified_modules.push(project_verified_module(record, verified_module)?);
    }

    Ok(MachineImportCertificateContext {
        verified_modules,
        direct_import_keys,
    })
}

#[derive(Clone, Debug)]
struct DecodedCertificateRecord {
    key: VerifiedImportKey,
    certificate_bytes: Vec<u8>,
    imports: Vec<VerifiedImportKey>,
}

fn decode_closure(
    import_closure: &[VerifiedModuleCertificateInput<'_>],
) -> Result<BTreeMap<VerifiedImportKey, DecodedCertificateRecord>, ImportProjectionError> {
    let mut records = BTreeMap::new();
    let mut module_keys = BTreeMap::new();

    for input in import_closure {
        let key = input.key();
        match module_keys.insert(key.module.clone(), key.clone()) {
            Some(previous) if previous != key => {
                return Err(ImportProjectionError::ConflictingModuleKey {
                    module: key.module.clone(),
                });
            }
            _ => {}
        }
        if records.contains_key(&key) {
            return Err(ImportProjectionError::DuplicateClosureKey { key: Box::new(key) });
        }

        let cert = decode_module_cert(input.certificate_bytes).map_err(|source| {
            ImportProjectionError::DecodeFailed {
                key: Box::new(key.clone()),
                source: Box::new(source),
            }
        })?;
        if cert.header.module != key.module {
            return Err(ImportProjectionError::ModuleNameMismatch {
                expected: key.module.clone(),
                actual: cert.header.module.clone(),
            });
        }
        let imports = certificate_import_keys(&key, &cert)?;

        records.insert(
            key.clone(),
            DecodedCertificateRecord {
                key,
                certificate_bytes: input.certificate_bytes.to_vec(),
                imports,
            },
        );
    }

    for record in records.values() {
        for imported in &record.imports {
            if !records.contains_key(imported) {
                return Err(ImportProjectionError::MissingClosureDependency {
                    owner: Box::new(record.key.clone()),
                    missing: Box::new(imported.clone()),
                });
            }
        }
    }

    Ok(records)
}

fn certificate_import_keys(
    owner: &VerifiedImportKey,
    cert: &ModuleCert,
) -> Result<Vec<VerifiedImportKey>, ImportProjectionError> {
    cert.imports
        .iter()
        .map(|entry| {
            let certificate_hash = entry.certificate_hash.ok_or_else(|| {
                ImportProjectionError::MissingImportCertificateHash {
                    owner: Box::new(owner.clone()),
                    imported_module: entry.module.clone(),
                }
            })?;
            Ok(VerifiedImportKey::new(
                entry.module.clone(),
                entry.export_hash,
                certificate_hash,
            ))
        })
        .collect()
}

fn canonical_direct_import_keys(
    direct_import_keys: &[VerifiedImportKey],
    records: &BTreeMap<VerifiedImportKey, DecodedCertificateRecord>,
) -> Result<Vec<VerifiedImportKey>, ImportProjectionError> {
    let mut direct = BTreeSet::new();
    let mut module_keys = BTreeMap::new();
    for key in direct_import_keys {
        match module_keys.insert(key.module.clone(), key.clone()) {
            Some(previous) if previous != *key => {
                return Err(ImportProjectionError::ConflictingModuleKey {
                    module: key.module.clone(),
                });
            }
            _ => {}
        }
        if !records.contains_key(key) {
            return Err(ImportProjectionError::MissingDirectImport {
                key: Box::new(key.clone()),
            });
        }
        direct.insert(key.clone());
    }
    Ok(direct.into_iter().collect())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VisitState {
    Visiting,
    Done,
}

fn reachable_verification_order(
    direct_import_keys: &[VerifiedImportKey],
    records: &BTreeMap<VerifiedImportKey, DecodedCertificateRecord>,
) -> Result<Vec<VerifiedImportKey>, ImportProjectionError> {
    let mut states = BTreeMap::new();
    let mut order = Vec::new();
    for key in direct_import_keys {
        visit_closure_key(key, records, &mut states, &mut order)?;
    }
    Ok(order)
}

fn visit_closure_key(
    key: &VerifiedImportKey,
    records: &BTreeMap<VerifiedImportKey, DecodedCertificateRecord>,
    states: &mut BTreeMap<VerifiedImportKey, VisitState>,
    order: &mut Vec<VerifiedImportKey>,
) -> Result<(), ImportProjectionError> {
    match states.get(key) {
        Some(VisitState::Done) => return Ok(()),
        Some(VisitState::Visiting) => {
            return Err(ImportProjectionError::ImportCycle {
                key: Box::new(key.clone()),
            });
        }
        None => {}
    }

    let record = records
        .get(key)
        .ok_or_else(|| ImportProjectionError::MissingDirectImport {
            key: Box::new(key.clone()),
        })?;
    states.insert(key.clone(), VisitState::Visiting);
    for imported in &record.imports {
        visit_closure_key(imported, records, states, order)?;
    }
    states.insert(key.clone(), VisitState::Done);
    order.push(key.clone());
    Ok(())
}

fn reject_unreachable_closure_entries(
    records: &BTreeMap<VerifiedImportKey, DecodedCertificateRecord>,
    verification_order: &[VerifiedImportKey],
) -> Result<(), ImportProjectionError> {
    let reachable: BTreeSet<_> = verification_order.iter().cloned().collect();
    for key in records.keys() {
        if !reachable.contains(key) {
            return Err(ImportProjectionError::UnreachableClosureEntry {
                key: Box::new(key.clone()),
            });
        }
    }
    Ok(())
}

fn project_verified_module(
    record: &DecodedCertificateRecord,
    verified_module: VerifiedModule,
) -> Result<VerifiedModuleContextEntry, ImportProjectionError> {
    let key = record.key.clone();
    let decl_index_table = project_decl_index_table(&key, &verified_module)?;
    let generated_decl_table = project_generated_decl_table(&key, &verified_module)?;
    let decoded_name_table_hash = decoded_name_table_hash(&key, &verified_module);
    let decl_index_table_hash = decl_index_table_hash(&key, &decl_index_table, &verified_module);
    let generated_decl_table_hash =
        generated_decl_table_hash(&key, &decl_index_table, &generated_decl_table);
    let export_signature_summary_hash = export_signature_summary_hash(&key, &verified_module)?;
    let certified_env_decl_hashes_summary_hash =
        certified_env_decl_hashes_summary_hash(&key, &verified_module);
    let axiom_report_hash = axiom_report_hash(verified_module.axiom_report());

    Ok(VerifiedModuleContextEntry {
        key,
        certificate_bytes: record.certificate_bytes.clone(),
        certificate_import_table: record.imports.clone(),
        decoded_name_table: verified_module.name_table().to_vec(),
        decl_index_table,
        generated_decl_table,
        export_block: verified_module.export_block().to_vec(),
        axiom_report: verified_module.axiom_report().clone(),
        decoded_name_table_hash,
        decl_index_table_hash,
        generated_decl_table_hash,
        export_signature_summary_hash,
        certified_env_decl_hashes_summary_hash,
        axiom_report_hash,
        verified_module,
    })
}

fn project_decl_index_table(
    key: &VerifiedImportKey,
    module: &VerifiedModule,
) -> Result<Vec<VerifiedImportDeclIndexEntry>, ImportProjectionError> {
    module
        .declarations()
        .iter()
        .enumerate()
        .map(|(decl_index, decl)| {
            Ok(VerifiedImportDeclIndexEntry {
                decl_index,
                name: name_by_id(key, module, decl_name_id(&decl.decl)?)?,
                decl: decl.decl.clone(),
                dependencies: decl.dependencies.clone(),
                axiom_dependencies: decl.axiom_dependencies.clone(),
                hashes: decl.hashes.clone(),
            })
        })
        .collect()
}

fn project_generated_decl_table(
    key: &VerifiedImportKey,
    module: &VerifiedModule,
) -> Result<Vec<VerifiedImportGeneratedDeclEntry>, ImportProjectionError> {
    let mut entries = Vec::new();
    for (parent_decl_index, decl) in module.declarations().iter().enumerate() {
        let DeclPayload::Inductive {
            constructors,
            recursor,
            ..
        } = &decl.decl
        else {
            continue;
        };

        for constructor in constructors {
            let name = name_by_id(key, module, constructor.name)?;
            entries.push(VerifiedImportGeneratedDeclEntry {
                parent_decl_index,
                name: name.clone(),
                kind: GeneratedDeclKind::Constructor,
                payload: VerifiedImportGeneratedDeclPayload::Constructor(constructor.clone()),
                export: generated_export(
                    key,
                    module,
                    parent_decl_index,
                    &name,
                    ExportKind::Constructor,
                    &decl.hashes.decl_interface_hash,
                )?,
            });
        }

        if let Some(recursor) = recursor {
            let name = name_by_id(key, module, recursor.name)?;
            entries.push(VerifiedImportGeneratedDeclEntry {
                parent_decl_index,
                name: name.clone(),
                kind: GeneratedDeclKind::Recursor,
                payload: VerifiedImportGeneratedDeclPayload::Recursor(recursor.clone()),
                export: generated_export(
                    key,
                    module,
                    parent_decl_index,
                    &name,
                    ExportKind::Recursor,
                    &decl.hashes.decl_interface_hash,
                )?,
            });
        }
    }
    Ok(entries)
}

fn generated_export(
    key: &VerifiedImportKey,
    module: &VerifiedModule,
    parent_decl_index: usize,
    generated_name: &Name,
    kind: ExportKind,
    decl_interface_hash: &Hash,
) -> Result<ExportEntry, ImportProjectionError> {
    let name_id = module
        .name_table()
        .iter()
        .position(|name| name == generated_name)
        .ok_or_else(|| ImportProjectionError::MissingGeneratedExport {
            key: Box::new(key.clone()),
            parent_decl_index,
            generated_name: generated_name.clone(),
        })?;

    module
        .export_block()
        .iter()
        .find(|entry| {
            entry.name == name_id
                && entry.kind == kind
                && &entry.decl_interface_hash == decl_interface_hash
        })
        .cloned()
        .ok_or_else(|| ImportProjectionError::MissingGeneratedExport {
            key: Box::new(key.clone()),
            parent_decl_index,
            generated_name: generated_name.clone(),
        })
}

fn decl_name_id(decl: &DeclPayload) -> Result<NameId, ImportProjectionError> {
    Ok(match decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    })
}

fn name_by_id(
    key: &VerifiedImportKey,
    module: &VerifiedModule,
    name_id: NameId,
) -> Result<Name, ImportProjectionError> {
    module
        .name_table()
        .get(name_id)
        .cloned()
        .ok_or_else(|| ImportProjectionError::MissingName {
            key: Box::new(key.clone()),
            name_id,
        })
}

fn export_signature_summary_hash(
    key: &VerifiedImportKey,
    module: &VerifiedModule,
) -> Result<Hash, ImportProjectionError> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.export-signature-summary.v1");
    encode_name(&mut out, &key.module);
    out.extend(key.export_hash);
    out.extend(key.certificate_hash);
    encode_uvar(&mut out, module.export_block().len() as u64);
    for export in module.export_block() {
        let export_name = name_by_id(key, module, export.name)?;
        encode_name(&mut out, &export_name);
        out.push(export_kind_tag(export.kind));
        encode_uvar(&mut out, export.universe_params.len() as u64);
        for param in &export.universe_params {
            let param_name = name_by_id(key, module, *param)?;
            let [component] = param_name.0.as_slice() else {
                return Err(ImportProjectionError::InvalidUniverseParamName {
                    key: Box::new(key.clone()),
                    export_name: export_name.clone(),
                    name: param_name,
                });
            };
            encode_string(&mut out, component);
        }
        out.extend(export.type_hash);
        encode_option_hash(&mut out, export.body_hash.as_ref());
        encode_option_reducibility(&mut out, export.reducibility);
        encode_option_opacity(&mut out, export.opacity);
        out.extend(export.decl_interface_hash);
        out.extend(hash_axiom_refs(&export.axiom_dependencies));
    }
    Ok(hash_bytes(&out))
}

fn decoded_name_table_hash(key: &VerifiedImportKey, module: &VerifiedModule) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.decoded-name-table.v1");
    encode_verified_import_key(&mut out, key);
    encode_uvar(&mut out, module.name_table().len() as u64);
    for name in module.name_table() {
        encode_name(&mut out, name);
    }
    hash_bytes(&out)
}

fn decl_index_table_hash(
    key: &VerifiedImportKey,
    decls: &[VerifiedImportDeclIndexEntry],
    module: &VerifiedModule,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.import-decl-index-table.v1");
    encode_verified_import_key(&mut out, key);
    encode_uvar(&mut out, decls.len() as u64);
    for decl in decls {
        encode_uvar(&mut out, decl.decl_index as u64);
        encode_name(&mut out, &decl.name);
        out.extend(decl.hashes.decl_interface_hash);
        out.push(if decl_public_export(decl, module) {
            0x01
        } else {
            0x00
        });
    }
    hash_bytes(&out)
}

fn decl_public_export(decl: &VerifiedImportDeclIndexEntry, module: &VerifiedModule) -> bool {
    module.export_block().iter().any(|export| {
        export.decl_interface_hash == decl.hashes.decl_interface_hash
            && export_kind_matches_decl_payload(export.kind, &decl.decl)
            && module
                .name_table()
                .get(export.name)
                .map(|name| name == &decl.name)
                .unwrap_or(false)
    })
}

fn export_kind_matches_decl_payload(kind: ExportKind, decl: &DeclPayload) -> bool {
    matches!(
        (kind, decl),
        (ExportKind::Axiom, DeclPayload::Axiom { .. })
            | (ExportKind::Def, DeclPayload::Def { .. })
            | (ExportKind::Theorem, DeclPayload::Theorem { .. })
            | (ExportKind::Inductive, DeclPayload::Inductive { .. })
    )
}

fn generated_decl_table_hash(
    key: &VerifiedImportKey,
    decls: &[VerifiedImportDeclIndexEntry],
    generated: &[VerifiedImportGeneratedDeclEntry],
) -> Hash {
    let mut entries = generated.iter().collect::<Vec<_>>();
    entries.sort_by(|left, right| {
        left.parent_decl_index
            .cmp(&right.parent_decl_index)
            .then_with(|| name_canonical_bytes(&left.name).cmp(&name_canonical_bytes(&right.name)))
            .then_with(|| generated_kind_tag(left.kind).cmp(&generated_kind_tag(right.kind)))
    });

    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.import-generated-decl-table.v1");
    encode_verified_import_key(&mut out, key);
    encode_uvar(&mut out, entries.len() as u64);
    for entry in entries {
        let parent = decls
            .iter()
            .find(|decl| decl.decl_index == entry.parent_decl_index)
            .expect("generated import entries are projected from an existing parent declaration");
        encode_uvar(&mut out, entry.parent_decl_index as u64);
        encode_name(&mut out, &parent.name);
        encode_name(&mut out, &entry.name);
        out.extend(parent.hashes.decl_interface_hash);
        out.extend(entry.export.decl_interface_hash);
        out.push(0x01);
    }
    hash_bytes(&out)
}

fn generated_kind_tag(kind: GeneratedDeclKind) -> u8 {
    match kind {
        GeneratedDeclKind::Constructor => 0x00,
        GeneratedDeclKind::Recursor => 0x01,
    }
}

fn certified_env_decl_hashes_summary_hash(
    key: &VerifiedImportKey,
    module: &VerifiedModule,
) -> Hash {
    let mut out = Vec::new();
    encode_string(
        &mut out,
        "npa.machine-api.certified-env-decl-hashes-summary.v1",
    );
    encode_name(&mut out, &key.module);
    out.extend(key.export_hash);
    out.extend(key.certificate_hash);
    encode_uvar(&mut out, module.declarations().len() as u64);
    for (decl_index, decl) in module.declarations().iter().enumerate() {
        encode_uvar(&mut out, decl_index as u64);
        out.extend(decl.hashes.decl_interface_hash);
        out.extend(decl.hashes.decl_certificate_hash);
    }
    hash_bytes(&out)
}

fn axiom_report_hash(report: &AxiomReport) -> Hash {
    let mut out = Vec::new();
    encode_uvar(&mut out, report.per_declaration.len() as u64);
    for entry in &report.per_declaration {
        encode_uvar(&mut out, entry.decl_index as u64);
        encode_axiom_refs(&mut out, &entry.direct_axioms);
        encode_axiom_refs(&mut out, &entry.transitive_axioms);
    }
    encode_axiom_refs(&mut out, &report.module_axioms);
    hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &out)
}

fn encode_verified_import_key(out: &mut Vec<u8>, key: &VerifiedImportKey) {
    encode_name(out, &key.module);
    out.extend(key.export_hash);
    out.extend(key.certificate_hash);
}

fn verified_import_key_canonical_bytes(key: &VerifiedImportKey) -> Vec<u8> {
    let mut out = Vec::new();
    encode_verified_import_key(&mut out, key);
    out
}

fn name_canonical_bytes(name: &Name) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, name);
    out
}

fn encode_axiom_refs(out: &mut Vec<u8>, axioms: &[AxiomRef]) {
    encode_uvar(out, axioms.len() as u64);
    for axiom in axioms {
        encode_global_ref(out, &axiom.global_ref);
        encode_uvar(out, axiom.name as u64);
        out.extend(axiom.decl_interface_hash);
    }
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn hash_axiom_refs(axioms: &[AxiomRef]) -> Hash {
    let mut ordered = axioms.to_vec();
    ordered.sort();
    let mut out = Vec::new();
    encode_uvar(&mut out, ordered.len() as u64);
    for axiom in &ordered {
        encode_global_ref(&mut out, &axiom.global_ref);
        encode_uvar(&mut out, axiom.name as u64);
        out.extend(axiom.decl_interface_hash);
    }
    hash_bytes(&out)
}

fn encode_global_ref(out: &mut Vec<u8>, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar(out, *import_index as u64);
            encode_uvar(out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_uvar(out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_uvar(out, *decl_index as u64);
            encode_uvar(out, *name as u64);
        }
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_uvar(out, *name as u64);
            out.extend(decl_interface_hash);
        }
    }
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

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            out.extend(hash);
        }
        None => out.push(0x00),
    }
}

fn encode_option_reducibility(out: &mut Vec<u8>, value: Option<CertReducibility>) {
    match value {
        Some(reducibility) => {
            out.push(0x01);
            out.push(match reducibility {
                CertReducibility::Reducible => 0x00,
                CertReducibility::Opaque => 0x01,
            });
        }
        None => out.push(0x00),
    }
}

fn encode_option_opacity(out: &mut Vec<u8>, value: Option<Opacity>) {
    match value {
        Some(Opacity::Opaque) => {
            out.push(0x01);
            out.push(0x00);
        }
        None => out.push(0x00),
    }
}

fn export_kind_tag(kind: ExportKind) -> u8 {
    match kind {
        ExportKind::Axiom => 0x00,
        ExportKind::Def => 0x01,
        ExportKind::Theorem => 0x02,
        ExportKind::Inductive => 0x03,
        ExportKind::Constructor => 0x04,
        ExportKind::Recursor => 0x05,
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

fn hash_bytes(bytes: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_cert::{build_module_cert, encode_module_cert, CoreModule};
    use npa_kernel::{ConstructorDecl, Decl, Expr, InductiveDecl, Level, Reducibility};

    fn id_type(a: &str, x: &str) -> Expr {
        Expr::pi(
            a,
            Expr::sort(Level::param("u")),
            Expr::pi(x, Expr::bvar(0), Expr::bvar(1)),
        )
    }

    fn id_value(a: &str, x: &str) -> Expr {
        Expr::lam(
            a,
            Expr::sort(Level::param("u")),
            Expr::lam(x, Expr::bvar(0), Expr::bvar(0)),
        )
    }

    fn id_module(module: &str, decl: &str) -> CoreModule {
        CoreModule {
            name: Name::from_dotted(module),
            declarations: vec![Decl::Def {
                name: decl.to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: id_value("A", "x"),
                reducibility: Reducibility::Reducible,
            }],
        }
    }

    fn use_id_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Test.UseId"),
            declarations: vec![Decl::Def {
                name: "use_id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: Expr::konst("id", vec![Level::param("u")]),
                reducibility: Reducibility::Reducible,
            }],
        }
    }

    fn unary() -> Expr {
        Expr::konst("Unary", vec![])
    }

    fn unary_inductive_module() -> CoreModule {
        let data = InductiveDecl::new(
            "Unary",
            vec![],
            vec![],
            vec![],
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
                universe_params: vec![],
                ty: Expr::sort(Level::succ(Level::zero())),
                data: Box::new(data),
            }],
        }
    }

    fn cert_bytes(module: CoreModule, imports: &[VerifiedModule]) -> (Vec<u8>, VerifiedModule) {
        let cert = build_module_cert(module, imports).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut session = VerifierSession::new();
        for import in imports {
            session.register_verified_module(import.clone());
        }
        let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
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
        VerifiedImportKey::from_verified_module(verified)
    }

    #[test]
    fn projects_verified_module_context_from_certificate_bytes() {
        let (bytes, verified) = cert_bytes(id_module("Test.Id", "id"), &[]);
        let key = key_from_verified(&verified);
        let context = project_import_certificate_context(
            &[input_from_verified(&verified, &bytes)],
            std::slice::from_ref(&key),
            &AxiomPolicy::high_trust(),
        )
        .unwrap();

        assert_eq!(context.direct_import_keys(), std::slice::from_ref(&key));
        assert_eq!(context.verified_modules().len(), 1);
        let entry = &context.verified_modules()[0];
        assert_eq!(entry.key, key);
        assert_eq!(entry.certificate_bytes, bytes);
        assert!(entry.certificate_import_table.is_empty());
        assert_eq!(entry.decl_index_table.len(), 1);
        assert_eq!(entry.decl_index_table[0].decl_index, 0);
        assert_eq!(entry.decl_index_table[0].name, Name::from_dotted("id"));
        assert_eq!(
            entry.decl_index_table[0].hashes,
            verified.declarations()[0].hashes
        );
        assert!(entry.generated_decl_table.is_empty());
        assert_eq!(entry.axiom_report, *verified.axiom_report());
        assert_ne!(entry.decoded_name_table_hash, [0; 32]);
        assert_ne!(entry.decl_index_table_hash, [0; 32]);
        assert_ne!(entry.generated_decl_table_hash, [0; 32]);
        assert_ne!(entry.export_signature_summary_hash, [0; 32]);
        assert_ne!(entry.certified_env_decl_hashes_summary_hash, [0; 32]);
        assert_ne!(entry.axiom_report_hash, [0; 32]);
    }

    #[test]
    fn import_keys_use_machine_api_name_canonical_order() {
        let (b_bytes, verified_b) = cert_bytes(id_module("B", "B.id"), &[]);
        let (aa_bytes, verified_aa) = cert_bytes(id_module("AA", "AA.id"), &[]);
        let b_key = key_from_verified(&verified_b);
        let aa_key = key_from_verified(&verified_aa);

        let context = project_import_certificate_context(
            &[
                input_from_verified(&verified_aa, &aa_bytes),
                input_from_verified(&verified_b, &b_bytes),
            ],
            &[aa_key.clone(), b_key.clone()],
            &AxiomPolicy::high_trust(),
        )
        .unwrap();

        assert_eq!(
            context.direct_import_keys(),
            &[b_key.clone(), aa_key.clone()]
        );
        assert_eq!(context.verified_modules()[0].key, b_key);
        assert_eq!(context.verified_modules()[1].key, aa_key);
    }

    #[test]
    fn verifies_closure_in_dependency_order_and_projects_direct_imports() {
        let (id_bytes, verified_id) = cert_bytes(id_module("Test.Id", "id"), &[]);
        let (use_id_bytes, verified_use_id) =
            cert_bytes(use_id_module(), std::slice::from_ref(&verified_id));
        let id_key = key_from_verified(&verified_id);
        let use_id_key = key_from_verified(&verified_use_id);

        let context = project_import_certificate_context(
            &[
                input_from_verified(&verified_use_id, &use_id_bytes),
                input_from_verified(&verified_id, &id_bytes),
            ],
            std::slice::from_ref(&use_id_key),
            &AxiomPolicy::high_trust(),
        )
        .unwrap();

        assert_eq!(
            context.direct_import_keys(),
            std::slice::from_ref(&use_id_key)
        );
        let direct = context.direct_import_entries();
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].key, use_id_key);
        assert_eq!(direct[0].certificate_import_table, vec![id_key]);
        assert_eq!(context.verified_modules().len(), 2);
    }

    #[test]
    fn projects_generated_constructor_table_from_inductive_certificate() {
        let (bytes, verified) = cert_bytes(unary_inductive_module(), &[]);
        let key = key_from_verified(&verified);
        let context = project_import_certificate_context(
            &[input_from_verified(&verified, &bytes)],
            std::slice::from_ref(&key),
            &AxiomPolicy::high_trust(),
        )
        .unwrap();
        let entry = &context.verified_modules()[0];

        assert_eq!(entry.generated_decl_table.len(), 2);
        assert_eq!(
            entry.generated_decl_table[0].name,
            Name::from_dotted("Unary.zero")
        );
        assert_eq!(entry.generated_decl_table[0].parent_decl_index, 0);
        assert_eq!(
            entry.generated_decl_table[0].kind,
            GeneratedDeclKind::Constructor
        );
        assert_eq!(
            entry.generated_decl_table[1].name,
            Name::from_dotted("Unary.succ")
        );
        assert_eq!(
            entry.generated_decl_table[1].export.decl_interface_hash,
            verified.declarations()[0].hashes.decl_interface_hash
        );
    }

    #[test]
    fn rejects_extra_unreachable_closure_certificate() {
        let (id_bytes, verified_id) = cert_bytes(id_module("Test.Id", "id"), &[]);
        let (extra_bytes, verified_extra) = cert_bytes(id_module("Test.Extra", "extra"), &[]);
        let id_key = key_from_verified(&verified_id);

        let err = project_import_certificate_context(
            &[
                input_from_verified(&verified_id, &id_bytes),
                input_from_verified(&verified_extra, &extra_bytes),
            ],
            std::slice::from_ref(&id_key),
            &AxiomPolicy::high_trust(),
        )
        .unwrap_err();

        assert!(matches!(
            err,
            ImportProjectionError::UnreachableClosureEntry { .. }
        ));
    }

    #[test]
    fn rejects_missing_transitive_dependency_certificate() {
        let (_, verified_id) = cert_bytes(id_module("Test.Id", "id"), &[]);
        let (use_id_bytes, verified_use_id) =
            cert_bytes(use_id_module(), std::slice::from_ref(&verified_id));
        let use_id_key = key_from_verified(&verified_use_id);

        let err = project_import_certificate_context(
            &[input_from_verified(&verified_use_id, &use_id_bytes)],
            std::slice::from_ref(&use_id_key),
            &AxiomPolicy::high_trust(),
        )
        .unwrap_err();

        assert!(matches!(
            err,
            ImportProjectionError::MissingClosureDependency { .. }
        ));
    }
}
