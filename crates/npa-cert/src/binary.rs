use crate::*;

const MODULE_HASH_TRAILER_LEN: usize = 32 * 3;
const CORE_FEATURE_REPORT_TAG: &str = "core_features";

pub(crate) fn encode_module_cert_full_for_header(cert: &ModuleCert) -> Result<Vec<u8>> {
    let version = certificate_format_version(&cert.header)?;
    Ok(encode_module_cert_with_format(cert, version, true))
}

pub(crate) fn encode_module_cert_without_certificate_hash(cert: &ModuleCert) -> Vec<u8> {
    encode_module_cert_with_format(cert, CertificateFormatVersion::Current, false)
}

pub(crate) fn encode_module_cert_without_certificate_hash_for_header(
    cert: &ModuleCert,
) -> Result<Vec<u8>> {
    let version = certificate_format_version(&cert.header)?;
    Ok(encode_module_cert_with_format(cert, version, false))
}

fn encode_module_cert_with_format(
    cert: &ModuleCert,
    version: CertificateFormatVersion,
    include_certificate_hash: bool,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_header_to(&mut out, &cert.header);
    encode_imports_to(&mut out, &cert.imports);
    encode_name_table_to(&mut out, &cert.name_table);
    encode_level_table_to(&mut out, &cert.level_table);
    encode_term_table_to(&mut out, &cert.term_table);
    encode_declarations_to(&mut out, &cert.declarations);
    out.extend(encode_export_block_with_format(&cert.export_block, version));
    out.extend(encode_axiom_report(&cert.axiom_report));
    encode_hash_to(&mut out, &cert.hashes.export_hash);
    encode_hash_to(&mut out, &cert.hashes.axiom_report_hash);
    if include_certificate_hash {
        encode_hash_to(&mut out, &cert.hashes.certificate_hash);
    }
    out
}

fn encode_header_to(out: &mut Vec<u8>, header: &CertHeader) {
    encode_string_to(out, &header.format);
    encode_string_to(out, &header.core_spec);
    encode_name_to(out, &header.module);
}

fn encode_imports_to(out: &mut Vec<u8>, imports: &[ImportEntry]) {
    encode_uvar_to(out, imports.len() as u64);
    for import in imports {
        encode_name_to(out, &import.module);
        encode_hash_to(out, &import.export_hash);
        encode_option_hash_to(out, import.certificate_hash.as_ref());
    }
}

fn encode_name_table_to(out: &mut Vec<u8>, names: &[Name]) {
    encode_uvar_to(out, names.len() as u64);
    for name in names {
        encode_name_to(out, name);
    }
}

fn encode_level_table_to(out: &mut Vec<u8>, levels: &[LevelNode]) {
    encode_uvar_to(out, levels.len() as u64);
    for level in levels {
        match level {
            LevelNode::Zero => out.push(0x00),
            LevelNode::Succ(inner) => {
                out.push(0x01);
                encode_uvar_to(out, *inner as u64);
            }
            LevelNode::Max(lhs, rhs) => {
                out.push(0x02);
                encode_uvar_to(out, *lhs as u64);
                encode_uvar_to(out, *rhs as u64);
            }
            LevelNode::IMax(lhs, rhs) => {
                out.push(0x03);
                encode_uvar_to(out, *lhs as u64);
                encode_uvar_to(out, *rhs as u64);
            }
            LevelNode::Param(name) => {
                out.push(0x04);
                encode_uvar_to(out, *name as u64);
            }
        }
    }
}

fn encode_term_table_to(out: &mut Vec<u8>, terms: &[TermNode]) {
    encode_uvar_to(out, terms.len() as u64);
    for term in terms {
        match term {
            TermNode::Sort(level) => {
                out.push(0x00);
                encode_uvar_to(out, *level as u64);
            }
            TermNode::BVar(index) => {
                out.push(0x01);
                encode_uvar_to(out, *index as u64);
            }
            TermNode::Const { global_ref, levels } => {
                out.push(0x02);
                encode_global_ref_to(out, global_ref);
                encode_usize_vec(out, levels);
            }
            TermNode::App(fun, arg) => {
                out.push(0x03);
                encode_uvar_to(out, *fun as u64);
                encode_uvar_to(out, *arg as u64);
            }
            TermNode::Lam { ty, body } => {
                out.push(0x04);
                encode_uvar_to(out, *ty as u64);
                encode_uvar_to(out, *body as u64);
            }
            TermNode::Pi { ty, body } => {
                out.push(0x05);
                encode_uvar_to(out, *ty as u64);
                encode_uvar_to(out, *body as u64);
            }
            TermNode::Let { ty, value, body } => {
                out.push(0x06);
                encode_uvar_to(out, *ty as u64);
                encode_uvar_to(out, *value as u64);
                encode_uvar_to(out, *body as u64);
            }
        }
    }
}

fn encode_declarations_to(out: &mut Vec<u8>, declarations: &[DeclCert]) {
    encode_uvar_to(out, declarations.len() as u64);
    for decl in declarations {
        encode_decl_payload_to(out, &decl.decl);
        encode_dependency_entries_to(out, &decl.dependencies);
        encode_axiom_refs_to(out, &decl.axiom_dependencies);
        encode_hash_to(out, &decl.hashes.decl_interface_hash);
        encode_hash_to(out, &decl.hashes.decl_certificate_hash);
    }
}

fn encode_decl_payload_to(out: &mut Vec<u8>, decl: &DeclPayload) {
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ty,
        } => {
            out.push(0x00);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar_to(out, *ty as u64);
        }
        DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
        } => {
            out.push(0x10);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs_to(out, universe_constraints);
            encode_uvar_to(out, *ty as u64);
        }
        DeclPayload::Def {
            name,
            universe_params,
            ty,
            value,
            reducibility,
        } => {
            out.push(0x01);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar_to(out, *ty as u64);
            encode_uvar_to(out, *value as u64);
            encode_reducibility_to(out, *reducibility);
        }
        DeclPayload::DefConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            value,
            reducibility,
        } => {
            out.push(0x11);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs_to(out, universe_constraints);
            encode_uvar_to(out, *ty as u64);
            encode_uvar_to(out, *value as u64);
            encode_reducibility_to(out, *reducibility);
        }
        DeclPayload::Theorem {
            name,
            universe_params,
            ty,
            proof,
            opacity,
        } => {
            out.push(0x02);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar_to(out, *ty as u64);
            encode_uvar_to(out, *proof as u64);
            encode_opacity_to(out, *opacity);
        }
        DeclPayload::TheoremConstrained {
            name,
            universe_params,
            universe_constraints,
            ty,
            proof,
            opacity,
        } => {
            out.push(0x12);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs_to(out, universe_constraints);
            encode_uvar_to(out, *ty as u64);
            encode_uvar_to(out, *proof as u64);
            encode_opacity_to(out, *opacity);
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
            out.push(0x03);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_uvar_to(out, params.len() as u64);
            for param in params {
                encode_uvar_to(out, param.ty as u64);
            }
            encode_uvar_to(out, indices.len() as u64);
            for index in indices {
                encode_uvar_to(out, index.ty as u64);
            }
            encode_uvar_to(out, *sort as u64);
            encode_uvar_to(out, constructors.len() as u64);
            for constructor in constructors {
                encode_uvar_to(out, constructor.name as u64);
                encode_uvar_to(out, constructor.ty as u64);
            }
            match recursor {
                Some(recursor) => {
                    out.push(0x01);
                    encode_uvar_to(out, recursor.name as u64);
                    encode_usize_vec(out, &recursor.universe_params);
                    encode_uvar_to(out, recursor.ty as u64);
                    encode_uvar_to(out, recursor.rules.minor_start as u64);
                    encode_uvar_to(out, recursor.rules.major_index as u64);
                }
                None => out.push(0x00),
            }
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
            out.push(0x13);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs_to(out, universe_constraints);
            encode_uvar_to(out, params.len() as u64);
            for param in params {
                encode_uvar_to(out, param.ty as u64);
            }
            encode_uvar_to(out, indices.len() as u64);
            for index in indices {
                encode_uvar_to(out, index.ty as u64);
            }
            encode_uvar_to(out, *sort as u64);
            encode_uvar_to(out, constructors.len() as u64);
            for constructor in constructors {
                encode_uvar_to(out, constructor.name as u64);
                encode_uvar_to(out, constructor.ty as u64);
            }
            match recursor {
                Some(recursor) => {
                    out.push(0x01);
                    encode_uvar_to(out, recursor.name as u64);
                    encode_usize_vec(out, &recursor.universe_params);
                    encode_uvar_to(out, recursor.ty as u64);
                    encode_uvar_to(out, recursor.rules.minor_start as u64);
                    encode_uvar_to(out, recursor.rules.major_index as u64);
                }
                None => out.push(0x00),
            }
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            universe_constraints,
            inductives,
        } => {
            out.push(0x04);
            encode_uvar_to(out, *name as u64);
            encode_usize_vec(out, universe_params);
            encode_universe_constraint_specs_to(out, universe_constraints);
            encode_uvar_to(out, inductives.len() as u64);
            for inductive in inductives {
                encode_uvar_to(out, inductive.name as u64);
                encode_binder_types_to(out, &inductive.params);
                encode_binder_types_to(out, &inductive.indices);
                encode_uvar_to(out, inductive.sort as u64);
                encode_constructor_specs_to(out, &inductive.constructors);
                encode_recursor_spec_to(out, inductive.recursor.as_ref());
            }
        }
    }
}

fn encode_binder_types_to(out: &mut Vec<u8>, binders: &[BinderType]) {
    encode_uvar_to(out, binders.len() as u64);
    for binder in binders {
        encode_uvar_to(out, binder.ty as u64);
    }
}

fn encode_constructor_specs_to(out: &mut Vec<u8>, constructors: &[ConstructorSpec]) {
    encode_uvar_to(out, constructors.len() as u64);
    for constructor in constructors {
        encode_uvar_to(out, constructor.name as u64);
        encode_uvar_to(out, constructor.ty as u64);
    }
}

fn encode_recursor_spec_to(out: &mut Vec<u8>, recursor: Option<&RecursorSpec>) {
    match recursor {
        Some(recursor) => {
            out.push(0x01);
            encode_uvar_to(out, recursor.name as u64);
            encode_usize_vec(out, &recursor.universe_params);
            encode_uvar_to(out, recursor.ty as u64);
            encode_uvar_to(out, recursor.rules.minor_start as u64);
            encode_uvar_to(out, recursor.rules.major_index as u64);
        }
        None => out.push(0x00),
    }
}

fn encode_universe_constraint_specs_to(out: &mut Vec<u8>, constraints: &[UniverseConstraintSpec]) {
    encode_uvar_to(out, constraints.len() as u64);
    for constraint in constraints {
        encode_uvar_to(out, constraint.lhs as u64);
        out.push(match constraint.relation {
            npa_kernel::UniverseConstraintRelation::Le => 0x00,
            npa_kernel::UniverseConstraintRelation::Eq => 0x01,
        });
        encode_uvar_to(out, constraint.rhs as u64);
    }
}

pub(crate) fn encode_export_block(block: &ExportBlock) -> Vec<u8> {
    encode_export_block_with_format(block, CertificateFormatVersion::Current)
}

pub(crate) fn encode_export_block_legacy(block: &ExportBlock) -> Vec<u8> {
    encode_export_block_with_format(block, CertificateFormatVersion::Legacy)
}

pub(crate) fn encode_export_block_previous(block: &ExportBlock) -> Vec<u8> {
    encode_export_block_with_format(block, CertificateFormatVersion::Previous)
}

fn encode_export_block_with_format(
    block: &ExportBlock,
    version: CertificateFormatVersion,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, block.len() as u64);
    for entry in block {
        encode_uvar_to(&mut out, entry.name as u64);
        out.push(match entry.kind {
            ExportKind::Axiom => 0x00,
            ExportKind::Def => 0x01,
            ExportKind::Theorem => 0x02,
            ExportKind::Inductive => 0x03,
            ExportKind::Constructor => 0x04,
            ExportKind::Recursor => 0x05,
        });
        encode_usize_vec(&mut out, &entry.universe_params);
        if version.encodes_export_universe_constraints() {
            encode_universe_constraint_specs_to(&mut out, &entry.universe_constraints);
        }
        encode_uvar_to(&mut out, entry.ty as u64);
        encode_option_usize_to(&mut out, entry.body);
        encode_hash_to(&mut out, &entry.type_hash);
        encode_option_hash_to(&mut out, entry.body_hash.as_ref());
        encode_option_reducibility_to(&mut out, entry.reducibility);
        encode_option_opacity_to(&mut out, entry.opacity);
        encode_hash_to(&mut out, &entry.decl_interface_hash);
        encode_axiom_refs_to(&mut out, &entry.axiom_dependencies);
    }
    out
}

pub(crate) fn encode_axiom_report(report: &AxiomReport) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, report.per_declaration.len() as u64);
    for entry in &report.per_declaration {
        encode_uvar_to(&mut out, entry.decl_index as u64);
        encode_axiom_refs_to(&mut out, &entry.direct_axioms);
        encode_axiom_refs_to(&mut out, &entry.transitive_axioms);
    }
    encode_axiom_refs_to(&mut out, &report.module_axioms);
    if !report.core_features.is_empty() {
        encode_string_to(&mut out, CORE_FEATURE_REPORT_TAG);
        encode_uvar_to(&mut out, report.core_features.len() as u64);
        for feature in &report.core_features {
            encode_string_to(&mut out, feature.as_str());
        }
    }
    out
}

pub(crate) fn encode_dependency_entries_to(out: &mut Vec<u8>, deps: &[DependencyEntry]) {
    encode_uvar_to(out, deps.len() as u64);
    for dep in deps {
        encode_global_ref_to(out, &dep.global_ref);
        encode_hash_to(out, &dep.decl_interface_hash);
    }
}

pub(crate) fn encode_axiom_refs_to(out: &mut Vec<u8>, axioms: &[AxiomRef]) {
    encode_uvar_to(out, axioms.len() as u64);
    for axiom in axioms {
        encode_global_ref_to(out, &axiom.global_ref);
        encode_uvar_to(out, axiom.name as u64);
        encode_hash_to(out, &axiom.decl_interface_hash);
    }
}

pub(crate) fn encode_global_ref_to(out: &mut Vec<u8>, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_uvar_to(out, *name as u64);
            encode_hash_to(out, decl_interface_hash);
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar_to(out, *import_index as u64);
            encode_uvar_to(out, *name as u64);
            encode_hash_to(out, decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_uvar_to(out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_uvar_to(out, *decl_index as u64);
            encode_uvar_to(out, *name as u64);
        }
    }
}

pub(crate) fn encode_name_to(out: &mut Vec<u8>, name: &Name) {
    encode_uvar_to(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string_to(out, component);
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_uvar_to(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.extend(hash);
}

fn encode_option_hash_to(out: &mut Vec<u8>, hash: Option<&Hash>) {
    match hash {
        Some(hash) => {
            out.push(0x01);
            encode_hash_to(out, hash);
        }
        None => out.push(0x00),
    }
}

fn encode_option_usize_to(out: &mut Vec<u8>, value: Option<usize>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_uvar_to(out, value as u64);
        }
        None => out.push(0x00),
    }
}

pub(crate) fn encode_usize_vec(out: &mut Vec<u8>, values: &[usize]) {
    encode_uvar_to(out, values.len() as u64);
    for value in values {
        encode_uvar_to(out, *value as u64);
    }
}

pub(crate) fn encode_reducibility_to(out: &mut Vec<u8>, value: CertReducibility) {
    out.push(match value {
        CertReducibility::Reducible => 0x00,
        CertReducibility::Opaque => 0x01,
    });
}

fn encode_option_reducibility_to(out: &mut Vec<u8>, value: Option<CertReducibility>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_reducibility_to(out, value);
        }
        None => out.push(0x00),
    }
}

pub(crate) fn encode_opacity_to(out: &mut Vec<u8>, value: Opacity) {
    match value {
        Opacity::Opaque => out.push(0x00),
    }
}

fn encode_option_opacity_to(out: &mut Vec<u8>, value: Option<Opacity>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_opacity_to(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_uvar(value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, value);
    out
}

pub(crate) fn encode_uvar_to(out: &mut Vec<u8>, mut value: u64) {
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

pub(crate) struct Decoder<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Decoder<'a> {
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    pub(crate) fn is_done(&self) -> bool {
        self.offset == self.bytes.len()
    }

    fn remaining_len(&self) -> usize {
        self.bytes.len().saturating_sub(self.offset)
    }

    fn has_core_feature_report(&self) -> bool {
        let feature_report_len = self.remaining_len().saturating_sub(MODULE_HASH_TRAILER_LEN);
        let tag = CORE_FEATURE_REPORT_TAG.as_bytes();
        feature_report_len > tag.len()
            && self.bytes.get(self.offset) == Some(&(tag.len() as u8))
            && self.bytes.get(self.offset + 1..self.offset + 1 + tag.len()) == Some(tag)
    }

    pub(crate) fn module_cert(&mut self) -> Result<ModuleCert> {
        let header = self.header()?;
        let version = certificate_format_version(&header)?;
        let imports = self.imports()?;
        let name_table = self.name_table()?;
        let level_table = self.level_table()?;
        let term_table = self.term_table()?;
        let declarations = self.declarations()?;
        let export_block = self.export_block(version)?;
        let mut axiom_report = self.axiom_report()?;
        if self.has_core_feature_report() {
            axiom_report.core_features = self.core_features()?;
        }
        let hashes = ModuleHashes {
            export_hash: self.hash()?,
            axiom_report_hash: self.hash()?,
            certificate_hash: self.hash()?,
        };
        Ok(ModuleCert {
            header,
            imports,
            name_table,
            level_table,
            term_table,
            declarations,
            export_block,
            axiom_report,
            hashes,
        })
    }

    fn header(&mut self) -> Result<CertHeader> {
        Ok(CertHeader {
            format: self.string()?,
            core_spec: self.string()?,
            module: self.name()?,
        })
    }

    fn imports(&mut self) -> Result<Vec<ImportEntry>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(ImportEntry {
                    module: self.name()?,
                    export_hash: self.hash()?,
                    certificate_hash: self.option_hash()?,
                })
            })
            .collect()
    }

    fn name_table(&mut self) -> Result<Vec<Name>> {
        let len = self.bounded_len()?;
        (0..len).map(|_| self.name()).collect()
    }

    fn level_table(&mut self) -> Result<Vec<LevelNode>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(match self.byte()? {
                    0x00 => LevelNode::Zero,
                    0x01 => LevelNode::Succ(self.usize()?),
                    0x02 => LevelNode::Max(self.usize()?, self.usize()?),
                    0x03 => LevelNode::IMax(self.usize()?, self.usize()?),
                    0x04 => LevelNode::Param(self.usize()?),
                    tag => return Err(CertError::UnsupportedEncoding { tag }),
                })
            })
            .collect()
    }

    fn term_table(&mut self) -> Result<Vec<TermNode>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(match self.byte()? {
                    0x00 => TermNode::Sort(self.usize()?),
                    0x01 => TermNode::BVar(self.u32()?),
                    0x02 => TermNode::Const {
                        global_ref: self.global_ref()?,
                        levels: self.usize_vec()?,
                    },
                    0x03 => TermNode::App(self.usize()?, self.usize()?),
                    0x04 => TermNode::Lam {
                        ty: self.usize()?,
                        body: self.usize()?,
                    },
                    0x05 => TermNode::Pi {
                        ty: self.usize()?,
                        body: self.usize()?,
                    },
                    0x06 => TermNode::Let {
                        ty: self.usize()?,
                        value: self.usize()?,
                        body: self.usize()?,
                    },
                    tag => return Err(CertError::UnsupportedEncoding { tag }),
                })
            })
            .collect()
    }

    fn declarations(&mut self) -> Result<Vec<DeclCert>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(DeclCert {
                    decl: self.decl_payload()?,
                    dependencies: self.dependency_entries()?,
                    axiom_dependencies: self.axiom_refs()?,
                    hashes: DeclHashes {
                        decl_interface_hash: self.hash()?,
                        decl_certificate_hash: self.hash()?,
                    },
                })
            })
            .collect()
    }

    fn decl_payload(&mut self) -> Result<DeclPayload> {
        Ok(match self.byte()? {
            0x00 => DeclPayload::Axiom {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
            },
            0x10 => DeclPayload::AxiomConstrained {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize()?,
            },
            0x01 => DeclPayload::Def {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
                value: self.usize()?,
                reducibility: self.reducibility()?,
            },
            0x11 => DeclPayload::DefConstrained {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize()?,
                value: self.usize()?,
                reducibility: self.reducibility()?,
            },
            0x02 => DeclPayload::Theorem {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
                proof: self.usize()?,
                opacity: self.opacity()?,
            },
            0x12 => DeclPayload::TheoremConstrained {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                universe_constraints: self.universe_constraint_specs()?,
                ty: self.usize()?,
                proof: self.usize()?,
                opacity: self.opacity()?,
            },
            0x03 => {
                let name = self.usize()?;
                let universe_params = self.usize_vec()?;
                let params = self.binder_types()?;
                let indices = self.binder_types()?;
                let sort = self.usize()?;
                let constructors_len = self.bounded_len()?;
                let mut constructors = Vec::with_capacity(constructors_len);
                for _ in 0..constructors_len {
                    constructors.push(ConstructorSpec {
                        name: self.usize()?,
                        ty: self.usize()?,
                    });
                }
                let recursor = match self.byte()? {
                    0x00 => None,
                    0x01 => Some(RecursorSpec {
                        name: self.usize()?,
                        universe_params: self.usize_vec()?,
                        ty: self.usize()?,
                        rules: RecursorRulesSpec {
                            minor_start: self.usize()?,
                            major_index: self.usize()?,
                        },
                    }),
                    tag => return Err(CertError::UnsupportedEncoding { tag }),
                };
                DeclPayload::Inductive {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                }
            }
            0x13 => {
                let name = self.usize()?;
                let universe_params = self.usize_vec()?;
                let universe_constraints = self.universe_constraint_specs()?;
                let params = self.binder_types()?;
                let indices = self.binder_types()?;
                let sort = self.usize()?;
                let constructors_len = self.bounded_len()?;
                let mut constructors = Vec::with_capacity(constructors_len);
                for _ in 0..constructors_len {
                    constructors.push(ConstructorSpec {
                        name: self.usize()?,
                        ty: self.usize()?,
                    });
                }
                let recursor = match self.byte()? {
                    0x00 => None,
                    0x01 => Some(RecursorSpec {
                        name: self.usize()?,
                        universe_params: self.usize_vec()?,
                        ty: self.usize()?,
                        rules: RecursorRulesSpec {
                            minor_start: self.usize()?,
                            major_index: self.usize()?,
                        },
                    }),
                    tag => return Err(CertError::UnsupportedEncoding { tag }),
                };
                DeclPayload::InductiveConstrained {
                    name,
                    universe_params,
                    universe_constraints,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor,
                }
            }
            0x04 => {
                let name = self.usize()?;
                let universe_params = self.usize_vec()?;
                let universe_constraints = self.universe_constraint_specs()?;
                let len = self.bounded_len()?;
                let mut inductives = Vec::with_capacity(len);
                for _ in 0..len {
                    inductives.push(MutualInductiveSpec {
                        name: self.usize()?,
                        params: self.binder_types()?,
                        indices: self.binder_types()?,
                        sort: self.usize()?,
                        constructors: self.constructor_specs()?,
                        recursor: self.recursor_spec()?,
                    });
                }
                DeclPayload::MutualInductiveBlock {
                    name,
                    universe_params,
                    universe_constraints,
                    inductives,
                }
            }
            tag => return Err(CertError::UnsupportedEncoding { tag }),
        })
    }

    fn universe_constraint_specs(&mut self) -> Result<Vec<UniverseConstraintSpec>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                let lhs = self.usize()?;
                let relation = match self.byte()? {
                    0x00 => npa_kernel::UniverseConstraintRelation::Le,
                    0x01 => npa_kernel::UniverseConstraintRelation::Eq,
                    tag => return Err(CertError::UnsupportedEncoding { tag }),
                };
                Ok(UniverseConstraintSpec {
                    lhs,
                    relation,
                    rhs: self.usize()?,
                })
            })
            .collect()
    }

    fn binder_types(&mut self) -> Result<Vec<BinderType>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| Ok(BinderType { ty: self.usize()? }))
            .collect()
    }

    fn constructor_specs(&mut self) -> Result<Vec<ConstructorSpec>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(ConstructorSpec {
                    name: self.usize()?,
                    ty: self.usize()?,
                })
            })
            .collect()
    }

    fn recursor_spec(&mut self) -> Result<Option<RecursorSpec>> {
        match self.byte()? {
            0x00 => Ok(None),
            0x01 => Ok(Some(RecursorSpec {
                name: self.usize()?,
                universe_params: self.usize_vec()?,
                ty: self.usize()?,
                rules: RecursorRulesSpec {
                    minor_start: self.usize()?,
                    major_index: self.usize()?,
                },
            })),
            tag => Err(CertError::UnsupportedEncoding { tag }),
        }
    }

    fn export_block(&mut self, version: CertificateFormatVersion) -> Result<ExportBlock> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                let name = self.usize()?;
                let kind = match self.byte()? {
                    0x00 => ExportKind::Axiom,
                    0x01 => ExportKind::Def,
                    0x02 => ExportKind::Theorem,
                    0x03 => ExportKind::Inductive,
                    0x04 => ExportKind::Constructor,
                    0x05 => ExportKind::Recursor,
                    tag => return Err(CertError::UnsupportedEncoding { tag }),
                };
                Ok(ExportEntry {
                    name,
                    kind,
                    universe_params: self.usize_vec()?,
                    universe_constraints: if version.encodes_export_universe_constraints() {
                        self.universe_constraint_specs()?
                    } else {
                        Vec::new()
                    },
                    ty: self.usize()?,
                    body: self.option_usize()?,
                    type_hash: self.hash()?,
                    body_hash: self.option_hash()?,
                    reducibility: self.option_reducibility()?,
                    opacity: self.option_opacity()?,
                    decl_interface_hash: self.hash()?,
                    axiom_dependencies: self.axiom_refs()?,
                })
            })
            .collect()
    }

    fn axiom_report(&mut self) -> Result<AxiomReport> {
        let len = self.bounded_len()?;
        let per_declaration = (0..len)
            .map(|_| {
                Ok(DeclAxiomReport {
                    decl_index: self.usize()?,
                    direct_axioms: self.axiom_refs()?,
                    transitive_axioms: self.axiom_refs()?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let module_axioms = self.axiom_refs()?;
        Ok(AxiomReport {
            per_declaration,
            module_axioms,
            core_features: Vec::new(),
        })
    }

    fn core_features(&mut self) -> Result<Vec<CoreFeature>> {
        let tag = self.string()?;
        if tag != CORE_FEATURE_REPORT_TAG {
            return Err(CertError::NonCanonicalEncoding {
                object: "CoreFeatureReport",
            });
        }
        let len = self.bounded_len()?;
        if len == 0 {
            return Err(CertError::NonCanonicalEncoding {
                object: "CoreFeatureReport",
            });
        }
        let mut features = Vec::with_capacity(len);
        for _ in 0..len {
            let feature = self.string()?;
            let feature = CoreFeature::from_name(&feature)
                .ok_or(CertError::UnsupportedCoreFeature { feature })?;
            features.push(feature);
        }
        if features.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(CertError::NonCanonicalEncoding {
                object: "CoreFeatureReport",
            });
        }
        Ok(features)
    }

    fn dependency_entries(&mut self) -> Result<Vec<DependencyEntry>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(DependencyEntry {
                    global_ref: self.global_ref()?,
                    decl_interface_hash: self.hash()?,
                })
            })
            .collect()
    }

    fn axiom_refs(&mut self) -> Result<Vec<AxiomRef>> {
        let len = self.bounded_len()?;
        (0..len)
            .map(|_| {
                Ok(AxiomRef {
                    global_ref: self.global_ref()?,
                    name: self.usize()?,
                    decl_interface_hash: self.hash()?,
                })
            })
            .collect()
    }

    fn global_ref(&mut self) -> Result<GlobalRef> {
        Ok(match self.byte()? {
            0x03 => GlobalRef::Builtin {
                name: self.usize()?,
                decl_interface_hash: self.hash()?,
            },
            0x00 => GlobalRef::Imported {
                import_index: self.usize()?,
                name: self.usize()?,
                decl_interface_hash: self.hash()?,
            },
            0x01 => GlobalRef::Local {
                decl_index: self.usize()?,
            },
            0x02 => GlobalRef::LocalGenerated {
                decl_index: self.usize()?,
                name: self.usize()?,
            },
            tag => return Err(CertError::UnsupportedEncoding { tag }),
        })
    }

    fn reducibility(&mut self) -> Result<CertReducibility> {
        Ok(match self.byte()? {
            0x00 => CertReducibility::Reducible,
            0x01 => CertReducibility::Opaque,
            tag => return Err(CertError::UnsupportedEncoding { tag }),
        })
    }

    fn option_reducibility(&mut self) -> Result<Option<CertReducibility>> {
        match self.byte()? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.reducibility()?)),
            tag => Err(CertError::UnsupportedEncoding { tag }),
        }
    }

    fn opacity(&mut self) -> Result<Opacity> {
        Ok(match self.byte()? {
            0x00 => Opacity::Opaque,
            tag => return Err(CertError::UnsupportedEncoding { tag }),
        })
    }

    fn option_opacity(&mut self) -> Result<Option<Opacity>> {
        match self.byte()? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.opacity()?)),
            tag => Err(CertError::UnsupportedEncoding { tag }),
        }
    }

    fn name(&mut self) -> Result<Name> {
        let len = self.bounded_len()?;
        if len == 0 {
            return Err(CertError::NonCanonicalEncoding { object: "Name" });
        }
        let mut components = Vec::with_capacity(len);
        for _ in 0..len {
            let component = self.string()?;
            if component.is_empty() || component.contains('.') {
                return Err(CertError::NonCanonicalEncoding { object: "Name" });
            }
            components.push(component);
        }
        let name = Name(components);
        if name.is_canonical() {
            Ok(name)
        } else {
            Err(CertError::NonCanonicalEncoding { object: "Name" })
        }
    }

    fn string(&mut self) -> Result<String> {
        let len = self.usize()?;
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec())
            .map_err(|_| CertError::NonCanonicalEncoding { object: "string" })
    }

    fn usize_vec(&mut self) -> Result<Vec<usize>> {
        let len = self.bounded_len()?;
        (0..len).map(|_| self.usize()).collect()
    }

    fn option_usize(&mut self) -> Result<Option<usize>> {
        match self.byte()? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.usize()?)),
            tag => Err(CertError::UnsupportedEncoding { tag }),
        }
    }

    fn option_hash(&mut self) -> Result<Option<Hash>> {
        match self.byte()? {
            0x00 => Ok(None),
            0x01 => Ok(Some(self.hash()?)),
            tag => Err(CertError::UnsupportedEncoding { tag }),
        }
    }

    fn hash(&mut self) -> Result<Hash> {
        let bytes = self.take(32)?;
        let mut hash = [0; 32];
        hash.copy_from_slice(bytes);
        Ok(hash)
    }

    fn uvar(&mut self) -> Result<u64> {
        let start = self.offset;
        let mut shift = 0;
        let mut value = 0u64;
        loop {
            let byte = self.byte()?;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                let canonical = encode_uvar(value);
                if canonical != self.bytes[start..self.offset] {
                    return Err(CertError::NonCanonicalEncoding { object: "uvar" });
                }
                return Ok(value);
            }
            shift += 7;
            if shift >= 64 {
                return Err(CertError::DecodeError);
            }
        }
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(self.uvar()?).map_err(|_| CertError::DecodeError)
    }

    fn u32(&mut self) -> Result<u32> {
        u32::try_from(self.uvar()?).map_err(|_| CertError::DecodeError)
    }

    fn bounded_len(&mut self) -> Result<usize> {
        let len = self.usize()?;
        let remaining = self.bytes.len().saturating_sub(self.offset);
        if len > remaining {
            return Err(CertError::DecodeError);
        }
        Ok(len)
    }

    fn byte(&mut self) -> Result<u8> {
        let byte = *self.bytes.get(self.offset).ok_or(CertError::DecodeError)?;
        self.offset += 1;
        Ok(byte)
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self.offset.checked_add(len).ok_or(CertError::DecodeError)?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or(CertError::DecodeError)?;
        self.offset = end;
        Ok(bytes)
    }
}
