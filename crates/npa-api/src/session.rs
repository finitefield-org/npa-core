use std::{
    collections::BTreeSet,
    sync::atomic::{AtomicU64, Ordering},
};

use npa_cert::{
    builtin_decl_interface_hash, decode_module_cert, AxiomPolicy, DeclPayload, ExportEntry, Hash,
    Name, TrustMode,
};
use npa_frontend::{
    canonicalize_machine_term_source, decode_machine_term_source_canonical,
    elaborate_machine_term_check, elaborate_machine_term_infer_from_ast, MachineCompileOptions,
    MachineGlobalScopeEntry, MachineResolvedConstant, MachineSurfaceCallableRef,
    MachineSurfaceMode, MachineTermElabContext,
};
use npa_kernel::{Ctx, Decl, Expr};
use npa_tactic::{
    core_expr_hash, machine_tactic_options_canonical_bytes,
    resolved_family_options_canonical_bytes, EqFamilyRef, MachineKernelProfile, MachineProofSpec,
    MachineTacticDiagnostic, MachineTacticDiagnosticKind, MachineTacticEnv, MachineTacticOptions,
    NatFamilyRef, ResolvedEqFamily, ResolvedNatFamily, RewriteDirection, SimpRuleRef,
    VerifiedImportRef,
};
use sha2::{Digest, Sha256};

use crate::adapter::{
    machine_tactic_start_machine_proof_with_kernel_profile, map_frontend_diagnostic_kind,
    MachineApiDiagnosticPhase, MachineApiDiagnosticProjection, MachineApiUpstreamDiagnostic,
};
use crate::callable::{
    build_machine_surface_callable_interface_table, MachineSurfaceCallableInterfaceBuildError,
};
use crate::current::{
    encode_machine_axiom_ref_wire, imported_axiom_ref_to_wire,
    machine_tactic_import_refs_from_context,
    project_checked_current_decl_context_with_kernel_profile,
    validate_checked_current_decl_package_bytes, CheckedCurrentDeclPackageInput,
    MachineAxiomRefWire, MachineCheckedCurrentDeclContext,
};
use crate::json::{JsonValue, JsonValueKind};
use crate::projection::{
    project_import_certificate_context, MachineImportCertificateContext, VerifiedImportKey,
    VerifiedModuleCertificateInput, VerifiedModuleContextEntry,
};
use crate::renderer::{
    MachineApiResolvedDisplayCoreRefOwner, MachineDisplayRenderScope,
    MachineDisplayRenderScopeEntry, MachineGlobalRefView,
};
use crate::snapshot::{MachineSnapshotMaterializationContext, MachineSnapshotStoreError};
use crate::types::{
    is_machine_surface_renderable_name_wire, parse_fully_qualified_name_wire,
    parse_machine_surface_renderable_name_wire, parse_machine_universe_param_name,
    parse_module_name_wire, CheckedMachineProofRoot, HashString, KernelCheckProfileId,
    MachineApiEndpoint, MachineApiErrorWire, MachineApiOptions, MachineApiVersion,
    MachineProofSession, MachineRootTermSource, MachineTacticOptionsRequest, SessionId,
};
use crate::validate_machine_endpoint_envelope;
use crate::validation::{
    parse_request_body, parse_strict_u64_token, validate_json_object, FieldSpec, JsonFieldType,
    JsonPath, MachineApiErrorKind, MachineApiRequestError, MachineApiRequestErrorReason,
    ObjectSchema, StrictUnsignedIntegerError, ValidatedObject,
};

static NEXT_SESSION_LOCAL_ID: AtomicU64 = AtomicU64::new(1);

const ROOT_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("module", JsonFieldType::String),
    FieldSpec::required("theorem_name", JsonFieldType::String),
    FieldSpec::required(
        "source_index",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required("universe_params", JsonFieldType::Array),
    FieldSpec::required("theorem_type", JsonFieldType::Object),
];

const ROOT_THEOREM_TYPE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("format", JsonFieldType::String),
    FieldSpec::required("source", JsonFieldType::String),
];

const IMPORT_CLOSURE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("module", JsonFieldType::String),
    FieldSpec::required("expected_export_hash", JsonFieldType::String),
    FieldSpec::required("expected_certificate_hash", JsonFieldType::String),
    FieldSpec::required("certificate", JsonFieldType::Object),
];

const IMPORT_KEY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("module", JsonFieldType::String),
    FieldSpec::required("expected_export_hash", JsonFieldType::String),
    FieldSpec::required("expected_certificate_hash", JsonFieldType::String),
];

const CERTIFICATE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("encoding", JsonFieldType::String),
    FieldSpec::required("bytes", JsonFieldType::String),
];

const CHECKED_CURRENT_DECL_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("encoding", JsonFieldType::String),
    FieldSpec::required("bytes", JsonFieldType::String),
];

const OPTIONS_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("kernel_check_profile", JsonFieldType::String),
    FieldSpec::required("allow_axioms", JsonFieldType::Array),
    FieldSpec::required("tactic_options", JsonFieldType::Object),
];

const TACTIC_OPTIONS_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("simp_rules", JsonFieldType::Array),
    FieldSpec::required("eq_family", JsonFieldType::Object).allow_null(),
    FieldSpec::required("nat_family", JsonFieldType::Object).allow_null(),
    FieldSpec::required(
        "max_simp_rewrite_steps",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_open_goals",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
    FieldSpec::required(
        "max_metas",
        JsonFieldType::UnsignedInteger { max: u64::MAX },
    ),
];

const SIMP_RULE_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("name", JsonFieldType::String),
    FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    FieldSpec::required("direction", JsonFieldType::String),
];

const EQ_FAMILY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("eq_name", JsonFieldType::String),
    FieldSpec::required("eq_interface_hash", JsonFieldType::String),
    FieldSpec::required("refl_name", JsonFieldType::String),
    FieldSpec::required("refl_interface_hash", JsonFieldType::String),
    FieldSpec::required("rec_name", JsonFieldType::String),
    FieldSpec::required("rec_interface_hash", JsonFieldType::String),
];

const NAT_FAMILY_FIELDS: &[FieldSpec] = &[
    FieldSpec::required("nat_name", JsonFieldType::String),
    FieldSpec::required("nat_interface_hash", JsonFieldType::String),
    FieldSpec::required("zero_name", JsonFieldType::String),
    FieldSpec::required("zero_interface_hash", JsonFieldType::String),
    FieldSpec::required("succ_name", JsonFieldType::String),
    FieldSpec::required("succ_interface_hash", JsonFieldType::String),
    FieldSpec::required("rec_name", JsonFieldType::String),
    FieldSpec::required("rec_interface_hash", JsonFieldType::String),
];

#[derive(Clone, Debug)]
pub struct MachineSessionCreateOk {
    pub session: MachineProofSession,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSessionCreateError {
    pub diagnostic: MachineApiDiagnosticProjection,
    pub error: MachineApiErrorWire,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSessionCreateRequest {
    protocol_version: MachineApiVersion,
    root: MachineSessionRootRequest,
    import_closure: Vec<MachineSessionImportCertificateRequest>,
    imports: Vec<VerifiedImportKey>,
    checked_current_decls: Vec<MachineSessionCheckedCurrentDeclRequest>,
    options: MachineApiOptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MachineSessionRootRequest {
    module: Name,
    theorem_name: Name,
    source_index: u64,
    universe_params: Vec<String>,
    theorem_type: MachineRootTheoremTypeRequest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MachineRootTheoremTypeRequest {
    source: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MachineSessionImportCertificateRequest {
    key: VerifiedImportKey,
    certificate_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MachineSessionCheckedCurrentDeclRequest {
    bytes: Vec<u8>,
}

pub fn create_machine_session(
    source: &str,
) -> Result<MachineSessionCreateOk, Box<MachineSessionCreateError>> {
    let request = parse_session_create_request(source).map_err(request_error)?;

    validate_kernel_profile(request.options.kernel_check_profile)?;
    let import_context =
        build_import_context(&request.import_closure, &request.imports).map_err(|message| {
            semantic_error(
                MachineApiErrorKind::InvalidVerifiedImport,
                MachineApiDiagnosticPhase::SessionCreate,
                message,
            )
        })?;
    validate_root_import_collisions(&request.root, &import_context)?;

    let checked_current_decls = build_checked_current_context(
        &request.root,
        &import_context,
        &request,
        machine_tactic_kernel_profile(request.options.kernel_check_profile),
    )?;
    validate_current_collisions(&request.root, &import_context, &checked_current_decls)?;

    let mut options = request.options.clone();
    validate_allow_axioms(
        &options.allow_axioms,
        &request.root.module,
        &import_context,
        &checked_current_decls,
        options.kernel_check_profile,
    )?;
    validate_tactic_option_head_resolution(
        &options.tactic_options,
        &import_context,
        &checked_current_decls,
    )?;
    let machine_tactic_imports = machine_tactic_direct_import_refs(&import_context)?;
    let machine_tactic_options = machine_tactic_options(&options.tactic_options)?;
    let machine_tactic_kernel_profile = machine_tactic_kernel_profile(options.kernel_check_profile);
    let tactic_env = MachineTacticEnv::new_with_kernel_profile(
        machine_tactic_kernel_profile,
        machine_tactic_imports.clone(),
        checked_current_decls.checked_current_decls().to_vec(),
        machine_tactic_options.clone(),
    )
    .map_err(option_semantic_error)?;
    options.tactic_options = tactic_options_request_from_machine_tactic(&tactic_env.options)?;

    let dependency_axioms = verified_and_current_axioms(&import_context, &checked_current_decls)?;
    ensure_axioms_allowed(&options.allow_axioms, &dependency_axioms)?;

    let callable_table = build_machine_surface_callable_interface_table(
        &request.root.module,
        &import_context,
        &checked_current_decls,
    )
    .map_err(callable_build_error)?;
    let display_scope = build_display_render_scope(
        &request.root.module,
        &import_context,
        &checked_current_decls,
    )?;
    let elab_context = root_term_elab_context(
        &request.root,
        &import_context,
        &checked_current_decls,
        callable_table.clone(),
        options.kernel_check_profile,
    )?;
    let checked_root = check_root_theorem_type(&request.root, &elab_context, &options)?;
    let root_axioms = root_theorem_type_axioms(
        &checked_root.constants,
        &import_context,
        &checked_current_decls,
    )?;
    ensure_axioms_allowed(&options.allow_axioms, &root_axioms)?;

    let proof_spec = MachineProofSpec {
        module: checked_root.root.module.clone(),
        theorem_name: checked_root.root.theorem_name.clone(),
        source_index: checked_root.root.source_index,
        universe_params: checked_root.root.universe_params.clone(),
        theorem_type: checked_root.expr,
    };
    let started = machine_tactic_start_machine_proof_with_kernel_profile(
        machine_tactic_kernel_profile,
        proof_spec,
        machine_tactic_imports,
        checked_current_decls.checked_current_decls().to_vec(),
        machine_tactic_options,
    )
    .map_err(|error| {
        let mut diagnostic = error.diagnostic;
        if !matches!(
            diagnostic.kind,
            MachineApiErrorKind::MachineTermParseError
                | MachineApiErrorKind::MachineTermElaborationError
                | MachineApiErrorKind::UnknownName
                | MachineApiErrorKind::ImplicitArgumentRequired
                | MachineApiErrorKind::TypeMismatch
                | MachineApiErrorKind::ExpectedPiType
        ) {
            diagnostic.kind = MachineApiErrorKind::InvalidMachineProofState;
            diagnostic.phase = MachineApiDiagnosticPhase::SessionCreate;
            diagnostic.primary_name = None;
            diagnostic.expected_hash = None;
            diagnostic.actual_hash = None;
        }
        boxed_error(diagnostic)
    })?;

    let session_root_hash = session_root_hash(SessionRootHashInput {
        protocol_version: request.protocol_version,
        root: &checked_root.root,
        imports: &import_context,
        current: &checked_current_decls,
        options: &options,
        machine_tactic_options: &started.options,
        resolved_eq_family: started.resolved_eq_family.as_ref(),
        resolved_nat_family: started.resolved_nat_family.as_ref(),
        callable_table: &callable_table,
        simp_registry_fingerprint: started.simp_registry_hash,
    });
    let session_id = fresh_session_id();
    let mut snapshots = crate::MachineSnapshotStore::new(session_id.clone());
    let snapshot_context = MachineSnapshotMaterializationContext {
        session_id: &session_id,
        display_scope: &display_scope,
        callable_interface_table: &callable_table,
    };
    let initial_snapshot = snapshots
        .insert_state(&snapshot_context, started.state)
        .map_err(snapshot_store_error)?;

    Ok(MachineSessionCreateOk {
        session: MachineProofSession {
            session_id,
            protocol_version: request.protocol_version,
            session_root_hash,
            root: checked_root.root,
            imports: import_context.direct_import_keys().to_vec(),
            import_certificate_context: import_context,
            machine_display_render_scope: display_scope,
            machine_surface_callable_interface_table: callable_table,
            checked_current_decls,
            options,
            initial_snapshot,
            snapshots,
        },
    })
}

fn parse_session_create_request(
    source: &str,
) -> Result<MachineSessionCreateRequest, MachineApiRequestError> {
    let doc = parse_request_body(source, MachineApiErrorKind::InvalidSessionRequest)?;
    let envelope = validate_machine_endpoint_envelope(
        doc.root(),
        MachineApiEndpoint::CreateSession,
        &JsonPath::root(),
    )?;
    let protocol_version = MachineApiVersion::parse(
        envelope
            .field("protocol_version")
            .and_then(JsonValue::string_value)
            .expect("endpoint validation checked protocol_version string"),
    )
    .expect("endpoint validation checked protocol_version grammar");
    let root = parse_root_request(
        envelope
            .field("root")
            .expect("endpoint validation checked root presence"),
        &JsonPath::root().field("root"),
    )?;
    let import_closure = parse_import_closure_request(
        envelope
            .field("import_closure")
            .expect("endpoint validation checked import_closure presence"),
        &JsonPath::root().field("import_closure"),
    )?;
    let imports = parse_import_keys_request(
        envelope
            .field("imports")
            .expect("endpoint validation checked imports presence"),
        &JsonPath::root().field("imports"),
    )?;
    let checked_current_decls = parse_checked_current_decls_request(
        envelope
            .field("checked_current_decls")
            .expect("endpoint validation checked checked_current_decls presence"),
        &JsonPath::root().field("checked_current_decls"),
    )?;
    let options = parse_options_request(
        envelope
            .field("options")
            .expect("endpoint validation checked options presence"),
        &JsonPath::root().field("options"),
    )?;
    Ok(MachineSessionCreateRequest {
        protocol_version,
        root,
        import_closure,
        imports,
        checked_current_decls,
        options,
    })
}

fn parse_root_request(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineSessionRootRequest, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidSessionRequest, ROOT_FIELDS),
        path,
    )?;
    let module = parse_module_name_wire(required_string(&object, "module")).map_err(|_| {
        grammar_error(
            MachineApiErrorKind::InvalidSessionRequest,
            path.field("module"),
            "module",
            JsonValueKind::String,
        )
    })?;
    let theorem_name =
        parse_machine_surface_renderable_name_wire(required_string(&object, "theorem_name"))
            .map_err(|_| {
                grammar_error(
                    MachineApiErrorKind::InvalidSessionRequest,
                    path.field("theorem_name"),
                    "theorem_name",
                    JsonValueKind::String,
                )
            })?;
    if !has_strict_module_prefix(&module, &theorem_name) {
        return Err(grammar_error(
            MachineApiErrorKind::InvalidSessionRequest,
            path.field("theorem_name"),
            "theorem_name",
            JsonValueKind::String,
        ));
    }
    let source_index = parse_u64_field(&object, "source_index")?;
    let universe_params = parse_universe_params(
        object
            .field("universe_params")
            .expect("root schema checked universe_params presence"),
        &path.field("universe_params"),
    )?;
    let theorem_type = parse_root_theorem_type(
        object
            .field("theorem_type")
            .expect("root schema checked theorem_type presence"),
        &path.field("theorem_type"),
    )?;
    Ok(MachineSessionRootRequest {
        module,
        theorem_name,
        source_index,
        universe_params,
        theorem_type,
    })
}

fn parse_root_theorem_type(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineRootTheoremTypeRequest, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidSessionRequest,
            ROOT_THEOREM_TYPE_FIELDS,
        ),
        path,
    )?;
    if required_string(&object, "format") != "machine_surface_v1" {
        return Err(grammar_error(
            MachineApiErrorKind::InvalidSessionRequest,
            path.field("format"),
            "format",
            JsonValueKind::String,
        ));
    }
    Ok(MachineRootTheoremTypeRequest {
        source: required_string(&object, "source").to_owned(),
    })
}

fn parse_universe_params(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<String>, MachineApiRequestError> {
    let elements = value
        .array_elements()
        .expect("root schema checked universe_params array");
    let mut seen = BTreeSet::new();
    let mut params = Vec::with_capacity(elements.len());
    for (index, item) in elements.iter().enumerate() {
        let item_path = path.index(index);
        let Some(raw) = item.string_value() else {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidSessionRequest,
                item_path,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "universe_params",
                    expected: JsonFieldType::String,
                    actual: item.kind(),
                },
            ));
        };
        let param = parse_machine_universe_param_name(raw).map_err(|_| {
            grammar_error(
                MachineApiErrorKind::InvalidSessionRequest,
                item_path.clone(),
                "universe_params",
                JsonValueKind::String,
            )
        })?;
        if !seen.insert(param.clone()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidSessionRequest,
                item_path,
                MachineApiRequestErrorReason::DuplicateKey { key: param },
            ));
        }
        params.push(param);
    }
    Ok(params)
}

fn parse_import_closure_request(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachineSessionImportCertificateRequest>, MachineApiRequestError> {
    value
        .array_elements()
        .expect("endpoint validation checked import_closure array")
        .iter()
        .enumerate()
        .map(|(index, item)| parse_import_closure_item(item, &path.index(index)))
        .collect()
}

fn parse_import_closure_item(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineSessionImportCertificateRequest, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidVerifiedImport,
            IMPORT_CLOSURE_FIELDS,
        ),
        path,
    )?;
    let key = parse_import_key_fields(&object, path, MachineApiErrorKind::InvalidVerifiedImport)?;
    let certificate = validate_json_object(
        object
            .field("certificate")
            .expect("import_closure schema checked certificate presence"),
        ObjectSchema::new(
            MachineApiErrorKind::InvalidVerifiedImport,
            CERTIFICATE_FIELDS,
        ),
        &path.field("certificate"),
    )?;
    if required_string(&certificate, "encoding") != "npa.certificate.canonical.v0.1.hex" {
        return Err(grammar_error(
            MachineApiErrorKind::InvalidVerifiedImport,
            path.field("certificate").field("encoding"),
            "encoding",
            JsonValueKind::String,
        ));
    }
    let certificate_bytes = decode_hex_bytes(
        required_string(&certificate, "bytes"),
        MachineApiErrorKind::InvalidVerifiedImport,
        path.field("certificate").field("bytes"),
        "bytes",
    )?;
    Ok(MachineSessionImportCertificateRequest {
        key,
        certificate_bytes,
    })
}

fn parse_import_keys_request(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<VerifiedImportKey>, MachineApiRequestError> {
    value
        .array_elements()
        .expect("endpoint validation checked imports array")
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let item_path = path.index(index);
            let object = validate_json_object(
                item,
                ObjectSchema::new(
                    MachineApiErrorKind::InvalidVerifiedImport,
                    IMPORT_KEY_FIELDS,
                ),
                &item_path,
            )?;
            parse_import_key_fields(
                &object,
                &item_path,
                MachineApiErrorKind::InvalidVerifiedImport,
            )
        })
        .collect()
}

fn parse_import_key_fields(
    object: &ValidatedObject<'_, '_>,
    path: &JsonPath,
    error_kind: MachineApiErrorKind,
) -> Result<VerifiedImportKey, MachineApiRequestError> {
    let module = parse_module_name_wire(required_string(object, "module")).map_err(|_| {
        grammar_error(
            error_kind,
            path.field("module"),
            "module",
            JsonValueKind::String,
        )
    })?;
    let expected_export_hash = parse_hash_field(object, "expected_export_hash", path, error_kind)?;
    let expected_certificate_hash =
        parse_hash_field(object, "expected_certificate_hash", path, error_kind)?;
    Ok(VerifiedImportKey::new(
        module,
        expected_export_hash,
        expected_certificate_hash,
    ))
}

fn parse_checked_current_decls_request(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachineSessionCheckedCurrentDeclRequest>, MachineApiRequestError> {
    value
        .array_elements()
        .expect("endpoint validation checked checked_current_decls array")
        .iter()
        .enumerate()
        .map(|(index, item)| parse_checked_current_decl_item(item, &path.index(index)))
        .collect()
}

fn parse_checked_current_decl_item(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineSessionCheckedCurrentDeclRequest, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidCheckedCurrentDecl,
            CHECKED_CURRENT_DECL_FIELDS,
        ),
        path,
    )?;
    if required_string(&object, "encoding")
        != "npa.machine-api.checked-current-decl-package.canonical.v5.hex"
    {
        return Err(grammar_error(
            MachineApiErrorKind::InvalidCheckedCurrentDecl,
            path.field("encoding"),
            "encoding",
            JsonValueKind::String,
        ));
    }
    let bytes = decode_hex_bytes(
        required_string(&object, "bytes"),
        MachineApiErrorKind::InvalidCheckedCurrentDecl,
        path.field("bytes"),
        "bytes",
    )?;
    validate_checked_current_decl_package_bytes(&bytes).map_err(|_| {
        grammar_error(
            MachineApiErrorKind::InvalidCheckedCurrentDecl,
            path.field("bytes"),
            "bytes",
            JsonValueKind::String,
        )
    })?;
    Ok(MachineSessionCheckedCurrentDeclRequest { bytes })
}

fn parse_options_request(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineApiOptions, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            OPTIONS_FIELDS,
        ),
        path,
    )?;
    let kernel_check_profile =
        KernelCheckProfileId::parse(required_string(&object, "kernel_check_profile")).map_err(
            |_| {
                grammar_error(
                    MachineApiErrorKind::InvalidMachineApiOptions,
                    path.field("kernel_check_profile"),
                    "kernel_check_profile",
                    JsonValueKind::String,
                )
            },
        )?;
    let mut allow_axioms = parse_allow_axioms(
        object
            .field("allow_axioms")
            .expect("options schema checked allow_axioms presence"),
        &path.field("allow_axioms"),
    )?;
    sort_dedup_axiom_refs(&mut allow_axioms);
    let tactic_options = parse_tactic_options_request(
        object
            .field("tactic_options")
            .expect("options schema checked tactic_options presence"),
        &path.field("tactic_options"),
    )?;
    Ok(MachineApiOptions {
        kernel_check_profile,
        allow_axioms,
        tactic_options,
    })
}

fn parse_allow_axioms(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Vec<MachineAxiomRefWire>, MachineApiRequestError> {
    value
        .array_elements()
        .expect("options schema checked allow_axioms array")
        .iter()
        .enumerate()
        .map(|(index, item)| parse_allow_axiom_item(item, &path.index(index)))
        .collect()
}

fn parse_allow_axiom_item(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineAxiomRefWire, MachineApiRequestError> {
    let Some(members) = value.object_members() else {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(MachineApiRequestError::new(
                MachineApiErrorKind::InvalidMachineApiOptions,
                path.field(member.key()),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }
    let Some(kind_value) = members.iter().find(|member| member.key() == "kind") else {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.field("kind"),
            MachineApiRequestErrorReason::MissingField { field: "kind" },
        ));
    };
    let Some(kind) = kind_value.value().string_value() else {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.field("kind"),
            MachineApiRequestErrorReason::TypeMismatch {
                field: "kind",
                expected: JsonFieldType::String,
                actual: kind_value.value().kind(),
            },
        ));
    };
    match kind {
        "imported" => parse_allow_axiom_imported(value, path),
        "current_module" => parse_allow_axiom_current_module(value, path),
        "builtin" => parse_allow_axiom_builtin(value, path),
        _ => Err(grammar_error(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.field("kind"),
            "kind",
            JsonValueKind::String,
        )),
    }
}

fn parse_allow_axiom_imported(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineAxiomRefWire, MachineApiRequestError> {
    const FIELDS: &[FieldSpec] = &[
        FieldSpec::required("kind", JsonFieldType::String),
        FieldSpec::required("module", JsonFieldType::String),
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::required("export_hash", JsonFieldType::String),
        FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    ];
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidMachineApiOptions, FIELDS),
        path,
    )?;
    Ok(MachineAxiomRefWire::Imported {
        module: parse_module_name_option(&object, path, "module")?,
        name: parse_fully_qualified_name_option(&object, path, "name")?,
        export_hash: parse_hash_field(
            &object,
            "export_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        decl_interface_hash: parse_hash_field(
            &object,
            "decl_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
    })
}

fn parse_allow_axiom_current_module(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineAxiomRefWire, MachineApiRequestError> {
    const FIELDS: &[FieldSpec] = &[
        FieldSpec::required("kind", JsonFieldType::String),
        FieldSpec::required("module", JsonFieldType::String),
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::required(
            "source_index",
            JsonFieldType::UnsignedInteger { max: u64::MAX },
        ),
        FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    ];
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidMachineApiOptions, FIELDS),
        path,
    )?;
    Ok(MachineAxiomRefWire::CurrentModule {
        module: parse_module_name_option(&object, path, "module")?,
        name: parse_fully_qualified_name_option(&object, path, "name")?,
        source_index: parse_u64_field(&object, "source_index")?,
        decl_interface_hash: parse_hash_field(
            &object,
            "decl_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
    })
}

fn parse_allow_axiom_builtin(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineAxiomRefWire, MachineApiRequestError> {
    const FIELDS: &[FieldSpec] = &[
        FieldSpec::required("kind", JsonFieldType::String),
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::required("decl_interface_hash", JsonFieldType::String),
    ];
    let object = validate_json_object(
        value,
        ObjectSchema::new(MachineApiErrorKind::InvalidMachineApiOptions, FIELDS),
        path,
    )?;
    Ok(MachineAxiomRefWire::Builtin {
        name: parse_fully_qualified_name_option(&object, path, "name")?,
        decl_interface_hash: parse_hash_field(
            &object,
            "decl_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
    })
}

fn parse_tactic_options_request(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<MachineTacticOptionsRequest, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            TACTIC_OPTIONS_FIELDS,
        ),
        path,
    )?;
    let mut simp_rules = object
        .field("simp_rules")
        .expect("tactic options schema checked simp_rules presence")
        .array_elements()
        .expect("tactic options schema checked simp_rules array")
        .iter()
        .enumerate()
        .map(|(index, item)| parse_simp_rule(item, &path.field("simp_rules").index(index)))
        .collect::<Result<Vec<_>, _>>()?;
    sort_dedup_simp_rules(&mut simp_rules);
    let eq_family = parse_optional_eq_family(
        object
            .field("eq_family")
            .expect("tactic options schema checked eq_family presence"),
        &path.field("eq_family"),
    )?;
    let nat_family = parse_optional_nat_family(
        object
            .field("nat_family")
            .expect("tactic options schema checked nat_family presence"),
        &path.field("nat_family"),
    )?;
    Ok(MachineTacticOptionsRequest {
        simp_rules,
        eq_family,
        nat_family,
        max_simp_rewrite_steps: parse_nonzero_u64_field(
            &object,
            "max_simp_rewrite_steps",
            &path.field("max_simp_rewrite_steps"),
        )?,
        max_open_goals: parse_nonzero_u64_field(
            &object,
            "max_open_goals",
            &path.field("max_open_goals"),
        )?,
        max_metas: parse_nonzero_u64_field(&object, "max_metas", &path.field("max_metas"))?,
    })
}

fn parse_simp_rule(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<SimpRuleRef, MachineApiRequestError> {
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            SIMP_RULE_FIELDS,
        ),
        path,
    )?;
    let direction = match required_string(&object, "direction") {
        "forward" => RewriteDirection::Forward,
        "backward" => RewriteDirection::Backward,
        _ => {
            return Err(grammar_error(
                MachineApiErrorKind::InvalidMachineApiOptions,
                path.field("direction"),
                "direction",
                JsonValueKind::String,
            ));
        }
    };
    Ok(SimpRuleRef {
        name: parse_renderable_name_option(&object, path, "name")?,
        decl_interface_hash: parse_hash_field(
            &object,
            "decl_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        direction,
    })
}

fn parse_optional_eq_family(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Option<EqFamilyRef>, MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            EQ_FAMILY_FIELDS,
        ),
        path,
    )?;
    Ok(Some(EqFamilyRef {
        eq_name: parse_renderable_name_option(&object, path, "eq_name")?,
        eq_interface_hash: parse_hash_field(
            &object,
            "eq_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        refl_name: parse_renderable_name_option(&object, path, "refl_name")?,
        refl_interface_hash: parse_hash_field(
            &object,
            "refl_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        rec_name: parse_renderable_name_option(&object, path, "rec_name")?,
        rec_interface_hash: parse_hash_field(
            &object,
            "rec_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
    }))
}

fn parse_optional_nat_family(
    value: &JsonValue<'_>,
    path: &JsonPath,
) -> Result<Option<NatFamilyRef>, MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let object = validate_json_object(
        value,
        ObjectSchema::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            NAT_FAMILY_FIELDS,
        ),
        path,
    )?;
    Ok(Some(NatFamilyRef {
        nat_name: parse_renderable_name_option(&object, path, "nat_name")?,
        nat_interface_hash: parse_hash_field(
            &object,
            "nat_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        zero_name: parse_renderable_name_option(&object, path, "zero_name")?,
        zero_interface_hash: parse_hash_field(
            &object,
            "zero_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        succ_name: parse_renderable_name_option(&object, path, "succ_name")?,
        succ_interface_hash: parse_hash_field(
            &object,
            "succ_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
        rec_name: parse_renderable_name_option(&object, path, "rec_name")?,
        rec_interface_hash: parse_hash_field(
            &object,
            "rec_interface_hash",
            path,
            MachineApiErrorKind::InvalidMachineApiOptions,
        )?,
    }))
}

fn validate_kernel_profile(
    profile: KernelCheckProfileId,
) -> Result<(), Box<MachineSessionCreateError>> {
    match profile {
        KernelCheckProfileId::BuiltinNone => Ok(()),
        KernelCheckProfileId::BuiltinNatEqRec => Ok(()),
    }
}

fn machine_tactic_kernel_profile(profile: KernelCheckProfileId) -> MachineKernelProfile {
    match profile {
        KernelCheckProfileId::BuiltinNone => MachineKernelProfile::BuiltinNone,
        KernelCheckProfileId::BuiltinNatEqRec => MachineKernelProfile::BuiltinNatEqRec,
    }
}

fn build_import_context(
    import_closure: &[MachineSessionImportCertificateRequest],
    imports: &[VerifiedImportKey],
) -> Result<MachineImportCertificateContext, String> {
    let policy = high_trust_policy_for_imports(import_closure)?;
    let closure_inputs = import_closure
        .iter()
        .map(|input| VerifiedModuleCertificateInput {
            module: &input.key.module,
            expected_export_hash: input.key.export_hash,
            expected_certificate_hash: input.key.certificate_hash,
            certificate_bytes: &input.certificate_bytes,
        })
        .collect::<Vec<_>>();
    project_import_certificate_context(&closure_inputs, imports, &policy)
        .map_err(|err| format!("import certificate projection failed: {err:?}"))
}

fn high_trust_policy_for_imports(
    import_closure: &[MachineSessionImportCertificateRequest],
) -> Result<AxiomPolicy, String> {
    let mut allowlisted_axioms = BTreeSet::new();
    for input in import_closure {
        let cert = decode_module_cert(&input.certificate_bytes).map_err(|err| {
            format!("certificate decode failed before high-trust verify: {err:?}")
        })?;
        allowlisted_axioms.extend(cert.name_table.into_iter().filter(Name::is_canonical));
    }
    Ok(AxiomPolicy {
        mode: TrustMode::HighTrust,
        allowlisted_axioms,
        deny_sorry: true,
        supported_core_features: BTreeSet::new(),
    })
}

fn validate_root_import_collisions(
    root: &MachineSessionRootRequest,
    imports: &MachineImportCertificateContext,
) -> Result<(), Box<MachineSessionCreateError>> {
    if imports
        .verified_modules()
        .iter()
        .any(|entry| entry.key.module == root.module)
    {
        return Err(semantic_error(
            MachineApiErrorKind::InvalidSessionRequest,
            MachineApiDiagnosticPhase::SessionCreate,
            format!(
                "root module {} collides with a verified import module",
                root.module.as_dotted()
            ),
        ));
    }
    if direct_public_export_names(imports)?.contains(&root.theorem_name) {
        return Err(semantic_error(
            MachineApiErrorKind::InvalidSessionRequest,
            MachineApiDiagnosticPhase::SessionCreate,
            format!(
                "root theorem {} collides with a direct import export",
                root.theorem_name.as_dotted()
            ),
        ));
    }
    Ok(())
}

fn build_checked_current_context(
    root: &MachineSessionRootRequest,
    import_context: &MachineImportCertificateContext,
    request: &MachineSessionCreateRequest,
    kernel_profile: MachineKernelProfile,
) -> Result<MachineCheckedCurrentDeclContext, Box<MachineSessionCreateError>> {
    let inputs = request
        .checked_current_decls
        .iter()
        .map(|input| CheckedCurrentDeclPackageInput {
            bytes: &input.bytes,
        })
        .collect::<Vec<_>>();
    project_checked_current_decl_context_with_kernel_profile(
        kernel_profile,
        &root.module,
        root.source_index,
        import_context,
        &inputs,
    )
    .map_err(|err| {
        semantic_error(
            MachineApiErrorKind::InvalidCheckedCurrentDecl,
            MachineApiDiagnosticPhase::SessionCreate,
            format!("checked current declaration projection failed: {err:?}"),
        )
    })
}

fn validate_current_collisions(
    root: &MachineSessionRootRequest,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<(), Box<MachineSessionCreateError>> {
    let mut occupied = direct_public_export_names(imports)?;
    occupied.insert(root.theorem_name.clone());
    let mut current_names = BTreeSet::new();
    for entry in current.decl_index_table() {
        let name = &entry.signature.name;
        if !has_strict_module_prefix(&root.module, name)
            || !is_machine_surface_renderable_name_wire(name)
        {
            return Err(invalid_current_name(
                name,
                "current declaration name is outside the root module or not renderable",
            ));
        }
        if !current_names.insert(name.clone()) || occupied.contains(name) {
            return Err(invalid_current_name(
                name,
                "current declaration name collides with the session scope",
            ));
        }
    }
    occupied.extend(current_names);
    let mut generated_names = BTreeSet::new();
    for generated in current.generated_decl_table() {
        let name = &generated.generated_name;
        if generated.module != root.module
            || !has_strict_module_prefix(&root.module, name)
            || !is_machine_surface_renderable_name_wire(name)
        {
            return Err(invalid_current_name(
                name,
                "generated current declaration name is outside the root module or not renderable",
            ));
        }
        if !generated_names.insert(name.clone()) || occupied.contains(name) {
            return Err(invalid_current_name(
                name,
                "generated current declaration name collides with the session scope",
            ));
        }
    }
    Ok(())
}

fn validate_allow_axioms(
    allow_axioms: &[MachineAxiomRefWire],
    root_module: &Name,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
    kernel_check_profile: KernelCheckProfileId,
) -> Result<(), Box<MachineSessionCreateError>> {
    for axiom in allow_axioms {
        match axiom {
            MachineAxiomRefWire::Imported {
                module,
                name,
                export_hash,
                decl_interface_hash,
            } => {
                let Some(entry) = imports.verified_modules().iter().find(|entry| {
                    entry.key.module == *module && entry.key.export_hash == *export_hash
                }) else {
                    return Err(invalid_options(format!(
                        "allow_axioms imported module {} is unknown",
                        module.as_dotted()
                    )));
                };
                let Some(decl) = entry.decl_index_table.iter().find(|decl| {
                    decl.name == *name && decl.hashes.decl_interface_hash == *decl_interface_hash
                }) else {
                    return Err(invalid_options(format!(
                        "allow_axioms imported axiom {} is unknown",
                        name.as_dotted()
                    )));
                };
                if !matches!(decl.decl, DeclPayload::Axiom { .. }) {
                    return Err(invalid_options(format!(
                        "allow_axioms imported ref {} is not an axiom",
                        name.as_dotted()
                    )));
                }
            }
            MachineAxiomRefWire::CurrentModule {
                module,
                name,
                source_index,
                decl_interface_hash,
            } => {
                if module != root_module {
                    return Err(invalid_options(format!(
                        "allow_axioms current module {} does not match root module {}",
                        module.as_dotted(),
                        root_module.as_dotted()
                    )));
                }
                let Some(entry) = current
                    .decl_index_table()
                    .iter()
                    .find(|entry| entry.source_index == *source_index)
                else {
                    return Err(invalid_options(format!(
                        "allow_axioms current source_index {source_index} is unknown"
                    )));
                };
                if entry.signature.name != *name
                    || entry.signature.decl_interface_hash != *decl_interface_hash
                    || !matches!(entry.core_decl, Decl::Axiom { .. })
                {
                    return Err(invalid_options(format!(
                        "allow_axioms current ref {} is not an axiom",
                        name.as_dotted()
                    )));
                }
            }
            MachineAxiomRefWire::Builtin {
                name,
                decl_interface_hash,
            } => {
                if matches!(kernel_check_profile, KernelCheckProfileId::BuiltinNone) {
                    return Err(invalid_options(format!(
                        "allow_axioms builtin ref {} is not allowed by kernel_check_profile {}",
                        name.as_dotted(),
                        kernel_check_profile.as_str()
                    )));
                }
                if name.as_dotted() != "Eq.rec"
                    || builtin_decl_interface_hash(name) != Some(*decl_interface_hash)
                {
                    return Err(invalid_options(format!(
                        "allow_axioms builtin ref {} is not an allowed builtin axiom",
                        name.as_dotted()
                    )));
                }
            }
        }
    }
    Ok(())
}

fn machine_tactic_direct_import_refs(
    import_context: &MachineImportCertificateContext,
) -> Result<Vec<VerifiedImportRef>, Box<MachineSessionCreateError>> {
    machine_tactic_import_refs_from_context(import_context).map_err(|diagnostic| {
        machine_tactic_import_error(diagnostic, MachineApiErrorKind::InvalidVerifiedImport)
    })
}

fn machine_tactic_options(
    options: &MachineTacticOptionsRequest,
) -> Result<MachineTacticOptions, Box<MachineSessionCreateError>> {
    options
        .clone()
        .try_into()
        .map_err(|err| invalid_options(format!("invalid tactic option integer width: {err:?}")))
}

pub(crate) fn validate_machine_tactic_options_request_against_context(
    kernel_check_profile: KernelCheckProfileId,
    options: &MachineTacticOptionsRequest,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<MachineTacticOptionsRequest, Box<MachineSessionCreateError>> {
    validate_tactic_option_head_resolution(options, imports, current)?;
    let machine_tactic_imports = machine_tactic_direct_import_refs(imports)?;
    let machine_tactic_options = machine_tactic_options(options)?;
    let tactic_env = MachineTacticEnv::new_with_kernel_profile(
        machine_tactic_kernel_profile(kernel_check_profile),
        machine_tactic_imports,
        current.checked_current_decls().to_vec(),
        machine_tactic_options,
    )
    .map_err(option_semantic_error)?;
    tactic_options_request_from_machine_tactic(&tactic_env.options)
}

fn tactic_options_request_from_machine_tactic(
    options: &MachineTacticOptions,
) -> Result<MachineTacticOptionsRequest, Box<MachineSessionCreateError>> {
    Ok(MachineTacticOptionsRequest {
        simp_rules: options.simp_rules.clone(),
        eq_family: options.eq_family.clone(),
        nat_family: options.nat_family.clone(),
        max_simp_rewrite_steps: options.max_simp_rewrite_steps,
        max_open_goals: u64::try_from(options.max_open_goals).map_err(|_| {
            invalid_options("max_open_goals does not fit u64 after machine tactic validation")
        })?,
        max_metas: u64::try_from(options.max_metas).map_err(|_| {
            invalid_options("max_metas does not fit u64 after machine tactic validation")
        })?,
    })
}

fn validate_tactic_option_head_resolution(
    options: &MachineTacticOptionsRequest,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<(), Box<MachineSessionCreateError>> {
    for rule in &options.simp_rules {
        validate_tactic_option_head(&rule.name, &rule.decl_interface_hash, imports, current)?;
    }
    if let Some(family) = &options.eq_family {
        for (name, hash) in [
            (&family.eq_name, &family.eq_interface_hash),
            (&family.refl_name, &family.refl_interface_hash),
            (&family.rec_name, &family.rec_interface_hash),
        ] {
            validate_tactic_option_head(name, hash, imports, current)?;
        }
    }
    if let Some(family) = &options.nat_family {
        for (name, hash) in [
            (&family.nat_name, &family.nat_interface_hash),
            (&family.zero_name, &family.zero_interface_hash),
            (&family.succ_name, &family.succ_interface_hash),
            (&family.rec_name, &family.rec_interface_hash),
        ] {
            validate_tactic_option_head(name, hash, imports, current)?;
        }
    }
    Ok(())
}

fn validate_tactic_option_head(
    name: &Name,
    decl_interface_hash: &Hash,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<(), Box<MachineSessionCreateError>> {
    if current.generated_decl_table().iter().any(|entry| {
        entry.generated_name == *name && entry.generated_decl_interface_hash == *decl_interface_hash
    }) {
        return Err(invalid_option_head(
            name,
            format!(
                "tactic option head {} resolves only as a current generated declaration",
                name.as_dotted()
            ),
        ));
    }

    let mut matches = 0usize;
    for import in imports.direct_import_entries() {
        for export in &import.export_block {
            if export.decl_interface_hash == *decl_interface_hash
                && export_name(import, export)? == *name
            {
                matches += 1;
            }
        }
    }
    matches += current
        .decl_index_table()
        .iter()
        .filter(|entry| {
            entry.signature.name == *name
                && entry.signature.decl_interface_hash == *decl_interface_hash
        })
        .count();

    match matches {
        1 => Ok(()),
        0 => Err(invalid_option_head(
            name,
            format!(
                "tactic option head {} with the requested interface hash is outside the session option scope",
                name.as_dotted()
            ),
        )),
        _ => Err(invalid_option_head(
            name,
            format!("tactic option head {} is ambiguous", name.as_dotted()),
        )),
    }
}

fn verified_and_current_axioms(
    import_context: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<Vec<MachineAxiomRefWire>, Box<MachineSessionCreateError>> {
    let mut axioms = Vec::new();
    for entry in import_context.verified_modules() {
        for axiom in &entry.axiom_report.module_axioms {
            axioms.push(
                imported_axiom_ref_to_wire(0, import_context, entry, axiom).map_err(|err| {
                    semantic_error(
                        MachineApiErrorKind::InvalidVerifiedImport,
                        MachineApiDiagnosticPhase::SessionCreate,
                        format!("verified import axiom report is malformed: {err:?}"),
                    )
                })?,
            );
        }
    }
    for entry in current.decl_index_table() {
        axioms.extend(entry.dependency_report.axiom_dependencies.clone());
    }
    sort_dedup_axiom_refs(&mut axioms);
    Ok(axioms)
}

fn ensure_axioms_allowed(
    allow_axioms: &[MachineAxiomRefWire],
    dependencies: &[MachineAxiomRefWire],
) -> Result<(), Box<MachineSessionCreateError>> {
    let allowed = allow_axioms
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<BTreeSet<_>>();
    for axiom in dependencies {
        if !allowed.contains(&encode_machine_axiom_ref_wire(axiom)) {
            return Err(disallowed_axiom_error(axiom.clone()));
        }
    }
    Ok(())
}

fn build_display_render_scope(
    root_module: &Name,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<MachineDisplayRenderScope, Box<MachineSessionCreateError>> {
    let mut entries = Vec::new();
    for (import_index, import) in imports.direct_import_entries().iter().enumerate() {
        for export in &import.export_block {
            let name = export_name(import, export)?;
            let callable_ref = MachineSurfaceCallableRef::Imported {
                module: import.key.module.clone(),
                name: name.clone(),
                export_hash: import.key.export_hash,
                decl_interface_hash: export.decl_interface_hash,
            };
            let owner_context = MachineApiResolvedDisplayCoreRefOwner::VerifiedImportedModule {
                owner_module: import.key.module.clone(),
                owner_export_hash: import.key.export_hash,
            };
            let view = imported_export_view(import, export, &name)?;
            let entry = MachineDisplayRenderScopeEntry::new(view, owner_context, callable_ref)
                .with_candidate_resolution(MachineGlobalScopeEntry::Imported {
                    name,
                    import_index: import_index as u32,
                    decl_interface_hash: export.decl_interface_hash,
                });
            entries.push(entry);
        }
    }
    for entry in current.decl_index_table() {
        let name = entry.signature.name.clone();
        let view = MachineGlobalRefView::CurrentModule {
            module: root_module.clone(),
            name: name.clone(),
            decl_interface_hash: entry.signature.decl_interface_hash,
            source_index: entry.source_index,
        };
        entries.push(
            MachineDisplayRenderScopeEntry::new(
                view,
                MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                    module: root_module.clone(),
                },
                MachineSurfaceCallableRef::CurrentModule {
                    module: root_module.clone(),
                    name: name.clone(),
                    source_index: entry.source_index,
                    decl_interface_hash: entry.signature.decl_interface_hash,
                },
            )
            .with_candidate_resolution(MachineGlobalScopeEntry::CurrentModule {
                name,
                source_index: entry.source_index,
                decl_interface_hash: entry.signature.decl_interface_hash,
            }),
        );
    }
    for generated in current.generated_decl_table() {
        let name = generated.generated_name.clone();
        let view = MachineGlobalRefView::LocalGenerated {
            module: root_module.clone(),
            export_hash: None,
            parent_name: generated.parent_name.clone(),
            name: name.clone(),
            parent_decl_interface_hash: generated.parent_decl_interface_hash,
            decl_interface_hash: generated.generated_decl_interface_hash,
            public_export: false,
            tactic_head_visible: false,
        };
        entries.push(
            MachineDisplayRenderScopeEntry::new(
                view,
                MachineApiResolvedDisplayCoreRefOwner::CurrentSessionRootModule {
                    module: root_module.clone(),
                },
                MachineSurfaceCallableRef::CurrentGenerated {
                    module: root_module.clone(),
                    name: name.clone(),
                    parent_source_index: generated.parent_source_index,
                    decl_interface_hash: generated.generated_decl_interface_hash,
                },
            )
            .with_candidate_resolution(MachineGlobalScopeEntry::CurrentGenerated {
                name,
                parent_source_index: generated.parent_source_index,
                decl_interface_hash: generated.generated_decl_interface_hash,
            }),
        );
    }
    MachineDisplayRenderScope::from_entries(entries).map_err(|err| {
        semantic_error(
            MachineApiErrorKind::InvalidMachineProofState,
            MachineApiDiagnosticPhase::SessionCreate,
            format!("display render scope construction failed: {err:?}"),
        )
    })
}

fn root_term_elab_context(
    root: &MachineSessionRootRequest,
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
    callable_table: npa_frontend::MachineSurfaceCallableInterfaceTable,
    kernel_check_profile: KernelCheckProfileId,
) -> Result<MachineTermElabContext, Box<MachineSessionCreateError>> {
    let direct_verified_modules = imports
        .direct_import_entries()
        .iter()
        .map(|entry| entry.verified_module.clone())
        .collect::<Vec<_>>();
    let all_verified_modules = imports
        .verified_modules()
        .iter()
        .map(|entry| entry.verified_module.clone())
        .collect::<Vec<_>>();
    let frontend_current_decls = current
        .decl_index_table()
        .iter()
        .map(|entry| npa_frontend::MachineCheckedCurrentDecl {
            name: entry.signature.name.clone(),
            source_index: entry.source_index,
            decl_interface_hash: entry.signature.decl_interface_hash,
            decl: entry.core_decl.clone(),
        })
        .collect::<Vec<_>>();
    let frontend_generated_decls = current
        .generated_decl_table()
        .iter()
        .map(|entry| npa_frontend::MachineCheckedCurrentGeneratedDecl {
            name: entry.generated_name.clone(),
            parent_source_index: entry.parent_source_index,
            decl_interface_hash: entry.generated_decl_interface_hash,
        })
        .collect::<Vec<_>>();
    MachineTermElabContext::from_verified_modules_and_current_decls_in_module_request(
        npa_frontend::MachineTermElabContextInModuleRequest {
            direct_verified_modules: &direct_verified_modules,
            available_verified_modules: &all_verified_modules,
            current_module: root.module.clone(),
            checked_current_decls: &frontend_current_decls,
            current_generated_decls: &frontend_generated_decls,
            local_context: Vec::new(),
            universe_params: root.universe_params.clone(),
            allow_builtin_kernel_decls: matches!(
                kernel_check_profile,
                KernelCheckProfileId::BuiltinNatEqRec
            ),
        },
    )
    .map(|context| context.with_callable_interface_table(callable_table))
    .map_err(|diagnostic| frontend_error(diagnostic, MachineApiDiagnosticPhase::SessionCreate))
}

#[derive(Clone, Debug)]
struct CheckedRootTerm {
    root: CheckedMachineProofRoot,
    expr: Expr,
    constants: Vec<MachineResolvedConstant>,
}

fn check_root_theorem_type(
    root: &MachineSessionRootRequest,
    context: &MachineTermElabContext,
    _options: &MachineApiOptions,
) -> Result<CheckedRootTerm, Box<MachineSessionCreateError>> {
    let canonical =
        canonicalize_machine_term_source(&root.theorem_type.source).map_err(|diagnostic| {
            frontend_error(diagnostic, MachineApiDiagnosticPhase::MachineTermParse)
        })?;
    let ast =
        decode_machine_term_source_canonical(&canonical.canonical_bytes).map_err(|diagnostic| {
            frontend_error(diagnostic, MachineApiDiagnosticPhase::MachineTermParse)
        })?;
    let compile_options = MachineCompileOptions {
        mode: MachineSurfaceMode::Complete,
        allow_universe_meta: false,
    };
    let (_expr, inferred_type) =
        elaborate_machine_term_infer_from_ast(&ast, context, &compile_options).map_err(
            |diagnostic| frontend_error(diagnostic, MachineApiDiagnosticPhase::MachineTermCheck),
        )?;
    ensure_inferred_type_is_sort(context, &root.universe_params, &inferred_type)?;
    let checked = elaborate_machine_term_check(
        &root.theorem_type.source,
        context,
        &inferred_type,
        &compile_options,
    )
    .map_err(|diagnostic| {
        frontend_error(diagnostic, MachineApiDiagnosticPhase::MachineTermCheck)
    })?;
    ensure_inferred_type_is_sort(context, &root.universe_params, &checked.inferred_type)?;
    let theorem_type_core_hash = core_expr_hash(&checked.expr);
    Ok(CheckedRootTerm {
        root: CheckedMachineProofRoot {
            module: root.module.clone(),
            theorem_name: root.theorem_name.clone(),
            source_index: root.source_index,
            universe_params: root.universe_params.clone(),
            theorem_type_source: MachineRootTermSource {
                source: canonical.source,
                frontend_canonical_hash: canonical.canonical_hash,
            },
            theorem_type_core_hash,
        },
        expr: checked.expr,
        constants: checked.constants,
    })
}

fn ensure_inferred_type_is_sort(
    context: &MachineTermElabContext,
    universe_params: &[String],
    inferred_type: &Expr,
) -> Result<(), Box<MachineSessionCreateError>> {
    match context
        .kernel_env()
        .env()
        .whnf(&Ctx::new(), universe_params, inferred_type)
    {
        Ok(Expr::Sort(_)) => Ok(()),
        Ok(actual) => Err(machine_term_check_error(format!(
            "root theorem type must have a sort type, got {actual:?}"
        ))),
        Err(err) => Err(machine_term_check_error(format!(
            "kernel rejected root theorem type: {err:?}"
        ))),
    }
}

fn root_theorem_type_axioms(
    constants: &[MachineResolvedConstant],
    imports: &MachineImportCertificateContext,
    current: &MachineCheckedCurrentDeclContext,
) -> Result<Vec<MachineAxiomRefWire>, Box<MachineSessionCreateError>> {
    let mut axioms = Vec::new();
    for constant in constants {
        if let Some((entry, export)) =
            direct_export_by_name_hash(imports, &constant.name, &constant.decl_interface_hash)?
        {
            for axiom in &export.axiom_dependencies {
                axioms.push(
                    imported_axiom_ref_to_wire(0, imports, entry, axiom).map_err(|err| {
                        semantic_error(
                            MachineApiErrorKind::InvalidMachineProofState,
                            MachineApiDiagnosticPhase::SessionCreate,
                            format!("root theorem imported axiom dependency is malformed: {err:?}"),
                        )
                    })?,
                );
            }
            continue;
        }
        if let Some(entry) = current.decl_index_table().iter().find(|entry| {
            entry.signature.name == constant.name
                && entry.signature.decl_interface_hash == constant.decl_interface_hash
        }) {
            axioms.extend(entry.dependency_report.axiom_dependencies.clone());
            continue;
        }
        if let Some(generated) = current.generated_decl_table().iter().find(|entry| {
            entry.generated_name == constant.name
                && entry.generated_decl_interface_hash == constant.decl_interface_hash
        }) {
            let Some(parent) = current
                .decl_index_table()
                .iter()
                .find(|entry| entry.source_index == generated.parent_source_index)
            else {
                return Err(invalid_machine_state(
                    "root theorem current generated dependency has no parent declaration",
                ));
            };
            axioms.extend(parent.dependency_report.axiom_dependencies.clone());
            continue;
        }
        if builtin_decl_interface_hash(&constant.name) == Some(constant.decl_interface_hash) {
            if constant.name.as_dotted() == "Eq.rec" {
                axioms.push(MachineAxiomRefWire::Builtin {
                    name: constant.name.clone(),
                    decl_interface_hash: constant.decl_interface_hash,
                });
            }
            continue;
        }
        return Err(invalid_machine_state(format!(
            "root theorem type constant {} is outside the session context",
            constant.name.as_dotted()
        )));
    }
    sort_dedup_axiom_refs(&mut axioms);
    Ok(axioms)
}

struct SessionRootHashInput<'a> {
    protocol_version: MachineApiVersion,
    root: &'a CheckedMachineProofRoot,
    imports: &'a MachineImportCertificateContext,
    current: &'a MachineCheckedCurrentDeclContext,
    options: &'a MachineApiOptions,
    machine_tactic_options: &'a MachineTacticOptions,
    resolved_eq_family: Option<&'a ResolvedEqFamily>,
    resolved_nat_family: Option<&'a ResolvedNatFamily>,
    callable_table: &'a npa_frontend::MachineSurfaceCallableInterfaceTable,
    simp_registry_fingerprint: Hash,
}

fn session_root_hash(input: SessionRootHashInput<'_>) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.session-root.v1");
    encode_string(&mut out, input.protocol_version.as_str());
    out.extend(input.root.canonical_bytes());
    encode_import_certificate_context_to(&mut out, input.imports);
    out.extend(input.callable_table.table_hash());
    encode_direct_imports_to(&mut out, input.imports);
    encode_checked_current_to(&mut out, input.current);
    encode_machine_api_options_to(
        &mut out,
        input.options,
        input.machine_tactic_options,
        input.resolved_eq_family,
        input.resolved_nat_family,
        &input.simp_registry_fingerprint,
    );
    sha256(&out)
}

fn encode_import_certificate_context_to(
    out: &mut Vec<u8>,
    imports: &MachineImportCertificateContext,
) {
    encode_string(out, "npa.machine-api.session-import-context.v1");
    encode_list_len(out, imports.verified_modules().len());
    for entry in imports.verified_modules() {
        encode_verified_import_key(out, &entry.key);
        encode_list_len(out, entry.certificate_import_table.len());
        for key in &entry.certificate_import_table {
            encode_verified_import_key(out, key);
        }
        out.extend(entry.decoded_name_table_hash);
        out.extend(entry.decl_index_table_hash);
        out.extend(entry.generated_decl_table_hash);
    }
}

fn encode_direct_imports_to(out: &mut Vec<u8>, imports: &MachineImportCertificateContext) {
    encode_string(out, "npa.machine-api.session-direct-imports.v1");
    encode_list_len(out, imports.direct_import_entries().len());
    for entry in imports.direct_import_entries() {
        encode_verified_import_key(out, &entry.key);
        out.extend(entry.export_signature_summary_hash);
        out.extend(entry.certified_env_decl_hashes_summary_hash);
        out.extend(entry.axiom_report_hash);
    }
}

fn encode_checked_current_to(out: &mut Vec<u8>, current: &MachineCheckedCurrentDeclContext) {
    encode_string(out, "npa.machine-api.session-checked-current.v1");
    encode_list_len(out, current.decl_index_table().len());
    for entry in current.decl_index_table() {
        out.extend(&entry.package_bytes);
    }
}

fn encode_machine_api_options_to(
    out: &mut Vec<u8>,
    options: &MachineApiOptions,
    machine_tactic_options: &MachineTacticOptions,
    resolved_eq_family: Option<&ResolvedEqFamily>,
    resolved_nat_family: Option<&ResolvedNatFamily>,
    simp_registry_hash: &Hash,
) {
    encode_string(out, "npa.machine-api.machine-api-options.v1");
    out.extend(kernel_check_profile_hash(options.kernel_check_profile));
    encode_list_len(out, options.allow_axioms.len());
    for axiom in &options.allow_axioms {
        out.extend(encode_machine_axiom_ref_wire(axiom));
    }
    out.extend(machine_tactic_options_canonical_bytes(
        machine_tactic_options,
    ));
    out.extend(resolved_family_options_canonical_bytes(
        resolved_eq_family,
        resolved_nat_family,
    ));
    out.extend(simp_registry_hash);
}

fn encode_verified_import_key(out: &mut Vec<u8>, key: &VerifiedImportKey) {
    encode_name(out, &key.module);
    out.extend(key.export_hash);
    out.extend(key.certificate_hash);
}

fn request_error(error: MachineApiRequestError) -> Box<MachineSessionCreateError> {
    let message = format!(
        "request validation failed at {}: {:?}",
        json_path_display(&error.path),
        error.reason
    );
    semantic_error(
        error.kind,
        MachineApiDiagnosticPhase::RequestValidation,
        message,
    )
}

fn semantic_error(
    kind: MachineApiErrorKind,
    phase: MachineApiDiagnosticPhase,
    message: impl Into<String>,
) -> Box<MachineSessionCreateError> {
    let message = message.into();
    boxed_error(MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id: None,
        tactic_kind: None,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message: message.clone(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::InvalidMachineProofState,
            message,
        )),
    })
}

fn frontend_error(
    diagnostic: npa_frontend::MachineDiagnostic,
    phase: MachineApiDiagnosticPhase,
) -> Box<MachineSessionCreateError> {
    let kind = map_frontend_diagnostic_kind(&diagnostic);
    let (expected_hash, actual_hash) = if kind == MachineApiErrorKind::TypeMismatch {
        let payload = diagnostic.payload.as_deref();
        (
            payload.and_then(|payload| payload.expected_hash),
            payload.and_then(|payload| payload.actual_hash),
        )
    } else {
        (None, None)
    };
    let source_message = diagnostic.message.clone();
    boxed_error(MachineApiDiagnosticProjection {
        kind,
        phase,
        retryable: false,
        goal_id: None,
        tactic_kind: None,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash,
        actual_hash,
        source_message,
        upstream: MachineApiUpstreamDiagnostic::Frontend(diagnostic),
    })
}

fn machine_term_check_error(message: impl Into<String>) -> Box<MachineSessionCreateError> {
    let message = message.into();
    boxed_error(MachineApiDiagnosticProjection {
        kind: MachineApiErrorKind::MachineTermElaborationError,
        phase: MachineApiDiagnosticPhase::MachineTermCheck,
        retryable: false,
        goal_id: None,
        tactic_kind: None,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message: message.clone(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::MachineTermElaborationError,
            message,
        )),
    })
}

fn option_semantic_error(diagnostic: MachineTacticDiagnostic) -> Box<MachineSessionCreateError> {
    let source_message = diagnostic.message.to_string();
    let primary_name = diagnostic
        .primary_name
        .as_deref()
        .filter(|name| name.is_canonical())
        .cloned();
    boxed_error(MachineApiDiagnosticProjection {
        kind: MachineApiErrorKind::InvalidMachineApiOptions,
        phase: MachineApiDiagnosticPhase::SessionCreate,
        retryable: false,
        goal_id: None,
        tactic_kind: None,
        primary_name,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message,
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(diagnostic),
    })
}

fn machine_tactic_import_error(
    diagnostic: MachineTacticDiagnostic,
    kind: MachineApiErrorKind,
) -> Box<MachineSessionCreateError> {
    let source_message = diagnostic.message.to_string();
    boxed_error(MachineApiDiagnosticProjection {
        kind,
        phase: MachineApiDiagnosticPhase::SessionCreate,
        retryable: false,
        goal_id: None,
        tactic_kind: None,
        primary_name: None,
        primary_axiom_ref: None,
        expected_hash: None,
        actual_hash: None,
        source_message,
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(diagnostic),
    })
}

fn disallowed_axiom_error(axiom: MachineAxiomRefWire) -> Box<MachineSessionCreateError> {
    let name = axiom_ref_name(&axiom).clone();
    let message = format!("axiom {} is not allowed in this session", name.as_dotted());
    boxed_error(MachineApiDiagnosticProjection {
        kind: MachineApiErrorKind::DisallowedAxiom,
        phase: MachineApiDiagnosticPhase::SessionCreate,
        retryable: false,
        goal_id: None,
        tactic_kind: None,
        primary_name: Some(name),
        primary_axiom_ref: Some(axiom),
        expected_hash: None,
        actual_hash: None,
        source_message: message.clone(),
        upstream: MachineApiUpstreamDiagnostic::MachineTactic(MachineTacticDiagnostic::new(
            MachineTacticDiagnosticKind::InvalidMachineProofState,
            message,
        )),
    })
}

fn boxed_error(diagnostic: MachineApiDiagnosticProjection) -> Box<MachineSessionCreateError> {
    let error = MachineApiErrorWire::from_projection(&diagnostic)
        .expect("session create diagnostics must satisfy machine API wire invariants");
    Box::new(MachineSessionCreateError { diagnostic, error })
}

fn callable_build_error(
    err: MachineSurfaceCallableInterfaceBuildError,
) -> Box<MachineSessionCreateError> {
    let kind = match err {
        MachineSurfaceCallableInterfaceBuildError::ImportedCallable { .. }
        | MachineSurfaceCallableInterfaceBuildError::DuplicateImportedCallable { .. } => {
            MachineApiErrorKind::InvalidVerifiedImport
        }
        MachineSurfaceCallableInterfaceBuildError::CheckedCurrentCallable { .. }
        | MachineSurfaceCallableInterfaceBuildError::DuplicateCheckedCurrentCallable { .. } => {
            MachineApiErrorKind::InvalidCheckedCurrentDecl
        }
    };
    semantic_error(
        kind,
        MachineApiDiagnosticPhase::SessionCreate,
        format!("callable interface table construction failed: {err:?}"),
    )
}

fn snapshot_store_error(err: MachineSnapshotStoreError) -> Box<MachineSessionCreateError> {
    semantic_error(
        MachineApiErrorKind::InvalidMachineProofState,
        MachineApiDiagnosticPhase::SessionCreate,
        format!("initial snapshot store failed: {err:?}"),
    )
}

fn invalid_current_name(name: &Name, reason: &'static str) -> Box<MachineSessionCreateError> {
    semantic_error(
        MachineApiErrorKind::InvalidCheckedCurrentDecl,
        MachineApiDiagnosticPhase::SessionCreate,
        format!("{reason}: {}", name.as_dotted()),
    )
}

fn invalid_options(message: impl Into<String>) -> Box<MachineSessionCreateError> {
    semantic_error(
        MachineApiErrorKind::InvalidMachineApiOptions,
        MachineApiDiagnosticPhase::SessionCreate,
        message,
    )
}

fn invalid_option_head(name: &Name, message: impl Into<String>) -> Box<MachineSessionCreateError> {
    let mut diagnostic =
        MachineTacticDiagnostic::new(MachineTacticDiagnosticKind::InvalidTacticOption, message);
    diagnostic.primary_name = Some(Box::new(name.clone()));
    option_semantic_error(diagnostic)
}

fn invalid_machine_state(message: impl Into<String>) -> Box<MachineSessionCreateError> {
    semantic_error(
        MachineApiErrorKind::InvalidMachineProofState,
        MachineApiDiagnosticPhase::SessionCreate,
        message,
    )
}

fn direct_public_export_names(
    imports: &MachineImportCertificateContext,
) -> Result<BTreeSet<Name>, Box<MachineSessionCreateError>> {
    let mut names = BTreeSet::new();
    for import in imports.direct_import_entries() {
        for export in &import.export_block {
            let name = export_name(import, export)?;
            if !names.insert(name.clone()) {
                return Err(semantic_error(
                    MachineApiErrorKind::InvalidVerifiedImport,
                    MachineApiDiagnosticPhase::SessionCreate,
                    format!(
                        "duplicate direct import public export name {}",
                        name.as_dotted()
                    ),
                ));
            }
        }
    }
    Ok(names)
}

fn direct_export_by_name_hash<'a>(
    imports: &'a MachineImportCertificateContext,
    name: &Name,
    decl_interface_hash: &Hash,
) -> Result<Option<(&'a VerifiedModuleContextEntry, &'a ExportEntry)>, Box<MachineSessionCreateError>>
{
    let mut matches = Vec::new();
    for entry in imports.direct_import_entries() {
        for export in &entry.export_block {
            if export.decl_interface_hash == *decl_interface_hash
                && export_name(entry, export)? == *name
            {
                matches.push((entry, export));
            }
        }
    }
    match matches.as_slice() {
        [] => Ok(None),
        [(entry, export)] => Ok(Some((*entry, *export))),
        _ => Err(invalid_machine_state(format!(
            "root theorem type constant {} is ambiguous across direct imports",
            name.as_dotted()
        ))),
    }
}

fn export_name(
    import: &VerifiedModuleContextEntry,
    export: &ExportEntry,
) -> Result<Name, Box<MachineSessionCreateError>> {
    import
        .decoded_name_table
        .get(export.name)
        .cloned()
        .ok_or_else(|| {
            semantic_error(
                MachineApiErrorKind::InvalidVerifiedImport,
                MachineApiDiagnosticPhase::SessionCreate,
                format!(
                    "import {} export references a missing name table entry",
                    import.key.module.as_dotted()
                ),
            )
        })
}

fn imported_export_view(
    import: &VerifiedModuleContextEntry,
    export: &ExportEntry,
    name: &Name,
) -> Result<MachineGlobalRefView, Box<MachineSessionCreateError>> {
    if let Some(generated) = import.generated_decl_table.iter().find(|generated| {
        generated.export.name == export.name
            && generated.export.decl_interface_hash == export.decl_interface_hash
    }) {
        let parent = import
            .decl_index_table
            .get(generated.parent_decl_index)
            .ok_or_else(|| {
                semantic_error(
                    MachineApiErrorKind::InvalidVerifiedImport,
                    MachineApiDiagnosticPhase::SessionCreate,
                    format!(
                        "import {} generated export has missing parent declaration",
                        import.key.module.as_dotted()
                    ),
                )
            })?;
        return Ok(MachineGlobalRefView::LocalGenerated {
            module: import.key.module.clone(),
            export_hash: Some(import.key.export_hash),
            parent_name: parent.name.clone(),
            name: name.clone(),
            parent_decl_interface_hash: parent.hashes.decl_interface_hash,
            decl_interface_hash: export.decl_interface_hash,
            public_export: true,
            tactic_head_visible: true,
        });
    }
    Ok(MachineGlobalRefView::Imported {
        module: import.key.module.clone(),
        name: name.clone(),
        export_hash: import.key.export_hash,
        decl_interface_hash: export.decl_interface_hash,
        public_export: true,
        tactic_head_visible: true,
    })
}

fn parse_module_name_option(
    object: &ValidatedObject<'_, '_>,
    path: &JsonPath,
    field: &'static str,
) -> Result<Name, MachineApiRequestError> {
    parse_module_name_wire(required_string(object, field)).map_err(|_| {
        grammar_error(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.field(field),
            field,
            JsonValueKind::String,
        )
    })
}

fn parse_fully_qualified_name_option(
    object: &ValidatedObject<'_, '_>,
    path: &JsonPath,
    field: &'static str,
) -> Result<Name, MachineApiRequestError> {
    parse_fully_qualified_name_wire(required_string(object, field)).map_err(|_| {
        grammar_error(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.field(field),
            field,
            JsonValueKind::String,
        )
    })
}

fn parse_renderable_name_option(
    object: &ValidatedObject<'_, '_>,
    path: &JsonPath,
    field: &'static str,
) -> Result<Name, MachineApiRequestError> {
    parse_machine_surface_renderable_name_wire(required_string(object, field)).map_err(|_| {
        grammar_error(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.field(field),
            field,
            JsonValueKind::String,
        )
    })
}

fn parse_hash_field(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
    error_kind: MachineApiErrorKind,
) -> Result<Hash, MachineApiRequestError> {
    HashString::parse(required_string(object, field))
        .map(HashString::digest)
        .map_err(|_| grammar_error(error_kind, path.field(field), field, JsonValueKind::String))
}

fn parse_u64_field(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
) -> Result<u64, MachineApiRequestError> {
    parse_strict_u64_token(
        object
            .field(field)
            .and_then(JsonValue::number_raw)
            .expect("schema checked unsigned integer field"),
        u64::MAX,
    )
    .map_err(|error| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidSessionRequest,
            JsonPath::root().field(field),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: object
                    .field(field)
                    .and_then(JsonValue::number_raw)
                    .unwrap_or_default()
                    .to_owned(),
                error,
            },
        )
    })
}

fn parse_nonzero_u64_field(
    object: &ValidatedObject<'_, '_>,
    field: &'static str,
    path: &JsonPath,
) -> Result<u64, MachineApiRequestError> {
    let raw = object
        .field(field)
        .and_then(JsonValue::number_raw)
        .expect("schema checked unsigned integer field");
    let value = parse_strict_u64_token(raw, u64::MAX).map_err(|error| {
        MachineApiRequestError::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.clone(),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: raw.to_owned(),
                error,
            },
        )
    })?;
    if value == 0 {
        return Err(MachineApiRequestError::new(
            MachineApiErrorKind::InvalidMachineApiOptions,
            path.clone(),
            MachineApiRequestErrorReason::InvalidUnsignedInteger {
                field,
                raw: raw.to_owned(),
                error: StrictUnsignedIntegerError::InvalidGrammar,
            },
        ));
    }
    Ok(value)
}

fn required_string<'a>(object: &'a ValidatedObject<'_, '_>, field: &str) -> &'a str {
    object
        .field(field)
        .and_then(JsonValue::string_value)
        .expect("schema checked string field")
}

fn decode_hex_bytes(
    value: &str,
    error_kind: MachineApiErrorKind,
    path: JsonPath,
    field: &'static str,
) -> Result<Vec<u8>, MachineApiRequestError> {
    let bytes = value.as_bytes();
    if !bytes.len().is_multiple_of(2) {
        return Err(grammar_error(
            error_kind,
            path,
            field,
            JsonValueKind::String,
        ));
    }
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for chunk in bytes.chunks_exact(2) {
        let high = lowercase_hex_value(chunk[0])
            .ok_or_else(|| grammar_error(error_kind, path.clone(), field, JsonValueKind::String))?;
        let low = lowercase_hex_value(chunk[1])
            .ok_or_else(|| grammar_error(error_kind, path.clone(), field, JsonValueKind::String))?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn lowercase_hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn grammar_error(
    kind: MachineApiErrorKind,
    path: JsonPath,
    field: &'static str,
    actual: JsonValueKind,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        kind,
        path,
        MachineApiRequestErrorReason::TypeMismatch {
            field,
            expected: JsonFieldType::String,
            actual,
        },
    )
}

fn sort_dedup_axiom_refs(entries: &mut Vec<MachineAxiomRefWire>) {
    entries.sort_by_key(encode_machine_axiom_ref_wire);
    entries.dedup_by(|lhs, rhs| {
        encode_machine_axiom_ref_wire(lhs) == encode_machine_axiom_ref_wire(rhs)
    });
}

fn sort_dedup_simp_rules(entries: &mut Vec<SimpRuleRef>) {
    entries.sort_by_key(encode_simp_rule_ref);
    entries.dedup_by(|lhs, rhs| encode_simp_rule_ref(lhs) == encode_simp_rule_ref(rhs));
}

fn encode_simp_rule_ref(rule: &SimpRuleRef) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.machine-api.simp-rule-ref.v1");
    encode_name(&mut out, &rule.name);
    out.extend(rule.decl_interface_hash);
    out.push(match rule.direction {
        RewriteDirection::Forward => 0x00,
        RewriteDirection::Backward => 0x01,
    });
    out
}

fn axiom_ref_name(axiom: &MachineAxiomRefWire) -> &Name {
    match axiom {
        MachineAxiomRefWire::Imported { name, .. }
        | MachineAxiomRefWire::CurrentModule { name, .. }
        | MachineAxiomRefWire::Builtin { name, .. } => name,
    }
}

fn has_strict_module_prefix(module: &Name, name: &Name) -> bool {
    name.0.starts_with(&module.0) && name.0.len() > module.0.len()
}

fn kernel_check_profile_hash(profile: KernelCheckProfileId) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "core-spec-v0.1");
    encode_string(&mut out, "npa-kernel.core.v0.1");
    encode_string(&mut out, "beta-delta-iota-zeta.v0.1");
    encode_string(&mut out, "levels-imax-v0.1");
    let builtin_profile_id = match profile {
        KernelCheckProfileId::BuiltinNone => "builtin-none-v0.1",
        KernelCheckProfileId::BuiltinNatEqRec => "builtin-nat-eq-rec-v0.1",
    };
    encode_string(&mut out, builtin_profile_id);
    hash_with_domain("npa.machine-tactic.kernel-check-profile.v1", &out)
}

fn hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain.as_bytes());
    hasher.update([0]);
    hasher.update(payload);
    hasher.finalize().into()
}

fn sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_list_len(out: &mut Vec<u8>, len: usize) {
    encode_uvar(out, len as u64);
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn fresh_session_id() -> SessionId {
    let local_id = NEXT_SESSION_LOCAL_ID.fetch_add(1, Ordering::Relaxed);
    SessionId::new_unchecked(format!("msess_{local_id}"))
}

#[cfg(test)]
fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + value - 10),
        _ => unreachable!("hex nybble is in range"),
    }
}

fn json_path_display(path: &JsonPath) -> String {
    if path.elements.is_empty() {
        return "$".to_owned();
    }
    let mut out = "$".to_owned();
    for element in &path.elements {
        match element {
            crate::JsonPathElement::Field(field) => {
                out.push('.');
                out.push_str(field);
            }
            crate::JsonPathElement::Index(index) => {
                out.push('[');
                out.push_str(&index.to_string());
                out.push(']');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::current::{
        encode_checked_current_decl_package_for_test, project_checked_current_decl_context,
    };
    use crate::format_hash_string;
    use npa_cert::{
        build_module_cert, encode_module_cert, verify_module_cert, CoreModule, VerifierSession,
    };
    use npa_kernel::{ConstructorDecl, InductiveDecl, Level, RecursorDecl, Reducibility};

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn default_options_json(allow_axioms: &str) -> String {
        format!(
            r#"{{
              "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
              "allow_axioms": {allow_axioms},
              "tactic_options": {{
                "simp_rules": [],
                "eq_family": null,
                "nat_family": null,
                "max_simp_rewrite_steps": 100,
                "max_open_goals": 32,
                "max_metas": 64
              }}
            }}"#
        )
    }

    fn minimal_session_json(theorem_type: &str) -> String {
        minimal_session_json_with_options(theorem_type, &default_options_json("[]"))
    }

    fn minimal_session_json_with_options(theorem_type: &str, options: &str) -> String {
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"{theorem_type}"}}
              }},
              "import_closure":[],
              "imports":[],
              "checked_current_decls":[],
              "options":{options}
            }}"#,
        )
    }

    fn current_nat() -> Expr {
        Expr::konst("Scratch.Nat", Vec::new())
    }

    fn current_nat_zero() -> Expr {
        Expr::konst("Scratch.Nat.zero", Vec::new())
    }

    fn current_nat_succ(arg: Expr) -> Expr {
        Expr::app(Expr::konst("Scratch.Nat.succ", Vec::new()), arg)
    }

    fn current_nat_rec_type(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", current_nat(), Expr::sort(level.clone()));
        let z_ty = Expr::app(Expr::bvar(0), current_nat_zero());
        let s_ty = Expr::pi(
            "n",
            current_nat(),
            Expr::pi(
                "ih",
                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                Expr::app(Expr::bvar(3), current_nat_succ(Expr::bvar(1))),
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
                    Expr::pi("n", current_nat(), Expr::app(Expr::bvar(3), Expr::bvar(0))),
                ),
            ),
        )
    }

    fn current_nat_decl() -> Decl {
        let nat_sort = Level::succ(Level::zero());
        Decl::Inductive {
            name: "Scratch.Nat".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::sort(nat_sort.clone()),
            data: Box::new(InductiveDecl::new(
                "Scratch.Nat",
                Vec::new(),
                Vec::new(),
                Vec::new(),
                nat_sort,
                vec![
                    ConstructorDecl::new("Scratch.Nat.zero", current_nat()),
                    ConstructorDecl::new(
                        "Scratch.Nat.succ",
                        Expr::pi("_", current_nat(), current_nat()),
                    ),
                ],
                Some(RecursorDecl::new(
                    "Scratch.Nat.rec",
                    vec!["u".to_owned()],
                    current_nat_rec_type(Level::param("u")),
                )),
            )),
        }
    }

    #[test]
    fn creates_empty_machine_session_with_stored_initial_snapshot() {
        let first = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;
        let second = create_machine_session(&minimal_session_json("Prop"))
            .unwrap()
            .session;

        assert_eq!(first.session_root_hash, second.session_root_hash);
        assert_ne!(first.session_id, second.session_id);
        assert_eq!(
            first.initial_snapshot.state_fingerprint,
            second.initial_snapshot.state_fingerprint
        );
        assert!(first.session_id.as_str().starts_with("msess_"));
        assert_eq!(first.initial_snapshot.session_id, first.session_id);
        assert_eq!(
            first.initial_snapshot.open_goals,
            vec![npa_tactic::GoalId(0)]
        );
        assert_eq!(first.initial_snapshot.goals[0].target.machine, "Prop");
        assert_eq!(first.snapshots.len(), 1);
    }

    #[test]
    fn rejects_builtin_axiom_allowlist_with_builtin_none_profile() {
        let eq_rec_hash =
            format_hash_string(&builtin_decl_interface_hash(&Name::from_dotted("Eq.rec")).unwrap());
        let options = format!(
            r#"{{
              "kernel_check_profile":"npa.kernel.v0.1.builtin-none",
              "allow_axioms": [{{
                "kind":"builtin",
                "name":"Eq.rec",
                "decl_interface_hash":"{eq_rec_hash}"
              }}],
              "tactic_options": {{
                "simp_rules": [],
                "eq_family": null,
                "nat_family": null,
                "max_simp_rewrite_steps": 100,
                "max_open_goals": 32,
                "max_metas": 64
              }}
            }}"#
        );

        let err = create_machine_session(&minimal_session_json_with_options("Prop", &options))
            .unwrap_err();

        assert_eq!(
            err.error.kind,
            MachineApiErrorKind::InvalidMachineApiOptions
        );
        assert!(err
            .diagnostic
            .source_message
            .contains("not allowed by kernel_check_profile"));
    }

    #[test]
    fn checked_current_session_root_projection_uses_package_bytes_only() {
        let root_module = Name::from_dotted("Scratch");
        let current_bytes =
            encode_checked_current_decl_package_for_test(&root_module, 0, id_decl());
        let current_context = project_checked_current_decl_context(
            &root_module,
            1,
            &MachineImportCertificateContext::empty(),
            &[CheckedCurrentDeclPackageInput {
                bytes: &current_bytes,
            }],
        )
        .unwrap();
        let mut actual = Vec::new();
        encode_checked_current_to(&mut actual, &current_context);

        let mut expected = Vec::new();
        encode_string(&mut expected, "npa.machine-api.session-checked-current.v1");
        encode_list_len(&mut expected, 1);
        expected.extend(&current_bytes);

        assert_eq!(actual, expected);
    }

    #[test]
    fn machine_api_options_projection_inlines_machine_tactic_bytes() {
        let machine_tactic_options = MachineTacticOptions {
            simp_rules: Vec::new(),
            max_simp_rewrite_steps: 100,
            max_open_goals: 32,
            max_metas: 64,
            eq_family: None,
            nat_family: None,
        };
        let options = MachineApiOptions {
            kernel_check_profile: KernelCheckProfileId::BuiltinNatEqRec,
            allow_axioms: Vec::new(),
            tactic_options: tactic_options_request_from_machine_tactic(&machine_tactic_options)
                .unwrap(),
        };
        let simp_registry_hash = [0x55; 32];
        let mut actual = Vec::new();
        encode_machine_api_options_to(
            &mut actual,
            &options,
            &machine_tactic_options,
            None,
            None,
            &simp_registry_hash,
        );

        let mut expected = Vec::new();
        encode_string(&mut expected, "npa.machine-api.machine-api-options.v1");
        expected.extend(kernel_check_profile_hash(options.kernel_check_profile));
        encode_list_len(&mut expected, 0);
        expected.extend(machine_tactic_options_canonical_bytes(
            &machine_tactic_options,
        ));
        expected.extend(resolved_family_options_canonical_bytes(None, None));
        expected.extend(simp_registry_hash);

        assert_eq!(actual, expected);
    }

    #[test]
    fn kernel_check_profile_hash_distinguishes_builtin_profiles() {
        assert_ne!(
            kernel_check_profile_hash(KernelCheckProfileId::BuiltinNone),
            kernel_check_profile_hash(KernelCheckProfileId::BuiltinNatEqRec)
        );
    }

    #[test]
    fn rejects_current_generated_nat_family_option_heads() {
        let root_module = Name::from_dotted("Scratch");
        let current_bytes =
            encode_checked_current_decl_package_for_test(&root_module, 0, current_nat_decl());
        let current_context = project_checked_current_decl_context(
            &root_module,
            1,
            &MachineImportCertificateContext::empty(),
            &[CheckedCurrentDeclPackageInput {
                bytes: &current_bytes,
            }],
        )
        .unwrap();
        let nat_hash = format_hash_string(
            &current_context.decl_index_table()[0]
                .signature
                .decl_interface_hash,
        );
        let current_hex = hex_bytes(&current_bytes);
        let body = format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":1,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"Prop"}}
              }},
              "import_closure":[],
              "imports":[],
              "checked_current_decls":[{{
                "encoding":"npa.machine-api.checked-current-decl-package.canonical.v5.hex",
                "bytes":"{current_hex}"
              }}],
              "options":{{
                "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
                "allow_axioms": [],
                "tactic_options": {{
                  "simp_rules": [],
                  "eq_family": null,
                  "nat_family": {{
                    "nat_name":"Scratch.Nat",
                    "nat_interface_hash":"{nat_hash}",
                    "zero_name":"Scratch.Nat.zero",
                    "zero_interface_hash":"{nat_hash}",
                    "succ_name":"Scratch.Nat.succ",
                    "succ_interface_hash":"{nat_hash}",
                    "rec_name":"Scratch.Nat.rec",
                    "rec_interface_hash":"{nat_hash}"
                  }},
                  "max_simp_rewrite_steps": 100,
                  "max_open_goals": 32,
                  "max_metas": 64
                }}
              }}
            }}"#
        );

        let err = create_machine_session(&body).unwrap_err();

        assert_eq!(
            err.error.kind,
            MachineApiErrorKind::InvalidMachineApiOptions
        );
        assert_eq!(
            err.error.primary_name,
            Some(Name::from_dotted("Scratch.Nat.zero"))
        );
        assert!(err
            .diagnostic
            .source_message
            .contains("current generated declaration"));
    }

    #[test]
    fn rejects_checked_current_wire_shape_with_request_phase() {
        let body = r#"{
          "protocol_version":"npa.machine-api.v1",
          "root":{
            "module":"Scratch",
            "theorem_name":"Scratch.t",
            "source_index":0,
            "universe_params":[],
            "theorem_type":{"format":"machine_surface_v1","source":"Prop"}
          },
          "import_closure":[],
          "imports":[],
          "checked_current_decls":[null],
          "options":{
            "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
            "allow_axioms": [],
            "tactic_options": {
              "simp_rules": [],
              "eq_family": null,
              "nat_family": null,
              "max_simp_rewrite_steps": 100,
              "max_open_goals": 32,
              "max_metas": 64
            }
          }
        }"#;

        let err = create_machine_session(body).unwrap_err();

        assert_eq!(
            err.error.kind,
            MachineApiErrorKind::InvalidCheckedCurrentDecl
        );
        assert_eq!(
            err.error.phase,
            MachineApiDiagnosticPhase::RequestValidation
        );
    }

    #[test]
    fn enforces_import_axiom_allowlist() {
        let module = CoreModule {
            name: Name::from_dotted("A"),
            declarations: vec![Decl::Axiom {
                name: "A.T".to_owned(),
                universe_params: Vec::new(),
                ty: prop(),
            }],
        };
        let cert = build_module_cert(module, &[]).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut session = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy.allowlisted_axioms.insert(Name::from_dotted("A.T"));
        let verified = verify_module_cert(&bytes, &mut session, &policy).unwrap();
        let export_hash = format_hash_string(&verified.export_hash());
        let certificate_hash = format_hash_string(&verified.certificate_hash());
        let hex = hex_bytes(&bytes);
        let without_allow =
            imported_axiom_session_json(&export_hash, &certificate_hash, &hex, "[]");

        let err = create_machine_session(&without_allow).unwrap_err();

        assert_eq!(err.error.kind, MachineApiErrorKind::DisallowedAxiom);
        assert_eq!(err.error.phase, MachineApiDiagnosticPhase::SessionCreate);
        assert_eq!(err.error.primary_name, Some(Name::from_dotted("A.T")));

        let allow = format!(
            r#"[{{
              "kind":"imported",
              "module":"A",
              "name":"A.T",
              "export_hash":"{export_hash}",
              "decl_interface_hash":"{}"
            }}]"#,
            format_hash_string(&verified.declarations()[0].hashes.decl_interface_hash)
        );
        let with_allow = imported_axiom_session_json(&export_hash, &certificate_hash, &hex, &allow);
        let ok = create_machine_session(&with_allow).unwrap().session;

        assert_eq!(ok.initial_snapshot.goals[0].target.machine, "A.T");
    }

    fn imported_axiom_session_json(
        export_hash: &str,
        certificate_hash: &str,
        cert_hex: &str,
        allow_axioms: &str,
    ) -> String {
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"A.T"}}
              }},
              "import_closure":[{{
                "module":"A",
                "expected_export_hash":"{export_hash}",
                "expected_certificate_hash":"{certificate_hash}",
                "certificate":{{
                  "encoding":"npa.certificate.canonical.v0.1.hex",
                  "bytes":"{cert_hex}"
                }}
              }}],
              "imports":[{{
                "module":"A",
                "expected_export_hash":"{export_hash}",
                "expected_certificate_hash":"{certificate_hash}"
              }}],
              "checked_current_decls":[],
              "options":{}
            }}"#,
            default_options_json(allow_axioms)
        )
    }

    fn hex_bytes(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            out.push(hex_digit(byte >> 4));
            out.push(hex_digit(byte & 0x0f));
        }
        out
    }

    #[allow(dead_code)]
    fn id_value() -> Expr {
        Expr::lam("A", type0(), Expr::lam("x", Expr::bvar(0), Expr::bvar(0)))
    }

    #[allow(dead_code)]
    fn id_decl() -> Decl {
        Decl::Def {
            name: "Scratch.id".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("A", type0(), Expr::pi("x", Expr::bvar(0), Expr::bvar(1))),
            value: id_value(),
            reducibility: Reducibility::Reducible,
        }
    }
}
