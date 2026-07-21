//! Prepare one declaration-level mathlib promotion plan.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read,
    path::Path,
};

use npa_api::{PackageArtifactReferenceSummaryMode, PackageArtifactVerifiedModule};
use npa_cert::{
    declaration_dependency_closure, resolve_verified_declaration_export, DeclarationClosure,
    DeclarationClosureKind, DeclarationClosureLimits, GlobalDeclarationIdentity, Name,
    ValidatedSourceDeclarationFamilies, ValidatedSourceDeclarationFamily,
    DECLARATION_CLOSURE_LIMITS_V1,
};
use npa_frontend::{
    bind_human_source_interface_to_verified_import, collect_human_source_declaration_families,
    extract_human_declaration_source, parse_human_module_with_source_interfaces,
    resolve_human_module_with_source_interfaces, FileId, HumanCompileOptions,
    HumanDeclarationFamilyMemberKind, HumanDeclarationSelection, HumanGlobalIdentity,
    HumanGlobalMapping, HumanGlobalMappingRow, HumanImportedSourceInterface,
    HumanSelectedDeclaration, HumanSourceDeclarationFamilies, Span, VerifiedImport,
};
use npa_package::{
    package_file_hash, parse_declaration_promotion_request_json,
    promotion_plan_v2_dependency_edge_hash, DeclarationPromotionRequest,
    DeclarationPromotionRootKind, MathlibPromotionPlanV2, PackageArtifactOrigin, PackageHash,
    PackageLockEntryOrigin, PackagePath, PromotionGovernanceV2, PromotionLifecycle,
    PromotionOriginEntryV2, PromotionPackageSnapshot, PromotionPlanEndpoint,
    PromotionPlanV2Declaration, PromotionPlanV2DependencyMapping, PromotionPlanV2EquivalentSource,
    PromotionPlanV2Identity, PromotionPlanV2Root, PromotionSelectionV2, PromotionSourceModule,
    PromotionSourceSpan, PromotionTargetSnapshotV2, MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA,
    MATHLIB_PROMOTION_PLAN_V2_SCHEMA, MATHLIB_PROMOTION_REGISTRY_PATH, PACKAGE_PUBLISH_PLAN_PATH,
    PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

use crate::{
    args::{
        PackageChecker, PackageCommonOptions, PackagePreparePromotionOptions,
        PackageValidatePromotionOriginRegistryOptions,
    },
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::render_package_root,
    governance_writer::{
        confined_governance_path, write_governance_artifact, GovernanceOutputPolicy,
    },
    package_api::v1::verify_certs_full,
    package_artifacts::{load_package_audit_snapshot, LoadedPackageAuditSnapshot},
    package_build::fallback_imported_source_interface,
    package_promotion_registry::{
        parse_promotion_origin_registry_versioned, promotion_plan_generated_read_mode,
        run_package_validate_promotion_origin_registry, validate_checked_generated,
        ParsedPromotionOriginRegistry,
    },
    package_verify::run_package_verify_certs,
};

const COMMAND: &str = "package prepare-promotion";
const CATALOG_POLICY_PATH: &str = "docs/catalog-policy.md";
const NAMESPACE_POLICY_PATH: &str = "docs/namespace-policy.md";
const SUPPORTED_PRODUCER_PROFILE: &str = "human-surface-explicit-term";
const MAX_EXTRACTION_SOURCE_BYTES: u64 = 256 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationSourceExtractionError {
    Unsupported,
    SourceBytesLimitExceeded { actual: u64 },
}

/// Validate declaration-selection inputs and create or check a canonical plan v2.
pub fn run_package_prepare_declaration_promotion(
    options: PackagePreparePromotionOptions,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    if let Err(diagnostic) = validate_equivalent_origin_root_count(&options.equivalent_origin_roots)
    {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let request_arg = match options.declaration_request.as_ref() {
        Some(path) => path,
        None => {
            return failed(
                &root_display,
                "promotion_declaration_request_invalid",
                "--declaration-request",
            )
        }
    };
    let request_path = PackagePath::new(request_arg.to_string_lossy());
    let out_path = PackagePath::new(options.out.to_string_lossy());
    if request_path == out_path {
        return failed(
            &root_display,
            "promotion_declaration_request_invalid",
            out_path.as_str(),
        );
    }
    let request_bytes = match read_confined(
        &options.common.root,
        &request_path,
        "promotion_declaration_request_invalid",
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let request_source = match String::from_utf8(request_bytes.clone()) {
        Ok(source) => source,
        Err(_) => {
            return failed(
                &root_display,
                "promotion_declaration_request_invalid",
                request_path.as_str(),
            )
        }
    };
    let request = match parse_declaration_promotion_request_json(&request_source) {
        Ok(request) => request,
        Err(_) => {
            return failed(
                &root_display,
                "promotion_declaration_request_invalid",
                request_path.as_str(),
            )
        }
    };

    let source = match load_snapshot(&options.common.root) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    let baseline = match load_snapshot(&options.target_baseline_root) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    for snapshot in [&source, &baseline] {
        if let Err(diagnostic) = validate_checked_generated(snapshot) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    for root in [&options.common.root, &options.target_baseline_root] {
        if run_package_verify_certs(verify_certs_full(
            PackageCommonOptions {
                root: root.clone(),
                json: false,
            },
            PackageChecker::Reference,
        ))
        .status
            != crate::diagnostic::CommandStatus::Passed
        {
            return failed(
                &root_display,
                "promotion_declaration_certificate_invalid",
                root.to_string_lossy().as_ref(),
            );
        }
    }
    let registry_validation = run_package_validate_promotion_origin_registry(
        PackageValidatePromotionOriginRegistryOptions {
            common: PackageCommonOptions {
                root: options.target_baseline_root.clone(),
                json: false,
            },
            source_roots: Vec::new(),
            previous_registry: None,
        },
    );
    if registry_validation.status != crate::diagnostic::CommandStatus::Passed {
        return CommandResult::failed(COMMAND, root_display, registry_validation.diagnostics);
    }
    if !request_matches_snapshots(&request, &source, &baseline) {
        return failed(
            &root_display,
            "promotion_declaration_request_invalid",
            request_path.as_str(),
        );
    }
    let source_module = match source
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .find(|module| module.module == request.source_module)
    {
        Some(module) if module.producer_profile.as_deref() == Some(SUPPORTED_PRODUCER_PROFILE) => {
            module
        }
        _ => {
            return failed_with_module(
                &root_display,
                "promotion_declaration_source_extraction_unsupported",
                &request.source_module,
                request_path.as_str(),
            )
        }
    };
    let (Some(meta_path), Some(replay_path)) = (&source_module.meta, &source_module.replay) else {
        return failed_with_module(
            &root_display,
            "promotion_declaration_source_extraction_unsupported",
            &request.source_module,
            request_path.as_str(),
        );
    };
    if baseline
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .any(|module| module.module == request.target_module)
    {
        return failed_with_module(
            &root_display,
            "promotion_declaration_target_collision",
            &request.target_module,
            "npa-package.toml",
        );
    }
    for path in target_artifact_paths(&request.target_module) {
        if confined_governance_path(
            &options.target_baseline_root,
            &path,
            path.as_str(),
            "promotion_declaration_target_collision",
        )
        .ok()
        .is_none_or(|full| fs::symlink_metadata(full).is_ok())
        {
            return failed_with_module(
                &root_display,
                "promotion_declaration_target_collision",
                &request.target_module,
                path.as_str(),
            );
        }
    }

    let mut extraction_source_bytes = 0;
    let source_bytes = match read_declaration_source(
        &options.common.root,
        &source_module.source,
        &mut extraction_source_bytes,
    ) {
        Ok(bytes) => bytes,
        Err(error) => {
            return source_extraction_failure(
                &root_display,
                &request.source_module,
                &source_module.source,
                error,
            )
        }
    };
    let source_text = match String::from_utf8(source_bytes.clone()) {
        Ok(source) => source,
        Err(_) => {
            return failed(
                &root_display,
                "promotion_declaration_source_extraction_unsupported",
                source_module.source.as_str(),
            )
        }
    };
    let meta_bytes = match read_confined(
        &options.common.root,
        meta_path,
        "promotion_declaration_source_extraction_unsupported",
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let replay_bytes = match read_confined(
        &options.common.root,
        replay_path,
        "promotion_declaration_source_extraction_unsupported",
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let source_verified = match record_for(&source, &request.source_module) {
        Some(record) => &record.verified_module,
        None => {
            return failed_with_module(
                &root_display,
                "promotion_declaration_root_missing",
                &request.source_module,
                source_module.certificate.as_str(),
            )
        }
    };
    let imported_interfaces = match direct_import_interfaces(
        &options.common.root,
        &source,
        &source_module.imports,
        extraction_source_bytes,
    ) {
        Ok(interfaces) => interfaces,
        Err(error) => {
            return source_extraction_failure(
                &root_display,
                &request.source_module,
                &source_module.source,
                error,
            )
        }
    };
    let human_families = match collect_human_source_declaration_families(
        FileId(0),
        &source_text,
        &imported_interfaces,
    ) {
        Ok(families) => families,
        Err(_) => {
            return failed_with_module(
                &root_display,
                "promotion_declaration_source_extraction_unsupported",
                &request.source_module,
                source_module.source.as_str(),
            )
        }
    };
    let (families, human_members) = match reconcile_families(source_verified, &human_families) {
        Ok(value) => value,
        Err((reason, name)) => {
            return failed_with_declaration(
                &root_display,
                reason,
                &request.source_module,
                &name,
                source_module.source.as_str(),
            )
        }
    };
    let roots = match resolve_roots(&request, source_verified, &human_families) {
        Ok(roots) => roots,
        Err((reason, name)) => {
            return failed_with_declaration(
                &root_display,
                reason,
                &request.source_module,
                &name,
                request_path.as_str(),
            )
        }
    };
    let modules = source
        .snapshot
        .decoded_module_records
        .values()
        .map(|record| (record.key.module.clone(), record.verified_module.clone()))
        .collect::<BTreeMap<_, _>>();
    let (externalized, mapping_routes) = match declaration_mappings(&request, &source, &baseline) {
        Ok(value) => value,
        Err((reason, name)) => {
            return failed_with_declaration(
                &root_display,
                reason,
                &request.source_module,
                &name,
                request_path.as_str(),
            )
        }
    };
    let closure = match declaration_dependency_closure(
        &modules,
        &roots,
        &families,
        &externalized,
        DeclarationClosureLimits::default(),
    ) {
        Ok(closure) => closure,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![declaration_closure_failure_diagnostic(
                    &error,
                    &request,
                    &request_path,
                    &baseline,
                )],
            );
        }
    };
    if let Some(identity) = source_local_externalized_axiom(&closure, &mapping_routes) {
        return failed_with_declaration(
            &root_display,
            "promotion_declaration_custom_axiom_rejected",
            &identity.module,
            &identity.name,
            request_path.as_str(),
        );
    }
    let plan_roots = plan_roots(&request, &human_families);
    let declarations = match plan_declarations(&closure, &human_members) {
        Ok(rows) => rows,
        Err(name) => {
            return failed_with_declaration(
                &root_display,
                "promotion_declaration_source_family_invalid",
                &request.source_module,
                &name,
                source_module.source.as_str(),
            )
        }
    };
    let generated_exports = declarations
        .iter()
        .flat_map(|row| row.generated_exports.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let used_mappings = match used_plan_mappings(&closure, &mapping_routes, &baseline) {
        Ok(rows) => rows,
        Err(name) => {
            return failed_with_declaration(
                &root_display,
                "promotion_declaration_dependency_mapping_stale",
                &request.source_module,
                &name,
                request_path.as_str(),
            )
        }
    };
    if request.dependency_mappings.iter().any(|requested| {
        !used_mappings
            .iter()
            .any(|used| used.source == requested.source && used.target == requested.target)
    }) {
        return failed(
            &root_display,
            "promotion_declaration_request_invalid",
            request_path.as_str(),
        );
    }
    if extraction_preview(
        &request,
        &source_text,
        &imported_interfaces,
        &closure,
        &human_members,
        &externalized,
    )
    .is_err()
    {
        return failed_with_module(
            &root_display,
            "promotion_declaration_source_extraction_unsupported",
            &request.source_module,
            source_module.source.as_str(),
        );
    }

    let catalog_policy = match read_baseline(&options.target_baseline_root, CATALOG_POLICY_PATH) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let namespace_policy = match read_baseline(&options.target_baseline_root, NAMESPACE_POLICY_PATH)
    {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let export_summary = match read_baseline(
        &options.target_baseline_root,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let publish_plan = match read_baseline(&options.target_baseline_root, PACKAGE_PUBLISH_PLAN_PATH)
    {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let registry_bytes = match read_baseline(
        &options.target_baseline_root,
        MATHLIB_PROMOTION_REGISTRY_PATH,
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let registry = match std::str::from_utf8(&registry_bytes)
        .ok()
        .and_then(|source| parse_promotion_origin_registry_versioned(source).ok())
    {
        Some(registry) => registry,
        None => {
            return failed(
                &root_display,
                "promotion_declaration_dependency_mapping_stale",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
        }
    };
    if let Some(target) = request
        .dependency_mappings
        .iter()
        .map(|mapping| &mapping.target)
        .find(|target| {
            target.origin == PackageArtifactOrigin::Local
                && !registry_owns_active_target(&registry, &target.module)
        })
    {
        return failed_with_module(
            &root_display,
            "promotion_declaration_dependency_mapping_stale",
            &target.module,
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    let source_origin = PromotionSourceModule {
        module: request.source_module.clone(),
        source_file_hash: package_file_hash(&source_bytes),
        certificate_file_hash: source_module.expected_certificate_file_hash,
        certificate_hash: source_module.expected_certificate_hash,
        export_hash: source_module.expected_export_hash,
    };
    if registry_collides(&registry, &request, &closure, &source_origin) {
        return failed_with_module(
            &root_display,
            "promotion_declaration_target_collision",
            &request.target_module,
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    let dependency_edge_hash =
        match promotion_plan_v2_dependency_edge_hash(&declarations, &used_mappings) {
            Ok(hash) => hash,
            Err(_) => {
                return failed(
                    &root_display,
                    "promotion_declaration_request_invalid",
                    request_path.as_str(),
                )
            }
        };
    let equivalent_sources = match equivalent_sources(
        &options.equivalent_origin_roots,
        &request,
        &source_bytes,
        source_module,
        &closure,
        dependency_edge_hash,
    ) {
        Ok(rows) => rows,
        Err(result) => return result,
    };
    let Some((source_axiom, source_index)) = checked_hashes(&source) else {
        return failed(
            &root_display,
            "promotion_declaration_request_invalid",
            "generated",
        );
    };
    let Some((baseline_axiom, baseline_index)) = checked_hashes(&baseline) else {
        return failed(
            &root_display,
            "promotion_declaration_request_invalid",
            "generated",
        );
    };
    let source_manifest = source.snapshot.validated.manifest();
    let baseline_manifest = baseline.snapshot.validated.manifest();
    let mut plan = MathlibPromotionPlanV2 {
        schema: MATHLIB_PROMOTION_PLAN_V2_SCHEMA.to_owned(),
        promotion_id: PackageHash::new([0; 32]),
        source: PromotionPackageSnapshot {
            package: source_manifest.package.clone(),
            version: source_manifest.version.clone(),
            manifest_file_hash: source.snapshot.manifest.file_hash,
            lock_file_hash: package_file_hash(source.package_lock_json.as_bytes()),
            axiom_report_file_hash: source_axiom,
            theorem_index_file_hash: source_index,
        },
        target_baseline: PromotionTargetSnapshotV2 {
            package: baseline_manifest.package.clone(),
            version: baseline_manifest.version.clone(),
            planned_version: request.target.planned_version.clone(),
            manifest_file_hash: baseline.snapshot.manifest.file_hash,
            lock_file_hash: package_file_hash(baseline.package_lock_json.as_bytes()),
            axiom_report_file_hash: baseline_axiom,
            theorem_index_file_hash: baseline_index,
            verified_export_summary_file_hash: package_file_hash(&export_summary),
            publish_plan_file_hash: package_file_hash(&publish_plan),
            registry_file_hash: package_file_hash(&registry_bytes),
        },
        governance: PromotionGovernanceV2 {
            request_path: request_path.clone(),
            request_schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
            request_file_hash: package_file_hash(&request_bytes),
            catalog_policy_file_hash: package_file_hash(&catalog_policy),
            namespace_policy_file_hash: package_file_hash(&namespace_policy),
        },
        selection: PromotionSelectionV2 {
            source_module: request.source_module.clone(),
            target_module: request.target_module.clone(),
            source_path: source_module.source.clone(),
            source_file_hash: package_file_hash(&source_bytes),
            meta_path: meta_path.clone(),
            meta_file_hash: package_file_hash(&meta_bytes),
            replay_path: replay_path.clone(),
            replay_file_hash: package_file_hash(&replay_bytes),
            certificate_path: source_module.certificate.clone(),
            certificate_file_hash: source_module.expected_certificate_file_hash,
            certificate_hash: source_module.expected_certificate_hash,
            export_hash: source_module.expected_export_hash,
            axiom_report_hash: source_module.expected_axiom_report_hash,
            roots: plan_roots,
            materialized_declarations: declarations,
            generated_exports,
            declaration_closure_hash: PackageHash::from(closure.declaration_closure_hash),
        },
        dependency_mappings: used_mappings,
        equivalent_sources,
        requested_maturity: "verified".to_owned(),
        plan_hash: PackageHash::new([0; 32]),
        proof_evidence: false,
    };
    if plan.finalize().is_err() {
        return failed(
            &root_display,
            "promotion_declaration_request_invalid",
            request_path.as_str(),
        );
    }
    let json = match plan.canonical_json() {
        Ok(json) => json,
        Err(_) => {
            return failed(
                &root_display,
                "promotion_declaration_request_invalid",
                request_path.as_str(),
            )
        }
    };
    if options.check {
        if read_confined(
            &options.common.root,
            &out_path,
            "promotion_plan_output_conflict",
        )
        .ok()
        .as_deref()
            != Some(json.as_bytes())
        {
            return failed(
                &root_display,
                "promotion_plan_output_conflict",
                out_path.as_str(),
            );
        }
    } else if let Err(diagnostic) = write_governance_artifact(
        &options.common.root,
        &out_path,
        json.as_bytes(),
        GovernanceOutputPolicy::CreateOrIdentical,
        "promotion_plan",
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "mathlib_declaration_promotion_plan".to_owned(),
        path: out_path.as_str().to_owned(),
    });
    result
}

fn validate_equivalent_origin_root_count(
    roots: &[std::path::PathBuf],
) -> Result<(), Box<CommandDiagnostic>> {
    let maximum = DECLARATION_CLOSURE_LIMITS_V1.loaded_modules;
    if roots.len() > maximum {
        return Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::PackagePolicy,
                "promotion_declaration_closure_limit_exceeded",
            )
            .with_path("--equivalent-origin-root")
            .with_field("equivalent_sources")
            .with_expected_value(maximum.to_string())
            .with_actual_value(roots.len().to_string()),
        ));
    }
    Ok(())
}

fn load_snapshot(root: &Path) -> Result<LoadedPackageAuditSnapshot, CommandResult> {
    load_package_audit_snapshot(
        root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    )
}

fn request_matches_snapshots(
    request: &DeclarationPromotionRequest,
    source: &LoadedPackageAuditSnapshot,
    baseline: &LoadedPackageAuditSnapshot,
) -> bool {
    let source_manifest = source.snapshot.validated.manifest();
    let baseline_manifest = baseline.snapshot.validated.manifest();
    request.source.package == source_manifest.package
        && request.source.version == source_manifest.version
        && request.target.package == baseline_manifest.package
        && request.target.baseline_version == baseline_manifest.version
}

pub(crate) fn direct_import_interfaces(
    root: &Path,
    snapshot: &LoadedPackageAuditSnapshot,
    imports: &[Name],
    initial_source_bytes: u64,
) -> Result<Vec<HumanImportedSourceInterface>, DeclarationSourceExtractionError> {
    direct_import_interfaces_with_limit(
        root,
        snapshot,
        imports,
        initial_source_bytes,
        MAX_EXTRACTION_SOURCE_BYTES,
    )
}

fn direct_import_interfaces_with_limit(
    root: &Path,
    snapshot: &LoadedPackageAuditSnapshot,
    imports: &[Name],
    initial_source_bytes: u64,
    max_source_bytes: u64,
) -> Result<Vec<HumanImportedSourceInterface>, DeclarationSourceExtractionError> {
    if initial_source_bytes > max_source_bytes {
        return Err(DeclarationSourceExtractionError::SourceBytesLimitExceeded {
            actual: initial_source_bytes,
        });
    }
    let manifest = snapshot.snapshot.validated.manifest();
    let supported_modules = manifest
        .modules
        .iter()
        .enumerate()
        .filter(|(_, module)| {
            module.producer_profile.as_deref() == Some(SUPPORTED_PRODUCER_PROFILE)
        })
        .map(|(index, module)| (module.module.clone(), (index, module)))
        .collect::<BTreeMap<_, _>>();
    let reconstruction_order = import_interface_dependency_order(imports, |module| {
        supported_modules
            .get(module)
            .map(|(_, manifest_module)| manifest_module.imports.as_slice())
    })?;
    let mut cache = BTreeMap::new();
    let mut source_bytes = initial_source_bytes;
    for module in reconstruction_order {
        let record =
            record_for(snapshot, &module).ok_or(DeclarationSourceExtractionError::Unsupported)?;
        let Some((module_index, manifest_module)) = supported_modules.get(&module) else {
            cache.insert(
                module,
                fallback_imported_source_interface(&record.verified_module),
            );
            continue;
        };
        let direct_interfaces = manifest_module
            .imports
            .iter()
            .map(|dependency| {
                cache
                    .get(dependency)
                    .cloned()
                    .ok_or(DeclarationSourceExtractionError::Unsupported)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let verified_imports = manifest_module
            .imports
            .iter()
            .map(|dependency| {
                record_for(snapshot, dependency)
                    .map(|record| VerifiedImport::from(&record.verified_module))
                    .ok_or(DeclarationSourceExtractionError::Unsupported)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let source = read_declaration_source_with_limit(
            root,
            &manifest_module.source,
            &mut source_bytes,
            max_source_bytes,
        )?;
        let source = std::str::from_utf8(&source)
            .map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
        let file_id = FileId(
            u32::try_from(*module_index + 1)
                .map_err(|_| DeclarationSourceExtractionError::Unsupported)?,
        );
        let parsed = parse_human_module_with_source_interfaces(file_id, source, &direct_interfaces)
            .map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
        let resolved = resolve_human_module_with_source_interfaces(
            module.clone(),
            parsed,
            &verified_imports,
            &direct_interfaces,
            &HumanCompileOptions::default(),
        )
        .map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
        let verified_import = VerifiedImport::from(&record.verified_module);
        let source_interface = bind_human_source_interface_to_verified_import(
            resolved.state.source_interfaces.current,
            &verified_import,
            Span::empty(file_id),
        )
        .map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
        cache.insert(
            module.clone(),
            HumanImportedSourceInterface {
                module,
                export_hash: record.verified_module.export_hash(),
                certificate_hash: Some(record.verified_module.certificate_hash()),
                source_interface,
            },
        );
    }
    imports
        .iter()
        .map(|module| {
            cache
                .get(module)
                .cloned()
                .ok_or(DeclarationSourceExtractionError::Unsupported)
        })
        .collect()
}

#[derive(Debug)]
struct ImportInterfaceDependencyFrame {
    module: Name,
    next_dependency: usize,
}

fn import_interface_dependency_order<'a>(
    roots: &[Name],
    dependencies: impl Fn(&Name) -> Option<&'a [Name]>,
) -> Result<Vec<Name>, DeclarationSourceExtractionError> {
    let mut finished = BTreeSet::new();
    let mut order = Vec::new();
    for root in roots {
        if finished.contains(root) {
            continue;
        }
        let mut visiting = BTreeSet::from([root.clone()]);
        let mut stack = vec![ImportInterfaceDependencyFrame {
            module: root.clone(),
            next_dependency: 0,
        }];
        while let Some(frame) = stack.last_mut() {
            let next_dependency = dependencies(&frame.module)
                .and_then(|imports| imports.get(frame.next_dependency))
                .cloned();
            if let Some(dependency) = next_dependency {
                frame.next_dependency += 1;
                if finished.contains(&dependency) {
                    continue;
                }
                if !visiting.insert(dependency.clone()) {
                    return Err(DeclarationSourceExtractionError::Unsupported);
                }
                stack.push(ImportInterfaceDependencyFrame {
                    module: dependency,
                    next_dependency: 0,
                });
                continue;
            }
            let completed = stack
                .pop()
                .ok_or(DeclarationSourceExtractionError::Unsupported)?;
            visiting.remove(&completed.module);
            if finished.insert(completed.module.clone()) {
                order.push(completed.module);
            }
        }
    }
    Ok(order)
}

fn record_for<'a>(
    snapshot: &'a LoadedPackageAuditSnapshot,
    module: &Name,
) -> Option<&'a PackageArtifactVerifiedModule> {
    snapshot
        .snapshot
        .decoded_module_records
        .values()
        .find(|record| &record.key.module == module)
}

pub(crate) type HumanMemberMap =
    BTreeMap<Name, (HumanDeclarationFamilyMemberKind, Span, Name, Vec<Name>)>;

pub(crate) fn reconcile_families(
    verified: &npa_cert::VerifiedModule,
    human: &HumanSourceDeclarationFamilies,
) -> Result<(ValidatedSourceDeclarationFamilies, HumanMemberMap), (&'static str, Name)> {
    let mut families = Vec::new();
    let mut members_by_name = BTreeMap::new();
    for family in &human.families {
        let owner = resolve_verified_declaration_export(verified, &family.owner).map_err(|_| {
            (
                "promotion_declaration_source_family_invalid",
                family.owner.clone(),
            )
        })?;
        if !human_cert_kind_matches(family.owner_kind, owner.identity.kind) {
            return Err((
                "promotion_declaration_source_family_invalid",
                family.owner.clone(),
            ));
        }
        let mut members = Vec::new();
        let family_names = family
            .members
            .iter()
            .map(|member| member.name.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        for member in &family.members {
            let resolved =
                resolve_verified_declaration_export(verified, &member.name).map_err(|_| {
                    (
                        "promotion_declaration_source_family_invalid",
                        member.name.clone(),
                    )
                })?;
            if !human_cert_kind_matches(member.kind, resolved.identity.kind)
                || members_by_name
                    .insert(
                        member.name.clone(),
                        (
                            member.kind,
                            family.item_span,
                            family.owner.clone(),
                            family_names.clone(),
                        ),
                    )
                    .is_some()
            {
                return Err((
                    "promotion_declaration_source_family_invalid",
                    member.name.clone(),
                ));
            }
            members.push(resolved);
        }
        families.push(ValidatedSourceDeclarationFamily {
            owner: owner.identity,
            members,
        });
    }
    for export in verified.export_block() {
        let Some(name) = verified.name_table().get(export.name) else {
            return Err((
                "promotion_declaration_source_family_invalid",
                Name::from_dotted("unknown"),
            ));
        };
        if !members_by_name.contains_key(name) {
            return Err(("promotion_declaration_source_family_invalid", name.clone()));
        }
    }
    ValidatedSourceDeclarationFamilies::new(families)
        .map(|families| (families, members_by_name))
        .map_err(|error| {
            (
                error.reason.as_str(),
                error
                    .identity
                    .map_or_else(|| Name::from_dotted("unknown"), |identity| identity.name),
            )
        })
}

fn human_cert_kind_matches(
    human: HumanDeclarationFamilyMemberKind,
    cert: DeclarationClosureKind,
) -> bool {
    matches!(
        (human, cert),
        (
            HumanDeclarationFamilyMemberKind::Theorem,
            DeclarationClosureKind::Theorem
        ) | (
            HumanDeclarationFamilyMemberKind::Definition
                | HumanDeclarationFamilyMemberKind::ClassField
                | HumanDeclarationFamilyMemberKind::Instance,
            DeclarationClosureKind::Definition
        ) | (
            HumanDeclarationFamilyMemberKind::Axiom,
            DeclarationClosureKind::Axiom
        ) | (
            HumanDeclarationFamilyMemberKind::Inductive | HumanDeclarationFamilyMemberKind::Class,
            DeclarationClosureKind::Inductive
        ) | (
            HumanDeclarationFamilyMemberKind::Constructor,
            DeclarationClosureKind::Constructor
        ) | (
            HumanDeclarationFamilyMemberKind::Recursor,
            DeclarationClosureKind::Recursor
        )
    )
}

pub(crate) fn resolve_roots(
    request: &DeclarationPromotionRequest,
    verified: &npa_cert::VerifiedModule,
    families: &HumanSourceDeclarationFamilies,
) -> Result<BTreeSet<GlobalDeclarationIdentity>, (&'static str, Name)> {
    let mut roots = BTreeSet::new();
    for root in &request.roots {
        let matches = families
            .families
            .iter()
            .filter(|family| {
                family
                    .members
                    .iter()
                    .any(|member| member.name == root.source_name)
            })
            .collect::<Vec<_>>();
        if matches.len() > 1 {
            return Err((
                "promotion_declaration_generated_owner_ambiguous",
                root.source_name.clone(),
            ));
        }
        if matches.is_empty() {
            return Err((
                "promotion_declaration_root_missing",
                root.source_name.clone(),
            ));
        }
        if request_kind(matches[0].owner_kind) != Some(root.kind) {
            return Err((
                "promotion_declaration_root_kind_mismatch",
                root.source_name.clone(),
            ));
        }
        let resolved =
            resolve_verified_declaration_export(verified, &root.source_name).map_err(|_| {
                (
                    "promotion_declaration_root_missing",
                    root.source_name.clone(),
                )
            })?;
        roots.insert(resolved.identity);
    }
    Ok(roots)
}

fn request_kind(kind: HumanDeclarationFamilyMemberKind) -> Option<DeclarationPromotionRootKind> {
    match kind {
        HumanDeclarationFamilyMemberKind::Theorem => Some(DeclarationPromotionRootKind::Theorem),
        HumanDeclarationFamilyMemberKind::Definition => {
            Some(DeclarationPromotionRootKind::Definition)
        }
        HumanDeclarationFamilyMemberKind::Inductive => {
            Some(DeclarationPromotionRootKind::Inductive)
        }
        HumanDeclarationFamilyMemberKind::Class => Some(DeclarationPromotionRootKind::Class),
        HumanDeclarationFamilyMemberKind::Instance => Some(DeclarationPromotionRootKind::Instance),
        _ => None,
    }
}

type MappingRoute = (PromotionPlanEndpoint, PromotionPlanEndpoint);
type MappingRoutes = BTreeMap<(Name, Name), MappingRoute>;
type DeclarationMappings = BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>;
type DeclarationMappingResult = Result<(DeclarationMappings, MappingRoutes), (&'static str, Name)>;

fn source_local_externalized_axiom<'a>(
    closure: &'a DeclarationClosure,
    routes: &MappingRoutes,
) -> Option<&'a GlobalDeclarationIdentity> {
    closure.externalized.iter().find_map(|(source, _)| {
        (source.kind == DeclarationClosureKind::Axiom
            && routes
                .get(&(source.module.clone(), source.name.clone()))
                .is_some_and(|(source_endpoint, _)| {
                    source_endpoint.origin == PackageArtifactOrigin::Local
                }))
        .then_some(source)
    })
}

fn declaration_closure_failure_reason(
    reason: npa_cert::DeclarationClosureErrorReason,
    identity: &GlobalDeclarationIdentity,
    request: &DeclarationPromotionRequest,
    baseline: &LoadedPackageAuditSnapshot,
) -> &'static str {
    if reason != npa_cert::DeclarationClosureErrorReason::DependencyMappingMissing {
        return reason.as_str();
    }
    if request
        .dependency_mappings
        .iter()
        .any(|row| row.source.module == identity.module)
    {
        return "promotion_declaration_dependency_mapping_stale";
    }
    if baseline
        .snapshot
        .decoded_module_records
        .values()
        .any(|record| {
            resolve_verified_declaration_export(&record.verified_module, &identity.name).is_ok_and(
                |resolved| {
                    resolved.identity.kind == identity.kind
                        && resolved.identity.decl_interface_hash == identity.decl_interface_hash
                },
            )
        })
    {
        "promotion_declaration_dependency_mapping_missing"
    } else {
        "promotion_declaration_dependency_unmaterialized"
    }
}

fn declaration_closure_failure_diagnostic(
    error: &npa_cert::DeclarationClosureError,
    request: &DeclarationPromotionRequest,
    request_path: &PackagePath,
    baseline: &LoadedPackageAuditSnapshot,
) -> CommandDiagnostic {
    let reason = error.identity.as_deref().map_or_else(
        || error.reason.as_str(),
        |identity| declaration_closure_failure_reason(error.reason, identity, request, baseline),
    );
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason)
        .with_path(request_path.as_str());
    if let Some(identity) = error.identity.as_deref() {
        diagnostic = diagnostic
            .with_module(identity.module.as_dotted())
            .with_field(identity.name.as_dotted())
            .with_actual_value(npa_package::format_package_hash(&PackageHash::from(
                identity.decl_interface_hash,
            )));
    } else {
        diagnostic = diagnostic.with_module(request.source_module.as_dotted());
    }
    if let Some(field) = error.field {
        diagnostic = diagnostic.with_field(field);
    }
    if let Some(expected) = error.expected_value {
        diagnostic = diagnostic.with_expected_value(expected.to_string());
    }
    if let Some(actual) = error.actual_value {
        diagnostic = diagnostic.with_actual_value(actual.to_string());
    }
    diagnostic
}

fn declaration_mappings(
    request: &DeclarationPromotionRequest,
    source: &LoadedPackageAuditSnapshot,
    target: &LoadedPackageAuditSnapshot,
) -> DeclarationMappingResult {
    let mut identities = BTreeMap::new();
    let mut routes = BTreeMap::new();
    for row in &request.dependency_mappings {
        let source_record = endpoint_record(source, &row.source).ok_or_else(|| {
            (
                "promotion_declaration_dependency_mapping_stale",
                row.source.module.clone(),
            )
        })?;
        let target_record = endpoint_record(target, &row.target).ok_or_else(|| {
            (
                "promotion_declaration_dependency_mapping_stale",
                row.target.module.clone(),
            )
        })?;
        for export in source_record.verified_module.export_block() {
            let Some(name) = source_record.verified_module.name_table().get(export.name) else {
                continue;
            };
            let Ok(source_identity) =
                resolve_verified_declaration_export(&source_record.verified_module, name)
            else {
                continue;
            };
            let Ok(target_identity) =
                resolve_verified_declaration_export(&target_record.verified_module, name)
            else {
                continue;
            };
            let compatible = source_identity.identity.kind == target_identity.identity.kind
                && source_identity.identity.decl_interface_hash
                    == target_identity.identity.decl_interface_hash;
            if compatible
                && (identities
                    .insert(
                        source_identity.identity.clone(),
                        target_identity.identity.clone(),
                    )
                    .is_some()
                    || routes
                        .insert(
                            (
                                source_identity.identity.module.clone(),
                                source_identity.identity.name.clone(),
                            ),
                            (row.source.clone(), row.target.clone()),
                        )
                        .is_some())
            {
                return Err((
                    "promotion_declaration_dependency_mapping_stale",
                    name.clone(),
                ));
            }
        }
    }
    Ok((identities, routes))
}

pub(crate) fn endpoint_record<'a>(
    snapshot: &'a LoadedPackageAuditSnapshot,
    endpoint: &PromotionPlanEndpoint,
) -> Option<&'a PackageArtifactVerifiedModule> {
    let manifest = snapshot.snapshot.validated.manifest();
    let lock = snapshot
        .snapshot
        .package_lock_manifest
        .entries
        .iter()
        .find(|entry| entry.module == endpoint.module)?;
    let identity_matches = match endpoint.origin {
        PackageArtifactOrigin::Local => {
            lock.origin == PackageLockEntryOrigin::Local
                && endpoint.package == manifest.package
                && endpoint.version == manifest.version
        }
        PackageArtifactOrigin::External => {
            lock.origin == PackageLockEntryOrigin::External
                && lock.package.as_ref() == Some(&endpoint.package)
                && lock.version.as_ref() == Some(&endpoint.version)
        }
    };
    identity_matches
        .then(|| record_for(snapshot, &endpoint.module))
        .flatten()
}

pub(crate) fn plan_roots(
    request: &DeclarationPromotionRequest,
    families: &HumanSourceDeclarationFamilies,
) -> Vec<PromotionPlanV2Root> {
    let mut roots = request
        .roots
        .iter()
        .filter_map(|root| {
            families
                .families
                .iter()
                .find(|family| {
                    family
                        .members
                        .iter()
                        .any(|member| member.name == root.source_name)
                })
                .map(|family| PromotionPlanV2Root {
                    requested_name: root.source_name.clone(),
                    owner_name: family.owner.clone(),
                    kind: root.kind.as_str().to_owned(),
                })
        })
        .collect::<Vec<_>>();
    roots.sort();
    roots
}

fn plan_identity(identity: &GlobalDeclarationIdentity) -> PromotionPlanV2Identity {
    PromotionPlanV2Identity {
        module: identity.module.clone(),
        name: identity.name.clone(),
        kind: identity.kind.as_str().to_owned(),
        decl_interface_hash: PackageHash::from(identity.decl_interface_hash),
    }
}

pub(crate) fn plan_declarations(
    closure: &DeclarationClosure,
    human: &HumanMemberMap,
) -> Result<Vec<PromotionPlanV2Declaration>, Name> {
    let mut rows = Vec::new();
    for declaration in &closure.declarations {
        let Some((human_kind, span, owner, family_members)) = human.get(&declaration.identity.name)
        else {
            return Err(declaration.identity.name.clone());
        };
        let mut generated = declaration
            .generated_exports
            .iter()
            .map(|row| plan_identity(&row.identity))
            .collect::<Vec<_>>();
        generated.sort();
        let mut direct = closure
            .edges
            .iter()
            .filter(|edge| edge.source == declaration.identity)
            .map(|edge| plan_identity(&edge.target))
            .collect::<Vec<_>>();
        direct.sort();
        direct.dedup();
        let mut members = family_members.clone();
        members.sort();
        members.dedup();
        rows.push(PromotionPlanV2Declaration {
            role: declaration.role.as_str().to_owned(),
            source_name: declaration.identity.name.clone(),
            target_name: declaration.identity.name.clone(),
            certificate_kind: declaration.identity.kind.as_str().to_owned(),
            human_kind: human_kind.as_str().to_owned(),
            source_decl_index: declaration.decl_index as u64,
            decl_interface_hash: PackageHash::from(declaration.identity.decl_interface_hash),
            decl_certificate_hash: PackageHash::from(declaration.decl_certificate_hash),
            type_hash: PackageHash::from(declaration.export_type_hash),
            body_hash: declaration.export_body_hash.map(PackageHash::from),
            item_span: PromotionSourceSpan {
                start: span.start.0 as u64,
                end: span.end.0 as u64,
            },
            family_owner: owner.clone(),
            family_members: members,
            generated_exports: generated,
            direct_dependencies: direct,
        });
    }
    rows.sort();
    Ok(rows)
}

fn used_plan_mappings(
    closure: &DeclarationClosure,
    routes: &MappingRoutes,
    baseline: &LoadedPackageAuditSnapshot,
) -> Result<Vec<PromotionPlanV2DependencyMapping>, Name> {
    let mut rows = Vec::new();
    for (source, target) in &closure.externalized {
        let (source_endpoint, target_endpoint) = routes
            .get(&(source.module.clone(), source.name.clone()))
            .ok_or_else(|| source.name.clone())?;
        let record =
            endpoint_record(baseline, target_endpoint).ok_or_else(|| target.name.clone())?;
        rows.push(PromotionPlanV2DependencyMapping {
            source: source_endpoint.clone(),
            target: target_endpoint.clone(),
            declaration_name: source.name.clone(),
            source_decl_interface_hash: PackageHash::from(source.decl_interface_hash),
            target_decl_interface_hash: PackageHash::from(target.decl_interface_hash),
            target_certificate_file_hash: record.certificate.file_hash,
            target_certificate_hash: record.key.certificate_hash,
            target_export_hash: record.key.export_hash,
        });
    }
    rows.sort();
    Ok(rows)
}

fn extraction_preview(
    request: &DeclarationPromotionRequest,
    source: &str,
    imports: &[HumanImportedSourceInterface],
    closure: &DeclarationClosure,
    human: &HumanMemberMap,
    externalized: &BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
) -> Result<(), ()> {
    let declarations = closure
        .declarations
        .iter()
        .map(|row| {
            let (kind, span, _, _) = human.get(&row.identity.name).ok_or(())?;
            Ok(HumanSelectedDeclaration {
                name: row.identity.name.clone(),
                kind: *kind,
                item_span: *span,
                decl_interface_hash: row.identity.decl_interface_hash,
            })
        })
        .collect::<Result<Vec<_>, ()>>()?;
    let mut mapping = closure
        .declarations
        .iter()
        .map(|row| HumanGlobalMappingRow {
            source: HumanGlobalIdentity {
                module: request.source_module.clone(),
                name: row.identity.name.clone(),
                decl_interface_hash: row.identity.decl_interface_hash,
            },
            target: HumanGlobalIdentity {
                module: request.target_module.clone(),
                name: row.identity.name.clone(),
                decl_interface_hash: row.identity.decl_interface_hash,
            },
        })
        .collect::<Vec<_>>();
    mapping.extend(
        externalized
            .iter()
            .map(|(source, target)| HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: source.module.clone(),
                    name: source.name.clone(),
                    decl_interface_hash: source.decl_interface_hash,
                },
                target: HumanGlobalIdentity {
                    module: target.module.clone(),
                    name: target.name.clone(),
                    decl_interface_hash: target.decl_interface_hash,
                },
            }),
    );
    mapping.sort();
    extract_human_declaration_source(
        FileId(0),
        source,
        imports,
        &HumanDeclarationSelection {
            source_module: request.source_module.clone(),
            target_module: request.target_module.clone(),
            declarations,
        },
        &HumanGlobalMapping { rows: mapping },
    )
    .map(|_| ())
    .map_err(|_| ())
}

pub(crate) fn registry_owns_active_target(
    registry: &ParsedPromotionOriginRegistry,
    target: &Name,
) -> bool {
    let v1_entry_owns = |entry: &npa_package::PromotionOriginEntry| {
        entry.lifecycle == PromotionLifecycle::Active
            && entry
                .module_routes
                .iter()
                .any(|route| &route.target_module == target)
    };
    let reservation_owns = |reservation: &npa_package::PromotionLegacyTargetReservation| {
        reservation.lifecycle == PromotionLifecycle::Active && &reservation.target_module == target
    };
    match registry {
        ParsedPromotionOriginRegistry::V1(registry) => {
            registry.entries.iter().any(v1_entry_owns)
                || registry
                    .unresolved_legacy_targets
                    .iter()
                    .any(reservation_owns)
        }
        ParsedPromotionOriginRegistry::V2(registry) => {
            registry.entries.iter().any(|entry| match entry {
                PromotionOriginEntryV2::WholeModuleV1(entry) => v1_entry_owns(entry),
                PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
                    entry.lifecycle == "active" && &entry.target_module == target
                }
            }) || registry
                .unresolved_legacy_targets
                .iter()
                .any(reservation_owns)
        }
    }
}

fn registry_collides(
    registry: &ParsedPromotionOriginRegistry,
    request: &DeclarationPromotionRequest,
    closure: &DeclarationClosure,
    source_origin: &PromotionSourceModule,
) -> bool {
    match registry {
        ParsedPromotionOriginRegistry::V2(registry) => {
            registry
                .unresolved_legacy_targets
                .iter()
                .any(|row| row.target_module == request.target_module)
                || registry.entries.iter().any(|entry| match entry {
                    PromotionOriginEntryV2::WholeModuleV1(entry) => {
                        entry
                            .module_routes
                            .iter()
                            .any(|route| route.target_module == request.target_module)
                            || whole_module_origin_matches(&entry.canonical_source, source_origin)
                            || entry
                                .equivalent_sources
                                .iter()
                                .any(|origin| whole_module_origin_matches(origin, source_origin))
                    }
                    PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
                        entry.target_module == request.target_module
                            || entry.closure.iter().any(|old| {
                                closure.declarations.iter().any(|new| {
                                    entry.source_module == new.identity.module
                                        && old.source_name == new.identity.name
                                        && old.certificate_kind == new.identity.kind.as_str()
                                        && old.decl_interface_hash
                                            == PackageHash::from(new.identity.decl_interface_hash)
                                })
                            })
                    }
                })
        }
        ParsedPromotionOriginRegistry::V1(registry) => {
            registry
                .unresolved_legacy_targets
                .iter()
                .any(|row| row.target_module == request.target_module)
                || registry.entries.iter().any(|entry| {
                    entry
                        .module_routes
                        .iter()
                        .any(|route| route.target_module == request.target_module)
                        || whole_module_origin_matches(&entry.canonical_source, source_origin)
                        || entry
                            .equivalent_sources
                            .iter()
                            .any(|origin| whole_module_origin_matches(origin, source_origin))
                })
        }
    }
}

fn whole_module_origin_matches(
    origin: &npa_package::PromotionSourceOrigin,
    source: &PromotionSourceModule,
) -> bool {
    origin.modules.contains(source)
}

fn equivalent_sources(
    roots: &[std::path::PathBuf],
    request: &DeclarationPromotionRequest,
    canonical_source: &[u8],
    canonical_module: &npa_package::PackageModule,
    closure: &DeclarationClosure,
    dependency_edge_hash: PackageHash,
) -> Result<Vec<PromotionPlanV2EquivalentSource>, CommandResult> {
    let mut rows = Vec::new();
    for root in roots {
        let root_display = render_package_root(root);
        let snapshot = load_snapshot(root)?;
        if let Err(diagnostic) = validate_checked_generated(&snapshot) {
            return Err(CommandResult::failed(
                COMMAND,
                root_display,
                vec![*diagnostic],
            ));
        }
        let manifest = snapshot.snapshot.validated.manifest();
        let Some(module) = manifest
            .modules
            .iter()
            .find(|module| module.module == request.source_module)
        else {
            return Err(failed(
                &root_display,
                "promotion_registry_source_identity_mismatch",
                &request.source_module.as_dotted(),
            ));
        };
        let bytes = read_confined(
            root,
            &module.source,
            "promotion_registry_source_identity_mismatch",
        )
        .map_err(|diagnostic| {
            CommandResult::failed(COMMAND, root_display.clone(), vec![*diagnostic])
        })?;
        if bytes != canonical_source
            || module.expected_certificate_file_hash
                != canonical_module.expected_certificate_file_hash
            || module.expected_certificate_hash != canonical_module.expected_certificate_hash
            || module.expected_export_hash != canonical_module.expected_export_hash
        {
            return Err(failed(
                &root_display,
                "promotion_registry_source_identity_mismatch",
                module.source.as_str(),
            ));
        }
        rows.push(PromotionPlanV2EquivalentSource {
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            source_module: request.source_module.clone(),
            source_file_hash: package_file_hash(&bytes),
            certificate_file_hash: module.expected_certificate_file_hash,
            certificate_hash: module.expected_certificate_hash,
            export_hash: module.expected_export_hash,
            declaration_closure_hash: PackageHash::from(closure.declaration_closure_hash),
            dependency_edge_hash,
        });
    }
    rows.sort();
    if rows.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(failed(
            ".",
            "promotion_registry_source_identity_mismatch",
            "--equivalent-origin-root",
        ));
    }
    Ok(rows)
}

fn checked_hashes(snapshot: &LoadedPackageAuditSnapshot) -> Option<(PackageHash, PackageHash)> {
    Some((
        package_file_hash(
            snapshot
                .checked_generated
                .axiom_report_json
                .as_deref()?
                .as_bytes(),
        ),
        package_file_hash(
            snapshot
                .checked_generated
                .theorem_index_json
                .as_deref()?
                .as_bytes(),
        ),
    ))
}

fn target_artifact_paths(module: &Name) -> [PackagePath; 4] {
    let base = module.as_dotted().replace('.', "/");
    [
        PackagePath::new(format!("{base}/source.npa")),
        PackagePath::new(format!("{base}/certificate.npcert")),
        PackagePath::new(format!("{base}/meta.json")),
        PackagePath::new(format!("{base}/replay.json")),
    ]
}

pub(crate) fn read_declaration_source(
    root: &Path,
    path: &PackagePath,
    cumulative_source_bytes: &mut u64,
) -> Result<Vec<u8>, DeclarationSourceExtractionError> {
    read_declaration_source_with_limit(
        root,
        path,
        cumulative_source_bytes,
        MAX_EXTRACTION_SOURCE_BYTES,
    )
}

fn read_declaration_source_with_limit(
    root: &Path,
    path: &PackagePath,
    cumulative_source_bytes: &mut u64,
    max_source_bytes: u64,
) -> Result<Vec<u8>, DeclarationSourceExtractionError> {
    if *cumulative_source_bytes > max_source_bytes {
        return Err(DeclarationSourceExtractionError::SourceBytesLimitExceeded {
            actual: *cumulative_source_bytes,
        });
    }
    let full = confined_governance_path(
        root,
        path,
        path.as_str(),
        "promotion_declaration_source_extraction_unsupported",
    )
    .map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
    let file = fs::File::open(full).map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
    let file_bytes = file
        .metadata()
        .map_err(|_| DeclarationSourceExtractionError::Unsupported)?
        .len();
    let projected_source_bytes = cumulative_source_bytes.saturating_add(file_bytes);
    if projected_source_bytes > max_source_bytes {
        return Err(DeclarationSourceExtractionError::SourceBytesLimitExceeded {
            actual: projected_source_bytes,
        });
    }

    let remaining_source_bytes = max_source_bytes - *cumulative_source_bytes;
    let mut source = Vec::new();
    file.take(remaining_source_bytes.saturating_add(1))
        .read_to_end(&mut source)
        .map_err(|_| DeclarationSourceExtractionError::Unsupported)?;
    let actual_source_bytes =
        cumulative_source_bytes.saturating_add(u64::try_from(source.len()).unwrap_or(u64::MAX));
    if actual_source_bytes > max_source_bytes {
        return Err(DeclarationSourceExtractionError::SourceBytesLimitExceeded {
            actual: actual_source_bytes,
        });
    }
    *cumulative_source_bytes = actual_source_bytes;
    Ok(source)
}

fn read_baseline(root: &Path, path: &str) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    read_confined(
        root,
        &PackagePath::new(path),
        "promotion_declaration_request_invalid",
    )
}

fn read_confined(
    root: &Path,
    path: &PackagePath,
    reason: &str,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let full = confined_governance_path(root, path, path.as_str(), reason)?;
    fs::read(full).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason).with_path(path.as_str()),
        )
    })
}

fn failed(root: &str, reason: &str, path: &str) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        root,
        vec![CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path)],
    )
}

fn failed_with_module(root: &str, reason: &str, module: &Name, path: &str) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        root,
        vec![
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason)
                .with_module(module.as_dotted())
                .with_path(path),
        ],
    )
}

fn source_extraction_failure(
    root: &str,
    module: &Name,
    path: &PackagePath,
    error: DeclarationSourceExtractionError,
) -> CommandResult {
    match error {
        DeclarationSourceExtractionError::Unsupported => failed_with_module(
            root,
            "promotion_declaration_source_extraction_unsupported",
            module,
            path.as_str(),
        ),
        DeclarationSourceExtractionError::SourceBytesLimitExceeded { actual } => {
            CommandResult::failed(
                COMMAND,
                root,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "promotion_declaration_closure_limit_exceeded",
                )
                .with_module(module.as_dotted())
                .with_path(path.as_str())
                .with_field("source_bytes")
                .with_expected_value(MAX_EXTRACTION_SOURCE_BYTES.to_string())
                .with_actual_value(actual.to_string())],
            )
        }
    }
}

fn failed_with_declaration(
    root: &str,
    reason: &str,
    module: &Name,
    declaration: &Name,
    path: &str,
) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        root,
        vec![
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason)
                .with_module(module.as_dotted())
                .with_field(declaration.as_dotted())
                .with_path(path),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_package::{
        migrate_promotion_origin_registry_v1_to_v2, promotion_legacy_target_reservation_id,
        PromotionAuditLocation, PromotionEvidence, PromotionLegacyTargetReservation,
        PromotionReservedTheorem, PromotionTargetRevision,
    };

    #[test]
    fn local_mapping_targets_require_active_registry_ownership() {
        let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package");
        let source = fs::read_to_string(
            fixtures.join("npa-mathlib-declaration-baseline/promotion-origins.json"),
        )
        .unwrap();
        let mut registry = match parse_promotion_origin_registry_versioned(&source).unwrap() {
            ParsedPromotionOriginRegistry::V1(registry) => registry,
            ParsedPromotionOriginRegistry::V2(_) => panic!("fixture registry must be v1"),
        };
        let target = Name::from_dotted("Mathlib.Registered.Dependency");
        assert!(!registry_owns_active_target(
            &ParsedPromotionOriginRegistry::V1(registry.clone()),
            &target,
        ));

        let revision = PromotionTargetRevision::<PromotionReservedTheorem> {
            target_version: npa_package::PackageVersion::new("0.1.0"),
            target_source_file_hash: PackageHash::new([1; 32]),
            target_certificate_file_hash: PackageHash::new([2; 32]),
            target_certificate_hash: PackageHash::new([3; 32]),
            target_export_hash: PackageHash::new([4; 32]),
            target_axiom_report_hash: PackageHash::new([5; 32]),
            theorems: Vec::new(),
        };
        let audit_location = PromotionAuditLocation {
            repository: "npa-mathlib".to_owned(),
            path: PackagePath::new("docs/promotion/registered-dependency.md"),
        };
        registry
            .unresolved_legacy_targets
            .push(PromotionLegacyTargetReservation {
                reservation_id: promotion_legacy_target_reservation_id(&target, &revision).unwrap(),
                lifecycle: PromotionLifecycle::Active,
                target_module: target.clone(),
                target_revisions: vec![revision],
                evidence: PromotionEvidence::LegacyAudit {
                    audit_location: audit_location.clone(),
                    audit_file_hash: PackageHash::new([6; 32]),
                },
            });
        registry.refresh_hash().unwrap();
        assert!(registry_owns_active_target(
            &ParsedPromotionOriginRegistry::V1(registry.clone()),
            &target,
        ));

        let migrated = migrate_promotion_origin_registry_v1_to_v2(&registry).unwrap();
        assert!(registry_owns_active_target(
            &ParsedPromotionOriginRegistry::V2(migrated),
            &target,
        ));

        registry.unresolved_legacy_targets[0].lifecycle = PromotionLifecycle::Retired {
            retired_version: npa_package::PackageVersion::new("0.1.1"),
            audit_location,
            audit_file_hash: PackageHash::new([7; 32]),
        };
        registry.refresh_hash().unwrap();
        assert!(!registry_owns_active_target(
            &ParsedPromotionOriginRegistry::V1(registry),
            &target,
        ));
    }

    #[test]
    fn imported_dependency_failure_distinguishes_eligible_and_absent_routes() {
        let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package");
        let source = match load_snapshot(&fixtures.join("proofs")) {
            Ok(snapshot) => snapshot,
            Err(_) => panic!("proof fixture snapshot must load"),
        };
        let empty_baseline = match load_snapshot(&fixtures.join("npa-mathlib-declaration-baseline"))
        {
            Ok(snapshot) => snapshot,
            Err(_) => panic!("empty mathlib fixture snapshot must load"),
        };
        let request_source =
            fs::read_to_string(fixtures.join("proofs/promotion/declaration-local.selection.json"))
                .unwrap();
        let request = parse_declaration_promotion_request_json(&request_source).unwrap();
        let module = Name::from_dotted("Proofs.Ai.EqReasoning");
        let record = record_for(&source, &module).expect("fixture module must be verified");
        let identity = resolve_verified_declaration_export(
            &record.verified_module,
            &Name::from_dotted("eq_symm"),
        )
        .unwrap()
        .identity;

        assert_eq!(
            declaration_closure_failure_reason(
                npa_cert::DeclarationClosureErrorReason::DependencyMappingMissing,
                &identity,
                &request,
                &source,
            ),
            "promotion_declaration_dependency_mapping_missing"
        );
        assert_eq!(
            declaration_closure_failure_reason(
                npa_cert::DeclarationClosureErrorReason::DependencyMappingMissing,
                &identity,
                &request,
                &empty_baseline,
            ),
            "promotion_declaration_dependency_unmaterialized"
        );

        let request_path = PackagePath::new("promotion/declaration-local.selection.json");
        let identity_error = npa_cert::DeclarationClosureError {
            reason: npa_cert::DeclarationClosureErrorReason::DependencyMappingMissing,
            identity: Some(Box::new(identity.clone())),
            field: None,
            expected_value: None,
            actual_value: None,
        };
        let diagnostic = declaration_closure_failure_diagnostic(
            &identity_error,
            &request,
            &request_path,
            &empty_baseline,
        );
        assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.EqReasoning"));
        assert_eq!(diagnostic.field.as_deref(), Some("eq_symm"));
        let expected_interface_hash =
            npa_package::format_package_hash(&PackageHash::from(identity.decl_interface_hash));
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some(expected_interface_hash.as_str())
        );

        let limit_error = npa_cert::DeclarationClosureError {
            reason: npa_cert::DeclarationClosureErrorReason::LimitExceeded,
            identity: None,
            field: Some("dependency_edges"),
            expected_value: Some(10),
            actual_value: Some(11),
        };
        let diagnostic = declaration_closure_failure_diagnostic(
            &limit_error,
            &request,
            &request_path,
            &empty_baseline,
        );
        assert_eq!(
            diagnostic.module.as_deref(),
            Some("Proofs.Ai.Analysis.AbstractMetricTopology")
        );
        assert_eq!(diagnostic.field.as_deref(), Some("dependency_edges"));
        assert_eq!(diagnostic.expected_value.as_deref(), Some("10"));
        assert_eq!(diagnostic.actual_value.as_deref(), Some("11"));
    }

    #[test]
    fn source_local_axiom_externalization_is_rejected() {
        let source = GlobalDeclarationIdentity {
            module: Name::from_dotted("Proofs.LocalAxioms"),
            name: Name::from_dotted("choice"),
            kind: DeclarationClosureKind::Axiom,
            decl_interface_hash: [1; 32],
        };
        let target = GlobalDeclarationIdentity {
            module: Name::from_dotted("Std.Logic.Classical"),
            name: source.name.clone(),
            kind: DeclarationClosureKind::Axiom,
            decl_interface_hash: source.decl_interface_hash,
        };
        let closure = DeclarationClosure {
            requested_roots: Vec::new(),
            root_owners: Vec::new(),
            declarations: Vec::new(),
            externalized: vec![(source.clone(), target)],
            builtins: Vec::new(),
            allowed_axioms: vec![source.clone()],
            edges: Vec::new(),
            declaration_closure_hash: [0; 32],
        };
        let routes = BTreeMap::from([(
            (source.module.clone(), source.name.clone()),
            (
                PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: npa_package::PackageId::new("source-package"),
                    version: npa_package::PackageVersion::new("0.1.0"),
                    module: source.module.clone(),
                },
                PromotionPlanEndpoint {
                    origin: PackageArtifactOrigin::External,
                    package: npa_package::PackageId::new("npa-std"),
                    version: npa_package::PackageVersion::new("0.1.0"),
                    module: Name::from_dotted("Std.Logic.Classical"),
                },
            ),
        )]);

        assert_eq!(
            source_local_externalized_axiom(&closure, &routes),
            Some(&source)
        );

        let mut external_routes = routes;
        external_routes
            .values_mut()
            .next()
            .expect("fixture route must exist")
            .0
            .origin = PackageArtifactOrigin::External;
        assert_eq!(
            source_local_externalized_axiom(&closure, &external_routes),
            None
        );
    }

    #[test]
    fn imported_source_reconstruction_enforces_cumulative_byte_limit() {
        let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package");
        let root = fixtures.join("proofs");
        let source = match load_snapshot(&root) {
            Ok(snapshot) => snapshot,
            Err(_) => panic!("proof fixture snapshot must load"),
        };
        let module = source
            .snapshot
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| {
                module.module == Name::from_dotted("Proofs.Ai.Analysis.AbstractMetricTopology")
            })
            .expect("fixture module must exist");
        let imported_module = source
            .snapshot
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == Name::from_dotted("Proofs.Ai.EqReasoning"))
            .expect("fixture import must exist");
        let imported_source_bytes = fs::metadata(root.join(imported_module.source.as_str()))
            .expect("fixture import source must exist")
            .len();

        let error = direct_import_interfaces_with_limit(
            &root,
            &source,
            &module.imports,
            1,
            imported_source_bytes,
        )
        .expect_err("the selected source byte must count against the import budget");
        assert_eq!(
            error,
            DeclarationSourceExtractionError::SourceBytesLimitExceeded {
                actual: imported_source_bytes + 1,
            }
        );
    }

    #[test]
    fn equivalent_origin_limit_is_checked_before_loading_snapshots() {
        let roots = vec![
            std::path::PathBuf::from("unloaded");
            DECLARATION_CLOSURE_LIMITS_V1.loaded_modules + 1
        ];
        let diagnostic = validate_equivalent_origin_root_count(&roots).unwrap_err();
        assert_eq!(
            diagnostic.reason_code,
            "promotion_declaration_closure_limit_exceeded"
        );
        assert_eq!(diagnostic.field.as_deref(), Some("equivalent_sources"));
        let expected = DECLARATION_CLOSURE_LIMITS_V1.loaded_modules.to_string();
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some(expected.as_str())
        );
        let actual = roots.len().to_string();
        assert_eq!(diagnostic.actual_value.as_deref(), Some(actual.as_str()));
    }

    #[test]
    fn import_interface_dependency_order_handles_deep_chains_iteratively() {
        let modules = (0..4_096)
            .map(|index| Name::from_dotted(format!("Module.M{index}")))
            .collect::<Vec<_>>();
        let dependencies = modules
            .iter()
            .enumerate()
            .map(|(index, module)| {
                (
                    module.clone(),
                    modules.get(index + 1).cloned().into_iter().collect(),
                )
            })
            .collect::<BTreeMap<_, _>>();

        let order = import_interface_dependency_order(&modules[..1], |module| {
            dependencies.get(module).map(Vec::as_slice)
        })
        .expect("a deep acyclic import chain must have a postorder");
        assert_eq!(order.len(), modules.len());
        assert_eq!(order.first(), modules.last());
        assert_eq!(order.last(), modules.first());
    }

    #[test]
    fn import_interface_dependency_order_rejects_cycles() {
        let first = Name::from_dotted("Module.First");
        let second = Name::from_dotted("Module.Second");
        let dependencies = BTreeMap::from([
            (first.clone(), vec![second.clone()]),
            (second, vec![first.clone()]),
        ]);

        assert_eq!(
            import_interface_dependency_order(&[first], |module| {
                dependencies.get(module).map(Vec::as_slice)
            }),
            Err(DeclarationSourceExtractionError::Unsupported)
        );
    }
}
