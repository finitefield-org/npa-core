//! Build a canonical package-generic mathlib promotion plan.

use std::{collections::BTreeSet, fs};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_cert::{ExportKind, Name};
use npa_package::{
    package_file_hash, parse_l2_acceptance_policy_json, parse_l2_acceptance_v2_json,
    parse_l2_namespace_transport_policy_json, parse_l2_namespace_transport_request_json,
    MathlibPromotionPlan, PackageArtifactOrigin, PackageHash, PackagePath, PackageVersion,
    PromotionGovernance, PromotionOriginLookup, PromotionPackageSnapshot,
    PromotionPlanDependencyMapping, PromotionPlanEndpoint, PromotionPlanExport,
    PromotionPlanSelectedModule, PromotionPlanTheorem, PromotionSourceModule,
    PromotionSourceOrigin, PromotionTargetSnapshot, MATHLIB_PROMOTION_PLAN_SCHEMA,
    MATHLIB_PROMOTION_REGISTRY_PATH,
};

use crate::{
    args::PackagePreparePromotionOptions,
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::render_package_root,
    governance_writer::{
        confined_governance_path, write_governance_artifact, GovernanceOutputPolicy,
    },
    package::load_package_root,
    package_artifacts::{
        load_package_audit_snapshot, LoadedPackageAuditSnapshot, PACKAGE_THEOREM_INDEX_PATH,
    },
    package_l2_acceptance_aggregate::validate_l2_acceptance_v2_current,
    package_promotion_prepare_declaration::run_package_prepare_declaration_promotion,
    package_promotion_registry::{
        load_registry_versioned_with_source, lookup_promotion_origin_versioned,
        promotion_plan_generated_read_mode, validate_checked_generated,
    },
};

const COMMAND: &str = "package prepare-promotion";

/// Validate current promotion inputs and create or check one canonical plan.
pub fn run_package_prepare_promotion(options: PackagePreparePromotionOptions) -> CommandResult {
    if options.declaration_request.is_some() {
        return run_package_prepare_declaration_promotion(options);
    }
    run_package_prepare_module_promotion(options)
}

fn run_package_prepare_module_promotion(options: PackagePreparePromotionOptions) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let Some(acceptance_policy_path) = options.acceptance_policy.as_ref() else {
        return failure(
            &root_display,
            "promotion_plan_policy_stale",
            "--acceptance-policy",
        );
    };
    let Some(source_acceptance_path) = options.source_acceptance.as_ref() else {
        return failure(
            &root_display,
            "promotion_plan_source_acceptance_failed",
            "--source-acceptance",
        );
    };
    let Some(transport_policy_path) = options.transport_policy.as_ref() else {
        return failure(
            &root_display,
            "promotion_plan_policy_stale",
            "--transport-policy",
        );
    };
    let Some(mapping_request_path) = options.mapping.as_ref() else {
        return failure(&root_display, "promotion_plan_mapping_stale", "--mapping");
    };
    let source_root = match load_package_root(&options.common.root, COMMAND) {
        Ok(root) => root,
        Err(result) => return result,
    };
    let source = match load_package_audit_snapshot(
        &options.common.root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    let target = match load_package_audit_snapshot(
        &options.target_baseline_root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    for snapshot in [&source, &target] {
        if let Err(diagnostic) = validate_checked_generated(snapshot) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }

    let policy_source =
        match read_workspace_file(acceptance_policy_path, "promotion_plan_policy_stale") {
            Ok(source) => source,
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
            }
        };
    let acceptance_policy = match parse_l2_acceptance_policy_json(&policy_source) {
        Ok(policy) => policy,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_plan_policy_stale",
                "--acceptance-policy",
            )
        }
    };
    let acceptance_path = PackagePath::new(source_acceptance_path.to_string_lossy());
    let acceptance_source = match read_source_file(
        &options.common.root,
        &acceptance_path,
        "promotion_plan_source_acceptance_failed",
    ) {
        Ok(source) => source,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let acceptance = match parse_l2_acceptance_v2_json(&acceptance_source) {
        Ok(acceptance) => acceptance,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_plan_source_acceptance_failed",
                acceptance_path.as_str(),
            )
        }
    };
    let policy_hash = package_file_hash(policy_source.as_bytes());
    if let Err(diagnostic) = validate_l2_acceptance_v2_current(
        &source_root,
        &acceptance,
        &acceptance_policy,
        policy_hash,
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }

    let transport_policy_source =
        match read_workspace_file(transport_policy_path, "promotion_plan_policy_stale") {
            Ok(source) => source,
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
            }
        };
    let transport_policy = match parse_l2_namespace_transport_policy_json(&transport_policy_source)
    {
        Ok(policy) => policy,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_plan_policy_stale",
                "--transport-policy",
            )
        }
    };
    let mapping_path = PackagePath::new(mapping_request_path.to_string_lossy());
    let mapping_source = match read_source_file(
        &options.common.root,
        &mapping_path,
        "promotion_plan_mapping_stale",
    ) {
        Ok(source) => source,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let mapping = match parse_l2_namespace_transport_request_json(&mapping_source) {
        Ok(mapping) => mapping,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_plan_mapping_stale",
                mapping_path.as_str(),
            )
        }
    };
    let (registry, registry_source) =
        match load_registry_versioned_with_source(&options.target_baseline_root, COMMAND) {
            Ok(registry) => registry,
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
            }
        };

    if let Err(diagnostic) = validate_governance_and_mapping(
        &source,
        &target,
        &acceptance_policy,
        policy_hash,
        &transport_policy,
        &mapping,
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }

    let source_index = match source.snapshot.project_theorem_index() {
        Ok(index) => index,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_plan_generated_identity_mismatch",
                PACKAGE_THEOREM_INDEX_PATH,
            )
        }
    };
    let selected_names = mapping
        .module_mappings
        .iter()
        .filter(|row| row.role == npa_package::L2TransportModuleRole::Selected)
        .map(|row| row.source.module.clone())
        .collect::<BTreeSet<_>>();
    if let Err(diagnostic) =
        validate_complete_acceptance(&selected_names, &source_index, &acceptance)
    {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    if let Err(diagnostic) = validate_selected_closure(&source, &selected_names) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }

    let mut selected_modules = Vec::new();
    for row in mapping
        .module_mappings
        .iter()
        .filter(|row| row.role == npa_package::L2TransportModuleRole::Selected)
    {
        let projected =
            match project_selected_module(&options.common.root, &source, &source_index, row) {
                Ok(module) => module,
                Err(diagnostic) => {
                    return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
                }
            };
        selected_modules.push(projected);
    }
    selected_modules.sort_by(|left, right| {
        (&left.source_module, &left.target_module)
            .cmp(&(&right.source_module, &right.target_module))
    });
    if let Err(diagnostic) =
        validate_target_artifact_paths_absent(&options.target_baseline_root, &selected_modules)
    {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let canonical_origin = PromotionSourceOrigin {
        package: source.snapshot.validated.manifest().package.clone(),
        version: source.snapshot.validated.manifest().version.clone(),
        modules: selected_modules
            .iter()
            .map(|module| PromotionSourceModule {
                module: module.source_module.clone(),
                source_file_hash: module.source_file_hash,
                certificate_file_hash: module.certificate_file_hash,
                certificate_hash: module.certificate_hash,
                export_hash: module.export_hash,
            })
            .collect(),
    };
    let target_names = selected_modules
        .iter()
        .map(|module| module.target_module.clone())
        .collect::<Vec<_>>();
    let duplicate =
        lookup_promotion_origin_versioned(&registry, &canonical_origin, &target_names, &[]);
    if duplicate != PromotionOriginLookup::NoRegistryMatch {
        let reason = match duplicate {
            PromotionOriginLookup::ExactOriginAlreadyPromoted => {
                "promotion_plan_origin_already_promoted"
            }
            PromotionOriginLookup::ArtifactAliasAlreadyPromoted => {
                "promotion_plan_artifact_alias_already_promoted"
            }
            PromotionOriginLookup::TargetModuleCollision => {
                "promotion_plan_target_module_collision"
            }
            PromotionOriginLookup::TargetArtifactCollision => {
                "promotion_plan_target_artifact_collision"
            }
            PromotionOriginLookup::NoRegistryMatch => unreachable!(),
        };
        return failure(&root_display, reason, MATHLIB_PROMOTION_REGISTRY_PATH);
    }

    let mut equivalent_sources = Vec::new();
    for equivalent_root in &options.equivalent_origin_roots {
        let equivalent = match load_package_audit_snapshot(
            equivalent_root,
            COMMAND,
            promotion_plan_generated_read_mode(),
            PackageArtifactReferenceSummaryMode::Include,
        ) {
            Ok(snapshot) => snapshot,
            Err(result) => return result,
        };
        if let Err(diagnostic) = validate_checked_generated(&equivalent) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
        match project_equivalent_source(equivalent_root, &equivalent, &canonical_origin) {
            Ok(origin) => equivalent_sources.push(origin),
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
            }
        }
    }
    equivalent_sources.sort_by(|left, right| {
        (&left.package, &left.version).cmp(&(&right.package, &right.version))
    });

    let dependency_mappings = match project_dependencies(&target, &mapping) {
        Ok(rows) => rows,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let source_manifest = source.snapshot.validated.manifest();
    let target_manifest = target.snapshot.validated.manifest();
    let mut plan = MathlibPromotionPlan {
        schema: MATHLIB_PROMOTION_PLAN_SCHEMA.to_owned(),
        promotion_id: zero_hash(),
        source: PromotionPackageSnapshot {
            package: source_manifest.package.clone(),
            version: source_manifest.version.clone(),
            manifest_file_hash: source.snapshot.manifest.file_hash,
            lock_file_hash: package_file_hash(source.package_lock_json.as_bytes()),
            axiom_report_file_hash: package_file_hash(
                source
                    .checked_generated
                    .axiom_report_json
                    .as_deref()
                    .expect("all generated")
                    .as_bytes(),
            ),
            theorem_index_file_hash: package_file_hash(
                source
                    .checked_generated
                    .theorem_index_json
                    .as_deref()
                    .expect("all generated")
                    .as_bytes(),
            ),
        },
        target_baseline: PromotionTargetSnapshot {
            package: target_manifest.package.clone(),
            version: target_manifest.version.clone(),
            planned_version: mapping.target.version.clone(),
            manifest_file_hash: target.snapshot.manifest.file_hash,
            lock_file_hash: package_file_hash(target.package_lock_json.as_bytes()),
            axiom_report_file_hash: package_file_hash(
                target
                    .checked_generated
                    .axiom_report_json
                    .as_deref()
                    .expect("all generated")
                    .as_bytes(),
            ),
            theorem_index_file_hash: package_file_hash(
                target
                    .checked_generated
                    .theorem_index_json
                    .as_deref()
                    .expect("all generated")
                    .as_bytes(),
            ),
        },
        governance: PromotionGovernance {
            acceptance_policy_id: acceptance_policy.policy_id.clone(),
            acceptance_policy_version: acceptance_policy.policy_version,
            acceptance_policy_file_hash: policy_hash,
            source_acceptance_path: acceptance_path,
            source_acceptance_schema: acceptance.schema.clone(),
            source_acceptance_file_hash: package_file_hash(acceptance_source.as_bytes()),
            transport_policy_id: transport_policy.policy_id.clone(),
            transport_policy_version: transport_policy.policy_version,
            transport_policy_file_hash: package_file_hash(transport_policy_source.as_bytes()),
            mapping_path,
            mapping_schema: mapping.schema.clone(),
            mapping_file_hash: package_file_hash(mapping_source.as_bytes()),
            registry_file_hash: package_file_hash(registry_source.as_bytes()),
        },
        selected_modules,
        dependency_mappings,
        equivalent_sources,
        compatibility_alias: "none".to_owned(),
        plan_hash: zero_hash(),
        proof_evidence: false,
    };
    if plan.finalize().is_err() {
        return failure(
            &root_display,
            "promotion_plan_generated_identity_mismatch",
            "--out",
        );
    }
    let json = match plan.canonical_json() {
        Ok(json) => json,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_plan_generated_identity_mismatch",
                "--out",
            )
        }
    };
    let out = PackagePath::new(options.out.to_string_lossy());
    if options.check {
        let existing =
            read_source_file(&options.common.root, &out, "promotion_plan_output_conflict");
        if !matches!(existing, Ok(ref value) if value.as_bytes() == json.as_bytes()) {
            return failure(
                &root_display,
                "promotion_plan_output_conflict",
                out.as_str(),
            );
        }
    } else if let Err(diagnostic) = write_governance_artifact(
        &options.common.root,
        &out,
        json.as_bytes(),
        GovernanceOutputPolicy::CreateOrIdentical,
        "promotion_plan",
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "mathlib_promotion_plan".to_owned(),
        path: out.as_str().to_owned(),
    });
    result
}

fn validate_governance_and_mapping(
    source: &LoadedPackageAuditSnapshot,
    target: &LoadedPackageAuditSnapshot,
    acceptance_policy: &npa_package::L2AcceptancePolicy,
    acceptance_policy_hash: PackageHash,
    transport_policy: &npa_package::L2NamespaceTransportPolicy,
    mapping: &npa_package::L2NamespaceTransportRequest,
) -> Result<(), Box<CommandDiagnostic>> {
    let source_manifest = source.snapshot.validated.manifest();
    let target_manifest = target.snapshot.validated.manifest();
    if transport_policy.source_acceptance_policy_id != acceptance_policy.policy_id
        || transport_policy.source_acceptance_policy_version != acceptance_policy.policy_version
        || transport_policy.source_acceptance_policy_file_hash != acceptance_policy_hash
        || transport_policy.target_package != target_manifest.package
        || mapping.source.package != source_manifest.package
        || mapping.source.version != source_manifest.version
        || mapping.target.package != target_manifest.package
        || version_tuple(&mapping.target.version) <= version_tuple(&target_manifest.version)
    {
        return Err(policy_diagnostic(
            "promotion_plan_mapping_stale",
            "--mapping",
        ));
    }
    if mapping.module_mappings.iter().any(|row| {
        !row.renames.is_empty()
            || row.declaration_mapping != "same-name-except-explicit"
            || !promotion_mapping_source_is_current(source_manifest, mapping, row)
            || row.target.package != mapping.target.package
            || row.target.version != mapping.target.version
            || row.target.origin != PackageArtifactOrigin::Local
            || !transport_policy
                .allowed_source_prefixes
                .iter()
                .any(|prefix| row.source.module.as_dotted().starts_with(prefix))
            || !transport_policy
                .allowed_target_prefixes
                .iter()
                .any(|prefix| row.target.module.as_dotted().starts_with(prefix))
    }) {
        return Err(policy_diagnostic(
            "promotion_plan_declaration_rename_unsupported",
            "--mapping",
        ));
    }
    if mapping
        .module_mappings
        .iter()
        .filter(|row| row.role == npa_package::L2TransportModuleRole::Selected)
        .any(|row| {
            target_manifest
                .modules
                .iter()
                .any(|module| module.module == row.target.module)
        })
    {
        return Err(policy_diagnostic(
            "promotion_plan_target_module_collision",
            "--mapping",
        ));
    }
    Ok(())
}

pub(crate) fn promotion_mapping_source_is_current(
    source_manifest: &npa_package::PackageManifest,
    mapping: &npa_package::L2NamespaceTransportRequest,
    row: &npa_package::L2TransportModuleMapping,
) -> bool {
    match row.role {
        npa_package::L2TransportModuleRole::Selected => {
            row.source.origin == PackageArtifactOrigin::Local
                && row.source.package == mapping.source.package
                && row.source.version == mapping.source.version
                && source_manifest
                    .modules
                    .iter()
                    .any(|module| module.module == row.source.module)
        }
        npa_package::L2TransportModuleRole::Dependency => {
            row.source.origin == PackageArtifactOrigin::External
                && source_manifest.imports.as_ref().is_some_and(|imports| {
                    imports.iter().any(|import| {
                        import.module == row.source.module
                            && import.package == row.source.package
                            && import.version == row.source.version
                    })
                })
        }
    }
}

pub(crate) fn promotion_selected_target_artifact_paths(
    selected_modules: &[PromotionPlanSelectedModule],
) -> BTreeSet<PackagePath> {
    selected_modules
        .iter()
        .flat_map(|module| {
            let base = module.target_module.as_dotted().replace('.', "/");
            [
                PackagePath::new(format!("{base}/source.npa")),
                PackagePath::new(format!("{base}/certificate.npcert")),
                PackagePath::new(format!("{base}/meta.json")),
                PackagePath::new(format!("{base}/replay.json")),
            ]
        })
        .collect()
}

fn validate_target_artifact_paths_absent(
    target_root: &std::path::Path,
    selected_modules: &[PromotionPlanSelectedModule],
) -> Result<(), Box<CommandDiagnostic>> {
    for path in promotion_selected_target_artifact_paths(selected_modules) {
        let full = confined_governance_path(
            target_root,
            &path,
            path.as_str(),
            "promotion_plan_target_artifact_collision",
        )?;
        match fs::symlink_metadata(full) {
            Ok(_) => {
                return Err(policy_diagnostic(
                    "promotion_plan_target_artifact_collision",
                    path.as_str(),
                ))
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => {
                return Err(policy_diagnostic(
                    "promotion_plan_generated_identity_mismatch",
                    path.as_str(),
                ))
            }
        }
    }
    Ok(())
}

fn validate_complete_acceptance(
    selected: &BTreeSet<Name>,
    index: &npa_package::PackageTheoremIndex,
    acceptance: &npa_package::L2AcceptanceV2,
) -> Result<(), Box<CommandDiagnostic>> {
    for theorem in index.entries.iter().filter(|row| {
        selected.contains(&row.global_ref.module)
            && row.kind == npa_package::PackageTheoremIndexKind::Theorem
    }) {
        if !acceptance.entries.iter().any(|entry| {
            entry.module == theorem.global_ref.module
                && entry.theorem == theorem.global_ref.name
                && entry.statement_hash == theorem.statement.core_hash
                && entry.certificate_hash == theorem.global_ref.certificate_hash
        }) {
            return Err(policy_diagnostic(
                "promotion_plan_source_acceptance_failed",
                &theorem.global_ref.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_selected_closure(
    source: &LoadedPackageAuditSnapshot,
    selected: &BTreeSet<Name>,
) -> Result<(), Box<CommandDiagnostic>> {
    let locals = source
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    for module in source
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .filter(|module| selected.contains(&module.module))
    {
        if module
            .imports
            .iter()
            .any(|import| locals.contains(import) && !selected.contains(import))
        {
            return Err(policy_diagnostic(
                "promotion_plan_closure_incomplete",
                &module.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn project_selected_module(
    root: &std::path::Path,
    source: &LoadedPackageAuditSnapshot,
    theorem_index: &npa_package::PackageTheoremIndex,
    mapping: &npa_package::L2TransportModuleMapping,
) -> Result<PromotionPlanSelectedModule, Box<CommandDiagnostic>> {
    if mapping.source.origin != PackageArtifactOrigin::Local {
        return Err(policy_diagnostic(
            "promotion_plan_closure_incomplete",
            "--mapping",
        ));
    }
    let module = source
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .find(|module| module.module == mapping.source.module)
        .ok_or_else(|| {
            policy_diagnostic(
                "promotion_plan_closure_incomplete",
                &mapping.source.module.as_dotted(),
            )
        })?;
    if source
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .any(|existing| existing.module == mapping.target.module)
    {
        return Err(policy_diagnostic(
            "promotion_plan_target_module_collision",
            &mapping.target.module.as_dotted(),
        ));
    }
    let verified = source
        .snapshot
        .decoded_module_records
        .values()
        .find(|record| record.key.module == module.module)
        .ok_or_else(|| {
            policy_diagnostic(
                "promotion_plan_generated_identity_mismatch",
                &module.module.as_dotted(),
            )
        })?;
    let mut exports = verified
        .verified_module
        .export_block()
        .iter()
        .map(|export| {
            let name = verified.verified_module.name_table()[export.name].clone();
            PromotionPlanExport {
                kind: export_kind(export.kind).to_owned(),
                source_name: name.clone(),
                target_name: name,
                decl_interface_hash: PackageHash::from(export.decl_interface_hash),
            }
        })
        .collect::<Vec<_>>();
    exports.sort();
    let mut theorems = theorem_index
        .entries
        .iter()
        .filter(|entry| {
            entry.global_ref.module == module.module
                && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
        })
        .map(|entry| PromotionPlanTheorem {
            source_name: entry.global_ref.name.clone(),
            target_name: entry.global_ref.name.clone(),
            statement_hash: entry.statement.core_hash,
        })
        .collect::<Vec<_>>();
    theorems.sort();
    let source_path = confined_governance_path(
        root,
        &module.source,
        module.source.as_str(),
        "promotion_plan_generated_identity_mismatch",
    )?;
    let mut imports = module.imports.clone();
    imports.sort();
    Ok(PromotionPlanSelectedModule {
        source_module: module.module.clone(),
        target_module: mapping.target.module.clone(),
        source_path: module.source.clone(),
        source_file_hash: package_file_hash(&fs::read(source_path).map_err(|_| {
            policy_diagnostic(
                "promotion_plan_generated_identity_mismatch",
                module.source.as_str(),
            )
        })?),
        certificate_file_hash: module.expected_certificate_file_hash,
        certificate_hash: module.expected_certificate_hash,
        export_hash: module.expected_export_hash,
        axiom_report_hash: module.expected_axiom_report_hash,
        imports,
        exports,
        theorems,
    })
}

fn project_dependencies(
    target: &LoadedPackageAuditSnapshot,
    mapping: &npa_package::L2NamespaceTransportRequest,
) -> Result<Vec<PromotionPlanDependencyMapping>, Box<CommandDiagnostic>> {
    let mut result = Vec::new();
    for row in mapping
        .module_mappings
        .iter()
        .filter(|row| row.role == npa_package::L2TransportModuleRole::Dependency)
    {
        let module = target
            .snapshot
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == row.target.module)
            .ok_or_else(|| {
                policy_diagnostic(
                    "promotion_plan_mapping_stale",
                    &row.target.module.as_dotted(),
                )
            })?;
        result.push(PromotionPlanDependencyMapping {
            role: "dependency".to_owned(),
            source: endpoint(&row.source),
            target: endpoint(&row.target),
            declaration_mapping: row.declaration_mapping.clone(),
            renames: Vec::new(),
            target_certificate_file_hash: module.expected_certificate_file_hash,
            target_certificate_hash: module.expected_certificate_hash,
            target_export_hash: module.expected_export_hash,
        });
    }
    result.sort_by(|left, right| (&left.source, &left.target).cmp(&(&right.source, &right.target)));
    Ok(result)
}

pub(crate) fn project_equivalent_source(
    root: &std::path::Path,
    source: &LoadedPackageAuditSnapshot,
    canonical: &PromotionSourceOrigin,
) -> Result<PromotionSourceOrigin, Box<CommandDiagnostic>> {
    let manifest = source.snapshot.validated.manifest();
    let mut modules = Vec::new();
    for expected in &canonical.modules {
        let module = manifest
            .modules
            .iter()
            .find(|module| module.module == expected.module)
            .ok_or_else(|| {
                policy_diagnostic(
                    "promotion_plan_artifact_alias_already_promoted",
                    &expected.module.as_dotted(),
                )
            })?;
        let path = confined_governance_path(
            root,
            &module.source,
            module.source.as_str(),
            "promotion_plan_generated_identity_mismatch",
        )?;
        let actual = PromotionSourceModule {
            module: module.module.clone(),
            source_file_hash: package_file_hash(&fs::read(path).map_err(|_| {
                policy_diagnostic(
                    "promotion_plan_generated_identity_mismatch",
                    module.source.as_str(),
                )
            })?),
            certificate_file_hash: module.expected_certificate_file_hash,
            certificate_hash: module.expected_certificate_hash,
            export_hash: module.expected_export_hash,
        };
        if (
            &actual.source_file_hash,
            &actual.certificate_file_hash,
            &actual.certificate_hash,
            &actual.export_hash,
        ) != (
            &expected.source_file_hash,
            &expected.certificate_file_hash,
            &expected.certificate_hash,
            &expected.export_hash,
        ) {
            return Err(policy_diagnostic(
                "promotion_registry_source_identity_mismatch",
                &module.module.as_dotted(),
            ));
        }
        modules.push(actual);
    }
    Ok(PromotionSourceOrigin {
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        modules,
    })
}

fn endpoint(value: &npa_package::L2TransportEndpoint) -> PromotionPlanEndpoint {
    PromotionPlanEndpoint {
        origin: value.origin,
        package: value.package.clone(),
        version: value.version.clone(),
        module: value.module.clone(),
    }
}

fn export_kind(kind: ExportKind) -> &'static str {
    match kind {
        ExportKind::Axiom => "axiom",
        ExportKind::Def => "definition",
        ExportKind::Theorem => "theorem",
        ExportKind::Inductive => "inductive",
        ExportKind::Constructor => "constructor",
        ExportKind::Recursor => "recursor",
    }
}

fn read_workspace_file(
    path: &std::path::Path,
    reason: &str,
) -> Result<String, Box<CommandDiagnostic>> {
    fs::read_to_string(path).map_err(|_| policy_diagnostic(reason, &path.display().to_string()))
}

fn read_source_file(
    root: &std::path::Path,
    path: &PackagePath,
    reason: &str,
) -> Result<String, Box<CommandDiagnostic>> {
    let full = confined_governance_path(root, path, path.as_str(), reason)?;
    fs::read_to_string(full).map_err(|_| policy_diagnostic(reason, path.as_str()))
}

fn version_tuple(version: &PackageVersion) -> (u64, u64, u64) {
    let mut parts = version
        .as_str()
        .split('.')
        .map(|part| part.parse::<u64>().unwrap_or(0));
    (
        parts.next().unwrap_or(0),
        parts.next().unwrap_or(0),
        parts.next().unwrap_or(0),
    )
}

fn zero_hash() -> PackageHash {
    PackageHash::new([0; 32])
}

fn policy_diagnostic(reason: &str, path: &str) -> Box<CommandDiagnostic> {
    Box::new(CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path))
}

fn failure(root: &str, reason: &str, path: &str) -> CommandResult {
    CommandResult::failed(COMMAND, root, vec![*policy_diagnostic(reason, path)])
}
