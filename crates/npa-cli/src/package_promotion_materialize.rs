//! Deterministic package-generic mathlib promotion materialization.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_cert::{
    declaration_dependency_closure, resolve_verified_declaration_export, DeclarationClosureLimits,
    GlobalDeclarationIdentity, Name,
};
use npa_frontend::{
    collect_human_source_declaration_families, extract_human_declaration_source,
    parse_human_import_spans, parse_human_name_spans, FileId, HumanDeclarationFamilyMemberKind,
    HumanDeclarationSelection, HumanGlobalIdentity, HumanGlobalMapping, HumanGlobalMappingRow,
    HumanSelectedDeclaration, Span,
};
use npa_package::{
    format_package_hash, migrate_promotion_origin_registry_v1_to_v2, package_file_hash,
    parse_and_validate_manifest_str, parse_declaration_promotion_request_json,
    parse_l2_acceptance_policy_json, parse_l2_acceptance_v2_json,
    parse_l2_namespace_transport_attestation_json, parse_l2_namespace_transport_policy_json,
    parse_l2_namespace_transport_request_json, parse_mathlib_promotion_plan_json,
    parse_mathlib_promotion_plan_v2_json, parse_package_proof_replay,
    parse_promotion_transaction_json, parse_verified_materialization_attestation_json,
    promotion_plan_v2_dependency_edge_hash, promotion_transaction_path_hash,
    validate_declaration_registry_entry_admission, validate_package_path,
    validate_promotion_origin_registry_v1_to_v2_transition,
    validate_promotion_origin_registry_v2_transition, DeclarationClosureRegistryEntry,
    MathlibPromotionPlan, MathlibPromotionPlanV2, PackageArtifactOrigin, PackageHash, PackagePath,
    PackageProofReplay, PromotionAcceptanceEvidence, PromotionDeclarationEvidence,
    PromotionDeclarationTargetRevision, PromotionDeclarationTargetTheorem, PromotionEvidence,
    PromotionLifecycle, PromotionModuleRoute, PromotionOldFile, PromotionOriginEntry,
    PromotionOriginEntryV2, PromotionReplacementState, PromotionReplayOmission,
    PromotionRouteTheorem, PromotionSourceModule, PromotionSourceOrigin, PromotionTargetRevision,
    PromotionTransactionJournal, PromotionTransactionPhase, PromotionTransactionRow,
    PromotionTransactionState, PromotionTransportEvidence, MATHLIB_PROMOTION_PLAN_SCHEMA,
    MATHLIB_PROMOTION_REGISTRY_PATH, MATHLIB_PROMOTION_TRANSACTION_SCHEMA,
    PACKAGE_PUBLISH_PLAN_PATH, PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
    PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON,
};
use toml_edit::{Array, ArrayOfTables, DocumentMut, Item, Table};

use crate::{
    args::{
        PackageAxiomReportOptions, PackageBuildCertsOptions, PackageBuildCheckCacheMode,
        PackageBuildSelection, PackageCommonOptions, PackageExportSummaryOptions,
        PackageIndexOptions, PackageL2NamespaceTransportOptions, PackageLockCommand,
        PackageMaterializePromotionOptions, PackagePromotionPhase, PackagePublishPlanOptions,
        PackageTheoremPremiseReportOptions, PackageTimingMode,
        PackageValidatePromotionMaterializationOptions,
        PackageValidatePromotionOriginRegistryOptions,
    },
    diagnostic::{
        CommandArtifact, CommandDiagnostic, CommandResult, CommandStatus, DiagnosticKind,
    },
    fs::render_package_root,
    governance_writer::confined_governance_path,
    package_artifacts::{
        load_package_audit_snapshot, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
        PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH, PACKAGE_THEOREM_PREMISE_REPORT_PATH,
    },
    package_axiom_report::run_package_axiom_report,
    package_build::run_package_build_certs,
    package_export_summary::run_package_export_summary,
    package_index::run_package_index,
    package_l2_acceptance_aggregate::validate_l2_acceptance_v2_current,
    package_l2_namespace_transport::run_package_validate_l2_namespace_transport,
    package_lock::run_package_lock_command,
    package_promotion_materialization_validate::run_package_validate_promotion_materialization,
    package_promotion_prepare::{
        project_equivalent_source, promotion_mapping_source_is_current,
        promotion_selected_target_artifact_paths,
    },
    package_promotion_prepare_declaration::{
        direct_import_interfaces, endpoint_record, plan_declarations, plan_roots,
        read_declaration_source, reconcile_families, registry_owns_active_target, resolve_roots,
        DeclarationSourceExtractionError,
    },
    package_promotion_registry::{
        parse_promotion_origin_registry_versioned, promotion_plan_generated_read_mode,
        run_package_validate_promotion_origin_registry, validate_checked_generated,
        ParsedPromotionOriginRegistry,
    },
    package_promotion_transaction::TargetLock,
    package_publish::run_package_publish_plan,
    package_theorem_premise_report::run_package_theorem_premise_report,
};

const COMMAND: &str = "package materialize-promotion";
const TARGET_LOCK_PREFIX: &str = ".npa-promotion-lock-";

#[derive(Clone)]
struct Change {
    path: PackagePath,
    old: Option<Vec<u8>>,
    new: Vec<u8>,
}

struct MaterializationSourceModule {
    source: String,
    replay: PackageProofReplay,
}

struct MaterializationSourceSnapshot {
    modules: BTreeMap<npa_cert::Name, MaterializationSourceModule>,
}

struct PreservedTargetModules {
    artifacts: BTreeMap<PackagePath, Vec<u8>>,
    manifest_source: String,
}

/// Validate, dry-run, apply, or recover one promotion materialization.
pub fn run_package_materialize_promotion(
    options: PackageMaterializePromotionOptions,
) -> CommandResult {
    if let Some(journal) = &options.recover {
        return recover_transaction(&options.target_root, journal);
    }
    materialize_normal(options)
}

fn is_declaration_promotion_plan(source: &str) -> bool {
    parse_mathlib_promotion_plan_v2_json(source).is_ok()
}

fn materialize_normal(options: PackageMaterializePromotionOptions) -> CommandResult {
    let root_display = render_package_root(&options.target_root);
    let Some(baseline_root) = options.target_baseline_root.as_ref() else {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            "--target-baseline-root",
        );
    };
    if options.apply
        && fs::canonicalize(&options.target_root).ok() == fs::canonicalize(baseline_root).ok()
    {
        return failure(
            &root_display,
            "promotion_materialize_baseline_mismatch",
            "--target-baseline-root",
        );
    }
    let Some(plan_arg) = options.plan.as_ref() else {
        return failure(&root_display, "promotion_materialize_plan_stale", "--plan");
    };
    let plan_path = PackagePath::new(plan_arg.to_string_lossy());
    let Some(phase) = options.phase else {
        return failure(&root_display, "promotion_materialize_plan_stale", "--phase");
    };
    let plan_bytes = match read_confined(&options.common.root, &plan_path) {
        Ok(bytes) => bytes,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_plan_stale",
                plan_path.as_str(),
            )
        }
    };
    let plan_source = match String::from_utf8(plan_bytes.clone()) {
        Ok(source) => source,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_plan_stale",
                plan_path.as_str(),
            )
        }
    };
    if is_declaration_promotion_plan(&plan_source) {
        return materialize_declaration_normal(options, plan_path, plan_bytes, plan_source);
    }
    let plan = match parse_mathlib_promotion_plan_json(&plan_source) {
        Ok(plan) => plan,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_plan_stale",
                plan_path.as_str(),
            )
        }
    };
    if options.apply && pending_transaction_exists(&options.target_root) {
        return failure(
            &root_display,
            "promotion_recovery_required",
            "--target-root",
        );
    }
    let source = match load_package_audit_snapshot(
        &options.common.root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    let baseline = match load_package_audit_snapshot(
        baseline_root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    for snapshot in [&source, &baseline] {
        if let Err(diagnostic) = validate_checked_generated(snapshot) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    if !snapshot_matches_plan(&source, &plan, true)
        || !snapshot_matches_plan(&baseline, &plan, false)
    {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            plan_path.as_str(),
        );
    }
    if !validate_equivalent_origins(&options.equivalent_origin_roots, &plan) {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            "--equivalent-origin-root",
        );
    }
    let materialization_source =
        match capture_materialization_source(&options.common.root, &source, &plan) {
            Some(snapshot) => snapshot,
            None => {
                return failure(
                    &root_display,
                    "promotion_materialize_plan_stale",
                    plan_path.as_str(),
                )
            }
        };
    if !revalidate_plan_inputs(
        &options.common.root,
        baseline_root,
        &source,
        &baseline,
        &materialization_source,
        &plan,
    ) {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            plan_path.as_str(),
        );
    }
    let captured_target = match tree_snapshot(&options.target_root) {
        Ok(files) => files,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_target_not_clean",
                "--target-root",
            )
        }
    };
    let baseline_files = match tree_snapshot(baseline_root) {
        Ok(files) => files,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_baseline_mismatch",
                "--target-baseline-root",
            )
        }
    };
    if captured_target != baseline_files {
        return failure(
            &root_display,
            "promotion_materialize_target_not_clean",
            "--target-root",
        );
    }
    if let Some(collision) = promotion_selected_target_artifact_paths(&plan.selected_modules)
        .iter()
        .find(|path| {
            !target_path_is_absent(baseline_root, path)
                || !target_path_is_absent(&options.target_root, path)
        })
    {
        return failure(
            &root_display,
            "promotion_plan_target_artifact_collision",
            collision.as_str(),
        );
    }
    let registry_bytes = baseline_files
        .get(&PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH))
        .cloned()
        .unwrap_or_default();
    if package_file_hash(&registry_bytes) != plan.governance.registry_file_hash {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }

    let parent = options
        .target_root
        .parent()
        .unwrap_or_else(|| Path::new("."));
    let stage = parent.join(format!(
        ".npa-promotion-stage-{}-{}",
        std::process::id(),
        short_hash(plan.promotion_id)
    ));
    if write_tree_snapshot(&captured_target, &stage).is_err() {
        return failure(
            &root_display,
            "promotion_concurrent_update",
            "--target-root",
        );
    }
    let build_result = materialize_stage(&materialization_source, &stage, &plan);
    if let Err(reason) = build_result {
        let _ = fs::remove_dir_all(&stage);
        return failure(&root_display, reason, "--plan");
    }
    let attestation = if phase == PackagePromotionPhase::Tracked {
        let Some(attestation_arg) = options.transport_attestation.as_ref() else {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_materialize_transport_attestation_required",
                "--transport-attestation",
            );
        };
        let path = PackagePath::new(attestation_arg.to_string_lossy());
        let bytes = match read_confined(&options.common.root, &path) {
            Ok(bytes) => bytes,
            Err(_) => {
                let _ = fs::remove_dir_all(&stage);
                return failure(
                    &root_display,
                    "promotion_materialize_transport_attestation_stale",
                    path.as_str(),
                );
            }
        };
        let source = match String::from_utf8(bytes.clone()) {
            Ok(source) => source,
            Err(_) => {
                let _ = fs::remove_dir_all(&stage);
                return failure(
                    &root_display,
                    "promotion_materialize_transport_attestation_stale",
                    path.as_str(),
                );
            }
        };
        let transport_check =
            run_package_validate_l2_namespace_transport(PackageL2NamespaceTransportOptions {
                common: PackageCommonOptions {
                    root: options.common.root.clone(),
                    json: false,
                },
                target_baseline_root: baseline_root.clone(),
                target_root: stage.clone(),
                acceptance_policy: baseline_root.join("policy/l2-acceptance-policy.json"),
                source_acceptance: PathBuf::from(plan.governance.source_acceptance_path.as_str()),
                transport_policy: baseline_root.join("policy/l2-namespace-transport-policy.json"),
                mapping: PathBuf::from(plan.governance.mapping_path.as_str()),
                out: Some(PathBuf::from(path.as_str())),
                check: true,
            });
        if transport_check.status != CommandStatus::Passed {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_materialize_transport_attestation_stale",
                path.as_str(),
            );
        }
        let parsed = match parse_l2_namespace_transport_attestation_json(&source) {
            Ok(parsed) => parsed,
            Err(_) => {
                let _ = fs::remove_dir_all(&stage);
                return failure(
                    &root_display,
                    "promotion_materialize_transport_attestation_stale",
                    path.as_str(),
                );
            }
        };
        if !attestation_matches(&parsed, &plan, baseline_root, &stage) {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_materialize_transport_attestation_stale",
                path.as_str(),
            );
        }
        if update_stage_registry(
            &stage,
            &plan_path,
            &plan_bytes,
            &path,
            &bytes,
            &plan,
            &parsed,
        )
        .is_err()
        {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_registry_transition_not_append_only",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            );
        }
        Some((path, parsed))
    } else {
        None
    };
    let staged_files = match tree_snapshot(&stage) {
        Ok(files) => files,
        Err(_) => {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_materialize_target_identity_mismatch",
                "--target-root",
            );
        }
    };
    if let Some(unexpected_removal) = captured_target
        .keys()
        .find(|path| !staged_files.contains_key(path))
    {
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            "promotion_materialize_unscoped_path",
            unexpected_removal.as_str(),
        );
    }
    let mut changes = diff_snapshots(&captured_target, &staged_files);
    changes.sort_by_key(change_order);
    if let Some(unscoped) = changes
        .iter()
        .find(|change| !change_is_scoped(change, &plan, phase))
    {
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            "promotion_materialize_unscoped_path",
            unscoped.path.as_str(),
        );
    }
    if !options.apply {
        let _ = fs::remove_dir_all(&stage);
        let mut result = CommandResult::passed(COMMAND, root_display);
        for change in changes {
            result.artifacts.push(CommandArtifact {
                kind: if change.old.is_some() {
                    "promotion_replace"
                } else {
                    "promotion_create"
                }
                .to_owned(),
                path: change.path.as_str().to_owned(),
            });
        }
        return result;
    }
    let _attestation = attestation;
    let mut lock = match TargetLock::acquire(&options.target_root) {
        Ok(lock) => lock,
        Err(_) => {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_concurrent_update",
                TARGET_LOCK_PREFIX,
            );
        }
    };
    if let Err(reason) = locked_apply_preflight(&options.target_root, &captured_target) {
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(&root_display, reason, "--target-root");
    }
    let transaction = match transaction_path(&options.target_root, plan.promotion_id) {
        Ok(path) => path,
        Err(_) => {
            drop(lock);
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_materialize_unscoped_path",
                "--target-root",
            );
        }
    };
    let journal_name = transaction
        .file_name()
        .and_then(|name| name.to_str())
        .map(str::to_owned);
    if lock
        .record(
            Some(plan.promotion_id),
            "materialize",
            journal_name.as_deref(),
        )
        .is_err()
    {
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            "promotion_concurrent_update",
            TARGET_LOCK_PREFIX,
        );
    }
    let mut transaction_visible = false;
    let apply = apply_transaction(
        &options.target_root,
        phase,
        plan.promotion_id,
        &changes,
        &mut transaction_visible,
    );
    if apply.is_err() {
        let rolled_back = !transaction_visible
            || rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_concurrent_update"
            } else {
                "promotion_recovery_required"
            },
            "--target-root",
        );
    }
    if tree_snapshot(&options.target_root).ok().as_ref() != Some(&staged_files) {
        let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_materialize_target_identity_mismatch"
            } else {
                "promotion_recovery_required"
            },
            "--target-root",
        );
    }
    let written = match load_package_audit_snapshot(
        &options.target_root,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(_) => {
            let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
            drop(lock);
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                if rolled_back {
                    "promotion_materialize_target_identity_mismatch"
                } else {
                    "promotion_recovery_required"
                },
                "--target-root",
            );
        }
    };
    if validate_checked_generated(&written).is_err() {
        let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_materialize_target_identity_mismatch"
            } else {
                "promotion_recovery_required"
            },
            "--target-root",
        );
    }
    if phase == PackagePromotionPhase::Tracked
        && run_package_validate_promotion_origin_registry(
            PackageValidatePromotionOriginRegistryOptions {
                common: PackageCommonOptions {
                    root: options.target_root.clone(),
                    json: false,
                },
                source_roots: std::iter::once(options.common.root.clone())
                    .chain(options.equivalent_origin_roots.iter().cloned())
                    .collect(),
                previous_registry: None,
            },
        )
        .status
            != CommandStatus::Passed
    {
        let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_registry_target_identity_mismatch"
            } else {
                "promotion_recovery_required"
            },
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    if finalize_transaction(&transaction).is_err() {
        drop(lock);
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            "promotion_recovery_required",
            "--target-root",
        );
    }
    let _ = lock.record(Some(plan.promotion_id), "materialize", None);
    let _ = fs::remove_dir_all(&stage);
    drop(lock);
    let mut result = CommandResult::passed(COMMAND, root_display);
    for change in changes {
        result.artifacts.push(CommandArtifact {
            kind: if change.old.is_some() {
                "promotion_replace"
            } else {
                "promotion_create"
            }
            .to_owned(),
            path: change.path.as_str().to_owned(),
        });
    }
    result
}

fn materialize_stage(
    source_snapshot: &MaterializationSourceSnapshot,
    stage: &Path,
    plan: &MathlibPromotionPlan,
) -> Result<(), &'static str> {
    let preserved_modules = capture_existing_module_artifacts(stage)?;
    let mut import_map = BTreeMap::new();
    for module in &plan.selected_modules {
        import_map.insert(
            module.source_module.as_dotted(),
            module.target_module.as_dotted(),
        );
    }
    for mapping in &plan.dependency_mappings {
        import_map.insert(
            mapping.source.module.as_dotted(),
            mapping.target.module.as_dotted(),
        );
    }
    for module in &plan.selected_modules {
        let captured = source_snapshot
            .modules
            .get(&module.source_module)
            .ok_or("promotion_materialize_source_rewrite_failed")?;
        let rewritten = rewrite_imports(&captured.source, &import_map)?;
        let target_dir = stage.join(module.target_module.as_dotted().replace('.', "/"));
        fs::create_dir_all(&target_dir)
            .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
        fs::write(target_dir.join("source.npa"), rewritten)
            .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
        fs::write(
            target_dir.join("replay.json"),
            source_replay_json(captured, &module.target_module)?,
        )
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    }
    edit_manifest(stage, plan, &import_map)?;
    // Selected modules must bind to the preserved baseline certificate for an
    // existing target dependency, not to a transient rebuild of that module.
    externalize_preserved_dependencies(stage, plan, &preserved_modules)?;
    let common = PackageCommonOptions {
        root: stage.to_path_buf(),
        json: false,
    };
    let build = run_package_build_certs(PackageBuildCertsOptions {
        common: common.clone(),
        check: false,
        build_check_cache: PackageBuildCheckCacheMode::Off,
        update_manifest_hashes: true,
        selection: PackageBuildSelection::Full,
    });
    if build.status != CommandStatus::Passed {
        return Err("promotion_materialize_compile_failed");
    }
    restore_existing_module_artifacts(stage, plan, &preserved_modules)?;
    let lock = run_package_lock_command(PackageLockCommand::Write(common.clone()));
    if lock.status != CommandStatus::Passed {
        return Err("promotion_materialize_target_identity_mismatch");
    }
    let axiom = run_package_axiom_report(PackageAxiomReportOptions {
        common: common.clone(),
        check: false,
        timings: PackageTimingMode::Off,
    });
    let index = run_package_index(PackageIndexOptions {
        common: common.clone(),
        check: false,
        timings: PackageTimingMode::Off,
    });
    if axiom.status != CommandStatus::Passed || index.status != CommandStatus::Passed {
        return Err("promotion_materialize_target_identity_mismatch");
    }
    write_meta_sidecars(stage, plan)?;
    // Keep disposable and tracked materializations byte-identical before the
    // tracked-only registry update. Build-certs invalidates these generated
    // files after the manifest changes, so both phases must regenerate them.
    let export = run_package_export_summary(PackageExportSummaryOptions {
        common: common.clone(),
        out: None,
        check: false,
        timings: PackageTimingMode::Off,
    });
    let publish = run_package_publish_plan(PackagePublishPlanOptions {
        common,
        check: false,
        timings: PackageTimingMode::Off,
    });
    if export.status != CommandStatus::Passed || publish.status != CommandStatus::Passed {
        return Err("promotion_materialize_target_identity_mismatch");
    }
    Ok(())
}

fn capture_existing_module_artifacts(stage: &Path) -> Result<PreservedTargetModules, &'static str> {
    let manifest_source = fs::read_to_string(stage.join("npa-package.toml"))
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let manifest = parse_and_validate_manifest_str(&manifest_source)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .into_manifest();
    let mut artifacts = BTreeMap::new();
    for module in manifest.modules {
        let paths = [
            (Some(module.source), true),
            (Some(module.certificate), true),
            (module.meta, false),
            (module.replay, false),
        ];
        for (path, required) in paths {
            let Some(path) = path else {
                continue;
            };
            match fs::read(stage.join(path.as_str())) {
                Ok(bytes) => {
                    artifacts.insert(path, bytes);
                }
                Err(error) if !required && error.kind() == io::ErrorKind::NotFound => {}
                Err(_) => return Err("promotion_materialize_target_identity_mismatch"),
            }
        }
    }
    Ok(PreservedTargetModules {
        artifacts,
        manifest_source,
    })
}

fn restore_existing_module_artifacts(
    stage: &Path,
    plan: &MathlibPromotionPlan,
    preserved: &PreservedTargetModules,
) -> Result<(), &'static str> {
    for (path, bytes) in &preserved.artifacts {
        let full = stage.join(path.as_str());
        if let Some(parent) = full.parent() {
            fs::create_dir_all(parent)
                .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
        }
        fs::write(full, bytes).map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    }
    let manifest_path = stage.join("npa-package.toml");
    let built_document = fs::read_to_string(&manifest_path)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let built_tables = built_document["modules"]
        .as_array_of_tables()
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    let selected_names = plan
        .selected_modules
        .iter()
        .map(|module| module.target_module.as_dotted())
        .collect::<BTreeSet<_>>();
    let selected_tables = built_tables
        .iter()
        .filter(|table| {
            table
                .get("module")
                .and_then(Item::as_str)
                .is_some_and(|module| selected_names.contains(module))
        })
        .cloned()
        .collect::<Vec<_>>();
    if selected_tables.len() != selected_names.len() {
        return Err("promotion_materialize_target_identity_mismatch");
    }
    // Rebuild the final manifest from the preserved baseline so unrelated
    // tables, comments, and hash pins remain byte-for-byte governed by it.
    let mut document = preserved
        .manifest_source
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    document["version"] = toml_edit::value(plan.target_baseline.planned_version.as_str());
    let tables = document["modules"]
        .as_array_of_tables_mut()
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    for table in selected_tables {
        tables.push(table);
    }
    fs::write(manifest_path, document.to_string())
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    Ok(())
}

fn externalize_preserved_dependencies(
    stage: &Path,
    plan: &MathlibPromotionPlan,
    preserved: &PreservedTargetModules,
) -> Result<(), &'static str> {
    if plan.dependency_mappings.is_empty() {
        return Ok(());
    }
    let preserved_manifest = parse_and_validate_manifest_str(&preserved.manifest_source)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .into_manifest();
    let dependency_names = plan
        .dependency_mappings
        .iter()
        .map(|mapping| mapping.target.module.as_dotted())
        .collect::<BTreeSet<_>>();
    let dependency_modules = dependency_names
        .iter()
        .map(|name| {
            preserved_manifest
                .modules
                .iter()
                .find(|module| module.module.as_dotted() == *name)
                .ok_or("promotion_materialize_target_identity_mismatch")
        })
        .collect::<Result<Vec<_>, _>>()?;

    let manifest_path = stage.join("npa-package.toml");
    let mut document = fs::read_to_string(&manifest_path)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let current_tables = document["modules"]
        .as_array_of_tables()
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    let mut build_tables = ArrayOfTables::new();
    for table in current_tables.iter() {
        let module = table
            .get("module")
            .and_then(Item::as_str)
            .ok_or("promotion_materialize_target_identity_mismatch")?;
        if !dependency_names.contains(module) {
            build_tables.push(table.clone());
        }
    }
    document["modules"] = Item::ArrayOfTables(build_tables);
    let imports = import_tables_mut(&mut document)?;
    for module in dependency_modules {
        let mut table = Table::new();
        table["module"] = toml_edit::value(module.module.as_dotted());
        table["package"] = toml_edit::value(plan.target_baseline.package.as_str());
        table["version"] = toml_edit::value(plan.target_baseline.version.as_str());
        table["certificate"] = toml_edit::value(module.certificate.as_str());
        table["export_hash"] = toml_edit::value(format_package_hash(&module.expected_export_hash));
        table["certificate_hash"] =
            toml_edit::value(format_package_hash(&module.expected_certificate_hash));
        imports.push(table);
    }
    fs::write(manifest_path, document.to_string())
        .map_err(|_| "promotion_materialize_target_identity_mismatch")
}

fn rewrite_imports(
    source: &str,
    mapping: &BTreeMap<String, String>,
) -> Result<String, &'static str> {
    let spans = parse_human_import_spans(FileId(0), source)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    let names = parse_human_name_spans(FileId(0), source)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    if names.iter().any(|name| {
        !spans.iter().any(|import| import.module_span == name.span)
            && mapping
                .keys()
                .any(|mapped| name.name == *mapped || name.name.starts_with(&format!("{mapped}.")))
    }) {
        return Err("promotion_materialize_source_rewrite_failed");
    }
    let mut out = source.to_owned();
    for span in spans.into_iter().rev() {
        if let Some(target) = mapping.get(&span.module) {
            out.replace_range(
                span.module_span.start.0 as usize..span.module_span.end.0 as usize,
                target,
            );
        }
    }
    parse_human_import_spans(FileId(0), &out)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    Ok(out)
}

fn edit_manifest(
    stage: &Path,
    plan: &MathlibPromotionPlan,
    mapping: &BTreeMap<String, String>,
) -> Result<(), &'static str> {
    let path = stage.join("npa-package.toml");
    let source =
        fs::read_to_string(&path).map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let mut document = source
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    document["version"] = toml_edit::value(plan.target_baseline.planned_version.as_str());
    if !document.as_table().contains_key("modules")
        || document["modules"]
            .as_array()
            .is_some_and(|modules| modules.is_empty())
    {
        document["modules"] = Item::ArrayOfTables(ArrayOfTables::new());
    }
    let tables = document["modules"]
        .as_array_of_tables_mut()
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    for selected in selected_topological_order(&plan.selected_modules)? {
        let base = selected.target_module.as_dotted().replace('.', "/");
        let mut table = Table::new();
        table["module"] = toml_edit::value(selected.target_module.as_dotted());
        table["source"] = toml_edit::value(format!("{base}/source.npa"));
        table["certificate"] = toml_edit::value(format!("{base}/certificate.npcert"));
        table["meta"] = toml_edit::value(format!("{base}/meta.json"));
        table["replay"] = toml_edit::value(format!("{base}/replay.json"));
        table["producer_profile"] = toml_edit::value("human-surface-explicit-term");
        for field in [
            "expected_source_hash",
            "expected_certificate_file_hash",
            "expected_export_hash",
            "expected_axiom_report_hash",
            "expected_certificate_hash",
        ] {
            table[field] = toml_edit::value(format_package_hash(&PackageHash::new([0; 32])));
        }
        let mut imports = Array::new();
        for import in &selected.imports {
            let source = import.as_dotted();
            imports.push(mapping.get(&source).cloned().unwrap_or(source));
        }
        table["imports"] = Item::Value(imports.into());
        let mut theorems = Array::new();
        let mut definitions = Array::new();
        let mut inductives = Array::new();
        let mut axioms = Array::new();
        for theorem in &selected.theorems {
            theorems.push(theorem.target_name.as_dotted());
        }
        for export in &selected.exports {
            match export.kind.as_str() {
                "definition" => definitions.push(export.target_name.as_dotted()),
                "inductive" => inductives.push(export.target_name.as_dotted()),
                "axiom" => axioms.push(export.target_name.as_dotted()),
                _ => {}
            }
        }
        table["theorems"] = Item::Value(theorems.into());
        if !inductives.is_empty() {
            table["inductives"] = Item::Value(inductives.into());
        }
        table["definitions"] = Item::Value(definitions.into());
        table["axioms"] = Item::Value(axioms.into());
        tables.push(table);
    }
    fs::write(path, document.to_string())
        .map_err(|_| "promotion_materialize_target_identity_mismatch")
}

fn selected_topological_order(
    selected_modules: &[npa_package::PromotionPlanSelectedModule],
) -> Result<Vec<&npa_package::PromotionPlanSelectedModule>, &'static str> {
    let by_source = selected_modules
        .iter()
        .enumerate()
        .map(|(index, module)| (module.source_module.as_dotted(), index))
        .collect::<BTreeMap<_, _>>();
    let mut dependency_count = vec![0_usize; selected_modules.len()];
    let mut dependents = vec![Vec::new(); selected_modules.len()];
    for (index, module) in selected_modules.iter().enumerate() {
        for import in &module.imports {
            if let Some(&dependency) = by_source.get(&import.as_dotted()) {
                dependency_count[index] += 1;
                dependents[dependency].push(index);
            }
        }
    }
    let mut ready = selected_modules
        .iter()
        .enumerate()
        .filter(|(index, _)| dependency_count[*index] == 0)
        .map(|(index, module)| (module.target_module.as_dotted(), index))
        .collect::<BTreeSet<_>>();
    let mut ordered = Vec::with_capacity(selected_modules.len());
    while let Some((_, index)) = ready.pop_first() {
        ordered.push(&selected_modules[index]);
        for &dependent in &dependents[index] {
            dependency_count[dependent] -= 1;
            if dependency_count[dependent] == 0 {
                ready.insert((
                    selected_modules[dependent].target_module.as_dotted(),
                    dependent,
                ));
            }
        }
    }
    if ordered.len() != selected_modules.len() {
        return Err("promotion_materialize_import_mapping_incomplete");
    }
    Ok(ordered)
}

fn write_meta_sidecars(stage: &Path, plan: &MathlibPromotionPlan) -> Result<(), &'static str> {
    let loaded = crate::package::load_package_root(stage, COMMAND)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    for selected in &plan.selected_modules {
        let module = loaded
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == selected.target_module)
            .ok_or("promotion_materialize_target_identity_mismatch")?;
        let declarations = selected
            .exports
            .iter()
            .filter(|export| {
                matches!(
                    export.kind.as_str(),
                    "axiom" | "definition" | "theorem" | "inductive"
                )
            })
            .map(|export| {
                format!(
                    "    {{\n      \"name\": \"{}\",\n      \"kind\": \"{}\"\n    }}",
                    export.target_name.as_dotted(),
                    if export.kind == "definition" {
                        "def"
                    } else {
                        export.kind.as_str()
                    }
                )
            })
            .collect::<Vec<_>>()
            .join(",\n");
        let imports = module
            .imports
            .iter()
            .map(|name| format!("\"{}\"", name.as_dotted()))
            .collect::<Vec<_>>()
            .join(", ");
        let axioms = module
            .axioms
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|name| format!("\"{}\"", name.as_dotted()))
            .collect::<Vec<_>>()
            .join(", ");
        let json = format!(
            "{{\n  \"schema\": \"npa-ai-proof-meta-v0.1\",\n  \"module\": \"{}\",\n  \"source\": \"{}\",\n  \"certificate\": \"{}\",\n  \"producer_profile\": \"human-surface-explicit-term\",\n  \"trusted_status\": \"verified_by_certificate\",\n  \"source_sha256\": \"{}\",\n  \"certificate_file_sha256\": \"{}\",\n  \"export_hash\": \"{}\",\n  \"axiom_report_hash\": \"{}\",\n  \"certificate_hash\": \"{}\",\n  \"imports\": [{}],\n  \"axioms\": [{}],\n  \"declarations\": [\n{}\n  ],\n  \"trust_boundary\": \"source, replay, and metadata are non-trusted sidecars; only the canonical certificate verified by npa-cert is accepted\"\n}}\n",
            module.module.as_dotted(), module.source.as_str(), module.certificate.as_str(),
            format_package_hash(&module.expected_source_hash), format_package_hash(&module.expected_certificate_file_hash),
            format_package_hash(&module.expected_export_hash), format_package_hash(&module.expected_axiom_report_hash),
            format_package_hash(&module.expected_certificate_hash), imports, axioms, declarations
        );
        let path = module
            .meta
            .as_ref()
            .ok_or("promotion_materialize_target_identity_mismatch")?;
        fs::write(stage.join(path.as_str()), json)
            .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    }
    Ok(())
}

fn source_replay_json(
    captured: &MaterializationSourceModule,
    target_module: &npa_cert::Name,
) -> Result<String, &'static str> {
    let mut replay = captured.replay.clone();
    replay.module = target_module.clone();
    if replay.accepted_artifact.is_some() {
        replay.accepted_artifact = Some(PackagePath::new(format!(
            "{}/certificate.npcert",
            target_module.as_dotted().replace('.', "/")
        )));
    }
    Ok(replay.canonical_json())
}

fn snapshot_matches_plan(
    snapshot: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    plan: &MathlibPromotionPlan,
    source: bool,
) -> bool {
    let manifest = snapshot.snapshot.validated.manifest();
    let (package, version, manifest_hash, lock_hash, axiom_hash, theorem_hash) = if source {
        (
            &plan.source.package,
            &plan.source.version,
            plan.source.manifest_file_hash,
            plan.source.lock_file_hash,
            plan.source.axiom_report_file_hash,
            plan.source.theorem_index_file_hash,
        )
    } else {
        (
            &plan.target_baseline.package,
            &plan.target_baseline.version,
            plan.target_baseline.manifest_file_hash,
            plan.target_baseline.lock_file_hash,
            plan.target_baseline.axiom_report_file_hash,
            plan.target_baseline.theorem_index_file_hash,
        )
    };
    manifest.package == *package
        && manifest.version == *version
        && snapshot.snapshot.manifest.file_hash == manifest_hash
        && package_file_hash(snapshot.package_lock_json.as_bytes()) == lock_hash
        && snapshot
            .checked_generated
            .axiom_report_json
            .as_deref()
            .is_some_and(|bytes| package_file_hash(bytes.as_bytes()) == axiom_hash)
        && snapshot
            .checked_generated
            .theorem_index_json
            .as_deref()
            .is_some_and(|bytes| package_file_hash(bytes.as_bytes()) == theorem_hash)
}

fn validate_equivalent_origins(roots: &[PathBuf], plan: &MathlibPromotionPlan) -> bool {
    if roots.len() != plan.equivalent_sources.len() {
        return false;
    }
    let canonical = PromotionSourceOrigin {
        package: plan.source.package.clone(),
        version: plan.source.version.clone(),
        modules: plan
            .selected_modules
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
    let mut actual = Vec::with_capacity(roots.len());
    for root in roots {
        let loaded = match load_package_audit_snapshot(
            root,
            COMMAND,
            promotion_plan_generated_read_mode(),
            PackageArtifactReferenceSummaryMode::Include,
        ) {
            Ok(loaded) => loaded,
            Err(_) => return false,
        };
        if validate_checked_generated(&loaded).is_err() {
            return false;
        }
        match project_equivalent_source(root, &loaded, &canonical) {
            Ok(origin) => actual.push(origin),
            Err(_) => return false,
        }
    }
    actual.sort_by(|left, right| {
        (&left.package, &left.version).cmp(&(&right.package, &right.version))
    });
    actual == plan.equivalent_sources
}

fn capture_materialization_source(
    root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    plan: &MathlibPromotionPlan,
) -> Option<MaterializationSourceSnapshot> {
    let manifest = source.snapshot.validated.manifest();
    let mut modules = BTreeMap::new();
    for selected in &plan.selected_modules {
        let module = manifest
            .modules
            .iter()
            .find(|module| module.module == selected.source_module)?;
        if module.source != selected.source_path {
            return None;
        }
        let source_path = confined_governance_path(
            root,
            &module.source,
            module.source.as_str(),
            "promotion_materialize_source_rewrite_failed",
        )
        .ok()?;
        let source_bytes = fs::read(source_path).ok()?;
        if package_file_hash(&source_bytes) != selected.source_file_hash {
            return None;
        }
        let replay_path = module.replay.as_ref()?;
        let replay_path = confined_governance_path(
            root,
            replay_path,
            replay_path.as_str(),
            "promotion_materialize_source_rewrite_failed",
        )
        .ok()?;
        modules.insert(
            selected.source_module.clone(),
            MaterializationSourceModule {
                source: String::from_utf8(source_bytes).ok()?,
                replay: {
                    let replay =
                        parse_package_proof_replay(&fs::read_to_string(replay_path).ok()?).ok()?;
                    if replay.module != selected.source_module
                        || replay
                            .accepted_artifact
                            .as_ref()
                            .is_some_and(|artifact| artifact != &module.certificate)
                    {
                        return None;
                    }
                    replay
                },
            },
        );
    }
    Some(MaterializationSourceSnapshot { modules })
}

fn revalidate_plan_inputs(
    source_root: &Path,
    baseline_root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    baseline: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    materialization_source: &MaterializationSourceSnapshot,
    plan: &MathlibPromotionPlan,
) -> bool {
    let acceptance_policy_path = baseline_root.join("policy/l2-acceptance-policy.json");
    let transport_policy_path = baseline_root.join("policy/l2-namespace-transport-policy.json");
    let acceptance_policy_bytes = match fs::read(&acceptance_policy_path) {
        Ok(bytes) => bytes,
        Err(_) => return false,
    };
    let transport_policy_bytes = match fs::read(&transport_policy_path) {
        Ok(bytes) => bytes,
        Err(_) => return false,
    };
    let acceptance_bytes = match read_confined(source_root, &plan.governance.source_acceptance_path)
    {
        Ok(bytes) => bytes,
        Err(_) => return false,
    };
    let mapping_bytes = match read_confined(source_root, &plan.governance.mapping_path) {
        Ok(bytes) => bytes,
        Err(_) => return false,
    };
    if package_file_hash(&acceptance_policy_bytes) != plan.governance.acceptance_policy_file_hash
        || package_file_hash(&transport_policy_bytes) != plan.governance.transport_policy_file_hash
        || package_file_hash(&acceptance_bytes) != plan.governance.source_acceptance_file_hash
        || package_file_hash(&mapping_bytes) != plan.governance.mapping_file_hash
    {
        return false;
    }
    let policy_source = match std::str::from_utf8(&acceptance_policy_bytes) {
        Ok(source) => source,
        Err(_) => return false,
    };
    let transport_source = match std::str::from_utf8(&transport_policy_bytes) {
        Ok(source) => source,
        Err(_) => return false,
    };
    let acceptance_source = match std::str::from_utf8(&acceptance_bytes) {
        Ok(source) => source,
        Err(_) => return false,
    };
    let mapping_source = match std::str::from_utf8(&mapping_bytes) {
        Ok(source) => source,
        Err(_) => return false,
    };
    let policy = match parse_l2_acceptance_policy_json(policy_source) {
        Ok(policy) => policy,
        Err(_) => return false,
    };
    let transport = match parse_l2_namespace_transport_policy_json(transport_source) {
        Ok(policy) => policy,
        Err(_) => return false,
    };
    let acceptance = match parse_l2_acceptance_v2_json(acceptance_source) {
        Ok(acceptance) => acceptance,
        Err(_) => return false,
    };
    let mapping = match parse_l2_namespace_transport_request_json(mapping_source) {
        Ok(mapping) => mapping,
        Err(_) => return false,
    };
    let loaded_source = match crate::package::load_package_root(source_root, COMMAND) {
        Ok(loaded) => loaded,
        Err(_) => return false,
    };
    if validate_l2_acceptance_v2_current(
        &loaded_source,
        &acceptance,
        &policy,
        plan.governance.acceptance_policy_file_hash,
    )
    .is_err()
        || policy.policy_id != plan.governance.acceptance_policy_id
        || policy.policy_version != plan.governance.acceptance_policy_version
        || transport.policy_id != plan.governance.transport_policy_id
        || transport.policy_version != plan.governance.transport_policy_version
        || mapping.source.package != plan.source.package
        || mapping.source.version != plan.source.version
        || mapping.target.package != plan.target_baseline.package
        || mapping.target.version != plan.target_baseline.planned_version
    {
        return false;
    }
    if transport.source_acceptance_policy_id != policy.policy_id
        || transport.source_acceptance_policy_version != policy.policy_version
        || transport.source_acceptance_policy_file_hash
            != plan.governance.acceptance_policy_file_hash
        || transport.target_package != plan.target_baseline.package
        || mapping.module_mappings.iter().any(|row| {
            !row.renames.is_empty()
                || row.declaration_mapping != "same-name-except-explicit"
                || !promotion_mapping_source_is_current(
                    source.snapshot.validated.manifest(),
                    &mapping,
                    row,
                )
                || row.target.package != mapping.target.package
                || row.target.version != mapping.target.version
                || row.target.origin != npa_package::PackageArtifactOrigin::Local
                || !transport
                    .allowed_source_prefixes
                    .iter()
                    .any(|prefix| row.source.module.as_dotted().starts_with(prefix))
                || !transport
                    .allowed_target_prefixes
                    .iter()
                    .any(|prefix| row.target.module.as_dotted().starts_with(prefix))
        })
    {
        return false;
    }
    let selected_rows = mapping
        .module_mappings
        .iter()
        .filter(|row| row.role == npa_package::L2TransportModuleRole::Selected)
        .collect::<Vec<_>>();
    if selected_rows.len() != plan.selected_modules.len()
        || selected_rows.iter().any(|row| {
            !plan.selected_modules.iter().any(|selected| {
                selected.source_module == row.source.module
                    && selected.target_module == row.target.module
            })
        })
    {
        return false;
    }
    let dependency_rows = mapping
        .module_mappings
        .iter()
        .filter(|row| row.role == npa_package::L2TransportModuleRole::Dependency)
        .collect::<Vec<_>>();
    if dependency_rows.len() != plan.dependency_mappings.len()
        || dependency_rows.iter().any(|row| {
            !plan.dependency_mappings.iter().any(|dependency| {
                dependency.role == "dependency"
                    && dependency.renames.is_empty()
                    && dependency.declaration_mapping == row.declaration_mapping
                    && dependency.source.origin == row.source.origin
                    && dependency.source.package == row.source.package
                    && dependency.source.version == row.source.version
                    && dependency.source.module == row.source.module
                    && dependency.target.origin == row.target.origin
                    && dependency.target.package == row.target.package
                    && dependency.target.version == row.target.version
                    && dependency.target.module == row.target.module
            })
        })
    {
        return false;
    }
    let selected_names = plan
        .selected_modules
        .iter()
        .map(|module| module.source_module.clone())
        .collect::<BTreeSet<_>>();
    let local_names = source
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    if plan.selected_modules.iter().any(|selected| {
        selected
            .imports
            .iter()
            .any(|import| local_names.contains(import) && !selected_names.contains(import))
            || baseline
                .snapshot
                .validated
                .manifest()
                .modules
                .iter()
                .any(|module| module.module == selected.target_module)
    }) {
        return false;
    }
    let index = match source.snapshot.project_theorem_index() {
        Ok(index) => index,
        Err(_) => return false,
    };
    for selected in &plan.selected_modules {
        let module = match source
            .snapshot
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == selected.source_module)
        {
            Some(module) => module,
            None => return false,
        };
        let Some(captured) = materialization_source.modules.get(&selected.source_module) else {
            return false;
        };
        if module.source != selected.source_path
            || package_file_hash(captured.source.as_bytes()) != selected.source_file_hash
            || module.expected_certificate_file_hash != selected.certificate_file_hash
            || module.expected_certificate_hash != selected.certificate_hash
            || module.expected_export_hash != selected.export_hash
            || module.expected_axiom_report_hash != selected.axiom_report_hash
            || {
                let mut imports = module.imports.clone();
                imports.sort();
                imports != selected.imports
            }
        {
            return false;
        }
        let expected_theorems = index
            .entries
            .iter()
            .filter(|row| {
                row.global_ref.module == selected.source_module
                    && row.kind == npa_package::PackageTheoremIndexKind::Theorem
            })
            .map(|row| {
                (
                    row.global_ref.name.clone(),
                    row.statement.core_hash,
                    row.global_ref.certificate_hash,
                )
            })
            .collect::<BTreeSet<_>>();
        let planned_theorems = selected
            .theorems
            .iter()
            .map(|row| {
                (
                    row.source_name.clone(),
                    row.statement_hash,
                    selected.certificate_hash,
                )
            })
            .collect::<BTreeSet<_>>();
        if expected_theorems != planned_theorems
            || expected_theorems.iter().any(|(name, hash, certificate)| {
                !acceptance.entries.iter().any(|entry| {
                    entry.module == selected.source_module
                        && &entry.theorem == name
                        && &entry.statement_hash == hash
                        && &entry.certificate_hash == certificate
                })
            })
        {
            return false;
        }
    }
    for dependency in &plan.dependency_mappings {
        let module = match baseline
            .snapshot
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == dependency.target.module)
        {
            Some(module) => module,
            None => return false,
        };
        if module.expected_certificate_file_hash != dependency.target_certificate_file_hash
            || module.expected_certificate_hash != dependency.target_certificate_hash
            || module.expected_export_hash != dependency.target_export_hash
        {
            return false;
        }
    }
    true
}

fn attestation_matches(
    attestation: &npa_package::L2NamespaceTransportAttestation,
    plan: &MathlibPromotionPlan,
    baseline: &Path,
    stage: &Path,
) -> bool {
    let files = match tree_snapshot(stage) {
        Ok(files) => files,
        Err(_) => return false,
    };
    if !(attestation.source_package == plan.source.package
        && attestation.source_version == plan.source.version
        && attestation.target_package == plan.target_baseline.package
        && attestation.target_baseline_version == plan.target_baseline.version
        && attestation.target_version == plan.target_baseline.planned_version
        && attestation.acceptance_policy_file_hash == plan.governance.acceptance_policy_file_hash
        && attestation.source_acceptance_file_hash == plan.governance.source_acceptance_file_hash
        && attestation.transport_policy_file_hash == plan.governance.transport_policy_file_hash
        && attestation.mapping_request_file_hash == plan.governance.mapping_file_hash
        && attestation.source_manifest_hash == plan.source.manifest_file_hash
        && attestation.source_lock_hash == plan.source.lock_file_hash
        && attestation.source_axiom_report_hash == plan.source.axiom_report_file_hash
        && attestation.source_theorem_index_hash == plan.source.theorem_index_file_hash
        && attestation.target_baseline_manifest_hash == plan.target_baseline.manifest_file_hash
        && attestation.target_baseline_lock_hash == plan.target_baseline.lock_file_hash
        && attestation.target_baseline_axiom_report_hash
            == plan.target_baseline.axiom_report_file_hash
        && attestation.target_baseline_theorem_index_hash
            == plan.target_baseline.theorem_index_file_hash
        && files
            .get(&PackagePath::new("npa-package.toml"))
            .is_some_and(|bytes| package_file_hash(bytes) == attestation.target_manifest_hash)
        && files
            .get(&PackagePath::new(PACKAGE_LOCK_PATH))
            .is_some_and(|bytes| package_file_hash(bytes) == attestation.target_lock_hash)
        && files
            .get(&PackagePath::new(PACKAGE_AXIOM_REPORT_PATH))
            .is_some_and(|bytes| package_file_hash(bytes) == attestation.target_axiom_report_hash)
        && files
            .get(&PackagePath::new(PACKAGE_THEOREM_INDEX_PATH))
            .is_some_and(|bytes| package_file_hash(bytes) == attestation.target_theorem_index_hash))
    {
        return false;
    }
    let loaded = match crate::package::load_package_root(stage, COMMAND) {
        Ok(loaded) => loaded,
        Err(_) => return false,
    };
    let audit = match load_package_audit_snapshot(
        stage,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(audit) => audit,
        Err(_) => return false,
    };
    let index = match audit.snapshot.project_theorem_index() {
        Ok(index) => index,
        Err(_) => return false,
    };
    for selected in &plan.selected_modules {
        let target = match loaded
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == selected.target_module)
        {
            Some(target) => target,
            None => return false,
        };
        let target_source_hash = match fs::read(stage.join(target.source.as_str())) {
            Ok(bytes) => package_file_hash(&bytes),
            Err(_) => return false,
        };
        if !attestation.module_pairs.iter().any(|pair| {
            pair.role == npa_package::L2TransportModuleRole::Selected
                && pair.source_module == selected.source_module
                && pair.target_module == selected.target_module
                && pair.source_source_file_hash == Some(selected.source_file_hash)
                && pair.target_source_file_hash == target_source_hash
                && pair.source_certificate_file_hash == selected.certificate_file_hash
                && pair.target_certificate_file_hash == target.expected_certificate_file_hash
                && pair.source_certificate_hash == selected.certificate_hash
                && pair.target_certificate_hash == target.expected_certificate_hash
                && pair.source_export_hash == selected.export_hash
                && pair.target_export_hash == target.expected_export_hash
                && pair.source_axiom_report_hash == selected.axiom_report_hash
                && pair.target_axiom_report_hash == target.expected_axiom_report_hash
        }) {
            return false;
        }
        for theorem in &selected.theorems {
            let target_hash = match index.entries.iter().find(|row| {
                row.kind == npa_package::PackageTheoremIndexKind::Theorem
                    && row.global_ref.module == selected.target_module
                    && row.global_ref.name == theorem.target_name
            }) {
                Some(row) => row.statement.core_hash,
                None => return false,
            };
            if !attestation.theorem_pairs.iter().any(|pair| {
                pair.source_module == selected.source_module
                    && pair.source_theorem == theorem.source_name
                    && pair.source_statement_hash == theorem.statement_hash
                    && pair.target_module == selected.target_module
                    && pair.target_theorem == theorem.target_name
                    && pair.target_statement_hash == target_hash
            }) {
                return false;
            }
        }
    }
    let baseline_files = match tree_snapshot(baseline) {
        Ok(files) => files,
        Err(_) => return false,
    };
    let expected_changes = diff_snapshots(&baseline_files, &files)
        .into_iter()
        .filter(|change| {
            !matches!(
                change.path.as_str(),
                "generated/verified-export-summary.json"
                    | "generated/publish-plan.json"
                    | MATHLIB_PROMOTION_REGISTRY_PATH
            )
        })
        .map(|change| {
            (
                change.path,
                change.old.as_deref().map(package_file_hash),
                package_file_hash(&change.new),
            )
        })
        .collect::<BTreeSet<_>>();
    let attested_changes = attestation
        .changed_paths
        .iter()
        .map(|change| {
            (
                change.path.clone(),
                change.baseline_file_hash,
                change.target_file_hash,
            )
        })
        .collect::<BTreeSet<_>>();
    expected_changes == attested_changes
}

fn update_stage_registry(
    stage: &Path,
    plan_path: &PackagePath,
    plan_bytes: &[u8],
    attestation_path: &PackagePath,
    attestation_bytes: &[u8],
    plan: &MathlibPromotionPlan,
    attestation: &npa_package::L2NamespaceTransportAttestation,
) -> Result<(), ()> {
    enum PreviousRegistry {
        V1(npa_package::PromotionOriginRegistry),
        V2(npa_package::PromotionOriginRegistryV2),
    }
    let registry_path = stage.join(MATHLIB_PROMOTION_REGISTRY_PATH);
    let registry_source = fs::read_to_string(&registry_path).map_err(|_| ())?;
    let (previous, mut registry) = match parse_promotion_origin_registry_versioned(&registry_source)
        .map_err(|_| ())?
    {
        ParsedPromotionOriginRegistry::V2(previous) => {
            (PreviousRegistry::V2(previous.clone()), previous)
        }
        ParsedPromotionOriginRegistry::V1(previous) => {
            let migrated = migrate_promotion_origin_registry_v1_to_v2(&previous).map_err(|_| ())?;
            (PreviousRegistry::V1(previous), migrated)
        }
    };
    let loaded = crate::package::load_package_root(stage, COMMAND).map_err(|_| ())?;
    let audit = load_package_audit_snapshot(
        stage,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    )
    .map_err(|_| ())?;
    let index = audit.snapshot.project_theorem_index().map_err(|_| ())?;
    let mut routes = Vec::new();
    for selected in &plan.selected_modules {
        let target = loaded
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == selected.target_module)
            .ok_or(())?;
        let source_hash =
            package_file_hash(&fs::read(stage.join(target.source.as_str())).map_err(|_| ())?);
        let mut theorems = selected
            .theorems
            .iter()
            .map(|source| {
                let target_row = index
                    .entries
                    .iter()
                    .find(|row| {
                        row.global_ref.module == selected.target_module
                            && row.global_ref.name == source.target_name
                            && row.kind == npa_package::PackageTheoremIndexKind::Theorem
                    })
                    .ok_or(())?;
                Ok(PromotionRouteTheorem {
                    source_name: source.source_name.clone(),
                    source_statement_hash: source.statement_hash,
                    target_name: source.target_name.clone(),
                    target_statement_hash: target_row.statement.core_hash,
                })
            })
            .collect::<Result<Vec<_>, ()>>()?;
        theorems.sort();
        routes.push(PromotionModuleRoute {
            source_module: selected.source_module.clone(),
            target_module: selected.target_module.clone(),
            declaration_mapping: "same-name-except-explicit".to_owned(),
            renames: Vec::new(),
            target_revisions: vec![PromotionTargetRevision {
                target_version: plan.target_baseline.planned_version.clone(),
                target_source_file_hash: source_hash,
                target_certificate_file_hash: target.expected_certificate_file_hash,
                target_certificate_hash: target.expected_certificate_hash,
                target_export_hash: target.expected_export_hash,
                target_axiom_report_hash: target.expected_axiom_report_hash,
                theorems,
            }],
        });
    }
    routes.sort_by(|left, right| {
        (&left.source_module, &left.target_module)
            .cmp(&(&right.source_module, &right.target_module))
    });
    let entry = PromotionOriginEntry {
        promotion_id: plan.promotion_id,
        lifecycle: PromotionLifecycle::Active,
        introduced_version: plan.target_baseline.planned_version.clone(),
        canonical_source: PromotionSourceOrigin {
            package: plan.source.package.clone(),
            version: plan.source.version.clone(),
            modules: plan
                .selected_modules
                .iter()
                .map(|module| PromotionSourceModule {
                    module: module.source_module.clone(),
                    source_file_hash: module.source_file_hash,
                    certificate_file_hash: module.certificate_file_hash,
                    certificate_hash: module.certificate_hash,
                    export_hash: module.export_hash,
                })
                .collect(),
        },
        equivalent_sources: plan.equivalent_sources.clone(),
        module_routes: routes,
        evidence: PromotionEvidence::NamespaceTransportV2 {
            plan_schema: MATHLIB_PROMOTION_PLAN_SCHEMA.to_owned(),
            plan_path: plan_path.clone(),
            plan_file_hash: package_file_hash(plan_bytes),
            acceptance: Box::new(PromotionAcceptanceEvidence {
                policy_id: plan.governance.acceptance_policy_id.clone(),
                policy_version: plan.governance.acceptance_policy_version,
                policy_file_hash: plan.governance.acceptance_policy_file_hash,
                source_ledger_schema: plan.governance.source_acceptance_schema.clone(),
                source_ledger_path: plan.governance.source_acceptance_path.clone(),
                source_ledger_file_hash: plan.governance.source_acceptance_file_hash,
            }),
            transport: Box::new(PromotionTransportEvidence {
                policy_id: plan.governance.transport_policy_id.clone(),
                policy_version: plan.governance.transport_policy_version,
                policy_file_hash: plan.governance.transport_policy_file_hash,
                mapping_request_schema: plan.governance.mapping_schema.clone(),
                mapping_request_path: plan.governance.mapping_path.clone(),
                mapping_request_file_hash: plan.governance.mapping_file_hash,
                attestation_schema: attestation.schema.clone(),
                attestation_path: attestation_path.clone(),
                attestation_file_hash: package_file_hash(attestation_bytes),
                normalized_closure_hash: attestation.normalized_closure_hash,
            }),
        },
    };
    registry
        .entries
        .push(PromotionOriginEntryV2::WholeModuleV1(Box::new(entry)));
    registry
        .entries
        .sort_by_key(PromotionOriginEntryV2::promotion_id);
    registry.generation = registry.generation.checked_add(1).ok_or(())?;
    registry.refresh_hash().map_err(|_| ())?;
    match previous {
        PreviousRegistry::V1(previous) => {
            validate_promotion_origin_registry_v1_to_v2_transition(&previous, &registry)
                .map_err(|_| ())?;
        }
        PreviousRegistry::V2(previous) => {
            validate_promotion_origin_registry_v2_transition(&previous, &registry)
                .map_err(|_| ())?;
        }
    }
    fs::write(registry_path, registry.canonical_json().map_err(|_| ())?).map_err(|_| ())
}

fn change_is_scoped(
    change: &Change,
    plan: &MathlibPromotionPlan,
    phase: PackagePromotionPhase,
) -> bool {
    let path = change.path.as_str();
    if promotion_selected_target_artifact_paths(&plan.selected_modules).contains(&change.path) {
        return change.old.is_none();
    }
    matches!(
        path,
        "npa-package.toml"
            | PACKAGE_LOCK_PATH
            | PACKAGE_AXIOM_REPORT_PATH
            | PACKAGE_THEOREM_INDEX_PATH
            | "generated/verified-export-summary.json"
            | "generated/publish-plan.json"
    ) || (phase == PackagePromotionPhase::Tracked && path == MATHLIB_PROMOTION_REGISTRY_PATH)
}

pub(crate) fn tree_snapshot(root: &Path) -> io::Result<BTreeMap<PackagePath, Vec<u8>>> {
    fn snapshot_path(relative: &Path) -> io::Result<PackagePath> {
        let mut components = Vec::new();
        for component in relative.components() {
            let std::path::Component::Normal(component) = component else {
                return Err(io::Error::other("snapshot path"));
            };
            components.push(
                component
                    .to_str()
                    .ok_or_else(|| io::Error::other("snapshot path encoding"))?,
            );
        }
        let path = PackagePath::new(components.join("/"));
        validate_package_path(&path, "snapshot.path")
            .map_err(|_| io::Error::other("snapshot path"))?;
        Ok(path)
    }

    fn walk(
        root: &Path,
        current: &Path,
        out: &mut BTreeMap<PackagePath, Vec<u8>>,
    ) -> io::Result<()> {
        let mut entries = fs::read_dir(current)?.collect::<Result<Vec<_>, _>>()?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let name = entry.file_name();
            if current == root && name == ".git" {
                continue;
            }
            let path = entry.path();
            let ty = entry.file_type()?;
            if ty.is_symlink() {
                return Err(io::Error::other("symlink"));
            }
            if ty.is_dir() {
                walk(root, &path, out)?;
            } else if ty.is_file() {
                let relative = path
                    .strip_prefix(root)
                    .map_err(|_| io::Error::other("path"))?;
                let package_path = snapshot_path(relative)?;
                if out.insert(package_path, fs::read(path)?).is_some() {
                    return Err(io::Error::other("duplicate snapshot path"));
                }
            }
        }
        Ok(())
    }
    let mut out = BTreeMap::new();
    walk(root, root, &mut out)?;
    Ok(out)
}

pub(crate) fn write_tree_snapshot(
    snapshot: &BTreeMap<PackagePath, Vec<u8>>,
    target: &Path,
) -> io::Result<()> {
    fs::create_dir(target)?;
    let write_result = (|| {
        for (path, bytes) in snapshot {
            validate_package_path(path, "snapshot.path")
                .map_err(|_| io::Error::other("snapshot path"))?;
            let destination = confined_governance_path(
                target,
                path,
                path.as_str(),
                "promotion_materialize_unscoped_path",
            )
            .map_err(|_| io::Error::other("snapshot path"))?;
            let parent = destination
                .parent()
                .ok_or_else(|| io::Error::other("snapshot path parent"))?;
            fs::create_dir_all(parent)?;
            fs::write(destination, bytes)?;
        }
        Ok(())
    })();
    if write_result.is_err() {
        let _ = fs::remove_dir_all(target);
    }
    write_result
}

fn diff_snapshots(
    old: &BTreeMap<PackagePath, Vec<u8>>,
    new: &BTreeMap<PackagePath, Vec<u8>>,
) -> Vec<Change> {
    new.iter()
        .filter_map(|(path, bytes)| match old.get(path) {
            Some(previous) if previous == bytes => None,
            previous => Some(Change {
                path: path.clone(),
                old: previous.cloned(),
                new: bytes.clone(),
            }),
        })
        .collect()
}

fn change_order(change: &Change) -> (u8, String) {
    let path = change.path.as_str();
    let class = if path == MATHLIB_PROMOTION_REGISTRY_PATH {
        4
    } else if path == PACKAGE_LOCK_PATH || path.starts_with("generated/") {
        3
    } else if path == "npa-package.toml" {
        2
    } else {
        1
    };
    (class, path.to_owned())
}

fn apply_transaction(
    target: &Path,
    phase: PackagePromotionPhase,
    promotion_id: PackageHash,
    changes: &[Change],
    transaction_visible: &mut bool,
) -> io::Result<()> {
    *transaction_visible = false;
    let canonical = fs::canonicalize(target)?;
    let transaction = transaction_path(target, promotion_id)?;
    let preparing = preparing_transaction_path(target, promotion_id)?;
    match fs::symlink_metadata(&transaction) {
        Ok(_) => return Err(io::Error::other("recovery required")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    if changes.iter().any(|change| {
        replacement_temp_path(target, &change.path)
            .and_then(|path| path_entry_exists(&path))
            .unwrap_or(true)
    }) {
        return Err(io::Error::other("replacement temporary path exists"));
    }
    let mut preparing_created = false;
    let prepared = (|| -> io::Result<PromotionTransactionJournal> {
        fs::create_dir(&preparing)?;
        preparing_created = true;
        fs::create_dir(preparing.join("old"))?;
        fs::create_dir(preparing.join("new"))?;
        let mut rows = Vec::new();
        for (index, change) in changes.iter().enumerate() {
            let path_hash = promotion_transaction_path_hash(&change.path)
                .map_err(|_| io::Error::other("path hash"))?;
            let filename = format_package_hash(&path_hash)
                .trim_start_matches("sha256:")
                .to_owned();
            if let Some(old) = &change.old {
                write_sync(&preparing.join("old").join(&filename), old)?;
            }
            write_sync(&preparing.join("new").join(&filename), &change.new)?;
            rows.push(PromotionTransactionRow {
                replacement_order: index as u64,
                logical_path: change.path.clone(),
                logical_path_hash: path_hash,
                old: change
                    .old
                    .as_ref()
                    .map_or(PromotionOldFile::Absent, |bytes| {
                        PromotionOldFile::Present(package_file_hash(bytes))
                    }),
                new_file_hash: package_file_hash(&change.new),
                replacement_state: PromotionReplacementState::Pending,
            });
        }
        let mut journal = PromotionTransactionJournal {
            schema: MATHLIB_PROMOTION_TRANSACTION_SCHEMA.to_owned(),
            promotion_id,
            phase: match phase {
                PackagePromotionPhase::Temporary => PromotionTransactionPhase::Temporary,
                PackagePromotionPhase::Tracked => PromotionTransactionPhase::Tracked,
            },
            target_canonical_path_hash: package_file_hash(canonical.to_string_lossy().as_bytes()),
            transaction_state: PromotionTransactionState::Applying,
            rows,
            journal_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        journal
            .refresh_hash()
            .map_err(|_| io::Error::other("journal"))?;
        write_journal_transition(&preparing, &journal)?;
        sync_directory(&preparing.join("old"))?;
        sync_directory(&preparing.join("new"))?;
        sync_directory(&preparing)?;
        fs::rename(&preparing, &transaction)?;
        *transaction_visible = true;
        sync_directory(
            transaction
                .parent()
                .ok_or_else(|| io::Error::other("transaction parent"))?,
        )?;
        Ok(journal)
    })();
    let mut journal = match prepared {
        Ok(journal) => journal,
        Err(error) => {
            if preparing_created {
                let _ = fs::remove_dir_all(&preparing);
            }
            return Err(error);
        }
    };
    for (index, change) in changes.iter().enumerate() {
        replace_file(target, &change.path, &change.new)?;
        journal.rows[index].replacement_state = PromotionReplacementState::Replaced;
        journal
            .refresh_hash()
            .map_err(|_| io::Error::other("journal"))?;
        write_journal_transition(&transaction, &journal)?;
    }
    Ok(())
}

fn transaction_path(target: &Path, promotion_id: PackageHash) -> io::Result<std::path::PathBuf> {
    let canonical = fs::canonicalize(target)?;
    let parent = canonical
        .parent()
        .ok_or_else(|| io::Error::other("target parent"))?;
    Ok(parent.join(format!(
        ".npa-promotion-transaction-{}",
        format_package_hash(&promotion_id).trim_start_matches("sha256:")
    )))
}

fn preparing_transaction_path(
    target: &Path,
    promotion_id: PackageHash,
) -> io::Result<std::path::PathBuf> {
    let canonical = fs::canonicalize(target)?;
    let parent = canonical
        .parent()
        .ok_or_else(|| io::Error::other("target parent"))?;
    let promotion = format_package_hash(&promotion_id);
    for serial in 0_u32..=u32::MAX {
        let candidate = parent.join(format!(
            ".npa-promotion-preparing-{}-{}-{serial}",
            promotion.trim_start_matches("sha256:"),
            std::process::id()
        ));
        match fs::symlink_metadata(&candidate) {
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(candidate),
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::other("preparing transaction path"))
}

fn pending_transaction_exists(target: &Path) -> bool {
    let canonical = match fs::canonicalize(target) {
        Ok(path) => path,
        Err(_) => return true,
    };
    let parent = match canonical.parent() {
        Some(parent) => parent,
        None => return true,
    };
    fs::read_dir(parent).map_or(true, |mut entries| {
        entries.any(|entry| {
            entry.is_err()
                || entry.ok().is_some_and(|entry| {
                    entry
                        .file_name()
                        .to_str()
                        .is_some_and(|name| name.starts_with(".npa-promotion-transaction-"))
                })
        })
    })
}

fn locked_apply_preflight(
    target: &Path,
    captured_target: &BTreeMap<PackagePath, Vec<u8>>,
) -> Result<(), &'static str> {
    if pending_transaction_exists(target) {
        return Err("promotion_recovery_required");
    }
    if tree_snapshot(target).ok().as_ref() != Some(captured_target) {
        return Err("promotion_concurrent_update");
    }
    Ok(())
}

fn rollback_transaction(target: &Path, transaction: &Path) -> io::Result<()> {
    match fs::symlink_metadata(transaction) {
        Ok(metadata) if metadata.file_type().is_dir() => {}
        Ok(_) => return Err(io::Error::other("invalid transaction path type")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    }
    let source = fs::read_to_string(transaction.join("journal.json"))?;
    let journal =
        parse_promotion_transaction_json(&source).map_err(|_| io::Error::other("journal"))?;
    for row in journal.rows.iter().rev() {
        let temporary = replacement_temp_path(target, &row.logical_path)?;
        match fs::symlink_metadata(&temporary) {
            Ok(metadata) if !metadata.file_type().is_file() => {
                return Err(io::Error::other("replacement temporary conflict"));
            }
            Ok(_) => {
                let temporary_hash = package_file_hash(&fs::read(&temporary)?);
                let old_hash = match row.old {
                    PromotionOldFile::Absent => None,
                    PromotionOldFile::Present(hash) => Some(hash),
                };
                if temporary_hash != row.new_file_hash && Some(temporary_hash) != old_hash {
                    return Err(io::Error::other("replacement temporary conflict"));
                }
                fs::remove_file(&temporary)?;
                if let Some(parent) = temporary.parent() {
                    sync_directory(parent)?;
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        let target_path = confined_target_path(target, &row.logical_path)?;
        let current = match fs::read(&target_path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == io::ErrorKind::NotFound => None,
            Err(error) => return Err(error),
        };
        let current_hash = current.as_deref().map(package_file_hash);
        let old_hash = match row.old {
            PromotionOldFile::Absent => None,
            PromotionOldFile::Present(hash) => Some(hash),
        };
        if current_hash != Some(row.new_file_hash) && current_hash != old_hash {
            return Err(io::Error::other("recovery conflict"));
        }
        match row.old {
            PromotionOldFile::Absent => {
                if current_hash == Some(row.new_file_hash) {
                    fs::remove_file(&target_path)?;
                    if let Some(parent) = target_path.parent() {
                        sync_directory(parent)?;
                    }
                }
            }
            PromotionOldFile::Present(expected) => {
                if current_hash != Some(expected) {
                    let filename = format_package_hash(&row.logical_path_hash)
                        .trim_start_matches("sha256:")
                        .to_owned();
                    let bytes = fs::read(transaction.join("old").join(filename))?;
                    if package_file_hash(&bytes) != expected {
                        return Err(io::Error::other("old hash"));
                    }
                    replace_file(target, &row.logical_path, &bytes)?;
                }
            }
        }
    }
    remove_transaction(transaction)
}

fn finalize_transaction(transaction: &Path) -> io::Result<()> {
    let source = fs::read_to_string(transaction.join("journal.json"))?;
    let mut journal =
        parse_promotion_transaction_json(&source).map_err(|_| io::Error::other("journal"))?;
    if journal
        .rows
        .iter()
        .any(|row| row.replacement_state != PromotionReplacementState::Replaced)
    {
        return Err(io::Error::other("pending replacement"));
    }
    journal.transaction_state = PromotionTransactionState::Validated;
    journal
        .refresh_hash()
        .map_err(|_| io::Error::other("journal"))?;
    write_journal_transition(transaction, &journal)?;
    remove_transaction(transaction)
}

fn recover_transaction(target: &Path, journal_path: &Path) -> CommandResult {
    let root_display = render_package_root(target);
    let mut lock = match TargetLock::acquire(target) {
        Ok(lock) => lock,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_concurrent_update",
                TARGET_LOCK_PREFIX,
            )
        }
    };
    let canonical_target = match fs::canonicalize(target) {
        Ok(path) => path,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_recovery_conflict",
                "--target-root",
            )
        }
    };
    let canonical_journal = match fs::canonicalize(journal_path) {
        Ok(path) => path,
        Err(_) => return failure(&root_display, "promotion_recovery_conflict", "--recover"),
    };
    let transaction = match canonical_journal.parent() {
        Some(path) => path,
        None => return failure(&root_display, "promotion_recovery_conflict", "--recover"),
    };
    let expected_parent = canonical_target.parent().unwrap_or_else(|| Path::new("."));
    if transaction.parent() != Some(expected_parent)
        || canonical_journal.file_name().and_then(|name| name.to_str()) != Some("journal.json")
        || !transaction
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with(".npa-promotion-transaction-"))
    {
        return failure(&root_display, "promotion_recovery_conflict", "--recover");
    }
    let source = match fs::read_to_string(&canonical_journal) {
        Ok(source) => source,
        Err(_) => return failure(&root_display, "promotion_recovery_conflict", "--recover"),
    };
    let journal = match parse_promotion_transaction_json(&source) {
        Ok(journal) => journal,
        Err(_) => return failure(&root_display, "promotion_recovery_conflict", "--recover"),
    };
    let journal_name = transaction.file_name().and_then(|name| name.to_str());
    if lock
        .record(Some(journal.promotion_id), "recover", journal_name)
        .is_err()
    {
        return failure(&root_display, "promotion_recovery_conflict", "--recover");
    }
    if journal.target_canonical_path_hash
        != package_file_hash(canonical_target.to_string_lossy().as_bytes())
    {
        return failure(
            &root_display,
            "promotion_recovery_conflict",
            "--target-root",
        );
    }
    let expected_name = format!(
        ".npa-promotion-transaction-{}",
        format_package_hash(&journal.promotion_id).trim_start_matches("sha256:")
    );
    if transaction.file_name().and_then(|name| name.to_str()) != Some(expected_name.as_str())
        || !transaction_layout_is_exact(transaction, &journal)
    {
        return failure(&root_display, "promotion_recovery_conflict", "--recover");
    }
    if journal.transaction_state == PromotionTransactionState::Applying {
        if rollback_transaction(target, transaction).is_err() {
            return failure(&root_display, "promotion_recovery_conflict", "--recover");
        }
    } else {
        if journal.rows.iter().any(|row| {
            read_confined(target, &row.logical_path)
                .ok()
                .is_none_or(|bytes| package_file_hash(&bytes) != row.new_file_hash)
        }) || remove_transaction(transaction).is_err()
        {
            return failure(&root_display, "promotion_recovery_conflict", "--recover");
        }
    }
    let _ = lock.record(Some(journal.promotion_id), "recover", None);
    CommandResult::passed(COMMAND, root_display)
}

fn transaction_layout_is_exact(transaction: &Path, journal: &PromotionTransactionJournal) -> bool {
    let read_names = |path: &Path| -> Option<BTreeSet<String>> {
        let mut names = BTreeSet::new();
        for entry in fs::read_dir(path).ok()? {
            names.insert(entry.ok()?.file_name().into_string().ok()?);
        }
        Some(names)
    };
    let Some(root_names) = read_names(transaction) else {
        return false;
    };
    let expected_root = BTreeSet::from([
        "journal.json".to_owned(),
        "new".to_owned(),
        "old".to_owned(),
    ]);
    let mut interrupted_root = expected_root.clone();
    interrupted_root.insert("journal.next".to_owned());
    if root_names != expected_root && root_names != interrupted_root {
        return false;
    }
    if !fs::symlink_metadata(transaction.join("journal.json"))
        .is_ok_and(|metadata| metadata.file_type().is_file())
        || !fs::symlink_metadata(transaction.join("old"))
            .is_ok_and(|metadata| metadata.file_type().is_dir())
        || !fs::symlink_metadata(transaction.join("new"))
            .is_ok_and(|metadata| metadata.file_type().is_dir())
    {
        return false;
    }
    let next = transaction.join("journal.next");
    if root_names.contains("journal.next")
        && !fs::symlink_metadata(&next).is_ok_and(|metadata| metadata.file_type().is_file())
    {
        return false;
    }
    let expected_new = journal
        .rows
        .iter()
        .map(|row| {
            format_package_hash(&row.logical_path_hash)
                .trim_start_matches("sha256:")
                .to_owned()
        })
        .collect::<BTreeSet<_>>();
    let expected_old = journal
        .rows
        .iter()
        .filter(|row| matches!(row.old, PromotionOldFile::Present(_)))
        .map(|row| {
            format_package_hash(&row.logical_path_hash)
                .trim_start_matches("sha256:")
                .to_owned()
        })
        .collect::<BTreeSet<_>>();
    let read_regular_file_names = |path: &Path| -> Option<BTreeSet<String>> {
        let mut names = BTreeSet::new();
        for entry in fs::read_dir(path).ok()? {
            let entry = entry.ok()?;
            if !entry.file_type().ok()?.is_file() {
                return None;
            }
            names.insert(entry.file_name().into_string().ok()?);
        }
        Some(names)
    };
    read_regular_file_names(&transaction.join("new")).as_ref() == Some(&expected_new)
        && read_regular_file_names(&transaction.join("old")).as_ref() == Some(&expected_old)
}

fn replace_file(root: &Path, path: &PackagePath, bytes: &[u8]) -> io::Result<()> {
    let target = confined_target_path(root, path)?;
    let parent = target
        .parent()
        .ok_or_else(|| io::Error::other("parent"))?
        .to_path_buf();
    fs::create_dir_all(&parent)?;
    let target = confined_target_path(root, path)?;
    let temporary = replacement_temp_path(root, path)?;
    let mut temporary_file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&temporary)?;
    if let Err(error) = temporary_file
        .write_all(bytes)
        .and_then(|()| temporary_file.sync_all())
    {
        drop(temporary_file);
        let _ = fs::remove_file(&temporary);
        return Err(error);
    }
    drop(temporary_file);
    fs::rename(temporary, target)?;
    File::open(parent)?.sync_all()
}

fn replacement_temp_path(root: &Path, path: &PackagePath) -> io::Result<PathBuf> {
    let target = confined_target_path(root, path)?;
    let parent = target.parent().ok_or_else(|| io::Error::other("parent"))?;
    let path_hash =
        promotion_transaction_path_hash(path).map_err(|_| io::Error::other("logical path hash"))?;
    Ok(parent.join(format!(
        ".npa-promotion-tmp-{}",
        format_package_hash(&path_hash).trim_start_matches("sha256:")
    )))
}

fn confined_target_path(root: &Path, path: &PackagePath) -> io::Result<PathBuf> {
    confined_governance_path(
        root,
        path,
        path.as_str(),
        "promotion_materialize_unscoped_path",
    )
    .map_err(|_| io::Error::other("confined target path"))
}

fn target_path_is_absent(root: &Path, path: &PackagePath) -> bool {
    let Ok(full) = confined_target_path(root, path) else {
        return false;
    };
    fs::symlink_metadata(full).is_err_and(|error| error.kind() == io::ErrorKind::NotFound)
}

fn path_entry_exists(path: &Path) -> io::Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

fn write_sync(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut file = File::create(path)?;
    file.write_all(bytes)?;
    file.sync_all()
}

fn write_journal_transition(
    transaction: &Path,
    journal: &PromotionTransactionJournal,
) -> io::Result<()> {
    let next = transaction.join("journal.next");
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&next)?;
    let bytes = journal
        .canonical_json()
        .map_err(|_| io::Error::other("journal"))?;
    if let Err(error) = file
        .write_all(bytes.as_bytes())
        .and_then(|()| file.sync_all())
    {
        drop(file);
        let _ = fs::remove_file(&next);
        return Err(error);
    }
    drop(file);
    fs::rename(next, transaction.join("journal.json"))?;
    sync_directory(transaction)
}

fn sync_directory(path: &Path) -> io::Result<()> {
    File::open(path)?.sync_all()
}

fn remove_transaction(transaction: &Path) -> io::Result<()> {
    let parent = transaction
        .parent()
        .ok_or_else(|| io::Error::other("transaction parent"))?
        .to_path_buf();
    fs::remove_dir_all(transaction)?;
    sync_directory(&parent)
}

fn read_confined(root: &Path, path: &PackagePath) -> io::Result<Vec<u8>> {
    let full = confined_governance_path(
        root,
        path,
        path.as_str(),
        "promotion_materialize_unscoped_path",
    )
    .map_err(|_| io::Error::other("confined path"))?;
    fs::read(full)
}

fn short_hash(hash: PackageHash) -> String {
    format_package_hash(&hash)[7..19].to_owned()
}

fn failure(root: &str, reason: &str, path: &str) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        root,
        vec![CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path)],
    )
}

fn materialize_declaration_normal(
    options: PackageMaterializePromotionOptions,
    plan_path: PackagePath,
    plan_bytes: Vec<u8>,
    plan_source: String,
) -> CommandResult {
    let root_display = render_package_root(&options.target_root);
    let Some(baseline_root) = options.target_baseline_root.as_ref() else {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            "--target-baseline-root",
        );
    };
    let Some(phase) = options.phase else {
        return failure(&root_display, "promotion_materialize_plan_stale", "--phase");
    };
    if options.transport_attestation.is_some()
        || (phase == PackagePromotionPhase::Tracked && options.verification_attestation.is_none())
        || (phase == PackagePromotionPhase::Temporary && options.verification_attestation.is_some())
    {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            "--verification-attestation",
        );
    }
    let plan = match parse_mathlib_promotion_plan_v2_json(&plan_source) {
        Ok(plan) => plan,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_plan_stale",
                plan_path.as_str(),
            )
        }
    };
    if options.apply && pending_transaction_exists(&options.target_root) {
        return failure(
            &root_display,
            "promotion_recovery_required",
            "--target-root",
        );
    }
    let source = match load_package_audit_snapshot(
        &options.common.root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    let baseline = match load_package_audit_snapshot(
        baseline_root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(snapshot) => snapshot,
        Err(result) => return result,
    };
    for snapshot in [&source, &baseline] {
        if let Err(diagnostic) = validate_checked_generated(snapshot) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    if !declaration_plan_inputs_current(
        &options.common.root,
        baseline_root,
        &source,
        &baseline,
        &plan,
    ) || !declaration_equivalent_origins_current(&options.equivalent_origin_roots, &plan)
    {
        return failure(
            &root_display,
            "promotion_materialize_plan_stale",
            plan_path.as_str(),
        );
    }
    let captured_target = match tree_snapshot(&options.target_root) {
        Ok(files) => files,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_target_not_clean",
                "--target-root",
            )
        }
    };
    let baseline_files = match tree_snapshot(baseline_root) {
        Ok(files) => files,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_materialize_baseline_mismatch",
                "--target-baseline-root",
            )
        }
    };
    if captured_target != baseline_files {
        return failure(
            &root_display,
            "promotion_materialize_target_not_clean",
            "--target-root",
        );
    }
    if let Some(collision) = declaration_target_artifact_collision(baseline_root, &plan)
        .or_else(|| declaration_target_artifact_collision(&options.target_root, &plan))
    {
        return failure(
            &root_display,
            "promotion_declaration_target_collision",
            collision.as_str(),
        );
    }
    let parent = options
        .target_root
        .parent()
        .unwrap_or_else(|| Path::new("."));
    let stage = parent.join(format!(
        ".npa-promotion-stage-{}-{}",
        std::process::id(),
        short_hash(plan.promotion_id)
    ));
    if write_tree_snapshot(&captured_target, &stage).is_err() {
        return failure(
            &root_display,
            "promotion_concurrent_update",
            "--target-root",
        );
    }
    if let Err(reason) =
        build_declaration_materialization_candidate(&options.common.root, &stage, &plan)
    {
        let _ = fs::remove_dir_all(&stage);
        return failure(&root_display, reason, "--plan");
    }
    if phase == PackagePromotionPhase::Tracked {
        let attestation_arg = options
            .verification_attestation
            .as_ref()
            .expect("checked above");
        let attestation_path = PackagePath::new(attestation_arg.to_string_lossy());
        let attestation_bytes = match read_confined(&options.common.root, &attestation_path) {
            Ok(bytes) => bytes,
            Err(_) => {
                let _ = fs::remove_dir_all(&stage);
                return failure(
                    &root_display,
                    "promotion_verification_attestation_stale",
                    attestation_path.as_str(),
                );
            }
        };
        let attestation_source = match String::from_utf8(attestation_bytes.clone()) {
            Ok(source) => source,
            Err(_) => {
                let _ = fs::remove_dir_all(&stage);
                return failure(
                    &root_display,
                    "promotion_verification_attestation_stale",
                    attestation_path.as_str(),
                );
            }
        };
        let attestation = match parse_verified_materialization_attestation_json(&attestation_source)
        {
            Ok(attestation) => attestation,
            Err(_) => {
                let _ = fs::remove_dir_all(&stage);
                return failure(
                    &root_display,
                    "promotion_verification_attestation_stale",
                    attestation_path.as_str(),
                );
            }
        };
        let validation = run_package_validate_promotion_materialization(
            PackageValidatePromotionMaterializationOptions {
                common: PackageCommonOptions {
                    root: options.common.root.clone(),
                    json: false,
                },
                target_baseline_root: baseline_root.clone(),
                target_root: stage.clone(),
                plan: PathBuf::from(plan_path.as_str()),
                out: PathBuf::from(attestation_path.as_str()),
                check: true,
            },
        );
        if validation.status != CommandStatus::Passed
            || attestation.promotion_id != plan.promotion_id
            || attestation.plan.file_hash != package_file_hash(&plan_bytes)
            || update_stage_registry_v2(
                &stage,
                &plan_path,
                &plan_bytes,
                &attestation_path,
                &attestation_bytes,
                &plan,
                &attestation,
            )
            .is_err()
        {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                attestation_path.as_str(),
            );
        }
    }
    let staged_files = match tree_snapshot(&stage) {
        Ok(files) => files,
        Err(_) => {
            let _ = fs::remove_dir_all(&stage);
            return failure(
                &root_display,
                "promotion_materialize_target_identity_mismatch",
                "--target-root",
            );
        }
    };
    let mut changes = diff_snapshots(&captured_target, &staged_files);
    changes.sort_by_key(change_order);
    if let Some(unscoped) = changes
        .iter()
        .find(|change| !declaration_change_is_scoped(change, &plan, phase))
    {
        let _ = fs::remove_dir_all(&stage);
        return failure(
            &root_display,
            "promotion_materialize_unscoped_path",
            unscoped.path.as_str(),
        );
    }
    if !options.apply {
        let _ = fs::remove_dir_all(&stage);
        return change_result(root_display, changes);
    }
    apply_declaration_stage(
        &options,
        phase,
        plan.promotion_id,
        &captured_target,
        &staged_files,
        &changes,
        &stage,
    )
}

/// Build the deterministic declaration target into an exact baseline copy.
pub(crate) fn build_declaration_materialization_candidate(
    source_root: &Path,
    stage: &Path,
    plan: &MathlibPromotionPlanV2,
) -> Result<Vec<PromotionReplayOmission>, &'static str> {
    let source = load_package_audit_snapshot(
        source_root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    )
    .map_err(|_| "promotion_materialize_plan_stale")?;
    let manifest = source.snapshot.validated.manifest();
    let module = manifest
        .modules
        .iter()
        .find(|module| module.module == plan.selection.source_module)
        .ok_or("promotion_materialize_plan_stale")?;
    let mut extraction_source_bytes = 0;
    let source_bytes =
        read_declaration_source(source_root, &module.source, &mut extraction_source_bytes)
            .map_err(materialization_source_extraction_reason)?;
    if package_file_hash(&source_bytes) != plan.selection.source_file_hash {
        return Err("promotion_materialize_plan_stale");
    }
    let source_text = String::from_utf8(source_bytes)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    let imported_interfaces = direct_import_interfaces(
        source_root,
        &source,
        &module.imports,
        extraction_source_bytes,
    )
    .map_err(materialization_source_extraction_reason)?;
    let declarations = plan
        .selection
        .materialized_declarations
        .iter()
        .map(|row| {
            Ok(HumanSelectedDeclaration {
                name: row.source_name.clone(),
                kind: parse_human_kind(&row.human_kind)?,
                item_span: Span::new(
                    FileId(0),
                    u32::try_from(row.item_span.start)
                        .map_err(|_| "promotion_materialize_source_rewrite_failed")?,
                    u32::try_from(row.item_span.end)
                        .map_err(|_| "promotion_materialize_source_rewrite_failed")?,
                ),
                decl_interface_hash: row.decl_interface_hash.into_bytes(),
            })
        })
        .collect::<Result<Vec<_>, &'static str>>()?;
    let mut mapping = plan
        .selection
        .materialized_declarations
        .iter()
        .map(|row| HumanGlobalMappingRow {
            source: HumanGlobalIdentity {
                module: plan.selection.source_module.clone(),
                name: row.source_name.clone(),
                decl_interface_hash: row.decl_interface_hash.into_bytes(),
            },
            target: HumanGlobalIdentity {
                module: plan.selection.target_module.clone(),
                name: row.target_name.clone(),
                decl_interface_hash: row.decl_interface_hash.into_bytes(),
            },
        })
        .collect::<Vec<_>>();
    mapping.extend(
        plan.dependency_mappings
            .iter()
            .map(|row| HumanGlobalMappingRow {
                source: HumanGlobalIdentity {
                    module: row.source.module.clone(),
                    name: row.declaration_name.clone(),
                    decl_interface_hash: row.source_decl_interface_hash.into_bytes(),
                },
                target: HumanGlobalIdentity {
                    module: row.target.module.clone(),
                    name: row.declaration_name.clone(),
                    decl_interface_hash: row.target_decl_interface_hash.into_bytes(),
                },
            }),
    );
    mapping.sort();
    let extracted = extract_human_declaration_source(
        FileId(0),
        &source_text,
        &imported_interfaces,
        &HumanDeclarationSelection {
            source_module: plan.selection.source_module.clone(),
            target_module: plan.selection.target_module.clone(),
            declarations,
        },
        &HumanGlobalMapping { rows: mapping },
    )
    .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    let target_base = plan.selection.target_module.as_dotted().replace('.', "/");
    let target_dir = stage.join(&target_base);
    fs::create_dir_all(&target_dir).map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    fs::write(target_dir.join("source.npa"), extracted.source)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    let replay_bytes = read_confined(source_root, &plan.selection.replay_path)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    if package_file_hash(&replay_bytes) != plan.selection.replay_file_hash {
        return Err("promotion_materialize_plan_stale");
    }
    let replay_source = std::str::from_utf8(&replay_bytes)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    let (replay, omissions) = filtered_declaration_replay(replay_source, plan)?;
    fs::write(target_dir.join("replay.json"), replay)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;

    let preserved = capture_existing_module_artifacts(stage)?;
    edit_manifest_v2(stage, plan)?;
    externalize_preserved_dependencies_v2(stage, plan, &preserved)?;
    let common = PackageCommonOptions {
        root: stage.to_path_buf(),
        json: false,
    };
    if run_package_build_certs(PackageBuildCertsOptions {
        common: common.clone(),
        check: false,
        build_check_cache: PackageBuildCheckCacheMode::Off,
        update_manifest_hashes: true,
        selection: PackageBuildSelection::Full,
    })
    .status
        != CommandStatus::Passed
    {
        return Err("promotion_materialize_compile_failed");
    }
    restore_existing_module_artifacts_v2(stage, plan, &preserved)?;
    if run_package_lock_command(PackageLockCommand::Write(common.clone())).status
        != CommandStatus::Passed
        || run_package_axiom_report(PackageAxiomReportOptions {
            common: common.clone(),
            check: false,
            timings: PackageTimingMode::Off,
        })
        .status
            != CommandStatus::Passed
        || run_package_index(PackageIndexOptions {
            common: common.clone(),
            check: false,
            timings: PackageTimingMode::Off,
        })
        .status
            != CommandStatus::Passed
        || run_package_theorem_premise_report(PackageTheoremPremiseReportOptions {
            common: common.clone(),
            check: false,
            timings: PackageTimingMode::Off,
        })
        .status
            != CommandStatus::Passed
    {
        return Err("promotion_materialize_target_identity_mismatch");
    }
    write_meta_sidecar_v2(stage, plan)?;
    if run_package_export_summary(PackageExportSummaryOptions {
        common: common.clone(),
        out: None,
        check: false,
        timings: PackageTimingMode::Off,
    })
    .status
        != CommandStatus::Passed
        || run_package_publish_plan(PackagePublishPlanOptions {
            common,
            check: false,
            timings: PackageTimingMode::Off,
        })
        .status
            != CommandStatus::Passed
    {
        return Err("promotion_materialize_target_identity_mismatch");
    }
    validate_materialized_declaration_inventory(stage, plan)?;
    Ok(omissions)
}

fn materialization_source_extraction_reason(
    error: DeclarationSourceExtractionError,
) -> &'static str {
    match error {
        DeclarationSourceExtractionError::Unsupported => {
            "promotion_materialize_source_rewrite_failed"
        }
        DeclarationSourceExtractionError::SourceBytesLimitExceeded { .. } => {
            "promotion_declaration_closure_limit_exceeded"
        }
    }
}

fn parse_human_kind(value: &str) -> Result<HumanDeclarationFamilyMemberKind, &'static str> {
    match value {
        "theorem" => Ok(HumanDeclarationFamilyMemberKind::Theorem),
        "definition" => Ok(HumanDeclarationFamilyMemberKind::Definition),
        "inductive" => Ok(HumanDeclarationFamilyMemberKind::Inductive),
        "class" => Ok(HumanDeclarationFamilyMemberKind::Class),
        "class_field" => Ok(HumanDeclarationFamilyMemberKind::ClassField),
        "instance" => Ok(HumanDeclarationFamilyMemberKind::Instance),
        _ => Err("promotion_materialize_source_rewrite_failed"),
    }
}

/// Rebuild the exact filtered replay and its deterministic omission inventory.
pub(crate) fn filtered_declaration_replay(
    source: &str,
    plan: &MathlibPromotionPlanV2,
) -> Result<(String, Vec<PromotionReplayOmission>), &'static str> {
    let mut replay = parse_package_proof_replay(source)
        .map_err(|_| "promotion_materialize_source_rewrite_failed")?;
    if replay.module != plan.selection.source_module {
        return Err("promotion_materialize_source_rewrite_failed");
    }
    let selected = plan
        .selection
        .materialized_declarations
        .iter()
        .map(|row| row.source_name.as_dotted())
        .collect::<BTreeSet<_>>();
    let mapped_modules = std::iter::once(plan.selection.source_module.as_dotted())
        .chain(
            plan.dependency_mappings
                .iter()
                .map(|row| row.source.module.as_dotted()),
        )
        .collect::<BTreeSet<_>>();
    let source_hash = package_file_hash(source.as_bytes());
    let mut omissions = Vec::new();
    let mut retained = Vec::new();
    for (index, step) in replay.steps.into_iter().enumerate() {
        if !selected.contains(&step.declaration) {
            continue;
        }
        let unsafe_rewrite = step
            .term
            .as_ref()
            .into_iter()
            .chain(step.note.as_ref())
            .any(|text| mapped_modules.iter().any(|module| text.contains(module)));
        if unsafe_rewrite {
            omissions.push(PromotionReplayOmission {
                source_replay_file_hash: source_hash,
                declaration: Name::from_dotted(&step.declaration),
                row_index: index as u64,
                reason: PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON.to_owned(),
            });
        } else {
            retained.push(step);
        }
    }
    replay.module = plan.selection.target_module.clone();
    replay.steps = retained;
    replay.accepted_artifact = Some(PackagePath::new(format!(
        "{}/certificate.npcert",
        plan.selection.target_module.as_dotted().replace('.', "/")
    )));
    omissions.sort();
    Ok((replay.canonical_json(), omissions))
}

fn edit_manifest_v2(stage: &Path, plan: &MathlibPromotionPlanV2) -> Result<(), &'static str> {
    let path = stage.join("npa-package.toml");
    let mut document = fs::read_to_string(&path)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    document["version"] = toml_edit::value(plan.target_baseline.planned_version.as_str());
    let base = plan.selection.target_module.as_dotted().replace('.', "/");
    let mut table = Table::new();
    table["module"] = toml_edit::value(plan.selection.target_module.as_dotted());
    table["source"] = toml_edit::value(format!("{base}/source.npa"));
    table["certificate"] = toml_edit::value(format!("{base}/certificate.npcert"));
    table["meta"] = toml_edit::value(format!("{base}/meta.json"));
    table["replay"] = toml_edit::value(format!("{base}/replay.json"));
    table["producer_profile"] = toml_edit::value("human-surface-explicit-term");
    for field in [
        "expected_source_hash",
        "expected_certificate_file_hash",
        "expected_export_hash",
        "expected_axiom_report_hash",
        "expected_certificate_hash",
    ] {
        table[field] = toml_edit::value(format_package_hash(&PackageHash::new([0; 32])));
    }
    let mut imports = Array::new();
    for module in plan
        .dependency_mappings
        .iter()
        .map(|row| row.target.module.clone())
        .collect::<BTreeSet<_>>()
    {
        imports.push(module.as_dotted());
    }
    table["imports"] = Item::Value(imports.into());
    for (field, kind) in [
        ("theorems", "theorem"),
        ("definitions", "definition"),
        ("inductives", "inductive"),
    ] {
        let mut values = Array::new();
        for row in &plan.selection.materialized_declarations {
            if row.certificate_kind == kind {
                values.push(row.target_name.as_dotted());
            }
        }
        if field != "inductives" || !values.is_empty() {
            table[field] = Item::Value(values.into());
        }
    }
    table["axioms"] = Item::Value(Array::new().into());
    append_module_table(&mut document, table)?;
    fs::write(path, document.to_string())
        .map_err(|_| "promotion_materialize_target_identity_mismatch")
}

fn append_module_table(document: &mut DocumentMut, table: Table) -> Result<(), &'static str> {
    let replace_empty = !document.as_table().contains_key("modules")
        || document["modules"]
            .as_array()
            .is_some_and(|modules| modules.is_empty());
    if replace_empty {
        let mut tables = ArrayOfTables::new();
        tables.push(table);
        document.as_table_mut().remove("modules");
        document["modules"] = Item::ArrayOfTables(tables);
        return Ok(());
    }
    document["modules"]
        .as_array_of_tables_mut()
        .ok_or("promotion_materialize_target_identity_mismatch")?
        .push(table);
    Ok(())
}

fn import_tables_mut(document: &mut DocumentMut) -> Result<&mut ArrayOfTables, &'static str> {
    let replace_empty = !document.as_table().contains_key("imports")
        || document["imports"]
            .as_array()
            .is_some_and(|imports| imports.is_empty());
    if replace_empty {
        document.as_table_mut().remove("imports");
        document["imports"] = Item::ArrayOfTables(ArrayOfTables::new());
    }
    document["imports"]
        .as_array_of_tables_mut()
        .ok_or("promotion_materialize_target_identity_mismatch")
}

fn restore_existing_module_artifacts_v2(
    stage: &Path,
    plan: &MathlibPromotionPlanV2,
    preserved: &PreservedTargetModules,
) -> Result<(), &'static str> {
    for (path, bytes) in &preserved.artifacts {
        let full = stage.join(path.as_str());
        if let Some(parent) = full.parent() {
            fs::create_dir_all(parent)
                .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
        }
        fs::write(full, bytes).map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    }
    let manifest_path = stage.join("npa-package.toml");
    let built = fs::read_to_string(&manifest_path)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let selected = built["modules"]
        .as_array_of_tables()
        .and_then(|tables| {
            tables.iter().find(|table| {
                table.get("module").and_then(Item::as_str)
                    == Some(plan.selection.target_module.as_dotted().as_str())
            })
        })
        .cloned()
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    let mut document = preserved
        .manifest_source
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    document["version"] = toml_edit::value(plan.target_baseline.planned_version.as_str());
    append_module_table(&mut document, selected)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    fs::write(manifest_path, document.to_string())
        .map_err(|_| "promotion_materialize_target_identity_mismatch")
}

fn externalize_preserved_dependencies_v2(
    stage: &Path,
    plan: &MathlibPromotionPlanV2,
    preserved: &PreservedTargetModules,
) -> Result<(), &'static str> {
    let local_names = plan
        .dependency_mappings
        .iter()
        .filter(|row| row.target.origin == PackageArtifactOrigin::Local)
        .map(|row| row.target.module.as_dotted())
        .collect::<BTreeSet<_>>();
    if local_names.is_empty() {
        return Ok(());
    }
    let preserved_manifest = parse_and_validate_manifest_str(&preserved.manifest_source)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .into_manifest();
    let local_modules = local_names
        .iter()
        .map(|name| {
            preserved_manifest
                .modules
                .iter()
                .find(|module| module.module.as_dotted() == *name)
                .ok_or("promotion_materialize_target_identity_mismatch")
        })
        .collect::<Result<Vec<_>, _>>()?;
    let manifest_path = stage.join("npa-package.toml");
    let mut document = fs::read_to_string(&manifest_path)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?
        .parse::<DocumentMut>()
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let tables = document["modules"]
        .as_array_of_tables()
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    let mut retained = ArrayOfTables::new();
    for table in tables {
        if !table
            .get("module")
            .and_then(Item::as_str)
            .is_some_and(|name| local_names.contains(name))
        {
            retained.push(table.clone());
        }
    }
    document["modules"] = Item::ArrayOfTables(retained);
    let imports = import_tables_mut(&mut document)?;
    for module in local_modules {
        let mut table = Table::new();
        table["module"] = toml_edit::value(module.module.as_dotted());
        table["package"] = toml_edit::value(plan.target_baseline.package.as_str());
        table["version"] = toml_edit::value(plan.target_baseline.version.as_str());
        table["certificate"] = toml_edit::value(module.certificate.as_str());
        table["export_hash"] = toml_edit::value(format_package_hash(&module.expected_export_hash));
        table["certificate_hash"] =
            toml_edit::value(format_package_hash(&module.expected_certificate_hash));
        imports.push(table);
    }
    fs::write(manifest_path, document.to_string())
        .map_err(|_| "promotion_materialize_target_identity_mismatch")
}

fn write_meta_sidecar_v2(stage: &Path, plan: &MathlibPromotionPlanV2) -> Result<(), &'static str> {
    let loaded = crate::package::load_package_root(stage, COMMAND)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let module = loaded
        .validated
        .manifest()
        .modules
        .iter()
        .find(|module| module.module == plan.selection.target_module)
        .ok_or("promotion_materialize_target_identity_mismatch")?;
    let declarations = plan
        .selection
        .materialized_declarations
        .iter()
        .map(|row| {
            format!(
                "    {{\n      \"name\": \"{}\",\n      \"kind\": \"{}\"\n    }}",
                row.target_name.as_dotted(),
                if row.certificate_kind == "definition" {
                    "def"
                } else {
                    row.certificate_kind.as_str()
                }
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");
    let imports = module
        .imports
        .iter()
        .map(|name| format!("\"{}\"", name.as_dotted()))
        .collect::<Vec<_>>()
        .join(", ");
    let json = format!(
        "{{\n  \"schema\": \"npa-ai-proof-meta-v0.1\",\n  \"module\": \"{}\",\n  \"source\": \"{}\",\n  \"certificate\": \"{}\",\n  \"producer_profile\": \"human-surface-explicit-term\",\n  \"trusted_status\": \"verified_by_certificate\",\n  \"source_sha256\": \"{}\",\n  \"certificate_file_sha256\": \"{}\",\n  \"export_hash\": \"{}\",\n  \"axiom_report_hash\": \"{}\",\n  \"certificate_hash\": \"{}\",\n  \"imports\": [{}],\n  \"axioms\": [],\n  \"declarations\": [\n{}\n  ],\n  \"trust_boundary\": \"source, replay, and metadata are non-trusted sidecars; only the canonical certificate verified by npa-cert is accepted\"\n}}\n",
        module.module.as_dotted(), module.source.as_str(), module.certificate.as_str(),
        format_package_hash(&module.expected_source_hash), format_package_hash(&module.expected_certificate_file_hash),
        format_package_hash(&module.expected_export_hash), format_package_hash(&module.expected_axiom_report_hash),
        format_package_hash(&module.expected_certificate_hash), imports, declarations,
    );
    fs::write(
        stage.join(
            module
                .meta
                .as_ref()
                .ok_or("promotion_materialize_target_identity_mismatch")?
                .as_str(),
        ),
        json,
    )
    .map_err(|_| "promotion_materialize_target_identity_mismatch")
}

pub(crate) fn validate_materialized_declaration_inventory(
    stage: &Path,
    plan: &MathlibPromotionPlanV2,
) -> Result<(), &'static str> {
    let snapshot = load_package_audit_snapshot(
        stage,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    )
    .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    validate_checked_generated(&snapshot)
        .map_err(|_| "promotion_materialize_target_identity_mismatch")?;
    let record = snapshot
        .snapshot
        .decoded_module_records
        .values()
        .find(|record| record.key.module == plan.selection.target_module)
        .ok_or("promotion_declaration_export_mismatch")?;
    let actual = record
        .verified_module
        .export_block()
        .iter()
        .map(|export| {
            let name = record
                .verified_module
                .name_table()
                .get(export.name)
                .ok_or("promotion_declaration_export_mismatch")?
                .clone();
            Ok(name)
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let expected = plan
        .selection
        .materialized_declarations
        .iter()
        .map(|row| row.target_name.clone())
        .chain(
            plan.selection
                .generated_exports
                .iter()
                .map(|row| row.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    if actual != expected {
        return Err("promotion_declaration_export_mismatch");
    }
    let imports = record
        .verified_module
        .imports()
        .iter()
        .map(|entry| entry.module.clone())
        .collect::<BTreeSet<_>>();
    let expected_imports = plan
        .dependency_mappings
        .iter()
        .map(|row| row.target.module.clone())
        .collect::<BTreeSet<_>>();
    if imports != expected_imports {
        return Err("promotion_declaration_import_mismatch");
    }
    Ok(())
}

pub(crate) fn declaration_plan_inputs_current(
    source_root: &Path,
    baseline_root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    baseline: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    plan: &MathlibPromotionPlanV2,
) -> bool {
    let source_manifest = source.snapshot.validated.manifest();
    let baseline_manifest = baseline.snapshot.validated.manifest();
    if run_package_validate_promotion_origin_registry(
        PackageValidatePromotionOriginRegistryOptions {
            common: PackageCommonOptions {
                root: baseline_root.to_path_buf(),
                json: false,
            },
            source_roots: Vec::new(),
            previous_registry: None,
        },
    )
    .status
        != CommandStatus::Passed
    {
        return false;
    }
    let registry_bytes = match read_confined(
        baseline_root,
        &PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH),
    ) {
        Ok(bytes) => bytes,
        Err(_) => return false,
    };
    if package_file_hash(&registry_bytes) != plan.target_baseline.registry_file_hash {
        return false;
    }
    let registry = match std::str::from_utf8(&registry_bytes)
        .ok()
        .and_then(|source| parse_promotion_origin_registry_versioned(source).ok())
    {
        Some(registry) => registry,
        None => return false,
    };
    let mut source_external = BTreeMap::new();
    for mapping in &plan.dependency_mappings {
        if mapping.target.origin == PackageArtifactOrigin::Local
            && !registry_owns_active_target(&registry, &mapping.target.module)
        {
            return false;
        }
        let Some(source_record) = endpoint_record(source, &mapping.source) else {
            return false;
        };
        let Some(target_record) = endpoint_record(baseline, &mapping.target) else {
            return false;
        };
        let Ok(source_identity) = resolve_verified_declaration_export(
            &source_record.verified_module,
            &mapping.declaration_name,
        ) else {
            return false;
        };
        let Ok(target_identity) = resolve_verified_declaration_export(
            &target_record.verified_module,
            &mapping.declaration_name,
        ) else {
            return false;
        };
        if source_external
            .insert(
                source_identity.identity.clone(),
                target_identity.identity.clone(),
            )
            .is_some()
            || PackageHash::from(source_identity.identity.decl_interface_hash)
                != mapping.source_decl_interface_hash
            || PackageHash::from(target_identity.identity.decl_interface_hash)
                != mapping.target_decl_interface_hash
            || source_identity.identity.kind != target_identity.identity.kind
            || target_record.certificate.file_hash != mapping.target_certificate_file_hash
            || target_record.key.certificate_hash != mapping.target_certificate_hash
            || target_record.key.export_hash != mapping.target_export_hash
        {
            return false;
        }
    }
    let request = read_confined(source_root, &plan.governance.request_path)
        .ok()
        .and_then(|bytes| String::from_utf8(bytes).ok())
        .and_then(|source| parse_declaration_promotion_request_json(&source).ok());
    let Some(request) = request else {
        return false;
    };
    let request_roots = request
        .roots
        .iter()
        .map(|root| {
            (
                root.source_name.clone(),
                root.target_name.clone(),
                root.kind.as_str().to_owned(),
            )
        })
        .collect::<Vec<_>>();
    let plan_roots = plan
        .selection
        .roots
        .iter()
        .map(|root| {
            (
                root.requested_name.clone(),
                root.requested_name.clone(),
                root.kind.clone(),
            )
        })
        .collect::<Vec<_>>();
    let request_mappings = request
        .dependency_mappings
        .iter()
        .map(|row| (row.source.clone(), row.target.clone()))
        .collect::<BTreeSet<_>>();
    let plan_mappings = plan
        .dependency_mappings
        .iter()
        .map(|row| (row.source.clone(), row.target.clone()))
        .collect::<BTreeSet<_>>();
    if request.source.package != plan.source.package
        || request.source.version != plan.source.version
        || request.target.package != plan.target_baseline.package
        || request.target.baseline_version != plan.target_baseline.version
        || request.target.planned_version != plan.target_baseline.planned_version
        || request.source_module != plan.selection.source_module
        || request.target_module != plan.selection.target_module
        || request.requested_maturity != plan.requested_maturity
        || request_roots != plan_roots
        || request_mappings != plan_mappings
    {
        return false;
    }
    let generated_match =
        |snapshot: &crate::package_artifacts::LoadedPackageAuditSnapshot,
         expected: &npa_package::PromotionPackageSnapshot| {
            snapshot.snapshot.manifest.file_hash == expected.manifest_file_hash
                && package_file_hash(snapshot.package_lock_json.as_bytes())
                    == expected.lock_file_hash
                && snapshot
                    .checked_generated
                    .axiom_report_json
                    .as_deref()
                    .is_some_and(|value| {
                        package_file_hash(value.as_bytes()) == expected.axiom_report_file_hash
                    })
                && snapshot
                    .checked_generated
                    .theorem_index_json
                    .as_deref()
                    .is_some_and(|value| {
                        package_file_hash(value.as_bytes()) == expected.theorem_index_file_hash
                    })
        };
    if source_manifest.package != plan.source.package
        || source_manifest.version != plan.source.version
        || baseline_manifest.package != plan.target_baseline.package
        || baseline_manifest.version != plan.target_baseline.version
        || !generated_match(source, &plan.source)
    {
        return false;
    }
    let baseline_projection = npa_package::PromotionPackageSnapshot {
        package: plan.target_baseline.package.clone(),
        version: plan.target_baseline.version.clone(),
        manifest_file_hash: plan.target_baseline.manifest_file_hash,
        lock_file_hash: plan.target_baseline.lock_file_hash,
        axiom_report_file_hash: plan.target_baseline.axiom_report_file_hash,
        theorem_index_file_hash: plan.target_baseline.theorem_index_file_hash,
    };
    if !generated_match(baseline, &baseline_projection) {
        return false;
    }
    let source_module = match source_manifest
        .modules
        .iter()
        .find(|module| module.module == plan.selection.source_module)
    {
        Some(module) => module,
        None => return false,
    };
    let files = [
        (&plan.selection.source_path, plan.selection.source_file_hash),
        (&plan.selection.meta_path, plan.selection.meta_file_hash),
        (&plan.selection.replay_path, plan.selection.replay_file_hash),
        (
            &plan.selection.certificate_path,
            plan.selection.certificate_file_hash,
        ),
        (
            &plan.governance.request_path,
            plan.governance.request_file_hash,
        ),
    ];
    let artifact_inputs_current = source_module.source == plan.selection.source_path
        && source_module.meta.as_ref() == Some(&plan.selection.meta_path)
        && source_module.replay.as_ref() == Some(&plan.selection.replay_path)
        && source_module.certificate == plan.selection.certificate_path
        && source_module.expected_certificate_hash == plan.selection.certificate_hash
        && source_module.expected_export_hash == plan.selection.export_hash
        && source_module.expected_axiom_report_hash == plan.selection.axiom_report_hash
        && files.iter().all(|(path, hash)| {
            read_confined(source_root, path)
                .ok()
                .is_some_and(|bytes| package_file_hash(&bytes) == *hash)
        })
        && [
            (
                "docs/catalog-policy.md",
                plan.governance.catalog_policy_file_hash,
            ),
            (
                "docs/namespace-policy.md",
                plan.governance.namespace_policy_file_hash,
            ),
            (
                PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
                plan.target_baseline.verified_export_summary_file_hash,
            ),
            (
                PACKAGE_PUBLISH_PLAN_PATH,
                plan.target_baseline.publish_plan_file_hash,
            ),
        ]
        .iter()
        .all(|(path, hash)| {
            read_confined(baseline_root, &PackagePath::new(*path))
                .ok()
                .is_some_and(|bytes| package_file_hash(&bytes) == *hash)
        });
    artifact_inputs_current
        && declaration_plan_selection_current(source_root, source, &request, plan, &source_external)
}

pub(crate) fn declaration_plan_selection_current(
    source_root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    request: &npa_package::DeclarationPromotionRequest,
    plan: &MathlibPromotionPlanV2,
    source_external: &BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>,
) -> bool {
    let manifest = source.snapshot.validated.manifest();
    let Some(module) = manifest
        .modules
        .iter()
        .find(|module| module.module == request.source_module)
    else {
        return false;
    };
    let mut extraction_source_bytes = 0;
    let Some(source_text) =
        read_declaration_source(source_root, &module.source, &mut extraction_source_bytes)
            .ok()
            .and_then(|bytes| String::from_utf8(bytes).ok())
    else {
        return false;
    };
    let Ok(imported_interfaces) = direct_import_interfaces(
        source_root,
        source,
        &module.imports,
        extraction_source_bytes,
    ) else {
        return false;
    };
    let Ok(human_families) =
        collect_human_source_declaration_families(FileId(0), &source_text, &imported_interfaces)
    else {
        return false;
    };
    let Some(verified) = source
        .snapshot
        .decoded_module_records
        .values()
        .find(|record| record.key.module == request.source_module)
        .map(|record| &record.verified_module)
    else {
        return false;
    };
    let Ok((families, human_members)) = reconcile_families(verified, &human_families) else {
        return false;
    };
    let Ok(roots) = resolve_roots(request, verified, &human_families) else {
        return false;
    };
    let modules = source
        .snapshot
        .decoded_module_records
        .values()
        .map(|record| (record.key.module.clone(), record.verified_module.clone()))
        .collect::<BTreeMap<_, _>>();
    let Ok(closure) = declaration_dependency_closure(
        &modules,
        &roots,
        &families,
        source_external,
        DeclarationClosureLimits::default(),
    ) else {
        return false;
    };
    let Ok(declarations) = plan_declarations(&closure, &human_members) else {
        return false;
    };
    let generated_exports = declarations
        .iter()
        .flat_map(|row| row.generated_exports.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let actual_externalized = closure
        .externalized
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let planned_externalized = source_external
        .iter()
        .map(|(source, target)| (source.clone(), target.clone()))
        .collect::<BTreeSet<_>>();

    plan.selection.roots == plan_roots(request, &human_families)
        && plan.selection.materialized_declarations == declarations
        && plan.selection.generated_exports == generated_exports
        && plan.selection.declaration_closure_hash
            == PackageHash::from(closure.declaration_closure_hash)
        && actual_externalized == planned_externalized
}

fn declaration_equivalent_origins_current(
    roots: &[PathBuf],
    plan: &MathlibPromotionPlanV2,
) -> bool {
    if roots.len() != plan.equivalent_sources.len() {
        return false;
    }
    let mut rows = Vec::new();
    for root in roots {
        let Ok(snapshot) = load_package_audit_snapshot(
            root,
            COMMAND,
            promotion_plan_generated_read_mode(),
            PackageArtifactReferenceSummaryMode::Include,
        ) else {
            return false;
        };
        if validate_checked_generated(&snapshot).is_err() {
            return false;
        }
        let manifest = snapshot.snapshot.validated.manifest();
        let Some(module) = manifest
            .modules
            .iter()
            .find(|module| module.module == plan.selection.source_module)
        else {
            return false;
        };
        let Ok(source) = read_confined(root, &module.source) else {
            return false;
        };
        let Some(expected) = plan
            .equivalent_sources
            .iter()
            .find(|row| row.package == manifest.package && row.version == manifest.version)
        else {
            return false;
        };
        if expected.source_file_hash != package_file_hash(&source)
            || expected.certificate_file_hash != module.expected_certificate_file_hash
            || expected.certificate_hash != module.expected_certificate_hash
            || expected.export_hash != module.expected_export_hash
        {
            return false;
        }
        rows.push(expected.clone());
    }
    rows.sort();
    rows == plan.equivalent_sources
}

fn declaration_change_is_scoped(
    change: &Change,
    plan: &MathlibPromotionPlanV2,
    phase: PackagePromotionPhase,
) -> bool {
    if declaration_target_artifact_paths(plan).contains(&change.path) {
        return change.old.is_none();
    }
    matches!(
        change.path.as_str(),
        "npa-package.toml"
            | PACKAGE_LOCK_PATH
            | PACKAGE_AXIOM_REPORT_PATH
            | PACKAGE_THEOREM_INDEX_PATH
            | PACKAGE_THEOREM_PREMISE_REPORT_PATH
            | PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH
            | PACKAGE_PUBLISH_PLAN_PATH
    ) || (phase == PackagePromotionPhase::Tracked
        && change.path.as_str() == MATHLIB_PROMOTION_REGISTRY_PATH)
}

fn declaration_target_artifact_paths(plan: &MathlibPromotionPlanV2) -> [PackagePath; 4] {
    let base = plan.selection.target_module.as_dotted().replace('.', "/");
    [
        PackagePath::new(format!("{base}/source.npa")),
        PackagePath::new(format!("{base}/certificate.npcert")),
        PackagePath::new(format!("{base}/meta.json")),
        PackagePath::new(format!("{base}/replay.json")),
    ]
}

pub(crate) fn declaration_target_artifact_collision(
    root: &Path,
    plan: &MathlibPromotionPlanV2,
) -> Option<PackagePath> {
    declaration_target_artifact_paths(plan)
        .into_iter()
        .find(|path| !target_path_is_absent(root, path))
}

pub(crate) fn declaration_target_diff_is_scoped(
    baseline: &BTreeMap<PackagePath, Vec<u8>>,
    target: &BTreeMap<PackagePath, Vec<u8>>,
    plan: &MathlibPromotionPlanV2,
) -> bool {
    baseline.keys().all(|path| target.contains_key(path))
        && diff_snapshots(baseline, target).iter().all(|change| {
            declaration_change_is_scoped(change, plan, PackagePromotionPhase::Temporary)
        })
}

fn change_result(root_display: String, changes: Vec<Change>) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root_display);
    for change in changes {
        result.artifacts.push(CommandArtifact {
            kind: if change.old.is_some() {
                "promotion_replace"
            } else {
                "promotion_create"
            }
            .to_owned(),
            path: change.path.as_str().to_owned(),
        });
    }
    result
}

fn apply_declaration_stage(
    options: &PackageMaterializePromotionOptions,
    phase: PackagePromotionPhase,
    promotion_id: PackageHash,
    captured: &BTreeMap<PackagePath, Vec<u8>>,
    staged: &BTreeMap<PackagePath, Vec<u8>>,
    changes: &[Change],
    stage: &Path,
) -> CommandResult {
    let root_display = render_package_root(&options.target_root);
    let mut lock = match TargetLock::acquire(&options.target_root) {
        Ok(lock) => lock,
        Err(_) => {
            let _ = fs::remove_dir_all(stage);
            return failure(
                &root_display,
                "promotion_concurrent_update",
                TARGET_LOCK_PREFIX,
            );
        }
    };
    if let Err(reason) = locked_apply_preflight(&options.target_root, captured) {
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(&root_display, reason, "--target-root");
    }
    let transaction = match transaction_path(&options.target_root, promotion_id) {
        Ok(path) => path,
        Err(_) => {
            drop(lock);
            let _ = fs::remove_dir_all(stage);
            return failure(
                &root_display,
                "promotion_materialize_unscoped_path",
                "--target-root",
            );
        }
    };
    let journal = transaction
        .file_name()
        .and_then(|name| name.to_str())
        .map(str::to_owned);
    if lock
        .record(Some(promotion_id), "materialize", journal.as_deref())
        .is_err()
    {
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(
            &root_display,
            "promotion_concurrent_update",
            TARGET_LOCK_PREFIX,
        );
    }
    let mut visible = false;
    if apply_transaction(
        &options.target_root,
        phase,
        promotion_id,
        changes,
        &mut visible,
    )
    .is_err()
    {
        let rolled_back =
            !visible || rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_concurrent_update"
            } else {
                "promotion_recovery_required"
            },
            "--target-root",
        );
    }
    if tree_snapshot(&options.target_root).ok().as_ref() != Some(staged) {
        let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_materialize_target_identity_mismatch"
            } else {
                "promotion_recovery_required"
            },
            "--target-root",
        );
    }
    let valid = load_package_audit_snapshot(
        &options.target_root,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    )
    .ok()
    .is_some_and(|snapshot| validate_checked_generated(&snapshot).is_ok());
    if !valid {
        let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_materialize_target_identity_mismatch"
            } else {
                "promotion_recovery_required"
            },
            "--target-root",
        );
    }
    if phase == PackagePromotionPhase::Tracked
        && run_package_validate_promotion_origin_registry(
            PackageValidatePromotionOriginRegistryOptions {
                common: PackageCommonOptions {
                    root: options.target_root.clone(),
                    json: false,
                },
                source_roots: std::iter::once(options.common.root.clone())
                    .chain(options.equivalent_origin_roots.iter().cloned())
                    .collect(),
                previous_registry: None,
            },
        )
        .status
            != CommandStatus::Passed
    {
        let rolled_back = rollback_transaction(&options.target_root, &transaction).is_ok();
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(
            &root_display,
            if rolled_back {
                "promotion_registry_target_identity_mismatch"
            } else {
                "promotion_recovery_required"
            },
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    if finalize_transaction(&transaction).is_err() {
        drop(lock);
        let _ = fs::remove_dir_all(stage);
        return failure(
            &root_display,
            "promotion_recovery_required",
            "--target-root",
        );
    }
    let _ = lock.record(Some(promotion_id), "materialize", None);
    drop(lock);
    let _ = fs::remove_dir_all(stage);
    change_result(root_display, changes.to_vec())
}

fn update_stage_registry_v2(
    stage: &Path,
    plan_path: &PackagePath,
    plan_bytes: &[u8],
    attestation_path: &PackagePath,
    attestation_bytes: &[u8],
    plan: &MathlibPromotionPlanV2,
    attestation: &npa_package::VerifiedMaterializationAttestation,
) -> Result<(), ()> {
    let registry_path = stage.join(MATHLIB_PROMOTION_REGISTRY_PATH);
    let registry_source = fs::read_to_string(&registry_path).map_err(|_| ())?;
    enum Previous {
        V1(npa_package::PromotionOriginRegistry),
        V2(npa_package::PromotionOriginRegistryV2),
    }
    let (previous, mut registry) = match parse_promotion_origin_registry_versioned(&registry_source)
        .map_err(|_| ())?
    {
        ParsedPromotionOriginRegistry::V2(previous) => (Previous::V2(previous.clone()), previous),
        ParsedPromotionOriginRegistry::V1(previous) => {
            let migrated = migrate_promotion_origin_registry_v1_to_v2(&previous).map_err(|_| ())?;
            (Previous::V1(previous), migrated)
        }
    };
    let snapshot = load_package_audit_snapshot(
        stage,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    )
    .map_err(|_| ())?;
    let index = snapshot.snapshot.project_theorem_index().map_err(|_| ())?;
    let mut theorems = index
        .entries
        .iter()
        .filter(|entry| {
            entry.global_ref.module == plan.selection.target_module
                && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
        })
        .map(|entry| PromotionDeclarationTargetTheorem {
            target_name: entry.global_ref.name.clone(),
            statement_hash: entry.statement.core_hash,
        })
        .collect::<Vec<_>>();
    theorems.sort();
    let edge_hash = promotion_plan_v2_dependency_edge_hash(
        &plan.selection.materialized_declarations,
        &plan.dependency_mappings,
    )
    .map_err(|_| ())?;
    let canonical_source = npa_package::PromotionPlanV2EquivalentSource {
        package: plan.source.package.clone(),
        version: plan.source.version.clone(),
        source_module: plan.selection.source_module.clone(),
        source_file_hash: plan.selection.source_file_hash,
        certificate_file_hash: plan.selection.certificate_file_hash,
        certificate_hash: plan.selection.certificate_hash,
        export_hash: plan.selection.export_hash,
        declaration_closure_hash: plan.selection.declaration_closure_hash,
        dependency_edge_hash: edge_hash,
    };
    let entry = DeclarationClosureRegistryEntry {
        promotion_id: plan.promotion_id,
        lifecycle: "active".to_owned(),
        introduced_version: plan.target_baseline.planned_version.clone(),
        canonical_source,
        equivalent_sources: plan.equivalent_sources.clone(),
        source_module: plan.selection.source_module.clone(),
        target_module: plan.selection.target_module.clone(),
        roots: plan.selection.roots.clone(),
        closure: plan.selection.materialized_declarations.clone(),
        dependency_mappings: plan.dependency_mappings.clone(),
        target_revisions: vec![PromotionDeclarationTargetRevision {
            target_version: plan.target_baseline.planned_version.clone(),
            target_source_file_hash: attestation.target.source_file_hash,
            target_meta_file_hash: attestation.target.meta_file_hash,
            target_replay_file_hash: attestation.target.replay_file_hash,
            target_certificate_file_hash: attestation.target.certificate_file_hash,
            target_certificate_hash: attestation.target.certificate_hash,
            target_export_hash: attestation.target.export_hash,
            target_axiom_report_hash: attestation.target.axiom_report_hash,
            theorems,
        }],
        evidence: PromotionDeclarationEvidence {
            kind: "verified_declaration_materialization_v1".to_owned(),
            plan_schema: plan.schema.clone(),
            plan_path: plan_path.clone(),
            plan_file_hash: package_file_hash(plan_bytes),
            attestation_schema: attestation.schema.clone(),
            attestation_path: attestation_path.clone(),
            attestation_file_hash: package_file_hash(attestation_bytes),
            declaration_closure_hash: plan.selection.declaration_closure_hash,
            normalized_closure_hash: attestation.normalized_closure_hash,
            catalog_policy_file_hash: plan.governance.catalog_policy_file_hash,
            namespace_policy_file_hash: plan.governance.namespace_policy_file_hash,
        },
        // Verified maturity is the admission evidence itself. This array is
        // reserved for later exact-target review events.
        maturity_events: Vec::new(),
    };
    validate_declaration_registry_entry_admission(&entry, plan, attestation).map_err(|_| ())?;
    registry
        .entries
        .push(PromotionOriginEntryV2::DeclarationClosureV1(Box::new(
            entry,
        )));
    registry
        .entries
        .sort_by_key(PromotionOriginEntryV2::promotion_id);
    registry.generation = registry.generation.checked_add(1).ok_or(())?;
    registry.refresh_hash().map_err(|_| ())?;
    match previous {
        Previous::V1(previous) => {
            validate_promotion_origin_registry_v1_to_v2_transition(&previous, &registry)
                .map_err(|_| ())?;
        }
        Previous::V2(previous) => {
            validate_promotion_origin_registry_v2_transition(&previous, &registry)
                .map_err(|_| ())?;
        }
    }
    fs::write(registry_path, registry.canonical_json().map_err(|_| ())?).map_err(|_| ())
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use std::os::unix::fs::symlink;
    use std::sync::atomic::{AtomicU64, Ordering};

    use npa_cert::Name;
    use npa_package::{
        PackageId, PackageVersion, PromotionGovernance, PromotionPackageSnapshot,
        PromotionPlanSelectedModule, PromotionPlanTheorem, PromotionTargetSnapshot,
        MATHLIB_PROMOTION_PLAN_V2_SCHEMA,
    };

    use super::*;

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn selected(source: &str, target: &str, imports: &[&str]) -> PromotionPlanSelectedModule {
        PromotionPlanSelectedModule {
            source_module: Name::from_dotted(source),
            target_module: Name::from_dotted(target),
            source_path: PackagePath::new(format!("{}/source.npa", source.replace('.', "/"))),
            source_file_hash: package_file_hash(b"source"),
            certificate_file_hash: package_file_hash(b"certificate-file"),
            certificate_hash: package_file_hash(b"certificate"),
            export_hash: package_file_hash(b"export"),
            axiom_report_hash: package_file_hash(b"axioms"),
            imports: imports.iter().map(Name::from_dotted).collect(),
            exports: Vec::new(),
            theorems: Vec::<PromotionPlanTheorem>::new(),
        }
    }

    fn apply_test_transaction(
        target: &Path,
        phase: PackagePromotionPhase,
        promotion_id: PackageHash,
        changes: &[Change],
    ) -> io::Result<()> {
        let mut transaction_visible = false;
        apply_transaction(
            target,
            phase,
            promotion_id,
            changes,
            &mut transaction_visible,
        )
    }

    #[test]
    fn legacy_plan_dispatch_ignores_embedded_v2_schema_text() {
        let hash = |value: &str| package_file_hash(value.as_bytes());
        let mut plan = MathlibPromotionPlan {
            schema: MATHLIB_PROMOTION_PLAN_SCHEMA.to_owned(),
            promotion_id: PackageHash::new([0; 32]),
            source: PromotionPackageSnapshot {
                package: PackageId::new("npa-project-example-proofs"),
                version: PackageVersion::new("0.1.0"),
                manifest_file_hash: hash("source-manifest"),
                lock_file_hash: hash("source-lock"),
                axiom_report_file_hash: hash("source-axioms"),
                theorem_index_file_hash: hash("source-index"),
            },
            target_baseline: PromotionTargetSnapshot {
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.2.1"),
                planned_version: PackageVersion::new("0.2.2"),
                manifest_file_hash: hash("target-manifest"),
                lock_file_hash: hash("target-lock"),
                axiom_report_file_hash: hash("target-axioms"),
                theorem_index_file_hash: hash("target-index"),
            },
            governance: PromotionGovernance {
                acceptance_policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
                acceptance_policy_version: 2,
                acceptance_policy_file_hash: hash("acceptance-policy"),
                source_acceptance_path: PackagePath::new("l2-acceptance.json"),
                source_acceptance_schema: "npa.l2_acceptance.v2".to_owned(),
                source_acceptance_file_hash: hash("acceptance"),
                transport_policy_id: "finitefield-org.npa-mathlib.l2-namespace-transport"
                    .to_owned(),
                transport_policy_version: 1,
                transport_policy_file_hash: hash("transport-policy"),
                mapping_path: PackagePath::new(MATHLIB_PROMOTION_PLAN_V2_SCHEMA),
                mapping_schema: "npa.l2_namespace_transport_request.v1".to_owned(),
                mapping_file_hash: hash("mapping"),
                registry_file_hash: hash("registry"),
            },
            selected_modules: vec![selected(
                "Proofs.Ai.Example.Basic",
                "Mathlib.Example.Basic",
                &[],
            )],
            dependency_mappings: Vec::new(),
            equivalent_sources: Vec::new(),
            compatibility_alias: "none".to_owned(),
            plan_hash: PackageHash::new([0; 32]),
            proof_evidence: false,
        };
        plan.finalize().unwrap();
        let source = plan.canonical_json().unwrap();

        assert!(source.contains(MATHLIB_PROMOTION_PLAN_V2_SCHEMA));
        assert!(parse_mathlib_promotion_plan_json(&source).is_ok());
        assert!(!is_declaration_promotion_plan(&source));
    }

    #[test]
    fn import_rewrite_changes_only_import_name_spans() {
        let source = "-- Proofs.Ai.Dependency remains documentation\nimport Proofs.Ai.Dependency\nnotation \"Proofs.Ai.Dependency\" => Nat.zero\n\ndef keep : Type := Type\n";
        let mapping = BTreeMap::from([(
            "Proofs.Ai.Dependency".to_owned(),
            "Mathlib.Dependency".to_owned(),
        )]);
        assert_eq!(
            rewrite_imports(source, &mapping).unwrap(),
            "-- Proofs.Ai.Dependency remains documentation\nimport Mathlib.Dependency\nnotation \"Proofs.Ai.Dependency\" => Nat.zero\n\ndef keep : Type := Type\n"
        );

        let leaked = "import Proofs.Ai.Dependency\n\ndef keep : Type := Proofs.Ai.Dependency\n";
        assert_eq!(
            rewrite_imports(leaked, &mapping),
            Err("promotion_materialize_source_rewrite_failed")
        );
    }

    #[cfg(unix)]
    #[test]
    fn tree_snapshot_rejects_literal_backslash_paths() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-promotion-snapshot-backslash-{}-{serial}",
            std::process::id()
        ));
        fs::create_dir(&root).unwrap();
        let hostile_name = format!("{}tmp{}npa-promotion-victim", '\\', '\\');
        fs::write(root.join(hostile_name), b"controlled").unwrap();

        assert!(tree_snapshot(&root).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn tree_snapshot_only_hides_root_git_metadata() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-promotion-snapshot-prefixed-{}-{serial}",
            std::process::id()
        ));
        fs::create_dir(&root).unwrap();
        fs::create_dir_all(root.join(".git")).unwrap();
        fs::write(root.join(".git/root-marker"), b"ignored root metadata").unwrap();
        fs::create_dir_all(root.join("nested/.git")).unwrap();
        let prefixed_path = PackagePath::new(".npa-promotion-unscoped");
        let nested_git_path = PackagePath::new("nested/.git/marker");
        fs::write(root.join(prefixed_path.as_str()), b"unscoped").unwrap();
        fs::write(root.join(nested_git_path.as_str()), b"nested content").unwrap();

        let snapshot = tree_snapshot(&root).unwrap();
        assert_eq!(
            snapshot.get(&prefixed_path).map(Vec::as_slice),
            Some(&b"unscoped"[..])
        );
        assert_eq!(
            snapshot.get(&nested_git_path).map(Vec::as_slice),
            Some(&b"nested content"[..])
        );
        assert!(!snapshot.contains_key(&PackagePath::new(".git/root-marker")));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn write_tree_snapshot_rejects_absolute_package_paths() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let target = std::env::temp_dir().join(format!(
            "npa-promotion-snapshot-target-{}-{serial}",
            std::process::id()
        ));
        let snapshot = BTreeMap::from([(PackagePath::new("/tmp/npa-victim"), b"x".to_vec())]);

        assert!(write_tree_snapshot(&snapshot, &target).is_err());
        assert!(!target.exists());
    }

    #[test]
    fn selected_modules_are_ordered_by_dependencies_then_target_name() {
        let modules = vec![
            selected("Proofs.Ai.Top", "Mathlib.A.Top", &["Proofs.Ai.Foundation"]),
            selected("Proofs.Ai.Other", "Mathlib.B.Other", &[]),
            selected("Proofs.Ai.Foundation", "Mathlib.Z.Foundation", &[]),
        ];
        let names = selected_topological_order(&modules)
            .unwrap()
            .into_iter()
            .map(|module| module.target_module.as_dotted())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            ["Mathlib.B.Other", "Mathlib.Z.Foundation", "Mathlib.A.Top"]
        );
    }

    #[test]
    fn replacement_order_keeps_manifest_before_generated_state_and_registry_last() {
        let change = |path: &str| Change {
            path: PackagePath::new(path),
            old: None,
            new: Vec::new(),
        };
        assert!(
            change_order(&change("Mathlib/Logic/New/certificate.npcert"))
                < change_order(&change("npa-package.toml"))
        );
        assert!(
            change_order(&change("npa-package.toml")) < change_order(&change(PACKAGE_LOCK_PATH))
        );
        assert_eq!(
            change_order(&change(PACKAGE_LOCK_PATH)).0,
            change_order(&change(PACKAGE_THEOREM_INDEX_PATH)).0
        );
        assert!(
            change_order(&change(PACKAGE_THEOREM_INDEX_PATH))
                < change_order(&change(MATHLIB_PROMOTION_REGISTRY_PATH))
        );
    }

    #[test]
    fn snapshot_writer_never_removes_a_preexisting_stage() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-promotion-existing-stage-{}-{serial}",
            std::process::id()
        ));
        let stage = root.join("stage");
        fs::create_dir_all(&stage).unwrap();
        fs::write(stage.join("sentinel.txt"), b"belongs to another process").unwrap();
        let snapshot = BTreeMap::from([(PackagePath::new("new.txt"), b"new".to_vec())]);

        assert!(write_tree_snapshot(&snapshot, &stage).is_err());
        assert_eq!(
            fs::read(stage.join("sentinel.txt")).unwrap(),
            b"belongs to another process"
        );
        assert!(!stage.join("new.txt").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn transaction_rolls_back_and_finalizes_exact_bytes() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let target = std::env::temp_dir().join(format!(
            "npa-promotion-materialize-{}-{serial}",
            std::process::id()
        ));
        fs::create_dir(&target).unwrap();
        fs::write(target.join("old.txt"), b"old").unwrap();
        let changes = vec![
            Change {
                path: PackagePath::new("old.txt"),
                old: Some(b"old".to_vec()),
                new: b"new".to_vec(),
            },
            Change {
                path: PackagePath::new("created.txt"),
                old: None,
                new: b"created".to_vec(),
            },
        ];
        let promotion_id = package_file_hash(b"transaction-test");
        let transaction = transaction_path(&target, promotion_id).unwrap();
        let colliding_temporary = replacement_temp_path(&target, &changes[0].path).unwrap();
        fs::write(&colliding_temporary, b"preexisting").unwrap();
        let mut transaction_visible = true;
        assert!(apply_transaction(
            &target,
            PackagePromotionPhase::Temporary,
            promotion_id,
            &changes,
            &mut transaction_visible,
        )
        .is_err());
        assert!(!transaction_visible);
        assert_eq!(fs::read(&colliding_temporary).unwrap(), b"preexisting");
        assert!(!transaction.exists());
        fs::remove_file(colliding_temporary).unwrap();

        apply_test_transaction(
            &target,
            PackagePromotionPhase::Temporary,
            promotion_id,
            &changes,
        )
        .unwrap();
        fs::write(transaction.join("journal.next"), b"interrupted replacement").unwrap();
        rollback_transaction(&target, &transaction).unwrap();
        assert_eq!(fs::read(target.join("old.txt")).unwrap(), b"old");
        assert!(!target.join("created.txt").exists());

        apply_test_transaction(
            &target,
            PackagePromotionPhase::Temporary,
            promotion_id,
            &changes,
        )
        .unwrap();
        finalize_transaction(&transaction).unwrap();
        assert_eq!(fs::read(target.join("old.txt")).unwrap(), b"new");
        assert_eq!(fs::read(target.join("created.txt")).unwrap(), b"created");
        assert!(!transaction.exists());
        fs::remove_dir_all(target).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn rollback_rejects_target_symlink_ancestors() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-promotion-symlink-recovery-{}-{serial}",
            std::process::id()
        ));
        let target = root.join("target");
        let outside = root.join("outside");
        fs::create_dir_all(target.join("nested")).unwrap();
        fs::create_dir_all(&outside).unwrap();
        fs::write(target.join("nested/state.txt"), b"old").unwrap();
        let changes = vec![Change {
            path: PackagePath::new("nested/state.txt"),
            old: Some(b"old".to_vec()),
            new: b"new".to_vec(),
        }];
        let promotion_id = package_file_hash(b"symlink-recovery-test");
        let transaction = transaction_path(&target, promotion_id).unwrap();
        apply_test_transaction(
            &target,
            PackagePromotionPhase::Tracked,
            promotion_id,
            &changes,
        )
        .unwrap();

        fs::remove_file(target.join("nested/state.txt")).unwrap();
        fs::remove_dir(target.join("nested")).unwrap();
        fs::write(outside.join("state.txt"), b"new").unwrap();
        symlink(&outside, target.join("nested")).unwrap();

        assert!(rollback_transaction(&target, &transaction).is_err());
        assert_eq!(fs::read(outside.join("state.txt")).unwrap(), b"new");
        assert!(transaction.exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn transaction_layout_rejects_broken_journal_next_symlink() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-promotion-broken-journal-next-{}-{serial}",
            std::process::id()
        ));
        let target = root.join("target");
        fs::create_dir_all(&target).unwrap();
        let changes = vec![Change {
            path: PackagePath::new("state.txt"),
            old: None,
            new: b"new".to_vec(),
        }];
        let promotion_id = package_file_hash(b"broken-journal-next-test");
        let transaction = transaction_path(&target, promotion_id).unwrap();
        apply_test_transaction(
            &target,
            PackagePromotionPhase::Tracked,
            promotion_id,
            &changes,
        )
        .unwrap();
        let journal = parse_promotion_transaction_json(
            &fs::read_to_string(transaction.join("journal.json")).unwrap(),
        )
        .unwrap();
        symlink("missing-journal", transaction.join("journal.next")).unwrap();

        assert!(!transaction_layout_is_exact(&transaction, &journal));
        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn dangling_transaction_and_temporary_symlinks_fail_closed() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-promotion-dangling-sentinels-{}-{serial}",
            std::process::id()
        ));
        let target = root.join("target");
        fs::create_dir_all(&target).unwrap();
        let promotion_id = package_file_hash(b"dangling-sentinel-test");
        let transaction = transaction_path(&target, promotion_id).unwrap();
        symlink("missing-transaction", &transaction).unwrap();

        assert!(pending_transaction_exists(&target));
        assert_eq!(
            locked_apply_preflight(&target, &BTreeMap::new()),
            Err("promotion_recovery_required")
        );
        assert!(rollback_transaction(&target, &transaction).is_err());
        fs::remove_file(&transaction).unwrap();

        let change = Change {
            path: PackagePath::new("state.txt"),
            old: None,
            new: b"new".to_vec(),
        };
        let temporary = replacement_temp_path(&target, &change.path).unwrap();
        symlink("missing-temporary", &temporary).unwrap();
        assert!(apply_test_transaction(
            &target,
            PackagePromotionPhase::Tracked,
            promotion_id,
            &[change]
        )
        .is_err());
        assert!(!path_entry_exists(&transaction).unwrap());
        fs::remove_dir_all(root).unwrap();
    }
}
