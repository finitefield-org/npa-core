//! Independently validate declaration-level promotion materialization.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::Path,
    sync::atomic::{AtomicU64, Ordering},
};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_cert::{
    declaration_dependency_closure, normalized_declaration_closure_hash,
    normalized_declaration_closure_projection, resolve_verified_declaration_export,
    DeclarationClosureLimits, GlobalDeclarationIdentity, Name, ValidatedSourceDeclarationFamilies,
    VerifiedModule,
};
use npa_frontend::{collect_human_source_declaration_families, FileId};
use npa_package::{
    format_package_hash, package_file_hash, parse_mathlib_promotion_plan_v2_json,
    MathlibPromotionPlanV2, PackageHash, PackagePath, PromotionAttestationArtifactRef,
    PromotionCheckerVerdict, PromotionGateResult, PromotionMaterializedTarget,
    VerifiedMaterializationAttestation, MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA,
    MATHLIB_PROMOTION_PLAN_V2_SCHEMA, MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA,
    PACKAGE_PUBLISH_PLAN_PATH, PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

use crate::{
    args::{
        PackageAxiomReportOptions, PackageBuildCertsOptions, PackageBuildCheckCacheMode,
        PackageBuildSelection, PackageChecker, PackageCommonOptions, PackageExportSummaryOptions,
        PackageIndexOptions, PackagePublishPlanOptions, PackageTimingMode,
        PackageValidatePromotionMaterializationOptions,
    },
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::render_package_root,
    governance_writer::{
        confined_governance_path, write_governance_artifact, GovernanceOutputPolicy,
    },
    package_api::v1::verify_certs_full,
    package_artifacts::{
        load_package_audit_snapshot, LoadedPackageAuditSnapshot, PackageGeneratedArtifactReadMode,
    },
    package_axiom_report::run_package_axiom_report,
    package_build::run_package_build_certs,
    package_check::run_package_check,
    package_export_summary::run_package_export_summary,
    package_hashes::run_package_check_hashes,
    package_index::run_package_index,
    package_promotion_materialize::{
        build_declaration_materialization_candidate, declaration_plan_inputs_current,
        declaration_target_artifact_collision, declaration_target_diff_is_scoped, tree_snapshot,
        validate_materialized_declaration_inventory, write_tree_snapshot,
    },
    package_promotion_prepare_declaration::{
        direct_import_interfaces, endpoint_record, plan_declarations, read_declaration_source,
        reconcile_families, DeclarationSourceExtractionError, HumanMemberMap,
    },
    package_promotion_registry::{promotion_plan_generated_read_mode, validate_checked_generated},
    package_publish::run_package_publish_plan,
    package_verify::run_package_verify_certs,
};

const COMMAND: &str = "package validate-promotion-materialization";

/// Validate a disposable target and create or check its canonical attestation.
pub fn run_package_validate_promotion_materialization(
    options: PackageValidatePromotionMaterializationOptions,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let plan_path = PackagePath::new(options.plan.to_string_lossy());
    let plan_bytes = match read_confined(&options.common.root, &plan_path) {
        Some(bytes) => bytes,
        None => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                plan_path.as_str(),
            )
        }
    };
    let plan_source = match std::str::from_utf8(&plan_bytes) {
        Ok(source) => source,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                plan_path.as_str(),
            )
        }
    };
    let plan = match parse_mathlib_promotion_plan_v2_json(plan_source) {
        Ok(plan) => plan,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                plan_path.as_str(),
            )
        }
    };
    if let Some(collision) =
        declaration_target_artifact_collision(&options.target_baseline_root, &plan)
    {
        return failure(
            &root_display,
            "promotion_declaration_target_collision",
            collision.as_str(),
        );
    }
    let source = match load_plan_snapshot(&options.common.root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    let baseline = match load_plan_snapshot(&options.target_baseline_root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    let target = match load_target_snapshot(&options.target_root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    for snapshot in [&source, &baseline, &target] {
        if let Err(diagnostic) = validate_checked_generated(snapshot) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    if !positive_package_gates_pass(&options.common.root, false)
        || !positive_package_gates_pass(&options.target_root, true)
    {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            "package-gates",
        );
    }
    if !declaration_plan_inputs_current(
        &options.common.root,
        &options.target_baseline_root,
        &source,
        &baseline,
        &plan,
    ) || target.snapshot.validated.manifest().package != plan.target_baseline.package
        || target.snapshot.validated.manifest().version != plan.target_baseline.planned_version
        || validate_materialized_declaration_inventory(&options.target_root, &plan).is_err()
    {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            plan_path.as_str(),
        );
    }
    let baseline_tree = match tree_snapshot(&options.target_baseline_root) {
        Ok(tree) => tree,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                "--target-baseline-root",
            )
        }
    };
    let target_tree = match tree_snapshot(&options.target_root) {
        Ok(tree) => tree,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                "--target-root",
            )
        }
    };
    // Bind the semantic snapshot used below to the exact byte snapshot being
    // attested. A concurrent writer may otherwise change the target between
    // the initial audit load and this tree capture.
    let target = match load_target_snapshot(&options.target_root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&target) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    if target.snapshot.validated.manifest().package != plan.target_baseline.package
        || target.snapshot.validated.manifest().version != plan.target_baseline.planned_version
        || validate_materialized_declaration_inventory(&options.target_root, &plan).is_err()
        || tree_snapshot(&options.target_root).ok().as_ref() != Some(&target_tree)
    {
        return failure(
            &root_display,
            "promotion_concurrent_update",
            "--target-root",
        );
    }
    if !declaration_target_diff_is_scoped(&baseline_tree, &target_tree, &plan) {
        return failure(
            &root_display,
            "promotion_materialize_unscoped_path",
            "--target-root",
        );
    }
    let (rebuilt, omissions) = match deterministic_rebuilds(
        &options.common.root,
        &options.target_baseline_root,
        &baseline_tree,
        &plan,
    ) {
        Ok(value) => value,
        Err(reason) => return failure(&root_display, reason, "--target-root"),
    };
    if rebuilt != target_tree {
        return failure(
            &root_display,
            "promotion_materialization_nondeterministic",
            "--target-root",
        );
    }
    if !declaration_plan_inputs_current(
        &options.common.root,
        &options.target_baseline_root,
        &source,
        &baseline,
        &plan,
    ) || tree_snapshot(&options.target_baseline_root).ok().as_ref() != Some(&baseline_tree)
        || tree_snapshot(&options.target_root).ok().as_ref() != Some(&target_tree)
    {
        return failure(
            &root_display,
            "promotion_concurrent_update",
            "--target-root",
        );
    }
    let normalized_closure_hash = match normalized_closure_identity(
        &options.common.root,
        &options.target_root,
        &source,
        &baseline,
        &target,
        &plan,
    ) {
        Ok(hash) => hash,
        Err(reason) => return failure(&root_display, reason, "--target-root"),
    };
    let target_module = match target
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .find(|module| module.module == plan.selection.target_module)
    {
        Some(module) => module,
        None => {
            return failure(
                &root_display,
                "promotion_declaration_export_mismatch",
                "--target-root",
            )
        }
    };
    let target_record = match record_for(&target, &plan.selection.target_module) {
        Some(record) => record,
        None => {
            return failure(
                &root_display,
                "promotion_declaration_export_mismatch",
                "--target-root",
            )
        }
    };
    let base = plan.selection.target_module.as_dotted().replace('.', "/");
    let target_source_path = PackagePath::new(format!("{base}/source.npa"));
    let target_meta_path = PackagePath::new(format!("{base}/meta.json"));
    let target_replay_path = PackagePath::new(format!("{base}/replay.json"));
    let target_certificate_path = PackagePath::new(format!("{base}/certificate.npcert"));
    let Some(target_source) = target_tree.get(&target_source_path) else {
        return failure(
            &root_display,
            "promotion_declaration_export_mismatch",
            target_source_path.as_str(),
        );
    };
    let Some(target_meta) = target_tree.get(&target_meta_path) else {
        return failure(
            &root_display,
            "promotion_declaration_export_mismatch",
            target_meta_path.as_str(),
        );
    };
    let Some(target_replay) = target_tree.get(&target_replay_path) else {
        return failure(
            &root_display,
            "promotion_declaration_export_mismatch",
            target_replay_path.as_str(),
        );
    };
    let Some(target_certificate) = target_tree.get(&target_certificate_path) else {
        return failure(
            &root_display,
            "promotion_declaration_export_mismatch",
            target_certificate_path.as_str(),
        );
    };
    let Some(target_axiom) = target.checked_generated.axiom_report_json.as_deref() else {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            "generated/axiom-report.json",
        );
    };
    let Some(target_index) = target.checked_generated.theorem_index_json.as_deref() else {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            "generated/theorem-index.json",
        );
    };
    let Some(export_summary) =
        target_tree.get(&PackagePath::new(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH))
    else {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
        );
    };
    let Some(publish_plan) = target_tree.get(&PackagePath::new(PACKAGE_PUBLISH_PLAN_PATH)) else {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            PACKAGE_PUBLISH_PLAN_PATH,
        );
    };
    let request_bytes = match read_confined(&options.common.root, &plan.governance.request_path) {
        Some(bytes) => bytes,
        None => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                plan.governance.request_path.as_str(),
            )
        }
    };
    let source_record = match record_for(&source, &plan.selection.source_module) {
        Some(record) => record,
        None => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                plan.selection.source_path.as_str(),
            )
        }
    };
    let mut checker_verdicts = vec![
        PromotionCheckerVerdict {
            side: "source".to_owned(),
            checker: "npa-checker-ref".to_owned(),
            profile: "reference".to_owned(),
            cache: "off".to_owned(),
            certificate_hash: source_record.key.certificate_hash,
            export_hash: source_record.key.export_hash,
            status: "passed".to_owned(),
        },
        PromotionCheckerVerdict {
            side: "target".to_owned(),
            checker: "npa-checker-ref".to_owned(),
            profile: "reference".to_owned(),
            cache: "off".to_owned(),
            certificate_hash: target_record.key.certificate_hash,
            export_hash: target_record.key.export_hash,
            status: "passed".to_owned(),
        },
    ];
    checker_verdicts.sort();
    let mut gate_results = [
        ("source", "package-check", plan.source.manifest_file_hash),
        ("source", "check-hashes", plan.source.lock_file_hash),
        (
            "source",
            "build-certs-check",
            source_record.key.certificate_hash,
        ),
        (
            "source",
            "axiom-report-check",
            plan.source.axiom_report_file_hash,
        ),
        (
            "source",
            "theorem-index-check",
            plan.source.theorem_index_file_hash,
        ),
        (
            "source",
            "reference-verification",
            source_record.key.certificate_hash,
        ),
        (
            "target",
            "package-check",
            target.snapshot.manifest.file_hash,
        ),
        (
            "target",
            "check-hashes",
            package_file_hash(target.package_lock_json.as_bytes()),
        ),
        (
            "target",
            "build-certs-check",
            target_record.key.certificate_hash,
        ),
        (
            "target",
            "axiom-report-check",
            package_file_hash(target_axiom.as_bytes()),
        ),
        (
            "target",
            "theorem-index-check",
            package_file_hash(target_index.as_bytes()),
        ),
        (
            "target",
            "export-summary-check",
            package_file_hash(export_summary),
        ),
        (
            "target",
            "publish-plan-check",
            package_file_hash(publish_plan),
        ),
        (
            "target",
            "deterministic-rebuild",
            package_file_hash(target_source),
        ),
        (
            "target",
            "diff-allowlist",
            package_file_hash(
                target
                    .snapshot
                    .validated
                    .manifest()
                    .package
                    .as_str()
                    .as_bytes(),
            ),
        ),
        (
            "target",
            "export-import-inventory",
            target_record.key.export_hash,
        ),
        (
            "target",
            "normalized-closure-equality",
            normalized_closure_hash,
        ),
        (
            "target",
            "reference-verification",
            target_record.key.certificate_hash,
        ),
    ]
    .into_iter()
    .map(|(side, gate, identity_hash)| PromotionGateResult {
        side: side.to_owned(),
        gate: gate.to_owned(),
        status: "passed".to_owned(),
        identity_hash,
    })
    .collect::<Vec<_>>();
    gate_results.sort();
    let mut attestation = VerifiedMaterializationAttestation {
        schema: MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA.to_owned(),
        promotion_id: plan.promotion_id,
        request: PromotionAttestationArtifactRef {
            path: plan.governance.request_path.clone(),
            schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
            file_hash: package_file_hash(&request_bytes),
            identity_hash: plan.governance.request_file_hash,
        },
        plan: PromotionAttestationArtifactRef {
            path: plan_path.clone(),
            schema: MATHLIB_PROMOTION_PLAN_V2_SCHEMA.to_owned(),
            file_hash: package_file_hash(&plan_bytes),
            identity_hash: plan.plan_hash,
        },
        source: plan.source.clone(),
        target_baseline: plan.target_baseline.clone(),
        target: PromotionMaterializedTarget {
            package: plan.target_baseline.package.clone(),
            version: plan.target_baseline.planned_version.clone(),
            manifest_file_hash: target.snapshot.manifest.file_hash,
            lock_file_hash: package_file_hash(target.package_lock_json.as_bytes()),
            axiom_report_file_hash: package_file_hash(target_axiom.as_bytes()),
            theorem_index_file_hash: package_file_hash(target_index.as_bytes()),
            verified_export_summary_file_hash: package_file_hash(export_summary),
            publish_plan_file_hash: package_file_hash(publish_plan),
            source_path: target_source_path,
            source_file_hash: package_file_hash(target_source),
            meta_path: target_meta_path,
            meta_file_hash: package_file_hash(target_meta),
            replay_path: target_replay_path,
            replay_file_hash: package_file_hash(target_replay),
            certificate_path: target_certificate_path,
            certificate_file_hash: package_file_hash(target_certificate),
            certificate_hash: target_record.key.certificate_hash,
            export_hash: target_record.key.export_hash,
            axiom_report_hash: target_module.expected_axiom_report_hash,
        },
        source_declaration_closure_hash: plan.selection.declaration_closure_hash,
        normalized_closure_hash,
        materialized_declarations: plan.selection.materialized_declarations.clone(),
        generated_exports: plan.selection.generated_exports.clone(),
        externalized_dependencies: plan.dependency_mappings.clone(),
        replay_omissions: omissions,
        checker_verdicts,
        gate_results,
        status: "verified_materialization_accepted".to_owned(),
        attestation_hash: PackageHash::new([0; 32]),
        proof_evidence: false,
    };
    if attestation.finalize().is_err() {
        return failure(
            &root_display,
            "promotion_verification_attestation_stale",
            "--out",
        );
    }
    let json = match attestation.canonical_json() {
        Ok(json) => json,
        Err(_) => {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                "--out",
            )
        }
    };
    let out = PackagePath::new(options.out.to_string_lossy());
    if options.check {
        if read_confined(&options.common.root, &out).as_deref() != Some(json.as_bytes()) {
            return failure(
                &root_display,
                "promotion_verification_attestation_stale",
                out.as_str(),
            );
        }
    } else if let Err(diagnostic) = write_governance_artifact(
        &options.common.root,
        &out,
        json.as_bytes(),
        GovernanceOutputPolicy::CreateOrIdentical,
        "promotion_verification_attestation",
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "verified_materialization_attestation".to_owned(),
        path: out.as_str().to_owned(),
    });
    result
}

fn load_plan_snapshot(root: &Path) -> Result<LoadedPackageAuditSnapshot, CommandResult> {
    load_package_audit_snapshot(
        root,
        COMMAND,
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    )
}

fn load_target_snapshot(root: &Path) -> Result<LoadedPackageAuditSnapshot, CommandResult> {
    load_package_audit_snapshot(
        root,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    )
}

fn positive_package_gates_pass(root: &Path, publication: bool) -> bool {
    let common = PackageCommonOptions {
        root: root.to_path_buf(),
        json: false,
    };
    let mut results = vec![
        run_package_check(common.clone()),
        run_package_check_hashes(common.clone()),
        run_package_build_certs(PackageBuildCertsOptions {
            common: common.clone(),
            check: true,
            build_check_cache: PackageBuildCheckCacheMode::Off,
            update_manifest_hashes: false,
            selection: PackageBuildSelection::Full,
        }),
        run_package_axiom_report(PackageAxiomReportOptions {
            common: common.clone(),
            check: true,
            timings: PackageTimingMode::Off,
        }),
        run_package_index(PackageIndexOptions {
            common: common.clone(),
            check: true,
            timings: PackageTimingMode::Off,
        }),
        run_package_verify_certs(verify_certs_full(common.clone(), PackageChecker::Reference)),
    ];
    if publication {
        results.push(run_package_export_summary(PackageExportSummaryOptions {
            common: common.clone(),
            out: None,
            check: true,
            timings: PackageTimingMode::Off,
        }));
        results.push(run_package_publish_plan(PackagePublishPlanOptions {
            common,
            check: true,
            timings: PackageTimingMode::Off,
        }));
    }
    results
        .iter()
        .all(|result| result.status == crate::diagnostic::CommandStatus::Passed)
}

type RebuiltTree = BTreeMap<PackagePath, Vec<u8>>;
type DeterministicRebuildResult =
    Result<(RebuiltTree, Vec<npa_package::PromotionReplayOmission>), &'static str>;

fn deterministic_rebuilds(
    source_root: &Path,
    baseline_root: &Path,
    baseline: &RebuiltTree,
    plan: &MathlibPromotionPlanV2,
) -> DeterministicRebuildResult {
    static NEXT_REBUILD: AtomicU64 = AtomicU64::new(0);

    let parent = baseline_root.parent().unwrap_or_else(|| Path::new("."));
    let (first, second) = loop {
        let sequence = NEXT_REBUILD.fetch_add(1, Ordering::Relaxed);
        let prefix = format!(
            ".npa-promotion-verify-{}-{}-{}-",
            std::process::id(),
            short_hash(plan.promotion_id),
            sequence
        );
        let first = parent.join(format!("{prefix}a"));
        let second = parent.join(format!("{prefix}b"));
        match write_tree_snapshot(baseline, &first) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(_) => return Err("promotion_materialization_nondeterministic"),
        }
        match write_tree_snapshot(baseline, &second) {
            Ok(()) => break (first, second),
            Err(error) => {
                // `first` was created by this invocation. Never remove the
                // colliding `second`, which may belong to another validator.
                let _ = fs::remove_dir_all(&first);
                if error.kind() == io::ErrorKind::AlreadyExists {
                    continue;
                }
                return Err("promotion_materialization_nondeterministic");
            }
        }
    };
    let cleanup = || {
        let _ = fs::remove_dir_all(&first);
        let _ = fs::remove_dir_all(&second);
    };
    let first_omissions =
        match build_declaration_materialization_candidate(source_root, &first, plan) {
            Ok(rows) => rows,
            Err(reason) => {
                cleanup();
                return Err(reason);
            }
        };
    let second_omissions =
        match build_declaration_materialization_candidate(source_root, &second, plan) {
            Ok(rows) => rows,
            Err(reason) => {
                cleanup();
                return Err(reason);
            }
        };
    let (first_tree, second_tree) = snapshot_rebuild_trees_and_cleanup(&first, &second)?;
    if first_tree != second_tree || first_omissions != second_omissions {
        return Err("promotion_materialization_nondeterministic");
    }
    Ok((first_tree, first_omissions))
}

fn snapshot_rebuild_trees_and_cleanup(
    first: &Path,
    second: &Path,
) -> Result<(RebuiltTree, RebuiltTree), &'static str> {
    let result = (|| {
        let first_tree =
            tree_snapshot(first).map_err(|_| "promotion_materialization_nondeterministic")?;
        let second_tree =
            tree_snapshot(second).map_err(|_| "promotion_materialization_nondeterministic")?;
        Ok((first_tree, second_tree))
    })();
    let _ = fs::remove_dir_all(first);
    let _ = fs::remove_dir_all(second);
    result
}

fn short_hash(hash: PackageHash) -> String {
    format_package_hash(&hash)[7..19].to_owned()
}

pub(crate) fn normalized_closure_identity(
    source_root: &Path,
    target_root: &Path,
    source: &LoadedPackageAuditSnapshot,
    baseline: &LoadedPackageAuditSnapshot,
    target: &LoadedPackageAuditSnapshot,
    plan: &MathlibPromotionPlanV2,
) -> Result<PackageHash, &'static str> {
    let source_modules = module_map(source);
    let target_modules = module_map(target);
    let source_verified = source_modules
        .get(&plan.selection.source_module)
        .ok_or("promotion_declaration_semantic_mismatch")?;
    let target_verified = target_modules
        .get(&plan.selection.target_module)
        .ok_or("promotion_declaration_semantic_mismatch")?;
    let (source_families, source_human) =
        actual_declaration_families(source_root, source, &plan.selection.source_module)?;
    let (target_families, _) =
        actual_declaration_families(target_root, target, &plan.selection.target_module)?;
    let source_roots = roots(
        source_verified,
        &plan
            .selection
            .roots
            .iter()
            .map(|root| root.requested_name.clone())
            .collect::<Vec<_>>(),
    )?;
    let target_roots = roots(
        target_verified,
        &plan
            .selection
            .roots
            .iter()
            .map(|root| root.requested_name.clone())
            .collect::<Vec<_>>(),
    )?;
    let mut source_external = BTreeMap::new();
    let mut target_external = BTreeMap::new();
    for mapping in &plan.dependency_mappings {
        let source_record = endpoint_record(source, &mapping.source)
            .ok_or("promotion_declaration_semantic_mismatch")?;
        let target_record = endpoint_record(target, &mapping.target)
            .or_else(|| endpoint_record(baseline, &mapping.target))
            .or_else(|| current_local_endpoint_record(target, &mapping.target))
            .ok_or("promotion_declaration_semantic_mismatch")?;
        let source_id = resolve_verified_declaration_export(
            &source_record.verified_module,
            &mapping.declaration_name,
        )
        .map_err(|_| "promotion_declaration_semantic_mismatch")?
        .identity;
        let target_id = resolve_verified_declaration_export(
            &target_record.verified_module,
            &mapping.declaration_name,
        )
        .map_err(|_| "promotion_declaration_semantic_mismatch")?
        .identity;
        if PackageHash::from(source_id.decl_interface_hash) != mapping.source_decl_interface_hash
            || PackageHash::from(target_id.decl_interface_hash)
                != mapping.target_decl_interface_hash
            || target_record.certificate.file_hash != mapping.target_certificate_file_hash
            || target_record.key.certificate_hash != mapping.target_certificate_hash
            || target_record.key.export_hash != mapping.target_export_hash
            || source_external
                .insert(source_id, target_id.clone())
                .is_some()
        {
            return Err("promotion_declaration_semantic_mismatch");
        }
        target_external.insert(target_id.clone(), target_id);
    }
    let source_closure = declaration_dependency_closure(
        &source_modules,
        &source_roots,
        &source_families,
        &source_external,
        DeclarationClosureLimits::default(),
    )
    .map_err(|_| "promotion_declaration_semantic_mismatch")?;
    if PackageHash::from(source_closure.declaration_closure_hash)
        != plan.selection.declaration_closure_hash
    {
        return Err("promotion_verification_attestation_stale");
    }
    let expected_declarations = plan_declarations(&source_closure, &source_human)
        .map_err(|_| "promotion_declaration_semantic_mismatch")?;
    let expected_generated = expected_declarations
        .iter()
        .flat_map(|row| row.generated_exports.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let planned_externalized = source_external
        .iter()
        .map(|(source, target)| (source.clone(), target.clone()))
        .collect::<BTreeSet<_>>();
    let actual_externalized = source_closure
        .externalized
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if expected_declarations != plan.selection.materialized_declarations
        || expected_generated != plan.selection.generated_exports
        || planned_externalized != actual_externalized
    {
        return Err("promotion_verification_attestation_stale");
    }
    let target_closure = declaration_dependency_closure(
        &target_modules,
        &target_roots,
        &target_families,
        &target_external,
        DeclarationClosureLimits::default(),
    )
    .map_err(|_| "promotion_declaration_semantic_mismatch")?;
    let mut global_mapping = source_external;
    for row in &plan.selection.materialized_declarations {
        let source_id = resolve_verified_declaration_export(source_verified, &row.source_name)
            .map_err(|_| "promotion_declaration_semantic_mismatch")?
            .identity;
        let target_id = resolve_verified_declaration_export(target_verified, &row.target_name)
            .map_err(|_| "promotion_declaration_semantic_mismatch")?
            .identity;
        global_mapping.insert(source_id, target_id);
    }
    for row in &plan.selection.generated_exports {
        let source_id = resolve_verified_declaration_export(source_verified, &row.name)
            .map_err(|_| "promotion_declaration_semantic_mismatch")?
            .identity;
        let target_id = resolve_verified_declaration_export(target_verified, &row.name)
            .map_err(|_| "promotion_declaration_semantic_mismatch")?
            .identity;
        global_mapping.insert(source_id, target_id);
    }
    let source_projection = normalized_declaration_closure_projection(
        &source_modules,
        &source_closure,
        &global_mapping,
    )
    .map_err(|_| "promotion_declaration_semantic_mismatch")?;
    let target_projection = normalized_declaration_closure_projection(
        &target_modules,
        &target_closure,
        &BTreeMap::new(),
    )
    .map_err(|_| "promotion_declaration_semantic_mismatch")?;
    if source_projection != target_projection {
        return Err("promotion_declaration_semantic_mismatch");
    }
    Ok(PackageHash::from(normalized_declaration_closure_hash(
        &source_projection,
    )))
}

fn current_local_endpoint_record<'a>(
    target: &'a LoadedPackageAuditSnapshot,
    endpoint: &npa_package::PromotionPlanEndpoint,
) -> Option<&'a npa_api::PackageArtifactVerifiedModule> {
    if endpoint.origin != npa_package::PackageArtifactOrigin::Local {
        return None;
    }
    let manifest = target.snapshot.validated.manifest();
    let lock = target
        .snapshot
        .package_lock_manifest
        .entries
        .iter()
        .find(|entry| entry.module == endpoint.module)?;
    (lock.origin == npa_package::PackageLockEntryOrigin::Local
        && endpoint.package == manifest.package
        && package_version_tuple(&endpoint.version) <= package_version_tuple(&manifest.version))
    .then(|| record_for(target, &endpoint.module))
    .flatten()
}

fn package_version_tuple(version: &npa_package::PackageVersion) -> (u64, u64, u64) {
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

fn module_map(snapshot: &LoadedPackageAuditSnapshot) -> BTreeMap<Name, VerifiedModule> {
    snapshot
        .snapshot
        .decoded_module_records
        .values()
        .map(|record| (record.key.module.clone(), record.verified_module.clone()))
        .collect()
}

fn actual_declaration_families(
    root: &Path,
    snapshot: &LoadedPackageAuditSnapshot,
    module: &Name,
) -> Result<(ValidatedSourceDeclarationFamilies, HumanMemberMap), &'static str> {
    let manifest_module = snapshot
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .find(|candidate| &candidate.module == module)
        .ok_or("promotion_declaration_semantic_mismatch")?;
    let mut extraction_source_bytes = 0;
    let source =
        read_declaration_source(root, &manifest_module.source, &mut extraction_source_bytes)
            .map_err(validation_source_extraction_reason)
            .and_then(|bytes| {
                String::from_utf8(bytes).map_err(|_| "promotion_declaration_semantic_mismatch")
            })?;
    let imports = direct_import_interfaces(
        root,
        snapshot,
        &manifest_module.imports,
        extraction_source_bytes,
    )
    .map_err(validation_source_extraction_reason)?;
    let human = collect_human_source_declaration_families(FileId(0), &source, &imports)
        .map_err(|_| "promotion_declaration_semantic_mismatch")?;
    let verified = record_for(snapshot, module)
        .map(|record| &record.verified_module)
        .ok_or("promotion_declaration_semantic_mismatch")?;
    reconcile_families(verified, &human).map_err(|_| "promotion_declaration_semantic_mismatch")
}

fn validation_source_extraction_reason(error: DeclarationSourceExtractionError) -> &'static str {
    match error {
        DeclarationSourceExtractionError::Unsupported => "promotion_declaration_semantic_mismatch",
        DeclarationSourceExtractionError::SourceBytesLimitExceeded { .. } => {
            "promotion_declaration_closure_limit_exceeded"
        }
    }
}

fn roots(
    verified: &VerifiedModule,
    names: &[Name],
) -> Result<BTreeSet<GlobalDeclarationIdentity>, &'static str> {
    names
        .iter()
        .map(|name| {
            resolve_verified_declaration_export(verified, name)
                .map(|row| row.identity)
                .map_err(|_| "promotion_declaration_semantic_mismatch")
        })
        .collect()
}

fn record_for<'a>(
    snapshot: &'a LoadedPackageAuditSnapshot,
    module: &Name,
) -> Option<&'a npa_api::PackageArtifactVerifiedModule> {
    snapshot
        .snapshot
        .decoded_module_records
        .values()
        .find(|record| &record.key.module == module)
}

fn read_confined(root: &Path, path: &PackagePath) -> Option<Vec<u8>> {
    let full = confined_governance_path(
        root,
        path,
        path.as_str(),
        "promotion_verification_attestation_stale",
    )
    .ok()?;
    fs::read(full).ok()
}

fn failure(root: &str, reason: &str, path: &str) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        root,
        vec![CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path)],
    )
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use std::os::unix::fs::symlink;

    use super::*;

    #[cfg(unix)]
    #[test]
    fn rebuild_snapshot_failure_cleans_both_scratch_trees() {
        static NEXT_TEST: AtomicU64 = AtomicU64::new(0);

        let root = std::env::temp_dir().join(format!(
            "npa-promotion-rebuild-cleanup-{}-{}",
            std::process::id(),
            NEXT_TEST.fetch_add(1, Ordering::Relaxed)
        ));
        let first = root.join("first");
        let second = root.join("second");
        fs::create_dir_all(&first).unwrap();
        fs::create_dir_all(&second).unwrap();
        symlink("missing", first.join("invalid-symlink")).unwrap();
        fs::write(second.join("state.txt"), b"second").unwrap();

        assert_eq!(
            snapshot_rebuild_trees_and_cleanup(&first, &second),
            Err("promotion_materialization_nondeterministic")
        );
        assert!(fs::symlink_metadata(&first)
            .is_err_and(|error| error.kind() == io::ErrorKind::NotFound));
        assert!(fs::symlink_metadata(&second)
            .is_err_and(|error| error.kind() == io::ErrorKind::NotFound));
        fs::remove_dir(root).unwrap();
    }
}
