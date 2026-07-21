use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use npa_cert::Name;
use npa_package::{
    format_package_hash, package_file_hash, parse_and_validate_manifest_str,
    parse_mathlib_promotion_plan_v2_json, parse_promotion_origin_registry_v2_json,
    parse_verified_materialization_attestation_json, validate_declaration_registry_entry_admission,
    DeclarationPromotionDependencyMapping, DeclarationPromotionRequest, DeclarationPromotionRoot,
    DeclarationPromotionRootKind, DeclarationPromotionSource, DeclarationPromotionTarget,
    PackageArtifactOrigin, PackageHash, PackageId, PackagePath, PackageVersion,
    PromotionOriginEntryV2, PromotionPlanEndpoint, PromotionReplayOmission,
    MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA, MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA,
    PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON,
};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempRoot(PathBuf);

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn copy_tree(source: &Path, target: &Path) {
    fs::create_dir(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&source_path, &target_path);
        } else {
            fs::copy(source_path, target_path).unwrap();
        }
    }
}

fn run(binary: &Path, arguments: &[&OsStr]) -> Output {
    Command::new(binary).args(arguments).output().unwrap()
}

fn assert_passed(output: Output) {
    assert!(
        output.status.success(),
        "command failed\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_failed_with_reason(output: Output, reason: &str) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "command unexpectedly passed\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains(reason) || stderr.contains(reason),
        "missing reason {reason}\nstdout: {stdout}\nstderr: {stderr}"
    );
    stdout.into_owned()
}

#[test]
fn declaration_promotion_materializes_attests_and_publishes_exact_closure() {
    let root = TempRoot(std::env::temp_dir().join(format!(
        "npa-declaration-promotion-flow-{}-{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    )));
    fs::create_dir(&root.0).unwrap();
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source = root.0.join("source");
    let baseline = root.0.join("baseline");
    let temporary = root.0.join("temporary");
    let tampered = root.0.join("tampered");
    let tracked = root.0.join("tracked");
    copy_tree(&repository.join("testdata/package/proofs"), &source);
    for target in [&baseline, &temporary, &tampered, &tracked] {
        copy_tree(
            &repository.join("testdata/package/npa-mathlib-declaration-baseline"),
            target,
        );
    }
    for package in [&source, &baseline, &temporary, &tampered, &tracked] {
        fs::remove_file(package.join("generated/theorem-premise-report.json")).unwrap();
    }
    let binary = Path::new(env!("CARGO_BIN_EXE_npa"));
    let source_arg = source.as_os_str();
    let baseline_arg = baseline.as_os_str();
    let temporary_arg = temporary.as_os_str();
    let tampered_arg = tampered.as_os_str();
    let tracked_arg = tracked.as_os_str();

    let unmaterialized_request = DeclarationPromotionRequest {
        schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
        source: DeclarationPromotionSource {
            package: PackageId::new("npa-proof-corpus"),
            version: PackageVersion::new("0.1.0"),
        },
        target: DeclarationPromotionTarget {
            package: PackageId::new("npa-mathlib"),
            baseline_version: PackageVersion::new("0.1.0"),
            planned_version: PackageVersion::new("0.1.1"),
        },
        source_module: Name::from_dotted("Proofs.Ai.Analysis.AbstractMetricTopology"),
        target_module: Name::from_dotted("Mathlib.Analysis.UnmaterializedDependency"),
        roots: vec![DeclarationPromotionRoot {
            source_name: Name::from_dotted("local_eq_symm"),
            target_name: Name::from_dotted("local_eq_symm"),
            kind: DeclarationPromotionRootKind::Theorem,
        }],
        dependency_mappings: Vec::new(),
        requested_maturity: "verified".to_owned(),
        proof_evidence: false,
    };
    fs::write(
        source.join("promotion/declaration-unmaterialized.selection.json"),
        unmaterialized_request.canonical_json().unwrap(),
    )
    .unwrap();
    let unmaterialized_output = assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("prepare-promotion"),
                OsStr::new("--root"),
                source_arg,
                OsStr::new("--target-baseline-root"),
                baseline_arg,
                OsStr::new("--declaration-request"),
                OsStr::new("promotion/declaration-unmaterialized.selection.json"),
                OsStr::new("--out"),
                OsStr::new("promotion/declaration-unmaterialized.plan.json"),
                OsStr::new("--json"),
            ],
        ),
        "promotion_declaration_dependency_unmaterialized",
    );
    assert!(unmaterialized_output.contains("\"module\":\"Proofs.Ai.EqReasoning\""));
    assert!(unmaterialized_output.contains("\"field\":\"eq_symm\""));
    assert!(unmaterialized_output.contains("\"actual_value\":\"sha256:"));

    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("prepare-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--declaration-request"),
            OsStr::new("promotion/declaration-local.selection.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-local.plan.json"),
            OsStr::new("--json"),
        ],
    ));
    let plan = parse_mathlib_promotion_plan_v2_json(
        &fs::read_to_string(source.join("promotion/declaration-local.plan.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(plan.selection.roots.len(), 2);
    assert_eq!(plan.selection.materialized_declarations.len(), 4);

    for sidecar in ["meta", "replay"] {
        let mut path_tampered_plan = plan.clone();
        let duplicate_path =
            PackagePath::new(format!("promotion/declaration-local.{sidecar}-copy.json"));
        let original_path = if sidecar == "meta" {
            &plan.selection.meta_path
        } else {
            &plan.selection.replay_path
        };
        fs::copy(
            source.join(original_path.as_str()),
            source.join(duplicate_path.as_str()),
        )
        .unwrap();
        if sidecar == "meta" {
            path_tampered_plan.selection.meta_path = duplicate_path;
        } else {
            path_tampered_plan.selection.replay_path = duplicate_path;
        }
        path_tampered_plan.finalize().unwrap();
        let plan_path = format!("promotion/declaration-local.{sidecar}-path.plan.json");
        fs::write(
            source.join(&plan_path),
            path_tampered_plan.canonical_json().unwrap(),
        )
        .unwrap();
        assert_failed_with_reason(
            run(
                binary,
                &[
                    OsStr::new("package"),
                    OsStr::new("materialize-promotion"),
                    OsStr::new("--root"),
                    source_arg,
                    OsStr::new("--target-baseline-root"),
                    baseline_arg,
                    OsStr::new("--target-root"),
                    baseline_arg,
                    OsStr::new("--plan"),
                    OsStr::new(&plan_path),
                    OsStr::new("--phase"),
                    OsStr::new("temporary"),
                    OsStr::new("--json"),
                ],
            ),
            "promotion_materialize_plan_stale",
        );
    }

    let smuggled_request = DeclarationPromotionRequest {
        schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
        source: DeclarationPromotionSource {
            package: PackageId::new("npa-proof-corpus"),
            version: PackageVersion::new("0.1.0"),
        },
        target: DeclarationPromotionTarget {
            package: PackageId::new("npa-mathlib"),
            baseline_version: PackageVersion::new("0.1.0"),
            planned_version: PackageVersion::new("0.1.1"),
        },
        source_module: Name::from_dotted("Proofs.Ai.Analysis.AbstractMetricTopology"),
        target_module: Name::from_dotted("Mathlib.Analysis.Smuggled"),
        roots: vec![DeclarationPromotionRoot {
            source_name: Name::from_dotted("MetricBall"),
            target_name: Name::from_dotted("MetricBall"),
            kind: DeclarationPromotionRootKind::Definition,
        }],
        dependency_mappings: Vec::new(),
        requested_maturity: "verified".to_owned(),
        proof_evidence: false,
    };
    fs::write(
        source.join("promotion/declaration-smuggled.selection.json"),
        smuggled_request.canonical_json().unwrap(),
    )
    .unwrap();
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("prepare-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--declaration-request"),
            OsStr::new("promotion/declaration-smuggled.selection.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-smuggled.plan.json"),
            OsStr::new("--json"),
        ],
    ));
    let smuggled_plan = parse_mathlib_promotion_plan_v2_json(
        &fs::read_to_string(source.join("promotion/declaration-smuggled.plan.json")).unwrap(),
    )
    .unwrap();
    let mut tampered_plan = plan.clone();
    tampered_plan.selection.materialized_declarations.extend(
        smuggled_plan
            .selection
            .materialized_declarations
            .into_iter()
            .map(|mut declaration| {
                declaration.role = "support".to_owned();
                declaration
            }),
    );
    tampered_plan.selection.materialized_declarations.sort();
    tampered_plan.selection.generated_exports = tampered_plan
        .selection
        .materialized_declarations
        .iter()
        .flat_map(|declaration| declaration.generated_exports.iter().cloned())
        .collect();
    tampered_plan.selection.generated_exports.sort();
    tampered_plan.selection.generated_exports.dedup();
    tampered_plan.finalize().unwrap();
    fs::write(
        source.join("promotion/declaration-local.tampered.plan.json"),
        tampered_plan.canonical_json().unwrap(),
    )
    .unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("materialize-promotion"),
                OsStr::new("--root"),
                source_arg,
                OsStr::new("--target-baseline-root"),
                baseline_arg,
                OsStr::new("--target-root"),
                tampered_arg,
                OsStr::new("--plan"),
                OsStr::new("promotion/declaration-local.tampered.plan.json"),
                OsStr::new("--phase"),
                OsStr::new("temporary"),
                OsStr::new("--apply"),
                OsStr::new("--json"),
            ],
        ),
        "promotion_materialize_plan_stale",
    );
    assert!(!tampered.join("Mathlib/Analysis/Local/source.npa").exists());
    let rejected_smuggled_plan = run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-materialization"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--target-root"),
            tampered_arg,
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local.tampered.plan.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-local.tampered.attestation.json"),
            OsStr::new("--json"),
        ],
    );
    assert!(!rejected_smuggled_plan.status.success());
    assert!(!source
        .join("promotion/declaration-local.tampered.attestation.json")
        .exists());

    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("materialize-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--target-root"),
            temporary_arg,
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local.plan.json"),
            OsStr::new("--phase"),
            OsStr::new("temporary"),
            OsStr::new("--apply"),
            OsStr::new("--json"),
        ],
    ));
    let promoted_source =
        fs::read_to_string(temporary.join("Mathlib/Analysis/Local/source.npa")).unwrap();
    for retained in [
        "LocalMem",
        "LocalPred",
        "local_mem_elim",
        "local_pred_apply",
    ] {
        assert!(promoted_source.contains(retained));
    }
    for excluded in [
        "MetricBall",
        "Neighborhood",
        "local_eq_refl",
        "metric_ball_intro",
    ] {
        assert!(!promoted_source.contains(excluded));
    }
    assert_eq!(
        fs::read(temporary.join("promotion-origins.json")).unwrap(),
        fs::read(baseline.join("promotion-origins.json")).unwrap()
    );

    let collision_baseline = root.0.join("collision-baseline");
    let collision_target = root.0.join("collision-target");
    copy_tree(&baseline, &collision_baseline);
    let target_base = plan.selection.target_module.as_dotted().replace('.', "/");
    for filename in [
        "source.npa",
        "certificate.npcert",
        "meta.json",
        "replay.json",
    ] {
        let relative = format!("{target_base}/{filename}");
        let destination = collision_baseline.join(&relative);
        fs::create_dir_all(destination.parent().unwrap()).unwrap();
        fs::copy(temporary.join(&relative), destination).unwrap();
    }
    copy_tree(&collision_baseline, &collision_target);
    let collision_attestation = "promotion/declaration-local.collision-attestation.json";
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("validate-promotion-materialization"),
                OsStr::new("--root"),
                source_arg,
                OsStr::new("--target-baseline-root"),
                collision_baseline.as_os_str(),
                OsStr::new("--target-root"),
                temporary_arg,
                OsStr::new("--plan"),
                OsStr::new("promotion/declaration-local.plan.json"),
                OsStr::new("--out"),
                OsStr::new(collision_attestation),
                OsStr::new("--json"),
            ],
        ),
        "promotion_declaration_target_collision",
    );
    assert!(!source.join(collision_attestation).exists());
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("materialize-promotion"),
                OsStr::new("--root"),
                source_arg,
                OsStr::new("--target-baseline-root"),
                collision_baseline.as_os_str(),
                OsStr::new("--target-root"),
                collision_target.as_os_str(),
                OsStr::new("--plan"),
                OsStr::new("promotion/declaration-local.plan.json"),
                OsStr::new("--phase"),
                OsStr::new("temporary"),
                OsStr::new("--apply"),
                OsStr::new("--json"),
            ],
        ),
        "promotion_declaration_target_collision",
    );

    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-materialization"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--target-root"),
            temporary_arg,
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local.plan.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-local.verified-materialization.json"),
            OsStr::new("--json"),
        ],
    ));
    let target_source_path = temporary.join("Mathlib/Analysis/Local/source.npa");
    let original_target_source = fs::read(&target_source_path).unwrap();
    let mut corrupt_target_source = original_target_source.clone();
    corrupt_target_source.extend_from_slice(b"\n-- corruption\n");
    fs::write(&target_source_path, corrupt_target_source).unwrap();
    let corrupt = run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-materialization"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--target-root"),
            temporary_arg,
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local.plan.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-local.verified-materialization.json"),
            OsStr::new("--check"),
            OsStr::new("--json"),
        ],
    );
    assert!(!corrupt.status.success());
    fs::write(target_source_path, original_target_source).unwrap();

    let missing_attestation = run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("materialize-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--target-root"),
            tracked_arg,
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local.plan.json"),
            OsStr::new("--phase"),
            OsStr::new("tracked"),
            OsStr::new("--apply"),
        ],
    );
    assert!(!missing_attestation.status.success());

    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("materialize-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            baseline_arg,
            OsStr::new("--target-root"),
            tracked_arg,
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local.plan.json"),
            OsStr::new("--verification-attestation"),
            OsStr::new("promotion/declaration-local.verified-materialization.json"),
            OsStr::new("--phase"),
            OsStr::new("tracked"),
            OsStr::new("--apply"),
            OsStr::new("--json"),
        ],
    ));
    let registry = parse_promotion_origin_registry_v2_json(
        &fs::read_to_string(tracked.join("promotion-origins.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(registry.schema, MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA);
    assert_eq!(registry.generation, 2);
    let [PromotionOriginEntryV2::DeclarationClosureV1(entry)] = registry.entries.as_slice() else {
        panic!("expected one declaration-closure registry entry")
    };
    assert!(entry.maturity_events.is_empty());
    assert_eq!(entry.closure.len(), 4);
    let attestation = parse_verified_materialization_attestation_json(
        &fs::read_to_string(
            source.join("promotion/declaration-local.verified-materialization.json"),
        )
        .unwrap(),
    )
    .unwrap();
    assert!(attestation
        .gate_results
        .iter()
        .all(|gate| gate.gate != "theorem-premise-report-check"));
    validate_declaration_registry_entry_admission(entry, &plan, &attestation).unwrap();

    let mut unplanned_equivalent = (**entry).clone();
    let mut forged_origin = unplanned_equivalent.canonical_source.clone();
    forged_origin.package = PackageId::new("unplanned-equivalent-source");
    unplanned_equivalent.equivalent_sources.push(forged_origin);
    unplanned_equivalent.equivalent_sources.sort();
    assert!(validate_declaration_registry_entry_admission(
        &unplanned_equivalent,
        &plan,
        &attestation,
    )
    .is_err());

    let registry_without_premise_report = root.0.join("registry-without-premise-report");
    copy_tree(&tracked, &registry_without_premise_report);
    fs::remove_file(registry_without_premise_report.join("generated/theorem-premise-report.json"))
        .unwrap();
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-origin-registry"),
            OsStr::new("--root"),
            registry_without_premise_report.as_os_str(),
            OsStr::new("--json"),
        ],
    ));

    let mut wrong_plan_file_hash = attestation.clone();
    wrong_plan_file_hash.plan.file_hash = PackageHash::new([97; 32]);
    wrong_plan_file_hash.finalize().unwrap();
    let mut matching_wrong_evidence = (**entry).clone();
    matching_wrong_evidence.evidence.plan_file_hash = wrong_plan_file_hash.plan.file_hash;
    assert!(validate_declaration_registry_entry_admission(
        &matching_wrong_evidence,
        &plan,
        &wrong_plan_file_hash,
    )
    .is_err());

    let mut wrong_attestation_file_hash = (**entry).clone();
    wrong_attestation_file_hash.evidence.attestation_file_hash = PackageHash::new([98; 32]);
    assert!(validate_declaration_registry_entry_admission(
        &wrong_attestation_file_hash,
        &plan,
        &attestation,
    )
    .is_err());

    let mut wrong_omission_source = attestation.clone();
    wrong_omission_source.replay_omissions.clear();
    wrong_omission_source
        .replay_omissions
        .push(PromotionReplayOmission {
            source_replay_file_hash: PackageHash::new([94; 32]),
            declaration: plan.selection.materialized_declarations[0]
                .source_name
                .clone(),
            row_index: u64::MAX,
            reason: PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON.to_owned(),
        });
    wrong_omission_source.finalize().unwrap();
    let wrong_omission_source_json = wrong_omission_source.canonical_json().unwrap();
    let mut matching_wrong_omission_evidence = (**entry).clone();
    matching_wrong_omission_evidence
        .evidence
        .attestation_file_hash = package_file_hash(wrong_omission_source_json.as_bytes());
    assert!(validate_declaration_registry_entry_admission(
        &matching_wrong_omission_evidence,
        &plan,
        &wrong_omission_source,
    )
    .is_err());

    for sidecar in ["source", "meta", "replay", "certificate"] {
        let mut wrong_target_path = attestation.clone();
        let path = PackagePath::new(format!("Mathlib/Wrong/{sidecar}"));
        match sidecar {
            "source" => wrong_target_path.target.source_path = path,
            "meta" => wrong_target_path.target.meta_path = path,
            "replay" => wrong_target_path.target.replay_path = path,
            "certificate" => wrong_target_path.target.certificate_path = path,
            _ => unreachable!(),
        }
        wrong_target_path.finalize().unwrap();
        assert!(
            validate_declaration_registry_entry_admission(entry, &plan, &wrong_target_path)
                .is_err()
        );
    }

    let registry_tampered = root.0.join("registry-tampered");
    copy_tree(&tracked, &registry_tampered);
    let mut mismatched_admission = registry.clone();
    let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut mismatched_admission.entries[0]
    else {
        panic!("expected declaration route")
    };
    entry.closure[0].decl_certificate_hash = PackageHash::new([99; 32]);
    mismatched_admission.refresh_hash().unwrap();
    fs::write(
        registry_tampered.join("promotion-origins.json"),
        mismatched_admission.canonical_json().unwrap(),
    )
    .unwrap();
    let mismatched_admission_result = run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-origin-registry"),
            OsStr::new("--root"),
            registry_tampered.as_os_str(),
            OsStr::new("--source-root"),
            source_arg,
            OsStr::new("--json"),
        ],
    );
    assert!(!mismatched_admission_result.status.success());

    let duplicate_identity_source = root.0.join("duplicate-identity-source");
    copy_tree(&source, &duplicate_identity_source);
    fs::write(
        duplicate_identity_source.join(plan.selection.source_path.as_str()),
        b"tampered duplicate source\n",
    )
    .unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("validate-promotion-origin-registry"),
                OsStr::new("--root"),
                tracked_arg,
                OsStr::new("--source-root"),
                duplicate_identity_source.as_os_str(),
                OsStr::new("--source-root"),
                source_arg,
                OsStr::new("--json"),
            ],
        ),
        "promotion_registry_source_identity_mismatch",
    );

    // Plan, attestation, and registry hashes are governance integrity, not
    // proof authority. Synchronized edits must still be rejected when their
    // declaration identities disagree with the verified source certificate.
    let forged_source = root.0.join("forged-source");
    let forged_target = root.0.join("forged-target");
    copy_tree(&source, &forged_source);
    copy_tree(&tracked, &forged_target);
    let mut forged_plan = plan.clone();
    forged_plan.selection.materialized_declarations[0].decl_certificate_hash =
        PackageHash::new([96; 32]);
    forged_plan.finalize().unwrap();
    let forged_plan_source = forged_plan.canonical_json().unwrap();
    fs::write(
        forged_source.join("promotion/declaration-local.plan.json"),
        &forged_plan_source,
    )
    .unwrap();
    let mut forged_attestation = attestation.clone();
    forged_attestation.plan.file_hash = package_file_hash(forged_plan_source.as_bytes());
    forged_attestation.plan.identity_hash = forged_plan.plan_hash;
    forged_attestation.materialized_declarations =
        forged_plan.selection.materialized_declarations.clone();
    forged_attestation.finalize().unwrap();
    let forged_attestation_source = forged_attestation.canonical_json().unwrap();
    fs::write(
        forged_source.join("promotion/declaration-local.verified-materialization.json"),
        &forged_attestation_source,
    )
    .unwrap();
    let mut forged_registry = registry.clone();
    let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut forged_registry.entries[0]
    else {
        panic!("expected declaration route")
    };
    entry.closure = forged_plan.selection.materialized_declarations.clone();
    entry.evidence.plan_file_hash = package_file_hash(forged_plan_source.as_bytes());
    entry.evidence.attestation_file_hash = package_file_hash(forged_attestation_source.as_bytes());
    forged_registry.refresh_hash().unwrap();
    fs::write(
        forged_target.join("promotion-origins.json"),
        forged_registry.canonical_json().unwrap(),
    )
    .unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("validate-promotion-origin-registry"),
                OsStr::new("--root"),
                forged_target.as_os_str(),
                OsStr::new("--source-root"),
                forged_source.as_os_str(),
                OsStr::new("--json"),
            ],
        ),
        "promotion_registry_source_identity_mismatch",
    );

    // Even a schema-valid omission with the exact source replay hash must be
    // rederived from the source replay rather than accepted from synchronized
    // governance hashes.
    let forged_omission_source = root.0.join("forged-omission-source");
    let forged_omission_target = root.0.join("forged-omission-target");
    copy_tree(&source, &forged_omission_source);
    copy_tree(&tracked, &forged_omission_target);
    let mut forged_omission_attestation = attestation.clone();
    forged_omission_attestation.replay_omissions.clear();
    forged_omission_attestation
        .replay_omissions
        .push(PromotionReplayOmission {
            source_replay_file_hash: plan.selection.replay_file_hash,
            declaration: plan.selection.materialized_declarations[0]
                .source_name
                .clone(),
            row_index: u64::MAX,
            reason: PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON.to_owned(),
        });
    forged_omission_attestation.finalize().unwrap();
    let forged_omission_attestation_source = forged_omission_attestation.canonical_json().unwrap();
    fs::write(
        forged_omission_source.join("promotion/declaration-local.verified-materialization.json"),
        &forged_omission_attestation_source,
    )
    .unwrap();
    let mut forged_omission_registry = registry.clone();
    let PromotionOriginEntryV2::DeclarationClosureV1(entry) =
        &mut forged_omission_registry.entries[0]
    else {
        panic!("expected declaration route")
    };
    entry.evidence.attestation_file_hash =
        package_file_hash(forged_omission_attestation_source.as_bytes());
    forged_omission_registry.refresh_hash().unwrap();
    fs::write(
        forged_omission_target.join("promotion-origins.json"),
        forged_omission_registry.canonical_json().unwrap(),
    )
    .unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("validate-promotion-origin-registry"),
                OsStr::new("--root"),
                forged_omission_target.as_os_str(),
                OsStr::new("--source-root"),
                forged_omission_source.as_os_str(),
                OsStr::new("--json"),
            ],
        ),
        "promotion_registry_source_identity_mismatch",
    );

    let forged_semantics_source = root.0.join("forged-semantics-source");
    let forged_semantics_target = root.0.join("forged-semantics-target");
    copy_tree(&source, &forged_semantics_source);
    copy_tree(&tracked, &forged_semantics_target);
    let forged_normalized_hash = PackageHash::new([95; 32]);
    let mut forged_semantics_attestation = attestation.clone();
    forged_semantics_attestation.normalized_closure_hash = forged_normalized_hash;
    forged_semantics_attestation
        .gate_results
        .iter_mut()
        .find(|gate| gate.side == "target" && gate.gate == "normalized-closure-equality")
        .unwrap()
        .identity_hash = forged_normalized_hash;
    forged_semantics_attestation.finalize().unwrap();
    let forged_semantics_attestation_source =
        forged_semantics_attestation.canonical_json().unwrap();
    fs::write(
        forged_semantics_source.join("promotion/declaration-local.verified-materialization.json"),
        &forged_semantics_attestation_source,
    )
    .unwrap();
    let mut forged_semantics_registry = registry.clone();
    let PromotionOriginEntryV2::DeclarationClosureV1(entry) =
        &mut forged_semantics_registry.entries[0]
    else {
        panic!("expected declaration route")
    };
    entry.evidence.normalized_closure_hash = forged_normalized_hash;
    entry.evidence.attestation_file_hash =
        package_file_hash(forged_semantics_attestation_source.as_bytes());
    forged_semantics_registry.refresh_hash().unwrap();
    fs::write(
        forged_semantics_target.join("promotion-origins.json"),
        forged_semantics_registry.canonical_json().unwrap(),
    )
    .unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("validate-promotion-origin-registry"),
                OsStr::new("--root"),
                forged_semantics_target.as_os_str(),
                OsStr::new("--source-root"),
                forged_semantics_source.as_os_str(),
                OsStr::new("--json"),
            ],
        ),
        "promotion_registry_source_identity_mismatch",
    );

    let mut future_revision = registry.clone();
    let PromotionOriginEntryV2::DeclarationClosureV1(entry) = &mut future_revision.entries[0]
    else {
        panic!("expected declaration route")
    };
    entry.introduced_version = PackageVersion::new("9.0.0");
    entry.target_revisions[0].target_version = PackageVersion::new("9.0.0");
    future_revision.refresh_hash().unwrap();
    fs::write(
        registry_tampered.join("promotion-origins.json"),
        future_revision.canonical_json().unwrap(),
    )
    .unwrap();
    let future_revision_result = run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-origin-registry"),
            OsStr::new("--root"),
            registry_tampered.as_os_str(),
            OsStr::new("--json"),
        ],
    );
    assert!(!future_revision_result.status.success());

    // A later request from the same large source module may promote a disjoint
    // root when it explicitly externalizes already-public support.
    let later_request = DeclarationPromotionRequest {
        schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
        source: DeclarationPromotionSource {
            package: PackageId::new("npa-proof-corpus"),
            version: PackageVersion::new("0.1.0"),
        },
        target: DeclarationPromotionTarget {
            package: PackageId::new("npa-mathlib"),
            baseline_version: PackageVersion::new("0.1.1"),
            planned_version: PackageVersion::new("0.1.2"),
        },
        source_module: Name::from_dotted("Proofs.Ai.Analysis.AbstractMetricTopology"),
        target_module: Name::from_dotted("Mathlib.Analysis.LocalIntroduction"),
        roots: vec![DeclarationPromotionRoot {
            source_name: Name::from_dotted("local_mem_intro"),
            target_name: Name::from_dotted("local_mem_intro"),
            kind: DeclarationPromotionRootKind::Theorem,
        }],
        dependency_mappings: vec![DeclarationPromotionDependencyMapping {
            source: PromotionPlanEndpoint {
                origin: PackageArtifactOrigin::Local,
                package: PackageId::new("npa-proof-corpus"),
                version: PackageVersion::new("0.1.0"),
                module: Name::from_dotted("Proofs.Ai.Analysis.AbstractMetricTopology"),
            },
            target: PromotionPlanEndpoint {
                origin: PackageArtifactOrigin::Local,
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.1.1"),
                module: Name::from_dotted("Mathlib.Analysis.Local"),
            },
            declaration_mapping: "same-name".to_owned(),
        }],
        requested_maturity: "verified".to_owned(),
        proof_evidence: false,
    };
    fs::write(
        source.join("promotion/declaration-local-introduction.selection.json"),
        later_request.canonical_json().unwrap(),
    )
    .unwrap();
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("prepare-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            tracked_arg,
            OsStr::new("--declaration-request"),
            OsStr::new("promotion/declaration-local-introduction.selection.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-local-introduction.plan.json"),
            OsStr::new("--json"),
        ],
    ));
    let later_plan = parse_mathlib_promotion_plan_v2_json(
        &fs::read_to_string(source.join("promotion/declaration-local-introduction.plan.json"))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(later_plan.selection.materialized_declarations.len(), 1);
    assert_eq!(later_plan.dependency_mappings.len(), 1);

    // A self-consistent hand-authored plan cannot bypass active registry
    // ownership by rebinding itself to an otherwise unchanged baseline.
    let unowned_baseline = root.0.join("unowned-baseline");
    copy_tree(&tracked, &unowned_baseline);
    let mut unowned_registry = parse_promotion_origin_registry_v2_json(
        &fs::read_to_string(unowned_baseline.join("promotion-origins.json")).unwrap(),
    )
    .unwrap();
    unowned_registry.entries.clear();
    unowned_registry.refresh_hash().unwrap();
    let unowned_registry_source = unowned_registry.canonical_json().unwrap();
    fs::write(
        unowned_baseline.join("promotion-origins.json"),
        &unowned_registry_source,
    )
    .unwrap();
    let mut unowned_plan = later_plan.clone();
    unowned_plan.target_baseline.registry_file_hash =
        package_file_hash(unowned_registry_source.as_bytes());
    unowned_plan.finalize().unwrap();
    fs::write(
        source.join("promotion/declaration-local-introduction.unowned.plan.json"),
        unowned_plan.canonical_json().unwrap(),
    )
    .unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("materialize-promotion"),
                OsStr::new("--root"),
                source_arg,
                OsStr::new("--target-baseline-root"),
                unowned_baseline.as_os_str(),
                OsStr::new("--target-root"),
                unowned_baseline.as_os_str(),
                OsStr::new("--plan"),
                OsStr::new("promotion/declaration-local-introduction.unowned.plan.json"),
                OsStr::new("--phase"),
                OsStr::new("temporary"),
                OsStr::new("--json"),
            ],
        ),
        "promotion_materialize_plan_stale",
    );

    let later_temporary = root.0.join("later-temporary");
    let later_tracked = root.0.join("later-tracked");
    copy_tree(&tracked, &later_temporary);
    copy_tree(&tracked, &later_tracked);
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("materialize-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            tracked_arg,
            OsStr::new("--target-root"),
            later_temporary.as_os_str(),
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local-introduction.plan.json"),
            OsStr::new("--phase"),
            OsStr::new("temporary"),
            OsStr::new("--apply"),
            OsStr::new("--json"),
        ],
    ));
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-materialization"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            tracked_arg,
            OsStr::new("--target-root"),
            later_temporary.as_os_str(),
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local-introduction.plan.json"),
            OsStr::new("--out"),
            OsStr::new("promotion/declaration-local-introduction.verified-materialization.json"),
            OsStr::new("--json"),
        ],
    ));
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("materialize-promotion"),
            OsStr::new("--root"),
            source_arg,
            OsStr::new("--target-baseline-root"),
            tracked_arg,
            OsStr::new("--target-root"),
            later_tracked.as_os_str(),
            OsStr::new("--plan"),
            OsStr::new("promotion/declaration-local-introduction.plan.json"),
            OsStr::new("--verification-attestation"),
            OsStr::new("promotion/declaration-local-introduction.verified-materialization.json"),
            OsStr::new("--phase"),
            OsStr::new("tracked"),
            OsStr::new("--apply"),
            OsStr::new("--json"),
        ],
    ));
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-origin-registry"),
            OsStr::new("--root"),
            later_tracked.as_os_str(),
            OsStr::new("--source-root"),
            source_arg,
            OsStr::new("--json"),
        ],
    ));

    // Consume only the newly promoted certificate from a fresh package. This
    // is the source-free downstream smoke for declaration-level publication.
    let downstream = root.0.join("downstream");
    fs::create_dir_all(downstream.join("Downstream/Local")).unwrap();
    fs::create_dir_all(downstream.join("vendor/npa-mathlib/Mathlib/Analysis/Local")).unwrap();
    let tracked_manifest_source = fs::read_to_string(tracked.join("npa-package.toml")).unwrap();
    assert!(tracked_manifest_source.contains("\n[[modules]]\n"));
    let tracked_manifest = parse_and_validate_manifest_str(&tracked_manifest_source)
        .unwrap()
        .into_manifest();
    let promoted = tracked_manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == "Mathlib.Analysis.Local")
        .unwrap();
    fs::copy(
        tracked.join(promoted.certificate.as_str()),
        downstream.join("vendor/npa-mathlib/Mathlib/Analysis/Local/certificate.npcert"),
    )
    .unwrap();
    fs::write(
        downstream.join("Downstream/Local/source.npa"),
        "import Mathlib.Analysis.Local\n\ntheorem local_mem_passthrough.{u} :\n  forall (X : Sort u), forall (domain : forall (x : X), Prop), forall (x : X), forall (h : @LocalMem.{u} X domain x), domain x :=\n  fun X => fun domain => fun x => fun h => @local_mem_elim.{u} X domain x h\n",
    )
    .unwrap();
    let zero = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
    let downstream_manifest = format!(
        "schema = \"npa.package.v0.1\"\npackage = \"npa-declaration-downstream\"\nversion = \"0.1.0\"\nlicense = \"Apache-2.0\"\n\ncore_spec = \"npa.core.v0.1\"\nkernel_profile = \"npa.kernel.v0.1\"\ncertificate_format = \"npa.certificate.canonical.v0.1\"\nchecker_profile = \"npa.checker.reference.v0.1\"\n\n[policy]\nallow_custom_axioms = false\nallowed_axioms = []\n\n[[imports]]\nmodule = \"Mathlib.Analysis.Local\"\npackage = \"npa-mathlib\"\nversion = \"0.1.1\"\ncertificate = \"vendor/npa-mathlib/Mathlib/Analysis/Local/certificate.npcert\"\nexport_hash = \"{}\"\ncertificate_hash = \"{}\"\n\n[[modules]]\nmodule = \"Downstream.Local\"\nsource = \"Downstream/Local/source.npa\"\ncertificate = \"Downstream/Local/certificate.npcert\"\nproducer_profile = \"human-surface-explicit-term\"\nexpected_source_hash = \"{zero}\"\nexpected_certificate_file_hash = \"{zero}\"\nexpected_export_hash = \"{zero}\"\nexpected_axiom_report_hash = \"{zero}\"\nexpected_certificate_hash = \"{zero}\"\nimports = [\"Mathlib.Analysis.Local\"]\ndefinitions = []\ntheorems = [\"local_mem_passthrough\"]\naxioms = []\n",
        format_package_hash(&promoted.expected_export_hash),
        format_package_hash(&promoted.expected_certificate_hash),
    );
    fs::write(downstream.join("npa-package.toml"), downstream_manifest).unwrap();
    let downstream_arg = downstream.as_os_str();
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("build-certs"),
            OsStr::new("--root"),
            downstream_arg,
            OsStr::new("--build-check-cache"),
            OsStr::new("off"),
            OsStr::new("--update-manifest-hashes"),
            OsStr::new("--json"),
        ],
    ));
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("verify-certs"),
            OsStr::new("--root"),
            downstream_arg,
            OsStr::new("--checker"),
            OsStr::new("reference"),
            OsStr::new("--package-lock"),
            OsStr::new("checked"),
            OsStr::new("--audit-cache"),
            OsStr::new("off"),
            OsStr::new("--verifier-memo"),
            OsStr::new("off"),
            OsStr::new("--json"),
        ],
    ));
}
