use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

use npa_cli::{
    args::{
        PackageAxiomReportOptions, PackageCommand, PackageCommonOptions, PackageIndexOptions,
        PackageL2AcceptanceAggregateOptions, PackageL2NamespaceTransportOptions,
        PackageL2ReviewInputOptions, PackageLockCommand, PackageMaterializePromotionOptions,
        PackagePreparePromotionOptions, PackagePromotionPhase, PackageTimingMode,
        PackageValidatePromotionOriginRegistryOptions,
    },
    diagnostic::CommandStatus,
    package::run_package_command,
};
use npa_package::{
    format_package_hash, package_file_hash, parse_and_validate_manifest_str,
    parse_l2_acceptance_policy_json, parse_l2_namespace_transport_attestation_json,
    parse_l2_review_input_json, parse_package_proof_replay, parse_package_theorem_index_json,
    parse_promotion_origin_registry_json, promotion_legacy_target_reservation_id,
    promotion_transaction_path_hash, L2NamespaceTransportRequest, L2ReviewCheckDecision,
    L2ReviewCheckResult, L2ReviewReport, L2TransportEndpoint, L2TransportModuleMapping,
    L2TransportModuleRole, L2TransportPackageIdentity, PackageArtifactOrigin, PackageHash,
    PackagePath, PromotionAuditLocation, PromotionEvidence, PromotionLegacyTargetReservation,
    PromotionLifecycle, PromotionOldFile, PromotionOriginRegistry, PromotionReplacementState,
    PromotionReservedTheorem, PromotionTargetRevision, PromotionTransactionJournal,
    PromotionTransactionPhase, PromotionTransactionRow, PromotionTransactionState,
    MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA, MATHLIB_PROMOTION_REGISTRY_ID,
    MATHLIB_PROMOTION_TRANSACTION_SCHEMA,
};

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct Fixture {
    root: PathBuf,
    source: PathBuf,
    equivalent_source: PathBuf,
    baseline: PathBuf,
    target: PathBuf,
    tracked: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let root = std::env::temp_dir().join(format!(
            "npa-cli-l2-promotion-flow-{}-{index}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let source = root.join("source");
        let equivalent_source = root.join("equivalent-source");
        let baseline = root.join("baseline");
        let target = root.join("target");
        let tracked = root.join("tracked");
        copy_directory(
            &repo_root().join("testdata/package/npa-mathlib-seed"),
            &source,
        );
        install_external_existing_dependency(&source);
        copy_directory(&source, &equivalent_source);
        replace_manifest_package(&equivalent_source, "npa-mathlib-seed", "npa-project-alias");
        regenerate_generated_artifacts(&equivalent_source);
        copy_directory(&repo_root().join("testdata/package/npa-mathlib"), &baseline);
        for (module, path) in [
            ("Mathlib.Core.Reduction", "Mathlib/Core/Reduction"),
            ("Mathlib.Logic.Prop", "Mathlib/Logic/Prop"),
        ] {
            remove_manifest_module(&baseline, module);
            fs::remove_dir_all(baseline.join(path)).unwrap();
        }
        regenerate_generated_artifacts(&baseline);
        install_promotion_governance(&baseline);
        copy_directory(&baseline, &target);
        copy_directory(&baseline, &tracked);
        Self {
            root,
            source,
            equivalent_source,
            baseline,
            target,
            tracked,
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn promotion_prepare_materialize_transport_and_registry_end_to_end() {
    let fixture = Fixture::new();
    let policy_path = fixture.baseline.join("policy/l2-acceptance-policy.json");
    let transport_policy_path = fixture
        .baseline
        .join("policy/l2-namespace-transport-policy.json");
    let policy_bytes = fs::read(&policy_path).unwrap();
    let policy =
        parse_l2_acceptance_policy_json(std::str::from_utf8(&policy_bytes).unwrap()).unwrap();
    let theorem_index = parse_package_theorem_index_json(
        &fs::read_to_string(fixture.source.join("generated/theorem-index.json")).unwrap(),
    )
    .unwrap();
    let selected_modules = [
        ("Proofs.Ai.Prop", "Mathlib.Logic.Prop"),
        ("Proofs.Ai.Reduction", "Mathlib.Core.Reduction"),
    ];
    let theorems = theorem_index
        .entries
        .iter()
        .filter(|entry| {
            selected_modules
                .iter()
                .any(|(source, _)| entry.global_ref.module.as_dotted() == *source)
                && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
                && entry.artifact.origin == PackageArtifactOrigin::Local
        })
        .map(|entry| {
            (
                entry.global_ref.module.as_dotted(),
                entry.global_ref.name.as_dotted(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(theorems.len(), 11);

    let mut review_inputs = Vec::new();
    let mut reviews = Vec::new();
    for (theorem_index, (module, theorem)) in theorems.iter().enumerate() {
        let module_leaf = module.rsplit('.').next().unwrap();
        let input_path = PathBuf::from(format!("l2-reviews/{module_leaf}/{theorem}.input.json"));
        let prepared = run_package_command(PackageCommand::PrepareL2ReviewInput(
            PackageL2ReviewInputOptions {
                common: common(&fixture.source),
                policy: policy_path.clone(),
                module: module.clone(),
                declaration: theorem.clone(),
                out: input_path.clone(),
                check: false,
            },
        ));
        assert_eq!(prepared.status, CommandStatus::Passed, "{prepared:?}");
        let input_bytes = fs::read(fixture.source.join(&input_path)).unwrap();
        let input = parse_l2_review_input_json(std::str::from_utf8(&input_bytes).unwrap()).unwrap();
        review_inputs.push(input_path.clone());

        for (authority_index, authority) in policy.authorities.iter().enumerate() {
            let report_path = PathBuf::from(format!(
                "l2-reviews/{module_leaf}/{theorem}.{}.json",
                authority.reviewer_role
            ));
            let report = L2ReviewReport {
                schema: "npa.l2.review-report.v1".to_owned(),
                policy_id: policy.policy_id.clone(),
                policy_version: policy.policy_version,
                policy_file_hash: package_file_hash(&policy_bytes),
                review_protocol: policy.review_protocol.clone(),
                input_path: PackagePath::new(input_path.to_string_lossy()),
                input_file_hash: package_file_hash(&input_bytes),
                input_hash: input.input_hash,
                authority: authority.authority.clone(),
                authority_version: authority.authority_version,
                decision_id: format!(
                    "{}{:04}",
                    authority.decision_id_prefix,
                    theorem_index * policy.authorities.len() + authority_index
                ),
                reviewer_role: authority.reviewer_role.clone(),
                agent_task: format!("{}fixture_{theorem_index}", authority.agent_task_prefix),
                check_results: policy
                    .required_checks
                    .iter()
                    .map(|check| L2ReviewCheckResult {
                        check: check.clone(),
                        decision: L2ReviewCheckDecision::Pass,
                        rationale: "Verified by the integration fixture.".to_owned(),
                    })
                    .collect(),
                verdict: "accepted".to_owned(),
                rationale: "The exact review input is accepted by this fixture.".to_owned(),
                proof_evidence: false,
            };
            let full_report_path = fixture.source.join(&report_path);
            fs::create_dir_all(full_report_path.parent().unwrap()).unwrap();
            fs::write(full_report_path, report.canonical_json().unwrap()).unwrap();
            reviews.push(report_path);
        }
    }

    let acceptance_path = PathBuf::from("l2-acceptance.json");
    let aggregated = run_package_command(PackageCommand::AggregateL2Acceptance(Box::new(
        PackageL2AcceptanceAggregateOptions {
            common: common(&fixture.source),
            policy: policy_path.clone(),
            review_inputs: review_inputs.clone(),
            reviews: reviews.clone(),
            existing: None,
            replacements: Vec::new(),
            out: acceptance_path.clone(),
            check: false,
        },
    )));
    assert_eq!(aggregated.status, CommandStatus::Passed, "{aggregated:?}");

    let in_place = run_package_command(PackageCommand::AggregateL2Acceptance(Box::new(
        PackageL2AcceptanceAggregateOptions {
            common: common(&fixture.source),
            policy: policy_path.clone(),
            review_inputs,
            reviews,
            existing: Some(acceptance_path.clone()),
            replacements: theorems
                .iter()
                .map(|(module, theorem)| {
                    (
                        npa_cert::Name::from_dotted(module),
                        npa_cert::Name::from_dotted(theorem),
                    )
                })
                .collect(),
            out: acceptance_path.clone(),
            check: false,
        },
    )));
    assert_eq!(in_place.status, CommandStatus::Passed, "{in_place:?}");
    assert!(!fixture.source.join("l2-acceptance.json.lock").exists());

    let mapping_path = PathBuf::from("l2-transports/reduction.transport-request.json");
    let request = L2NamespaceTransportRequest {
        schema: "npa.l2_namespace_transport_request.v1".to_owned(),
        source: L2TransportPackageIdentity {
            package: theorem_index.package.clone(),
            version: theorem_index.version.clone(),
        },
        target: L2TransportPackageIdentity {
            package: npa_package::PackageId::new("npa-mathlib"),
            version: npa_package::PackageVersion::new("0.2.0"),
        },
        module_mappings: selected_modules
            .iter()
            .map(|(source_module, target_module)| L2TransportModuleMapping {
                role: L2TransportModuleRole::Selected,
                source: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: theorem_index.package.clone(),
                    version: theorem_index.version.clone(),
                    module: npa_cert::Name::from_dotted(source_module),
                },
                target: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: npa_package::PackageId::new("npa-mathlib"),
                    version: npa_package::PackageVersion::new("0.2.0"),
                    module: npa_cert::Name::from_dotted(target_module),
                },
                declaration_mapping: "same-name-except-explicit".to_owned(),
                renames: Vec::new(),
            })
            .chain(std::iter::once(L2TransportModuleMapping {
                role: L2TransportModuleRole::Dependency,
                source: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::External,
                    package: npa_package::PackageId::new("npa-seed-dependency"),
                    version: npa_package::PackageVersion::new("0.1.0"),
                    module: npa_cert::Name::from_dotted("Proofs.Ai.Basic"),
                },
                target: L2TransportEndpoint {
                    origin: PackageArtifactOrigin::Local,
                    package: npa_package::PackageId::new("npa-mathlib"),
                    version: npa_package::PackageVersion::new("0.2.0"),
                    module: npa_cert::Name::from_dotted("Mathlib.Logic.Basic"),
                },
                declaration_mapping: "same-name-except-explicit".to_owned(),
                renames: Vec::new(),
            }))
            .collect(),
        proof_evidence: false,
    };
    let full_mapping_path = fixture.source.join(&mapping_path);
    fs::create_dir_all(full_mapping_path.parent().unwrap()).unwrap();
    fs::write(full_mapping_path, request.canonical_json().unwrap()).unwrap();

    let plan_path = PathBuf::from("promotions/reduction.plan.json");
    let prepare_options = PackagePreparePromotionOptions {
        common: common(&fixture.source),
        target_baseline_root: fixture.baseline.clone(),
        acceptance_policy: policy_path.clone(),
        source_acceptance: acceptance_path.clone(),
        transport_policy: transport_policy_path.clone(),
        mapping: mapping_path.clone(),
        equivalent_origin_roots: vec![fixture.equivalent_source.clone()],
        out: plan_path.clone(),
        check: false,
    };
    let prepared = run_package_command(PackageCommand::PreparePromotion(Box::new(
        prepare_options.clone(),
    )));
    assert_eq!(prepared.status, CommandStatus::Passed, "{prepared:?}");
    let checked = run_package_command(PackageCommand::PreparePromotion(Box::new(
        PackagePreparePromotionOptions {
            check: true,
            ..prepare_options
        },
    )));
    assert_eq!(checked.status, CommandStatus::Passed, "{checked:?}");

    let collision_baseline = fixture.root.join("collision-baseline");
    copy_directory(&fixture.baseline, &collision_baseline);
    let collision_path = collision_baseline.join("Mathlib/Logic/Prop/source.npa");
    fs::create_dir_all(collision_path.parent().unwrap()).unwrap();
    fs::write(&collision_path, b"orphan target artifact\n").unwrap();
    let collision_plan_path = PathBuf::from("promotions/collision.plan.json");
    let collision_prepare = run_package_command(PackageCommand::PreparePromotion(Box::new(
        PackagePreparePromotionOptions {
            common: common(&fixture.source),
            target_baseline_root: collision_baseline.clone(),
            acceptance_policy: policy_path.clone(),
            source_acceptance: acceptance_path.clone(),
            transport_policy: transport_policy_path.clone(),
            mapping: mapping_path.clone(),
            equivalent_origin_roots: vec![fixture.equivalent_source.clone()],
            out: collision_plan_path.clone(),
            check: false,
        },
    )));
    assert_eq!(collision_prepare.status, CommandStatus::Failed);
    assert_eq!(
        collision_prepare.diagnostics[0].reason_code,
        "promotion_plan_target_artifact_collision"
    );
    assert!(!fixture.source.join(collision_plan_path).exists());

    let directory_collision_baseline = fixture.root.join("directory-collision-baseline");
    let directory_collision_target = fixture.root.join("directory-collision-target");
    copy_directory(&fixture.baseline, &directory_collision_baseline);
    fs::create_dir_all(directory_collision_baseline.join("Mathlib/Logic/Prop/source.npa")).unwrap();
    copy_directory(&directory_collision_baseline, &directory_collision_target);
    let collision_before = snapshot_directory(&directory_collision_target);
    let mut collision_options = materialize_options(
        &fixture,
        &directory_collision_target,
        &plan_path,
        vec![fixture.equivalent_source.clone()],
        PackagePromotionPhase::Temporary,
        None,
        true,
    );
    collision_options.target_baseline_root = Some(directory_collision_baseline);
    let collision_materialize = run_package_command(PackageCommand::MaterializePromotion(
        Box::new(collision_options),
    ));
    assert_eq!(collision_materialize.status, CommandStatus::Failed);
    assert_eq!(
        collision_materialize.diagnostics[0].reason_code,
        "promotion_plan_target_artifact_collision"
    );
    assert_eq!(
        snapshot_directory(&directory_collision_target),
        collision_before
    );

    let missing_equivalent_origin = run_package_command(PackageCommand::MaterializePromotion(
        Box::new(materialize_options(
            &fixture,
            &fixture.target,
            &plan_path,
            Vec::new(),
            PackagePromotionPhase::Temporary,
            None,
            false,
        )),
    ));
    assert_eq!(missing_equivalent_origin.status, CommandStatus::Failed);
    assert_eq!(
        missing_equivalent_origin.diagnostics[0].reason_code,
        "promotion_materialize_plan_stale"
    );
    let wrong_equivalent_origin = run_package_command(PackageCommand::MaterializePromotion(
        Box::new(materialize_options(
            &fixture,
            &fixture.target,
            &plan_path,
            vec![fixture.source.clone()],
            PackagePromotionPhase::Temporary,
            None,
            false,
        )),
    ));
    assert_eq!(wrong_equivalent_origin.status, CommandStatus::Failed);
    assert_eq!(
        wrong_equivalent_origin.diagnostics[0].reason_code,
        "promotion_materialize_plan_stale"
    );

    let dry_run = run_package_command(PackageCommand::MaterializePromotion(Box::new(
        materialize_options(
            &fixture,
            &fixture.target,
            &plan_path,
            vec![fixture.equivalent_source.clone()],
            PackagePromotionPhase::Temporary,
            None,
            false,
        ),
    )));
    let repeated_dry_run = run_package_command(PackageCommand::MaterializePromotion(Box::new(
        materialize_options(
            &fixture,
            &fixture.target,
            &plan_path,
            vec![fixture.equivalent_source.clone()],
            PackagePromotionPhase::Temporary,
            None,
            false,
        ),
    )));
    assert_eq!(dry_run.status, CommandStatus::Passed, "{dry_run:?}");
    assert_eq!(repeated_dry_run, dry_run);

    let materialized = run_package_command(PackageCommand::MaterializePromotion(Box::new(
        materialize_options(
            &fixture,
            &fixture.target,
            &plan_path,
            vec![fixture.equivalent_source.clone()],
            PackagePromotionPhase::Temporary,
            None,
            true,
        ),
    )));
    assert_eq!(
        materialized.status,
        CommandStatus::Passed,
        "{materialized:?}"
    );

    let attestation_path = PathBuf::from("l2-transports/reduction.transport.json");
    let options = PackageL2NamespaceTransportOptions {
        common: common(&fixture.source),
        target_baseline_root: fixture.baseline.clone(),
        target_root: fixture.target.clone(),
        acceptance_policy: policy_path.clone(),
        source_acceptance: acceptance_path.clone(),
        transport_policy: transport_policy_path.clone(),
        mapping: mapping_path.clone(),
        out: Some(attestation_path.clone()),
        check: false,
    };
    let transported = run_package_command(PackageCommand::ValidateL2NamespaceTransport(Box::new(
        options.clone(),
    )));
    assert_eq!(transported.status, CommandStatus::Passed, "{transported:?}");
    let attestation = parse_l2_namespace_transport_attestation_json(
        &fs::read_to_string(fixture.source.join(&attestation_path)).unwrap(),
    )
    .unwrap();
    assert_eq!(attestation.module_pairs.len(), 3);
    assert_eq!(attestation.theorem_pairs.len(), theorems.len());

    let reproduced = run_package_command(PackageCommand::ValidateL2NamespaceTransport(Box::new(
        PackageL2NamespaceTransportOptions {
            check: true,
            ..options.clone()
        },
    )));
    assert_eq!(reproduced.status, CommandStatus::Passed, "{reproduced:?}");

    let tracked = run_package_command(PackageCommand::MaterializePromotion(Box::new(
        materialize_options(
            &fixture,
            &fixture.tracked,
            &plan_path,
            vec![fixture.equivalent_source.clone()],
            PackagePromotionPhase::Tracked,
            Some(attestation_path.clone()),
            true,
        ),
    )));
    assert_eq!(tracked.status, CommandStatus::Passed, "{tracked:?}");

    let registry_validation = run_package_command(PackageCommand::ValidatePromotionOriginRegistry(
        PackageValidatePromotionOriginRegistryOptions {
            common: common(&fixture.tracked),
            source_roots: vec![fixture.source.clone(), fixture.equivalent_source.clone()],
            previous_registry: Some(fixture.baseline.join("promotion-origins.json")),
        },
    ));
    assert_eq!(
        registry_validation.status,
        CommandStatus::Passed,
        "{registry_validation:?}"
    );
    let registry = parse_promotion_origin_registry_json(
        &fs::read_to_string(fixture.tracked.join("promotion-origins.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(registry.entries.len(), 1);
    assert_eq!(registry.entries[0].equivalent_sources.len(), 1);
    let replay = parse_package_proof_replay(
        &fs::read_to_string(fixture.tracked.join("Mathlib/Core/Reduction/replay.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(replay.module.as_dotted(), "Mathlib.Core.Reduction");
    assert_eq!(
        replay.accepted_artifact.as_ref().map(PackagePath::as_str),
        Some("Mathlib/Core/Reduction/certificate.npcert")
    );

    let tracked_before_repeat = snapshot_directory(&fixture.tracked);
    let repeated_tracked = run_package_command(PackageCommand::MaterializePromotion(Box::new(
        materialize_options(
            &fixture,
            &fixture.tracked,
            &plan_path,
            vec![fixture.equivalent_source.clone()],
            PackagePromotionPhase::Tracked,
            Some(attestation_path.clone()),
            true,
        ),
    )));
    assert_eq!(repeated_tracked.status, CommandStatus::Failed);
    assert_eq!(
        repeated_tracked.diagnostics[0].reason_code,
        "promotion_materialize_target_not_clean"
    );
    assert_eq!(snapshot_directory(&fixture.tracked), tracked_before_repeat);

    fs::write(
        fixture.target.join("Mathlib/Core/Reduction/source.npa"),
        b"tampered\n",
    )
    .unwrap();
    let stale = run_package_command(PackageCommand::ValidateL2NamespaceTransport(Box::new(
        PackageL2NamespaceTransportOptions {
            check: true,
            ..options.clone()
        },
    )));
    assert_eq!(stale.status, CommandStatus::Failed);
}

#[test]
fn materialize_recovery_covers_every_journal_state() {
    run_recovery_case(
        "all-old",
        PromotionTransactionState::Applying,
        &[
            recovery_file(
                "present.txt",
                Some(b"old one\n"),
                b"new one\n",
                Some(b"old one\n"),
                PromotionReplacementState::Pending,
            ),
            recovery_file(
                "absent.txt",
                None,
                b"created\n",
                None,
                PromotionReplacementState::Pending,
            ),
        ],
        CommandStatus::Passed,
        false,
    );
    run_recovery_case(
        "mixed",
        PromotionTransactionState::Applying,
        &[
            recovery_file(
                "present.txt",
                Some(b"old one\n"),
                b"new one\n",
                Some(b"new one\n"),
                PromotionReplacementState::Replaced,
            ),
            recovery_file(
                "other.txt",
                Some(b"old two\n"),
                b"new two\n",
                Some(b"old two\n"),
                PromotionReplacementState::Pending,
            ),
        ],
        CommandStatus::Passed,
        true,
    );
    run_recovery_case(
        "all-new-applying",
        PromotionTransactionState::Applying,
        &[
            recovery_file(
                "present.txt",
                Some(b"old one\n"),
                b"new one\n",
                Some(b"new one\n"),
                PromotionReplacementState::Replaced,
            ),
            recovery_file(
                "absent.txt",
                None,
                b"created\n",
                Some(b"created\n"),
                PromotionReplacementState::Replaced,
            ),
        ],
        CommandStatus::Passed,
        false,
    );
    run_recovery_case(
        "all-new-validated",
        PromotionTransactionState::Validated,
        &[
            recovery_file(
                "present.txt",
                Some(b"old one\n"),
                b"new one\n",
                Some(b"new one\n"),
                PromotionReplacementState::Replaced,
            ),
            recovery_file(
                "absent.txt",
                None,
                b"created\n",
                Some(b"created\n"),
                PromotionReplacementState::Replaced,
            ),
        ],
        CommandStatus::Passed,
        false,
    );
    run_recovery_case(
        "conflict",
        PromotionTransactionState::Applying,
        &[recovery_file(
            "present.txt",
            Some(b"old one\n"),
            b"new one\n",
            Some(b"conflict\n"),
            PromotionReplacementState::Replaced,
        )],
        CommandStatus::Failed,
        false,
    );
}

struct RecoveryFile<'a> {
    path: &'a str,
    old: Option<&'a [u8]>,
    new: &'a [u8],
    current: Option<&'a [u8]>,
    replacement_state: PromotionReplacementState,
}

fn recovery_file<'a>(
    path: &'a str,
    old: Option<&'a [u8]>,
    new: &'a [u8],
    current: Option<&'a [u8]>,
    replacement_state: PromotionReplacementState,
) -> RecoveryFile<'a> {
    RecoveryFile {
        path,
        old,
        new,
        current,
        replacement_state,
    }
}

fn run_recovery_case(
    label: &str,
    transaction_state: PromotionTransactionState,
    files: &[RecoveryFile<'_>],
    expected_status: CommandStatus,
    leave_journal_next: bool,
) {
    let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
    let root = std::env::temp_dir().join(format!(
        "npa-cli-promotion-recovery-{}-{index}-{label}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&root);
    let target = root.join("target");
    fs::create_dir_all(&target).unwrap();
    for file in files {
        if let Some(current) = file.current {
            let path = target.join(file.path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, current).unwrap();
        }
    }

    let promotion_id = package_file_hash(label.as_bytes());
    let transaction = root.join(format!(
        ".npa-promotion-transaction-{}",
        format_package_hash(&promotion_id).trim_start_matches("sha256:")
    ));
    fs::create_dir_all(transaction.join("old")).unwrap();
    fs::create_dir_all(transaction.join("new")).unwrap();
    let rows = files
        .iter()
        .enumerate()
        .map(|(index, file)| {
            let logical_path = PackagePath::new(file.path);
            let path_hash = promotion_transaction_path_hash(&logical_path).unwrap();
            let staged_name = format_package_hash(&path_hash)
                .trim_start_matches("sha256:")
                .to_owned();
            if let Some(old) = file.old {
                fs::write(transaction.join("old").join(&staged_name), old).unwrap();
            }
            fs::write(transaction.join("new").join(&staged_name), file.new).unwrap();
            PromotionTransactionRow {
                replacement_order: index as u64,
                logical_path,
                logical_path_hash: path_hash,
                old: file.old.map_or(PromotionOldFile::Absent, |old| {
                    PromotionOldFile::Present(package_file_hash(old))
                }),
                new_file_hash: package_file_hash(file.new),
                replacement_state: file.replacement_state,
            }
        })
        .collect();
    let canonical_target = fs::canonicalize(&target).unwrap();
    let mut journal = PromotionTransactionJournal {
        schema: MATHLIB_PROMOTION_TRANSACTION_SCHEMA.to_owned(),
        promotion_id,
        phase: PromotionTransactionPhase::Tracked,
        target_canonical_path_hash: package_file_hash(
            canonical_target.to_string_lossy().as_bytes(),
        ),
        transaction_state,
        rows,
        journal_hash: PackageHash::new([0; 32]),
        proof_evidence: false,
    };
    journal.refresh_hash().unwrap();
    fs::write(
        transaction.join("journal.json"),
        journal.canonical_json().unwrap(),
    )
    .unwrap();
    if leave_journal_next {
        fs::write(
            transaction.join("journal.next"),
            b"interrupted partial write",
        )
        .unwrap();
    }

    let recovered = run_package_command(PackageCommand::MaterializePromotion(Box::new(
        PackageMaterializePromotionOptions {
            common: common(&target),
            target_baseline_root: None,
            target_root: target.clone(),
            plan: None,
            equivalent_origin_roots: Vec::new(),
            transport_attestation: None,
            phase: None,
            apply: false,
            recover: Some(transaction.join("journal.json")),
        },
    )));
    assert_eq!(recovered.status, expected_status, "{recovered:?}");
    if expected_status == CommandStatus::Passed {
        let keep_new = transaction_state == PromotionTransactionState::Validated;
        for file in files {
            let actual = fs::read(target.join(file.path)).ok();
            let expected = if keep_new { Some(file.new) } else { file.old };
            assert_eq!(actual.as_deref(), expected, "{label}: {}", file.path);
        }
        assert!(!transaction.exists());
    } else {
        for file in files {
            assert_eq!(
                fs::read(target.join(file.path)).ok().as_deref(),
                file.current,
                "{label}: {}",
                file.path
            );
        }
        assert!(transaction.exists());
    }
    let _ = fs::remove_dir_all(root);
}

fn materialize_options(
    fixture: &Fixture,
    target_root: &Path,
    plan: &Path,
    equivalent_origin_roots: Vec<PathBuf>,
    phase: PackagePromotionPhase,
    transport_attestation: Option<PathBuf>,
    apply: bool,
) -> PackageMaterializePromotionOptions {
    PackageMaterializePromotionOptions {
        common: common(&fixture.source),
        target_baseline_root: Some(fixture.baseline.clone()),
        target_root: target_root.to_path_buf(),
        plan: Some(plan.to_path_buf()),
        equivalent_origin_roots,
        transport_attestation,
        phase: Some(phase),
        apply,
        recover: None,
    }
}

fn regenerate_generated_artifacts(root: &Path) {
    let common = common(root);
    for command in [
        PackageCommand::Lock(PackageLockCommand::Write(common.clone())),
        PackageCommand::AxiomReport(PackageAxiomReportOptions {
            common: common.clone(),
            check: false,
            timings: PackageTimingMode::Off,
        }),
        PackageCommand::Index(PackageIndexOptions {
            common: common.clone(),
            check: false,
            timings: PackageTimingMode::Off,
        }),
        PackageCommand::TheoremPremiseReport(npa_cli::package_api::v1::theorem_premise_report(
            common, false,
        )),
    ] {
        let result = run_package_command(command);
        assert_eq!(result.status, CommandStatus::Passed, "{result:?}");
    }
}

fn install_external_existing_dependency(root: &Path) {
    let manifest_path = root.join("npa-package.toml");
    let manifest_source = fs::read_to_string(&manifest_path).unwrap();
    let manifest = parse_and_validate_manifest_str(&manifest_source)
        .unwrap()
        .into_manifest();
    let basic = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == "Proofs.Ai.Basic")
        .unwrap();
    let vendor_certificate = "vendor/npa-seed-dependency/Proofs/Ai/Basic/certificate.npcert";
    let vendor_path = root.join(vendor_certificate);
    fs::create_dir_all(vendor_path.parent().unwrap()).unwrap();
    fs::copy(root.join(basic.certificate.as_str()), &vendor_path).unwrap();

    remove_manifest_module(root, "Proofs.Ai.Basic");
    let source = fs::read_to_string(&manifest_path).unwrap();
    let import = format!(
        "[[imports]]\nmodule = \"Proofs.Ai.Basic\"\npackage = \"npa-seed-dependency\"\nversion = \"0.1.0\"\ncertificate = \"{vendor_certificate}\"\nexport_hash = \"{}\"\ncertificate_hash = \"{}\"\n\n",
        npa_package::format_package_hash(&basic.expected_export_hash),
        npa_package::format_package_hash(&basic.expected_certificate_hash),
    );
    let source = source.replacen("[[modules]]", &format!("{import}[[modules]]"), 1);
    let source = source.replacen(
        "imports = [\"Std.Nat.Basic\"]",
        "imports = [\"Std.Nat.Basic\", \"Proofs.Ai.Basic\"]",
        1,
    );
    fs::write(&manifest_path, source).unwrap();
    let reduction_source = root.join("Proofs/Ai/Reduction/source.npa");
    let source = fs::read_to_string(&reduction_source).unwrap();
    fs::write(
        reduction_source,
        format!("import Proofs.Ai.Basic\n{source}"),
    )
    .unwrap();

    let built = run_package_command(PackageCommand::BuildCerts(
        npa_cli::package_api::v1::refresh_artifacts_write(common(root)),
    ));
    assert_eq!(built.status, CommandStatus::Passed, "{built:?}");
    regenerate_generated_artifacts(root);
}

fn install_promotion_governance(root: &Path) {
    let policy_source = repo_root().join("testdata/package/promotion-policy");
    copy_directory(&policy_source, &root.join("policy"));

    let manifest = parse_and_validate_manifest_str(
        &fs::read_to_string(root.join("npa-package.toml")).unwrap(),
    )
    .unwrap()
    .into_manifest();
    let theorem_index = parse_package_theorem_index_json(
        &fs::read_to_string(root.join("generated/theorem-index.json")).unwrap(),
    )
    .unwrap();
    let evidence = PromotionEvidence::LegacyAudit {
        audit_location: PromotionAuditLocation {
            repository: "npa-cli-integration-fixture".to_owned(),
            path: PackagePath::new("legacy-promotion-audit.md"),
        },
        audit_file_hash: package_file_hash(b"npa-cli integration fixture legacy audit\n"),
    };
    let mut reservations = manifest
        .modules
        .iter()
        .map(|module| {
            let mut theorems = theorem_index
                .entries
                .iter()
                .filter(|entry| {
                    entry.global_ref.module == module.module
                        && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
                        && entry.artifact.origin == PackageArtifactOrigin::Local
                })
                .map(|entry| PromotionReservedTheorem {
                    target_name: entry.global_ref.name.clone(),
                    target_statement_hash: entry.statement.core_hash,
                })
                .collect::<Vec<_>>();
            theorems.sort();
            let revision = PromotionTargetRevision {
                target_version: manifest.version.clone(),
                target_source_file_hash: package_file_hash(
                    &fs::read(root.join(module.source.as_str())).unwrap(),
                ),
                target_certificate_file_hash: module.expected_certificate_file_hash,
                target_certificate_hash: module.expected_certificate_hash,
                target_export_hash: module.expected_export_hash,
                target_axiom_report_hash: module.expected_axiom_report_hash,
                theorems,
            };
            PromotionLegacyTargetReservation {
                reservation_id: promotion_legacy_target_reservation_id(&module.module, &revision)
                    .unwrap(),
                lifecycle: PromotionLifecycle::Active,
                target_module: module.module.clone(),
                target_revisions: vec![revision],
                evidence: evidence.clone(),
            }
        })
        .collect::<Vec<_>>();
    reservations.sort_by_key(|row| row.reservation_id);
    let mut registry = PromotionOriginRegistry {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
        registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
        registry_version: 1,
        generation: 1,
        target_package: manifest.package,
        entries: Vec::new(),
        unresolved_legacy_targets: reservations,
        registry_hash: package_file_hash(b"placeholder"),
        proof_evidence: false,
    };
    registry.refresh_hash().unwrap();
    fs::write(
        root.join("promotion-origins.json"),
        registry.canonical_json().unwrap(),
    )
    .unwrap();
}

fn remove_manifest_module(root: &Path, module: &str) {
    let path = root.join("npa-package.toml");
    let source = fs::read_to_string(&path).unwrap();
    let marker = "[[modules]]";
    let mut parts = source.split(marker);
    let mut rewritten = parts.next().unwrap().to_owned();
    for part in parts {
        if !part.contains(&format!("module = \"{module}\"")) {
            rewritten.push_str(marker);
            rewritten.push_str(part);
        }
    }
    fs::write(path, rewritten).unwrap();
}

fn replace_manifest_package(root: &Path, old: &str, new: &str) {
    let path = root.join("npa-package.toml");
    let source = fs::read_to_string(&path).unwrap();
    let old_line = format!("package = \"{old}\"");
    let new_line = format!("package = \"{new}\"");
    assert!(source.contains(&old_line));
    fs::write(path, source.replacen(&old_line, &new_line, 1)).unwrap();
}

fn common(root: &Path) -> PackageCommonOptions {
    let mut common = PackageCommonOptions::default();
    common.root = root.to_path_buf();
    common.json = true;
    common
}

fn copy_directory(source: &Path, target: &Path) {
    fs::create_dir_all(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_directory(&source_path, &target_path);
        } else {
            fs::copy(source_path, target_path).unwrap();
        }
    }
}

fn snapshot_directory(root: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(root: &Path, current: &Path, files: &mut BTreeMap<PathBuf, Vec<u8>>) {
        let mut entries = fs::read_dir(current)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            if entry.file_type().unwrap().is_dir() {
                walk(root, &path, files);
            } else {
                files.insert(
                    path.strip_prefix(root).unwrap().to_path_buf(),
                    fs::read(path).unwrap(),
                );
            }
        }
    }
    let mut files = BTreeMap::new();
    walk(root, root, &mut files);
    files
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}
