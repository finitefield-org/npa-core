use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::Name;
use npa_cli::args::{
    PackageCommand, PackageCommonOptions, PackageRefactorPlanOptions, PackageRefactorPlanScope,
};
use npa_cli::diagnostic::{
    CommandExitCode, CommandStatus, DiagnosticKind, DiagnosticSeverity,
    PACKAGE_COMMAND_RESULT_SCHEMA,
};
use npa_cli::package::run_package_command;
use npa_cli::package_artifacts::{PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH};
use npa_cli::package_refactor_plan::{
    build_refactor_plan_module_candidates, build_refactor_plan_module_graph,
    load_refactor_plan_metadata, ModuleRefactorCandidate, RefactorCandidate,
    RefactorPlanModuleGraph, RefactorRecommendation, RefactorRisk, TheoremFamilyRefactorCandidate,
    TheoremIndexStatus, REFACTOR_PLAN_REPORT_SCHEMA,
};
use npa_package::{
    package_theorem_index_summary, parse_package_lock_json, parse_package_theorem_index_json,
    PackageArtifactOrigin, PackageGlobalRefView, PackageTheoremIndex, PackageTheoremIndexEntry,
    PackageTheoremIndexKind,
};

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct MetadataFixture {
    path: PathBuf,
}

impl MetadataFixture {
    fn new(label: &str, include_theorem_index: bool) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-refactor-plan-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(path.join("generated")).unwrap();
        let source = repo_root().join("testdata/package/proofs");
        fs::copy(
            source.join("npa-package.toml"),
            path.join("npa-package.toml"),
        )
        .unwrap();
        fs::copy(source.join(PACKAGE_LOCK_PATH), path.join(PACKAGE_LOCK_PATH)).unwrap();
        if include_theorem_index {
            fs::copy(
                source.join(PACKAGE_THEOREM_INDEX_PATH),
                path.join(PACKAGE_THEOREM_INDEX_PATH),
            )
            .unwrap();
        }
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn artifact_path(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for MetadataFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn package_refactor_plan_loads_lock_graph_and_checked_theorem_index() {
    let package = MetadataFixture::new("with-index", true);
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Basic/replay.json")
        .exists());
    assert!(!package.artifact_path("Proofs/Ai/Basic/meta.json").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Basic/certificate.npcert")
        .exists());

    let loaded = load_refactor_plan_metadata(&options(package.path(), None)).unwrap();

    assert_eq!(loaded.root_display, "<absolute-root>");
    assert_eq!(loaded.package_lock.entries.len(), 8);
    assert!(loaded
        .package_lock_graph
        .topological_order
        .contains(&name("Proofs.Ai.Basic")));
    assert!(loaded.theorem_index.is_some());
    assert_eq!(loaded.report.schema, REFACTOR_PLAN_REPORT_SCHEMA);
    assert_eq!(loaded.report.root, "<absolute-root>");
    assert_eq!(loaded.report.scope, PackageRefactorPlanScope::Modules);
    assert_eq!(
        loaded.report.theorem_index_status,
        TheoremIndexStatus::Loaded
    );
    assert!(loaded.report.warnings.is_empty());
    assert_eq!(loaded.report.candidates.len(), 6);
    assert!(loaded.report.candidates.iter().all(|candidate| {
        matches!(candidate, RefactorCandidate::Module(module) if !module.proof_evidence)
    }));
    assert!(module_candidate(&loaded.report.candidates, "Std.Logic.Eq").is_none());
    assert!(!loaded.report.proof_evidence);
}

#[test]
fn package_refactor_plan_missing_theorem_index_is_advisory() {
    let package = MetadataFixture::new("missing-index", false);

    let loaded = load_refactor_plan_metadata(&options(package.path(), None)).unwrap();

    assert!(loaded.theorem_index.is_none());
    assert_eq!(
        loaded.report.theorem_index_status,
        TheoremIndexStatus::Missing
    );
    assert_eq!(loaded.report.theorem_index_status.as_str(), "missing");
    assert!(!loaded.report.proof_evidence);
    assert!(loaded.report.candidates.iter().all(|candidate| {
        matches!(candidate, RefactorCandidate::Module(module) if module.metrics.theorem_count.is_none())
    }));
    assert!(loaded.report.candidates.iter().all(|candidate| {
        matches!(candidate, RefactorCandidate::Module(module) if module
            .evidence
            .contains(&"theorem_index_missing".to_owned()))
    }));
}

#[test]
fn package_refactor_plan_theorem_index_populates_module_metrics() {
    let package = MetadataFixture::new("theorem-index-metrics", true);

    let loaded = load_refactor_plan_metadata(&options(package.path(), None)).unwrap();

    assert!(loaded.theorem_aggregation.is_some());
    let basic = module_candidate(&loaded.report.candidates, "Proofs.Ai.Basic")
        .expect("expected Basic module candidate");
    assert_eq!(basic.metrics.theorem_count, Some(20));
    assert_eq!(basic.metrics.axiom_count, Some(0));
    assert_eq!(basic.metrics.public_export_count, Some(20));
    assert_eq!(basic.metrics.family_cluster_count, 1);
    assert_eq!(basic.metrics.local_complexity, 40.0);
    assert_eq!(basic.score, 42.0);
    assert_eq!(basic.recommendation, RefactorRecommendation::LocalCleanup);
    assert_eq!(basic.risk, RefactorRisk::Low);
    assert_eq!(basic.suggested_unit, "Proofs.Ai.Basic::imp_*");
    assert_eq!(basic.suggested_verification, low_risk_verification());

    let group = module_candidate(&loaded.report.candidates, "Proofs.Ai.Algebra.AbstractGroup")
        .expect("expected AbstractGroup module candidate");
    assert_eq!(group.metrics.theorem_count, Some(23));
    assert_eq!(group.metrics.axiom_count, Some(0));
    assert_eq!(group.metrics.public_export_count, Some(23));
    assert_eq!(group.metrics.family_cluster_count, 3);
    assert_eq!(group.metrics.local_complexity, 50.0);
    assert_eq!(group.metrics.dependent_complexity, 16.0);
    assert_eq!(group.score, 92.0);
}

#[test]
fn package_refactor_plan_theorem_families_filter_and_group_local_entries() {
    let package = MetadataFixture::new("theorem-families", true);
    rewrite_theorem_index(&package, |index| {
        let template = index.entries[0].clone();
        index.entries = vec![
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Basic",
                "foo_a",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::Local,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Std.Logic.Eq", "Eq"), ("Proofs.Ai.Basic", "id")],
            ),
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Basic",
                "foo_b",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::Local,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Std.Logic.Eq", "Eq"), ("Proofs.Ai.Basic", "compose")],
            ),
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Basic",
                "foo_c",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::Local,
                Some(("Proofs.Ai.Basic", "Prop")),
                &[("Std.Logic.Eq", "Eq")],
            ),
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Basic",
                "foo_axiom",
                PackageTheoremIndexKind::Axiom,
                PackageArtifactOrigin::Local,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Proofs.Ai.Basic", "id")],
            ),
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Basic",
                "bar_a",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::Local,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Std.Logic.Eq", "Eq")],
            ),
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Basic",
                "bar_b",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::Local,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Std.Logic.Eq", "Eq")],
            ),
            custom_theorem_entry(
                &template,
                "Std.Logic.Eq",
                "eq_external_ignored",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::External,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Std.Logic.Eq", "Eq")],
            ),
            custom_theorem_entry(
                &template,
                "Proofs.Ai.Unknown",
                "unknown_local_warns",
                PackageTheoremIndexKind::Theorem,
                PackageArtifactOrigin::Local,
                Some(("Std.Logic.Eq", "Eq")),
                &[("Std.Logic.Eq", "Eq")],
            ),
        ];
    });

    let loaded = load_refactor_plan_metadata(&options_with_scope(
        package.path(),
        PackageRefactorPlanScope::Both,
        None,
    ))
    .unwrap();

    assert_eq!(
        loaded.report.warnings,
        vec!["theorem_index_entry_unknown_module"]
    );
    let basic = module_candidate(&loaded.report.candidates, "Proofs.Ai.Basic")
        .expect("expected Basic module candidate");
    assert_eq!(basic.metrics.theorem_count, Some(5));
    assert_eq!(basic.metrics.axiom_count, Some(1));
    assert_eq!(basic.metrics.public_export_count, Some(6));
    assert_eq!(basic.metrics.family_cluster_count, 1);
    assert_eq!(basic.metrics.local_complexity, 14.0);
    assert_eq!(basic.score, 16.0);
    assert_eq!(basic.recommendation, RefactorRecommendation::NoAction);
    assert_eq!(basic.risk, RefactorRisk::Low);

    let family = theorem_family_candidate(
        &loaded.report.candidates,
        "Proofs.Ai.Basic",
        "Proofs.Ai.Basic::foo_*",
    )
    .expect("expected foo theorem-family candidate");
    assert_eq!(
        family.theorem_names,
        vec!["foo_a", "foo_axiom", "foo_b", "foo_c"]
    );
    assert_eq!(family.metrics.theorem_count, 3);
    assert_eq!(family.metrics.axiom_count, 1);
    assert_eq!(family.metrics.shared_prefix_length, 3);
    assert_eq!(family.metrics.statement_head_count, 2);
    assert_eq!(family.metrics.statement_constant_count, 3);
    assert_eq!(family.score, 13.0);
    assert_eq!(
        family.recommendation,
        RefactorRecommendation::TheoremFamilyGroup
    );
    assert_eq!(family.risk, RefactorRisk::High);
    assert_eq!(
        family.evidence,
        vec![
            "axiom_bearing_family",
            "shared_name_prefix",
            "statement_constant_signal"
        ]
    );
    assert_eq!(family.suggested_unit, "Proofs.Ai.Basic::foo_*");
    assert_eq!(family.suggested_verification, high_risk_verification());
    assert!(!family.proof_evidence);

    assert!(theorem_family_candidate(
        &loaded.report.candidates,
        "Proofs.Ai.Basic",
        "Proofs.Ai.Basic::bar_*",
    )
    .is_none());
    assert!(!format!("{:?}", loaded.report.candidates).contains("proof-dependent"));
}

#[test]
fn package_refactor_plan_large_theorem_family_scores_medium_risk() {
    let package = MetadataFixture::new("large-theorem-family", true);

    let loaded = load_refactor_plan_metadata(&options_with_scope(
        package.path(),
        PackageRefactorPlanScope::Theorems,
        Some("Proofs.Ai.EqReasoning"),
    ))
    .unwrap();

    assert_eq!(loaded.report.candidates.len(), 1);
    let family = theorem_family_candidate(
        &loaded.report.candidates,
        "Proofs.Ai.EqReasoning",
        "Proofs.Ai.EqReasoning::eq_*",
    )
    .expect("expected EqReasoning eq family");
    assert_eq!(family.metrics.theorem_count, 11);
    assert_eq!(family.metrics.axiom_count, 0);
    assert_eq!(family.metrics.module_dependent_complexity, 100.0);
    assert_eq!(family.score, 124.0);
    assert_eq!(family.risk, RefactorRisk::Medium);
    assert_eq!(
        family.evidence,
        vec![
            "large_theorem_family",
            "shared_name_prefix",
            "statement_constant_signal"
        ]
    );
    assert_eq!(family.suggested_verification, low_risk_verification());
}

#[test]
fn package_refactor_plan_module_metrics_are_local_source_free_and_deterministic() {
    let package = MetadataFixture::new("module-metrics", false);

    let loaded = load_refactor_plan_metadata(&options(package.path(), None)).unwrap();

    let eq_reasoning = module_candidate(&loaded.report.candidates, "Proofs.Ai.EqReasoning")
        .expect("expected EqReasoning module candidate");
    assert_eq!(eq_reasoning.metrics.direct_import_count, 1);
    assert_eq!(eq_reasoning.metrics.direct_dependents, 3);
    assert_eq!(eq_reasoning.metrics.transitive_dependents, 3);
    assert_eq!(eq_reasoning.metrics.local_complexity, 2.0);
    assert_eq!(eq_reasoning.metrics.dependent_complexity, 14.0);
    assert_eq!(eq_reasoning.metrics.certificate_size_bytes, None);
    assert_eq!(eq_reasoning.metrics.certificate_size_weight, 0.0);
    assert_eq!(
        eq_reasoning.evidence,
        vec!["certificate_metadata_unavailable", "theorem_index_missing"]
    );
    assert_eq!(eq_reasoning.suggested_unit, "Proofs.Ai.EqReasoning");

    let group = module_candidate(&loaded.report.candidates, "Proofs.Ai.Algebra.AbstractGroup")
        .expect("expected AbstractGroup module candidate");
    assert_eq!(group.metrics.direct_dependents, 1);
    assert_eq!(group.metrics.transitive_dependents, 1);
    assert_eq!(group.metrics.dependent_complexity, 6.0);
}

#[test]
fn package_refactor_plan_high_fanout_scores_stabilize_boundary_and_limits_top() {
    let package = MetadataFixture::new("high-fanout", false);
    let lock = parse_package_lock_json(&high_fanout_lock_json(12)).unwrap();
    let graph = build_refactor_plan_module_graph(&lock).unwrap();
    let candidates = build_refactor_plan_module_candidates(
        package.path(),
        &lock,
        &graph,
        &options_with_scope_top(package.path(), PackageRefactorPlanScope::Modules, None, 1),
    );

    assert_eq!(candidates.len(), 1);
    let a = module_candidate(&candidates, "Fixture.A").expect("expected Fixture.A candidate");
    assert_eq!(a.metrics.local_complexity, 0.0);
    assert_eq!(a.metrics.dependent_complexity, 24.0);
    assert_eq!(a.metrics.direct_dependents, 12);
    assert_eq!(a.metrics.transitive_dependents, 12);
    assert_eq!(a.score, 53.0);
    assert_eq!(a.recommendation, RefactorRecommendation::StabilizeBoundary);
    assert_eq!(a.risk, RefactorRisk::High);
    assert_eq!(
        a.evidence,
        vec![
            "high_direct_dependents",
            "high_transitive_dependents",
            "small_foundational_high_fanout",
            "certificate_metadata_unavailable",
            "theorem_index_missing"
        ]
    );
    assert_eq!(a.suggested_unit, "Fixture.A");
    assert_eq!(a.suggested_verification, high_risk_verification());
}

#[test]
fn package_refactor_plan_large_multi_family_module_recommends_split() {
    let package = MetadataFixture::new("module-split", true);
    rewrite_theorem_index(&package, |index| {
        let template = index.entries[0].clone();
        index.entries = (0..13)
            .map(|index| {
                custom_theorem_entry(
                    &template,
                    "Proofs.Ai.Basic",
                    &format!("foo_{index:02}"),
                    PackageTheoremIndexKind::Theorem,
                    PackageArtifactOrigin::Local,
                    Some(("Std.Logic.Eq", "Eq")),
                    &[("Std.Logic.Eq", "Eq")],
                )
            })
            .chain((0..12).map(|index| {
                custom_theorem_entry(
                    &template,
                    "Proofs.Ai.Basic",
                    &format!("bar_{index:02}"),
                    PackageTheoremIndexKind::Theorem,
                    PackageArtifactOrigin::Local,
                    Some(("Std.Logic.Eq", "Eq")),
                    &[("Std.Logic.Eq", "Eq")],
                )
            }))
            .collect();
    });

    let loaded =
        load_refactor_plan_metadata(&options(package.path(), Some("Proofs.Ai.Basic"))).unwrap();
    let basic = module_candidate(&loaded.report.candidates, "Proofs.Ai.Basic")
        .expect("expected Basic module candidate");

    assert_eq!(basic.metrics.theorem_count, Some(25));
    assert_eq!(basic.metrics.public_export_count, Some(25));
    assert_eq!(basic.metrics.family_cluster_count, 2);
    assert_eq!(basic.metrics.local_complexity, 50.0);
    assert_eq!(basic.score, 54.0);
    assert_eq!(basic.recommendation, RefactorRecommendation::ModuleSplit);
    assert_eq!(basic.risk, RefactorRisk::Medium);
    assert_eq!(
        basic.evidence,
        vec![
            "large_public_export_count",
            "multiple_theorem_family_clusters",
            "certificate_metadata_unavailable"
        ]
    );
    assert_eq!(basic.suggested_unit, "Proofs.Ai.Basic::foo_*");
    assert_eq!(basic.suggested_verification, low_risk_verification());
    assert!(!basic.suggested_unit.contains(';'));
    assert!(!basic.suggested_unit.contains('|'));
}

#[test]
fn package_refactor_plan_certificate_size_uses_metadata_only() {
    let package = MetadataFixture::new("certificate-metadata", false);
    let cert_path = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    fs::create_dir_all(cert_path.parent().unwrap()).unwrap();
    fs::write(&cert_path, vec![b'!'; 131_072]).unwrap();

    let loaded =
        load_refactor_plan_metadata(&options(package.path(), Some("Proofs.Ai.Basic"))).unwrap();

    assert_eq!(loaded.report.candidates.len(), 1);
    let basic = module_candidate(&loaded.report.candidates, "Proofs.Ai.Basic")
        .expect("expected Basic module candidate");
    assert_eq!(basic.metrics.certificate_size_bytes, Some(131_072));
    assert_eq!(basic.metrics.certificate_size_weight, 2.0);
    assert_eq!(basic.metrics.local_complexity, 2.0);
    assert_eq!(basic.evidence, vec!["theorem_index_missing"]);
}

#[test]
fn package_refactor_plan_reverse_closure_uses_shortest_distance() {
    let package = MetadataFixture::new("diamond", false);
    let lock = parse_package_lock_json(&diamond_lock_json()).unwrap();
    let graph = build_refactor_plan_module_graph(&lock).unwrap();
    let candidates = build_refactor_plan_module_candidates(
        package.path(),
        &lock,
        &graph,
        &options(package.path(), None),
    );

    assert_eq!(
        reverse_dependents(&graph, "Fixture.A"),
        vec![
            ("Fixture.B".to_owned(), 1),
            ("Fixture.C".to_owned(), 1),
            ("Fixture.D".to_owned(), 2)
        ]
    );
    let a = module_candidate(&candidates, "Fixture.A").expect("expected Fixture.A candidate");
    assert_eq!(a.metrics.direct_dependents, 2);
    assert_eq!(a.metrics.transitive_dependents, 3);
    assert_eq!(a.metrics.dependent_complexity, 5.0);
    assert!(module_candidate(&candidates, "External.Base").is_none());
}

#[test]
fn package_refactor_plan_invalid_theorem_index_uses_refactor_reason() {
    let package = MetadataFixture::new("invalid-index", true);
    let index_path = package.artifact_path(PACKAGE_THEOREM_INDEX_PATH);
    let mut index_source = fs::read_to_string(&index_path).unwrap();
    index_source.push('\n');
    fs::write(index_path, index_source).unwrap();

    let result = load_refactor_plan_metadata(&options(package.path(), None)).unwrap_err();

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.command, "package refactor-plan");
    assert_eq!(result.root, "<absolute-root>");
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::TheoremIndex);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "refactor_plan_theorem_index_invalid"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some(PACKAGE_THEOREM_INDEX_PATH)
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("non_canonical_order")
    );
}

#[test]
fn package_refactor_plan_distinguishes_unknown_and_external_requested_modules() {
    let package = MetadataFixture::new("module-filter", false);

    let local =
        load_refactor_plan_metadata(&options(package.path(), Some("Proofs.Ai.Basic"))).unwrap();
    assert_eq!(
        local.report.theorem_index_status,
        TheoremIndexStatus::Missing
    );
    assert!(local.theorem_index.is_none());

    let unknown = load_refactor_plan_metadata(&options(package.path(), Some("Proofs.Ai.Missing")))
        .unwrap_err();
    assert_eq!(unknown.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(unknown.diagnostics.len(), 1);
    assert_eq!(unknown.diagnostics[0].kind, DiagnosticKind::PackageLock);
    assert_eq!(
        unknown.diagnostics[0].reason_code,
        "refactor_plan_module_unknown"
    );
    assert_eq!(
        unknown.diagnostics[0].module.as_deref(),
        Some("Proofs.Ai.Missing")
    );

    let external =
        load_refactor_plan_metadata(&options(package.path(), Some("Std.Logic.Eq"))).unwrap_err();
    assert_eq!(external.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(external.diagnostics.len(), 1);
    assert_eq!(external.diagnostics[0].kind, DiagnosticKind::PackageLock);
    assert_eq!(
        external.diagnostics[0].reason_code,
        "refactor_plan_module_not_local"
    );
    assert_eq!(
        external.diagnostics[0].module.as_deref(),
        Some("Std.Logic.Eq")
    );
}

#[test]
fn package_refactor_plan_public_command_emits_source_free_diagnostics_and_json() {
    let package = MetadataFixture::new("public-default", false);
    let result = run_package_command(PackageCommand::RefactorPlan(options(package.path(), None)));

    assert_eq!(result.command, "package refactor-plan");
    assert_eq!(result.root, "<absolute-root>");
    assert_eq!(result.status, CommandStatus::Passed);
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.artifacts.is_empty());
    assert_eq!(result.diagnostics.len(), 7);

    let summary = &result.diagnostics[0];
    assert_eq!(summary.kind, DiagnosticKind::GeneratedArtifact);
    assert_eq!(summary.reason_code, "refactor_plan_summary");
    assert_eq!(summary.severity, DiagnosticSeverity::Info);
    assert_eq!(summary.field.as_deref(), Some("refactor_plan"));
    assert_eq!(summary.module, None);
    assert_eq!(
        summary.actual_value.as_deref(),
        Some(
            "schema=npa.cli.package.refactor_plan.v0.1;scope=modules;theorem_index_status=missing;candidate_count=6;module_candidate_count=6;theorem_family_candidate_count=0;warnings=none;proof_evidence=false"
        )
    );

    let first_candidate = &result.diagnostics[1];
    assert_eq!(first_candidate.kind, DiagnosticKind::GeneratedArtifact);
    assert_eq!(
        first_candidate.reason_code,
        "refactor_plan_module_candidate"
    );
    assert_eq!(first_candidate.severity, DiagnosticSeverity::Info);
    assert_eq!(
        first_candidate.module.as_deref(),
        Some("Proofs.Ai.EqReasoning")
    );
    assert_eq!(first_candidate.field.as_deref(), Some("refactor_plan"));
    assert_eq!(
        first_candidate.actual_value.as_deref(),
        Some(
            "kind=module;module=Proofs.Ai.EqReasoning;score=30.0;recommendation=no-action;risk=low;local_complexity=2.0;dependent_complexity=14.0;direct_dependents=3;transitive_dependents=3;direct_import_count=1;theorem_count=null;axiom_count=null;public_export_count=null;certificate_size_bytes=null;certificate_size_weight=0.0;family_cluster_count=0;evidence=certificate_metadata_unavailable,theorem_index_missing;suggested_unit=Proofs.Ai.EqReasoning;suggested_verification=npa package verify-certs --root <root> --changed --checker reference --json;proof_evidence=false"
        )
    );

    let json = result.render_json();
    assert!(json.starts_with(&format!(
        r#"{{"schema":"{PACKAGE_COMMAND_RESULT_SCHEMA}","command":"package refactor-plan""#
    )));
    assert!(json.contains(r#","artifacts":[]}"#));
    assert!(json.contains("proof_evidence=false"));
    assert!(!json.contains(&package.path().display().to_string()));
    assert!(
        json.find("module=Proofs.Ai.EqReasoning").unwrap()
            < json.find("module=Proofs.Ai.Algebra.AbstractGroup").unwrap()
    );
    assert!(
        json.find("module=Proofs.Ai.Algebra.AbstractGroup").unwrap()
            < json
                .find("module=Proofs.Ai.Algebra.AbstractGroupImage")
                .unwrap()
    );
}

#[test]
fn package_refactor_plan_public_command_outputs_filtered_both_scope_candidates() {
    let package = MetadataFixture::new("public-both", true);
    let result = run_package_command(PackageCommand::RefactorPlan(options_with_scope_top(
        package.path(),
        PackageRefactorPlanScope::Both,
        Some("Proofs.Ai.EqReasoning"),
        2,
    )));

    assert_eq!(result.status, CommandStatus::Passed);
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result.artifacts.is_empty());
    assert_eq!(result.diagnostics.len(), 3);
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some(
            "schema=npa.cli.package.refactor_plan.v0.1;scope=both;theorem_index_status=loaded;candidate_count=2;module_candidate_count=1;theorem_family_candidate_count=1;warnings=none;proof_evidence=false"
        )
    );

    assert_eq!(
        result.diagnostics[1].reason_code,
        "refactor_plan_module_candidate"
    );
    assert_eq!(
        result.diagnostics[1].module.as_deref(),
        Some("Proofs.Ai.EqReasoning")
    );
    assert_eq!(
        result.diagnostics[1].actual_value.as_deref(),
        Some(
            "kind=module;module=Proofs.Ai.EqReasoning;score=226.0;recommendation=local-cleanup;risk=low;local_complexity=24.0;dependent_complexity=100.0;direct_dependents=3;transitive_dependents=3;direct_import_count=1;theorem_count=11;axiom_count=0;public_export_count=11;certificate_size_bytes=null;certificate_size_weight=0.0;family_cluster_count=1;evidence=certificate_metadata_unavailable;suggested_unit=Proofs.Ai.EqReasoning::eq_*;suggested_verification=npa package verify-certs --root <root> --changed --checker reference --json;proof_evidence=false"
        )
    );

    assert_eq!(
        result.diagnostics[2].reason_code,
        "refactor_plan_theorem_family_candidate"
    );
    assert_eq!(
        result.diagnostics[2].module.as_deref(),
        Some("Proofs.Ai.EqReasoning")
    );
    assert_eq!(
        result.diagnostics[2].actual_value.as_deref(),
        Some(
            "kind=theorem-family;module=Proofs.Ai.EqReasoning;family=Proofs.Ai.EqReasoning::eq_*;score=124.0;recommendation=theorem-family-group;risk=medium;theorem_count=11;axiom_count=0;shared_prefix_length=2;statement_head_count=1;statement_constant_count=1;module_dependent_complexity=100.0;evidence=large_theorem_family,shared_name_prefix,statement_constant_signal;suggested_unit=Proofs.Ai.EqReasoning::eq_*;suggested_verification=npa package verify-certs --root <root> --changed --checker reference --json;proof_evidence=false"
        )
    );

    let json = result.render_json();
    assert!(!json.contains(&package.path().display().to_string()));
    assert!(json.contains(r#""schema":"npa.package.command_result.v0.1""#));
    assert!(json.contains(r#""artifacts":[]}"#));
}

#[test]
fn package_refactor_plan_stable_strings_are_lower_case() {
    assert_eq!(TheoremIndexStatus::Loaded.as_str(), "loaded");
    assert_eq!(RefactorRecommendation::ModuleSplit.as_str(), "module-split");
    assert_eq!(
        RefactorRecommendation::ExtractFoundation.as_str(),
        "extract-foundation"
    );
    assert_eq!(
        RefactorRecommendation::TheoremFamilyGroup.as_str(),
        "theorem-family-group"
    );
    assert_eq!(
        RefactorRecommendation::DependencyHygiene.as_str(),
        "dependency-hygiene"
    );
    assert_eq!(
        RefactorRecommendation::StabilizeBoundary.as_str(),
        "stabilize-boundary"
    );
    assert_eq!(
        RefactorRecommendation::LocalCleanup.as_str(),
        "local-cleanup"
    );
    assert_eq!(RefactorRecommendation::NoAction.as_str(), "no-action");
    assert_eq!(RefactorRisk::Low.as_str(), "low");
    assert_eq!(RefactorRisk::Medium.as_str(), "medium");
    assert_eq!(RefactorRisk::High.as_str(), "high");
}

fn options(root: &Path, module: Option<&str>) -> PackageRefactorPlanOptions {
    options_with_scope(root, PackageRefactorPlanScope::Modules, module)
}

fn options_with_scope(
    root: &Path,
    scope: PackageRefactorPlanScope,
    module: Option<&str>,
) -> PackageRefactorPlanOptions {
    options_with_scope_top(root, scope, module, 20)
}

fn options_with_scope_top(
    root: &Path,
    scope: PackageRefactorPlanScope,
    module: Option<&str>,
    top: usize,
) -> PackageRefactorPlanOptions {
    PackageRefactorPlanOptions {
        common: PackageCommonOptions {
            root: root.to_path_buf(),
            json: true,
        },
        scope,
        module: module.map(name),
        top,
        include_source_metrics: false,
    }
}

fn module_candidate<'a>(
    candidates: &'a [RefactorCandidate],
    module: &str,
) -> Option<&'a ModuleRefactorCandidate> {
    candidates.iter().find_map(|candidate| match candidate {
        RefactorCandidate::Module(candidate) if candidate.module == name(module) => Some(candidate),
        _ => None,
    })
}

fn theorem_family_candidate<'a>(
    candidates: &'a [RefactorCandidate],
    module: &str,
    family: &str,
) -> Option<&'a TheoremFamilyRefactorCandidate> {
    candidates.iter().find_map(|candidate| match candidate {
        RefactorCandidate::TheoremFamily(candidate)
            if candidate.module == name(module) && candidate.family == family =>
        {
            Some(candidate)
        }
        _ => None,
    })
}

fn reverse_dependents(graph: &RefactorPlanModuleGraph, module: &str) -> Vec<(String, usize)> {
    graph
        .reverse_transitive
        .get(&name(module))
        .into_iter()
        .flatten()
        .map(|dependent| (dependent.module.as_dotted(), dependent.distance))
        .collect()
}

fn name(value: &str) -> Name {
    Name::from_dotted(value)
}

fn rewrite_theorem_index(package: &MetadataFixture, edit: impl FnOnce(&mut PackageTheoremIndex)) {
    let index_path = package.artifact_path(PACKAGE_THEOREM_INDEX_PATH);
    let mut index =
        parse_package_theorem_index_json(&fs::read_to_string(&index_path).unwrap()).unwrap();
    edit(&mut index);
    index.summary = package_theorem_index_summary(&index.entries);
    let index = index.with_computed_hash().unwrap();
    fs::write(index_path, index.canonical_json().unwrap()).unwrap();
}

fn custom_theorem_entry(
    template: &PackageTheoremIndexEntry,
    module: &str,
    theorem: &str,
    kind: PackageTheoremIndexKind,
    origin: PackageArtifactOrigin,
    head: Option<(&str, &str)>,
    constants: &[(&str, &str)],
) -> PackageTheoremIndexEntry {
    let mut entry = template.clone();
    entry.global_ref.module = name(module);
    entry.global_ref.name = name(theorem);
    entry.kind = kind;
    entry.artifact.origin = origin;
    let reference_template = entry
        .statement
        .head
        .clone()
        .or_else(|| entry.statement.constants.first().cloned())
        .expect("fixture theorem entry has statement references");
    entry.statement.head =
        head.map(|(module, name)| statement_ref(&reference_template, module, name));
    entry.statement.constants = constants
        .iter()
        .map(|(module, name)| statement_ref(&reference_template, module, name))
        .collect();
    entry
}

fn statement_ref(
    template: &PackageGlobalRefView,
    module: &str,
    name_value: &str,
) -> PackageGlobalRefView {
    let mut reference = template.clone();
    reference.module = name(module);
    reference.name = name(name_value);
    reference
}

fn low_risk_verification() -> Vec<String> {
    vec!["npa package verify-certs --root <root> --changed --checker reference --json".to_owned()]
}

fn high_risk_verification() -> Vec<String> {
    vec![
        "npa package verify-certs --root <root> --changed --checker reference --json".to_owned(),
        "npa package index --root <root> --check --json".to_owned(),
        "npa package export-summary --root <root> --check --json".to_owned(),
    ]
}

fn diamond_lock_json() -> String {
    const HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
    let entry = |module: &str, origin: &str, certificate: &str, imports: &[&str]| {
        let package_fields = if origin == "external" {
            r#","package":"fixture-ext","version":"0.1.0""#
        } else {
            ""
        };
        let imports = imports
            .iter()
            .map(|import| {
                format!(
                    r#"{{"module":"{import}","export_hash":"{HASH}","certificate_hash":"{HASH}"}}"#
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            r#"{{"module":"{module}","origin":"{origin}"{package_fields},"certificate":"{certificate}","certificate_file_hash":"{HASH}","export_hash":"{HASH}","axiom_report_hash":"{HASH}","certificate_hash":"{HASH}","imports":[{imports}]}}"#
        )
    };
    let entries = [
        entry("External.Base", "external", "vendor/base.npcert", &[]),
        entry(
            "Fixture.A",
            "local",
            "Fixture/A/certificate.npcert",
            &["External.Base"],
        ),
        entry(
            "Fixture.B",
            "local",
            "Fixture/B/certificate.npcert",
            &["Fixture.A"],
        ),
        entry(
            "Fixture.C",
            "local",
            "Fixture/C/certificate.npcert",
            &["Fixture.A"],
        ),
        entry(
            "Fixture.D",
            "local",
            "Fixture/D/certificate.npcert",
            &["Fixture.B"],
        ),
    ]
    .join(",");
    format!(
        r#"{{"schema":"npa.package.lock.v0.1","package":"fixture-refactor","version":"0.1.0","manifest":{{"path":"npa-package.toml","file_hash":"{HASH}"}},"entries":[{entries}]}}"#
    )
}

fn high_fanout_lock_json(dependent_count: usize) -> String {
    const HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
    let entry = |module: &str, certificate: &str, imports: &[String]| {
        let imports = imports
            .iter()
            .map(|import| {
                format!(
                    r#"{{"module":"{import}","export_hash":"{HASH}","certificate_hash":"{HASH}"}}"#
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            r#"{{"module":"{module}","origin":"local","certificate":"{certificate}","certificate_file_hash":"{HASH}","export_hash":"{HASH}","axiom_report_hash":"{HASH}","certificate_hash":"{HASH}","imports":[{imports}]}}"#
        )
    };
    let mut entries = vec![entry("Fixture.A", "Fixture/A/certificate.npcert", &[])];
    for index in 0..dependent_count {
        let module = format!("Fixture.Dep{index:02}");
        let certificate = format!("Fixture/Dep{index:02}/certificate.npcert");
        entries.push(entry(&module, &certificate, &[String::from("Fixture.A")]));
    }
    format!(
        r#"{{"schema":"npa.package.lock.v0.1","package":"fixture-refactor","version":"0.1.0","manifest":{{"path":"npa-package.toml","file_hash":"{HASH}"}},"entries":[{}]}}"#,
        entries.join(",")
    )
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}
