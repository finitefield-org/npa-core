use std::path::PathBuf;

use npa_api::PerformanceDeclarationMeasurement;
use npa_cert::Name;
use npa_cli::args::{
    KernelFuelReportMode, PackageAuditCacheMode, PackageBuildCheckCacheMode, PackageBuildSelection,
    PackageChecker, PackageLockInputMode, PackageSourceStructureSelection, PackageTimingMode,
    PackageVerifierMemoMode,
};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package_api::v1::{
    audit_artifact_ledger_all, audit_artifact_ledger_modules, build_certs_check, build_certs_write,
    check_source_structure_all, check_source_structure_modules, check_source_structure_paths,
    common_options, external_checker_options, refresh_artifacts_check, refresh_artifacts_write,
    theorem_premise_report, verify_certs_base, verify_certs_full, verify_certs_modules,
    verify_changed_certificates,
};
use npa_cli::package_build::run_package_build_certs;
use npa_cli::package_verify::run_package_verify_certs;
use npa_kernel::KernelWorkCounters;

#[test]
fn v0_9_public_break_shapes_are_complete_and_current() {
    assert_eq!(env!("CARGO_PKG_VERSION"), "0.9.0");

    let counters = KernelWorkCounters {
        fuel: Default::default(),
        ..KernelWorkCounters::default()
    };
    assert_eq!(counters.fuel, Default::default());

    let compile_options = npa_frontend::HumanCompileOptions {
        kernel_fuel_report: npa_frontend::HumanKernelFuelReportMode::Detailed,
        ..npa_frontend::HumanCompileOptions::default()
    };
    assert_eq!(
        compile_options.kernel_fuel_report,
        npa_frontend::HumanKernelFuelReportMode::Detailed
    );

    let declaration = PerformanceDeclarationMeasurement {
        module: "Fixture.Module".to_owned(),
        declaration_index: 0,
        declaration: "Fixture.Module.theorem".to_owned(),
        term_nodes: 1,
        elaboration_elapsed_ns: 2,
        kernel: None,
    };
    assert!(declaration.kernel.is_none());
}

#[test]
fn package_build_certs_selection_builders_replace_full_selection() {
    let modules = vec![Name::from_dotted("Proofs.A"), Name::from_dotted("Proofs.B")];
    let request = build_certs_check(common_options("proofs", false)).with_modules(modules.clone());
    assert_eq!(request.selection, PackageBuildSelection::Modules(modules));
    assert_eq!(
        refresh_artifacts_write(common_options("proofs", false))
            .with_changed()
            .selection,
        PackageBuildSelection::Changed
    );
    assert_eq!(
        build_certs_write(common_options("proofs", false)).selection,
        PackageBuildSelection::Full
    );
}

#[test]
fn package_api_v1_common_and_external_options_preserve_inputs() {
    let common = common_options("proofs", true);
    assert_eq!(common.root, PathBuf::from("proofs"));
    assert!(common.json);

    let external = external_checker_options(
        "ci/runner.release.json",
        "sha256:runner-policy",
        "ci/checker-binaries.json",
    );
    assert_eq!(
        external.runner_policy,
        PathBuf::from("ci/runner.release.json")
    );
    assert_eq!(external.runner_policy_hash, "sha256:runner-policy");
    assert_eq!(
        external.checker_registry,
        PathBuf::from("ci/checker-binaries.json")
    );
}

#[test]
fn package_api_v1_artifact_ledger_constructors_preserve_selection() {
    let all = audit_artifact_ledger_all(common_options("proofs", true));
    assert_eq!(all.common.root, PathBuf::from("proofs"));
    assert!(all.modules.is_empty());

    let modules = vec![npa_cert::Name::from_dotted("Example.Module")];
    let selected = audit_artifact_ledger_modules(common_options("proofs", false), modules.clone());
    assert_eq!(selected.modules, modules);
}

#[test]
fn package_api_v1_source_structure_constructors_preserve_closed_selection() {
    let all = check_source_structure_all(common_options("all", true));
    assert_eq!(all.selection, PackageSourceStructureSelection::All);

    let names = vec![Name::from_dotted("Proofs.Example")];
    let modules = check_source_structure_modules(common_options("modules", false), names.clone());
    assert_eq!(
        modules.selection,
        PackageSourceStructureSelection::Modules(names)
    );

    let paths = vec![npa_package::PackagePath::new("Proofs/Example/source.npa")];
    let direct = check_source_structure_paths(common_options("paths", false), paths.clone());
    assert_eq!(
        direct.selection,
        PackageSourceStructureSelection::Paths(paths)
    );
}

#[test]
fn package_api_v1_theorem_premise_report_constructor_preserves_modes() {
    let request = theorem_premise_report(common_options("proofs", true), true)
        .with_timings(PackageTimingMode::Summary);
    assert_eq!(request.common.root, PathBuf::from("proofs"));
    assert!(request.common.json);
    assert!(request.check);
    assert_eq!(request.timings, PackageTimingMode::Summary);
}

#[test]
fn package_api_v1_verification_constructors_preserve_semantic_defaults() {
    for (options, expected_changed, expected_checker) in [
        (
            verify_certs_full(common_options("full", true), PackageChecker::Reference),
            false,
            PackageChecker::Reference,
        ),
        (
            verify_changed_certificates(common_options("changed", false), PackageChecker::Fast),
            true,
            PackageChecker::Fast,
        ),
    ] {
        assert_eq!(options.checker, expected_checker);
        assert_eq!(options.changed, expected_changed);
        assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
        assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);
        assert_eq!(options.jobs, 1);
        assert_eq!(options.external, None);
        assert_eq!(options.timings, PackageTimingMode::Off);
        assert_eq!(options.package_lock_mode, PackageLockInputMode::CheckedFile);
    }
}

#[test]
fn package_api_v1_verification_selector_constructors_and_builders_are_closed() {
    let names = vec![Name::from_dotted("Proofs.A"), Name::from_dotted("Proofs.B")];
    let modules = verify_certs_modules(
        common_options("modules", true),
        PackageChecker::Reference,
        names.clone(),
    );
    assert!(!modules.changed);
    assert_eq!(modules.modules, names);
    assert_eq!(modules.base, None);

    let base = verify_certs_base(
        common_options("base", false),
        PackageChecker::Fast,
        "origin/main",
    );
    assert!(!base.changed);
    assert!(base.modules.is_empty());
    assert_eq!(base.base.as_deref(), Some("origin/main"));

    let replaced =
        verify_changed_certificates(common_options("replace", false), PackageChecker::Reference)
            .with_modules(vec![Name::from_dotted("Proofs.C")])
            .with_base("HEAD^");
    assert!(!replaced.changed);
    assert!(replaced.modules.is_empty());
    assert_eq!(replaced.base.as_deref(), Some("HEAD^"));

    let replaced = replaced.with_modules(vec![Name::from_dotted("Proofs.D")]);
    assert!(!replaced.changed);
    assert_eq!(replaced.modules, vec![Name::from_dotted("Proofs.D")]);
    assert_eq!(replaced.base, None);
}

#[test]
fn package_api_v1_verification_selector_validation_precedes_package_io() {
    let missing_root = std::env::temp_dir().join(format!(
        "npa-cli-verify-selector-validation-missing-{}",
        std::process::id()
    ));
    let common = || common_options(&missing_root, true);
    let cases = [
        (
            "empty modules",
            verify_certs_modules(common(), PackageChecker::Reference, Vec::new()),
            "verify_module_selection_empty",
            "--module",
        ),
        (
            "duplicate modules",
            verify_certs_modules(
                common(),
                PackageChecker::Reference,
                vec![Name::from_dotted("Proofs.A"), Name::from_dotted("Proofs.A")],
            ),
            "verify_module_duplicate",
            "--module",
        ),
        (
            "module cache",
            verify_certs_modules(
                common(),
                PackageChecker::Reference,
                vec![Name::from_dotted("Proofs.A")],
            )
            .with_audit_cache(PackageAuditCacheMode::ReadThrough),
            "unsupported_flag",
            "--audit-cache",
        ),
        (
            "base reconstructed",
            verify_certs_base(common(), PackageChecker::Reference, "HEAD^")
                .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory),
            "unsupported_flag",
            "--package-lock",
        ),
        (
            "base memo",
            verify_certs_base(common(), PackageChecker::Reference, "HEAD^")
                .with_verifier_memo(PackageVerifierMemoMode::Disk),
            "unsupported_flag",
            "--verifier-memo",
        ),
    ];

    for (label, options, reason, field) in cases {
        let result = run_package_verify_certs(options);
        assert_eq!(
            result.exit_code(),
            CommandExitCode::UsageOrInternal,
            "{label}"
        );
        assert_eq!(result.diagnostics[0].reason_code, reason, "{label}");
        assert_eq!(
            result.diagnostics[0].field.as_deref(),
            Some(field),
            "{label}"
        );
    }
    assert!(!missing_root.exists());
}

#[test]
fn package_api_v1_build_constructors_encode_check_write_and_refresh_modes() {
    for (options, expected_check, expected_refresh) in [
        (
            build_certs_check(common_options("check", true)),
            true,
            false,
        ),
        (
            build_certs_write(common_options("write", true)),
            false,
            false,
        ),
        (
            refresh_artifacts_check(common_options("refresh-check", true)),
            true,
            true,
        ),
        (
            refresh_artifacts_write(common_options("refresh-write", true)),
            false,
            true,
        ),
    ] {
        assert_eq!(options.check, expected_check);
        assert_eq!(options.update_manifest_hashes, expected_refresh);
        assert_eq!(options.build_check_cache, PackageBuildCheckCacheMode::Off);
        assert_eq!(options.build_check_cache_root, None);
        assert_eq!(options.kernel_fuel_report, KernelFuelReportMode::Failure);
        assert_eq!(options.timings, PackageTimingMode::Off);
    }
}

#[test]
fn package_api_v1_verification_builders_are_pure_setters() {
    let base = verify_certs_full(common_options("proofs", true), PackageChecker::Reference);

    let mut expected = base.clone();
    expected.audit_cache = PackageAuditCacheMode::ReadThrough;
    assert_eq!(
        base.clone()
            .with_audit_cache(PackageAuditCacheMode::ReadThrough),
        expected
    );

    let mut expected = base.clone();
    expected.verifier_memo = PackageVerifierMemoMode::Disk;
    assert_eq!(
        base.clone()
            .with_verifier_memo(PackageVerifierMemoMode::Disk),
        expected
    );

    let mut expected = base.clone();
    expected.jobs = 4;
    assert_eq!(base.clone().with_jobs(4), expected);

    let external = external_checker_options(
        "ci/runner.release.json",
        "sha256:runner-policy",
        "ci/checker-binaries.json",
    );
    let mut expected = base.clone();
    expected.external = Some(external.clone());
    assert_eq!(base.clone().with_external(external), expected);

    let mut expected = base.clone();
    expected.timings = PackageTimingMode::Detailed;
    assert_eq!(
        base.clone().with_timings(PackageTimingMode::Detailed),
        expected
    );

    let mut expected = base.clone();
    expected.package_lock_mode = PackageLockInputMode::ReconstructedInMemory;
    assert_eq!(
        base.with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory),
        expected
    );
}

#[test]
fn package_api_v1_build_builder_is_a_pure_setter() {
    let base = build_certs_check(common_options("proofs", true));
    for (mode, spelling, uses_local_store) in [
        (PackageBuildCheckCacheMode::Off, "off", false),
        (
            PackageBuildCheckCacheMode::ReadThrough,
            "read-through",
            true,
        ),
        (PackageBuildCheckCacheMode::LocalHit, "local-hit", true),
    ] {
        let mut expected = base.clone();
        expected.build_check_cache = mode;
        let request = base.clone().with_build_check_cache(mode);
        assert_eq!(request, expected);
        assert_eq!(request.build_check_cache.as_str(), spelling);
        assert_eq!(
            request.build_check_cache.uses_local_store(),
            uses_local_store
        );
    }

    let local_hit = base
        .clone()
        .with_modules(vec![Name::from_dotted("Proofs.A")])
        .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit);
    assert_eq!(
        local_hit.selection,
        PackageBuildSelection::Modules(vec![Name::from_dotted("Proofs.A")])
    );
    assert_eq!(
        local_hit.build_check_cache,
        PackageBuildCheckCacheMode::LocalHit
    );

    let base = build_certs_check(common_options("proofs", true));
    let mut expected = base.clone();
    expected.kernel_fuel_report = KernelFuelReportMode::Detailed;
    assert_eq!(
        base.clone()
            .with_kernel_fuel_report(KernelFuelReportMode::Detailed),
        expected
    );

    let mut expected = base.clone();
    expected.timings = PackageTimingMode::Detailed;
    assert_eq!(base.with_timings(PackageTimingMode::Detailed), expected);
}

#[test]
fn package_api_v1_build_cache_root() {
    let base = build_certs_check(common_options("proofs", true));
    assert_eq!(base.build_check_cache_root, None);

    let root = PathBuf::from("target/isolated-build-check-cache");
    let mut expected = base.clone();
    expected.build_check_cache_root = Some(root.clone());

    assert_eq!(base.with_build_check_cache_root(root), expected);
}

#[test]
fn package_api_v1_build_observation_builders_cover_all_mode_pairs_orthogonally() {
    let base = build_certs_check(common_options("proofs", true));
    let fuel_modes = [
        KernelFuelReportMode::Off,
        KernelFuelReportMode::Failure,
        KernelFuelReportMode::Detailed,
    ];
    let timing_modes = [
        PackageTimingMode::Off,
        PackageTimingMode::Summary,
        PackageTimingMode::Detailed,
    ];

    for fuel in fuel_modes {
        for timings in timing_modes {
            let selected = base
                .clone()
                .with_kernel_fuel_report(fuel)
                .with_timings(timings);
            assert_eq!(selected.kernel_fuel_report, fuel);
            assert_eq!(selected.timings, timings);

            let mut expected = base.clone();
            expected.kernel_fuel_report = fuel;
            expected.timings = timings;
            assert_eq!(selected, expected);
            assert_eq!(
                base.clone()
                    .with_timings(timings)
                    .with_kernel_fuel_report(fuel),
                expected
            );
        }
    }
}

#[test]
fn package_api_v1_mode_strings_and_external_matches_are_forward_compatible() {
    assert_eq!(KernelFuelReportMode::Off.as_str(), "off");
    assert_eq!(KernelFuelReportMode::Failure.as_str(), "failure");
    assert_eq!(KernelFuelReportMode::Detailed.as_str(), "detailed");
    for (cli, human) in [
        (
            KernelFuelReportMode::Off,
            npa_frontend::HumanKernelFuelReportMode::Off,
        ),
        (
            KernelFuelReportMode::Failure,
            npa_frontend::HumanKernelFuelReportMode::Failure,
        ),
        (
            KernelFuelReportMode::Detailed,
            npa_frontend::HumanKernelFuelReportMode::Detailed,
        ),
    ] {
        assert_eq!(npa_frontend::HumanKernelFuelReportMode::from(cli), human);
    }
    assert_eq!(PackageLockInputMode::CheckedFile.as_str(), "checked");
    assert_eq!(
        PackageLockInputMode::ReconstructedInMemory.as_str(),
        "reconstructed"
    );

    let checker = match PackageChecker::Reference {
        PackageChecker::Reference => "reference",
        _ => "future",
    };
    let audit_cache = match PackageAuditCacheMode::Off {
        PackageAuditCacheMode::Off => "off",
        _ => "future",
    };
    let verifier_memo = match PackageVerifierMemoMode::Off {
        PackageVerifierMemoMode::Off => "off",
        _ => "future",
    };
    let timings = match PackageTimingMode::Off {
        PackageTimingMode::Off => "off",
        _ => "future",
    };
    let build_cache = match PackageBuildCheckCacheMode::Off {
        PackageBuildCheckCacheMode::Off => "off",
        _ => "future",
    };
    let package_lock = match PackageLockInputMode::CheckedFile {
        PackageLockInputMode::CheckedFile => "checked",
        _ => "future",
    };

    assert_eq!(
        (
            checker,
            audit_cache,
            verifier_memo,
            timings,
            build_cache,
            package_lock,
        ),
        ("reference", "off", "off", "off", "off", "checked")
    );
}

#[test]
fn package_api_v1_requests_are_accepted_by_public_run_signatures() {
    let missing_root = std::env::temp_dir().join(format!(
        "npa-cli-package-api-v1-missing-{}",
        std::process::id()
    ));
    if missing_root.exists() {
        std::fs::remove_dir_all(&missing_root).unwrap();
    }

    let verify_requests = [
        verify_certs_full(
            common_options(&missing_root, true),
            PackageChecker::Reference,
        ),
        verify_changed_certificates(common_options(&missing_root, true), PackageChecker::Fast),
    ];
    for request in verify_requests {
        assert_ne!(
            run_package_verify_certs(request).exit_code(),
            CommandExitCode::Success
        );
    }

    let build_requests = [
        build_certs_check(common_options(&missing_root, true)),
        build_certs_write(common_options(&missing_root, true)),
        refresh_artifacts_check(common_options(&missing_root, true)),
        refresh_artifacts_write(common_options(&missing_root, true)),
    ];
    for request in build_requests {
        assert_ne!(
            run_package_build_certs(request).exit_code(),
            CommandExitCode::Success
        );
    }
}

#[test]
fn package_api_v1_invalid_verify_requests_fail_before_package_io() {
    let missing_root = std::env::temp_dir().join(format!(
        "npa-cli-package-api-v1-validation-missing-{}",
        std::process::id()
    ));
    if missing_root.exists() {
        std::fs::remove_dir_all(&missing_root).unwrap();
    }
    let common = |label: &str| common_options(missing_root.join(label), true);
    let external = || {
        external_checker_options(
            "ci/runner.release.json",
            "sha256:runner-policy",
            "ci/checker-binaries.json",
        )
    };

    let cases = vec![
        (
            "jobs-zero",
            verify_certs_full(common("jobs-zero"), PackageChecker::Fast).with_jobs(0),
            "invalid_flag_value",
            Some("--jobs"),
            Some("0"),
            None,
        ),
        (
            "changed-external",
            verify_changed_certificates(common("changed-external"), PackageChecker::External)
                .with_external(external()),
            "unsupported_flag",
            Some("--changed"),
            Some("external"),
            None,
        ),
        (
            "changed-audit-cache",
            verify_changed_certificates(common("changed-audit-cache"), PackageChecker::Reference)
                .with_audit_cache(PackageAuditCacheMode::ReadThrough),
            "unsupported_flag",
            Some("--audit-cache"),
            Some("read-through"),
            None,
        ),
        (
            "changed-audit-cache-local-hit",
            verify_changed_certificates(
                common("changed-audit-cache-local-hit"),
                PackageChecker::Reference,
            )
            .with_audit_cache(PackageAuditCacheMode::LocalHit),
            "unsupported_flag",
            Some("--audit-cache"),
            Some("local-hit"),
            None,
        ),
        (
            "changed-verifier-memo",
            verify_changed_certificates(common("changed-verifier-memo"), PackageChecker::Reference)
                .with_verifier_memo(PackageVerifierMemoMode::Disk),
            "unsupported_flag",
            Some("--verifier-memo"),
            Some("disk"),
            None,
        ),
        (
            "changed-verifier-memo-read-through",
            verify_changed_certificates(
                common("changed-verifier-memo-read-through"),
                PackageChecker::Reference,
            )
            .with_verifier_memo(PackageVerifierMemoMode::ReadThrough),
            "unsupported_flag",
            Some("--verifier-memo"),
            Some("read-through"),
            None,
        ),
        (
            "missing-external-options",
            verify_certs_full(common("missing-external-options"), PackageChecker::External),
            "missing_external_checker_options",
            None,
            None,
            Some("npa-checker-ext"),
        ),
        (
            "unexpected-external-options",
            verify_certs_full(
                common("unexpected-external-options"),
                PackageChecker::Reference,
            )
            .with_external(external()),
            "unsupported_flag",
            Some("--runner-policy"),
            None,
            None,
        ),
        (
            "external-parallel-jobs",
            verify_certs_full(common("external-parallel-jobs"), PackageChecker::External)
                .with_jobs(2)
                .with_external(external()),
            "unsupported_flag",
            Some("--jobs"),
            Some("2"),
            None,
        ),
        (
            "external-audit-cache",
            verify_certs_full(common("external-audit-cache"), PackageChecker::External)
                .with_audit_cache(PackageAuditCacheMode::ReadThrough)
                .with_external(external()),
            "unsupported_flag",
            Some("--audit-cache"),
            Some("read-through"),
            None,
        ),
        (
            "external-audit-cache-local-hit",
            verify_certs_full(
                common("external-audit-cache-local-hit"),
                PackageChecker::External,
            )
            .with_audit_cache(PackageAuditCacheMode::LocalHit)
            .with_external(external()),
            "unsupported_flag",
            Some("--audit-cache"),
            Some("local-hit"),
            None,
        ),
        (
            "external-verifier-memo",
            verify_certs_full(common("external-verifier-memo"), PackageChecker::External)
                .with_verifier_memo(PackageVerifierMemoMode::Disk)
                .with_external(external()),
            "unsupported_flag",
            Some("--verifier-memo"),
            Some("disk"),
            None,
        ),
        (
            "external-verifier-memo-read-through",
            verify_certs_full(
                common("external-verifier-memo-read-through"),
                PackageChecker::External,
            )
            .with_verifier_memo(PackageVerifierMemoMode::ReadThrough)
            .with_external(external()),
            "unsupported_flag",
            Some("--verifier-memo"),
            Some("read-through"),
            None,
        ),
        (
            "external-reconstructed-lock",
            verify_certs_full(
                common("external-reconstructed-lock"),
                PackageChecker::External,
            )
            .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory)
            .with_external(external()),
            "unsupported_flag",
            Some("--package-lock"),
            Some("reconstructed;checker=external"),
            None,
        ),
        (
            "audit-cache-parallel-jobs",
            verify_certs_full(common("audit-cache-parallel-jobs"), PackageChecker::Fast)
                .with_audit_cache(PackageAuditCacheMode::ReadThrough)
                .with_jobs(4),
            "unsupported_flag",
            Some("--jobs"),
            Some("jobs=4;audit_cache=read-through"),
            None,
        ),
        (
            "audit-cache-verifier-memo",
            verify_certs_full(
                common("audit-cache-verifier-memo"),
                PackageChecker::Reference,
            )
            .with_audit_cache(PackageAuditCacheMode::ReadThrough)
            .with_verifier_memo(PackageVerifierMemoMode::Disk),
            "unsupported_flag",
            Some("--verifier-memo"),
            Some("disk"),
            None,
        ),
        (
            "precedence-jobs-zero-before-external-changed",
            verify_changed_certificates(
                common("precedence-jobs-zero-before-external-changed"),
                PackageChecker::External,
            )
            .with_jobs(0)
            .with_external(external()),
            "invalid_flag_value",
            Some("--jobs"),
            Some("0"),
            None,
        ),
        (
            "precedence-external-jobs-before-cache",
            verify_certs_full(
                common("precedence-external-jobs-before-cache"),
                PackageChecker::External,
            )
            .with_jobs(2)
            .with_audit_cache(PackageAuditCacheMode::LocalHit)
            .with_external(external()),
            "unsupported_flag",
            Some("--jobs"),
            Some("2"),
            None,
        ),
    ];

    for (label, request, reason, field, actual_value, checker) in cases {
        let result = run_package_verify_certs(request);
        assert_eq!(
            result.exit_code(),
            CommandExitCode::UsageOrInternal,
            "{label}"
        );
        assert_eq!(result.diagnostics.len(), 1, "{label}");
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.kind, DiagnosticKind::Usage, "{label}");
        assert_eq!(diagnostic.reason_code, reason, "{label}");
        assert_eq!(diagnostic.field.as_deref(), field, "{label}");
        assert_eq!(diagnostic.actual_value.as_deref(), actual_value, "{label}");
        assert_eq!(diagnostic.checker.as_deref(), checker, "{label}");
    }
}

#[test]
fn package_api_v1_invalid_build_requests_fail_before_package_io() {
    let missing_root = std::env::temp_dir().join(format!(
        "npa-cli-package-api-v1-build-validation-missing-{}",
        std::process::id()
    ));
    if missing_root.exists() {
        std::fs::remove_dir_all(&missing_root).unwrap();
    }
    let common = |label: &str| common_options(missing_root.join(label), true);
    let cases = [
        (
            "write-cache",
            build_certs_write(common("write-cache"))
                .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough),
        ),
        (
            "refresh-check-cache",
            refresh_artifacts_check(common("refresh-check-cache"))
                .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough),
        ),
        (
            "refresh-write-cache",
            refresh_artifacts_write(common("refresh-write-cache"))
                .with_build_check_cache(PackageBuildCheckCacheMode::ReadThrough),
        ),
    ];

    for (label, request) in cases {
        let result = run_package_build_certs(request);
        assert_eq!(
            result.exit_code(),
            CommandExitCode::UsageOrInternal,
            "{label}"
        );
        assert_eq!(result.diagnostics.len(), 1, "{label}");
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.kind, DiagnosticKind::Usage, "{label}");
        assert_eq!(diagnostic.reason_code, "unsupported_flag", "{label}");
        assert_eq!(
            diagnostic.field.as_deref(),
            Some("--build-check-cache"),
            "{label}"
        );
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some("read-through"),
            "{label}"
        );
    }
}

#[test]
fn package_build_check_cache_mode_api_keeps_selection_validation_projection() {
    let missing_root = std::env::temp_dir().join(format!(
        "npa-cli-local-hit-api-validation-missing-{}",
        std::process::id()
    ));
    let common = || common_options(&missing_root, true);
    let cases = [
        build_certs_check(common()).with_build_check_cache(PackageBuildCheckCacheMode::LocalHit),
        build_certs_write(common())
            .with_modules(vec![npa_cert::Name::from_dotted("Proofs.A")])
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit),
        refresh_artifacts_check(common())
            .with_modules(vec![npa_cert::Name::from_dotted("Proofs.A")])
            .with_build_check_cache(PackageBuildCheckCacheMode::LocalHit),
    ];

    for request in cases {
        let result = run_package_build_certs(request);
        assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
        assert_eq!(result.diagnostics.len(), 1);
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.kind, DiagnosticKind::Usage);
        assert_eq!(diagnostic.reason_code, "package_build_selection_invalid");
        assert_eq!(diagnostic.field.as_deref(), Some("--build-check-cache"));
        assert_eq!(diagnostic.actual_value.as_deref(), Some("local-hit"));
    }
    assert!(!missing_root.exists());
}
