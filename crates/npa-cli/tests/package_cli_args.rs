use std::path::{Path, PathBuf};
use std::process::Command;

use npa_cli::args::{
    parse_cli_args, render_help, CliAction, CliCommand, HelpTopic, PackageAuditCacheMode,
    PackageBuildCheckCacheMode, PackageBuildSelection, PackageChecker, PackageCommand,
    PackageLockCommand, PackageLockInputMode, PackageRefactorPlanScope, PackageTimingMode,
    PackageVerifierMemoMode, UsageReason,
};
use npa_cli::diagnostic::{CommandStatus, DiagnosticKind};
use npa_cli::package::run_package_command;

fn parse(args: &[&str]) -> CliAction {
    parse_cli_args(args.iter().copied()).unwrap()
}

fn parse_error(args: &[&str]) -> npa_cli::args::CliUsageError {
    parse_cli_args(args.iter().copied()).unwrap_err()
}

#[test]
fn package_l2_review_and_aggregate_args_parse_strict_contracts() {
    let action = parse(&[
        "package",
        "prepare-l2-review-input",
        "--root",
        "proofs",
        "--policy",
        "policy.json",
        "--module",
        "Proofs.Ai.Finite",
        "--declaration",
        "finite_intro",
        "--out",
        "l2-reviews/finite.input.json",
        "--check",
        "--json",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::PrepareL2ReviewInput(options))) = action
    else {
        panic!("expected review input command")
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json && options.check);
    assert_eq!(options.module, "Proofs.Ai.Finite");

    let action = parse(&[
        "package",
        "aggregate-l2-acceptance",
        "--root=proofs",
        "--policy=policy.json",
        "--review-input=l2-reviews/finite.input.json",
        "--review",
        "l2-reviews/finite.semantic.json",
        "--review=l2-reviews/finite.adversarial.json",
        "--existing=l2-acceptance.json",
        "--replace=Proofs.Ai.Finite::finite_intro",
        "--out=l2-acceptance.json",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::AggregateL2Acceptance(options))) =
        action
    else {
        panic!("expected aggregate command")
    };
    assert_eq!(options.review_inputs.len(), 1);
    assert_eq!(options.reviews.len(), 2);
    assert_eq!(options.replacements[0].0.as_dotted(), "Proofs.Ai.Finite");
    assert_eq!(options.replacements[0].1.as_dotted(), "finite_intro");

    let duplicate = parse_error(&[
        "package",
        "aggregate-l2-acceptance",
        "--policy=p",
        "--review-input=x",
        "--review=x",
        "--out=o",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
}

#[test]
fn package_l2_transport_args_require_three_roots_and_check_output() {
    let action = parse(&[
        "package",
        "validate-l2-namespace-transport",
        "--source-root",
        "source",
        "--target-baseline-root",
        "baseline",
        "--target-root",
        "target",
        "--acceptance-policy",
        "acceptance-policy.json",
        "--source-acceptance",
        "l2-acceptance.json",
        "--transport-policy",
        "transport-policy.json",
        "--mapping",
        "l2-transports/request.json",
        "--out",
        "l2-transports/attestation.json",
        "--check",
        "--json",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::ValidateL2NamespaceTransport(options))) =
        action
    else {
        panic!("expected transport command")
    };
    assert_eq!(options.common.root, PathBuf::from("source"));
    assert!(options.common.json && options.check);
    assert_eq!(options.target_baseline_root, PathBuf::from("baseline"));

    let missing_out = parse_error(&[
        "package",
        "validate-l2-namespace-transport",
        "--source-root=s",
        "--target-baseline-root=b",
        "--target-root=t",
        "--acceptance-policy=a",
        "--source-acceptance=x",
        "--transport-policy=p",
        "--mapping=m",
        "--check",
    ]);
    assert_eq!(missing_out.flag.as_deref(), Some("--out"));
}

#[test]
fn package_l2_acceptance_args_require_policy_and_record_and_parse_modules() {
    let action = parse(&[
        "package",
        "validate-l2-acceptance",
        "--root",
        "npa-corpus/proofs",
        "--policy",
        "npa-mathlib/policy/l2-acceptance-policy.json",
        "--acceptance=npa-corpus/proofs/l2-acceptance.json",
        "--module",
        "Proofs.Logic.Basic",
        "--module=Proofs.Logic.Basic",
        "--json",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::ValidateL2Acceptance(options))) = action
    else {
        panic!("expected package validate-l2-acceptance command");
    };
    assert_eq!(options.common.root, PathBuf::from("npa-corpus/proofs"));
    assert!(options.common.json);
    assert_eq!(
        options.policy,
        PathBuf::from("npa-mathlib/policy/l2-acceptance-policy.json")
    );
    assert_eq!(
        options.acceptance,
        PathBuf::from("npa-corpus/proofs/l2-acceptance.json")
    );
    assert_eq!(options.modules.len(), 1);

    let missing = parse_error(&[
        "package",
        "validate-l2-acceptance",
        "--policy",
        "policy.json",
    ]);
    assert_eq!(missing.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(missing.flag.as_deref(), Some("--acceptance"));

    let invalid = parse_error(&[
        "package",
        "validate-l2-acceptance",
        "--policy",
        "policy.json",
        "--acceptance",
        "acceptance.json",
        "--module",
        "Proofs..Bad",
    ]);
    assert_eq!(invalid.reason, UsageReason::InvalidModuleName);
}

#[test]
fn package_cli_args_parses_check_defaults_root_to_current_directory() {
    let action = parse(&["package", "check"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::Check(options))) = action else {
        panic!("expected package check command");
    };
    assert_eq!(options.root, PathBuf::from("."));
    assert!(!options.json);
}

#[test]
fn package_cli_args_parses_common_root_and_json_flags() {
    let action = parse(&["package", "check-hashes", "--root", "proofs", "--json"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::CheckHashes(options))) = action else {
        panic!("expected package check-hashes command");
    };
    assert_eq!(options.root, PathBuf::from("proofs"));
    assert!(options.json);
}

#[test]
fn package_lock_cli_args_parse_check_write_root_and_json() {
    let action = parse(&["package", "lock", "check", "--root", "proofs", "--json"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::Lock(PackageLockCommand::Check(
        options,
    )))) = action
    else {
        panic!("expected package lock check command");
    };
    assert_eq!(options.root, PathBuf::from("proofs"));
    assert!(options.json);

    let action = parse(&["package", "lock", "write", "--root=proofs", "--json"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::Lock(PackageLockCommand::Write(
        options,
    )))) = action
    else {
        panic!("expected package lock write command");
    };
    assert_eq!(options.root, PathBuf::from("proofs"));
    assert!(options.json);
}

#[test]
fn package_lock_cli_args_reject_missing_subcommand_and_unknown_flag() {
    let missing = parse_error(&["package", "lock"]);
    assert_eq!(missing.reason, UsageReason::UnknownCommand);
    assert_eq!(missing.command.as_deref(), Some("package lock"));

    let unknown_flag = parse_error(&["package", "lock", "--json"]);
    assert_eq!(unknown_flag.reason, UsageReason::UnknownFlag);
    assert_eq!(unknown_flag.command.as_deref(), Some("package lock"));
    assert_eq!(unknown_flag.flag.as_deref(), Some("--json"));

    let unknown_subcommand = parse_error(&["package", "lock", "repair"]);
    assert_eq!(unknown_subcommand.reason, UsageReason::UnknownCommand);
    assert_eq!(
        unknown_subcommand.command.as_deref(),
        Some("package lock repair")
    );
}

#[test]
fn package_lock_cli_args_common_errors_use_nested_command_name() {
    let duplicate = parse_error(&[
        "package",
        "lock",
        "check",
        "--root",
        "proofs",
        "--root=other",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.command.as_deref(), Some("package lock check"));
    assert_eq!(duplicate.flag.as_deref(), Some("--root"));

    let unknown = parse_error(&["package", "lock", "write", "--bogus"]);
    assert_eq!(unknown.reason, UsageReason::UnknownFlag);
    assert_eq!(unknown.command.as_deref(), Some("package lock write"));
    assert_eq!(unknown.flag.as_deref(), Some("--bogus"));
}

#[test]
fn package_gate_plan_cli_args_parse_base_root_and_json() {
    let action = parse(&[
        "package",
        "gate-plan",
        "--base",
        "origin/main",
        "--root",
        "proofs",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::GatePlan(options))) = action else {
        panic!("expected package gate-plan command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert_eq!(options.base, "origin/main");

    let action = parse(&["package", "gate-plan", "--base=HEAD"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::GatePlan(options))) = action else {
        panic!("expected package gate-plan command");
    };
    assert_eq!(options.base, "HEAD");
}

#[test]
fn package_gate_plan_cli_args_reject_missing_duplicate_and_help() {
    let missing = parse_error(&["package", "gate-plan"]);
    assert_eq!(missing.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(missing.flag.as_deref(), Some("--base"));

    let duplicate = parse_error(&[
        "package",
        "gate-plan",
        "--base",
        "origin/main",
        "--base=HEAD",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--base"));

    let help = parse(&["package", "gate-plan", "--help"]);
    assert_eq!(help, CliAction::Help(HelpTopic::PackageGatePlan));
}

#[test]
fn package_cli_args_refactor_plan_parse_defaults() {
    let action = parse(&["package", "refactor-plan"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::RefactorPlan(options))) = action else {
        panic!("expected package refactor-plan command");
    };
    assert_eq!(options.common.root, PathBuf::from("."));
    assert!(!options.common.json);
    assert_eq!(options.scope, PackageRefactorPlanScope::Modules);
    assert_eq!(options.module, None);
    assert_eq!(options.top, 20);
    assert!(!options.include_source_metrics);
}

#[test]
fn package_cli_args_refactor_plan_parse_scope_module_top_root_and_json() {
    let action = parse(&[
        "package",
        "refactor-plan",
        "--scope",
        "theorems",
        "--module",
        "Proofs.Ai.Basic",
        "--top",
        "1",
        "--root",
        "proofs",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::RefactorPlan(options))) = action else {
        panic!("expected package refactor-plan command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert_eq!(options.scope, PackageRefactorPlanScope::Theorems);
    assert_eq!(
        options.module.as_ref().map(|module| module.as_dotted()),
        Some("Proofs.Ai.Basic".to_owned())
    );
    assert_eq!(options.top, 1);

    let action = parse(&[
        "package",
        "refactor-plan",
        "--scope=both",
        "--module=Mathlib.Logic.Basic",
        "--top=200",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::RefactorPlan(options))) = action else {
        panic!("expected package refactor-plan command");
    };
    assert_eq!(options.scope, PackageRefactorPlanScope::Both);
    assert_eq!(
        options.module.as_ref().map(|module| module.as_dotted()),
        Some("Mathlib.Logic.Basic".to_owned())
    );
    assert_eq!(options.top, 200);
}

#[test]
fn package_cli_args_refactor_plan_reject_invalid_values_and_reserved_source_metrics() {
    let invalid_scope = parse_error(&["package", "refactor-plan", "--scope", "module"]);
    assert_eq!(invalid_scope.reason, UsageReason::InvalidFlagValue);
    assert_eq!(invalid_scope.flag.as_deref(), Some("--scope"));
    assert_eq!(invalid_scope.value.as_deref(), Some("module"));

    let invalid_module = parse_error(&["package", "refactor-plan", "--module", "Proofs..Bad"]);
    assert_eq!(invalid_module.reason, UsageReason::InvalidModuleName);
    assert_eq!(invalid_module.flag.as_deref(), Some("--module"));
    assert_eq!(invalid_module.value.as_deref(), Some("Proofs..Bad"));

    for value in ["0", "201", "abc"] {
        let error = parse_error(&["package", "refactor-plan", "--top", value]);
        assert_eq!(error.reason, UsageReason::InvalidFlagValue, "{value}");
        assert_eq!(error.flag.as_deref(), Some("--top"), "{value}");
        assert_eq!(error.value.as_deref(), Some(value), "{value}");
    }

    let source_metrics = parse_error(&["package", "refactor-plan", "--include-source-metrics"]);
    assert_eq!(source_metrics.reason, UsageReason::UnsupportedFlag);
    assert_eq!(
        source_metrics.flag.as_deref(),
        Some("--include-source-metrics")
    );
    assert_eq!(
        source_metrics.command.as_deref(),
        Some("package refactor-plan")
    );

    let source_metrics_equals =
        parse_error(&["package", "refactor-plan", "--include-source-metrics=true"]);
    assert_eq!(source_metrics_equals.reason, UsageReason::UnsupportedFlag);
    assert_eq!(
        source_metrics_equals.flag.as_deref(),
        Some("--include-source-metrics")
    );
    assert_eq!(
        source_metrics_equals.command.as_deref(),
        Some("package refactor-plan")
    );
}

#[test]
fn package_cli_args_refactor_plan_reject_duplicate_flags_and_help() {
    for (flag, first, second) in [
        ("--scope", "modules", "both"),
        ("--module", "Proofs.Ai.Basic", "Proofs.Ai.Other"),
        ("--top", "1", "2"),
    ] {
        let error = parse_error(&["package", "refactor-plan", flag, first, flag, second]);
        assert_eq!(error.reason, UsageReason::DuplicateFlag, "{flag}");
        assert_eq!(error.flag.as_deref(), Some(flag), "{flag}");
    }

    let help = parse(&["package", "refactor-plan", "--help"]);
    assert_eq!(help, CliAction::Help(HelpTopic::PackageRefactorPlan));

    let rendered = render_help(HelpTopic::PackageRefactorPlan);
    assert!(rendered.contains("not proof evidence"));
    assert!(!rendered.contains("--include-source-metrics"));
}

#[test]
fn package_cli_args_refactor_plan_runtime_reports_missing_manifest() {
    let action = parse(&["package", "refactor-plan", "--root", "missing-package"]);
    let CliAction::Run(CliCommand::Package(command)) = action else {
        panic!("expected package refactor-plan command");
    };

    let result = run_package_command(command);
    assert_eq!(result.command, "package refactor-plan");
    assert_eq!(result.root, "missing-package");
    assert_eq!(result.status, CommandStatus::Failed);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageManifest);
    assert_eq!(result.diagnostics[0].reason_code, "manifest_missing");
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("npa-package.toml")
    );
}

#[test]
fn package_generated_check_command_cli_args_parse_root_json_and_timings() {
    let action = parse(&[
        "package",
        "check-generated",
        "--root",
        "proofs",
        "--json",
        "--timings=summary",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::CheckGenerated(options))) = action
    else {
        panic!("expected package check-generated command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert_eq!(options.timings, PackageTimingMode::Summary);

    let help = parse(&["package", "check-generated", "--help"]);
    assert_eq!(help, CliAction::Help(HelpTopic::PackageCheckGenerated));
}

#[test]
fn package_theorem_premise_report_cli_args_and_help_are_stable() {
    let action = parse(&[
        "package",
        "theorem-premise-report",
        "--root",
        "proofs",
        "--check",
        "--json",
        "--timings=detailed",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::TheoremPremiseReport(options))) = action
    else {
        panic!("expected package theorem-premise-report command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(options.timings, PackageTimingMode::Detailed);

    let help = parse(&["package", "theorem-premise-report", "--help"]);
    assert_eq!(
        help,
        CliAction::Help(HelpTopic::PackageTheoremPremiseReport)
    );
    assert!(render_help(HelpTopic::PackageTheoremPremiseReport)
        .contains("generated/theorem-premise-report.json"));
}

#[test]
fn package_generated_check_command_cli_args_reject_duplicate_timings() {
    let duplicate = parse_error(&[
        "package",
        "check-generated",
        "--timings",
        "summary",
        "--timings=detailed",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--timings"));
    assert_eq!(
        duplicate.command.as_deref(),
        Some("package check-generated")
    );
}

#[test]
fn package_cli_args_parses_build_certs_check_mode() {
    let action = parse(&[
        "package",
        "build-certs",
        "--root=proofs",
        "--check",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(options.build_check_cache, PackageBuildCheckCacheMode::Off);
    assert!(!options.update_manifest_hashes);
}

#[test]
fn package_cli_args_parses_build_certs_build_check_cache_read_through() {
    let action = parse(&[
        "package",
        "build-certs",
        "--root=proofs",
        "--check",
        "--build-check-cache",
        "read-through",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.check);
    assert_eq!(
        options.build_check_cache,
        PackageBuildCheckCacheMode::ReadThrough
    );
    assert!(!options.update_manifest_hashes);

    let action = parse(&[
        "package",
        "build-certs",
        "--check",
        "--build-check-cache=off",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert_eq!(options.build_check_cache, PackageBuildCheckCacheMode::Off);
    assert!(!options.update_manifest_hashes);
}

#[test]
fn package_cli_args_parses_build_certs_update_manifest_hashes() {
    let action = parse(&[
        "package",
        "build-certs",
        "--root=proofs",
        "--json",
        "--update-manifest-hashes",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(!options.check);
    assert_eq!(options.build_check_cache, PackageBuildCheckCacheMode::Off);
    assert!(options.update_manifest_hashes);

    let action = parse(&[
        "package",
        "build-certs",
        "--check",
        "--update-manifest-hashes",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert!(options.check);
    assert_eq!(options.build_check_cache, PackageBuildCheckCacheMode::Off);
    assert!(options.update_manifest_hashes);
}

#[test]
fn package_build_certs_selection_parses_modules_and_changed() {
    let action = parse(&[
        "package",
        "build-certs",
        "--check",
        "--module",
        "Proofs.A",
        "--module=Proofs.B",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert_eq!(
        options.selection,
        PackageBuildSelection::Modules(vec![
            npa_cert::Name::from_dotted("Proofs.A"),
            npa_cert::Name::from_dotted("Proofs.B"),
        ])
    );

    let action = parse(&["package", "build-certs", "--check", "--changed"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::BuildCerts(options))) = action else {
        panic!("expected package build-certs command");
    };
    assert_eq!(options.selection, PackageBuildSelection::Changed);
}

#[test]
fn package_build_certs_selection_rejects_invalid_combinations() {
    for args in [
        vec!["package", "build-certs", "--module", "Proofs.A"],
        vec!["package", "build-certs", "--changed"],
    ] {
        let error = parse_error(&args);
        assert_eq!(error.reason, UsageReason::UnsupportedFlag);
    }
    let conflict = parse_error(&[
        "package",
        "build-certs",
        "--check",
        "--module=Proofs.A",
        "--changed",
    ]);
    assert_eq!(conflict.reason, UsageReason::InvalidFlagValue);
    let duplicate = parse_error(&[
        "package",
        "build-certs",
        "--check",
        "--module=Proofs.A",
        "--module",
        "Proofs.A",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    let invalid = parse_error(&["package", "build-certs", "--check", "--module=Proofs..A"]);
    assert_eq!(invalid.reason, UsageReason::InvalidModuleName);
}

#[test]
fn package_cli_args_rejects_build_certs_build_check_cache_duplicate_unknown_and_write_mode() {
    let duplicate = parse_error(&[
        "package",
        "build-certs",
        "--check",
        "--build-check-cache",
        "off",
        "--build-check-cache=read-through",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--build-check-cache"));

    let unknown = parse_error(&[
        "package",
        "build-certs",
        "--check",
        "--build-check-cache=local-hit",
    ]);
    assert_eq!(unknown.reason, UsageReason::UnsupportedBuildCheckCacheMode);
    assert_eq!(unknown.flag.as_deref(), Some("--build-check-cache"));
    assert_eq!(unknown.value.as_deref(), Some("local-hit"));

    let write_mode = parse_error(&[
        "package",
        "build-certs",
        "--build-check-cache",
        "read-through",
    ]);
    assert_eq!(write_mode.reason, UsageReason::UnsupportedFlag);
    assert_eq!(write_mode.flag.as_deref(), Some("--build-check-cache"));
    assert_eq!(write_mode.value.as_deref(), Some("read-through"));
}

#[test]
fn package_cli_args_rejects_build_certs_update_manifest_hashes_misuse() {
    let duplicate = parse_error(&[
        "package",
        "build-certs",
        "--update-manifest-hashes",
        "--update-manifest-hashes",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.command.as_deref(), Some("package build-certs"));
    assert_eq!(duplicate.flag.as_deref(), Some("--update-manifest-hashes"));

    let value_form = parse_error(&["package", "build-certs", "--update-manifest-hashes=true"]);
    assert_eq!(value_form.reason, UsageReason::UnsupportedFlag);
    assert_eq!(value_form.command.as_deref(), Some("package build-certs"));
    assert_eq!(value_form.flag.as_deref(), Some("--update-manifest-hashes"));
    assert_eq!(value_form.value.as_deref(), Some("true"));

    let read_through = parse_error(&[
        "package",
        "build-certs",
        "--check",
        "--update-manifest-hashes",
        "--build-check-cache",
        "read-through",
    ]);
    assert_eq!(read_through.reason, UsageReason::UnsupportedFlag);
    assert_eq!(read_through.command.as_deref(), Some("package build-certs"));
    assert_eq!(read_through.flag.as_deref(), Some("--build-check-cache"));
    assert_eq!(read_through.value.as_deref(), Some("read-through"));

    let write_read_through = parse_error(&[
        "package",
        "build-certs",
        "--update-manifest-hashes",
        "--build-check-cache",
        "read-through",
    ]);
    assert_eq!(write_read_through.reason, UsageReason::UnsupportedFlag);
    assert_eq!(
        write_read_through.command.as_deref(),
        Some("package build-certs")
    );
    assert_eq!(
        write_read_through.flag.as_deref(),
        Some("--build-check-cache")
    );
    assert_eq!(write_read_through.value.as_deref(), Some("read-through"));
}

#[test]
fn package_cli_args_build_certs_update_manifest_hashes_runtime_loads_package_root() {
    let action = parse(&[
        "package",
        "build-certs",
        "--root",
        "missing-package",
        "--update-manifest-hashes",
    ]);
    let CliAction::Run(CliCommand::Package(command)) = action else {
        panic!("expected package build-certs command");
    };

    let result = run_package_command(command);
    assert_eq!(result.command, "package build-certs");
    assert_eq!(result.root, "missing-package");
    assert_eq!(result.status, CommandStatus::Failed);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageManifest);
    assert_eq!(result.diagnostics[0].reason_code, "manifest_missing");
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("npa-package.toml")
    );
}

#[test]
fn package_cli_args_parses_axiom_report_check_mode() {
    let action = parse(&[
        "package",
        "axiom-report",
        "--root=proofs",
        "--check",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::AxiomReport(options))) = action else {
        panic!("expected package axiom-report command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(options.timings, PackageTimingMode::Off);
}

#[test]
fn package_timings_cli_args_parse_for_axiom_report() {
    let action = parse(&[
        "package",
        "axiom-report",
        "--root=proofs",
        "--timings",
        "summary",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::AxiomReport(options))) = action else {
        panic!("expected package axiom-report command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert_eq!(options.timings, PackageTimingMode::Summary);

    let action = parse(&["package", "axiom-report", "--timings=detailed"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::AxiomReport(options))) = action else {
        panic!("expected package axiom-report command");
    };
    assert_eq!(options.timings, PackageTimingMode::Detailed);

    let unknown = parse_error(&["package", "axiom-report", "--timings=trace"]);
    assert_eq!(unknown.reason, UsageReason::UnsupportedTimingMode);
    assert_eq!(unknown.flag.as_deref(), Some("--timings"));
    assert_eq!(unknown.value.as_deref(), Some("trace"));

    let duplicate = parse_error(&[
        "package",
        "axiom-report",
        "--timings=summary",
        "--timings",
        "off",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--timings"));
}

#[test]
fn package_cli_args_parses_package_index_check_mode() {
    let action = parse(&["package", "index", "--root=proofs", "--check", "--json"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::Index(options))) = action else {
        panic!("expected package index command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(options.timings, PackageTimingMode::Off);
}

#[test]
fn package_cli_args_parses_package_export_summary_check_mode() {
    let action = parse(&[
        "package",
        "export-summary",
        "--root=proofs",
        "--check",
        "--json",
        "--out",
        "generated/custom-export-summary.json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::ExportSummary(options))) = action else {
        panic!("expected package export-summary command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(
        options.out.as_deref(),
        Some(Path::new("generated/custom-export-summary.json"))
    );
    assert_eq!(options.timings, PackageTimingMode::Off);
}

#[test]
fn package_cli_args_parses_package_export_candidate_metadata() {
    let action = parse(&[
        "package",
        "export-candidate-metadata",
        "--root=proofs",
        "--module",
        "Proofs.Ai.Basic",
        "--declaration=compose",
        "--out",
        "target/candidates/compose.metadata.json",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::ExportCandidateMetadata(options))) =
        action
    else {
        panic!("expected package export-candidate-metadata command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert_eq!(options.module, "Proofs.Ai.Basic");
    assert_eq!(options.declaration, "compose");
    assert_eq!(
        options.out.as_path(),
        Path::new("target/candidates/compose.metadata.json")
    );

    let missing = parse_error(&[
        "package",
        "export-candidate-metadata",
        "--module",
        "Proofs.Ai.Basic",
        "--out",
        "target/candidates/compose.metadata.json",
    ]);
    assert_eq!(missing.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(missing.flag.as_deref(), Some("--declaration"));
}

#[test]
fn package_timings_cli_args_parse_for_projection_commands() {
    let action = parse(&["package", "index", "--timings=summary"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::Index(options))) = action else {
        panic!("expected package index command");
    };
    assert_eq!(options.timings, PackageTimingMode::Summary);

    let action = parse(&[
        "package",
        "export-summary",
        "--out",
        "generated/custom-export-summary.json",
        "--timings=detailed",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::ExportSummary(options))) = action else {
        panic!("expected package export-summary command");
    };
    assert_eq!(options.timings, PackageTimingMode::Detailed);

    let action = parse(&["package", "publish-plan", "--timings", "summary"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::PublishPlan(options))) = action else {
        panic!("expected package publish-plan command");
    };
    assert_eq!(options.timings, PackageTimingMode::Summary);
}

#[test]
fn package_cli_args_parses_publish_plan_check_mode() {
    let action = parse(&[
        "package",
        "publish-plan",
        "--root=proofs",
        "--check",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::PublishPlan(options))) = action else {
        panic!("expected package publish-plan command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(options.timings, PackageTimingMode::Off);
}

#[test]
fn package_cli_args_parses_high_trust_check_mode() {
    let action = parse(&[
        "package",
        "high-trust",
        "--root=proofs",
        "--release-policy",
        "ci/release.high-trust.json",
        "--release-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--runner-policy",
        "ci/runner.high-trust.json",
        "--runner-policy-hash",
        "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        "--challenge-runner-policy",
        "ci/runner.challenge.json",
        "--challenge-runner-policy-hash",
        "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
        "--checker-registry",
        "ci/checker-binaries.json",
        "--out",
        "proofs/generated/verified-high-trust.json",
        "--check",
        "--json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::HighTrust(options))) = action else {
        panic!("expected package high-trust command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert!(options.check);
    assert_eq!(
        options.release_policy,
        PathBuf::from("ci/release.high-trust.json")
    );
    assert_eq!(
        options.challenge_runner_policy,
        PathBuf::from("ci/runner.challenge.json")
    );
    assert_eq!(
        options.out.as_ref().unwrap(),
        &PathBuf::from("proofs/generated/verified-high-trust.json")
    );
}

#[test]
fn package_cli_args_defaults_verify_certs_checker_to_reference() {
    let action = parse(&["package", "verify-certs"]);

    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.checker, PackageChecker::Reference);
    assert!(!options.changed);
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);
    assert_eq!(options.jobs, 1);
    assert_eq!(options.timings, PackageTimingMode::Off);
    assert_eq!(options.package_lock_mode, PackageLockInputMode::CheckedFile);
    assert_eq!(options.common.root, PathBuf::from("."));
}

#[test]
fn package_cli_args_parses_verify_certs_package_lock_modes_with_existing_options() {
    let checked = parse(&[
        "package",
        "verify-certs",
        "--package-lock",
        "checked",
        "--changed",
        "--checker=fast",
        "--jobs=2",
        "--timings=summary",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(checked))) = checked else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(checked.package_lock_mode, PackageLockInputMode::CheckedFile);
    assert!(checked.changed);
    assert_eq!(checked.checker, PackageChecker::Fast);
    assert_eq!(checked.jobs, 2);
    assert_eq!(checked.timings, PackageTimingMode::Summary);

    let checked_equals = parse(&["package", "verify-certs", "--package-lock=checked"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(checked_equals))) =
        checked_equals
    else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(
        checked_equals.package_lock_mode,
        PackageLockInputMode::CheckedFile
    );

    let reconstructed_with_audit_cache = parse(&[
        "package",
        "verify-certs",
        "--package-lock=reconstructed",
        "--checker=fast",
        "--audit-cache=read-through",
        "--timings=detailed",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(
        reconstructed_with_audit_cache,
    ))) = reconstructed_with_audit_cache
    else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(
        reconstructed_with_audit_cache.package_lock_mode,
        PackageLockInputMode::ReconstructedInMemory
    );
    assert_eq!(
        reconstructed_with_audit_cache.audit_cache,
        PackageAuditCacheMode::ReadThrough
    );
    assert_eq!(
        reconstructed_with_audit_cache.timings,
        PackageTimingMode::Detailed
    );

    let reconstructed_with_memo = parse(&[
        "package",
        "verify-certs",
        "--package-lock",
        "reconstructed",
        "--checker=fast",
        "--verifier-memo=disk",
        "--jobs=4",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(reconstructed_with_memo))) =
        reconstructed_with_memo
    else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(
        reconstructed_with_memo.package_lock_mode,
        PackageLockInputMode::ReconstructedInMemory
    );
    assert_eq!(
        reconstructed_with_memo.verifier_memo,
        PackageVerifierMemoMode::Disk
    );
    assert_eq!(reconstructed_with_memo.jobs, 4);
}

#[test]
fn package_cli_args_rejects_invalid_package_lock_selection_before_package_loading() {
    let duplicate = parse_error(&[
        "package",
        "verify-certs",
        "--package-lock",
        "checked",
        "--package-lock=reconstructed",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--package-lock"));

    for args in [
        vec!["package", "verify-certs", "--package-lock"],
        vec!["package", "verify-certs", "--package-lock="],
    ] {
        let missing = parse_error(&args);
        assert_eq!(missing.reason, UsageReason::MissingFlagValue);
        assert_eq!(missing.flag.as_deref(), Some("--package-lock"));
        assert!(missing.value.is_none());
    }

    for (args, expected_value) in [
        (
            vec!["package", "verify-certs", "--package-lock", "auto"],
            "auto",
        ),
        (
            vec!["package", "verify-certs", "--package-lock=automatic"],
            "automatic",
        ),
    ] {
        let invalid = parse_error(&args);
        assert_eq!(invalid.reason, UsageReason::InvalidFlagValue);
        assert_eq!(invalid.flag.as_deref(), Some("--package-lock"));
        assert_eq!(invalid.value.as_deref(), Some(expected_value));
    }

    let reconstructed_external = parse_error(&[
        "package",
        "verify-certs",
        "--root=missing-package-root",
        "--package-lock=reconstructed",
        "--checker=external",
    ]);
    assert_eq!(reconstructed_external.reason, UsageReason::UnsupportedFlag);
    assert_eq!(
        reconstructed_external.flag.as_deref(),
        Some("--package-lock")
    );
    assert_eq!(
        reconstructed_external.value.as_deref(),
        Some("reconstructed;checker=external")
    );
}

#[test]
fn package_cli_args_parses_verify_certs_fast_checker() {
    let action = parse(&[
        "package",
        "verify-certs",
        "--checker",
        "fast",
        "--root",
        "proofs",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.checker, PackageChecker::Fast);
    assert!(!options.changed);
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);
    assert_eq!(options.jobs, 1);
    assert_eq!(options.timings, PackageTimingMode::Off);
    assert_eq!(options.common.root, PathBuf::from("proofs"));
}

#[test]
fn package_cli_args_parses_verify_certs_changed_certificate_selection() {
    let action = parse(&[
        "package",
        "verify-certs",
        "--changed",
        "--checker=fast",
        "--root",
        "proofs",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert!(options.changed);
    assert_eq!(options.checker, PackageChecker::Fast);
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);
    assert_eq!(options.common.root, PathBuf::from("proofs"));

    let duplicate = parse_error(&["package", "verify-certs", "--changed", "--changed"]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--changed"));

    let external = parse_error(&[
        "package",
        "verify-certs",
        "--changed",
        "--checker=external",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);
    assert_eq!(external.reason, UsageReason::UnsupportedFlag);
    assert_eq!(external.flag.as_deref(), Some("--changed"));
    assert_eq!(external.value.as_deref(), Some("external"));

    let audit_cache = parse_error(&[
        "package",
        "verify-certs",
        "--changed",
        "--audit-cache=read-through",
    ]);
    assert_eq!(audit_cache.reason, UsageReason::UnsupportedFlag);
    assert_eq!(audit_cache.flag.as_deref(), Some("--audit-cache"));
    assert_eq!(audit_cache.value.as_deref(), Some("read-through"));

    let verifier_memo = parse_error(&[
        "package",
        "verify-certs",
        "--changed",
        "--verifier-memo=disk",
    ]);
    assert_eq!(verifier_memo.reason, UsageReason::UnsupportedFlag);
    assert_eq!(verifier_memo.flag.as_deref(), Some("--verifier-memo"));
    assert_eq!(verifier_memo.value.as_deref(), Some("disk"));
}

#[test]
fn package_timings_cli_args_parse_for_verify_certs() {
    let action = parse(&[
        "package",
        "verify-certs",
        "--checker=fast",
        "--timings=detailed",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.checker, PackageChecker::Fast);
    assert_eq!(options.timings, PackageTimingMode::Detailed);

    let action = parse(&["package", "verify-certs", "--timings", "off"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.timings, PackageTimingMode::Off);

    let missing = parse_error(&["package", "verify-certs", "--timings="]);
    assert_eq!(missing.reason, UsageReason::MissingFlagValue);
    assert_eq!(missing.flag.as_deref(), Some("--timings"));

    let unknown = parse_error(&["package", "verify-certs", "--timings=trace"]);
    assert_eq!(unknown.reason, UsageReason::UnsupportedTimingMode);
    assert_eq!(unknown.flag.as_deref(), Some("--timings"));
    assert_eq!(unknown.value.as_deref(), Some("trace"));
}

#[test]
fn package_verify_certs_jobs_args_parse_and_reject_invalid_values() {
    let action = parse(&["package", "verify-certs", "--checker=fast", "--jobs", "4"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.jobs, 4);

    let action = parse(&["package", "verify-certs", "--jobs=2"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.jobs, 2);

    let zero = parse_error(&["package", "verify-certs", "--jobs", "0"]);
    assert_eq!(zero.reason, UsageReason::InvalidFlagValue);
    assert_eq!(zero.flag.as_deref(), Some("--jobs"));
    assert_eq!(zero.value.as_deref(), Some("0"));

    let non_integer = parse_error(&["package", "verify-certs", "--jobs=abc"]);
    assert_eq!(non_integer.reason, UsageReason::InvalidFlagValue);
    assert_eq!(non_integer.flag.as_deref(), Some("--jobs"));
    assert_eq!(non_integer.value.as_deref(), Some("abc"));

    let duplicate = parse_error(&["package", "verify-certs", "--jobs=1", "--jobs", "2"]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--jobs"));
}

#[test]
fn package_verify_certs_audit_cache_args_parse_read_through() {
    let action = parse(&[
        "package",
        "verify-certs",
        "--checker=fast",
        "--audit-cache",
        "read-through",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.checker, PackageChecker::Fast);
    assert_eq!(options.audit_cache, PackageAuditCacheMode::ReadThrough);

    let action = parse(&["package", "verify-certs", "--audit-cache=off"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);

    let action = parse(&["package", "verify-certs", "--audit-cache=local-hit"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.audit_cache, PackageAuditCacheMode::LocalHit);
}

#[test]
fn package_verify_certs_audit_cache_args_reject_duplicate_unknown_and_external() {
    let duplicate = parse_error(&[
        "package",
        "verify-certs",
        "--audit-cache",
        "off",
        "--audit-cache=read-through",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--audit-cache"));

    let unknown = parse_error(&["package", "verify-certs", "--audit-cache=remote-hit"]);
    assert_eq!(unknown.reason, UsageReason::UnsupportedAuditCacheMode);
    assert_eq!(unknown.flag.as_deref(), Some("--audit-cache"));
    assert_eq!(unknown.value.as_deref(), Some("remote-hit"));

    let external = parse_error(&[
        "package",
        "verify-certs",
        "--checker",
        "external",
        "--audit-cache",
        "read-through",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);
    assert_eq!(external.reason, UsageReason::UnsupportedFlag);
    assert_eq!(external.flag.as_deref(), Some("--audit-cache"));
    assert_eq!(external.value.as_deref(), Some("read-through"));

    let external_local_hit = parse_error(&[
        "package",
        "verify-certs",
        "--checker=external",
        "--audit-cache=local-hit",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);
    assert_eq!(external_local_hit.reason, UsageReason::UnsupportedFlag);
    assert_eq!(external_local_hit.flag.as_deref(), Some("--audit-cache"));
    assert_eq!(external_local_hit.value.as_deref(), Some("local-hit"));
}

#[test]
fn package_verify_certs_verifier_memo_args_parse_disk() {
    let action = parse(&[
        "package",
        "verify-certs",
        "--checker=fast",
        "--verifier-memo",
        "disk",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.checker, PackageChecker::Fast);
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Disk);

    let action = parse(&["package", "verify-certs", "--verifier-memo=off"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);

    let action = parse(&["package", "verify-certs", "--verifier-memo=read-through"]);
    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::ReadThrough);
}

#[test]
fn package_verify_certs_verifier_memo_args_reject_duplicate_unknown_external_and_audit_cache() {
    let duplicate = parse_error(&[
        "package",
        "verify-certs",
        "--verifier-memo",
        "off",
        "--verifier-memo=disk",
    ]);
    assert_eq!(duplicate.reason, UsageReason::DuplicateFlag);
    assert_eq!(duplicate.flag.as_deref(), Some("--verifier-memo"));

    let unknown = parse_error(&["package", "verify-certs", "--verifier-memo=remote"]);
    assert_eq!(unknown.reason, UsageReason::UnsupportedVerifierMemoMode);
    assert_eq!(unknown.flag.as_deref(), Some("--verifier-memo"));
    assert_eq!(unknown.value.as_deref(), Some("remote"));

    let external = parse_error(&[
        "package",
        "verify-certs",
        "--checker=external",
        "--verifier-memo=disk",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);
    assert_eq!(external.reason, UsageReason::UnsupportedFlag);
    assert_eq!(external.flag.as_deref(), Some("--verifier-memo"));
    assert_eq!(external.value.as_deref(), Some("disk"));

    let audit_cache = parse_error(&[
        "package",
        "verify-certs",
        "--audit-cache=read-through",
        "--verifier-memo=disk",
    ]);
    assert_eq!(audit_cache.reason, UsageReason::UnsupportedFlag);
    assert_eq!(audit_cache.flag.as_deref(), Some("--verifier-memo"));
    assert_eq!(audit_cache.value.as_deref(), Some("disk"));
}

#[test]
fn package_cli_args_parses_verify_certs_external_checker_with_runner_inputs() {
    let action = parse(&[
        "package",
        "verify-certs",
        "--checker",
        "external",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);

    let CliAction::Run(CliCommand::Package(PackageCommand::VerifyCerts(options))) = action else {
        panic!("expected package verify-certs command");
    };
    assert_eq!(options.checker, PackageChecker::External);
    let external = options.external.as_ref().unwrap();
    assert_eq!(
        external.runner_policy,
        PathBuf::from("ci/runner.release.json")
    );
    assert_eq!(
        external.runner_policy_hash,
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    );
    assert_eq!(
        external.checker_registry,
        PathBuf::from("ci/checker-binaries.json")
    );
}

#[test]
fn package_cli_args_rejects_external_checker_without_runner_inputs() {
    let error = parse_error(&["package", "verify-certs", "--checker", "external"]);

    assert_eq!(error.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(error.flag.as_deref(), Some("--runner-policy"));
    assert!(error.value.is_none());

    let partial = parse_error(&[
        "package",
        "verify-certs",
        "--checker=external",
        "--runner-policy",
        "ci/runner.release.json",
    ]);
    assert_eq!(partial.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(partial.flag.as_deref(), Some("--runner-policy-hash"));
    assert!(partial.value.is_none());

    let missing_registry = parse_error(&[
        "package",
        "verify-certs",
        "--checker=external",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    ]);
    assert_eq!(missing_registry.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(missing_registry.flag.as_deref(), Some("--checker-registry"));
    assert!(missing_registry.value.is_none());
}

#[test]
fn package_cli_args_shared_verify_validation_rejects_options_in_runtime_order() {
    let external_parallel = parse_error(&[
        "package",
        "verify-certs",
        "--checker=external",
        "--jobs=2",
        "--audit-cache=read-through",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);
    assert_eq!(external_parallel.reason, UsageReason::UnsupportedFlag);
    assert_eq!(external_parallel.flag.as_deref(), Some("--jobs"));
    assert_eq!(external_parallel.value.as_deref(), Some("2"));

    let cache_parallel = parse_error(&[
        "package",
        "verify-certs",
        "--checker=fast",
        "--jobs=4",
        "--audit-cache=read-through",
        "--verifier-memo=disk",
    ]);
    assert_eq!(cache_parallel.reason, UsageReason::UnsupportedFlag);
    assert_eq!(cache_parallel.flag.as_deref(), Some("--jobs"));
    assert_eq!(
        cache_parallel.value.as_deref(),
        Some("jobs=4;audit_cache=read-through")
    );

    let unexpected_external = parse_error(&[
        "package",
        "verify-certs",
        "--checker=reference",
        "--runner-policy",
        "ci/runner.release.json",
        "--runner-policy-hash",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--checker-registry",
        "ci/checker-binaries.json",
    ]);
    assert_eq!(unexpected_external.reason, UsageReason::UnsupportedFlag);
    assert_eq!(unexpected_external.flag.as_deref(), Some("--runner-policy"));
    assert!(unexpected_external.value.is_none());
}

#[test]
fn package_cli_args_rejects_high_trust_without_required_inputs() {
    let error = parse_error(&["package", "high-trust", "--check"]);

    assert_eq!(error.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(error.flag.as_deref(), Some("--release-policy"));
    assert!(error.value.is_none());
}

#[test]
fn package_cli_args_rejects_unsupported_clr04_flags() {
    for flag in [
        "--changed",
        "--changed=true",
        "--all",
        "--all=true",
        "--registry",
        "--registry=local",
        "--network",
        "--network=on",
        "--latest",
        "--latest=true",
        "--upload",
        "--upload=true",
        "--sign",
        "--sign=true",
        "--include-source",
        "--include-source=true",
        "--include-replay",
        "--include-replay=true",
        "--include-ai-traces",
        "--include-ai-traces=true",
        "--timings",
        "--timings=summary",
        "--package-lock",
        "--package-lock=checked",
    ] {
        let error = parse_error(&["package", "check", flag]);
        assert_eq!(error.reason, UsageReason::UnsupportedFlag, "{flag}");
        assert_eq!(error.flag.as_deref(), Some(flag), "{flag}");
    }

    let checker_error = parse_error(&["package", "axiom-report", "--checker=external"]);
    assert_eq!(checker_error.reason, UsageReason::UnsupportedFlag);
    assert_eq!(checker_error.flag.as_deref(), Some("--checker=external"));

    let export_summary_checker = parse_error(&["package", "export-summary", "--checker=reference"]);
    assert_eq!(export_summary_checker.reason, UsageReason::UnsupportedFlag);
    assert_eq!(
        export_summary_checker.flag.as_deref(),
        Some("--checker=reference")
    );

    let runner_policy_error = parse_error(&["package", "check", "--runner-policy=ci/policy.json"]);
    assert_eq!(runner_policy_error.reason, UsageReason::UnsupportedFlag);
    assert_eq!(
        runner_policy_error.flag.as_deref(),
        Some("--runner-policy=ci/policy.json")
    );
}

#[test]
fn package_cli_args_rejects_unknown_commands_and_flags() {
    let command_error = parse_error(&["package", "publish"]);
    assert_eq!(command_error.reason, UsageReason::UnknownCommand);
    assert_eq!(command_error.command.as_deref(), Some("package publish"));

    let flag_error = parse_error(&["package", "check", "--mystery"]);
    assert_eq!(flag_error.reason, UsageReason::UnknownFlag);
    assert_eq!(flag_error.flag.as_deref(), Some("--mystery"));
}

#[test]
fn package_cli_args_rejects_duplicate_flags() {
    let root_error = parse_error(&["package", "check", "--root", "proofs", "--root", "other"]);
    assert_eq!(root_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(root_error.flag.as_deref(), Some("--root"));

    let json_error = parse_error(&["package", "check", "--json", "--json"]);
    assert_eq!(json_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(json_error.flag.as_deref(), Some("--json"));

    let checker_error = parse_error(&[
        "package",
        "verify-certs",
        "--checker",
        "fast",
        "--checker",
        "reference",
    ]);
    assert_eq!(checker_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(checker_error.flag.as_deref(), Some("--checker"));

    let build_error = parse_error(&["package", "build-certs", "--check", "--check"]);
    assert_eq!(build_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(build_error.flag.as_deref(), Some("--check"));

    let axiom_report_error = parse_error(&["package", "axiom-report", "--check", "--check"]);
    assert_eq!(axiom_report_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(axiom_report_error.flag.as_deref(), Some("--check"));

    let index_error = parse_error(&["package", "index", "--check", "--check"]);
    assert_eq!(index_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(index_error.flag.as_deref(), Some("--check"));

    let export_summary_check_error =
        parse_error(&["package", "export-summary", "--check", "--check"]);
    assert_eq!(
        export_summary_check_error.reason,
        UsageReason::DuplicateFlag
    );
    assert_eq!(export_summary_check_error.flag.as_deref(), Some("--check"));

    let export_summary_out_error = parse_error(&[
        "package",
        "export-summary",
        "--out",
        "a.json",
        "--out=b.json",
    ]);
    assert_eq!(export_summary_out_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(export_summary_out_error.flag.as_deref(), Some("--out"));

    let publish_plan_error = parse_error(&["package", "publish-plan", "--check", "--check"]);
    assert_eq!(publish_plan_error.reason, UsageReason::DuplicateFlag);
    assert_eq!(publish_plan_error.flag.as_deref(), Some("--check"));
}

#[test]
fn package_cli_args_rejects_missing_flag_values() {
    let root_error = parse_error(&["package", "check", "--root"]);
    assert_eq!(root_error.reason, UsageReason::MissingFlagValue);
    assert_eq!(root_error.flag.as_deref(), Some("--root"));

    let checker_error = parse_error(&["package", "verify-certs", "--checker"]);
    assert_eq!(checker_error.reason, UsageReason::MissingFlagValue);
    assert_eq!(checker_error.flag.as_deref(), Some("--checker"));

    let checker_equals_error = parse_error(&["package", "verify-certs", "--checker="]);
    assert_eq!(checker_equals_error.reason, UsageReason::MissingFlagValue);
    assert_eq!(checker_equals_error.flag.as_deref(), Some("--checker"));

    let timing_error = parse_error(&["package", "axiom-report", "--timings"]);
    assert_eq!(timing_error.reason, UsageReason::MissingFlagValue);
    assert_eq!(timing_error.flag.as_deref(), Some("--timings"));

    for flag in ["--scope", "--module", "--top"] {
        let error = parse_error(&["package", "refactor-plan", flag]);
        assert_eq!(error.reason, UsageReason::MissingFlagValue, "{flag}");
        assert_eq!(error.flag.as_deref(), Some(flag), "{flag}");

        let equals_flag = format!("{flag}=");
        let error = parse_error(&["package", "refactor-plan", &equals_flag]);
        assert_eq!(error.reason, UsageReason::MissingFlagValue, "{flag}");
        assert_eq!(error.flag.as_deref(), Some(flag), "{flag}");
    }
}

#[test]
fn package_cli_args_parses_help_topics() {
    assert_eq!(parse(&["--help"]), CliAction::Help(HelpTopic::Root));
    assert_eq!(
        parse(&["package", "--help"]),
        CliAction::Help(HelpTopic::Package)
    );
    assert_eq!(
        parse(&["package", "check", "--help"]),
        CliAction::Help(HelpTopic::PackageCheck)
    );
    assert_eq!(
        parse(&["package", "build-certs", "--help"]),
        CliAction::Help(HelpTopic::PackageBuildCerts)
    );
    assert_eq!(
        parse(&["package", "verify-certs", "--help"]),
        CliAction::Help(HelpTopic::PackageVerifyCerts)
    );
    assert_eq!(
        parse(&["package", "lock", "--help"]),
        CliAction::Help(HelpTopic::PackageLock)
    );
    assert_eq!(
        parse(&["package", "lock", "check", "--help"]),
        CliAction::Help(HelpTopic::PackageLockCheck)
    );
    assert_eq!(
        parse(&["package", "lock", "write", "--help"]),
        CliAction::Help(HelpTopic::PackageLockWrite)
    );
    assert_eq!(
        parse(&["package", "axiom-report", "--help"]),
        CliAction::Help(HelpTopic::PackageAxiomReport)
    );
    assert_eq!(
        parse(&["package", "index", "--help"]),
        CliAction::Help(HelpTopic::PackageIndex)
    );
    assert_eq!(
        parse(&["package", "publish-plan", "--help"]),
        CliAction::Help(HelpTopic::PackagePublishPlan)
    );
    assert_eq!(
        parse(&["package", "high-trust", "--help"]),
        CliAction::Help(HelpTopic::PackageHighTrust)
    );
    assert_eq!(
        parse(&["package", "refactor-plan", "--help"]),
        CliAction::Help(HelpTopic::PackageRefactorPlan)
    );
}

#[test]
fn package_build_certs_help_documents_update_manifest_hashes() {
    let help = render_help(HelpTopic::PackageBuildCerts);

    assert!(help.contains("[--update-manifest-hashes]"));
    assert!(help.contains("refreshes local module hash pins"));
    assert!(help.contains("[--module MODULE]... [--changed]"));
    assert!(help.contains("required release gates"));
    assert!(help.contains("--check --build-check-cache read-through"));
}

#[test]
fn package_export_help_documents_package_root_relative_output() {
    let summary_help = render_help(HelpTopic::PackageExportSummary);
    let candidate_help = render_help(HelpTopic::PackageExportCandidateMetadata);

    for help in [summary_help, candidate_help] {
        assert!(help.contains("relative to --root"));
        assert!(help.contains("--root proofs --out generated/"));
        assert!(!help.contains("--out proofs/"));
    }
    assert!(summary_help.contains("Omitting --out uses generated/verified-export-summary.json"));
}

#[test]
fn package_verify_certs_help_documents_changed_and_package_lock_selection() {
    let help = render_help(HelpTopic::PackageVerifyCerts);

    assert!(help.contains("[--changed]"));
    assert!(help.contains("certificate files are changed in Git"));
    assert!(help.contains("[--package-lock checked|reconstructed]"));
    assert!(help.contains("package-lock input defaults to checked"));
    assert!(help.contains("Reconstructed is unavailable with the external checker"));
}

#[test]
fn package_cli_args_parses_version_topics() {
    assert_eq!(parse(&["--version"]), CliAction::Version);
    assert_eq!(parse(&["-V"]), CliAction::Version);
    assert_eq!(parse(&["version"]), CliAction::Version);
}

#[test]
fn package_cli_args_binary_reports_version() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .arg("--version")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("npa {}\n", env!("CARGO_PKG_VERSION"))
    );
}

#[test]
fn package_cli_args_binary_reports_deterministic_usage_error() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--checker", "external"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "package verify-certs: failed\nerror Usage missing_required_flag field=--runner-policy\n"
    );
}

#[test]
fn package_cli_args_binary_reports_json_usage_error_when_requested() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check", "--mystery", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"npa.package.command_result.v0.3\""));
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains("\"reason_code\":\"unknown_flag\""));
    assert!(stdout.contains("\"field\":\"--mystery\""));
}

#[test]
fn package_cli_args_binary_reports_package_lock_usage_errors() {
    let human = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--package-lock=auto"])
        .output()
        .unwrap();

    assert_eq!(human.status.code(), Some(2));
    assert!(human.stdout.is_empty());
    assert_eq!(
        String::from_utf8(human.stderr).unwrap(),
        "package verify-certs: failed\nerror Usage invalid_flag_value field=--package-lock actual=auto\n"
    );

    let json = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args([
            "package",
            "verify-certs",
            "--root=missing-package-root",
            "--package-lock=reconstructed",
            "--checker=external",
            "--json",
        ])
        .output()
        .unwrap();

    assert_eq!(json.status.code(), Some(2));
    assert!(json.stderr.is_empty());
    let stdout = String::from_utf8(json.stdout).unwrap();
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains("\"reason_code\":\"unsupported_flag\""));
    assert!(stdout.contains("\"field\":\"--package-lock\""));
    assert!(stdout.contains("\"actual_value\":\"reconstructed;checker=external\""));
}

#[test]
fn package_cli_args_parses_artifact_ledger_modules_and_deduplicates() {
    let action = parse(&[
        "package",
        "audit-artifact-ledger",
        "--root=proofs",
        "--json",
        "--module",
        "Example.Second",
        "--module=Example.First",
        "--module=Example.Second",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::AuditArtifactLedger(options))) = action
    else {
        panic!("expected artifact-ledger audit command");
    };
    assert_eq!(options.common.root, PathBuf::from("proofs"));
    assert!(options.common.json);
    assert_eq!(
        options
            .modules
            .iter()
            .map(npa_cert::Name::as_dotted)
            .collect::<Vec<_>>(),
        vec!["Example.Second", "Example.First"]
    );
}

#[test]
fn package_cli_args_artifact_ledger_help_and_errors_are_stable() {
    assert_eq!(
        parse(&["package", "audit-artifact-ledger", "--help"]),
        CliAction::Help(HelpTopic::PackageAuditArtifactLedger)
    );
    let help = render_help(HelpTopic::PackageAuditArtifactLedger);
    assert!(help.contains("[--module MODULE]..."));
    assert!(help.contains("writes no\nfiles"));
    assert!(!help.contains("--checker"));
    assert!(!help.contains("--check"));

    let missing = parse_error(&["package", "audit-artifact-ledger", "--module"]);
    assert_eq!(missing.reason, UsageReason::MissingFlagValue);
    let invalid = parse_error(&[
        "package",
        "audit-artifact-ledger",
        "--module=not..canonical",
    ]);
    assert_eq!(invalid.reason, UsageReason::InvalidModuleName);
    let unsupported = parse_error(&["package", "audit-artifact-ledger", "--checker=reference"]);
    assert_eq!(unsupported.reason, UsageReason::UnsupportedFlag);
}

#[test]
fn package_promotion_commands_parse_strict_modes() {
    let prepared = parse(&[
        "package",
        "prepare-promotion",
        "--root",
        "source",
        "--target-baseline-root",
        "baseline",
        "--acceptance-policy",
        "acceptance-policy.json",
        "--source-acceptance",
        "l2-acceptance.json",
        "--transport-policy",
        "transport-policy.json",
        "--mapping",
        "promotion/mapping.json",
        "--equivalent-origin-root",
        "alias-a",
        "--equivalent-origin-root=alias-b",
        "--out",
        "promotion/plan.json",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::PreparePromotion(options))) = prepared
    else {
        panic!("expected prepare-promotion");
    };
    assert_eq!(options.equivalent_origin_roots.len(), 2);

    let temporary = parse(&[
        "package",
        "materialize-promotion",
        "--root",
        "source",
        "--target-baseline-root",
        "baseline",
        "--target-root",
        "target",
        "--plan",
        "promotion/plan.json",
        "--equivalent-origin-root",
        "alias-a",
        "--phase",
        "temporary",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::MaterializePromotion(options))) =
        temporary
    else {
        panic!("expected materialize-promotion");
    };
    assert!(!options.apply, "dry-run must be the default");
    assert_eq!(options.equivalent_origin_roots, [PathBuf::from("alias-a")]);

    let missing_attestation = parse_error(&[
        "package",
        "materialize-promotion",
        "--root=source",
        "--target-baseline-root=baseline",
        "--target-root=target",
        "--plan=promotion/plan.json",
        "--phase=tracked",
    ]);
    assert_eq!(missing_attestation.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(
        missing_attestation.flag.as_deref(),
        Some("--transport-attestation")
    );

    let invalid_recovery = parse_error(&[
        "package",
        "materialize-promotion",
        "--target-root=target",
        "--recover=journal.json",
        "--root=source",
    ]);
    assert_eq!(invalid_recovery.reason, UsageReason::InvalidFlagValue);

    let recovery_with_alias = parse_error(&[
        "package",
        "materialize-promotion",
        "--target-root=target",
        "--recover=journal.json",
        "--equivalent-origin-root=alias-a",
    ]);
    assert_eq!(recovery_with_alias.reason, UsageReason::InvalidFlagValue);
}

#[test]
fn package_promotion_registry_commands_parse() {
    let validate = parse(&[
        "package",
        "validate-promotion-origin-registry",
        "--root=mathlib",
        "--source-root=corpus",
        "--source-root",
        "project",
        "--previous-registry=previous.json",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::ValidatePromotionOriginRegistry(
        options,
    ))) = validate
    else {
        panic!("expected registry validator");
    };
    assert_eq!(options.source_roots.len(), 2);

    let register = parse(&[
        "package",
        "register-equivalent-promotion-origin",
        "--root=project",
        "--target-root=mathlib",
        "--promotion-id=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    ]);
    let CliAction::Run(CliCommand::Package(PackageCommand::RegisterEquivalentPromotionOrigin(
        options,
    ))) = register
    else {
        panic!("expected equivalent-origin registration");
    };
    assert!(!options.apply);
}
