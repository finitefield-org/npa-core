use std::path::{Path, PathBuf};
use std::process::Command;

use npa_cli::args::{
    parse_cli_args, CliAction, CliCommand, HelpTopic, PackageAuditCacheMode,
    PackageBuildCheckCacheMode, PackageChecker, PackageCommand, PackageTimingMode,
    PackageVerifierMemoMode, UsageReason,
};

fn parse(args: &[&str]) -> CliAction {
    parse_cli_args(args.iter().copied()).unwrap()
}

fn parse_error(args: &[&str]) -> npa_cli::args::CliUsageError {
    parse_cli_args(args.iter().copied()).unwrap_err()
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
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);
    assert_eq!(options.jobs, 1);
    assert_eq!(options.timings, PackageTimingMode::Off);
    assert_eq!(options.common.root, PathBuf::from("."));
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
    assert_eq!(options.audit_cache, PackageAuditCacheMode::Off);
    assert_eq!(options.verifier_memo, PackageVerifierMemoMode::Off);
    assert_eq!(options.jobs, 1);
    assert_eq!(options.timings, PackageTimingMode::Off);
    assert_eq!(options.common.root, PathBuf::from("proofs"));
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
        parse(&["package", "verify-certs", "--help"]),
        CliAction::Help(HelpTopic::PackageVerifyCerts)
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
    assert!(stdout.contains("\"schema\":\"npa.package.command_result.v0.1\""));
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains("\"reason_code\":\"unknown_flag\""));
    assert!(stdout.contains("\"field\":\"--mystery\""));
}
