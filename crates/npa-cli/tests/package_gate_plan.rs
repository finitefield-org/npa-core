use std::path::PathBuf;
use std::{fs, process::Command};

use npa_cli::args::{PackageCommonOptions, PackageGatePlanOptions};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind};
use npa_cli::package_gate_plan::run_package_gate_plan;
use npa_package::{package_gate_plan_from_paths, PackageGateImpactClass};

#[test]
fn package_gate_plan_cli_renders_empty_head_diff_with_base_count_and_trust_boundary() {
    let result = run_package_gate_plan(PackageGatePlanOptions {
        common: PackageCommonOptions {
            root: PathBuf::from("proofs"),
            json: true,
        },
        base: "HEAD".to_owned(),
    });

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.command, "package gate-plan");
    assert_eq!(result.root, "proofs");
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.reason_code == "gate_plan_base"
            && diagnostic.actual_value.as_deref() == Some("HEAD")
    }));
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.reason_code == "gate_plan_changed_path_count"
            && diagnostic.actual_value.as_deref() == Some("0")
    }));
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::PackagePolicy
            && diagnostic.reason_code == "gate_plan_impact_class"
            && diagnostic.actual_value.as_deref() == Some("docs-only")
    }));
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.reason_code == "gate_plan_trust_boundary"
            && diagnostic
                .actual_value
                .as_deref()
                .is_some_and(|value| value.contains("never accepts proofs"))
    }));
    let json = result.render_json();
    assert!(json.contains("\"command\":\"package gate-plan\""));
    assert!(json.contains("\"reason_code\":\"gate_plan_required_commands\""));
    assert!(json.contains("\"reason_code\":\"gate_plan_selected_commands\""));
    assert!(json.contains("git diff --check"));
}

#[test]
fn package_gate_plan_cli_reports_bad_base_without_running_gates() {
    let result = run_package_gate_plan(PackageGatePlanOptions {
        common: PackageCommonOptions {
            root: PathBuf::from("proofs"),
            json: true,
        },
        base: "refs/heads/npa-package-gate-plan-missing-base".to_owned(),
    });

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::Internal && diagnostic.reason_code == "git_diff_failed"
    }));
    assert!(!result.render_json().contains("check-corpus-full.sh"));
}

#[test]
fn package_gate_plan_policy_covers_pas16_impact_classes() {
    let docs_only = package_gate_plan_from_paths([
        "develop/proof-corpus-package-audit-speed-plan.md",
        "proofs/README.md",
    ]);
    assert_eq!(docs_only.impact_class, PackageGateImpactClass::DocsOnly);
    assert!(!plan_requires(
        &docs_only,
        "./scripts/check-corpus-package.sh"
    ));
    assert!(!plan_requires(&docs_only, "./scripts/check-corpus-full.sh"));

    let proof_authoring = package_gate_plan_from_paths([
        "proofs/Proofs/Ai/Basic/source.npa",
        "proofs/Proofs/Ai/Basic/certificate.npcert",
    ]);
    assert_eq!(
        proof_authoring.impact_class,
        PackageGateImpactClass::ProofAuthoring
    );
    assert!(plan_requires(
        &proof_authoring,
        "./scripts/check-corpus-authoring.sh"
    ));
    assert!(!plan_requires(
        &proof_authoring,
        "./scripts/check-corpus-package.sh"
    ));

    for path in [
        "tools/proof-corpus/promote.rs",
        "crates/npa-cli/src/package_gate_plan.rs",
        "proofs/generated/package-lock.json",
        "proofs/generated/theorem-index.json",
    ] {
        let plan = package_gate_plan_from_paths([path]);
        assert_eq!(
            plan.impact_class,
            PackageGateImpactClass::PackageMetadataProjection,
            "{path}"
        );
        assert!(plan_requires(&plan, "./scripts/check-corpus-package.sh"));
    }

    for path in [
        "crates/npa-cert/src/lib.rs",
        "crates/npa-checker-ref/src/lib.rs",
        "crates/npa-api/src/package_verifier.rs",
        "crates/npa-package/src/lock.rs",
    ] {
        let plan = package_gate_plan_from_paths([path]);
        assert_eq!(
            plan.impact_class,
            PackageGateImpactClass::CheckerCertificateSemantics,
            "{path}"
        );
        assert!(plan_requires(&plan, "./scripts/check-corpus-package.sh"));
        assert!(plan_requires(&plan, "./scripts/check-corpus-full.sh"));
    }

    let kernel = package_gate_plan_from_paths(["crates/npa-kernel/src/lib.rs"]);
    assert_eq!(
        kernel.impact_class,
        PackageGateImpactClass::KernelCoreSemantics
    );
    assert!(plan_requires(&kernel, "./scripts/check-corpus-full.sh"));

    let high_trust = package_gate_plan_from_paths(["crates/npa-cli/src/package_high_trust.rs"]);
    assert_eq!(
        high_trust.impact_class,
        PackageGateImpactClass::ReleaseHighTrustAdjacent
    );
    assert!(plan_requires(
        &high_trust,
        "./scripts/check-corpus-package.sh"
    ));
    assert!(plan_requires(&high_trust, "./scripts/check-corpus-full.sh"));
    assert!(plan_requires(
        &high_trust,
        concat!(
            "(cd ../npa-core && ./scripts/",
            "phase",
            "8",
            "-release-audit.sh)"
        )
    ));

    let unknown_non_doc = package_gate_plan_from_paths(["crates/npa-cli/src/new_tool.rs"]);
    assert_eq!(
        unknown_non_doc.impact_class,
        PackageGateImpactClass::PackageMetadataProjection
    );
    assert!(plan_requires(
        &unknown_non_doc,
        "./scripts/check-corpus-package.sh"
    ));
}

#[test]
fn package_gate_plan_split_contract_keeps_core_fast_gate_corpus_free() {
    let root = repo_root();
    let check_fast = fs::read_to_string(root.join("scripts/check-fast.sh")).unwrap();
    assert!(check_fast.contains("cargo clippy --workspace --all-targets"));
    assert!(check_fast.contains("cargo test --workspace --"));
    assert!(!check_fast.contains("npa-proof-corpus"));
    assert!(!check_fast.contains("package-gate-plan-report"));
    assert!(!check_fast.contains("check-corpus"));

    let syntax = Command::new("bash")
        .arg("-n")
        .arg("scripts/check-fast.sh")
        .current_dir(root)
        .output()
        .unwrap();
    assert!(
        syntax.status.success(),
        "{}",
        String::from_utf8_lossy(&syntax.stderr)
    );

    let plan = package_gate_plan_from_paths([
        "proofs/Proofs/Ai/Basic/source.npa",
        "proofs/generated/package-lock.json",
    ]);
    assert!(plan_requires(
        &plan,
        "(cd ../npa-core && ./scripts/check-fast.sh)"
    ));
    assert!(plan_requires(&plan, "./scripts/check-corpus-package.sh"));
    assert!(!plan_requires(&plan, "./scripts/check-fast.sh"));
    assert!(plan
        .optional_local_acceleration_commands
        .iter()
        .any(|command| {
            command.contains("cargo run --manifest-path ../npa-core/Cargo.toml -p npa-cli")
        }));
}

#[test]
fn package_gate_plan_public_contract_recommends_split_corpus_package_checks() {
    let plan = package_gate_plan_from_paths([
        "crates/npa-package/src/lock.rs",
        "proofs/generated/package-lock.json",
    ]);

    assert_eq!(
        plan.impact_class,
        PackageGateImpactClass::CheckerCertificateSemantics
    );
    assert!(plan_requires(
        &plan,
        "(cd ../npa-core && ./scripts/check-fast.sh)"
    ));
    assert!(plan_requires(&plan, "./scripts/check-corpus-package.sh"));
    assert!(plan_requires(&plan, "./scripts/check-corpus-full.sh"));

    assert!(plan
        .optional_local_acceleration_commands
        .iter()
        .any(|command| {
            command == "(cd ../npa-core && cargo test -p npa-cli package_cli_smoke)"
        }));
    assert!(plan.optional_local_acceleration_commands.iter().any(|command| {
        command
            == "cargo run --manifest-path ../npa-core/Cargo.toml -p npa-cli -- package verify-certs --root proofs --checker fast --json"
    }));

    for command in plan
        .required_commands
        .iter()
        .chain(plan.optional_local_acceleration_commands.iter())
    {
        assert!(!command.contains("--audit-cache read-through"));
        assert!(!command.contains("--build-check-cache read-through"));
    }
}

fn plan_requires(plan: &npa_package::PackageGatePlan, command: &str) -> bool {
    plan.required_commands
        .iter()
        .any(|required| required == command)
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}
