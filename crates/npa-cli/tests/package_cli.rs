use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};

use npa_api::{
    project_package_axiom_report_from_extraction, project_package_theorem_index_from_extraction,
    project_package_theorem_premise_report_from_extraction, PackageArtifactReferenceSummaryMode,
};
use npa_cli::diagnostic::{CommandResult, PACKAGE_COMMAND_RESULT_SCHEMA};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_artifacts::{
    load_package_artifact_extraction, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
    PACKAGE_THEOREM_INDEX_PATH, PACKAGE_THEOREM_PREMISE_REPORT_PATH,
};
use npa_cli::package_publish::{
    checksum_only_signature_policy, collect_package_publish_artifacts,
    collect_package_publish_downstream_import_bundle, collect_package_publish_registry_entries,
    load_package_publish_inputs, validate_publish_checker_summaries,
};
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_package_axiom_report_json,
    parse_package_publish_plan_json, parse_package_theorem_index_json, PackageArtifactOrigin,
    PackageCheckerMode, PackageModule, PackagePath, PackagePublishArtifactRole,
    PackageRegistryCheckerStatus, PACKAGE_PUBLISH_PLAN_PATH,
    PACKAGE_REFERENCE_SUMMARY_CACHE_LAYOUT_DIR, PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct Example<'a> {
    args: &'a [&'a str],
    success_prefix: &'a str,
    required_output: &'a [&'a str],
}

struct TestPackage {
    path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-cli-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn artifact_path(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn package_cli_smoke_examples_cover_help_json_args_and_check_mode() {
    let help = run_cli(&["package", "--help"]);
    assert_eq!(help.status.code(), Some(0));
    assert!(help.stderr.is_empty());
    let help_stdout = String::from_utf8(help.stdout).unwrap();
    assert!(help_stdout.contains("Usage: npa package <command> [options]"));
    assert!(help_stdout.contains("build-certs"));
    assert!(help_stdout.contains("publish-plan"));

    let publish_help = run_cli(&["package", "publish-plan", "--help"]);
    assert_eq!(publish_help.status.code(), Some(0));
    assert!(publish_help.stderr.is_empty());
    let publish_help_stdout = String::from_utf8(publish_help.stdout).unwrap();
    assert!(publish_help_stdout.contains("Usage: npa package publish-plan"));
    assert!(publish_help_stdout.contains("--check"));

    let unconfigured_external =
        run_cli(&["package", "verify-certs", "--checker", "external", "--json"]);
    assert_usage_failure(
        unconfigured_external,
        "package verify-certs",
        "missing_required_flag",
    );

    let package = build_basic_package("smoke-check-mode", false);
    write_publish_input_metadata(&package);
    run_publish_plan_write(&package);
    let after_write = package_file_hashes(package.path());
    let check = run_publish_plan_check_json(&package);

    assert_eq!(check.status.code(), Some(0));
    assert!(check.stderr.is_empty());
    let stdout = String::from_utf8(check.stdout).unwrap();
    assert!(stdout.starts_with(&format!(
        "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"package publish-plan\","
    )));
    assert!(stdout.contains("\"status\":\"passed\""));
    assert!(stdout.contains("\"diagnostics\":[]"));
    assert!(stdout.contains(
        "\"artifacts\":[{\"kind\":\"package_publish_plan\",\"path\":\"generated/publish-plan.json\"}]"
    ));
    assert_host_path_free(&stdout, &package);
    assert_eq!(package_file_hashes(package.path()), after_write);
}

#[test]
fn package_cli_rejects_root_qualified_export_outputs_with_stable_json() {
    let package = TestPackage::new("root-qualified-export-output");
    let marker = package.path().file_name().unwrap().to_string_lossy();
    let out = format!("npa-project-example/{marker}/generated/output.json");

    let summary = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "export-summary", "--root"])
        .arg(package.path())
        .args(["--out", &out, "--json"])
        .output()
        .unwrap();
    assert_root_qualified_output_failure(summary, &package, "package export-summary", &out);

    let candidate = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "export-candidate-metadata", "--root"])
        .arg(package.path())
        .args([
            "--module",
            "Proofs.Example",
            "--declaration",
            "theorem_name",
            "--out",
            &out,
            "--json",
        ])
        .output()
        .unwrap();
    assert_root_qualified_output_failure(
        candidate,
        &package,
        "package export-candidate-metadata",
        &out,
    );

    assert!(!package.path().join("npa-project-example").exists());
}

#[test]
fn package_cli_full_corpus_examples_pass_on_proof_corpus() {
    let examples = [
        Example {
            args: ["package", "check", "--root", "testdata/package/proofs"].as_slice(),
            success_prefix: "package check: passed\n",
            required_output: &[],
        },
        Example {
            args: [
                "package",
                "build-certs",
                "--root",
                "testdata/package/proofs",
                "--check",
            ]
            .as_slice(),
            success_prefix: "package build-certs: passed\n",
            required_output: &[],
        },
        Example {
            args: [
                "package",
                "verify-certs",
                "--root",
                "testdata/package/proofs",
                "--checker",
                "reference",
                "--audit-cache",
                "off",
            ]
            .as_slice(),
            success_prefix: "package verify-certs: passed\n",
            required_output: &["package_verified", "module_verified", "npa-checker-ref"],
        },
        Example {
            args: [
                "package",
                "check-hashes",
                "--root",
                "testdata/package/proofs",
            ]
            .as_slice(),
            success_prefix: "package check-hashes: passed\n",
            required_output: &[],
        },
    ];

    for example in examples {
        let args = example.args;
        let output = run_cli(args);

        assert_eq!(output.status.code(), Some(0), "{}", args.join(" "));
        assert!(output.stderr.is_empty(), "{}", args.join(" "));
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.starts_with(example.success_prefix),
            "{}",
            args.join(" ")
        );
        for required in example.required_output {
            assert!(
                stdout.contains(required),
                "{} missing {required}",
                args.join(" ")
            );
        }
    }
}

#[test]
fn package_cli_source_free_verify_succeeds_without_source_replay_or_meta() {
    let package = build_basic_package("source-free", false);
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Basic/replay.json")
        .exists());
    assert!(!package.artifact_path("Proofs/Ai/Basic/meta.json").exists());

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--root"])
        .arg(package.path())
        .args(["--checker", "reference", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_json_envelope(&stdout, "package verify-certs", "passed");
    assert!(stdout.contains("\"root\":\"<absolute-root>\""));
    assert!(stdout.contains("\"kind\":\"ReferenceVerifier\""));
    assert!(stdout.contains("\"reason_code\":\"package_verified\""));
    assert!(stdout.contains("\"reason_code\":\"module_verified\""));
    assert!(stdout.contains("\"checker\":\"npa-checker-ref\""));
    assert_host_path_free(&stdout, &package);
}

#[test]
fn package_cli_source_free_refactor_plan_succeeds_without_source_sidecars_or_export_summary() {
    let package = build_refactor_plan_metadata_package("refactor-plan-missing-sidecars", false);
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Basic/replay.json")
        .exists());
    assert!(!package.artifact_path("Proofs/Ai/Basic/meta.json").exists());
    assert!(!package
        .artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH)
        .exists());

    let output = run_refactor_plan_json(&package, &[]);

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_json_envelope(&stdout, "package refactor-plan", "passed");
    assert!(stdout.contains("\"reason_code\":\"refactor_plan_summary\""));
    assert!(stdout.contains("theorem_index_status=missing"));
    assert!(stdout.contains("certificate_metadata_unavailable"));
    assert!(stdout.contains("\"root\":\"<absolute-root>\""));
    assert_host_path_free(&stdout, &package);
}

#[test]
fn package_cli_source_free_refactor_plan_output_ignores_source_only_changes() {
    let package = build_basic_package("refactor-plan-source-drift", true);
    let before = run_refactor_plan_success_stdout(&package, &[]);

    fs::write(
        package.artifact_path("Proofs/Ai/Basic/source.npa"),
        b"source-only bytes that must not affect refactor-plan",
    )
    .unwrap();
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/replay.json"),
        b"{\"source_only\":true}",
    )
    .unwrap();
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/meta.json"),
        b"{\"source_only\":true}",
    )
    .unwrap();
    write_file(
        package.artifact_path("Proofs/Ai/Basic/tactic-trace.json"),
        "{\"source_only\":true}",
    );
    write_file(
        package.artifact_path("Proofs/Ai/Basic/ai-trace.json"),
        "{\"source_only\":true}",
    );

    let after = run_refactor_plan_success_stdout(&package, &[]);

    assert_eq!(after, before);
}

#[test]
fn package_cli_source_free_refactor_plan_ignores_forbidden_sidecar_sentinels() {
    let package = build_basic_package("refactor-plan-sidecar-sentinels", false);
    write_directory(package.artifact_path("Proofs/Ai/Basic/source.npa"));
    write_directory(package.artifact_path("Proofs/Ai/Basic/replay.json"));
    write_directory(package.artifact_path("Proofs/Ai/Basic/meta.json"));
    write_directory(package.artifact_path("Proofs/Ai/Basic/tactic-trace.json"));
    write_directory(package.artifact_path("Proofs/Ai/Basic/ai-trace.json"));
    write_directory(package.artifact_path(PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH));

    let output = run_refactor_plan_json(&package, &[]);

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_json_envelope(&stdout, "package refactor-plan", "passed");
    assert!(stdout.contains("\"reason_code\":\"refactor_plan_summary\""));
    assert!(!stdout.contains("source.npa"));
    assert!(!stdout.contains("replay.json"));
    assert!(!stdout.contains("meta.json"));
    assert!(!stdout.contains("tactic-trace"));
    assert!(!stdout.contains("ai-trace"));
    assert!(!stdout.contains("verified-export-summary"));
    assert_host_path_free(&stdout, &package);
}

#[test]
fn package_cli_source_free_refactor_plan_negative_diagnostics_are_sanitized() {
    let malformed = build_refactor_plan_metadata_package("refactor-plan-malformed-index", true);
    let theorem_index_path = malformed.artifact_path(PACKAGE_THEOREM_INDEX_PATH);
    let mut theorem_index_source = fs::read_to_string(&theorem_index_path).unwrap();
    theorem_index_source.push('\n');
    fs::write(theorem_index_path, theorem_index_source).unwrap();
    let malformed_output = run_refactor_plan_json(&malformed, &[]);
    assert_eq!(malformed_output.status.code(), Some(1));
    assert!(malformed_output.stderr.is_empty());
    let malformed_stdout = String::from_utf8(malformed_output.stdout).unwrap();
    assert_json_envelope(&malformed_stdout, "package refactor-plan", "failed");
    assert!(malformed_stdout.contains("\"kind\":\"TheoremIndex\""));
    assert!(malformed_stdout.contains("\"reason_code\":\"refactor_plan_theorem_index_invalid\""));
    assert!(malformed_stdout.contains("\"path\":\"generated/theorem-index.json\""));
    assert!(malformed_stdout.contains("\"actual_value\":\"non_canonical_order\""));
    assert_host_path_free(&malformed_stdout, &malformed);

    let unknown = build_refactor_plan_metadata_package("refactor-plan-unknown-module", false);
    let unknown_output = run_refactor_plan_json(&unknown, &["--module", "Proofs.Ai.Missing"]);
    assert_eq!(unknown_output.status.code(), Some(1));
    assert!(unknown_output.stderr.is_empty());
    let unknown_stdout = String::from_utf8(unknown_output.stdout).unwrap();
    assert_json_envelope(&unknown_stdout, "package refactor-plan", "failed");
    assert!(unknown_stdout.contains("\"kind\":\"PackageLock\""));
    assert!(unknown_stdout.contains("\"reason_code\":\"refactor_plan_module_unknown\""));
    assert!(unknown_stdout.contains("\"module\":\"Proofs.Ai.Missing\""));
    assert_host_path_free(&unknown_stdout, &unknown);

    let external = build_refactor_plan_metadata_package("refactor-plan-external-module", false);
    let external_output = run_refactor_plan_json(&external, &["--module", "Std.Logic.Eq"]);
    assert_eq!(external_output.status.code(), Some(1));
    assert!(external_output.stderr.is_empty());
    let external_stdout = String::from_utf8(external_output.stdout).unwrap();
    assert_json_envelope(&external_stdout, "package refactor-plan", "failed");
    assert!(external_stdout.contains("\"kind\":\"PackageLock\""));
    assert!(external_stdout.contains("\"reason_code\":\"refactor_plan_module_not_local\""));
    assert!(external_stdout.contains("\"module\":\"Std.Logic.Eq\""));
    assert_host_path_free(&external_stdout, &external);
}

#[test]
fn package_cli_source_free_refactor_plan_theorem_family_output_uses_family_signals_only() {
    let package = build_refactor_plan_metadata_package("refactor-plan-theorem-family", true);

    let stdout = run_refactor_plan_success_stdout(
        &package,
        &["--scope", "theorems", "--module", "Proofs.Ai.EqReasoning"],
    );

    assert!(stdout.contains("\"reason_code\":\"refactor_plan_theorem_family_candidate\""));
    assert!(stdout
        .contains("evidence=large_theorem_family,shared_name_prefix,statement_constant_signal"));
    assert!(!stdout.contains("proof-dependent"));
    assert!(!stdout.contains("proof_dependent"));
    assert_host_path_free(&stdout, &package);
}

#[test]
fn package_publish_inputs_collects_manifest_generated_metadata_and_reference_summaries() {
    let package = build_basic_package("publish-inputs", false);
    write_publish_input_metadata(&package);

    let loaded = load_package_publish_inputs(package.path()).unwrap();

    assert_eq!(
        loaded.validated.manifest().package.as_str(),
        "fixture-package"
    );
    assert_eq!(loaded.manifest.path.as_str(), PACKAGE_MANIFEST_PATH);
    assert_eq!(loaded.package_lock.path.as_str(), LOCK_PATH);
    assert_eq!(
        loaded.axiom_report_file.path.as_str(),
        PACKAGE_AXIOM_REPORT_PATH
    );
    assert_eq!(
        loaded.theorem_index_file.path.as_str(),
        PACKAGE_THEOREM_INDEX_PATH
    );
    assert_eq!(loaded.certificate_files.len(), 1);
    assert_eq!(
        loaded.reference_verification_report.verdict_source.as_str(),
        "npa-checker-ref"
    );
    assert!(
        loaded
            .reference_verification_report
            .reference_checker_verdict
    );

    let reference_summary = loaded
        .checker_summaries
        .iter()
        .find(|summary| summary.mode == PackageCheckerMode::Reference)
        .expect("collector records reference checker summary");
    assert_eq!(reference_summary.checker, "npa-checker-ref");
    assert_eq!(reference_summary.profile, "npa.checker.reference.v0.1");
    assert_eq!(reference_summary.status, "passed");
    assert!(loaded
        .checker_summaries
        .iter()
        .filter(|summary| summary.mode == PackageCheckerMode::Fast)
        .all(|summary| summary.checker != "npa-checker-ref"));
}

#[test]
fn package_publish_inputs_rejects_stale_lock_metadata_certificate_and_checker_summaries() {
    let stale_lock = build_basic_package("publish-stale-lock", false);
    write_publish_input_metadata(&stale_lock);
    let lock_path = stale_lock.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(&lock_path, lock_source).unwrap();
    assert_command_result_failure(
        load_package_publish_inputs(stale_lock.path()).unwrap_err(),
        "HashMismatch",
        "package_lock_stale",
    );

    let stale_axiom = build_basic_package("publish-stale-axiom", false);
    write_publish_input_metadata(&stale_axiom);
    rewrite_axiom_report_status(&stale_axiom, "failed");
    assert_command_result_failure(
        load_package_publish_inputs(stale_axiom.path()).unwrap_err(),
        "AxiomReport",
        "axiom_report_stale",
    );

    let stale_index = build_basic_package("publish-stale-index", false);
    write_publish_input_metadata(&stale_index);
    rewrite_theorem_index_status(&stale_index, "failed");
    assert_command_result_failure(
        load_package_publish_inputs(stale_index.path()).unwrap_err(),
        "TheoremIndex",
        "theorem_index_stale",
    );

    let stale_certificate = build_basic_package("publish-stale-certificate", false);
    write_publish_input_metadata(&stale_certificate);
    fs::copy(
        repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"),
        stale_certificate.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
    )
    .unwrap();
    assert_command_result_failure(
        load_package_publish_inputs(stale_certificate.path()).unwrap_err(),
        "HashMismatch",
        "certificate_file_hash_mismatch",
    );

    let valid = build_basic_package("publish-summary-validation", false);
    write_publish_input_metadata(&valid);
    let loaded = load_package_publish_inputs(valid.path()).unwrap();

    let mut missing_reference = loaded.checker_summaries.clone();
    missing_reference.retain(|summary| summary.mode != PackageCheckerMode::Reference);
    let missing = validate_publish_checker_summaries(
        &loaded.package_lock_manifest,
        &loaded.validated.manifest().checker_profile,
        &missing_reference,
    )
    .unwrap_err();
    assert_eq!(missing.kind.as_str(), "ReferenceVerifier");
    assert_eq!(missing.reason_code, "checker_summary_missing");

    let mut rejected = loaded.checker_summaries.clone();
    rejected
        .iter_mut()
        .find(|summary| summary.mode == PackageCheckerMode::Reference)
        .unwrap()
        .status = "failed".to_owned();
    let rejected = validate_publish_checker_summaries(
        &loaded.package_lock_manifest,
        &loaded.validated.manifest().checker_profile,
        &rejected,
    )
    .unwrap_err();
    assert_eq!(rejected.kind.as_str(), "ReferenceVerifier");
    assert_eq!(rejected.reason_code, "checker_summary_stale");
    assert_eq!(rejected.field.as_deref(), Some("status"));

    let mut mislabeled_fast = loaded.checker_summaries.clone();
    mislabeled_fast
        .iter_mut()
        .find(|summary| summary.mode == PackageCheckerMode::Fast)
        .unwrap()
        .checker = "npa-checker-ref".to_owned();
    let mislabeled = validate_publish_checker_summaries(
        &loaded.package_lock_manifest,
        &loaded.validated.manifest().checker_profile,
        &mislabeled_fast,
    )
    .unwrap_err();
    assert_eq!(mislabeled.kind.as_str(), "ReferenceVerifier");
    assert_eq!(mislabeled.reason_code, "checker_summary_stale");
    assert_eq!(mislabeled.field.as_deref(), Some("mode"));
}

#[test]
fn package_publish_artifact_hashes_match_release_files_and_checksum_policy() {
    let package = build_basic_package("publish-artifact-hashes", false);
    write_publish_input_metadata(&package);

    let loaded = load_package_publish_inputs(package.path()).unwrap();
    let artifacts = collect_package_publish_artifacts(&loaded).unwrap();

    assert_eq!(artifacts.len(), 5);
    assert!(!artifacts
        .iter()
        .any(|artifact| artifact.path.as_str() == PACKAGE_PUBLISH_PLAN_PATH));
    assert!(artifacts
        .iter()
        .any(|artifact| artifact.role == PackagePublishArtifactRole::PackageManifest));
    assert!(artifacts
        .iter()
        .any(|artifact| artifact.role == PackagePublishArtifactRole::PackageLock));
    assert!(artifacts
        .iter()
        .any(|artifact| artifact.role == PackagePublishArtifactRole::AxiomReport));
    assert!(artifacts
        .iter()
        .any(|artifact| artifact.role == PackagePublishArtifactRole::TheoremIndex));

    let certificate = artifacts
        .iter()
        .find(|artifact| artifact.role == PackagePublishArtifactRole::LocalCertificate)
        .unwrap();
    assert_eq!(
        certificate.module.as_ref().unwrap().as_dotted(),
        "Proofs.Ai.Basic"
    );
    assert_eq!(certificate.origin, Some(PackageArtifactOrigin::Local));

    for artifact in &artifacts {
        let bytes = fs::read(package.artifact_path(artifact.path.as_str())).unwrap();
        assert_eq!(
            artifact.file_hash,
            package_file_hash(&bytes),
            "{}",
            artifact.path.as_str()
        );
    }

    let keys = artifacts
        .iter()
        .map(|artifact| {
            format!(
                "{}|{}|{}",
                artifact.role.as_str(),
                artifact
                    .module
                    .as_ref()
                    .map(|module| module.as_dotted())
                    .unwrap_or_default(),
                artifact.path.as_str()
            )
        })
        .collect::<Vec<_>>();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted);

    let policy = checksum_only_signature_policy();
    assert_eq!(policy.mode, "checksum-only");
    assert_eq!(policy.hash_algorithm, "sha256");
    assert!(!policy.signature_required);
    assert!(policy.signatures.is_empty());
}

#[test]
fn package_publish_registry_entries_link_artifacts_imports_and_checker_results() {
    let package = build_basic_package("publish-registry-entries", false);
    write_publish_input_metadata(&package);

    let loaded = load_package_publish_inputs(package.path()).unwrap();
    let entries = collect_package_publish_registry_entries(&loaded).unwrap();

    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(entry.schema, "npa.registry.module.v0.1");
    assert_eq!(entry.package.as_str(), "fixture-package");
    assert_eq!(entry.package_version.as_str(), "0.1.0");
    assert_eq!(entry.module.as_dotted(), "Proofs.Ai.Basic");
    assert_eq!(entry.core_spec, loaded.validated.manifest().core_spec);
    assert_eq!(
        entry.kernel_profile,
        loaded.validated.manifest().kernel_profile
    );
    assert_eq!(
        entry.certificate_format,
        loaded.validated.manifest().certificate_format
    );
    assert!(entry.imports.is_empty());
    assert_eq!(
        entry.artifact_hashes.package_lock_file_hash,
        loaded.package_lock.file_hash
    );
    assert_eq!(
        entry.artifact_hashes.axiom_report_file_hash,
        loaded.axiom_report_file.file_hash
    );
    assert_eq!(
        entry.artifact_hashes.theorem_index_file_hash,
        loaded.theorem_index_file.file_hash
    );

    let reference = entry
        .checker_results
        .iter()
        .find(|result| result.mode == "reference")
        .expect("reference checker result is published");
    assert_eq!(reference.checker, "npa-checker-ref");
    assert_eq!(reference.profile, "npa.checker.reference.v0.1");
    assert_eq!(reference.status, PackageRegistryCheckerStatus::Accepted);
    assert_eq!(reference.export_hash, entry.export_hash);
    assert_eq!(reference.certificate_hash, entry.certificate_hash);
    assert_eq!(reference.axiom_report_hash, entry.axiom_report_hash);

    let mut missing_reference = loaded.clone();
    missing_reference
        .checker_summaries
        .retain(|summary| summary.mode != PackageCheckerMode::Reference);
    let missing = collect_package_publish_registry_entries(&missing_reference).unwrap_err();
    assert_command_result_failure(missing, "GeneratedArtifact", "missing_field");

    let mut stale_reference = loaded;
    stale_reference
        .checker_summaries
        .iter_mut()
        .find(|summary| summary.mode == PackageCheckerMode::Reference)
        .unwrap()
        .export_hash = package_file_hash(b"stale registry checker summary");
    let stale = collect_package_publish_registry_entries(&stale_reference).unwrap_err();
    assert_command_result_failure(stale, "GeneratedArtifact", "invalid_enum_value");
}

#[test]
fn package_publish_downstream_import_bundle_exports_import_ready_modules() {
    let package = build_basic_package("publish-downstream-import-bundle", false);
    write_publish_input_metadata(&package);

    let loaded = load_package_publish_inputs(package.path()).unwrap();
    let registry_entries = collect_package_publish_registry_entries(&loaded).unwrap();
    let bundle = collect_package_publish_downstream_import_bundle(&loaded).unwrap();

    assert_eq!(bundle.package.as_str(), "fixture-package");
    assert_eq!(bundle.version.as_str(), "0.1.0");
    assert_eq!(bundle.modules.len(), 1);
    let module = &bundle.modules[0];
    let registry_entry = &registry_entries[0];
    assert_eq!(module.module.as_dotted(), "Proofs.Ai.Basic");
    assert_eq!(module.package, registry_entry.package);
    assert_eq!(module.version, registry_entry.package_version);
    assert_eq!(module.export_hash, registry_entry.export_hash);
    assert_eq!(module.certificate_hash, registry_entry.certificate_hash);
    assert_eq!(module.axiom_report_hash, registry_entry.axiom_report_hash);
    assert_eq!(module.certificate, registry_entry.certificate.path);
    assert_eq!(
        module.certificate_file_hash,
        registry_entry.certificate.file_hash
    );

    let downstream_manifest = format!(
        r#"schema = "npa.package.v0.1"
package = "downstream-fixture"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []

[[imports]]
module = "{}"
package = "{}"
version = "{}"
certificate = "{}"
export_hash = "{}"
certificate_hash = "{}"

[[modules]]
module = "Downstream.UsesBasic"
source = "Downstream/UsesBasic/source.npa"
certificate = "Downstream/UsesBasic/certificate.npcert"
imports = ["{}"]
expected_source_hash = "{}"
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
definitions = []
theorems = []
axioms = []
"#,
        module.module.as_dotted(),
        module.package.as_str(),
        module.version.as_str(),
        module.certificate.as_str(),
        format_package_hash(&module.export_hash),
        format_package_hash(&module.certificate_hash),
        module.module.as_dotted(),
        format_package_hash(&package_file_hash(b"downstream source placeholder")),
        format_package_hash(&package_file_hash(b"downstream certificate placeholder")),
        format_package_hash(&package_file_hash(b"downstream export placeholder")),
        format_package_hash(&package_file_hash(b"downstream axiom placeholder")),
        format_package_hash(&package_file_hash(
            b"downstream certificate hash placeholder"
        )),
    );
    let validated = parse_and_validate_manifest_str(&downstream_manifest).unwrap();
    let copied_import = &validated.manifest().imports.as_ref().unwrap()[0];
    assert_eq!(copied_import.module, module.module);
    assert_eq!(copied_import.package, module.package);
    assert_eq!(copied_import.version, module.version);
    assert_eq!(copied_import.certificate, module.certificate);
    assert_eq!(copied_import.export_hash, module.export_hash);
    assert_eq!(copied_import.certificate_hash, module.certificate_hash);
}

#[test]
fn package_publish_plan_check_write_and_registry_mismatch_diagnostics() {
    let package = build_basic_package("publish-plan", false);
    write_publish_input_metadata(&package);
    let publish_plan_path = package.artifact_path(PACKAGE_PUBLISH_PLAN_PATH);
    assert!(!publish_plan_path.exists());

    let missing_check = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .args(["--check", "--json"])
        .output()
        .unwrap();
    assert_json_failure(
        missing_check,
        &package,
        1,
        "package publish-plan",
        "GeneratedArtifact",
        "publish_plan_missing",
    );
    assert!(!publish_plan_path.exists());

    let before_write = package_file_hashes(package.path());
    let write = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .output()
        .unwrap();
    assert_eq!(write.status.code(), Some(0));
    assert!(write.stderr.is_empty());
    let stdout = String::from_utf8(write.stdout).unwrap();
    assert!(stdout.starts_with("package publish-plan: passed\n"));

    let publish_plan_bytes = fs::read(&publish_plan_path).unwrap();
    let publish_plan_json = String::from_utf8(publish_plan_bytes.clone()).unwrap();
    let publish_plan = parse_package_publish_plan_json(&publish_plan_json).unwrap();
    assert_eq!(publish_plan.package.as_str(), "fixture-package");
    assert_eq!(publish_plan.module_registry_entries.len(), 1);
    assert_eq!(publish_plan.downstream_import_bundle.modules.len(), 1);

    let mut expected_after_write = before_write;
    expected_after_write.insert(
        PACKAGE_PUBLISH_PLAN_PATH.to_owned(),
        package_file_hash(&publish_plan_bytes),
    );
    assert_eq!(package_file_hashes(package.path()), expected_after_write);

    let second_write = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .output()
        .unwrap();
    assert_eq!(second_write.status.code(), Some(0));
    assert!(second_write.stderr.is_empty());
    assert_eq!(package_file_hashes(package.path()), expected_after_write);

    let before_success_check = package_file_hashes(package.path());
    let check_json = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .args(["--check", "--json"])
        .output()
        .unwrap();
    assert_eq!(check_json.status.code(), Some(0));
    assert!(check_json.stderr.is_empty());
    let stdout = String::from_utf8(check_json.stdout).unwrap();
    assert!(stdout.starts_with(&format!(
        "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"package publish-plan\","
    )));
    assert!(stdout.contains("\"status\":\"passed\""));
    assert!(stdout.contains("\"artifacts\":[{\"kind\":\"package_publish_plan\""));
    assert!(stdout.contains("\"schema\":\"npa.package.command_result.v0.3\""));
    assert_host_path_free(&stdout, &package);
    assert_eq!(package_file_hashes(package.path()), before_success_check);

    let mut stale_plan = publish_plan.clone();
    stale_plan.release.checker_profile = "npa.checker.reference.v0.1.stale".to_owned();
    let stale_plan = stale_plan.with_computed_hash().unwrap();
    fs::write(&publish_plan_path, stale_plan.canonical_json().unwrap()).unwrap();
    let stale_plan_check = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .args(["--check"])
        .output()
        .unwrap();
    assert_eq!(stale_plan_check.status.code(), Some(1));
    assert!(stale_plan_check.stdout.is_empty());
    let stderr = String::from_utf8(stale_plan_check.stderr).unwrap();
    assert!(stderr.starts_with("package publish-plan: failed\n"));
    assert!(stderr
        .contains("error GeneratedArtifact publish_plan_stale path=generated/publish-plan.json"));
    assert!(stderr.contains("expected_hash=sha256:"));
    assert!(stderr.contains("actual_hash=sha256:"));
    fs::write(&publish_plan_path, publish_plan_json.as_bytes()).unwrap();

    let mut stale_registry = publish_plan;
    let stale_hash = package_file_hash(b"stale registry export hash");
    let stale_module = stale_registry.module_registry_entries[0].module.clone();
    stale_registry.module_registry_entries[0].export_hash = stale_hash;
    for result in &mut stale_registry.module_registry_entries[0].checker_results {
        result.export_hash = stale_hash;
    }
    stale_registry.downstream_import_bundle.modules[0].export_hash = stale_hash;
    for summary in stale_registry
        .checker_summaries
        .iter_mut()
        .filter(|summary| summary.module == stale_module)
    {
        summary.export_hash = stale_hash;
    }
    for summary in &mut stale_registry.downstream_import_bundle.modules[0].checker_summaries {
        summary.export_hash = stale_hash;
    }
    let stale_registry = stale_registry.with_computed_hash().unwrap();
    fs::write(&publish_plan_path, stale_registry.canonical_json().unwrap()).unwrap();
    let stale_check = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .args(["--check", "--json"])
        .output()
        .unwrap();
    assert_json_failure(
        stale_check,
        &package,
        1,
        "package publish-plan",
        "GeneratedArtifact",
        "registry_entry_mismatch",
    );
}

#[test]
fn package_cli_full_corpus_publish_plan_proof_corpus_check_mode_succeeds_with_checked_in_artifact()
{
    let publish_plan_path = repo_root()
        .join("testdata/package/proofs")
        .join(PACKAGE_PUBLISH_PLAN_PATH);
    let before = fs::read(&publish_plan_path).unwrap();

    let output = run_cli(&[
        "package",
        "publish-plan",
        "--root",
        "testdata/package/proofs",
        "--check",
        "--json",
    ]);

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with(&format!(
        "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"package publish-plan\","
    )));
    assert!(stdout.contains("\"root\":\"testdata/package/proofs\""));
    assert!(stdout.contains("\"status\":\"passed\""));
    assert!(stdout.contains("\"diagnostics\":[]"));
    assert!(stdout.contains(
        "\"artifacts\":[{\"kind\":\"package_publish_plan\",\"path\":\"generated/publish-plan.json\"}]"
    ));
    assert_eq!(fs::read(&publish_plan_path).unwrap(), before);
}

#[test]
fn package_publish_plan_cli_rejects_stale_inputs_and_checked_plan_metadata() {
    let stale_lock = build_basic_package("publish-plan-cli-stale-lock", false);
    write_publish_input_metadata(&stale_lock);
    let lock_path = stale_lock.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(&lock_path, lock_source).unwrap();
    assert_json_failure(
        run_publish_plan_check_json(&stale_lock),
        &stale_lock,
        1,
        "package publish-plan",
        "HashMismatch",
        "package_lock_stale",
    );

    let stale_axiom = build_basic_package("publish-plan-cli-stale-axiom", false);
    write_publish_input_metadata(&stale_axiom);
    rewrite_axiom_report_status(&stale_axiom, "failed");
    assert_json_failure(
        run_publish_plan_check_json(&stale_axiom),
        &stale_axiom,
        1,
        "package publish-plan",
        "AxiomReport",
        "axiom_report_stale",
    );

    let stale_index = build_basic_package("publish-plan-cli-stale-index", false);
    write_publish_input_metadata(&stale_index);
    rewrite_theorem_index_status(&stale_index, "failed");
    assert_json_failure(
        run_publish_plan_check_json(&stale_index),
        &stale_index,
        1,
        "package publish-plan",
        "TheoremIndex",
        "theorem_index_stale",
    );

    let stale_certificate = build_basic_package("publish-plan-cli-stale-certificate", false);
    write_publish_input_metadata(&stale_certificate);
    fs::copy(
        repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"),
        stale_certificate.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
    )
    .unwrap();
    assert_json_failure(
        run_publish_plan_check_json(&stale_certificate),
        &stale_certificate,
        1,
        "package publish-plan",
        "HashMismatch",
        "certificate_file_hash_mismatch",
    );

    let checked_plan = build_basic_package("publish-plan-cli-schema", false);
    write_publish_input_metadata(&checked_plan);
    run_publish_plan_write(&checked_plan);
    let publish_plan_path = checked_plan.artifact_path(PACKAGE_PUBLISH_PLAN_PATH);
    let canonical = fs::read_to_string(&publish_plan_path).unwrap();

    assert_mutated_publish_plan_check_failure(
        &checked_plan,
        canonical.replacen(
            "npa.registry.module.v0.1",
            "npa.independent-checker.checker_binary_registry.v1",
            1,
        ),
        "unsupported_schema",
    );
    assert_mutated_publish_plan_check_failure(
        &checked_plan,
        canonical.replacen(
            r#""version":"0.1.0","release":"#,
            r#""version":"latest","release":"#,
            1,
        ),
        "invalid_version",
    );
    assert_mutated_publish_plan_check_failure(
        &checked_plan,
        canonical.replacen(
            r#""artifact_hashes":"#,
            r#""registry_url":"https://registry.example/modules","artifact_hashes":"#,
            1,
        ),
        "unknown_field",
    );
}

#[test]
fn package_publish_plan_reference_cache_hits_and_delete_preserve_verdict() {
    let _guard = reference_summary_cache_test_lock();
    clear_reference_summary_cache();
    let package = build_basic_package("publish-plan-reference-cache", false);
    write_publish_input_metadata(&package);
    run_publish_plan_write(&package);

    let first = run_publish_plan_check_json_with_timings(&package);
    assert_eq!(first.status.code(), Some(0));
    assert!(first.stderr.is_empty());
    let first_stdout = String::from_utf8(first.stdout).unwrap();
    assert!(first_stdout.contains("\"reason_code\":\"reference_summary_cache_summary\""));
    assert!(first_stdout.contains("mode=reference-summary-cache"));
    assert!(first_stdout.contains("hits=0"));
    assert!(first_stdout.contains("misses=1"));
    assert!(first_stdout.contains("written=1"));
    assert!(first_stdout.contains("live_checked=1"));
    assert!(first_stdout.contains("cached=0"));
    assert!(first_stdout.contains("trusted=false"));
    assert!(first_stdout.contains("proof_evidence=false"));
    assert_host_path_free(&first_stdout, &package);

    let second = run_publish_plan_check_json_with_timings(&package);
    assert_eq!(second.status.code(), Some(0));
    assert!(second.stderr.is_empty());
    let second_stdout = String::from_utf8(second.stdout).unwrap();
    assert!(second_stdout.contains("hits=1"));
    assert!(second_stdout.contains("misses=0"));
    assert!(second_stdout.contains("written=0"));
    assert!(second_stdout.contains("live_checked=0"));
    assert!(second_stdout.contains("cached=1"));
    assert!(second_stdout.contains("proof_evidence=false"));

    clear_reference_summary_cache();
    let after_delete = run_publish_plan_check_json_with_timings(&package);
    assert_eq!(after_delete.status.code(), Some(0));
    assert!(after_delete.stderr.is_empty());
    let after_delete_stdout = String::from_utf8(after_delete.stdout).unwrap();
    assert!(after_delete_stdout.contains("hits=0"));
    assert!(after_delete_stdout.contains("misses=1"));
    assert!(after_delete_stdout.contains("live_checked=1"));
}

#[test]
fn package_publish_plan_reference_cache_rejects_stale_inputs_before_cache_use() {
    let _guard = reference_summary_cache_test_lock();
    clear_reference_summary_cache();

    let stale_lock = build_basic_package("publish-plan-reference-cache-stale-lock", false);
    write_publish_input_metadata(&stale_lock);
    run_publish_plan_write(&stale_lock);
    assert_eq!(
        run_publish_plan_check_json_with_timings(&stale_lock)
            .status
            .code(),
        Some(0)
    );
    let lock_path = stale_lock.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(&lock_path, lock_source).unwrap();
    assert_json_failure_with_timings(
        run_publish_plan_check_json_with_timings(&stale_lock),
        &stale_lock,
        1,
        "package publish-plan",
        "HashMismatch",
        "package_lock_stale",
    );

    let stale_axiom = build_basic_package("publish-plan-reference-cache-stale-axiom", false);
    write_publish_input_metadata(&stale_axiom);
    run_publish_plan_write(&stale_axiom);
    assert_eq!(
        run_publish_plan_check_json_with_timings(&stale_axiom)
            .status
            .code(),
        Some(0)
    );
    rewrite_axiom_report_status(&stale_axiom, "failed");
    assert_json_failure_with_timings(
        run_publish_plan_check_json_with_timings(&stale_axiom),
        &stale_axiom,
        1,
        "package publish-plan",
        "AxiomReport",
        "axiom_report_stale",
    );

    let stale_index = build_basic_package("publish-plan-reference-cache-stale-index", false);
    write_publish_input_metadata(&stale_index);
    run_publish_plan_write(&stale_index);
    assert_eq!(
        run_publish_plan_check_json_with_timings(&stale_index)
            .status
            .code(),
        Some(0)
    );
    rewrite_theorem_index_status(&stale_index, "failed");
    assert_json_failure_with_timings(
        run_publish_plan_check_json_with_timings(&stale_index),
        &stale_index,
        1,
        "package publish-plan",
        "TheoremIndex",
        "theorem_index_stale",
    );

    let stale_certificate =
        build_basic_package("publish-plan-reference-cache-stale-certificate", false);
    write_publish_input_metadata(&stale_certificate);
    run_publish_plan_write(&stale_certificate);
    assert_eq!(
        run_publish_plan_check_json_with_timings(&stale_certificate)
            .status
            .code(),
        Some(0)
    );
    fs::copy(
        repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"),
        stale_certificate.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
    )
    .unwrap();
    assert_json_failure_with_timings(
        run_publish_plan_check_json_with_timings(&stale_certificate),
        &stale_certificate,
        1,
        "package publish-plan",
        "HashMismatch",
        "certificate_file_hash_mismatch",
    );
}

#[test]
fn package_publish_plan_write_mode_is_source_free_with_unreadable_sidecars() {
    let package = build_basic_package("publish-plan-source-free-cli", false);
    write_publish_input_metadata(&package);
    let module = proof_basic_module();
    write_directory(package.artifact_path(module.source.as_str()));
    if let Some(replay) = &module.replay {
        write_directory(package.artifact_path(replay.as_str()));
    }
    if let Some(meta) = &module.meta {
        write_directory(package.artifact_path(meta.as_str()));
    }
    write_directory(package.artifact_path("ai/trace.json"));
    write_directory(package.artifact_path("registry/cache.json"));

    run_publish_plan_write(&package);
    let after_write = package_file_hashes(package.path());
    let check = run_publish_plan_check_json(&package);
    assert_eq!(check.status.code(), Some(0));
    assert!(check.stderr.is_empty());
    assert_eq!(package_file_hashes(package.path()), after_write);
}

#[test]
fn package_publish_source_free_boundary_ignores_source_replay_meta_ai_and_publish_plan() {
    let package = build_basic_package("publish-source-free", false);
    write_publish_input_metadata(&package);
    let module = proof_basic_module();
    write_directory(package.artifact_path(module.source.as_str()));
    if let Some(replay) = &module.replay {
        write_directory(package.artifact_path(replay.as_str()));
    }
    if let Some(meta) = &module.meta {
        write_directory(package.artifact_path(meta.as_str()));
    }
    write_directory(package.artifact_path("generated/publish-plan.json"));
    write_directory(package.artifact_path("ai/trace.json"));

    let loaded = load_package_publish_inputs(package.path()).unwrap();

    assert_eq!(loaded.artifact_extraction.verified_modules.len(), 1);
    assert!(package
        .artifact_path("generated/publish-plan.json")
        .is_dir());
}

#[test]
fn package_cli_temp_fixture_rejects_invalid_manifest() {
    let package = TestPackage::new("invalid-manifest");
    fs::write(package.artifact_path(PACKAGE_MANIFEST_PATH), "schema = ").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check", "--root"])
        .arg(package.path())
        .arg("--json")
        .output()
        .unwrap();

    assert_json_failure(
        output,
        &package,
        1,
        "package check",
        "PackageManifest",
        "invalid_toml",
    );
}

#[test]
fn package_cli_temp_fixture_rejects_stale_source_certificate_and_lock() {
    let stale_source = build_basic_package("stale-source", true);
    fs::write(
        stale_source.artifact_path("Proofs/Ai/Basic/source.npa"),
        b"changed source bytes",
    )
    .unwrap();
    let stale_source_output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check-hashes", "--root"])
        .arg(stale_source.path())
        .arg("--json")
        .output()
        .unwrap();
    assert_json_failure(
        stale_source_output,
        &stale_source,
        1,
        "package check-hashes",
        "HashMismatch",
        "source_hash_mismatch",
    );

    let stale_certificate = build_basic_package("stale-certificate", true);
    fs::copy(
        repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"),
        stale_certificate.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
    )
    .unwrap();
    let stale_certificate_output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "check-hashes", "--root"])
        .arg(stale_certificate.path())
        .arg("--json")
        .output()
        .unwrap();
    assert_json_failure(
        stale_certificate_output,
        &stale_certificate,
        1,
        "package check-hashes",
        "HashMismatch",
        "certificate_file_hash_mismatch",
    );

    let stale_lock = build_basic_package("stale-lock", false);
    let lock_path = stale_lock.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(&lock_path, lock_source).unwrap();
    let stale_lock_output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--root"])
        .arg(stale_lock.path())
        .args(["--checker", "reference", "--json"])
        .output()
        .unwrap();
    assert_json_failure(
        stale_lock_output,
        &stale_lock,
        1,
        "package verify-certs",
        "HashMismatch",
        "package_lock_stale",
    );
}

#[test]
fn package_cli_usage_failures_return_exit_two() {
    let unconfigured_external =
        run_cli(&["package", "verify-certs", "--checker", "external", "--json"]);
    assert_usage_failure(
        unconfigured_external,
        "package verify-certs",
        "missing_required_flag",
    );

    for flag in ["--latest", "--network", "--upload", "--sign"] {
        let unsupported = run_cli(&["package", "publish-plan", flag, "--json"]);
        assert_usage_failure(unsupported, "package publish-plan", "unsupported_flag");
    }

    let unsupported_flag = run_cli(&["package", "check", "--changed", "--json"]);
    assert_usage_failure(unsupported_flag, "package check", "unsupported_flag");
}

fn build_basic_package(label: &str, include_source_sidecars: bool) -> TestPackage {
    let package = TestPackage::new(label);
    let module = proof_basic_module();
    assert!(module.imports.is_empty());
    copy_artifact(&package, module.certificate.as_str());
    if include_source_sidecars {
        copy_artifact(&package, module.source.as_str());
        if let Some(replay) = &module.replay {
            copy_artifact(&package, replay.as_str());
        }
        if let Some(meta) = &module.meta {
            copy_artifact(&package, meta.as_str());
        }
    }

    let manifest_source = basic_manifest(&module);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_refactor_plan_metadata_package(label: &str, include_theorem_index: bool) -> TestPackage {
    let package = TestPackage::new(label);
    copy_artifact(&package, PACKAGE_MANIFEST_PATH);
    copy_artifact(&package, LOCK_PATH);
    if include_theorem_index {
        copy_artifact(&package, PACKAGE_THEOREM_INDEX_PATH);
    }
    package
}

fn basic_manifest(module: &PackageModule) -> String {
    let mut source = format!(
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = ["Eq.rec"]

[[modules]]
module = "{}"
source = "{}"
certificate = "{}"
"#,
        module.module.as_dotted(),
        module.source.as_str(),
        module.certificate.as_str(),
    );
    if let Some(meta) = &module.meta {
        source.push_str(&format!("meta = \"{}\"\n", meta.as_str()));
    }
    if let Some(replay) = &module.replay {
        source.push_str(&format!("replay = \"{}\"\n", replay.as_str()));
    }
    source.push_str(&format!(
        r#"imports = []
expected_source_hash = "{}"
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
inductives = []
definitions = []
theorems = []
axioms = []
tags = []
"#,
        format_package_hash(&module.expected_source_hash),
        format_package_hash(&module.expected_certificate_file_hash),
        format_package_hash(&module.expected_export_hash),
        format_package_hash(&module.expected_axiom_report_hash),
        format_package_hash(&module.expected_certificate_hash),
    ));
    source
}

fn proof_basic_module() -> PackageModule {
    let source =
        fs::read_to_string(repo_root().join("testdata/package/proofs/npa-package.toml")).unwrap();
    parse_and_validate_manifest_str(&source)
        .unwrap()
        .manifest()
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == "Proofs.Ai.Basic")
        .unwrap()
        .clone()
}

fn write_lock(package: &TestPackage, manifest_source: &str) {
    let validated = parse_and_validate_manifest_str(manifest_source).unwrap();
    let lock = build_package_lock_from_package_root(
        &validated,
        package.path(),
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap();
    let lock_json = lock.canonical_json().unwrap();
    let lock_path = package.artifact_path(LOCK_PATH);
    fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
    fs::write(lock_path, lock_json).unwrap();
}

fn write_publish_input_metadata(package: &TestPackage) {
    let loaded = load_package_artifact_extraction(
        package.path(),
        "test package publish-plan metadata",
        PackageGeneratedArtifactReadMode::none(),
        PackageArtifactReferenceSummaryMode::Omit,
    )
    .unwrap();
    let axiom_report = project_package_axiom_report_from_extraction(
        &loaded.validated,
        &loaded.extraction,
        loaded.package_lock.clone(),
    )
    .unwrap();
    let theorem_index = project_package_theorem_index_from_extraction(
        &loaded.validated,
        &loaded.extraction,
        loaded.package_lock.clone(),
    )
    .unwrap();
    let theorem_premise_report = project_package_theorem_premise_report_from_extraction(
        &loaded.validated,
        &loaded.extraction,
        loaded.package_lock,
    )
    .unwrap();
    write_file(
        package.artifact_path(PACKAGE_AXIOM_REPORT_PATH),
        &axiom_report.canonical_json().unwrap(),
    );
    write_file(
        package.artifact_path(PACKAGE_THEOREM_INDEX_PATH),
        &theorem_index.canonical_json().unwrap(),
    );
    write_file(
        package.artifact_path(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
        &theorem_premise_report.canonical_json().unwrap(),
    );
}

fn rewrite_axiom_report_status(package: &TestPackage, status: &str) {
    let path = package.artifact_path(PACKAGE_AXIOM_REPORT_PATH);
    let mut report = parse_package_axiom_report_json(&fs::read_to_string(&path).unwrap()).unwrap();
    report.checker_summaries[0].status = status.to_owned();
    let report = report.with_computed_hash().unwrap();
    fs::write(path, report.canonical_json().unwrap()).unwrap();
}

fn rewrite_theorem_index_status(package: &TestPackage, status: &str) {
    let path = package.artifact_path(PACKAGE_THEOREM_INDEX_PATH);
    let mut index = parse_package_theorem_index_json(&fs::read_to_string(&path).unwrap()).unwrap();
    index.checker_summaries[0].status = status.to_owned();
    let index = index.with_computed_hash().unwrap();
    fs::write(path, index.canonical_json().unwrap()).unwrap();
}

fn write_file(path: PathBuf, contents: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, contents).unwrap();
}

fn write_directory(path: PathBuf) {
    fs::create_dir_all(path).unwrap();
}

fn copy_artifact(package: &TestPackage, relative: &str) {
    let source = repo_root().join("testdata/package/proofs").join(relative);
    let target = package.artifact_path(relative);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::copy(source, target).unwrap();
}

fn run_publish_plan_check_json(package: &TestPackage) -> Output {
    Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .args(["--check", "--json"])
        .output()
        .unwrap()
}

fn run_publish_plan_check_json_with_timings(package: &TestPackage) -> Output {
    Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .args(["--check", "--timings", "summary", "--json"])
        .output()
        .unwrap()
}

fn run_publish_plan_write(package: &TestPackage) {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "publish-plan", "--root"])
        .arg(package.path())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("package publish-plan: passed\n"));
}

fn run_refactor_plan_json(package: &TestPackage, extra_args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "refactor-plan", "--root"])
        .arg(package.path())
        .args(extra_args)
        .arg("--json")
        .output()
        .unwrap()
}

fn run_refactor_plan_success_stdout(package: &TestPackage, extra_args: &[&str]) -> String {
    let output = run_refactor_plan_json(package, extra_args);
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    String::from_utf8(output.stdout).unwrap()
}

fn clear_reference_summary_cache() {
    let _ = fs::remove_dir_all(
        std::env::current_dir()
            .unwrap()
            .join(PACKAGE_REFERENCE_SUMMARY_CACHE_LAYOUT_DIR),
    );
}

fn reference_summary_cache_test_lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn assert_mutated_publish_plan_check_failure(
    package: &TestPackage,
    publish_plan_json: String,
    reason: &str,
) {
    fs::write(
        package.artifact_path(PACKAGE_PUBLISH_PLAN_PATH),
        publish_plan_json,
    )
    .unwrap();
    assert_json_failure(
        run_publish_plan_check_json(package),
        package,
        1,
        "package publish-plan",
        "GeneratedArtifact",
        reason,
    );
}

fn package_file_hashes(root: &Path) -> BTreeMap<String, npa_package::PackageHash> {
    fn collect(
        root: &Path,
        current: &Path,
        hashes: &mut BTreeMap<String, npa_package::PackageHash>,
    ) {
        for entry in fs::read_dir(current).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_dir() {
                collect(root, &path, hashes);
                continue;
            }
            let relative = path
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            hashes.insert(relative, package_file_hash(&fs::read(path).unwrap()));
        }
    }

    let mut hashes = BTreeMap::new();
    collect(root, root, &mut hashes);
    hashes
}

fn assert_command_result_failure(result: CommandResult, kind: &str, reason: &str) {
    assert_eq!(result.exit_code().as_u8(), 1);
    assert_eq!(result.command, "package publish-plan");
    assert_eq!(result.status.as_str(), "failed");
    assert_eq!(result.diagnostics[0].kind.as_str(), kind);
    assert_eq!(result.diagnostics[0].reason_code, reason);
}

fn assert_json_failure(
    output: Output,
    package: &TestPackage,
    code: i32,
    command: &str,
    kind: &str,
    reason: &str,
) {
    assert_eq!(output.status.code(), Some(code));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_json_envelope(&stdout, command, "failed");
    assert!(stdout.contains(&format!("\"kind\":\"{kind}\"")));
    assert!(stdout.contains(&format!("\"reason_code\":\"{reason}\"")));
    assert_host_path_free(&stdout, package);
}

fn assert_json_failure_with_timings(
    output: Output,
    package: &TestPackage,
    code: i32,
    command: &str,
    kind: &str,
    reason: &str,
) {
    assert_eq!(output.status.code(), Some(code));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with(&format!(
        "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"{command}\","
    )));
    assert!(stdout.contains("\"status\":\"failed\""));
    assert!(stdout.contains("\"diagnostics\":["));
    assert!(stdout.contains("\"timings\":{"));
    assert!(stdout.contains("\"artifacts\":[]"));
    assert!(stdout.contains(&format!("\"kind\":\"{kind}\"")));
    assert!(stdout.contains(&format!("\"reason_code\":\"{reason}\"")));
    assert_host_path_free(&stdout, package);
}

fn assert_usage_failure(output: Output, command: &str, reason: &str) {
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_json_envelope(&stdout, command, "failed");
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains(&format!("\"reason_code\":\"{reason}\"")));
}

fn assert_root_qualified_output_failure(
    output: Output,
    package: &TestPackage,
    command: &str,
    out: &str,
) {
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_json_envelope(&stdout, command, "failed");
    assert!(stdout.contains("\"root\":\"<absolute-root>\""));
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains("\"reason_code\":\"package_output_path_repeats_root\""));
    assert!(stdout.contains(&format!("\"path\":\"{out}\"")));
    assert!(stdout.contains("\"field\":\"--out\""));
    assert!(stdout.contains(
        "\"expected_value\":\"path relative to --root without the package-root directory\""
    ));
    assert!(stdout.contains("\"actual_value\":\"root-qualified path\""));
    assert_host_path_free(&stdout, package);
}

fn assert_json_envelope(stdout: &str, command: &str, status: &str) {
    assert!(stdout.starts_with(&format!(
        "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"{command}\","
    )));
    assert!(stdout.contains(&format!("\"status\":\"{status}\"")));
    assert!(stdout.contains("\"diagnostics\":["));
    assert!(stdout.ends_with("\"artifacts\":[]}\n"));
}

fn assert_host_path_free(stdout: &str, package: &TestPackage) {
    assert!(!stdout.contains(&package.path().to_string_lossy().to_string()));
    assert!(!stdout.contains("/tmp/"));
}

fn run_cli(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .unwrap()
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}
