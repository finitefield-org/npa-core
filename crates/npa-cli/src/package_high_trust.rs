//! Implementation of `npa package high-trust`.
//!
//! The command is an untrusted release-evidence collector. It validates that
//! source-free package artifacts and Phase 8 release/high-trust evidence agree,
//! then writes `generated/verified-high-trust.json`. The generated artifact is
//! not proof input.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};

use npa_api::{
    format_hash_string, independent_checker_file_hash, independent_checker_release_validate_bundle,
    independent_checker_validate_release_policy_runner_trust, parse_hash_string,
    parse_independent_checker_auxiliary_result, parse_independent_checker_binary_registry,
    parse_independent_checker_challenge_coverage_summary,
    parse_independent_checker_release_audit_bundle_manifest,
    parse_independent_checker_release_policy, parse_independent_checker_runner_policy,
    IndependentCheckerAllowlistEntry, IndependentCheckerAuxiliaryResult,
    IndependentCheckerAuxiliaryResultKind, IndependentCheckerAuxiliaryStatus,
    IndependentCheckerBinaryRegistry, IndependentCheckerCommandError,
    IndependentCheckerPolicyValidationError, IndependentCheckerReleaseAuditBundleArtifact,
    IndependentCheckerReleaseAuditBundleManifest, IndependentCheckerReleaseBundleArtifactKind,
    IndependentCheckerReleaseMode, IndependentCheckerRequestValidationError,
    IndependentCheckerRunnerPolicy, IndependentCheckerTrustMode, JsonDocument, JsonMember,
    JsonValue, JsonValueKind, INDEPENDENT_CHECKER_NORMALIZED_CHECK_RESULT_SCHEMA,
};
use npa_cert::Hash;
use npa_package::{
    format_package_hash, package_file_hash, parse_package_publish_plan_json,
    parse_package_verified_high_trust_json, PackageHash, PackagePath, PackageVerifiedHighTrust,
    PackageVerifiedHighTrustAuxiliaryKind, PackageVerifiedHighTrustAuxiliaryResult,
    PackageVerifiedHighTrustCheckerIdentity, PackageVerifiedHighTrustGeneratedBy,
    PACKAGE_PUBLISH_PLAN_PATH, PACKAGE_VERIFIED_HIGH_TRUST_PATH,
    PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA,
};

use crate::args::{PackageCommonOptions, PackageHighTrustOptions};
use crate::diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{join_package_path, render_package_root};
use crate::package_publish::{load_package_publish_inputs, LoadedPackagePublishInputs};

/// Stable command name for `npa package high-trust`.
pub const COMMAND: &str = "package high-trust";

const DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH: &str = "generated/release-audit/manifest.json";
const GENERATOR_ID: &str = "npa-cli";
const GENERATOR_VERSION: &str = "0.1.0";

#[derive(Clone, Debug)]
struct HighTrustPolicies {
    release_policy_hash: Hash,
    runner_policy_hash: Hash,
    challenge_runner_policy_hash: Hash,
    runner_policy: IndependentCheckerRunnerPolicy,
}

#[derive(Clone, Debug)]
struct HighTrustEvidence {
    normalized_result_hash: PackageHash,
    release_audit_bundle_manifest_hash: PackageHash,
    checker_identities: Vec<PackageVerifiedHighTrustCheckerIdentity>,
    auxiliary_results: Vec<PackageVerifiedHighTrustAuxiliaryResult>,
}

#[derive(Clone, Debug)]
struct NormalizedEvidence {
    normalized_result_hash: Hash,
    checker_identities: Vec<PackageVerifiedHighTrustCheckerIdentity>,
}

#[derive(Clone, Debug)]
struct OutputTarget {
    full_path: PathBuf,
    display_path: String,
}

/// Run `package high-trust`.
pub fn run_package_high_trust(options: PackageHighTrustOptions) -> CommandResult {
    if options.check {
        return run_package_high_trust_check(options);
    }
    run_package_high_trust_write(options)
}

fn run_package_high_trust_check(options: PackageHighTrustOptions) -> CommandResult {
    let generated = match generate_package_high_trust(&options) {
        Ok(generated) => generated,
        Err(result) => return result,
    };
    let target = match output_target(&options.common, options.out.as_deref()) {
        Ok(target) => target,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, generated.0, vec![*diagnostic]);
        }
    };
    let checked_json = match read_output_json(&target) {
        Ok(json) => json,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, generated.0, vec![*diagnostic]);
        }
    };
    if let Err(error) = parse_package_verified_high_trust_json(&checked_json) {
        return CommandResult::failed(
            COMMAND,
            generated.0,
            vec![verified_high_trust_artifact_error(
                &error,
                &target.display_path,
            )],
        );
    }
    if checked_json != generated.2 {
        return CommandResult::failed(
            COMMAND,
            generated.0,
            vec![verified_high_trust_stale_diagnostic(
                &checked_json,
                &generated.2,
                &target.display_path,
            )],
        );
    }
    passed_result(generated.0, target.display_path)
}

fn run_package_high_trust_write(options: PackageHighTrustOptions) -> CommandResult {
    let generated = match generate_package_high_trust(&options) {
        Ok(generated) => generated,
        Err(result) => return result,
    };
    let target = match output_target(&options.common, options.out.as_deref()) {
        Ok(target) => target,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, generated.0, vec![*diagnostic]);
        }
    };
    if let Err(diagnostic) = write_output_json(&target, generated.2.as_bytes()) {
        return CommandResult::failed(COMMAND, generated.0, vec![*diagnostic]);
    }
    passed_result(generated.0, target.display_path)
}

fn generate_package_high_trust(
    options: &PackageHighTrustOptions,
) -> Result<(String, PackageVerifiedHighTrust, String), CommandResult> {
    let root_display = render_package_root(&options.common.root);
    let policies = load_high_trust_policies(options).map_err(|diagnostic| {
        CommandResult::failed(COMMAND, root_display.clone(), vec![*diagnostic])
    })?;
    let evidence = load_high_trust_evidence(&options.common, &policies).map_err(|diagnostic| {
        CommandResult::failed(COMMAND, root_display.clone(), vec![*diagnostic])
    })?;
    let inputs = load_high_trust_package_inputs(&options.common)?;
    let publish_plan_hash = read_publish_plan_hash(&options.common, &inputs)?;

    let artifact = PackageVerifiedHighTrust {
        schema: PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA.to_owned(),
        package: inputs.validated.manifest().package.clone(),
        package_version: inputs.validated.manifest().version.clone(),
        package_lock_hash: inputs.package_lock.file_hash,
        axiom_report_hash: inputs.axiom_report.package_axiom_report_hash,
        theorem_index_hash: inputs.theorem_index.theorem_index_hash,
        publish_plan_hash,
        release_policy_hash: package_hash_from_hash(policies.release_policy_hash),
        runner_policy_hash: package_hash_from_hash(policies.runner_policy_hash),
        challenge_runner_policy_hash: package_hash_from_hash(policies.challenge_runner_policy_hash),
        normalized_result_hash: evidence.normalized_result_hash,
        release_audit_bundle_manifest_hash: evidence.release_audit_bundle_manifest_hash,
        required_checker_profiles: required_profiles(),
        checker_identities: evidence.checker_identities,
        auxiliary_results: evidence.auxiliary_results,
        generated_by: PackageVerifiedHighTrustGeneratedBy {
            command: COMMAND.to_owned(),
            generator: GENERATOR_ID.to_owned(),
            version: GENERATOR_VERSION.to_owned(),
        },
        artifact_hash: PackageHash::new([0; 32]),
    }
    .with_computed_hash()
    .map_err(|error| {
        CommandResult::failed(
            COMMAND,
            inputs.root_display.clone(),
            vec![verified_high_trust_artifact_error(
                &error,
                PACKAGE_VERIFIED_HIGH_TRUST_PATH,
            )],
        )
    })?;
    let json = artifact.canonical_json().map_err(|error| {
        CommandResult::failed(
            COMMAND,
            inputs.root_display.clone(),
            vec![verified_high_trust_artifact_error(
                &error,
                PACKAGE_VERIFIED_HIGH_TRUST_PATH,
            )],
        )
    })?;
    Ok((inputs.root_display, artifact, json))
}

fn load_high_trust_package_inputs(
    options: &PackageCommonOptions,
) -> Result<LoadedPackagePublishInputs, CommandResult> {
    load_package_publish_inputs(&options.root).map_err(|mut result| {
        result.command = COMMAND.to_owned();
        result
    })
}

fn read_publish_plan_hash(
    options: &PackageCommonOptions,
    inputs: &LoadedPackagePublishInputs,
) -> Result<Option<PackageHash>, CommandResult> {
    let path = PackagePath::new(PACKAGE_PUBLISH_PLAN_PATH);
    let full_path = match join_package_path(&options.root, &path, "publish_plan.path") {
        Ok(path) => path,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                COMMAND,
                inputs.root_display.clone(),
                vec![*diagnostic],
            ))
        }
    };
    let source = match fs::read_to_string(full_path) {
        Ok(source) => source,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(_) => {
            return Err(CommandResult::failed(
                COMMAND,
                inputs.root_display.clone(),
                vec![CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "publish_plan_unreadable",
                )
                .with_path(PACKAGE_PUBLISH_PLAN_PATH)],
            ))
        }
    };
    let plan = parse_package_publish_plan_json(&source).map_err(|error| {
        CommandResult::failed(
            COMMAND,
            inputs.root_display.clone(),
            vec![verified_high_trust_artifact_error(
                &error,
                PACKAGE_PUBLISH_PLAN_PATH,
            )],
        )
    })?;
    Ok(Some(plan.publish_plan_hash))
}

fn load_high_trust_policies(
    options: &PackageHighTrustOptions,
) -> Result<HighTrustPolicies, Box<CommandDiagnostic>> {
    let release_source = read_workspace_text(&options.release_policy, "release_policy_missing")?;
    let release_policy =
        parse_independent_checker_release_policy(&release_source).map_err(|error| {
            Box::new(policy_validation_diagnostic(
                "release_policy_invalid",
                error,
            ))
        })?;
    if release_policy.mode != IndependentCheckerReleaseMode::HighTrust {
        return Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::PackagePolicy,
                "release_policy_not_high_trust",
            )
            .with_path(workspace_path_display(&options.release_policy))
            .with_field("mode")
            .with_expected_value(IndependentCheckerReleaseMode::HighTrust.as_str())
            .with_actual_value(release_policy.mode.as_str()),
        ));
    }
    let release_policy_hash = parse_expected_hash(
        "--release-policy-hash",
        &options.release_policy_hash,
        &workspace_path_display(&options.release_policy),
    )?;
    ensure_hash(
        release_policy.policy_hash(),
        release_policy_hash,
        "release_policy_hash_mismatch",
        "--release-policy-hash",
        &workspace_path_display(&options.release_policy),
    )?;

    let runner_source = read_workspace_text(&options.runner_policy, "runner_policy_missing")?;
    let runner_policy = parse_independent_checker_runner_policy(&runner_source)
        .map_err(|error| Box::new(policy_validation_diagnostic("runner_policy_invalid", error)))?;
    let runner_policy_hash = parse_expected_hash(
        "--runner-policy-hash",
        &options.runner_policy_hash,
        &workspace_path_display(&options.runner_policy),
    )?;
    ensure_hash(
        runner_policy.policy_hash(),
        runner_policy_hash,
        "runner_policy_hash_mismatch",
        "--runner-policy-hash",
        &workspace_path_display(&options.runner_policy),
    )?;
    ensure_hash(
        release_policy.runner_policy_hash,
        runner_policy_hash,
        "release_runner_policy_hash_mismatch",
        "runner_policy_hash",
        &workspace_path_display(&options.release_policy),
    )?;

    let challenge_source = read_workspace_text(
        &options.challenge_runner_policy,
        "challenge_runner_policy_missing",
    )?;
    let challenge_runner_policy = parse_independent_checker_runner_policy(&challenge_source)
        .map_err(|error| {
            Box::new(policy_validation_diagnostic(
                "challenge_runner_policy_invalid",
                error,
            ))
        })?;
    let challenge_runner_policy_hash = parse_expected_hash(
        "--challenge-runner-policy-hash",
        &options.challenge_runner_policy_hash,
        &workspace_path_display(&options.challenge_runner_policy),
    )?;
    ensure_hash(
        challenge_runner_policy.policy_hash(),
        challenge_runner_policy_hash,
        "challenge_runner_policy_hash_mismatch",
        "--challenge-runner-policy-hash",
        &workspace_path_display(&options.challenge_runner_policy),
    )?;
    ensure_hash(
        release_policy.challenge_runner_policy_hash,
        challenge_runner_policy_hash,
        "release_challenge_runner_policy_hash_mismatch",
        "challenge_runner_policy_hash",
        &workspace_path_display(&options.release_policy),
    )?;
    independent_checker_validate_release_policy_runner_trust(
        &release_policy,
        &runner_policy,
        &challenge_runner_policy,
    )
    .map_err(|error| {
        Box::new(policy_validation_diagnostic(
            "release_policy_invalid",
            error,
        ))
    })?;
    validate_required_profiles(&runner_policy)?;
    validate_required_profiles(&challenge_runner_policy)?;

    let registry_source =
        read_workspace_text(&options.checker_registry, "checker_registry_missing")?;
    let registry =
        parse_independent_checker_binary_registry(&registry_source).map_err(|error| {
            Box::new(policy_validation_diagnostic(
                "checker_registry_invalid",
                error,
            ))
        })?;
    validate_registry_entries(&runner_policy, &registry)?;
    validate_registry_entries(&challenge_runner_policy, &registry)?;

    Ok(HighTrustPolicies {
        release_policy_hash,
        runner_policy_hash,
        challenge_runner_policy_hash,
        runner_policy,
    })
}

fn load_high_trust_evidence(
    options: &PackageCommonOptions,
    policies: &HighTrustPolicies,
) -> Result<HighTrustEvidence, Box<CommandDiagnostic>> {
    let manifest_path = PackagePath::new(DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH);
    let manifest_full_path = join_package_path(
        &options.root,
        &manifest_path,
        "release_audit_bundle_manifest.path",
    )?;
    let manifest_source = fs::read_to_string(&manifest_full_path).map_err(|error| {
        let reason = if error.kind() == io::ErrorKind::NotFound {
            "not_verified"
        } else {
            "release_audit_bundle_manifest_unreadable"
        };
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, reason)
                .with_path(DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH)
                .with_field("release_audit_bundle_manifest")
                .with_expected_value(
                    "ReleaseAuditBundleManifest with external and high-trust-reference evidence",
                )
                .with_actual_value("missing"),
        )
    })?;
    let manifest_file_hash = independent_checker_file_hash(manifest_source.as_bytes());
    let manifest = parse_independent_checker_release_audit_bundle_manifest(&manifest_source)
        .map_err(|error| {
            Box::new(command_error_diagnostic(
                "release_audit_bundle_manifest_invalid",
                error,
                DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH,
            ))
        })?;
    ensure_hash(
        policies.release_policy_hash,
        manifest.policy_hash,
        "release_audit_bundle_policy_hash_mismatch",
        "policy_hash",
        DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH,
    )?;

    let bundle_root = manifest_full_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| options.root.clone());
    let bundle_files = read_bundle_files(&bundle_root, &manifest)?;
    let audit_bundle_result = validate_release_audit_bundle(
        DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH,
        manifest_file_hash,
        &manifest_source,
        &bundle_files,
    )?;
    let normalized_artifact = unique_artifact(
        &manifest,
        IndependentCheckerReleaseBundleArtifactKind::NormalizedCheckResult,
    )?;
    let normalized_source = bundle_artifact_text(&bundle_files, normalized_artifact)?;
    let normalized = parse_normalized_evidence(&normalized_source, normalized_artifact, policies)?;

    let mut auxiliary_results = collect_auxiliary_results(&bundle_files, &manifest)?;
    auxiliary_results.push(auxiliary_result_from_phase8(
        &audit_bundle_result,
        audit_bundle_result.result_hash(),
    )?);
    validate_auxiliary_evidence(&auxiliary_results)?;

    Ok(HighTrustEvidence {
        normalized_result_hash: package_hash_from_hash(normalized.normalized_result_hash),
        release_audit_bundle_manifest_hash: package_hash_from_hash(manifest.bundle_hash),
        checker_identities: normalized.checker_identities,
        auxiliary_results,
    })
}

fn parse_normalized_evidence(
    source: &str,
    artifact: &IndependentCheckerReleaseAuditBundleArtifact,
    policies: &HighTrustPolicies,
) -> Result<NormalizedEvidence, Box<CommandDiagnostic>> {
    let document = JsonDocument::parse(source).map_err(|_| {
        evidence_error(
            "normalized_result_invalid",
            &artifact.path,
            "$",
            "valid_json",
            "invalid_json",
        )
    })?;
    let root = object_members(document.root(), "$", &artifact.path)?;
    let schema = required_string(root, "schema", "schema", &artifact.path)?;
    if schema != INDEPENDENT_CHECKER_NORMALIZED_CHECK_RESULT_SCHEMA {
        return Err(evidence_error(
            "normalized_result_invalid",
            &artifact.path,
            "schema",
            INDEPENDENT_CHECKER_NORMALIZED_CHECK_RESULT_SCHEMA,
            schema,
        ));
    }
    let normalized_result_hash = required_hash(
        root,
        "normalized_result_hash",
        "normalized_result_hash",
        &artifact.path,
    )?;
    let manifest_normalized_hash =
        required_artifact_hash(artifact, "normalized_result_hash", "normalized_result_hash")?;
    ensure_hash(
        manifest_normalized_hash,
        normalized_result_hash,
        "normalized_result_hash_mismatch",
        "normalized_result_hash",
        &artifact.path,
    )?;
    let artifact_hash = required_hash(root, "artifact_hash", "artifact_hash", &artifact.path)?;
    let manifest_artifact_hash =
        required_artifact_hash(artifact, "artifact_hash", "artifact_hash")?;
    ensure_hash(
        manifest_artifact_hash,
        artifact_hash,
        "normalized_artifact_hash_mismatch",
        "artifact_hash",
        &artifact.path,
    )?;

    let policy_value = required_value(root, "policy", "policy", &artifact.path)?;
    let policy_members = object_members(policy_value, "policy", &artifact.path)?;
    let normalized_policy_hash =
        required_hash(policy_members, "hash", "policy.hash", &artifact.path)?;
    ensure_hash(
        policies.runner_policy_hash,
        normalized_policy_hash,
        "normalized_runner_policy_hash_mismatch",
        "policy.hash",
        &artifact.path,
    )?;

    let comparison_value = required_value(root, "comparison", "comparison", &artifact.path)?;
    let comparison = object_members(comparison_value, "comparison", &artifact.path)?;
    let status = required_string(comparison, "status", "comparison.status", &artifact.path)?;
    if status != "all_agree_checked" {
        return Err(normalized_status_not_verified_diagnostic(
            status,
            &artifact.path,
        ));
    }
    let missing = required_string_array(
        comparison,
        "missing_checker_profiles",
        "comparison.missing_checker_profiles",
        &artifact.path,
    )?;
    if !missing.is_empty() {
        return Err(evidence_error(
            "not_verified",
            &artifact.path,
            "comparison.missing_checker_profiles",
            "[]",
            missing.join(","),
        ));
    }

    let selected = selected_checkers_by_profile(&policies.runner_policy)?;
    let mut by_profile = BTreeMap::<String, PackageVerifiedHighTrustCheckerIdentity>::new();
    let results = required_array(root, "results", "results", &artifact.path)?;
    for (index, result_value) in results.iter().enumerate() {
        let path = format!("results[{index}]");
        let members = object_members(result_value, &path, &artifact.path)?;
        let profile = required_string(
            members,
            "checker_profile",
            &format!("{path}.checker_profile"),
            &artifact.path,
        )?;
        if !required_profiles().contains(&profile) {
            continue;
        }
        if by_profile.contains_key(&profile) {
            return Err(evidence_error(
                "not_verified",
                &artifact.path,
                format!("{path}.checker_profile"),
                "unique required checker profile",
                profile,
            ));
        }
        let status = required_string(members, "status", &format!("{path}.status"), &artifact.path)?;
        if status != "checked" {
            return Err(evidence_error(
                "not_verified",
                &artifact.path,
                format!("{path}.status"),
                "checked",
                status,
            ));
        }
        let Some(selected_checker) = selected.get(profile.as_str()) else {
            return Err(evidence_error(
                "not_verified",
                &artifact.path,
                format!("{path}.checker_profile"),
                "runner policy selected checker",
                profile,
            ));
        };
        let checker_id = optional_string(
            members,
            "checker_id",
            &format!("{path}.checker_id"),
            &artifact.path,
        )?
        .unwrap_or_else(|| selected_checker.checker_id.clone());
        if checker_id != selected_checker.checker_id {
            return Err(evidence_error(
                "checker_identity_mismatch",
                &artifact.path,
                format!("{path}.checker_id"),
                selected_checker.checker_id.clone(),
                checker_id,
            ));
        }
        let binary_id = optional_string(
            members,
            "checker_binary_id",
            &format!("{path}.checker_binary_id"),
            &artifact.path,
        )?
        .unwrap_or_else(|| selected_checker.binary_id.clone());
        if binary_id != selected_checker.binary_id {
            return Err(evidence_error(
                "checker_identity_mismatch",
                &artifact.path,
                format!("{path}.checker_binary_id"),
                selected_checker.binary_id.clone(),
                binary_id,
            ));
        }
        let binary_hash = optional_hash(
            members,
            "checker_binary_hash",
            &format!("{path}.checker_binary_hash"),
            &artifact.path,
        )?
        .unwrap_or(selected_checker.binary_hash);
        ensure_hash(
            selected_checker.binary_hash,
            binary_hash,
            "checker_identity_hash_mismatch",
            format!("{path}.checker_binary_hash"),
            &artifact.path,
        )?;
        let build_hash = optional_hash(
            members,
            "checker_build_hash",
            &format!("{path}.checker_build_hash"),
            &artifact.path,
        )?
        .unwrap_or(selected_checker.build_hash);
        ensure_hash(
            selected_checker.build_hash,
            build_hash,
            "checker_build_hash_mismatch",
            format!("{path}.checker_build_hash"),
            &artifact.path,
        )?;
        by_profile.insert(
            profile.clone(),
            PackageVerifiedHighTrustCheckerIdentity {
                profile,
                checker_id,
                checker_version: optional_string(
                    members,
                    "checker_version",
                    &format!("{path}.checker_version"),
                    &artifact.path,
                )?,
                binary_id,
                binary_hash: package_hash_from_hash(binary_hash),
                build_hash: package_hash_from_hash(build_hash),
                result_hash: package_hash_from_hash(required_hash(
                    members,
                    "result_hash",
                    &format!("{path}.result_hash"),
                    &artifact.path,
                )?),
                status,
            },
        );
    }

    let mut checker_identities = Vec::new();
    for profile in required_profiles() {
        let Some(identity) = by_profile.remove(&profile) else {
            return Err(evidence_error(
                "not_verified",
                &artifact.path,
                "required_checker_profiles",
                profile,
                "missing",
            ));
        };
        checker_identities.push(identity);
    }
    Ok(NormalizedEvidence {
        normalized_result_hash,
        checker_identities,
    })
}

fn collect_auxiliary_results(
    bundle_files: &BTreeMap<String, Vec<u8>>,
    manifest: &IndependentCheckerReleaseAuditBundleManifest,
) -> Result<Vec<PackageVerifiedHighTrustAuxiliaryResult>, Box<CommandDiagnostic>> {
    let mut results = Vec::new();
    for artifact in manifest.artifacts.iter().filter(|artifact| {
        artifact.kind == IndependentCheckerReleaseBundleArtifactKind::AuxiliaryResult
    }) {
        let source = bundle_artifact_text(bundle_files, artifact)?;
        let auxiliary = parse_independent_checker_auxiliary_result(&source).map_err(|error| {
            Box::new(request_validation_diagnostic(
                "auxiliary_result_invalid",
                error,
                &artifact.path,
            ))
        })?;
        let result_hash = auxiliary.result_hash();
        let manifest_result_hash = required_artifact_hash(artifact, "result_hash", "result_hash")?;
        ensure_hash(
            manifest_result_hash,
            result_hash,
            "auxiliary_result_hash_mismatch",
            "result_hash",
            &artifact.path,
        )?;
        if auxiliary.status != IndependentCheckerAuxiliaryStatus::Passed {
            return Err(evidence_error(
                "not_verified",
                &artifact.path,
                "status",
                "passed",
                auxiliary.status.as_str(),
            ));
        }
        results.push(auxiliary_result_from_phase8(&auxiliary, result_hash)?);
    }
    for artifact in manifest.artifacts.iter().filter(|artifact| {
        artifact.kind == IndependentCheckerReleaseBundleArtifactKind::ChallengeCoverageSummary
    }) {
        let source = bundle_artifact_text(bundle_files, artifact)?;
        let summary =
            parse_independent_checker_challenge_coverage_summary(&source).map_err(|error| {
                Box::new(request_validation_diagnostic(
                    "challenge_coverage_invalid",
                    error,
                    &artifact.path,
                ))
            })?;
        let summary_hash = required_artifact_hash(artifact, "summary_hash", "summary_hash")?;
        ensure_hash(
            summary_hash,
            summary.summary_hash(),
            "challenge_coverage_hash_mismatch",
            "summary_hash",
            &artifact.path,
        )?;
        results.push(PackageVerifiedHighTrustAuxiliaryResult {
            kind: PackageVerifiedHighTrustAuxiliaryKind::ChallengeCoverage,
            status: "passed".to_owned(),
            policy_hash: package_hash_from_hash(summary.policy_hash),
            result_hash: package_hash_from_hash(summary_hash),
            artifact_hash: package_hash_from_hash(artifact.file_hash),
        });
    }
    Ok(results)
}

fn auxiliary_result_from_phase8(
    auxiliary: &IndependentCheckerAuxiliaryResult,
    result_hash: Hash,
) -> Result<PackageVerifiedHighTrustAuxiliaryResult, Box<CommandDiagnostic>> {
    let kind = match auxiliary.kind {
        IndependentCheckerAuxiliaryResultKind::AxiomPolicy => {
            PackageVerifiedHighTrustAuxiliaryKind::AxiomPolicy
        }
        IndependentCheckerAuxiliaryResultKind::Reproducibility => {
            PackageVerifiedHighTrustAuxiliaryKind::Reproducibility
        }
        IndependentCheckerAuxiliaryResultKind::AuditBundle => {
            PackageVerifiedHighTrustAuxiliaryKind::AuditBundle
        }
        IndependentCheckerAuxiliaryResultKind::ImportCertificateHash => {
            PackageVerifiedHighTrustAuxiliaryKind::ImportCertificateHash
        }
    };
    Ok(PackageVerifiedHighTrustAuxiliaryResult {
        kind,
        status: auxiliary.status.as_str().to_owned(),
        policy_hash: package_hash_from_hash(auxiliary.policy_hash),
        result_hash: package_hash_from_hash(result_hash),
        artifact_hash: package_hash_from_hash(auxiliary.artifact_hash),
    })
}

fn validate_auxiliary_evidence(
    results: &[PackageVerifiedHighTrustAuxiliaryResult],
) -> Result<(), Box<CommandDiagnostic>> {
    for required in [
        PackageVerifiedHighTrustAuxiliaryKind::AxiomPolicy,
        PackageVerifiedHighTrustAuxiliaryKind::Reproducibility,
        PackageVerifiedHighTrustAuxiliaryKind::AuditBundle,
        PackageVerifiedHighTrustAuxiliaryKind::ImportCertificateHash,
    ] {
        if !results.iter().any(|result| result.kind == required) {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, "not_verified")
                    .with_path(DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH)
                    .with_field("auxiliary_results")
                    .with_expected_value(required.as_str())
                    .with_actual_value("missing"),
            ));
        }
    }
    Ok(())
}

fn unique_artifact(
    manifest: &IndependentCheckerReleaseAuditBundleManifest,
    kind: IndependentCheckerReleaseBundleArtifactKind,
) -> Result<&IndependentCheckerReleaseAuditBundleArtifact, Box<CommandDiagnostic>> {
    let matches = manifest
        .artifacts
        .iter()
        .filter(|artifact| artifact.kind == kind)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [artifact] => Ok(*artifact),
        [] => Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, "not_verified")
                .with_path(DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH)
                .with_field(kind.as_str())
                .with_expected_value("one release audit bundle artifact")
                .with_actual_value("missing"),
        )),
        _ => Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, "not_verified")
                .with_path(DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH)
                .with_field(kind.as_str())
                .with_expected_value("one release audit bundle artifact")
                .with_actual_value("duplicate"),
        )),
    }
}

fn read_bundle_files(
    bundle_root: &Path,
    manifest: &IndependentCheckerReleaseAuditBundleManifest,
) -> Result<BTreeMap<String, Vec<u8>>, Box<CommandDiagnostic>> {
    let mut files = BTreeMap::new();
    for artifact in &manifest.artifacts {
        files.insert(
            artifact.path.clone(),
            read_bundle_artifact_bytes(bundle_root, artifact)?,
        );
    }
    Ok(files)
}

fn read_bundle_artifact_bytes(
    bundle_root: &Path,
    artifact: &IndependentCheckerReleaseAuditBundleArtifact,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let package_path = package_path_from_str(&artifact.path, "release_audit_bundle.artifact.path")?;
    let full_path = join_package_path(
        bundle_root,
        &package_path,
        "release_audit_bundle.artifact.path",
    )?;
    let bytes = fs::read(full_path).map_err(|error| {
        let reason = if error.kind() == io::ErrorKind::NotFound {
            "release_audit_bundle_artifact_missing"
        } else {
            "release_audit_bundle_artifact_unreadable"
        };
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, reason)
                .with_path(artifact.path.clone()),
        )
    })?;
    let actual_hash = independent_checker_file_hash(&bytes);
    ensure_hash(
        artifact.file_hash,
        actual_hash,
        "release_audit_bundle_artifact_hash_mismatch",
        "file_hash",
        &artifact.path,
    )?;
    Ok(bytes)
}

fn bundle_artifact_text(
    bundle_files: &BTreeMap<String, Vec<u8>>,
    artifact: &IndependentCheckerReleaseAuditBundleArtifact,
) -> Result<String, Box<CommandDiagnostic>> {
    let bytes = bundle_files.get(&artifact.path).ok_or_else(|| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::ExternalVerifier,
                "release_audit_bundle_artifact_missing",
            )
            .with_path(artifact.path.clone()),
        )
    })?;
    String::from_utf8(bytes.clone()).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, "artifact_not_utf8")
                .with_path(artifact.path.clone()),
        )
    })
}

fn validate_release_audit_bundle(
    manifest_path: &str,
    manifest_file_hash: Hash,
    manifest_source: &str,
    bundle_files: &BTreeMap<String, Vec<u8>>,
) -> Result<IndependentCheckerAuxiliaryResult, Box<CommandDiagnostic>> {
    let validation = independent_checker_release_validate_bundle(
        manifest_path.to_owned(),
        manifest_file_hash,
        manifest_source,
        bundle_files,
        None,
    )
    .map_err(|error| {
        Box::new(command_error_diagnostic(
            "release_audit_bundle_invalid",
            error,
            manifest_path,
        ))
    })?;
    if validation.result.status != IndependentCheckerAuxiliaryStatus::Passed {
        return Err(Box::new(release_audit_bundle_failure_diagnostic(
            &validation.result,
            manifest_path,
        )));
    }
    Ok(validation.result)
}

fn release_audit_bundle_failure_diagnostic(
    result: &IndependentCheckerAuxiliaryResult,
    manifest_path: &str,
) -> CommandDiagnostic {
    let reason_code = result
        .error
        .as_ref()
        .map(|error| error.reason_code.as_str())
        .unwrap_or("not_verified");
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, reason_code)
        .with_path(manifest_path)
        .with_field("release_audit_bundle")
        .with_expected_value(IndependentCheckerAuxiliaryStatus::Passed.as_str())
        .with_actual_value(result.status.as_str());
    if let Some(error) = &result.error {
        if let Some(field) = &error.field {
            diagnostic = diagnostic.with_field(field.clone());
        }
        if let (Some(expected), Some(actual)) = (error.expected_hash, error.actual_hash) {
            diagnostic =
                diagnostic.with_hashes(format_hash_string(&expected), format_hash_string(&actual));
        } else {
            if let Some(expected) = &error.expected_value {
                diagnostic = diagnostic.with_expected_value(expected.clone());
            }
            if let Some(actual) = &error.actual_value {
                diagnostic = diagnostic.with_actual_value(actual.clone());
            }
        }
    }
    diagnostic
}

fn validate_required_profiles(
    policy: &IndependentCheckerRunnerPolicy,
) -> Result<(), Box<CommandDiagnostic>> {
    let expected = required_profiles();
    if policy.trust_mode != IndependentCheckerTrustMode::HighTrust {
        return Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::PackagePolicy,
                "runner_policy_not_high_trust",
            )
            .with_field("trust_mode")
            .with_expected_value(IndependentCheckerTrustMode::HighTrust.as_str())
            .with_actual_value(policy.trust_mode.as_str()),
        ));
    }
    if policy.required_checker_profiles != expected {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "required_profiles_mismatch")
                .with_field("required_checker_profiles")
                .with_expected_value(expected.join(","))
                .with_actual_value(policy.required_checker_profiles.join(",")),
        ));
    }
    for profile in &expected {
        if policy.selected_checker_policy(profile).is_none() {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "checker_profile_missing")
                    .with_field("checker_allowlist")
                    .with_expected_value(profile)
                    .with_actual_value("missing"),
            ));
        }
    }
    Ok(())
}

fn validate_registry_entries(
    policy: &IndependentCheckerRunnerPolicy,
    registry: &IndependentCheckerBinaryRegistry,
) -> Result<(), Box<CommandDiagnostic>> {
    for profile in required_profiles() {
        let selected = policy
            .selected_checker_policy(&profile)
            .expect("required profiles validated before registry");
        if !registry
            .entries
            .iter()
            .any(|entry| entry.binary_id == selected.binary_id)
        {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "checker_binary_missing")
                    .with_field("checker_registry.entries")
                    .with_checker(profile)
                    .with_expected_value(selected.binary_id.clone())
                    .with_actual_value("missing"),
            ));
        }
    }
    Ok(())
}

fn selected_checkers_by_profile(
    policy: &IndependentCheckerRunnerPolicy,
) -> Result<BTreeMap<&str, &IndependentCheckerAllowlistEntry>, Box<CommandDiagnostic>> {
    let mut selected = BTreeMap::new();
    for profile in required_profiles() {
        let Some(entry) = policy.selected_checker_policy(&profile) else {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "checker_profile_missing")
                    .with_field("checker_allowlist")
                    .with_expected_value(profile)
                    .with_actual_value("missing"),
            ));
        };
        selected.insert(entry.profile.as_str(), entry);
    }
    Ok(selected)
}

fn output_target(
    options: &PackageCommonOptions,
    out: Option<&Path>,
) -> Result<OutputTarget, Box<CommandDiagnostic>> {
    if let Some(out) = out {
        validate_workspace_relative_path(out, "--out")?;
        return Ok(OutputTarget {
            full_path: out.to_path_buf(),
            display_path: workspace_path_display(out),
        });
    }
    Ok(OutputTarget {
        full_path: options.root.join(PACKAGE_VERIFIED_HIGH_TRUST_PATH),
        display_path: PACKAGE_VERIFIED_HIGH_TRUST_PATH.to_owned(),
    })
}

fn read_output_json(target: &OutputTarget) -> Result<String, Box<CommandDiagnostic>> {
    fs::read_to_string(&target.full_path).map_err(|error| {
        let reason = if error.kind() == io::ErrorKind::NotFound {
            "verified_high_trust_missing"
        } else {
            "generated_artifact_read_failed"
        };
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                .with_path(target.display_path.clone()),
        )
    })
}

fn write_output_json(target: &OutputTarget, json: &[u8]) -> Result<(), Box<CommandDiagnostic>> {
    match fs::read(&target.full_path) {
        Ok(existing) if existing == json => return Ok(()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err(Box::new(write_failed_diagnostic(&target.display_path))),
    }
    if let Some(parent) = target.full_path.parent() {
        fs::create_dir_all(parent)
            .map_err(|_| Box::new(write_failed_diagnostic(&target.display_path)))?;
    }
    let temp_path = temporary_write_path(&target.full_path);
    if fs::write(&temp_path, json).is_err() {
        return Err(Box::new(write_failed_diagnostic(&target.display_path)));
    }
    if fs::rename(&temp_path, &target.full_path).is_err() {
        let _ = fs::remove_file(&temp_path);
        return Err(Box::new(write_failed_diagnostic(&target.display_path)));
    }
    Ok(())
}

fn temporary_write_path(path: &Path) -> PathBuf {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("verified-high-trust.json");
    path.with_file_name(format!(".{file_name}.npa-high-trust.tmp"))
}

fn passed_result(root_display: String, path: String) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "verified_high_trust_current",
        )
        .with_path(path.clone())
        .with_actual_value("release evidence; not checker input"),
    );
    result.artifacts.push(CommandArtifact {
        kind: "package_verified_high_trust".to_owned(),
        path,
    });
    result
}

fn read_workspace_text(
    path: &Path,
    missing_reason: &'static str,
) -> Result<String, Box<CommandDiagnostic>> {
    validate_workspace_relative_path(path, "path")?;
    fs::read_to_string(path).map_err(|error| {
        let reason = if error.kind() == io::ErrorKind::NotFound {
            missing_reason
        } else {
            "artifact_unreadable"
        };
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason)
                .with_path(workspace_path_display(path)),
        )
    })
}

fn validate_workspace_relative_path(
    path: &Path,
    field: &'static str,
) -> Result<(), Box<CommandDiagnostic>> {
    if path.as_os_str().is_empty()
        || path.components().any(|component| {
            matches!(
                component,
                Component::Prefix(_) | Component::RootDir | Component::ParentDir
            )
        })
    {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Usage, "invalid_workspace_relative_path")
                .with_field(field)
                .with_expected_value("workspace-relative path without parent traversal")
                .with_actual_value(workspace_path_display(path)),
        ));
    }
    Ok(())
}

fn package_path_from_str(
    value: &str,
    field: &'static str,
) -> Result<PackagePath, Box<CommandDiagnostic>> {
    let path = PackagePath::new(value.to_owned());
    npa_package::validate_package_path(&path, field).map_err(|error| {
        Box::new(CommandDiagnostic::from_package_manifest_error(&error).with_field(field))
    })?;
    Ok(path)
}

fn workspace_path_display(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

fn parse_expected_hash(
    field: &'static str,
    value: &str,
    path: &str,
) -> Result<Hash, Box<CommandDiagnostic>> {
    parse_hash_string(value).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "invalid_hash_format")
                .with_path(path)
                .with_field(field)
                .with_expected_value("sha256:<lower-hex>")
                .with_actual_value(value),
        )
    })
}

fn ensure_hash(
    expected: Hash,
    actual: Hash,
    reason_code: &'static str,
    field: impl Into<String>,
    path: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    if expected == actual {
        Ok(())
    } else {
        Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, reason_code)
                .with_path(path)
                .with_field(field)
                .with_hashes(format_hash_string(&expected), format_hash_string(&actual)),
        ))
    }
}

fn required_artifact_hash(
    artifact: &IndependentCheckerReleaseAuditBundleArtifact,
    key: &str,
    field: &str,
) -> Result<Hash, Box<CommandDiagnostic>> {
    artifact.hashes.get(key).copied().ok_or_else(|| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, "not_verified")
                .with_path(artifact.path.clone())
                .with_field(field)
                .with_expected_value("release audit bundle artifact hash")
                .with_actual_value("missing"),
        )
    })
}

fn object_members<'a>(
    value: &'a JsonValue<'_>,
    path: &str,
    artifact_path: &str,
) -> Result<&'a [JsonMember<'a>], Box<CommandDiagnostic>> {
    value.object_members().ok_or_else(|| {
        evidence_error(
            "normalized_result_invalid",
            artifact_path,
            path,
            "object",
            json_kind_name(value.kind()),
        )
    })
}

fn required_value<'a>(
    members: &'a [JsonMember<'a>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<&'a JsonValue<'a>, Box<CommandDiagnostic>> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
        .ok_or_else(|| {
            evidence_error(
                "normalized_result_invalid",
                artifact_path,
                path,
                "present",
                "missing",
            )
        })
}

fn required_string(
    members: &[JsonMember<'_>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<String, Box<CommandDiagnostic>> {
    let value = required_value(members, field, path, artifact_path)?;
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        evidence_error(
            "normalized_result_invalid",
            artifact_path,
            path,
            "string",
            json_kind_name(value.kind()),
        )
    })
}

fn optional_string(
    members: &[JsonMember<'_>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<Option<String>, Box<CommandDiagnostic>> {
    let Some(value) = members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
    else {
        return Ok(None);
    };
    value
        .string_value()
        .map(|value| Some(value.to_owned()))
        .ok_or_else(|| {
            evidence_error(
                "normalized_result_invalid",
                artifact_path,
                path,
                "string",
                json_kind_name(value.kind()),
            )
        })
}

fn required_hash(
    members: &[JsonMember<'_>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<Hash, Box<CommandDiagnostic>> {
    let value = required_string(members, field, path, artifact_path)?;
    parse_hash_string(&value).map_err(|_| {
        evidence_error(
            "normalized_result_invalid",
            artifact_path,
            path,
            "sha256:<lower-hex>",
            value,
        )
    })
}

fn optional_hash(
    members: &[JsonMember<'_>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<Option<Hash>, Box<CommandDiagnostic>> {
    let Some(value) = members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
    else {
        return Ok(None);
    };
    let Some(raw) = value.string_value() else {
        return Err(evidence_error(
            "normalized_result_invalid",
            artifact_path,
            path,
            "sha256:<lower-hex>",
            json_kind_name(value.kind()),
        ));
    };
    parse_hash_string(raw).map(Some).map_err(|_| {
        evidence_error(
            "normalized_result_invalid",
            artifact_path,
            path,
            "sha256:<lower-hex>",
            raw,
        )
    })
}

fn required_array<'a>(
    members: &'a [JsonMember<'a>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<&'a [JsonValue<'a>], Box<CommandDiagnostic>> {
    let value = required_value(members, field, path, artifact_path)?;
    value.array_elements().ok_or_else(|| {
        evidence_error(
            "normalized_result_invalid",
            artifact_path,
            path,
            "array",
            json_kind_name(value.kind()),
        )
    })
}

fn required_string_array(
    members: &[JsonMember<'_>],
    field: &str,
    path: &str,
    artifact_path: &str,
) -> Result<Vec<String>, Box<CommandDiagnostic>> {
    required_array(members, field, path, artifact_path)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                evidence_error(
                    "normalized_result_invalid",
                    artifact_path,
                    format!("{path}[{index}]"),
                    "string",
                    json_kind_name(value.kind()),
                )
            })
        })
        .collect()
}

fn evidence_error(
    reason_code: &'static str,
    artifact_path: &str,
    field: impl Into<String>,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, reason_code)
            .with_path(artifact_path)
            .with_field(field)
            .with_expected_value(expected)
            .with_actual_value(actual),
    )
}

fn normalized_status_not_verified_diagnostic(
    status: String,
    artifact_path: &str,
) -> Box<CommandDiagnostic> {
    let reason_code = if status == "disagreement" {
        "checker_disagreement_blocks_release"
    } else {
        "not_verified"
    };
    let actual = if status == "disagreement" {
        "disagreement; checker_disagreement_record required before release retry".to_owned()
    } else {
        status
    };
    Box::new(
        CommandDiagnostic::error(DiagnosticKind::ExternalVerifier, reason_code)
            .with_path(artifact_path)
            .with_field("comparison.status")
            .with_expected_value("all_agree_checked")
            .with_actual_value(actual),
    )
}

fn policy_validation_diagnostic(
    reason_code: &str,
    error: IndependentCheckerPolicyValidationError,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason_code)
        .with_field(error.field)
        .with_expected_value(error.expected_value)
        .with_actual_value(error.actual_value)
}

fn request_validation_diagnostic(
    reason_code: &str,
    error: IndependentCheckerRequestValidationError,
    path: &str,
) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        if error.expected_hash.is_some() || error.actual_hash.is_some() {
            DiagnosticKind::HashMismatch
        } else {
            DiagnosticKind::ExternalVerifier
        },
        reason_code,
    )
    .with_path(path)
    .with_field(error.field.to_string());
    if let (Some(expected), Some(actual)) = (error.expected_hash, error.actual_hash) {
        diagnostic =
            diagnostic.with_hashes(format_hash_string(&expected), format_hash_string(&actual));
    } else {
        if let Some(expected) = error.expected_value {
            diagnostic = diagnostic.with_expected_value(expected.to_string());
        }
        if let Some(actual) = error.actual_value {
            diagnostic = diagnostic.with_actual_value(actual.to_string());
        }
    }
    diagnostic
}

fn command_error_diagnostic(
    reason_code: &str,
    error: IndependentCheckerCommandError,
    path: &str,
) -> CommandDiagnostic {
    let mut diagnostic = CommandDiagnostic::error(
        if error.expected_hash.is_some() || error.actual_hash.is_some() {
            DiagnosticKind::HashMismatch
        } else {
            DiagnosticKind::ExternalVerifier
        },
        reason_code,
    )
    .with_path(path);
    if let Some(field) = error.field {
        diagnostic = diagnostic.with_field(field.to_string());
    }
    if let (Some(expected), Some(actual)) = (error.expected_hash, error.actual_hash) {
        diagnostic =
            diagnostic.with_hashes(format_hash_string(&expected), format_hash_string(&actual));
    } else {
        if let Some(expected) = error.expected_value {
            diagnostic = diagnostic.with_expected_value(expected.to_string());
        }
        if let Some(actual) = error.actual_value {
            diagnostic = diagnostic.with_actual_value(actual.to_string());
        }
    }
    diagnostic
}

fn verified_high_trust_artifact_error(
    error: &npa_package::PackageArtifactError,
    artifact_path: &str,
) -> CommandDiagnostic {
    let reason_code = match error.reason_code {
        npa_package::PackageArtifactErrorReason::NonCanonicalOrder => {
            "verified_high_trust_non_canonical_order"
        }
        npa_package::PackageArtifactErrorReason::SelfHashMismatch => {
            "verified_high_trust_hash_mismatch"
        }
        _ => error.reason_code.as_str(),
    };
    let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason_code)
        .with_path(artifact_path);
    if let Some(field) = error.field.clone().or_else(|| {
        if error.path == "$" {
            None
        } else {
            Some(error.path.clone())
        }
    }) {
        diagnostic = diagnostic.with_field(field);
    }
    if error.reason_code == npa_package::PackageArtifactErrorReason::SelfHashMismatch {
        if let (Some(expected), Some(actual)) = (&error.expected_value, &error.actual_value) {
            diagnostic = diagnostic.with_hashes(expected.clone(), actual.clone());
        }
    } else {
        if let Some(expected) = &error.expected_value {
            diagnostic = diagnostic.with_expected_value(expected.clone());
        }
        if let Some(actual) = &error.actual_value {
            diagnostic = diagnostic.with_actual_value(actual.clone());
        }
    }
    diagnostic
}

fn verified_high_trust_stale_diagnostic(
    checked_json: &str,
    generated_json: &str,
    path: &str,
) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "verified_high_trust_stale",
    )
    .with_path(path)
    .with_hashes(
        format_package_hash(&package_file_hash(generated_json.as_bytes())),
        format_package_hash(&package_file_hash(checked_json.as_bytes())),
    )
}

fn write_failed_diagnostic(path: &str) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::GeneratedArtifact,
        "generated_artifact_write_failed",
    )
    .with_path(path)
}

fn required_profiles() -> Vec<String> {
    IndependentCheckerTrustMode::HighTrust
        .required_checker_profiles()
        .iter()
        .map(|profile| (*profile).to_owned())
        .collect()
}

fn package_hash_from_hash(hash: Hash) -> PackageHash {
    PackageHash::new(hash)
}

fn json_kind_name(kind: JsonValueKind) -> &'static str {
    match kind {
        JsonValueKind::Null => "null",
        JsonValueKind::Bool => "bool",
        JsonValueKind::Number => "number",
        JsonValueKind::String => "string",
        JsonValueKind::Array => "array",
        JsonValueKind::Object => "object",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_api::{IndependentCheckerAuxiliaryError, IndependentCheckerAuxiliaryReasonCode};

    #[test]
    fn package_high_trust_benchmark_failure_maps_release_audit_policy_diagnostic() {
        let result = IndependentCheckerAuxiliaryResult::failed(
            "aux_package_high_trust_benchmark_missing",
            IndependentCheckerAuxiliaryResultKind::AuditBundle,
            [1; 32],
            [2; 32],
            None,
            IndependentCheckerAuxiliaryError::value(
                IndependentCheckerAuxiliaryReasonCode::AuditBundleInvalid,
                "artifacts[performance_benchmark_summary]",
                "external checker benchmark",
                "missing",
            ),
        );

        let diagnostic = release_audit_bundle_failure_diagnostic(
            &result,
            DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH,
        );

        assert_eq!(diagnostic.kind, DiagnosticKind::ExternalVerifier);
        assert_eq!(diagnostic.reason_code, "audit_bundle_invalid");
        assert_eq!(
            diagnostic.path.as_deref(),
            Some(DEFAULT_RELEASE_AUDIT_BUNDLE_MANIFEST_PATH)
        );
        assert_eq!(
            diagnostic.field.as_deref(),
            Some("artifacts[performance_benchmark_summary]")
        );
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some("external checker benchmark")
        );
        assert_eq!(diagnostic.actual_value.as_deref(), Some("missing"));
        assert!(diagnostic.expected_hash.is_none());
        assert!(diagnostic.actual_hash.is_none());
    }

    #[test]
    fn package_high_trust_disagreement_status_requires_disagreement_record() {
        let diagnostic = normalized_status_not_verified_diagnostic(
            "disagreement".to_owned(),
            "build/normalized/package.json",
        );

        assert_eq!(diagnostic.kind, DiagnosticKind::ExternalVerifier);
        assert_eq!(
            diagnostic.reason_code,
            "checker_disagreement_blocks_release"
        );
        assert_eq!(
            diagnostic.path.as_deref(),
            Some("build/normalized/package.json")
        );
        assert_eq!(diagnostic.field.as_deref(), Some("comparison.status"));
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some("all_agree_checked")
        );
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some("disagreement; checker_disagreement_record required before release retry")
        );
    }
}
