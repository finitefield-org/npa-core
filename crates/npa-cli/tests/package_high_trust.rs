use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_api::{
    format_hash_string, IndependentCheckerAllowlistEntry,
    IndependentCheckerIdentityManifestReference, IndependentCheckerReleaseMode,
    IndependentCheckerReleasePolicy, IndependentCheckerReleasePolicyAiTriage,
    IndependentCheckerRunnerAxiomPolicy, IndependentCheckerRunnerBudget,
    IndependentCheckerRunnerImportPolicy, IndependentCheckerRunnerPolicy,
    IndependentCheckerTrustMode,
};
use npa_cert::Hash;

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestWorkspace {
    path: PathBuf,
}

impl TestWorkspace {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-high-trust-{}-{label}-{index}",
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

    fn write(&self, path: &str, source: &str) {
        let full_path = self.path.join(path);
        if let Some(parent) = full_path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(full_path, source).unwrap();
    }
}

impl Drop for TestWorkspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn package_high_trust_fails_without_release_audit_bundle_evidence() {
    let workspace = TestWorkspace::new("missing-release-audit");
    fs::create_dir_all(workspace.path().join("pkg")).unwrap();

    let runner = high_trust_runner_policy();
    let challenge_runner = high_trust_runner_policy();
    let release = IndependentCheckerReleasePolicy {
        id: "independent-checker-release".to_owned(),
        version: 1,
        mode: IndependentCheckerReleaseMode::HighTrust,
        runner_policy_hash: runner.policy_hash(),
        challenge_runner_policy_hash: challenge_runner.policy_hash(),
        ai_triage: IndependentCheckerReleasePolicyAiTriage {
            enabled: false,
            required: false,
            input_policy_hash: None,
        },
    };
    workspace.write("ci/runner.high-trust.json", &runner.canonical_json());
    workspace.write(
        "ci/runner.challenge.json",
        &challenge_runner.canonical_json(),
    );
    workspace.write("ci/release.high-trust.json", &release.canonical_json());
    workspace.write("ci/checker-binaries.json", &checker_registry_json(&runner));

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .current_dir(workspace.path())
        .args([
            "package",
            "high-trust",
            "--root",
            "pkg",
            "--release-policy",
            "ci/release.high-trust.json",
            "--release-policy-hash",
            &format_hash_string(&release.policy_hash()),
            "--runner-policy",
            "ci/runner.high-trust.json",
            "--runner-policy-hash",
            &format_hash_string(&runner.policy_hash()),
            "--challenge-runner-policy",
            "ci/runner.challenge.json",
            "--challenge-runner-policy-hash",
            &format_hash_string(&challenge_runner.policy_hash()),
            "--checker-registry",
            "ci/checker-binaries.json",
            "--check",
            "--json",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"command\":\"package high-trust\""));
    assert!(stdout.contains("\"reason_code\":\"not_verified\""));
    assert!(stdout.contains("\"field\":\"release_audit_bundle_manifest\""));
    assert!(stdout
        .contains("ReleaseAuditBundleManifest with external and high-trust-reference evidence"));
}

fn high_trust_runner_policy() -> IndependentCheckerRunnerPolicy {
    let profiles = IndependentCheckerTrustMode::HighTrust
        .required_checker_profiles()
        .iter()
        .map(|profile| (*profile).to_owned())
        .collect::<Vec<_>>();
    let mut budgets = BTreeMap::new();
    for profile in &profiles {
        budgets.insert(
            profile.clone(),
            IndependentCheckerRunnerBudget {
                max_steps: 1000,
                max_memory_mb: 256,
                timeout_ms: 1000,
            },
        );
    }
    let mut checker_allowlist = profiles
        .iter()
        .enumerate()
        .map(|(index, profile)| IndependentCheckerAllowlistEntry {
            profile: profile.clone(),
            checker_id: checker_id(profile),
            binary_id: binary_id(profile),
            binary_hash: hash(10 + index as u8),
            build_hash: hash(20 + index as u8),
            allowed_args: if profile == "external" {
                Vec::new()
            } else {
                vec!["--json".to_owned()]
            },
        })
        .collect::<Vec<_>>();
    checker_allowlist.sort_by(|left, right| left.profile.cmp(&right.profile));
    IndependentCheckerRunnerPolicy {
        id: "independent-checker-high-trust".to_owned(),
        version: 1,
        trust_mode: IndependentCheckerTrustMode::HighTrust,
        required_checker_profiles: profiles.clone(),
        optional_checker_profiles: Vec::new(),
        checker_allowlist,
        checker_identity_manifest: Some(IndependentCheckerIdentityManifestReference {
            path: "ci/checker-identities.json".to_owned(),
            manifest_hash: hash(30),
        }),
        import_policy: IndependentCheckerRunnerImportPolicy {
            mode: "locked_store".to_owned(),
            network: "forbidden".to_owned(),
            require_import_lock_hash: true,
        },
        axiom_policy: IndependentCheckerRunnerAxiomPolicy {
            path: "ci/axiom-policy.toml".to_owned(),
            hash: hash(9),
        },
        budgets,
    }
}

fn checker_registry_json(policy: &IndependentCheckerRunnerPolicy) -> String {
    let entries = policy
        .checker_allowlist
        .iter()
        .map(|entry| {
            format!(
                "{{\"binary_id\":\"{}\",\"path\":\"bin/{}\"}}",
                entry.binary_id, entry.binary_id
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"schema\":\"npa.independent-checker.checker_binary_registry.v1\",\"root_kind\":\"workspace\",\"entries\":[{entries}]}}"
    )
}

fn hash(seed: u8) -> Hash {
    [seed; 32]
}

fn checker_id(profile: &str) -> String {
    match profile {
        "external" => "npa-checker-ext".to_owned(),
        "reference" => "npa-checker-ref".to_owned(),
        "fast-kernel" => "fast-kernel-certificate-verifier".to_owned(),
        "high-trust-reference" => "npa-checker-ref-high-trust".to_owned(),
        other => format!("checker-{other}"),
    }
}

fn binary_id(profile: &str) -> String {
    match profile {
        "external" => "npa-checker-ext-test".to_owned(),
        "reference" => "npa-checker-ref-test".to_owned(),
        "fast-kernel" => "fast-kernel-test".to_owned(),
        "high-trust-reference" => "npa-checker-ref-high-trust-test".to_owned(),
        other => format!("binary-{other}"),
    }
}
