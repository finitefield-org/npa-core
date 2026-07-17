use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cli::args::{PackageCommand, PackageCommonOptions, PackageL2AcceptanceOptions};
use npa_cli::diagnostic::{CommandStatus, DiagnosticKind};
use npa_cli::package::run_package_command;
use npa_package::{
    compute_l2_review_input_hash, package_file_hash, parse_package_theorem_index_json,
    L2Acceptance, L2AcceptanceApproval, L2AcceptanceApprovalV2, L2AcceptanceAuthority,
    L2AcceptanceAuthorityStatus, L2AcceptanceEntry, L2AcceptanceEntryV2, L2AcceptancePolicy,
    L2AcceptanceReviewReportRef, L2AcceptanceV2, PackageArtifactOrigin, PackageId, PackagePath,
    PackageTheoremIndexKind, L2_ACCEPTANCE_LEVEL, L2_ACCEPTANCE_POLICY_SCHEMA,
    L2_ACCEPTANCE_REVIEW_PROTOCOL, L2_ACCEPTANCE_SCHEMA, L2_ACCEPTANCE_VALIDATOR_PROFILE,
};

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct L2Fixture {
    directory: PathBuf,
    package_root: PathBuf,
    policy: PathBuf,
    acceptance: PathBuf,
    entry: L2AcceptanceEntry,
    acceptance_model: L2Acceptance,
}

impl L2Fixture {
    fn new() -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let directory = std::env::temp_dir().join(format!(
            "npa-cli-l2-acceptance-{}-{index}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir_all(&directory).unwrap();

        let package_root = repo_root().join("testdata/package/npa-mathlib");
        let theorem_index_source =
            fs::read_to_string(package_root.join("generated/theorem-index.json")).unwrap();
        let theorem_index = parse_package_theorem_index_json(&theorem_index_source).unwrap();
        let current = theorem_index
            .entries
            .iter()
            .find(|entry| {
                entry.kind == PackageTheoremIndexKind::Theorem
                    && entry.artifact.origin == PackageArtifactOrigin::Local
            })
            .unwrap();

        let policy_model = L2AcceptancePolicy {
            schema: L2_ACCEPTANCE_POLICY_SCHEMA.to_owned(),
            policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
            policy_version: 1,
            governance_mode: "independent-subagent-quorum".to_owned(),
            validator_profile: L2_ACCEPTANCE_VALIDATOR_PROFILE.to_owned(),
            review_protocol: L2_ACCEPTANCE_REVIEW_PROTOCOL.to_owned(),
            accepted_level: L2_ACCEPTANCE_LEVEL.to_owned(),
            required_roles: vec![
                "adversarial-review".to_owned(),
                "semantic-review".to_owned(),
            ],
            required_checks: checks(),
            authorities: vec![
                L2AcceptanceAuthority {
                    authority: "finitefield-org/npa-l2-adversarial-review-subagent".to_owned(),
                    authority_version: 1,
                    status: L2AcceptanceAuthorityStatus::Active,
                    reviewer_role: "adversarial-review".to_owned(),
                    agent_task_prefix: "/root/l2_adversarial_".to_owned(),
                    decision_id_prefix: "NPA-L2-ADV-".to_owned(),
                },
                L2AcceptanceAuthority {
                    authority: "finitefield-org/npa-l2-semantic-review-subagent".to_owned(),
                    authority_version: 1,
                    status: L2AcceptanceAuthorityStatus::Active,
                    reviewer_role: "semantic-review".to_owned(),
                    agent_task_prefix: "/root/l2_semantic_".to_owned(),
                    decision_id_prefix: "NPA-L2-SEM-".to_owned(),
                },
            ],
            proof_evidence: false,
        };
        let policy_bytes = policy_model.canonical_json().unwrap();
        let policy = directory.join("policy.json");
        fs::write(&policy, &policy_bytes).unwrap();

        let entry = L2AcceptanceEntry {
            module: current.global_ref.module.clone(),
            theorem: current.global_ref.name.clone(),
            statement_hash: current.statement.core_hash,
            certificate_hash: current.global_ref.certificate_hash,
            accepted_level: L2_ACCEPTANCE_LEVEL.to_owned(),
            approvals: vec![
                approval("adversarial-review", "/root/l2_adversarial_fixture"),
                approval("semantic-review", "/root/l2_semantic_fixture"),
            ],
        };
        let mut acceptance_model = L2Acceptance {
            schema: L2_ACCEPTANCE_SCHEMA.to_owned(),
            policy_id: policy_model.policy_id.clone(),
            policy_version: policy_model.policy_version,
            policy_file_hash: package_file_hash(policy_bytes.as_bytes()),
            source_package: theorem_index.package.clone(),
            source_version: theorem_index.version.clone(),
            aggregator_agent_task: "/root".to_owned(),
            entries: vec![entry.clone()],
            proof_evidence: false,
        };
        let input_hash =
            compute_l2_review_input_hash(&acceptance_model, &acceptance_model.entries[0]);
        for approval in &mut acceptance_model.entries[0].approvals {
            approval.input_hash = input_hash;
        }
        let acceptance = directory.join("acceptance.json");
        fs::write(&acceptance, acceptance_model.canonical_json().unwrap()).unwrap();

        Self {
            directory,
            package_root,
            policy,
            acceptance,
            entry,
            acceptance_model,
        }
    }

    fn options(&self, modules: Vec<npa_cert::Name>) -> PackageL2AcceptanceOptions {
        let mut common = PackageCommonOptions::default();
        common.root = self.package_root.clone();
        common.json = true;
        PackageL2AcceptanceOptions {
            common,
            policy: self.policy.clone(),
            acceptance: self.acceptance.clone(),
            modules,
        }
    }

    fn write_acceptance(&self, acceptance: &L2Acceptance) {
        fs::write(&self.acceptance, acceptance.canonical_json().unwrap()).unwrap();
    }
}

impl Drop for L2Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn validates_exact_hash_bound_l2_entry() {
    let fixture = L2Fixture::new();
    let result = run_package_command(PackageCommand::ValidateL2Acceptance(
        fixture.options(vec![]),
    ));
    assert_eq!(result.status, CommandStatus::Passed);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "l2_theorem_accepted"));
}

#[test]
fn rejects_stale_hashes_unauthorized_decisions_and_incomplete_modules() {
    let fixture = L2Fixture::new();
    let mut stale = fixture.acceptance_model.clone();
    stale.entries[0].statement_hash = package_file_hash(b"stale statement");
    stale.entries[0].certificate_hash = package_file_hash(b"stale certificate");
    let stale_input_hash = compute_l2_review_input_hash(&stale, &stale.entries[0]);
    for approval in &mut stale.entries[0].approvals {
        approval.input_hash = stale_input_hash;
    }
    fixture.write_acceptance(&stale);
    let stale_result = run_package_command(PackageCommand::ValidateL2Acceptance(
        fixture.options(vec![]),
    ));
    assert_eq!(stale_result.status, CommandStatus::Failed);
    assert!(stale_result.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::HashMismatch
            && diagnostic.field.as_deref() == Some("statement_hash")
    }));
    assert!(stale_result.diagnostics.iter().any(|diagnostic| {
        diagnostic.kind == DiagnosticKind::HashMismatch
            && diagnostic.field.as_deref() == Some("certificate_hash")
    }));

    let mut unauthorized = fixture.acceptance_model.clone();
    unauthorized.entries[0].approvals[0].authority = "unreviewed-authority".to_owned();
    fixture.write_acceptance(&unauthorized);
    let unauthorized_result = run_package_command(PackageCommand::ValidateL2Acceptance(
        fixture.options(vec![]),
    ));
    assert_eq!(unauthorized_result.status, CommandStatus::Failed);
    assert!(unauthorized_result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "l2_authority_not_allowed"));

    let mut incomplete_checks = fixture.acceptance_model.clone();
    incomplete_checks.entries[0].approvals[0].checks.pop();
    fixture.write_acceptance(&incomplete_checks);
    let checks_result = run_package_command(PackageCommand::ValidateL2Acceptance(
        fixture.options(vec![]),
    ));
    assert_eq!(checks_result.status, CommandStatus::Failed);
    assert!(checks_result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "l2_review_checks_mismatch"));

    fixture.write_acceptance(&fixture.acceptance_model);
    let incomplete = run_package_command(PackageCommand::ValidateL2Acceptance(
        fixture.options(vec![fixture.entry.module.clone()]),
    ));
    assert_eq!(incomplete.status, CommandStatus::Failed);
    assert!(incomplete
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "l2_selected_module_theorem_missing"));
}

#[test]
fn v2_rejects_a_ledger_for_another_source_package_before_loading_reports() {
    let fixture = L2Fixture::new();
    let policy = repo_root().join("../npa-mathlib/policy/l2-acceptance-policy.json");
    let policy_bytes = fs::read(&policy).unwrap();
    let approval = |role: &str, seed: u8| L2AcceptanceApprovalV2 {
        authority: format!("finitefield-org/npa-l2-{role}-subagent"),
        authority_version: 1,
        decision_id: format!("NPA-L2-{seed}"),
        reviewer_role: role.to_owned(),
        agent_task: format!("/root/l2_{role}_{seed}"),
        review_protocol: "npa.l2.subagent-review.v2".to_owned(),
        input_hash: package_file_hash(b"input"),
        review_report: L2AcceptanceReviewReportRef {
            path: PackagePath::new(format!("l2-reviews/{role}.json")),
            file_hash: package_file_hash(&[seed]),
        },
        verdict: "accepted".to_owned(),
    };
    let ledger = L2AcceptanceV2 {
        schema: "npa.l2_acceptance.v2".to_owned(),
        policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
        policy_version: 2,
        policy_file_hash: package_file_hash(&policy_bytes),
        source_package: PackageId::new("another-proof-package"),
        source_version: fixture.acceptance_model.source_version.clone(),
        aggregator_agent_task: "/root".to_owned(),
        entries: vec![L2AcceptanceEntryV2 {
            module: fixture.entry.module.clone(),
            theorem: fixture.entry.theorem.clone(),
            statement_hash: fixture.entry.statement_hash,
            certificate_hash: fixture.entry.certificate_hash,
            accepted_level: L2_ACCEPTANCE_LEVEL.to_owned(),
            approvals: vec![
                approval("adversarial-review", 1),
                approval("semantic-review", 2),
            ],
        }],
        proof_evidence: false,
    };
    fs::write(&fixture.acceptance, ledger.canonical_json().unwrap()).unwrap();
    let mut options = fixture.options(vec![]);
    options.policy = policy;
    let result = run_package_command(PackageCommand::ValidateL2Acceptance(options));
    assert_eq!(result.status, CommandStatus::Failed);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.reason_code == "l2_acceptance_generated_identity_mismatch"
    }));
}

fn approval(role: &str, agent_task: &str) -> L2AcceptanceApproval {
    let adversarial = role == "adversarial-review";
    L2AcceptanceApproval {
        authority: if adversarial {
            "finitefield-org/npa-l2-adversarial-review-subagent"
        } else {
            "finitefield-org/npa-l2-semantic-review-subagent"
        }
        .to_owned(),
        authority_version: 1,
        decision_id: if adversarial {
            "NPA-L2-ADV-TEST-1"
        } else {
            "NPA-L2-SEM-TEST-1"
        }
        .to_owned(),
        reviewer_role: role.to_owned(),
        agent_task: agent_task.to_owned(),
        review_protocol: L2_ACCEPTANCE_REVIEW_PROTOCOL.to_owned(),
        input_hash: package_file_hash(b"pending"),
        checks: checks(),
        verdict: "accepted".to_owned(),
        rationale: format!("independent {role} accepted the exact fixture theorem"),
    }
}

fn checks() -> Vec<String> {
    vec![
        "certificate-closure-supports-derivation".to_owned(),
        "no-self-assuming-boundary".to_owned(),
        "public-api-semantically-stable".to_owned(),
        "statement-is-derived-not-assumed".to_owned(),
        "statement-matches-mathematical-claim".to_owned(),
    ]
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}
