use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use npa_api::{
    checker_disagreement_blocks_automatic_acceptance, proof_acceptance_negative_fixture_catalog,
    validate_proof_acceptance_transition, validate_verified_artifact_identity,
    validate_verified_only_sharing, ProofAcceptanceActorRole, ProofAcceptanceNegativeFixture,
    ProofAcceptanceNegativeFixtureKind, ProofAcceptanceNegativeFixtureRejectionKind,
    ProofAcceptanceState, ProofAcceptanceTransition, ProofAcceptanceTransitionError,
    ProofCandidateIdentity, ProofCandidateKind, ProofCandidateSourceKind, ProofTrustClassification,
    ProofTrustComponent, ProofTrustContractSurface, VerifiedArtifactIdentity,
    VerifiedOnlySharingArtifactKind, VerifiedOnlySharingCheck, VerifiedOnlySharingSurface,
    CHECKER_DISAGREEMENT_VERIFICATION_STATUS,
};

const PREVIOUS_HASH: &str =
    "sha256:0000000000000000000000000000000000000000000000000000000000000001";
const NEXT_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000002";
const POLICY_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000003";
const STALE_HASH: &str = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
const VERIFIED_ARTIFACT_HASH: [u8; 32] = [0x40; 32];

fn hash(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-api should be under workspace crates directory")
        .to_path_buf()
}

fn acceptance_negative_fixture_dir() -> PathBuf {
    workspace_root().join("../npa/develop/proof-using-agents/fixtures/acceptance-negative")
}

fn fixture_for(kind: ProofAcceptanceNegativeFixtureKind) -> ProofAcceptanceNegativeFixture {
    proof_acceptance_negative_fixture_catalog()
        .iter()
        .copied()
        .find(|fixture| fixture.kind == kind)
        .unwrap_or_else(|| panic!("missing negative fixture for {:?}", kind))
}

fn base_candidate_identity() -> ProofCandidateIdentity {
    ProofCandidateIdentity {
        task_kind: ProofCandidateKind::MachineTactic,
        source_kind: ProofCandidateSourceKind::Payload,
        canonical_source_or_payload_hash: hash(1),
        environment_hash: hash(2),
        import_closure_hash: hash(3),
        axiom_policy_hash: hash(4),
        feature_profile_hash: hash(5),
        statement_hash: hash(6),
        goal_fingerprint: hash(7),
        candidate_payload_hash: hash(8),
        deterministic_budget_hash: hash(9),
    }
}

fn certificate_verified_identity(candidate_hash: [u8; 32]) -> VerifiedArtifactIdentity {
    VerifiedArtifactIdentity {
        state: ProofAcceptanceState::CertificateVerified,
        candidate_hash,
        statement_hash: hash(6),
        certificate_hash: hash(20),
        export_hash: hash(21),
        axiom_report_hash: hash(22),
        package_manifest_hash: None,
        package_lock_hash: None,
        verifier_profile: None,
        verifier_binary_hash: None,
        verifier_version_or_build_hash: None,
        release_evidence_kind: None,
        release_evidence_hash: None,
    }
}

fn valid_transition(
    from_state: ProofAcceptanceState,
    to_state: ProofAcceptanceState,
) -> ProofAcceptanceTransition<'static> {
    ProofAcceptanceTransition {
        from_state,
        to_state,
        actor_role: ProofAcceptanceActorRole::VerifierWorker,
        previous_artifact_hash: Some(PREVIOUS_HASH),
        expected_previous_artifact_hash: Some(PREVIOUS_HASH),
        next_artifact_hash: Some(NEXT_HASH),
        policy_hash: Some(POLICY_HASH),
    }
}

fn assert_fixture_file(fixture: ProofAcceptanceNegativeFixture, root: &Path) {
    let path = root.join(format!("{}.json", fixture.id));
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    assert!(
        !path.starts_with(workspace_root().join("proofs")),
        "fixture must not be stored under proofs/**: {}",
        path.display()
    );
    assert!(source.contains(&format!(r#""id": "{}""#, fixture.id)));
    assert!(source.contains(&format!(r#""kind": "{}""#, fixture.kind.as_str())));
    assert!(source.contains(&format!(
        r#""rejection_kind": "{}""#,
        fixture.rejection_kind.as_str()
    )));
    assert!(!source.contains(r#""theorem_artifact": true"#));
}

#[test]
fn proof_acceptance_negative_fixture_catalog_matches_documented_files() {
    let fixtures = proof_acceptance_negative_fixture_catalog();
    assert_eq!(fixtures.len(), 10);

    let root = acceptance_negative_fixture_dir();
    let readme = fs::read_to_string(root.join("README.md")).expect("fixture README should exist");
    for phrase in [
        "score tampering",
        "prompt tampering",
        "sidecar substitution",
        "stale replay",
        "custom axiom",
        "checker disagreement",
    ] {
        assert!(
            readme.contains(phrase),
            "fixture README should mention {phrase:?}"
        );
    }

    let mut ids = BTreeSet::new();
    let mut kinds = BTreeSet::new();
    for fixture in fixtures.iter().copied() {
        assert!(ids.insert(fixture.id));
        assert!(kinds.insert(fixture.kind.as_str()));
        assert_fixture_file(fixture, &root);
    }
}

#[test]
fn proof_acceptance_negative_sidecar_tampering_stays_out_of_verified_evidence() {
    for (kind, component) in [
        (
            ProofAcceptanceNegativeFixtureKind::ScoreTampering,
            ProofTrustComponent::SearchScore,
        ),
        (
            ProofAcceptanceNegativeFixtureKind::PromptTampering,
            ProofTrustComponent::Prompt,
        ),
        (
            ProofAcceptanceNegativeFixtureKind::SidecarSubstitution,
            ProofTrustComponent::ReplaySidecar,
        ),
    ] {
        let fixture = fixture_for(kind);
        assert_eq!(
            fixture.rejection_kind,
            ProofAcceptanceNegativeFixtureRejectionKind::UntrustedSidecarNotEvidence
        );
        assert_eq!(
            component.classification(),
            ProofTrustClassification::UntrustedSidecar
        );
        assert!(!component.may_serialize_as_trusted_evidence());
        assert!(!component.may_claim_verified_state_on(ProofTrustContractSurface::Candidate));
        assert!(!component.may_claim_verified_state_on(ProofTrustContractSurface::Verification));
        assert!(!component.may_claim_verified_state_on(ProofTrustContractSurface::Integration));
        assert!(fixture.blocked_target_state >= ProofAcceptanceState::CertificateVerified);
    }
}

#[test]
fn proof_acceptance_negative_stale_replay_and_budget_tampering_have_structured_rejections() {
    let mut stale = valid_transition(
        ProofAcceptanceState::ProofCandidate,
        ProofAcceptanceState::ReplayVerified,
    );
    stale.expected_previous_artifact_hash = Some(STALE_HASH);

    assert_eq!(
        validate_proof_acceptance_transition(stale).unwrap_err(),
        ProofAcceptanceTransitionError::StaleInputHash {
            from_state: ProofAcceptanceState::ProofCandidate,
            to_state: ProofAcceptanceState::ReplayVerified,
            expected_previous_artifact_hash: STALE_HASH.to_owned(),
            actual_previous_artifact_hash: PREVIOUS_HASH.to_owned(),
        }
    );
    assert_eq!(
        fixture_for(ProofAcceptanceNegativeFixtureKind::StaleReplay)
            .rejection_kind
            .as_str(),
        "stale_input_hash"
    );

    let base = base_candidate_identity();
    let mut tampered_budget = base.clone();
    tampered_budget.deterministic_budget_hash = hash(0x99);
    assert_ne!(base.hash(), tampered_budget.hash());
    assert_eq!(
        fixture_for(ProofAcceptanceNegativeFixtureKind::ModifiedBudgetHash)
            .rejection_kind
            .as_str(),
        "modified_budget_hash_changes_identity"
    );
}

#[test]
fn proof_acceptance_negative_identity_collision_and_unverified_sharing_are_rejected() {
    let candidate = base_candidate_identity();
    let verified = certificate_verified_identity(candidate.hash());
    validate_verified_artifact_identity(&verified).unwrap();
    assert_ne!(candidate.hash(), verified.hash());

    let mut below_verified = verified.clone();
    below_verified.state = ProofAcceptanceState::ProofCandidate;
    assert_eq!(
        validate_verified_artifact_identity(&below_verified)
            .unwrap_err()
            .kind(),
        "state_below_certificate_verified"
    );
    assert_eq!(
        fixture_for(ProofAcceptanceNegativeFixtureKind::IdentityCollisionAttempt)
            .rejection_kind
            .as_str(),
        "identity_collision_rejected"
    );

    let check = VerifiedOnlySharingCheck {
        surface: VerifiedOnlySharingSurface::Premise,
        artifact_kind: VerifiedOnlySharingArtifactKind::UnverifiedLocalLemma,
        state: ProofAcceptanceState::CertificateVerified,
        verified_artifact_identity_hash: Some(&VERIFIED_ARTIFACT_HASH),
        candidate_identity_hash: None,
    };
    assert_eq!(
        validate_verified_only_sharing(check).unwrap_err().kind(),
        "artifact_kind_not_sharable"
    );
    assert_eq!(
        fixture_for(ProofAcceptanceNegativeFixtureKind::UnverifiedLemmaSharing)
            .rejection_kind
            .as_str(),
        "unverified_lemma_sharing_rejected"
    );

    let unverified_fixture_path =
        acceptance_negative_fixture_dir().join("unverified-lemma-sharing.json");
    let unverified_fixture = fs::read_to_string(&unverified_fixture_path).unwrap_or_else(|error| {
        panic!(
            "failed to read {}: {error}",
            unverified_fixture_path.display()
        )
    });
    for state in ["Proposed", "TypeChecked", "ProofTask", "Verified"] {
        assert!(
            unverified_fixture.contains(&format!(r#""local_lemma_state": "{state}""#)),
            "unverified fixture should cover sketch local lemma state {state}"
        );
    }
    assert!(unverified_fixture.contains(r#""parent_proof_dependency""#));

    let parent_proof_check = VerifiedOnlySharingCheck {
        surface: VerifiedOnlySharingSurface::ParentProofDependency,
        artifact_kind: VerifiedOnlySharingArtifactKind::UnverifiedLocalLemma,
        state: ProofAcceptanceState::CertificateVerified,
        verified_artifact_identity_hash: Some(&VERIFIED_ARTIFACT_HASH),
        candidate_identity_hash: None,
    };
    assert_eq!(
        validate_verified_only_sharing(parent_proof_check)
            .unwrap_err()
            .kind(),
        "artifact_kind_not_sharable"
    );
}

#[test]
fn proof_acceptance_negative_axiom_and_checker_disagreement_cases_do_not_advance() {
    for kind in [
        ProofAcceptanceNegativeFixtureKind::CustomAxiomInjection,
        ProofAcceptanceNegativeFixtureKind::SorryAxiomInjection,
    ] {
        let fixture = fixture_for(kind);
        assert_eq!(
            fixture.blocked_target_state,
            ProofAcceptanceState::CertificateVerified
        );
        assert!(matches!(
            fixture.rejection_kind,
            ProofAcceptanceNegativeFixtureRejectionKind::CustomAxiomPolicyRejected
                | ProofAcceptanceNegativeFixtureRejectionKind::SorryAxiomPolicyRejected
        ));
    }

    let fixture = fixture_for(ProofAcceptanceNegativeFixtureKind::CheckerDisagreement);
    assert_eq!(
        fixture.rejection_kind,
        ProofAcceptanceNegativeFixtureRejectionKind::CheckerDisagreementNonAdvancing
    );
    assert!(checker_disagreement_blocks_automatic_acceptance(
        CHECKER_DISAGREEMENT_VERIFICATION_STATUS
    ));
    assert_eq!(
        ProofAcceptanceState::from_verification_result_status(
            CHECKER_DISAGREEMENT_VERIFICATION_STATUS
        ),
        None
    );
}
