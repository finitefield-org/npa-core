use std::fmt;
use std::str::FromStr;

use npa_cert::{CertReducibility, ExportKind, Hash, Name, Opacity};
use npa_tactic::{goal_id_canonical_bytes, GoalId};
use sha2::{Digest, Sha256};

use crate::current::{encode_machine_axiom_ref_wire, MachineAxiomRefWire};
use crate::projection::{GeneratedDeclKind, MachineImportCertificateContext};
use crate::types::KernelCheckProfileId;

/// Canonical proof-acceptance states used at the proof trust boundary.
///
/// These values are distinct from task-service lifecycle states such as
/// `ready`, `leased`, `running`, and `verified`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofAcceptanceState {
    Proposed,
    Parsed,
    TypeChecked,
    ProofCandidate,
    ReplayVerified,
    CertificateGenerated,
    CertificateVerified,
    IndependentVerified,
    Integrated,
    Published,
}

pub const PROOF_ACCEPTANCE_STATES: [ProofAcceptanceState; 10] = [
    ProofAcceptanceState::Proposed,
    ProofAcceptanceState::Parsed,
    ProofAcceptanceState::TypeChecked,
    ProofAcceptanceState::ProofCandidate,
    ProofAcceptanceState::ReplayVerified,
    ProofAcceptanceState::CertificateGenerated,
    ProofAcceptanceState::CertificateVerified,
    ProofAcceptanceState::IndependentVerified,
    ProofAcceptanceState::Integrated,
    ProofAcceptanceState::Published,
];

pub const PROOF_ACCEPTANCE_STATE_WIRE_STRINGS: [&str; 10] = [
    "proposed",
    "parsed",
    "type_checked",
    "proof_candidate",
    "replay_verified",
    "certificate_generated",
    "certificate_verified",
    "independent_verified",
    "integrated",
    "published",
];

pub const PROOF_CANDIDATE_IDENTITY_PROFILE: &str = "npa.proof-candidate-identity.v1";
pub const VERIFIED_ARTIFACT_IDENTITY_PROFILE: &str = "npa.verified-artifact-identity.v1";
pub const VERIFIED_ONLY_SHARING_DEFAULT_MIN_STATE: ProofAcceptanceState =
    ProofAcceptanceState::CertificateVerified;
pub const CHECKER_DISAGREEMENT_VERIFICATION_STATUS: &str = "checker_disagreement";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofAcceptanceNegativeFixtureKind {
    ScoreTampering,
    PromptTampering,
    SidecarSubstitution,
    StaleReplay,
    ModifiedBudgetHash,
    CustomAxiomInjection,
    SorryAxiomInjection,
    IdentityCollisionAttempt,
    UnverifiedLemmaSharing,
    CheckerDisagreement,
}

impl ProofAcceptanceNegativeFixtureKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ScoreTampering => "score_tampering",
            Self::PromptTampering => "prompt_tampering",
            Self::SidecarSubstitution => "sidecar_substitution",
            Self::StaleReplay => "stale_replay",
            Self::ModifiedBudgetHash => "modified_budget_hash",
            Self::CustomAxiomInjection => "custom_axiom_injection",
            Self::SorryAxiomInjection => "sorry_axiom_injection",
            Self::IdentityCollisionAttempt => "identity_collision_attempt",
            Self::UnverifiedLemmaSharing => "unverified_lemma_sharing",
            Self::CheckerDisagreement => "checker_disagreement",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofAcceptanceNegativeFixtureRejectionKind {
    UntrustedSidecarNotEvidence,
    StaleInputHash,
    ModifiedBudgetHashChangesIdentity,
    CustomAxiomPolicyRejected,
    SorryAxiomPolicyRejected,
    IdentityCollisionRejected,
    UnverifiedLemmaSharingRejected,
    CheckerDisagreementNonAdvancing,
}

impl ProofAcceptanceNegativeFixtureRejectionKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UntrustedSidecarNotEvidence => "untrusted_sidecar_not_evidence",
            Self::StaleInputHash => "stale_input_hash",
            Self::ModifiedBudgetHashChangesIdentity => "modified_budget_hash_changes_identity",
            Self::CustomAxiomPolicyRejected => "custom_axiom_policy_rejected",
            Self::SorryAxiomPolicyRejected => "sorry_axiom_policy_rejected",
            Self::IdentityCollisionRejected => "identity_collision_rejected",
            Self::UnverifiedLemmaSharingRejected => "unverified_lemma_sharing_rejected",
            Self::CheckerDisagreementNonAdvancing => "checker_disagreement_non_advancing",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofAcceptanceNegativeFixture {
    pub id: &'static str,
    pub kind: ProofAcceptanceNegativeFixtureKind,
    pub rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind,
    pub blocked_target_state: ProofAcceptanceState,
}

pub const PROOF_ACCEPTANCE_NEGATIVE_FIXTURES: [ProofAcceptanceNegativeFixture; 10] = [
    ProofAcceptanceNegativeFixture {
        id: "score-tampering",
        kind: ProofAcceptanceNegativeFixtureKind::ScoreTampering,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::UntrustedSidecarNotEvidence,
        blocked_target_state: ProofAcceptanceState::CertificateVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "prompt-tampering",
        kind: ProofAcceptanceNegativeFixtureKind::PromptTampering,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::UntrustedSidecarNotEvidence,
        blocked_target_state: ProofAcceptanceState::CertificateVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "sidecar-substitution",
        kind: ProofAcceptanceNegativeFixtureKind::SidecarSubstitution,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::UntrustedSidecarNotEvidence,
        blocked_target_state: ProofAcceptanceState::CertificateVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "stale-replay",
        kind: ProofAcceptanceNegativeFixtureKind::StaleReplay,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::StaleInputHash,
        blocked_target_state: ProofAcceptanceState::ReplayVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "modified-budget-hash",
        kind: ProofAcceptanceNegativeFixtureKind::ModifiedBudgetHash,
        rejection_kind:
            ProofAcceptanceNegativeFixtureRejectionKind::ModifiedBudgetHashChangesIdentity,
        blocked_target_state: ProofAcceptanceState::ReplayVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "custom-axiom-injection",
        kind: ProofAcceptanceNegativeFixtureKind::CustomAxiomInjection,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::CustomAxiomPolicyRejected,
        blocked_target_state: ProofAcceptanceState::CertificateVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "sorry-axiom-injection",
        kind: ProofAcceptanceNegativeFixtureKind::SorryAxiomInjection,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::SorryAxiomPolicyRejected,
        blocked_target_state: ProofAcceptanceState::CertificateVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "identity-collision-attempt",
        kind: ProofAcceptanceNegativeFixtureKind::IdentityCollisionAttempt,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::IdentityCollisionRejected,
        blocked_target_state: ProofAcceptanceState::Integrated,
    },
    ProofAcceptanceNegativeFixture {
        id: "unverified-lemma-sharing",
        kind: ProofAcceptanceNegativeFixtureKind::UnverifiedLemmaSharing,
        rejection_kind: ProofAcceptanceNegativeFixtureRejectionKind::UnverifiedLemmaSharingRejected,
        blocked_target_state: ProofAcceptanceState::CertificateVerified,
    },
    ProofAcceptanceNegativeFixture {
        id: "checker-disagreement",
        kind: ProofAcceptanceNegativeFixtureKind::CheckerDisagreement,
        rejection_kind:
            ProofAcceptanceNegativeFixtureRejectionKind::CheckerDisagreementNonAdvancing,
        blocked_target_state: ProofAcceptanceState::IndependentVerified,
    },
];

pub const fn proof_acceptance_negative_fixture_catalog() -> &'static [ProofAcceptanceNegativeFixture]
{
    &PROOF_ACCEPTANCE_NEGATIVE_FIXTURES
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofCandidateKind {
    MachineTactic,
    ProofSkeleton,
    CoreTerm,
    HumanSourcePatch,
    SolverCertificate,
    TaskPlan,
    AuditResult,
}

impl ProofCandidateKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MachineTactic => "machine_tactic",
            Self::ProofSkeleton => "proof_skeleton",
            Self::CoreTerm => "core_term",
            Self::HumanSourcePatch => "human_source_patch",
            Self::SolverCertificate => "solver_certificate",
            Self::TaskPlan => "task_plan",
            Self::AuditResult => "audit_result",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofCandidateSourceKind {
    CanonicalSource,
    Payload,
}

impl ProofCandidateSourceKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CanonicalSource => "canonical_source",
            Self::Payload => "payload",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofCandidateIdentity {
    pub task_kind: ProofCandidateKind,
    pub source_kind: ProofCandidateSourceKind,
    pub canonical_source_or_payload_hash: Hash,
    pub environment_hash: Hash,
    pub import_closure_hash: Hash,
    pub axiom_policy_hash: Hash,
    pub feature_profile_hash: Hash,
    pub statement_hash: Hash,
    pub goal_fingerprint: Hash,
    pub candidate_payload_hash: Hash,
    pub deterministic_budget_hash: Hash,
}

impl ProofCandidateIdentity {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        proof_candidate_identity_canonical_bytes(self)
    }

    pub fn hash(&self) -> Hash {
        proof_candidate_identity_hash(self)
    }
}

pub fn proof_candidate_identity_canonical_bytes(identity: &ProofCandidateIdentity) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, PROOF_CANDIDATE_IDENTITY_PROFILE);
    encode_string(&mut out, identity.task_kind.as_str());
    encode_string(&mut out, identity.source_kind.as_str());
    encode_hash(&mut out, &identity.canonical_source_or_payload_hash);
    encode_hash(&mut out, &identity.environment_hash);
    encode_hash(&mut out, &identity.import_closure_hash);
    encode_hash(&mut out, &identity.axiom_policy_hash);
    encode_hash(&mut out, &identity.feature_profile_hash);
    encode_hash(&mut out, &identity.statement_hash);
    encode_hash(&mut out, &identity.goal_fingerprint);
    encode_hash(&mut out, &identity.candidate_payload_hash);
    encode_hash(&mut out, &identity.deterministic_budget_hash);
    out
}

pub fn proof_candidate_identity_hash(identity: &ProofCandidateIdentity) -> Hash {
    hash_with_domain(
        "npa.proof-candidate-identity.hash.v1",
        &proof_candidate_identity_canonical_bytes(identity),
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerifiedArtifactReleaseEvidenceKind {
    ReferenceCheckerOnly,
    HighTrust,
}

impl VerifiedArtifactReleaseEvidenceKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReferenceCheckerOnly => "reference_checker_only",
            Self::HighTrust => "high_trust",
        }
    }

    pub fn parse(value: &str) -> Result<Self, VerifiedArtifactReleaseEvidenceKindParseError> {
        match value {
            "reference_checker_only" => Ok(Self::ReferenceCheckerOnly),
            "high_trust" => Ok(Self::HighTrust),
            _ => Err(VerifiedArtifactReleaseEvidenceKindParseError {
                value: value.to_owned(),
            }),
        }
    }
}

impl FromStr for VerifiedArtifactReleaseEvidenceKind {
    type Err = VerifiedArtifactReleaseEvidenceKindParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::parse(value)
    }
}

impl fmt::Display for VerifiedArtifactReleaseEvidenceKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedArtifactReleaseEvidenceKindParseError {
    value: String,
}

impl VerifiedArtifactReleaseEvidenceKindParseError {
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl fmt::Display for VerifiedArtifactReleaseEvidenceKindParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unknown verified artifact release-evidence kind {:?}",
            self.value
        )
    }
}

impl std::error::Error for VerifiedArtifactReleaseEvidenceKindParseError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedArtifactIdentity {
    pub state: ProofAcceptanceState,
    pub candidate_hash: Hash,
    pub statement_hash: Hash,
    pub certificate_hash: Hash,
    pub export_hash: Hash,
    pub axiom_report_hash: Hash,
    pub package_manifest_hash: Option<Hash>,
    pub package_lock_hash: Option<Hash>,
    pub verifier_profile: Option<String>,
    pub verifier_binary_hash: Option<Hash>,
    pub verifier_version_or_build_hash: Option<Hash>,
    pub release_evidence_kind: Option<VerifiedArtifactReleaseEvidenceKind>,
    pub release_evidence_hash: Option<Hash>,
}

impl VerifiedArtifactIdentity {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        verified_artifact_identity_canonical_bytes(self)
    }

    pub fn hash(&self) -> Hash {
        verified_artifact_identity_hash(self)
    }

    pub fn validate(&self) -> Result<(), VerifiedArtifactIdentityError> {
        validate_verified_artifact_identity(self)
    }
}

pub fn verified_artifact_identity_canonical_bytes(identity: &VerifiedArtifactIdentity) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, VERIFIED_ARTIFACT_IDENTITY_PROFILE);
    encode_string(&mut out, identity.state.as_str());
    encode_hash(&mut out, &identity.candidate_hash);
    encode_hash(&mut out, &identity.statement_hash);
    encode_hash(&mut out, &identity.certificate_hash);
    encode_hash(&mut out, &identity.export_hash);
    encode_hash(&mut out, &identity.axiom_report_hash);
    encode_option_hash(&mut out, identity.package_manifest_hash.as_ref());
    encode_option_hash(&mut out, identity.package_lock_hash.as_ref());
    encode_option_string(&mut out, identity.verifier_profile.as_deref());
    encode_option_hash(&mut out, identity.verifier_binary_hash.as_ref());
    encode_option_hash(&mut out, identity.verifier_version_or_build_hash.as_ref());
    encode_option_release_evidence_kind(&mut out, identity.release_evidence_kind);
    encode_option_hash(&mut out, identity.release_evidence_hash.as_ref());
    out
}

pub fn verified_artifact_identity_hash(identity: &VerifiedArtifactIdentity) -> Hash {
    hash_with_domain(
        "npa.verified-artifact-identity.hash.v1",
        &verified_artifact_identity_canonical_bytes(identity),
    )
}

pub fn validate_verified_artifact_identity(
    identity: &VerifiedArtifactIdentity,
) -> Result<(), VerifiedArtifactIdentityError> {
    if !identity.state.is_verified_artifact_state() {
        return Err(
            VerifiedArtifactIdentityError::StateBelowCertificateVerified {
                state: identity.state,
            },
        );
    }

    if identity.state >= ProofAcceptanceState::IndependentVerified {
        match identity.verifier_profile.as_deref() {
            Some("") => {
                return Err(VerifiedArtifactIdentityError::MissingVerifierProfile {
                    state: identity.state,
                });
            }
            Some(profile) if profile.chars().any(char::is_control) => {
                return Err(VerifiedArtifactIdentityError::InvalidVerifierProfile {
                    state: identity.state,
                });
            }
            Some(_) => {}
            None => {
                return Err(VerifiedArtifactIdentityError::MissingVerifierProfile {
                    state: identity.state,
                });
            }
        }
        if identity.verifier_binary_hash.is_none() {
            return Err(VerifiedArtifactIdentityError::MissingVerifierBinaryHash {
                state: identity.state,
            });
        }
        if identity.verifier_version_or_build_hash.is_none() {
            return Err(
                VerifiedArtifactIdentityError::MissingVerifierVersionOrBuildHash {
                    state: identity.state,
                },
            );
        }
    }

    if identity.state >= ProofAcceptanceState::Integrated {
        if identity.package_manifest_hash.is_none() && identity.package_lock_hash.is_none() {
            return Err(
                VerifiedArtifactIdentityError::MissingPackageManifestOrLockHash {
                    state: identity.state,
                },
            );
        }
        if identity.release_evidence_kind.is_none() {
            return Err(VerifiedArtifactIdentityError::MissingReleaseEvidenceKind {
                state: identity.state,
            });
        }
        if identity.release_evidence_hash.is_none() {
            return Err(VerifiedArtifactIdentityError::MissingReleaseEvidenceHash {
                state: identity.state,
            });
        }
    }

    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifiedArtifactIdentityError {
    StateBelowCertificateVerified { state: ProofAcceptanceState },
    MissingVerifierProfile { state: ProofAcceptanceState },
    InvalidVerifierProfile { state: ProofAcceptanceState },
    MissingVerifierBinaryHash { state: ProofAcceptanceState },
    MissingVerifierVersionOrBuildHash { state: ProofAcceptanceState },
    MissingPackageManifestOrLockHash { state: ProofAcceptanceState },
    MissingReleaseEvidenceKind { state: ProofAcceptanceState },
    MissingReleaseEvidenceHash { state: ProofAcceptanceState },
}

impl VerifiedArtifactIdentityError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::StateBelowCertificateVerified { .. } => "state_below_certificate_verified",
            Self::MissingVerifierProfile { .. } => "missing_verifier_profile",
            Self::InvalidVerifierProfile { .. } => "invalid_verifier_profile",
            Self::MissingVerifierBinaryHash { .. } => "missing_verifier_binary_hash",
            Self::MissingVerifierVersionOrBuildHash { .. } => {
                "missing_verifier_version_or_build_hash"
            }
            Self::MissingPackageManifestOrLockHash { .. } => {
                "missing_package_manifest_or_lock_hash"
            }
            Self::MissingReleaseEvidenceKind { .. } => "missing_release_evidence_kind",
            Self::MissingReleaseEvidenceHash { .. } => "missing_release_evidence_hash",
        }
    }
}

impl fmt::Display for VerifiedArtifactIdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for VerifiedArtifactIdentityError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerifiedOnlySharingSurface {
    Premise,
    BlackboardVerifiedFact,
    TaskDependencyRelease,
    ParentProofDependency,
}

impl VerifiedOnlySharingSurface {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Premise => "premise",
            Self::BlackboardVerifiedFact => "blackboard_verified_fact",
            Self::TaskDependencyRelease => "task_dependency_release",
            Self::ParentProofDependency => "parent_proof_dependency",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerifiedOnlySharingArtifactKind {
    VerifiedArtifactIdentity,
    CandidateArtifact,
    ReplaySidecar,
    Cache,
    SidecarIndex,
    SearchScore,
    UnverifiedLocalLemma,
    TheoremGraphAdvisoryOutput,
}

impl VerifiedOnlySharingArtifactKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::VerifiedArtifactIdentity => "verified_artifact_identity",
            Self::CandidateArtifact => "candidate_artifact",
            Self::ReplaySidecar => "replay_sidecar",
            Self::Cache => "cache",
            Self::SidecarIndex => "sidecar_index",
            Self::SearchScore => "search_score",
            Self::UnverifiedLocalLemma => "unverified_local_lemma",
            Self::TheoremGraphAdvisoryOutput => "theorem_graph_advisory_output",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedOnlySharingCheck<'a> {
    pub surface: VerifiedOnlySharingSurface,
    pub artifact_kind: VerifiedOnlySharingArtifactKind,
    pub state: ProofAcceptanceState,
    pub verified_artifact_identity_hash: Option<&'a Hash>,
    pub candidate_identity_hash: Option<&'a Hash>,
}

pub fn is_verified_only_sharable(check: VerifiedOnlySharingCheck<'_>) -> bool {
    validate_verified_only_sharing(check).is_ok()
}

pub fn validate_verified_only_sharing(
    check: VerifiedOnlySharingCheck<'_>,
) -> Result<(), VerifiedOnlySharingError> {
    if check.state < VERIFIED_ONLY_SHARING_DEFAULT_MIN_STATE {
        return Err(VerifiedOnlySharingError::StateBelowSharingThreshold {
            surface: check.surface,
            state: check.state,
            minimum_state: VERIFIED_ONLY_SHARING_DEFAULT_MIN_STATE,
        });
    }

    if check.artifact_kind != VerifiedOnlySharingArtifactKind::VerifiedArtifactIdentity {
        return Err(VerifiedOnlySharingError::ArtifactKindNotSharable {
            surface: check.surface,
            artifact_kind: check.artifact_kind,
        });
    }

    if check.verified_artifact_identity_hash.is_none() {
        if check.surface == VerifiedOnlySharingSurface::TaskDependencyRelease
            && check.candidate_identity_hash.is_some()
        {
            return Err(
                VerifiedOnlySharingError::CandidateIdentityCannotReleaseTaskDependency {
                    surface: check.surface,
                },
            );
        }
        return Err(
            VerifiedOnlySharingError::MissingVerifiedArtifactIdentityHash {
                surface: check.surface,
            },
        );
    }

    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifiedOnlySharingError {
    StateBelowSharingThreshold {
        surface: VerifiedOnlySharingSurface,
        state: ProofAcceptanceState,
        minimum_state: ProofAcceptanceState,
    },
    ArtifactKindNotSharable {
        surface: VerifiedOnlySharingSurface,
        artifact_kind: VerifiedOnlySharingArtifactKind,
    },
    MissingVerifiedArtifactIdentityHash {
        surface: VerifiedOnlySharingSurface,
    },
    CandidateIdentityCannotReleaseTaskDependency {
        surface: VerifiedOnlySharingSurface,
    },
}

impl VerifiedOnlySharingError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::StateBelowSharingThreshold { .. } => "state_below_sharing_threshold",
            Self::ArtifactKindNotSharable { .. } => "artifact_kind_not_sharable",
            Self::MissingVerifiedArtifactIdentityHash { .. } => {
                "missing_verified_artifact_identity_hash"
            }
            Self::CandidateIdentityCannotReleaseTaskDependency { .. } => {
                "candidate_identity_cannot_release_task_dependency"
            }
        }
    }
}

impl fmt::Display for VerifiedOnlySharingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for VerifiedOnlySharingError {}

pub const LOCAL_LEMMA_PROOF_TASK_IDENTITY_PROFILE: &str = "npa.local-lemma.proof-task-identity.v1";
pub const LOCAL_LEMMA_SOURCE_FREE_VERIFIER_RESULT_PROFILE: &str =
    "npa.local-lemma.source-free-verifier-result.v1";
pub const LOCAL_LEMMA_AVAILABLE_DEPENDENCY_IDENTITY_PROFILE: &str =
    "npa.local-lemma.available-dependency-identity.v1";
pub const LOCAL_LEMMA_GENERALIZED_CONTEXT_PROFILE: &str = "npa.local-lemma.generalized-context.v1";
pub const LOCAL_LEMMA_VERIFICATION_COMMAND_PROFILE: &str =
    "npa.local-lemma.verification-command.v1";
pub const LOCAL_LEMMA_PROOF_TASK_HANDOFF_PROFILE: &str = "npa.local-lemma.proof-task-handoff.v1";
pub const LOCAL_LEMMA_AXIOM_SUMMARY_PROFILE: &str = "npa.local-lemma.axiom-summary.v1";
pub const LOCAL_LEMMA_VERIFIED_ARTIFACT_RECORD_PROFILE: &str =
    "npa.local-lemma.verified-artifact-record.v1";
pub const THEOREM_INVENTION_ARTIFACT_PROFILE: &str = "npa.theorem-invention.artifact.v1";
pub const THEOREM_INVENTION_GENERALIZED_CONTEXT_PROFILE: &str =
    "npa.theorem-invention.generalized-context.v1";
pub const THEOREM_INVENTION_VERIFICATION_COMMAND_PROFILE: &str =
    "npa.theorem-invention.verification-command.v1";
pub const INVENTED_CANDIDATE_IMPORT_CLOSURE_PROFILE: &str =
    "npa.theorem-invention.typecheck.import-closure.v1";
pub const INVENTED_CANDIDATE_TYPECHECK_WITNESS_PROFILE: &str =
    "npa.theorem-invention.typecheck.witness.v1";
pub const INVENTED_CANDIDATE_TYPECHECK_REQUEST_PROFILE: &str =
    "npa.theorem-invention.typecheck.request.v1";
pub const INVENTED_CANDIDATE_TYPECHECK_HANDOFF_PROFILE: &str =
    "npa.theorem-invention.typecheck.handoff.v1";
pub const INVENTED_CANDIDATE_TYPECHECK_BLOCKER_PROFILE: &str =
    "npa.theorem-invention.typecheck.blocker.v1";
pub const INVENTED_LEMMA_AUTHORING_COMMAND_PROFILE: &str =
    "npa.theorem-invention.proof-task.authoring-command.v1";
pub const INVENTED_LEMMA_PACKAGE_SIDE_EFFECT_PROFILE: &str =
    "npa.theorem-invention.proof-task.package-side-effect.v1";
pub const INVENTED_LEMMA_ARTIFACT_READINESS_PROFILE: &str =
    "npa.theorem-invention.proof-task.artifact-readiness.v1";
pub const INVENTED_LEMMA_PROOF_TASK_HANDOFF_PROFILE: &str =
    "npa.theorem-invention.proof-task.handoff.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremLevel {
    L0Statement,
    L1EvidencePackage,
    L2DerivedCertificate,
    L3PublicClosure,
    Unknown,
}

impl TheoremLevel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::L0Statement => "l0_statement",
            Self::L1EvidencePackage => "l1_evidence_package",
            Self::L2DerivedCertificate => "l2_derived_certificate",
            Self::L3PublicClosure => "l3_public_closure",
            Self::Unknown => "unknown",
        }
    }

    pub const fn is_l2_derived_certificate(self) -> bool {
        matches!(self, Self::L2DerivedCertificate)
    }

    pub const fn is_l3_public_closure(self) -> bool {
        matches!(self, Self::L3PublicClosure)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremInventionArtifactKind {
    CandidateSidecar,
    ProofCorpusTheoremArtifact,
}

impl TheoremInventionArtifactKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CandidateSidecar => "candidate_sidecar",
            Self::ProofCorpusTheoremArtifact => "proof_corpus_theorem_artifact",
        }
    }

    pub const fn is_checked_artifact(self) -> bool {
        matches!(self, Self::ProofCorpusTheoremArtifact)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremInventionPromotionIntent {
    AuthoringCandidate,
    BlockedPrerequisite,
    PromotionReady,
}

impl TheoremInventionPromotionIntent {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AuthoringCandidate => "authoring_candidate",
            Self::BlockedPrerequisite => "blocked_prerequisite",
            Self::PromotionReady => "promotion_ready",
        }
    }

    pub const fn is_promotion_ready(self) -> bool {
        matches!(self, Self::PromotionReady)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremInventionVerificationCommandKind {
    BuildModule,
    VerifyModuleSourceFree,
}

impl TheoremInventionVerificationCommandKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BuildModule => "build_module",
            Self::VerifyModuleSourceFree => "verify_module_source_free",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremInventionGeneralizedContextBinder {
    pub binder_id: String,
    pub type_hash: Hash,
    pub dependency_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremInventionGeneralizedContext {
    pub context_hash: Hash,
    pub binders: Vec<TheoremInventionGeneralizedContextBinder>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremInventionVerificationCommand {
    pub command_hash: Hash,
    pub kind: TheoremInventionVerificationCommandKind,
    pub module: String,
    pub verified_cache_authoring: bool,
    pub package_metadata: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremInventionArtifact {
    pub artifact_identity_hash: Hash,
    pub artifact_kind: TheoremInventionArtifactKind,
    pub theorem_level: TheoremLevel,
    pub statement_hash: Hash,
    pub normalized_statement: String,
    pub generalized_context: TheoremInventionGeneralizedContext,
    pub source_module: String,
    pub target_proof_corpus_module: String,
    pub declaration_name: String,
    pub dependency_identities: Vec<Hash>,
    pub import_closure: Vec<String>,
    pub axiom_policy_hash: Hash,
    pub replay_path: Option<String>,
    pub replay_hash: Option<Hash>,
    pub certificate_path: Option<String>,
    pub certificate_hash: Option<Hash>,
    pub verification_commands: Vec<TheoremInventionVerificationCommand>,
    pub promotion_intent: TheoremInventionPromotionIntent,
    pub prerequisite_blocker: Option<String>,
    pub conclusion_assuming: bool,
    pub replay_is_stale: bool,
    pub import_closure_is_stale: bool,
    pub axiom_policy_widened: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InventedCandidateTypecheckStatus {
    TypeChecked,
    Rejected,
}

impl InventedCandidateTypecheckStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TypeChecked => "type_checked",
            Self::Rejected => "rejected",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InventedCandidateImportIdentity {
    pub module: String,
    pub import_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedCandidateTypecheckWitness {
    pub witness_hash: Hash,
    pub status: InventedCandidateTypecheckStatus,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub import_closure_hash: Hash,
    pub axiom_policy_hash: Hash,
    pub target_proof_corpus_module: String,
    pub diagnostic_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedCandidateTypecheckRequest {
    pub request_hash: Hash,
    pub candidate_id: String,
    pub source_module: String,
    pub target_proof_corpus_module: String,
    pub declaration_name: String,
    pub normalized_statement: String,
    pub statement_hash: Hash,
    pub generalized_context: TheoremInventionGeneralizedContext,
    pub environment_hash: Hash,
    pub import_identities: Vec<InventedCandidateImportIdentity>,
    pub required_import_modules: Vec<String>,
    pub axiom_policy_hash: Hash,
    pub expected_axiom_policy_hash: Hash,
    pub typecheck_witness: Option<InventedCandidateTypecheckWitness>,
    pub conclusion_assuming: bool,
    pub axiom_policy_widened: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedCandidateTypecheckHandoff {
    pub handoff_hash: Hash,
    pub request_hash: Hash,
    pub candidate_id: String,
    pub source_module: String,
    pub target_proof_corpus_module: String,
    pub declaration_name: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub import_identities: Vec<InventedCandidateImportIdentity>,
    pub axiom_policy_hash: Hash,
    pub generalized_context: TheoremInventionGeneralizedContext,
    pub expected_authoring_commands: Vec<TheoremInventionVerificationCommand>,
    pub unproved_storage_kind: LocalLemmaUnprovedStorageKind,
    pub creates_theorem_declaration: bool,
}

impl InventedCandidateTypecheckHandoff {
    pub const fn can_create_proof_task(&self) -> bool {
        self.unproved_storage_kind.is_unproved_sidecar() && !self.creates_theorem_declaration
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InventedCandidateTypecheckBlockerReason {
    IllTypedStatement,
    StaleEnvironment,
    MissingImport,
    WidenedAxiomPolicy,
    ConclusionAssumingBoundary,
}

impl InventedCandidateTypecheckBlockerReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::IllTypedStatement => "ill_typed_statement",
            Self::StaleEnvironment => "stale_environment",
            Self::MissingImport => "missing_import",
            Self::WidenedAxiomPolicy => "widened_axiom_policy",
            Self::ConclusionAssumingBoundary => "conclusion_assuming_boundary",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedCandidateTypecheckBlocker {
    pub blocker_hash: Hash,
    pub request_hash: Hash,
    pub candidate_id: String,
    pub target_proof_corpus_module: String,
    pub declaration_name: String,
    pub statement_hash: Hash,
    pub reason: InventedCandidateTypecheckBlockerReason,
    pub evidence_hash: Option<Hash>,
    pub unproved_storage_kind: LocalLemmaUnprovedStorageKind,
    pub creates_theorem_declaration: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InventedCandidateTypecheckOutcome {
    Accepted(InventedCandidateTypecheckHandoff),
    Blocked(InventedCandidateTypecheckBlocker),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InventedLemmaAuthoringCommandKind {
    BuildModule,
    VerifyModuleSourceFree,
    VerifyChangedOnlySourceFree,
    CheckCorpusAuthoring,
}

impl InventedLemmaAuthoringCommandKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BuildModule => "build_module",
            Self::VerifyModuleSourceFree => "verify_module_source_free",
            Self::VerifyChangedOnlySourceFree => "verify_changed_only_source_free",
            Self::CheckCorpusAuthoring => "check_corpus_authoring",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedLemmaAuthoringCommand {
    pub command_hash: Hash,
    pub kind: InventedLemmaAuthoringCommandKind,
    pub module: Option<String>,
    pub verified_cache_authoring: bool,
    pub package_metadata: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedLemmaPackageSideEffectPolicy {
    pub policy_hash: Hash,
    pub package_lock_updated: bool,
    pub package_theorem_index_updated: bool,
    pub axiom_report_updated: bool,
    pub publish_plan_updated: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedLemmaArtifactReadiness {
    pub readiness_hash: Hash,
    pub theorem_level: TheoremLevel,
    pub source_exists: bool,
    pub certificate_exists: bool,
    pub meta_exists: bool,
    pub replay_exists: bool,
    pub source_free_verified: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedLemmaProofTaskHandoff {
    pub handoff_hash: Hash,
    pub typecheck_request_hash: Hash,
    pub typecheck_handoff_hash: Hash,
    pub candidate_id: String,
    pub source_module: String,
    pub target_proof_corpus_module: String,
    pub declaration_name: String,
    pub theorem_statement: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub generalized_context: TheoremInventionGeneralizedContext,
    pub dependency_identities: Vec<LocalLemmaAvailableDependencyIdentity>,
    pub import_identities: Vec<InventedCandidateImportIdentity>,
    pub import_closure_hash: Hash,
    pub axiom_policy_hash: Hash,
    pub source_path: String,
    pub certificate_path: String,
    pub meta_path: String,
    pub replay_path: String,
    pub expected_authoring_commands: Vec<InventedLemmaAuthoringCommand>,
    pub package_side_effect_policy: InventedLemmaPackageSideEffectPolicy,
    pub local_lemma_handoff_hash: Hash,
    pub creates_theorem_declaration: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InventedLemmaProofTaskField {
    HandoffHash,
    TypecheckRequestHash,
    TypecheckHandoffHash,
    CandidateId,
    SourceModule,
    TargetProofCorpusModule,
    DeclarationName,
    TheoremStatement,
    StatementHash,
    ExpectedTypeHash,
    EnvironmentHash,
    ImportClosureHash,
    AxiomPolicyHash,
    GeneralizedContextHash,
    SourcePath,
    CertificatePath,
    MetaPath,
    ReplayPath,
    AuthoringCommandHash,
    PackageSideEffectPolicyHash,
    PackageLockUpdated,
    PackageTheoremIndexUpdated,
    AxiomReportUpdated,
    PublishPlanUpdated,
    LocalLemmaHandoffHash,
    ReadinessHash,
    TheoremLevel,
    SourceArtifact,
    CertificateArtifact,
    MetaArtifact,
    ReplayArtifact,
    SourceFreeVerifierResultStatus,
}

impl InventedLemmaProofTaskField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::HandoffHash => "handoff_hash",
            Self::TypecheckRequestHash => "typecheck_request_hash",
            Self::TypecheckHandoffHash => "typecheck_handoff_hash",
            Self::CandidateId => "candidate_id",
            Self::SourceModule => "source_module",
            Self::TargetProofCorpusModule => "target_proof_corpus_module",
            Self::DeclarationName => "declaration_name",
            Self::TheoremStatement => "theorem_statement",
            Self::StatementHash => "statement_hash",
            Self::ExpectedTypeHash => "expected_type_hash",
            Self::EnvironmentHash => "environment_hash",
            Self::ImportClosureHash => "import_closure_hash",
            Self::AxiomPolicyHash => "axiom_policy_hash",
            Self::GeneralizedContextHash => "generalized_context_hash",
            Self::SourcePath => "source_path",
            Self::CertificatePath => "certificate_path",
            Self::MetaPath => "meta_path",
            Self::ReplayPath => "replay_path",
            Self::AuthoringCommandHash => "authoring_command_hash",
            Self::PackageSideEffectPolicyHash => "package_side_effect_policy_hash",
            Self::PackageLockUpdated => "package_lock_updated",
            Self::PackageTheoremIndexUpdated => "package_theorem_index_updated",
            Self::AxiomReportUpdated => "axiom_report_updated",
            Self::PublishPlanUpdated => "publish_plan_updated",
            Self::LocalLemmaHandoffHash => "local_lemma_handoff_hash",
            Self::ReadinessHash => "readiness_hash",
            Self::TheoremLevel => "theorem_level",
            Self::SourceArtifact => "source_artifact",
            Self::CertificateArtifact => "certificate_artifact",
            Self::MetaArtifact => "meta_artifact",
            Self::ReplayArtifact => "replay_artifact",
            Self::SourceFreeVerifierResultStatus => "source_free_verifier_result_status",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedLemmaProofTaskError {
    kind: InventedLemmaProofTaskErrorKind,
}

impl InventedLemmaProofTaskError {
    fn new(kind: InventedLemmaProofTaskErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &InventedLemmaProofTaskErrorKind {
        &self.kind
    }
}

impl fmt::Display for InventedLemmaProofTaskError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.as_str())
    }
}

impl std::error::Error for InventedLemmaProofTaskError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InventedLemmaProofTaskErrorKind {
    EmptyIdentifier {
        field: InventedLemmaProofTaskField,
    },
    IdentifierMismatch {
        field: InventedLemmaProofTaskField,
        expected: String,
        actual: String,
    },
    HashMismatch {
        field: InventedLemmaProofTaskField,
        expected: Hash,
        actual: Hash,
    },
    CandidateTypecheckInvalid {
        error_kind: String,
    },
    LocalLemmaHandoffInvalid {
        error_kind: String,
    },
    DependencyNotSharable {
        error_kind: &'static str,
    },
    UnexpectedAuthoringCommandCount {
        expected: usize,
        actual: usize,
    },
    AuthoringCommandKindMismatch {
        index: usize,
        expected: InventedLemmaAuthoringCommandKind,
        actual: InventedLemmaAuthoringCommandKind,
    },
    CommandModuleRequired {
        kind: InventedLemmaAuthoringCommandKind,
    },
    CommandModuleNotAllowed {
        kind: InventedLemmaAuthoringCommandKind,
    },
    PackageMetadataNotAllowed {
        kind: InventedLemmaAuthoringCommandKind,
    },
    VerifiedCacheAuthoringNotAllowed {
        kind: InventedLemmaAuthoringCommandKind,
    },
    VerifiedCacheAuthoringRequired {
        kind: InventedLemmaAuthoringCommandKind,
    },
    PackageSideEffectNotAllowed {
        field: InventedLemmaProofTaskField,
    },
    CreatesTheoremDeclaration,
    ReadinessRequired {
        status: LocalLemmaProofTaskStatus,
    },
    TheoremArtifactRequired {
        status: LocalLemmaProofTaskStatus,
    },
    TheoremArtifactNotAllowed {
        status: LocalLemmaProofTaskStatus,
    },
    ArtifactNotReady {
        field: InventedLemmaProofTaskField,
    },
    NonL2Artifact {
        theorem_level: TheoremLevel,
    },
    ParentHoleMustRemainUnresolved {
        status: LocalLemmaProofTaskStatus,
        parent_hole: LocalLemmaParentHoleDisposition,
    },
}

impl InventedLemmaProofTaskErrorKind {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::IdentifierMismatch { .. } => "identifier_mismatch",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::CandidateTypecheckInvalid { .. } => "candidate_typecheck_invalid",
            Self::LocalLemmaHandoffInvalid { .. } => "local_lemma_handoff_invalid",
            Self::DependencyNotSharable { .. } => "dependency_not_sharable",
            Self::UnexpectedAuthoringCommandCount { .. } => "unexpected_authoring_command_count",
            Self::AuthoringCommandKindMismatch { .. } => "authoring_command_kind_mismatch",
            Self::CommandModuleRequired { .. } => "command_module_required",
            Self::CommandModuleNotAllowed { .. } => "command_module_not_allowed",
            Self::PackageMetadataNotAllowed { .. } => "package_metadata_not_allowed",
            Self::VerifiedCacheAuthoringNotAllowed { .. } => "verified_cache_authoring_not_allowed",
            Self::VerifiedCacheAuthoringRequired { .. } => "verified_cache_authoring_required",
            Self::PackageSideEffectNotAllowed { .. } => "package_side_effect_not_allowed",
            Self::CreatesTheoremDeclaration => "creates_theorem_declaration",
            Self::ReadinessRequired { .. } => "readiness_required",
            Self::TheoremArtifactRequired { .. } => "theorem_artifact_required",
            Self::TheoremArtifactNotAllowed { .. } => "theorem_artifact_not_allowed",
            Self::ArtifactNotReady { .. } => "artifact_not_ready",
            Self::NonL2Artifact { .. } => "non_l2_artifact",
            Self::ParentHoleMustRemainUnresolved { .. } => "parent_hole_must_remain_unresolved",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InventedCandidateTypecheckField {
    RequestHash,
    WitnessHash,
    HandoffHash,
    BlockerHash,
    CandidateId,
    SourceModule,
    TargetProofCorpusModule,
    DeclarationName,
    NormalizedStatement,
    ImportModule,
    StatementHash,
    ExpectedTypeHash,
    EnvironmentHash,
    ImportClosureHash,
    AxiomPolicyHash,
    GeneralizedContextHash,
    VerificationCommandHash,
}

impl InventedCandidateTypecheckField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RequestHash => "request_hash",
            Self::WitnessHash => "witness_hash",
            Self::HandoffHash => "handoff_hash",
            Self::BlockerHash => "blocker_hash",
            Self::CandidateId => "candidate_id",
            Self::SourceModule => "source_module",
            Self::TargetProofCorpusModule => "target_proof_corpus_module",
            Self::DeclarationName => "declaration_name",
            Self::NormalizedStatement => "normalized_statement",
            Self::ImportModule => "import_module",
            Self::StatementHash => "statement_hash",
            Self::ExpectedTypeHash => "expected_type_hash",
            Self::EnvironmentHash => "environment_hash",
            Self::ImportClosureHash => "import_closure_hash",
            Self::AxiomPolicyHash => "axiom_policy_hash",
            Self::GeneralizedContextHash => "generalized_context_hash",
            Self::VerificationCommandHash => "verification_command_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventedCandidateTypecheckError {
    kind: InventedCandidateTypecheckErrorKind,
}

impl InventedCandidateTypecheckError {
    fn new(kind: InventedCandidateTypecheckErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &InventedCandidateTypecheckErrorKind {
        &self.kind
    }
}

impl fmt::Display for InventedCandidateTypecheckError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.as_str())
    }
}

impl std::error::Error for InventedCandidateTypecheckError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InventedCandidateTypecheckErrorKind {
    EmptyIdentifier {
        field: InventedCandidateTypecheckField,
    },
    IdentifierMismatch {
        field: InventedCandidateTypecheckField,
        expected: String,
        actual: String,
    },
    HashMismatch {
        field: InventedCandidateTypecheckField,
        expected: Hash,
        actual: Hash,
    },
    MissingExpectedVerificationCommand {
        kind: TheoremInventionVerificationCommandKind,
    },
    PackageMetadataNotAllowed {
        kind: TheoremInventionVerificationCommandKind,
    },
    VerifiedCacheAuthoringNotAllowed {
        kind: TheoremInventionVerificationCommandKind,
    },
    VerifiedCacheAuthoringRequired {
        kind: TheoremInventionVerificationCommandKind,
    },
    UnprovedStorageKindNotSidecar {
        storage_kind: LocalLemmaUnprovedStorageKind,
    },
    TypecheckWitnessRequiredForHandoff,
    TypecheckWitnessNotAccepted {
        status: InventedCandidateTypecheckStatus,
    },
    HandoffCreatesTheoremDeclaration,
    BlockerCreatesTheoremDeclaration,
}

impl InventedCandidateTypecheckErrorKind {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::IdentifierMismatch { .. } => "identifier_mismatch",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::MissingExpectedVerificationCommand { .. } => {
                "missing_expected_verification_command"
            }
            Self::PackageMetadataNotAllowed { .. } => "package_metadata_not_allowed",
            Self::VerifiedCacheAuthoringNotAllowed { .. } => "verified_cache_authoring_not_allowed",
            Self::VerifiedCacheAuthoringRequired { .. } => "verified_cache_authoring_required",
            Self::UnprovedStorageKindNotSidecar { .. } => "unproved_storage_kind_not_sidecar",
            Self::TypecheckWitnessRequiredForHandoff => "typecheck_witness_required_for_handoff",
            Self::TypecheckWitnessNotAccepted { .. } => "typecheck_witness_not_accepted",
            Self::HandoffCreatesTheoremDeclaration => "handoff_creates_theorem_declaration",
            Self::BlockerCreatesTheoremDeclaration => "blocker_creates_theorem_declaration",
        }
    }
}

impl TheoremInventionArtifact {
    pub fn identity_hash(&self) -> Hash {
        theorem_invention_artifact_identity_hash(self)
    }

    pub fn can_create_proof_corpus_theorem_artifact(&self) -> bool {
        self.artifact_kind.is_checked_artifact()
            && self.theorem_level.is_l2_derived_certificate()
            && validate_theorem_invention_artifact(self).is_ok()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TheoremInventionArtifactField {
    ArtifactIdentityHash,
    GeneralizedContextHash,
    VerificationCommandHash,
    SourceModule,
    TargetProofCorpusModule,
    DeclarationName,
    NormalizedStatement,
    ReplayPath,
    CertificatePath,
    PrerequisiteBlocker,
}

impl TheoremInventionArtifactField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ArtifactIdentityHash => "artifact_identity_hash",
            Self::GeneralizedContextHash => "generalized_context_hash",
            Self::VerificationCommandHash => "verification_command_hash",
            Self::SourceModule => "source_module",
            Self::TargetProofCorpusModule => "target_proof_corpus_module",
            Self::DeclarationName => "declaration_name",
            Self::NormalizedStatement => "normalized_statement",
            Self::ReplayPath => "replay_path",
            Self::CertificatePath => "certificate_path",
            Self::PrerequisiteBlocker => "prerequisite_blocker",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremInventionArtifactError {
    kind: TheoremInventionArtifactErrorKind,
}

impl TheoremInventionArtifactError {
    fn new(kind: TheoremInventionArtifactErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &TheoremInventionArtifactErrorKind {
        &self.kind
    }
}

impl fmt::Display for TheoremInventionArtifactError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.as_str())
    }
}

impl std::error::Error for TheoremInventionArtifactError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoremInventionArtifactErrorKind {
    EmptyIdentifier {
        field: TheoremInventionArtifactField,
    },
    IdentifierMismatch {
        field: TheoremInventionArtifactField,
        expected: String,
        actual: String,
    },
    HashMismatch {
        field: TheoremInventionArtifactField,
        expected: Hash,
        actual: Hash,
    },
    NonL2CandidateNeedsPrerequisiteBlocker {
        theorem_level: TheoremLevel,
    },
    PrerequisiteBlockerMissing {
        promotion_intent: TheoremInventionPromotionIntent,
    },
    SidecarCannotBePromotionReady,
    ProofCorpusArtifactRequiresL2 {
        theorem_level: TheoremLevel,
    },
    MissingExpectedVerificationCommand {
        kind: TheoremInventionVerificationCommandKind,
    },
    PackageMetadataNotAllowed {
        kind: TheoremInventionVerificationCommandKind,
    },
    VerifiedCacheAuthoringNotAllowed {
        kind: TheoremInventionVerificationCommandKind,
    },
    VerifiedCacheAuthoringRequired {
        kind: TheoremInventionVerificationCommandKind,
    },
    MissingReplay,
    MissingCertificate,
    ConclusionAssuming,
    StaleReplay,
    StaleImport,
    WidenedAxiomPolicy,
}

impl TheoremInventionArtifactErrorKind {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::IdentifierMismatch { .. } => "identifier_mismatch",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::NonL2CandidateNeedsPrerequisiteBlocker { .. } => {
                "non_l2_candidate_needs_prerequisite_blocker"
            }
            Self::PrerequisiteBlockerMissing { .. } => "prerequisite_blocker_missing",
            Self::SidecarCannotBePromotionReady => "sidecar_cannot_be_promotion_ready",
            Self::ProofCorpusArtifactRequiresL2 { .. } => "proof_corpus_artifact_requires_l2",
            Self::MissingExpectedVerificationCommand { .. } => {
                "missing_expected_verification_command"
            }
            Self::PackageMetadataNotAllowed { .. } => "package_metadata_not_allowed",
            Self::VerifiedCacheAuthoringNotAllowed { .. } => "verified_cache_authoring_not_allowed",
            Self::VerifiedCacheAuthoringRequired { .. } => "verified_cache_authoring_required",
            Self::MissingReplay => "missing_replay",
            Self::MissingCertificate => "missing_certificate",
            Self::ConclusionAssuming => "conclusion_assuming",
            Self::StaleReplay => "stale_replay",
            Self::StaleImport => "stale_import",
            Self::WidenedAxiomPolicy => "widened_axiom_policy",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaLifecyclePhase {
    Proposed,
    TypeChecked,
    ProofTask,
    Verified,
    Available,
}

impl LocalLemmaLifecyclePhase {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Proposed => "Proposed",
            Self::TypeChecked => "TypeChecked",
            Self::ProofTask => "ProofTask",
            Self::Verified => "Verified",
            Self::Available => "Available",
        }
    }

    pub const fn acceptance_state(self) -> ProofAcceptanceState {
        match self {
            Self::Proposed => ProofAcceptanceState::Proposed,
            Self::TypeChecked => ProofAcceptanceState::TypeChecked,
            Self::ProofTask => ProofAcceptanceState::ProofCandidate,
            Self::Verified | Self::Available => ProofAcceptanceState::CertificateVerified,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaLifecycleIdentityField {
    LemmaId,
    SketchHash,
    SketchNodeId,
    StatementHash,
    EnvironmentHash,
    PolicyHash,
    ExpectedTypeHash,
    TaskIdentityHash,
    ProofArtifactIdentityHash,
    SourceFreeVerifierResultStatus,
    SourceFreeVerifierResultHash,
    AvailableDependencyState,
    AvailableDependencyIdentityHash,
    VerifiedTheoremIdentityHash,
}

impl LocalLemmaLifecycleIdentityField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LemmaId => "lemma_id",
            Self::SketchHash => "sketch_hash",
            Self::SketchNodeId => "sketch_node_id",
            Self::StatementHash => "statement_hash",
            Self::EnvironmentHash => "environment_hash",
            Self::PolicyHash => "policy_hash",
            Self::ExpectedTypeHash => "expected_type_hash",
            Self::TaskIdentityHash => "task_identity_hash",
            Self::ProofArtifactIdentityHash => "proof_artifact_identity_hash",
            Self::SourceFreeVerifierResultStatus => "source_free_verifier_result_status",
            Self::SourceFreeVerifierResultHash => "source_free_verifier_result_hash",
            Self::AvailableDependencyState => "available_dependency_state",
            Self::AvailableDependencyIdentityHash => "available_dependency_identity_hash",
            Self::VerifiedTheoremIdentityHash => "verified_theorem_identity_hash",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaProposed {
    pub lemma_id: String,
    pub sketch_hash: Hash,
    pub sketch_node_id: String,
    pub statement_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaTypeChecked {
    pub lemma_id: String,
    pub sketch_hash: Hash,
    pub sketch_node_id: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaProofTask {
    pub lemma_id: String,
    pub sketch_hash: Hash,
    pub sketch_node_id: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub task_identity: LocalLemmaProofTaskIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaVerified {
    pub lemma_id: String,
    pub sketch_hash: Hash,
    pub sketch_node_id: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub task_identity: LocalLemmaProofTaskIdentity,
    pub proof_artifact_identity: VerifiedArtifactIdentity,
    pub proof_artifact_identity_hash: Hash,
    pub source_free_verifier_result: LocalLemmaSourceFreeVerifierResult,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaAvailable {
    pub lemma_id: String,
    pub sketch_hash: Hash,
    pub sketch_node_id: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub task_identity: LocalLemmaProofTaskIdentity,
    pub verified_theorem_identity: VerifiedArtifactIdentity,
    pub verified_theorem_identity_hash: Hash,
    pub available_dependency_identity: LocalLemmaAvailableDependencyIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaProofTaskIdentity {
    pub task_identity_hash: Hash,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub available_dependency_identities: Vec<LocalLemmaAvailableDependencyIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaSourceFreeVerifierResult {
    pub result_hash: Hash,
    pub status: ProofAcceptanceState,
    pub task_identity_hash: Hash,
    pub proof_artifact_identity_hash: Hash,
    pub statement_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaAvailableDependencyIdentity {
    pub dependency_identity_hash: Hash,
    pub verified_artifact_identity_hash: Hash,
    pub state: ProofAcceptanceState,
    pub statement_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaProofTaskStatus {
    Pending,
    Running,
    Failed,
    Cancelled,
    Blocked,
    SourceFreeVerified,
}

impl LocalLemmaProofTaskStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Running => "running",
            Self::Failed => "failed",
            Self::Cancelled => "cancelled",
            Self::Blocked => "blocked",
            Self::SourceFreeVerified => "source_free_verified",
        }
    }

    pub const fn creates_verified_artifact(self) -> bool {
        matches!(self, Self::SourceFreeVerified)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaParentHoleDisposition {
    Unresolved,
    Available,
}

impl LocalLemmaParentHoleDisposition {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unresolved => "unresolved",
            Self::Available => "available",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaUnprovedStorageKind {
    TaskSidecar,
    SketchSidecar,
    ProofCorpusTheoremDeclaration,
    L1EvidencePackage,
    VerifiedArtifactIdentity,
}

impl LocalLemmaUnprovedStorageKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TaskSidecar => "task_sidecar",
            Self::SketchSidecar => "sketch_sidecar",
            Self::ProofCorpusTheoremDeclaration => "proof_corpus_theorem_declaration",
            Self::L1EvidencePackage => "l1_evidence_package",
            Self::VerifiedArtifactIdentity => "verified_artifact_identity",
        }
    }

    pub const fn is_unproved_sidecar(self) -> bool {
        matches!(self, Self::TaskSidecar | Self::SketchSidecar)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaVerificationCommandKind {
    BuildModule,
    VerifyModuleSourceFree,
}

impl LocalLemmaVerificationCommandKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BuildModule => "build_module",
            Self::VerifyModuleSourceFree => "verify_module_source_free",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaGeneralizedContextBinder {
    pub binder_id: String,
    pub type_hash: Hash,
    pub dependency_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaGeneralizedContext {
    pub context_hash: Hash,
    pub binders: Vec<LocalLemmaGeneralizedContextBinder>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaExpectedVerificationCommand {
    pub command_hash: Hash,
    pub kind: LocalLemmaVerificationCommandKind,
    pub module: String,
    pub verified_cache_authoring: bool,
    pub package_metadata: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaProofTaskHandoff {
    pub handoff_hash: Hash,
    pub lemma_id: String,
    pub sketch_hash: Hash,
    pub sketch_node_id: String,
    pub module: String,
    pub declaration_name: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub axiom_policy_hash: Hash,
    pub generalized_context: LocalLemmaGeneralizedContext,
    pub dependency_identities: Vec<LocalLemmaAvailableDependencyIdentity>,
    pub target_proof_corpus_module: String,
    pub expected_verification_commands: Vec<LocalLemmaExpectedVerificationCommand>,
    pub unproved_storage_kind: LocalLemmaUnprovedStorageKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaAxiomSummaryEntry {
    pub axiom_name: String,
    pub axiom_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaVerifiedArtifactRecord {
    pub artifact_record_hash: Hash,
    pub module: String,
    pub declaration_name: String,
    pub statement_hash: Hash,
    pub task_identity_hash: Hash,
    pub certificate_hash: Hash,
    pub export_hash: Hash,
    pub declaration_interface_hash: Hash,
    pub source_hash: Hash,
    pub replay_path: String,
    pub replay_hash: Hash,
    pub axiom_summary: Vec<LocalLemmaAxiomSummaryEntry>,
    pub axiom_summary_hash: Hash,
    pub source_free_verifier_result: LocalLemmaSourceFreeVerifierResult,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaProofTaskOutcome {
    pub handoff_hash: Hash,
    pub status: LocalLemmaProofTaskStatus,
    pub parent_hole: LocalLemmaParentHoleDisposition,
    pub verified_artifact: Option<LocalLemmaVerifiedArtifactRecord>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLemmaProofTaskHandoffField {
    HandoffHash,
    LemmaId,
    SketchHash,
    SketchNodeId,
    Module,
    DeclarationName,
    StatementHash,
    ExpectedTypeHash,
    EnvironmentHash,
    AxiomPolicyHash,
    GeneralizedContextHash,
    DependencyIdentityHash,
    TargetProofCorpusModule,
    VerificationCommandHash,
    ArtifactRecordHash,
    CertificateHash,
    ExportHash,
    DeclarationInterfaceHash,
    SourceHash,
    ReplayPath,
    ReplayHash,
    AxiomSummaryHash,
    SourceFreeVerifierResultHash,
    ParentHoleDisposition,
}

impl LocalLemmaProofTaskHandoffField {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::HandoffHash => "handoff_hash",
            Self::LemmaId => "lemma_id",
            Self::SketchHash => "sketch_hash",
            Self::SketchNodeId => "sketch_node_id",
            Self::Module => "module",
            Self::DeclarationName => "declaration_name",
            Self::StatementHash => "statement_hash",
            Self::ExpectedTypeHash => "expected_type_hash",
            Self::EnvironmentHash => "environment_hash",
            Self::AxiomPolicyHash => "axiom_policy_hash",
            Self::GeneralizedContextHash => "generalized_context_hash",
            Self::DependencyIdentityHash => "dependency_identity_hash",
            Self::TargetProofCorpusModule => "target_proof_corpus_module",
            Self::VerificationCommandHash => "verification_command_hash",
            Self::ArtifactRecordHash => "artifact_record_hash",
            Self::CertificateHash => "certificate_hash",
            Self::ExportHash => "export_hash",
            Self::DeclarationInterfaceHash => "declaration_interface_hash",
            Self::SourceHash => "source_hash",
            Self::ReplayPath => "replay_path",
            Self::ReplayHash => "replay_hash",
            Self::AxiomSummaryHash => "axiom_summary_hash",
            Self::SourceFreeVerifierResultHash => "source_free_verifier_result_hash",
            Self::ParentHoleDisposition => "parent_hole_disposition",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaProofTaskHandoffError {
    kind: LocalLemmaProofTaskHandoffErrorKind,
}

impl LocalLemmaProofTaskHandoffError {
    fn new(kind: LocalLemmaProofTaskHandoffErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &LocalLemmaProofTaskHandoffErrorKind {
        &self.kind
    }
}

impl fmt::Display for LocalLemmaProofTaskHandoffError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.as_str())
    }
}

impl std::error::Error for LocalLemmaProofTaskHandoffError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalLemmaProofTaskHandoffErrorKind {
    EmptyIdentifier {
        field: LocalLemmaProofTaskHandoffField,
    },
    IdentifierMismatch {
        field: LocalLemmaProofTaskHandoffField,
        expected: String,
        actual: String,
    },
    HashMismatch {
        field: LocalLemmaProofTaskHandoffField,
        expected: Hash,
        actual: Hash,
    },
    UnprovedStorageKindNotSidecar {
        storage_kind: LocalLemmaUnprovedStorageKind,
    },
    MissingExpectedVerificationCommand {
        kind: LocalLemmaVerificationCommandKind,
    },
    PackageMetadataNotAllowed {
        kind: LocalLemmaVerificationCommandKind,
    },
    VerifiedCacheAuthoringNotAllowed {
        kind: LocalLemmaVerificationCommandKind,
    },
    VerifiedCacheAuthoringRequired {
        kind: LocalLemmaVerificationCommandKind,
    },
    DependencyNotSharable {
        error_kind: &'static str,
    },
    ParentHoleMustRemainUnresolved {
        status: LocalLemmaProofTaskStatus,
        parent_hole: LocalLemmaParentHoleDisposition,
    },
    TheoremArtifactNotAllowed {
        status: LocalLemmaProofTaskStatus,
    },
    MissingVerifiedArtifact {
        status: LocalLemmaProofTaskStatus,
    },
    VerifiedArtifactIdentityInvalid {
        error_kind: &'static str,
    },
    Lifecycle {
        error_kind: &'static str,
    },
}

impl LocalLemmaProofTaskHandoffErrorKind {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::IdentifierMismatch { .. } => "identifier_mismatch",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::UnprovedStorageKindNotSidecar { .. } => "unproved_storage_kind_not_sidecar",
            Self::MissingExpectedVerificationCommand { .. } => {
                "missing_expected_verification_command"
            }
            Self::PackageMetadataNotAllowed { .. } => "package_metadata_not_allowed",
            Self::VerifiedCacheAuthoringNotAllowed { .. } => "verified_cache_authoring_not_allowed",
            Self::VerifiedCacheAuthoringRequired { .. } => "verified_cache_authoring_required",
            Self::DependencyNotSharable { .. } => "dependency_not_sharable",
            Self::ParentHoleMustRemainUnresolved { .. } => "parent_hole_must_remain_unresolved",
            Self::TheoremArtifactNotAllowed { .. } => "theorem_artifact_not_allowed",
            Self::MissingVerifiedArtifact { .. } => "missing_verified_artifact",
            Self::VerifiedArtifactIdentityInvalid { .. } => "verified_artifact_identity_invalid",
            Self::Lifecycle { .. } => "local_lemma_lifecycle_error",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalLemmaLifecycleState {
    Proposed(LocalLemmaProposed),
    TypeChecked(LocalLemmaTypeChecked),
    ProofTask(LocalLemmaProofTask),
    Verified(LocalLemmaVerified),
    Available(LocalLemmaAvailable),
}

impl LocalLemmaLifecycleState {
    pub const fn phase(&self) -> LocalLemmaLifecyclePhase {
        match self {
            Self::Proposed(_) => LocalLemmaLifecyclePhase::Proposed,
            Self::TypeChecked(_) => LocalLemmaLifecyclePhase::TypeChecked,
            Self::ProofTask(_) => LocalLemmaLifecyclePhase::ProofTask,
            Self::Verified(_) => LocalLemmaLifecyclePhase::Verified,
            Self::Available(_) => LocalLemmaLifecyclePhase::Available,
        }
    }

    pub fn lemma_id(&self) -> &str {
        match self {
            Self::Proposed(state) => &state.lemma_id,
            Self::TypeChecked(state) => &state.lemma_id,
            Self::ProofTask(state) => &state.lemma_id,
            Self::Verified(state) => &state.lemma_id,
            Self::Available(state) => &state.lemma_id,
        }
    }

    pub fn sketch_node_id(&self) -> &str {
        match self {
            Self::Proposed(state) => &state.sketch_node_id,
            Self::TypeChecked(state) => &state.sketch_node_id,
            Self::ProofTask(state) => &state.sketch_node_id,
            Self::Verified(state) => &state.sketch_node_id,
            Self::Available(state) => &state.sketch_node_id,
        }
    }

    pub const fn sketch_hash(&self) -> Hash {
        match self {
            Self::Proposed(state) => state.sketch_hash,
            Self::TypeChecked(state) => state.sketch_hash,
            Self::ProofTask(state) => state.sketch_hash,
            Self::Verified(state) => state.sketch_hash,
            Self::Available(state) => state.sketch_hash,
        }
    }

    pub const fn statement_hash(&self) -> Hash {
        match self {
            Self::Proposed(state) => state.statement_hash,
            Self::TypeChecked(state) => state.statement_hash,
            Self::ProofTask(state) => state.statement_hash,
            Self::Verified(state) => state.statement_hash,
            Self::Available(state) => state.statement_hash,
        }
    }

    pub const fn environment_hash(&self) -> Hash {
        match self {
            Self::Proposed(state) => state.environment_hash,
            Self::TypeChecked(state) => state.environment_hash,
            Self::ProofTask(state) => state.environment_hash,
            Self::Verified(state) => state.environment_hash,
            Self::Available(state) => state.environment_hash,
        }
    }

    pub const fn policy_hash(&self) -> Hash {
        match self {
            Self::Proposed(state) => state.policy_hash,
            Self::TypeChecked(state) => state.policy_hash,
            Self::ProofTask(state) => state.policy_hash,
            Self::Verified(state) => state.policy_hash,
            Self::Available(state) => state.policy_hash,
        }
    }

    pub const fn expected_type_hash(&self) -> Option<Hash> {
        match self {
            Self::Proposed(_) => None,
            Self::TypeChecked(state) => Some(state.expected_type_hash),
            Self::ProofTask(state) => Some(state.expected_type_hash),
            Self::Verified(state) => Some(state.expected_type_hash),
            Self::Available(state) => Some(state.expected_type_hash),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalLemmaLifecycleError {
    kind: LocalLemmaLifecycleErrorKind,
}

impl LocalLemmaLifecycleError {
    fn new(kind: LocalLemmaLifecycleErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &LocalLemmaLifecycleErrorKind {
        &self.kind
    }
}

impl fmt::Display for LocalLemmaLifecycleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.as_str())
    }
}

impl std::error::Error for LocalLemmaLifecycleError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalLemmaLifecycleErrorKind {
    InvalidTransition {
        from: LocalLemmaLifecyclePhase,
        to: LocalLemmaLifecyclePhase,
    },
    IdentifierMismatch {
        field: LocalLemmaLifecycleIdentityField,
        expected: String,
        actual: String,
    },
    HashMismatch {
        field: LocalLemmaLifecycleIdentityField,
        expected: Hash,
        actual: Hash,
    },
    StateMismatch {
        field: LocalLemmaLifecycleIdentityField,
        expected: ProofAcceptanceState,
        actual: ProofAcceptanceState,
    },
    SourceFreeVerifierResultNotVerified {
        status: ProofAcceptanceState,
    },
    VerifiedArtifactIdentityInvalid {
        error_kind: &'static str,
    },
    DependencyNotSharable {
        surface: VerifiedOnlySharingSurface,
        error_kind: &'static str,
    },
}

impl LocalLemmaLifecycleErrorKind {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::InvalidTransition { .. } => "invalid_transition",
            Self::IdentifierMismatch { .. } => "identifier_mismatch",
            Self::HashMismatch { .. } => "hash_mismatch",
            Self::StateMismatch { .. } => "state_mismatch",
            Self::SourceFreeVerifierResultNotVerified { .. } => {
                "source_free_verifier_result_not_verified"
            }
            Self::VerifiedArtifactIdentityInvalid { .. } => "verified_artifact_identity_invalid",
            Self::DependencyNotSharable { .. } => "dependency_not_sharable",
        }
    }
}

pub fn local_lemma_proof_task_identity_hash(identity: &LocalLemmaProofTaskIdentity) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_PROOF_TASK_IDENTITY_PROFILE);
    encode_hash(&mut out, &identity.statement_hash);
    encode_hash(&mut out, &identity.expected_type_hash);
    encode_hash(&mut out, &identity.environment_hash);
    encode_hash(&mut out, &identity.policy_hash);
    let mut dependencies = identity.available_dependency_identities.clone();
    dependencies.sort_by_key(|dependency| dependency.dependency_identity_hash);
    encode_uvar(&mut out, dependencies.len() as u64);
    for dependency in dependencies {
        encode_hash(&mut out, &dependency.dependency_identity_hash);
    }
    hash_with_domain("npa.local-lemma.proof-task-identity.hash.v1", &out)
}

pub fn local_lemma_source_free_verifier_result_hash(
    result: &LocalLemmaSourceFreeVerifierResult,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_SOURCE_FREE_VERIFIER_RESULT_PROFILE);
    encode_string(&mut out, result.status.as_str());
    encode_hash(&mut out, &result.task_identity_hash);
    encode_hash(&mut out, &result.proof_artifact_identity_hash);
    encode_hash(&mut out, &result.statement_hash);
    encode_hash(&mut out, &result.environment_hash);
    encode_hash(&mut out, &result.policy_hash);
    hash_with_domain("npa.local-lemma.source-free-verifier-result.hash.v1", &out)
}

pub fn local_lemma_available_dependency_identity_hash(
    identity: &LocalLemmaAvailableDependencyIdentity,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_AVAILABLE_DEPENDENCY_IDENTITY_PROFILE);
    encode_hash(&mut out, &identity.verified_artifact_identity_hash);
    encode_string(&mut out, identity.state.as_str());
    encode_hash(&mut out, &identity.statement_hash);
    encode_hash(&mut out, &identity.environment_hash);
    encode_hash(&mut out, &identity.policy_hash);
    hash_with_domain(
        "npa.local-lemma.available-dependency-identity.hash.v1",
        &out,
    )
}

pub fn local_lemma_generalized_context_hash(context: &LocalLemmaGeneralizedContext) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_GENERALIZED_CONTEXT_PROFILE);
    encode_uvar(&mut out, context.binders.len() as u64);
    for binder in &context.binders {
        encode_string(&mut out, &binder.binder_id);
        encode_hash(&mut out, &binder.type_hash);
        let mut dependencies = binder.dependency_hashes.clone();
        dependencies.sort();
        encode_uvar(&mut out, dependencies.len() as u64);
        for dependency_hash in dependencies {
            encode_hash(&mut out, &dependency_hash);
        }
    }
    hash_with_domain("npa.local-lemma.generalized-context.hash.v1", &out)
}

pub fn local_lemma_expected_verification_command_hash(
    command: &LocalLemmaExpectedVerificationCommand,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_VERIFICATION_COMMAND_PROFILE);
    encode_string(&mut out, command.kind.as_str());
    encode_string(&mut out, &command.module);
    encode_bool(&mut out, command.verified_cache_authoring);
    encode_bool(&mut out, command.package_metadata);
    hash_with_domain("npa.local-lemma.verification-command.hash.v1", &out)
}

pub fn local_lemma_proof_task_handoff_hash(handoff: &LocalLemmaProofTaskHandoff) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_PROOF_TASK_HANDOFF_PROFILE);
    encode_string(&mut out, &handoff.lemma_id);
    encode_hash(&mut out, &handoff.sketch_hash);
    encode_string(&mut out, &handoff.sketch_node_id);
    encode_string(&mut out, &handoff.module);
    encode_string(&mut out, &handoff.declaration_name);
    encode_hash(&mut out, &handoff.statement_hash);
    encode_hash(&mut out, &handoff.expected_type_hash);
    encode_hash(&mut out, &handoff.environment_hash);
    encode_hash(&mut out, &handoff.axiom_policy_hash);
    encode_hash(&mut out, &handoff.generalized_context.context_hash);
    let mut dependencies = handoff.dependency_identities.clone();
    dependencies.sort_by_key(|dependency| dependency.dependency_identity_hash);
    encode_uvar(&mut out, dependencies.len() as u64);
    for dependency in dependencies {
        encode_hash(&mut out, &dependency.dependency_identity_hash);
    }
    encode_string(&mut out, &handoff.target_proof_corpus_module);
    encode_uvar(
        &mut out,
        handoff.expected_verification_commands.len() as u64,
    );
    for command in &handoff.expected_verification_commands {
        encode_hash(&mut out, &command.command_hash);
    }
    encode_string(&mut out, handoff.unproved_storage_kind.as_str());
    hash_with_domain("npa.local-lemma.proof-task-handoff.hash.v1", &out)
}

pub fn local_lemma_axiom_summary_hash(entries: &[LocalLemmaAxiomSummaryEntry]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_AXIOM_SUMMARY_PROFILE);
    let mut entries = entries.to_vec();
    entries.sort_by(|left, right| {
        left.axiom_name
            .cmp(&right.axiom_name)
            .then_with(|| left.axiom_hash.cmp(&right.axiom_hash))
    });
    encode_uvar(&mut out, entries.len() as u64);
    for entry in entries {
        encode_string(&mut out, &entry.axiom_name);
        encode_hash(&mut out, &entry.axiom_hash);
    }
    hash_with_domain("npa.local-lemma.axiom-summary.hash.v1", &out)
}

pub fn local_lemma_verified_artifact_record_hash(
    artifact: &LocalLemmaVerifiedArtifactRecord,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, LOCAL_LEMMA_VERIFIED_ARTIFACT_RECORD_PROFILE);
    encode_string(&mut out, &artifact.module);
    encode_string(&mut out, &artifact.declaration_name);
    encode_hash(&mut out, &artifact.statement_hash);
    encode_hash(&mut out, &artifact.task_identity_hash);
    encode_hash(&mut out, &artifact.certificate_hash);
    encode_hash(&mut out, &artifact.export_hash);
    encode_hash(&mut out, &artifact.declaration_interface_hash);
    encode_hash(&mut out, &artifact.source_hash);
    encode_string(&mut out, &artifact.replay_path);
    encode_hash(&mut out, &artifact.replay_hash);
    encode_hash(&mut out, &artifact.axiom_summary_hash);
    encode_hash(&mut out, &artifact.source_free_verifier_result.result_hash);
    hash_with_domain("npa.local-lemma.verified-artifact-record.hash.v1", &out)
}

pub fn theorem_invention_generalized_context_hash(
    context: &TheoremInventionGeneralizedContext,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, THEOREM_INVENTION_GENERALIZED_CONTEXT_PROFILE);
    encode_uvar(&mut out, context.binders.len() as u64);
    for binder in &context.binders {
        encode_string(&mut out, &binder.binder_id);
        encode_hash(&mut out, &binder.type_hash);
        let mut dependencies = binder.dependency_hashes.clone();
        dependencies.sort();
        encode_uvar(&mut out, dependencies.len() as u64);
        for dependency_hash in dependencies {
            encode_hash(&mut out, &dependency_hash);
        }
    }
    hash_with_domain("npa.theorem-invention.generalized-context.hash.v1", &out)
}

pub fn theorem_invention_verification_command_hash(
    command: &TheoremInventionVerificationCommand,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, THEOREM_INVENTION_VERIFICATION_COMMAND_PROFILE);
    encode_string(&mut out, command.kind.as_str());
    encode_string(&mut out, &command.module);
    encode_bool(&mut out, command.verified_cache_authoring);
    encode_bool(&mut out, command.package_metadata);
    hash_with_domain("npa.theorem-invention.verification-command.hash.v1", &out)
}

pub fn theorem_invention_artifact_identity_hash(artifact: &TheoremInventionArtifact) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, THEOREM_INVENTION_ARTIFACT_PROFILE);
    encode_string(&mut out, artifact.artifact_kind.as_str());
    encode_string(&mut out, artifact.theorem_level.as_str());
    encode_hash(&mut out, &artifact.statement_hash);
    encode_string(&mut out, &artifact.normalized_statement);
    encode_hash(&mut out, &artifact.generalized_context.context_hash);
    encode_string(&mut out, &artifact.source_module);
    encode_string(&mut out, &artifact.target_proof_corpus_module);
    encode_string(&mut out, &artifact.declaration_name);
    let mut dependencies = artifact.dependency_identities.clone();
    dependencies.sort();
    encode_uvar(&mut out, dependencies.len() as u64);
    for dependency_hash in dependencies {
        encode_hash(&mut out, &dependency_hash);
    }
    encode_uvar(&mut out, artifact.import_closure.len() as u64);
    for import in &artifact.import_closure {
        encode_string(&mut out, import);
    }
    encode_hash(&mut out, &artifact.axiom_policy_hash);
    encode_option_string(&mut out, artifact.replay_path.as_deref());
    encode_option_hash(&mut out, artifact.replay_hash.as_ref());
    encode_option_string(&mut out, artifact.certificate_path.as_deref());
    encode_option_hash(&mut out, artifact.certificate_hash.as_ref());
    encode_uvar(&mut out, artifact.verification_commands.len() as u64);
    for command in &artifact.verification_commands {
        encode_hash(&mut out, &command.command_hash);
    }
    encode_string(&mut out, artifact.promotion_intent.as_str());
    encode_option_string(&mut out, artifact.prerequisite_blocker.as_deref());
    encode_bool(&mut out, artifact.conclusion_assuming);
    encode_bool(&mut out, artifact.replay_is_stale);
    encode_bool(&mut out, artifact.import_closure_is_stale);
    encode_bool(&mut out, artifact.axiom_policy_widened);
    hash_with_domain("npa.theorem-invention.artifact-identity.hash.v1", &out)
}

pub fn invented_candidate_import_closure_hash(imports: &[InventedCandidateImportIdentity]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_CANDIDATE_IMPORT_CLOSURE_PROFILE);
    let mut imports = imports.to_vec();
    imports.sort();
    encode_uvar(&mut out, imports.len() as u64);
    for import in imports {
        encode_string(&mut out, &import.module);
        encode_hash(&mut out, &import.import_hash);
    }
    hash_with_domain(
        "npa.theorem-invention.typecheck.import-closure.hash.v1",
        &out,
    )
}

pub fn invented_candidate_typecheck_witness_hash(
    witness: &InventedCandidateTypecheckWitness,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_CANDIDATE_TYPECHECK_WITNESS_PROFILE);
    encode_string(&mut out, witness.status.as_str());
    encode_hash(&mut out, &witness.statement_hash);
    encode_hash(&mut out, &witness.expected_type_hash);
    encode_hash(&mut out, &witness.environment_hash);
    encode_hash(&mut out, &witness.import_closure_hash);
    encode_hash(&mut out, &witness.axiom_policy_hash);
    encode_string(&mut out, &witness.target_proof_corpus_module);
    encode_option_hash(&mut out, witness.diagnostic_hash.as_ref());
    hash_with_domain("npa.theorem-invention.typecheck.witness.hash.v1", &out)
}

pub fn invented_candidate_typecheck_request_hash(
    request: &InventedCandidateTypecheckRequest,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_CANDIDATE_TYPECHECK_REQUEST_PROFILE);
    encode_string(&mut out, &request.candidate_id);
    encode_string(&mut out, &request.source_module);
    encode_string(&mut out, &request.target_proof_corpus_module);
    encode_string(&mut out, &request.declaration_name);
    encode_string(&mut out, &request.normalized_statement);
    encode_hash(&mut out, &request.statement_hash);
    encode_hash(&mut out, &request.generalized_context.context_hash);
    encode_hash(&mut out, &request.environment_hash);
    encode_hash(
        &mut out,
        &invented_candidate_import_closure_hash(&request.import_identities),
    );
    let mut required_import_modules = request.required_import_modules.clone();
    required_import_modules.sort();
    required_import_modules.dedup();
    encode_uvar(&mut out, required_import_modules.len() as u64);
    for module in required_import_modules {
        encode_string(&mut out, &module);
    }
    encode_hash(&mut out, &request.axiom_policy_hash);
    encode_hash(&mut out, &request.expected_axiom_policy_hash);
    match request.typecheck_witness.as_ref() {
        Some(witness) => {
            out.push(0x01);
            encode_hash(&mut out, &witness.witness_hash);
        }
        None => out.push(0x00),
    }
    encode_bool(&mut out, request.conclusion_assuming);
    encode_bool(&mut out, request.axiom_policy_widened);
    hash_with_domain("npa.theorem-invention.typecheck.request.hash.v1", &out)
}

pub fn invented_candidate_typecheck_handoff_hash(
    handoff: &InventedCandidateTypecheckHandoff,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_CANDIDATE_TYPECHECK_HANDOFF_PROFILE);
    encode_hash(&mut out, &handoff.request_hash);
    encode_string(&mut out, &handoff.candidate_id);
    encode_string(&mut out, &handoff.source_module);
    encode_string(&mut out, &handoff.target_proof_corpus_module);
    encode_string(&mut out, &handoff.declaration_name);
    encode_hash(&mut out, &handoff.statement_hash);
    encode_hash(&mut out, &handoff.expected_type_hash);
    encode_hash(&mut out, &handoff.environment_hash);
    encode_hash(
        &mut out,
        &invented_candidate_import_closure_hash(&handoff.import_identities),
    );
    encode_hash(&mut out, &handoff.axiom_policy_hash);
    encode_hash(&mut out, &handoff.generalized_context.context_hash);
    encode_uvar(&mut out, handoff.expected_authoring_commands.len() as u64);
    for command in &handoff.expected_authoring_commands {
        encode_hash(&mut out, &command.command_hash);
    }
    encode_string(&mut out, handoff.unproved_storage_kind.as_str());
    encode_bool(&mut out, handoff.creates_theorem_declaration);
    hash_with_domain("npa.theorem-invention.typecheck.handoff.hash.v1", &out)
}

pub fn invented_candidate_typecheck_blocker_hash(
    blocker: &InventedCandidateTypecheckBlocker,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_CANDIDATE_TYPECHECK_BLOCKER_PROFILE);
    encode_hash(&mut out, &blocker.request_hash);
    encode_string(&mut out, &blocker.candidate_id);
    encode_string(&mut out, &blocker.target_proof_corpus_module);
    encode_string(&mut out, &blocker.declaration_name);
    encode_hash(&mut out, &blocker.statement_hash);
    encode_string(&mut out, blocker.reason.as_str());
    encode_option_hash(&mut out, blocker.evidence_hash.as_ref());
    encode_string(&mut out, blocker.unproved_storage_kind.as_str());
    encode_bool(&mut out, blocker.creates_theorem_declaration);
    hash_with_domain("npa.theorem-invention.typecheck.blocker.hash.v1", &out)
}

pub fn invented_candidate_expected_authoring_commands(
    target_proof_corpus_module: &str,
) -> Vec<TheoremInventionVerificationCommand> {
    let mut build = TheoremInventionVerificationCommand {
        command_hash: [0; 32],
        kind: TheoremInventionVerificationCommandKind::BuildModule,
        module: target_proof_corpus_module.to_owned(),
        verified_cache_authoring: false,
        package_metadata: false,
    };
    build.command_hash = theorem_invention_verification_command_hash(&build);

    let mut verify = TheoremInventionVerificationCommand {
        command_hash: [0; 32],
        kind: TheoremInventionVerificationCommandKind::VerifyModuleSourceFree,
        module: target_proof_corpus_module.to_owned(),
        verified_cache_authoring: true,
        package_metadata: false,
    };
    verify.command_hash = theorem_invention_verification_command_hash(&verify);
    vec![build, verify]
}

pub fn invented_candidate_typecheck(
    request: &InventedCandidateTypecheckRequest,
) -> Result<InventedCandidateTypecheckOutcome, InventedCandidateTypecheckError> {
    validate_invented_candidate_typecheck_request_shape(request)?;

    if request.conclusion_assuming {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::ConclusionAssumingBoundary,
                request
                    .typecheck_witness
                    .as_ref()
                    .map(|witness| witness.witness_hash),
            ),
        ));
    }
    if request.axiom_policy_widened
        || request.axiom_policy_hash != request.expected_axiom_policy_hash
    {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::WidenedAxiomPolicy,
                Some(request.axiom_policy_hash),
            ),
        ));
    }
    if let Some(missing_module) = invented_candidate_missing_required_import(request) {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::MissingImport,
                Some(hash_with_domain(
                    "npa.theorem-invention.typecheck.missing-import.hash.v1",
                    missing_module.as_bytes(),
                )),
            ),
        ));
    }

    let Some(witness) = request.typecheck_witness.as_ref() else {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::IllTypedStatement,
                None,
            ),
        ));
    };
    if witness.status != InventedCandidateTypecheckStatus::TypeChecked
        || witness.statement_hash != request.statement_hash
    {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::IllTypedStatement,
                witness.diagnostic_hash.or(Some(witness.witness_hash)),
            ),
        ));
    }
    if witness.environment_hash != request.environment_hash
        || witness.target_proof_corpus_module != request.target_proof_corpus_module
    {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::StaleEnvironment,
                Some(witness.environment_hash),
            ),
        ));
    }
    if witness.import_closure_hash
        != invented_candidate_import_closure_hash(&request.import_identities)
    {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::MissingImport,
                Some(witness.import_closure_hash),
            ),
        ));
    }
    if witness.axiom_policy_hash != request.axiom_policy_hash {
        return Ok(InventedCandidateTypecheckOutcome::Blocked(
            invented_candidate_typecheck_blocker(
                request,
                InventedCandidateTypecheckBlockerReason::WidenedAxiomPolicy,
                Some(witness.axiom_policy_hash),
            ),
        ));
    }

    let mut handoff = InventedCandidateTypecheckHandoff {
        handoff_hash: [0; 32],
        request_hash: request.request_hash,
        candidate_id: request.candidate_id.clone(),
        source_module: request.source_module.clone(),
        target_proof_corpus_module: request.target_proof_corpus_module.clone(),
        declaration_name: request.declaration_name.clone(),
        statement_hash: request.statement_hash,
        expected_type_hash: witness.expected_type_hash,
        environment_hash: request.environment_hash,
        import_identities: request.import_identities.clone(),
        axiom_policy_hash: request.axiom_policy_hash,
        generalized_context: request.generalized_context.clone(),
        expected_authoring_commands: invented_candidate_expected_authoring_commands(
            &request.target_proof_corpus_module,
        ),
        unproved_storage_kind: LocalLemmaUnprovedStorageKind::TaskSidecar,
        creates_theorem_declaration: false,
    };
    handoff.handoff_hash = invented_candidate_typecheck_handoff_hash(&handoff);
    validate_invented_candidate_typecheck_handoff(request, &handoff)?;
    Ok(InventedCandidateTypecheckOutcome::Accepted(handoff))
}

pub fn validate_invented_candidate_typecheck_handoff(
    request: &InventedCandidateTypecheckRequest,
    handoff: &InventedCandidateTypecheckHandoff,
) -> Result<(), InventedCandidateTypecheckError> {
    validate_invented_candidate_typecheck_request_shape(request)?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::CandidateId,
        &handoff.candidate_id,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::SourceModule,
        &handoff.source_module,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::TargetProofCorpusModule,
        &handoff.target_proof_corpus_module,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::DeclarationName,
        &handoff.declaration_name,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::HandoffHash,
        invented_candidate_typecheck_handoff_hash(handoff),
        handoff.handoff_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::RequestHash,
        request.request_hash,
        handoff.request_hash,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::CandidateId,
        &request.candidate_id,
        &handoff.candidate_id,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::SourceModule,
        &request.source_module,
        &handoff.source_module,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::TargetProofCorpusModule,
        &request.target_proof_corpus_module,
        &handoff.target_proof_corpus_module,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::DeclarationName,
        &request.declaration_name,
        &handoff.declaration_name,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::StatementHash,
        request.statement_hash,
        handoff.statement_hash,
    )?;
    let Some(witness) = request.typecheck_witness.as_ref() else {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::TypecheckWitnessRequiredForHandoff,
        ));
    };
    if witness.status != InventedCandidateTypecheckStatus::TypeChecked {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::TypecheckWitnessNotAccepted {
                status: witness.status,
            },
        ));
    }
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::StatementHash,
        request.statement_hash,
        witness.statement_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::ExpectedTypeHash,
        witness.expected_type_hash,
        handoff.expected_type_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::EnvironmentHash,
        request.environment_hash,
        witness.environment_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::ImportClosureHash,
        invented_candidate_import_closure_hash(&request.import_identities),
        witness.import_closure_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::AxiomPolicyHash,
        request.axiom_policy_hash,
        witness.axiom_policy_hash,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::TargetProofCorpusModule,
        &request.target_proof_corpus_module,
        &witness.target_proof_corpus_module,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::EnvironmentHash,
        request.environment_hash,
        handoff.environment_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::ImportClosureHash,
        invented_candidate_import_closure_hash(&request.import_identities),
        invented_candidate_import_closure_hash(&handoff.import_identities),
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::AxiomPolicyHash,
        request.axiom_policy_hash,
        handoff.axiom_policy_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::GeneralizedContextHash,
        request.generalized_context.context_hash,
        handoff.generalized_context.context_hash,
    )?;
    validate_invented_candidate_authoring_commands(
        &handoff.expected_authoring_commands,
        &handoff.target_proof_corpus_module,
    )?;
    if !handoff.unproved_storage_kind.is_unproved_sidecar() {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::UnprovedStorageKindNotSidecar {
                storage_kind: handoff.unproved_storage_kind,
            },
        ));
    }
    if handoff.creates_theorem_declaration {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::HandoffCreatesTheoremDeclaration,
        ));
    }
    Ok(())
}

pub fn validate_invented_candidate_typecheck_blocker(
    request: &InventedCandidateTypecheckRequest,
    blocker: &InventedCandidateTypecheckBlocker,
) -> Result<(), InventedCandidateTypecheckError> {
    validate_invented_candidate_typecheck_request_shape(request)?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::CandidateId,
        &blocker.candidate_id,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::TargetProofCorpusModule,
        &blocker.target_proof_corpus_module,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::DeclarationName,
        &blocker.declaration_name,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::BlockerHash,
        invented_candidate_typecheck_blocker_hash(blocker),
        blocker.blocker_hash,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::RequestHash,
        request.request_hash,
        blocker.request_hash,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::CandidateId,
        &request.candidate_id,
        &blocker.candidate_id,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::TargetProofCorpusModule,
        &request.target_proof_corpus_module,
        &blocker.target_proof_corpus_module,
    )?;
    validate_invented_candidate_identifier_match(
        InventedCandidateTypecheckField::DeclarationName,
        &request.declaration_name,
        &blocker.declaration_name,
    )?;
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::StatementHash,
        request.statement_hash,
        blocker.statement_hash,
    )?;
    if !blocker.unproved_storage_kind.is_unproved_sidecar() {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::UnprovedStorageKindNotSidecar {
                storage_kind: blocker.unproved_storage_kind,
            },
        ));
    }
    if blocker.creates_theorem_declaration {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::BlockerCreatesTheoremDeclaration,
        ));
    }
    Ok(())
}

pub fn invented_lemma_authoring_command_hash(command: &InventedLemmaAuthoringCommand) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_LEMMA_AUTHORING_COMMAND_PROFILE);
    encode_string(&mut out, command.kind.as_str());
    encode_option_string(&mut out, command.module.as_deref());
    encode_bool(&mut out, command.verified_cache_authoring);
    encode_bool(&mut out, command.package_metadata);
    hash_with_domain(
        "npa.theorem-invention.proof-task.authoring-command.hash.v1",
        &out,
    )
}

pub fn invented_lemma_package_side_effect_policy_hash(
    policy: &InventedLemmaPackageSideEffectPolicy,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_LEMMA_PACKAGE_SIDE_EFFECT_PROFILE);
    encode_bool(&mut out, policy.package_lock_updated);
    encode_bool(&mut out, policy.package_theorem_index_updated);
    encode_bool(&mut out, policy.axiom_report_updated);
    encode_bool(&mut out, policy.publish_plan_updated);
    hash_with_domain(
        "npa.theorem-invention.proof-task.package-side-effect.hash.v1",
        &out,
    )
}

pub fn invented_lemma_artifact_readiness_hash(readiness: &InventedLemmaArtifactReadiness) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_LEMMA_ARTIFACT_READINESS_PROFILE);
    encode_string(&mut out, readiness.theorem_level.as_str());
    encode_bool(&mut out, readiness.source_exists);
    encode_bool(&mut out, readiness.certificate_exists);
    encode_bool(&mut out, readiness.meta_exists);
    encode_bool(&mut out, readiness.replay_exists);
    encode_bool(&mut out, readiness.source_free_verified);
    hash_with_domain(
        "npa.theorem-invention.proof-task.artifact-readiness.hash.v1",
        &out,
    )
}

pub fn invented_lemma_proof_task_handoff_hash(handoff: &InventedLemmaProofTaskHandoff) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, INVENTED_LEMMA_PROOF_TASK_HANDOFF_PROFILE);
    encode_hash(&mut out, &handoff.typecheck_request_hash);
    encode_hash(&mut out, &handoff.typecheck_handoff_hash);
    encode_string(&mut out, &handoff.candidate_id);
    encode_string(&mut out, &handoff.source_module);
    encode_string(&mut out, &handoff.target_proof_corpus_module);
    encode_string(&mut out, &handoff.declaration_name);
    encode_string(&mut out, &handoff.theorem_statement);
    encode_hash(&mut out, &handoff.statement_hash);
    encode_hash(&mut out, &handoff.expected_type_hash);
    encode_hash(&mut out, &handoff.environment_hash);
    encode_hash(&mut out, &handoff.generalized_context.context_hash);
    let mut dependencies = handoff.dependency_identities.clone();
    dependencies.sort_by_key(|dependency| dependency.dependency_identity_hash);
    encode_uvar(&mut out, dependencies.len() as u64);
    for dependency in dependencies {
        encode_hash(&mut out, &dependency.dependency_identity_hash);
    }
    encode_hash(&mut out, &handoff.import_closure_hash);
    encode_hash(&mut out, &handoff.axiom_policy_hash);
    encode_string(&mut out, &handoff.source_path);
    encode_string(&mut out, &handoff.certificate_path);
    encode_string(&mut out, &handoff.meta_path);
    encode_string(&mut out, &handoff.replay_path);
    encode_uvar(&mut out, handoff.expected_authoring_commands.len() as u64);
    for command in &handoff.expected_authoring_commands {
        encode_hash(&mut out, &command.command_hash);
    }
    encode_hash(&mut out, &handoff.package_side_effect_policy.policy_hash);
    encode_hash(&mut out, &handoff.local_lemma_handoff_hash);
    encode_bool(&mut out, handoff.creates_theorem_declaration);
    hash_with_domain("npa.theorem-invention.proof-task.handoff.hash.v1", &out)
}

pub fn invented_lemma_no_package_side_effect_policy() -> InventedLemmaPackageSideEffectPolicy {
    let mut policy = InventedLemmaPackageSideEffectPolicy {
        policy_hash: [0; 32],
        package_lock_updated: false,
        package_theorem_index_updated: false,
        axiom_report_updated: false,
        publish_plan_updated: false,
    };
    policy.policy_hash = invented_lemma_package_side_effect_policy_hash(&policy);
    policy
}

pub fn invented_lemma_artifact_readiness(
    theorem_level: TheoremLevel,
    source_exists: bool,
    certificate_exists: bool,
    meta_exists: bool,
    replay_exists: bool,
    source_free_verified: bool,
) -> InventedLemmaArtifactReadiness {
    let mut readiness = InventedLemmaArtifactReadiness {
        readiness_hash: [0; 32],
        theorem_level,
        source_exists,
        certificate_exists,
        meta_exists,
        replay_exists,
        source_free_verified,
    };
    readiness.readiness_hash = invented_lemma_artifact_readiness_hash(&readiness);
    readiness
}

pub fn invented_lemma_expected_authoring_commands(
    target_proof_corpus_module: &str,
) -> Vec<InventedLemmaAuthoringCommand> {
    let mut commands = vec![
        InventedLemmaAuthoringCommand {
            command_hash: [0; 32],
            kind: InventedLemmaAuthoringCommandKind::BuildModule,
            module: Some(target_proof_corpus_module.to_owned()),
            verified_cache_authoring: false,
            package_metadata: false,
        },
        InventedLemmaAuthoringCommand {
            command_hash: [0; 32],
            kind: InventedLemmaAuthoringCommandKind::VerifyModuleSourceFree,
            module: Some(target_proof_corpus_module.to_owned()),
            verified_cache_authoring: true,
            package_metadata: false,
        },
        InventedLemmaAuthoringCommand {
            command_hash: [0; 32],
            kind: InventedLemmaAuthoringCommandKind::VerifyChangedOnlySourceFree,
            module: None,
            verified_cache_authoring: true,
            package_metadata: false,
        },
        InventedLemmaAuthoringCommand {
            command_hash: [0; 32],
            kind: InventedLemmaAuthoringCommandKind::CheckCorpusAuthoring,
            module: None,
            verified_cache_authoring: true,
            package_metadata: false,
        },
    ];
    for command in &mut commands {
        command.command_hash = invented_lemma_authoring_command_hash(command);
    }
    commands
}

pub fn invented_lemma_proof_task_handoff_from_typecheck(
    request: &InventedCandidateTypecheckRequest,
    typecheck_handoff: &InventedCandidateTypecheckHandoff,
    dependency_identities: Vec<LocalLemmaAvailableDependencyIdentity>,
    source_path: String,
    certificate_path: String,
    meta_path: String,
    replay_path: String,
) -> Result<InventedLemmaProofTaskHandoff, InventedLemmaProofTaskError> {
    validate_invented_candidate_typecheck_handoff(request, typecheck_handoff).map_err(|error| {
        InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::CandidateTypecheckInvalid {
                error_kind: error.kind().as_str().to_owned(),
            },
        )
    })?;
    let mut handoff = InventedLemmaProofTaskHandoff {
        handoff_hash: [0; 32],
        typecheck_request_hash: request.request_hash,
        typecheck_handoff_hash: typecheck_handoff.handoff_hash,
        candidate_id: typecheck_handoff.candidate_id.clone(),
        source_module: typecheck_handoff.source_module.clone(),
        target_proof_corpus_module: typecheck_handoff.target_proof_corpus_module.clone(),
        declaration_name: typecheck_handoff.declaration_name.clone(),
        theorem_statement: request.normalized_statement.clone(),
        statement_hash: typecheck_handoff.statement_hash,
        expected_type_hash: typecheck_handoff.expected_type_hash,
        environment_hash: typecheck_handoff.environment_hash,
        generalized_context: typecheck_handoff.generalized_context.clone(),
        dependency_identities,
        import_identities: typecheck_handoff.import_identities.clone(),
        import_closure_hash: invented_candidate_import_closure_hash(
            &typecheck_handoff.import_identities,
        ),
        axiom_policy_hash: typecheck_handoff.axiom_policy_hash,
        source_path,
        certificate_path,
        meta_path,
        replay_path,
        expected_authoring_commands: invented_lemma_expected_authoring_commands(
            &typecheck_handoff.target_proof_corpus_module,
        ),
        package_side_effect_policy: invented_lemma_no_package_side_effect_policy(),
        local_lemma_handoff_hash: [0; 32],
        creates_theorem_declaration: false,
    };
    let local_handoff = invented_lemma_local_proof_task_handoff_unchecked(&handoff);
    handoff.local_lemma_handoff_hash = local_lemma_proof_task_handoff_hash(&local_handoff);
    handoff.handoff_hash = invented_lemma_proof_task_handoff_hash(&handoff);
    validate_invented_lemma_proof_task_handoff(request, typecheck_handoff, &handoff)?;
    Ok(handoff)
}

pub fn validate_invented_lemma_proof_task_handoff(
    request: &InventedCandidateTypecheckRequest,
    typecheck_handoff: &InventedCandidateTypecheckHandoff,
    handoff: &InventedLemmaProofTaskHandoff,
) -> Result<(), InventedLemmaProofTaskError> {
    validate_invented_candidate_typecheck_handoff(request, typecheck_handoff).map_err(|error| {
        InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::CandidateTypecheckInvalid {
                error_kind: error.kind().as_str().to_owned(),
            },
        )
    })?;
    validate_invented_lemma_proof_task_shape(handoff)?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::TypecheckRequestHash,
        request.request_hash,
        handoff.typecheck_request_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::TypecheckHandoffHash,
        typecheck_handoff.handoff_hash,
        handoff.typecheck_handoff_hash,
    )?;
    validate_invented_lemma_identifier_match(
        InventedLemmaProofTaskField::CandidateId,
        &typecheck_handoff.candidate_id,
        &handoff.candidate_id,
    )?;
    validate_invented_lemma_identifier_match(
        InventedLemmaProofTaskField::SourceModule,
        &typecheck_handoff.source_module,
        &handoff.source_module,
    )?;
    validate_invented_lemma_identifier_match(
        InventedLemmaProofTaskField::TargetProofCorpusModule,
        &typecheck_handoff.target_proof_corpus_module,
        &handoff.target_proof_corpus_module,
    )?;
    validate_invented_lemma_identifier_match(
        InventedLemmaProofTaskField::DeclarationName,
        &typecheck_handoff.declaration_name,
        &handoff.declaration_name,
    )?;
    validate_invented_lemma_identifier_match(
        InventedLemmaProofTaskField::TheoremStatement,
        &request.normalized_statement,
        &handoff.theorem_statement,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::StatementHash,
        typecheck_handoff.statement_hash,
        handoff.statement_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::ExpectedTypeHash,
        typecheck_handoff.expected_type_hash,
        handoff.expected_type_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::EnvironmentHash,
        typecheck_handoff.environment_hash,
        handoff.environment_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::GeneralizedContextHash,
        theorem_invention_generalized_context_hash(&handoff.generalized_context),
        handoff.generalized_context.context_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::GeneralizedContextHash,
        typecheck_handoff.generalized_context.context_hash,
        handoff.generalized_context.context_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::ImportClosureHash,
        invented_candidate_import_closure_hash(&typecheck_handoff.import_identities),
        handoff.import_closure_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::ImportClosureHash,
        invented_candidate_import_closure_hash(&handoff.import_identities),
        handoff.import_closure_hash,
    )?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::AxiomPolicyHash,
        typecheck_handoff.axiom_policy_hash,
        handoff.axiom_policy_hash,
    )?;
    for dependency in &handoff.dependency_identities {
        validate_available_dependency_identity(dependency).map_err(|error| {
            InventedLemmaProofTaskError::new(
                InventedLemmaProofTaskErrorKind::DependencyNotSharable {
                    error_kind: error.kind().as_str(),
                },
            )
        })?;
    }
    validate_invented_lemma_authoring_commands(
        &handoff.expected_authoring_commands,
        &handoff.target_proof_corpus_module,
    )?;
    validate_invented_lemma_package_side_effect_policy(&handoff.package_side_effect_policy)?;
    let local_handoff = invented_lemma_local_proof_task_handoff_unchecked(handoff);
    validate_local_lemma_proof_task_handoff(&local_handoff).map_err(|error| {
        InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::LocalLemmaHandoffInvalid {
                error_kind: error.kind().as_str().to_owned(),
            },
        )
    })?;
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::LocalLemmaHandoffHash,
        local_lemma_proof_task_handoff_hash(&local_handoff),
        handoff.local_lemma_handoff_hash,
    )?;
    if handoff.creates_theorem_declaration {
        return Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::CreatesTheoremDeclaration,
        ));
    }
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::HandoffHash,
        invented_lemma_proof_task_handoff_hash(handoff),
        handoff.handoff_hash,
    )
}

pub fn invented_lemma_local_proof_task_handoff(
    request: &InventedCandidateTypecheckRequest,
    typecheck_handoff: &InventedCandidateTypecheckHandoff,
    handoff: &InventedLemmaProofTaskHandoff,
) -> Result<LocalLemmaProofTaskHandoff, InventedLemmaProofTaskError> {
    validate_invented_lemma_proof_task_handoff(request, typecheck_handoff, handoff)?;
    Ok(invented_lemma_local_proof_task_handoff_unchecked(handoff))
}

pub fn invented_lemma_local_proof_task_from_handoff(
    request: &InventedCandidateTypecheckRequest,
    typecheck_handoff: &InventedCandidateTypecheckHandoff,
    handoff: &InventedLemmaProofTaskHandoff,
) -> Result<LocalLemmaProofTask, InventedLemmaProofTaskError> {
    let local_type_checked = invented_lemma_local_type_checked(handoff);
    let local_handoff =
        invented_lemma_local_proof_task_handoff(request, typecheck_handoff, handoff)?;
    local_lemma_proof_task_from_handoff(&local_type_checked, &local_handoff).map_err(|error| {
        InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::LocalLemmaHandoffInvalid {
                error_kind: error.kind().as_str().to_owned(),
            },
        )
    })
}

pub fn validate_invented_lemma_proof_task_outcome(
    request: &InventedCandidateTypecheckRequest,
    typecheck_handoff: &InventedCandidateTypecheckHandoff,
    handoff: &InventedLemmaProofTaskHandoff,
    status: LocalLemmaProofTaskStatus,
    parent_hole: LocalLemmaParentHoleDisposition,
    verified_artifact: Option<&LocalLemmaVerifiedArtifactRecord>,
    readiness: Option<&InventedLemmaArtifactReadiness>,
) -> Result<(), InventedLemmaProofTaskError> {
    let local_handoff =
        invented_lemma_local_proof_task_handoff(request, typecheck_handoff, handoff)?;
    if status.creates_verified_artifact() {
        let artifact = verified_artifact.ok_or_else(|| {
            InventedLemmaProofTaskError::new(
                InventedLemmaProofTaskErrorKind::TheoremArtifactRequired { status },
            )
        })?;
        let readiness = readiness.ok_or_else(|| {
            InventedLemmaProofTaskError::new(InventedLemmaProofTaskErrorKind::ReadinessRequired {
                status,
            })
        })?;
        validate_invented_lemma_artifact_readiness(readiness)?;
        validate_invented_lemma_identifier_match(
            InventedLemmaProofTaskField::ReplayPath,
            &handoff.replay_path,
            &artifact.replay_path,
        )?;
        validate_local_lemma_verified_artifact_record(&local_handoff, artifact).map_err(
            |error| {
                InventedLemmaProofTaskError::new(
                    InventedLemmaProofTaskErrorKind::LocalLemmaHandoffInvalid {
                        error_kind: error.kind().as_str().to_owned(),
                    },
                )
            },
        )?;
        return Ok(());
    }
    if parent_hole != LocalLemmaParentHoleDisposition::Unresolved {
        return Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::ParentHoleMustRemainUnresolved {
                status,
                parent_hole,
            },
        ));
    }
    if verified_artifact.is_some() || readiness.is_some() {
        return Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::TheoremArtifactNotAllowed { status },
        ));
    }
    Ok(())
}

pub fn invented_lemma_verified_from_task(
    request: &InventedCandidateTypecheckRequest,
    typecheck_handoff: &InventedCandidateTypecheckHandoff,
    handoff: &InventedLemmaProofTaskHandoff,
    artifact: &LocalLemmaVerifiedArtifactRecord,
    readiness: &InventedLemmaArtifactReadiness,
) -> Result<LocalLemmaVerified, InventedLemmaProofTaskError> {
    validate_invented_lemma_proof_task_outcome(
        request,
        typecheck_handoff,
        handoff,
        LocalLemmaProofTaskStatus::SourceFreeVerified,
        LocalLemmaParentHoleDisposition::Available,
        Some(artifact),
        Some(readiness),
    )?;
    let local_handoff =
        invented_lemma_local_proof_task_handoff(request, typecheck_handoff, handoff)?;
    local_lemma_verified_from_handoff(&local_handoff, artifact).map_err(|error| {
        InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::LocalLemmaHandoffInvalid {
                error_kind: error.kind().as_str().to_owned(),
            },
        )
    })
}

pub fn validate_theorem_invention_artifact(
    artifact: &TheoremInventionArtifact,
) -> Result<(), TheoremInventionArtifactError> {
    validate_non_empty_theorem_invention_identifier(
        TheoremInventionArtifactField::SourceModule,
        &artifact.source_module,
    )?;
    validate_non_empty_theorem_invention_identifier(
        TheoremInventionArtifactField::TargetProofCorpusModule,
        &artifact.target_proof_corpus_module,
    )?;
    validate_non_empty_theorem_invention_identifier(
        TheoremInventionArtifactField::DeclarationName,
        &artifact.declaration_name,
    )?;
    validate_non_empty_theorem_invention_identifier(
        TheoremInventionArtifactField::NormalizedStatement,
        &artifact.normalized_statement,
    )?;
    if let Some(replay_path) = artifact.replay_path.as_deref() {
        validate_non_empty_theorem_invention_identifier(
            TheoremInventionArtifactField::ReplayPath,
            replay_path,
        )?;
    }
    if let Some(certificate_path) = artifact.certificate_path.as_deref() {
        validate_non_empty_theorem_invention_identifier(
            TheoremInventionArtifactField::CertificatePath,
            certificate_path,
        )?;
    }
    if let Some(blocker) = artifact.prerequisite_blocker.as_deref() {
        validate_non_empty_theorem_invention_identifier(
            TheoremInventionArtifactField::PrerequisiteBlocker,
            blocker,
        )?;
    }
    validate_theorem_invention_hash_match(
        TheoremInventionArtifactField::GeneralizedContextHash,
        theorem_invention_generalized_context_hash(&artifact.generalized_context),
        artifact.generalized_context.context_hash,
    )?;
    validate_theorem_invention_verification_commands(artifact)?;
    if !artifact.theorem_level.is_l2_derived_certificate()
        && artifact.prerequisite_blocker.is_none()
    {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::NonL2CandidateNeedsPrerequisiteBlocker {
                theorem_level: artifact.theorem_level,
            },
        ));
    }
    if artifact.promotion_intent == TheoremInventionPromotionIntent::BlockedPrerequisite
        && artifact.prerequisite_blocker.is_none()
    {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::PrerequisiteBlockerMissing {
                promotion_intent: artifact.promotion_intent,
            },
        ));
    }
    if artifact.promotion_intent.is_promotion_ready()
        && !artifact.artifact_kind.is_checked_artifact()
    {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::SidecarCannotBePromotionReady,
        ));
    }
    if artifact.artifact_kind.is_checked_artifact()
        && !artifact.theorem_level.is_l2_derived_certificate()
    {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::ProofCorpusArtifactRequiresL2 {
                theorem_level: artifact.theorem_level,
            },
        ));
    }
    if artifact.conclusion_assuming {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::ConclusionAssuming,
        ));
    }
    if artifact.replay_is_stale {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::StaleReplay,
        ));
    }
    if artifact.import_closure_is_stale {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::StaleImport,
        ));
    }
    if artifact.axiom_policy_widened {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::WidenedAxiomPolicy,
        ));
    }
    if artifact.artifact_kind.is_checked_artifact()
        || artifact.promotion_intent.is_promotion_ready()
    {
        if artifact.replay_path.is_none() || artifact.replay_hash.is_none() {
            return Err(TheoremInventionArtifactError::new(
                TheoremInventionArtifactErrorKind::MissingReplay,
            ));
        }
        if artifact.certificate_path.is_none() || artifact.certificate_hash.is_none() {
            return Err(TheoremInventionArtifactError::new(
                TheoremInventionArtifactErrorKind::MissingCertificate,
            ));
        }
    }
    validate_theorem_invention_hash_match(
        TheoremInventionArtifactField::ArtifactIdentityHash,
        theorem_invention_artifact_identity_hash(artifact),
        artifact.artifact_identity_hash,
    )
}

pub fn validate_local_lemma_proof_task_handoff(
    handoff: &LocalLemmaProofTaskHandoff,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::LemmaId,
        &handoff.lemma_id,
    )?;
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::SketchNodeId,
        &handoff.sketch_node_id,
    )?;
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::Module,
        &handoff.module,
    )?;
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::DeclarationName,
        &handoff.declaration_name,
    )?;
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::TargetProofCorpusModule,
        &handoff.target_proof_corpus_module,
    )?;
    validate_handoff_identifier_match(
        LocalLemmaProofTaskHandoffField::TargetProofCorpusModule,
        &handoff.module,
        &handoff.target_proof_corpus_module,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::GeneralizedContextHash,
        local_lemma_generalized_context_hash(&handoff.generalized_context),
        handoff.generalized_context.context_hash,
    )?;
    for dependency in &handoff.dependency_identities {
        validate_available_dependency_identity(dependency).map_err(|error| {
            LocalLemmaProofTaskHandoffError::new(
                LocalLemmaProofTaskHandoffErrorKind::DependencyNotSharable {
                    error_kind: error.kind.as_str(),
                },
            )
        })?;
    }
    validate_expected_local_lemma_verification_commands(handoff)?;
    if !handoff.unproved_storage_kind.is_unproved_sidecar() {
        return Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::UnprovedStorageKindNotSidecar {
                storage_kind: handoff.unproved_storage_kind,
            },
        ));
    }
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::HandoffHash,
        local_lemma_proof_task_handoff_hash(handoff),
        handoff.handoff_hash,
    )
}

pub fn local_lemma_proof_task_from_handoff(
    type_checked: &LocalLemmaTypeChecked,
    handoff: &LocalLemmaProofTaskHandoff,
) -> Result<LocalLemmaProofTask, LocalLemmaProofTaskHandoffError> {
    validate_local_lemma_proof_task_handoff(handoff)?;
    validate_handoff_identifier_match(
        LocalLemmaProofTaskHandoffField::LemmaId,
        &type_checked.lemma_id,
        &handoff.lemma_id,
    )?;
    validate_handoff_identifier_match(
        LocalLemmaProofTaskHandoffField::SketchNodeId,
        &type_checked.sketch_node_id,
        &handoff.sketch_node_id,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::SketchHash,
        type_checked.sketch_hash,
        handoff.sketch_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::StatementHash,
        type_checked.statement_hash,
        handoff.statement_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::ExpectedTypeHash,
        type_checked.expected_type_hash,
        handoff.expected_type_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::EnvironmentHash,
        type_checked.environment_hash,
        handoff.environment_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::AxiomPolicyHash,
        type_checked.policy_hash,
        handoff.axiom_policy_hash,
    )?;
    Ok(LocalLemmaProofTask {
        lemma_id: handoff.lemma_id.clone(),
        sketch_hash: handoff.sketch_hash,
        sketch_node_id: handoff.sketch_node_id.clone(),
        statement_hash: handoff.statement_hash,
        expected_type_hash: handoff.expected_type_hash,
        environment_hash: handoff.environment_hash,
        policy_hash: handoff.axiom_policy_hash,
        task_identity: local_lemma_task_identity_from_handoff(handoff),
    })
}

pub fn validate_local_lemma_proof_task_outcome(
    handoff: &LocalLemmaProofTaskHandoff,
    outcome: &LocalLemmaProofTaskOutcome,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    validate_local_lemma_proof_task_handoff(handoff)?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::HandoffHash,
        handoff.handoff_hash,
        outcome.handoff_hash,
    )?;
    if outcome.status.creates_verified_artifact() {
        let artifact = outcome.verified_artifact.as_ref().ok_or_else(|| {
            LocalLemmaProofTaskHandoffError::new(
                LocalLemmaProofTaskHandoffErrorKind::MissingVerifiedArtifact {
                    status: outcome.status,
                },
            )
        })?;
        validate_local_lemma_verified_artifact_record(handoff, artifact)?;
        return Ok(());
    }
    if outcome.parent_hole != LocalLemmaParentHoleDisposition::Unresolved {
        return Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::ParentHoleMustRemainUnresolved {
                status: outcome.status,
                parent_hole: outcome.parent_hole,
            },
        ));
    }
    if outcome.verified_artifact.is_some() {
        return Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::TheoremArtifactNotAllowed {
                status: outcome.status,
            },
        ));
    }
    Ok(())
}

pub fn validate_local_lemma_verified_artifact_record(
    handoff: &LocalLemmaProofTaskHandoff,
    artifact: &LocalLemmaVerifiedArtifactRecord,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    validate_local_lemma_proof_task_handoff(handoff)?;
    validate_local_lemma_verified_artifact_record_inner(handoff, artifact)
}

pub fn local_lemma_verified_from_handoff(
    handoff: &LocalLemmaProofTaskHandoff,
    artifact: &LocalLemmaVerifiedArtifactRecord,
) -> Result<LocalLemmaVerified, LocalLemmaProofTaskHandoffError> {
    validate_local_lemma_verified_artifact_record(handoff, artifact)?;
    let task_identity = local_lemma_task_identity_from_handoff(handoff);
    let proof_artifact_identity = local_lemma_verified_artifact_identity(handoff, artifact)?;
    let proof_artifact_identity_hash = proof_artifact_identity.hash();
    let verified = LocalLemmaVerified {
        lemma_id: handoff.lemma_id.clone(),
        sketch_hash: handoff.sketch_hash,
        sketch_node_id: handoff.sketch_node_id.clone(),
        statement_hash: handoff.statement_hash,
        expected_type_hash: handoff.expected_type_hash,
        environment_hash: handoff.environment_hash,
        policy_hash: handoff.axiom_policy_hash,
        task_identity,
        proof_artifact_identity,
        proof_artifact_identity_hash,
        source_free_verifier_result: artifact.source_free_verifier_result.clone(),
    };
    validate_local_lemma_verified_state(&verified).map_err(local_lemma_handoff_lifecycle_error)?;
    Ok(verified)
}

pub fn validate_local_lemma_lifecycle_transition(
    from: &LocalLemmaLifecycleState,
    to: &LocalLemmaLifecycleState,
) -> Result<(), LocalLemmaLifecycleError> {
    match (from, to) {
        (LocalLemmaLifecycleState::Proposed(from), LocalLemmaLifecycleState::TypeChecked(to)) => {
            validate_local_lemma_proposed_to_type_checked(from, to)
        }
        (LocalLemmaLifecycleState::TypeChecked(from), LocalLemmaLifecycleState::ProofTask(to)) => {
            validate_local_lemma_type_checked_to_proof_task(from, to)
        }
        (LocalLemmaLifecycleState::ProofTask(from), LocalLemmaLifecycleState::Verified(to)) => {
            validate_local_lemma_proof_task_to_verified(from, to)
        }
        (LocalLemmaLifecycleState::Verified(from), LocalLemmaLifecycleState::Available(to)) => {
            validate_local_lemma_verified_to_available(from, to)
        }
        _ => Err(LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::InvalidTransition {
                from: from.phase(),
                to: to.phase(),
            },
        )),
    }
}

pub fn local_lemma_available_from_verified(
    verified: &LocalLemmaVerified,
) -> Result<LocalLemmaAvailable, LocalLemmaLifecycleError> {
    validate_local_lemma_verified_state(verified)?;
    let verified_theorem_identity_hash = verified.proof_artifact_identity_hash;
    let mut available_dependency_identity = LocalLemmaAvailableDependencyIdentity {
        dependency_identity_hash: [0; 32],
        verified_artifact_identity_hash: verified_theorem_identity_hash,
        state: verified.proof_artifact_identity.state,
        statement_hash: verified.statement_hash,
        environment_hash: verified.environment_hash,
        policy_hash: verified.policy_hash,
    };
    available_dependency_identity.dependency_identity_hash =
        local_lemma_available_dependency_identity_hash(&available_dependency_identity);
    Ok(LocalLemmaAvailable {
        lemma_id: verified.lemma_id.clone(),
        sketch_hash: verified.sketch_hash,
        sketch_node_id: verified.sketch_node_id.clone(),
        statement_hash: verified.statement_hash,
        expected_type_hash: verified.expected_type_hash,
        environment_hash: verified.environment_hash,
        policy_hash: verified.policy_hash,
        task_identity: verified.task_identity.clone(),
        verified_theorem_identity: verified.proof_artifact_identity.clone(),
        verified_theorem_identity_hash,
        available_dependency_identity,
    })
}

pub fn local_lemma_verified_only_sharing_check<'a>(
    state: &'a LocalLemmaLifecycleState,
    surface: VerifiedOnlySharingSurface,
) -> VerifiedOnlySharingCheck<'a> {
    match state {
        LocalLemmaLifecycleState::Available(available) => VerifiedOnlySharingCheck {
            surface,
            artifact_kind: VerifiedOnlySharingArtifactKind::VerifiedArtifactIdentity,
            state: available.verified_theorem_identity.state,
            verified_artifact_identity_hash: Some(&available.verified_theorem_identity_hash),
            candidate_identity_hash: None,
        },
        _ => VerifiedOnlySharingCheck {
            surface,
            artifact_kind: VerifiedOnlySharingArtifactKind::UnverifiedLocalLemma,
            state: state.phase().acceptance_state(),
            verified_artifact_identity_hash: None,
            candidate_identity_hash: None,
        },
    }
}

pub fn validate_local_lemma_verified_only_sharing(
    state: &LocalLemmaLifecycleState,
    surface: VerifiedOnlySharingSurface,
) -> Result<LocalLemmaAvailableDependencyIdentity, VerifiedOnlySharingError> {
    let check = local_lemma_verified_only_sharing_check(state, surface);
    validate_verified_only_sharing(check)?;
    match state {
        LocalLemmaLifecycleState::Available(available) => {
            Ok(available.available_dependency_identity.clone())
        }
        _ => unreachable!("non-available local lemma sharing must be rejected"),
    }
}

fn validate_local_lemma_proposed_to_type_checked(
    from: &LocalLemmaProposed,
    to: &LocalLemmaTypeChecked,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::LemmaId,
        &from.lemma_id,
        &to.lemma_id,
    )?;
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::SketchNodeId,
        &from.sketch_node_id,
        &to.sketch_node_id,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::SketchHash,
        from.sketch_hash,
        to.sketch_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        from.statement_hash,
        to.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        from.environment_hash,
        to.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        from.policy_hash,
        to.policy_hash,
    )
}

fn validate_local_lemma_type_checked_to_proof_task(
    from: &LocalLemmaTypeChecked,
    to: &LocalLemmaProofTask,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_type_checked_common_identity(from, to)?;
    validate_task_identity(&to.task_identity)?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        from.statement_hash,
        to.task_identity.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ExpectedTypeHash,
        from.expected_type_hash,
        to.task_identity.expected_type_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        from.environment_hash,
        to.task_identity.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        from.policy_hash,
        to.task_identity.policy_hash,
    )
}

fn validate_local_lemma_proof_task_to_verified(
    from: &LocalLemmaProofTask,
    to: &LocalLemmaVerified,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_proof_task_common_identity(from, to)?;
    validate_task_identity(&from.task_identity)?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::TaskIdentityHash,
        from.task_identity.task_identity_hash,
        to.task_identity.task_identity_hash,
    )?;
    validate_local_lemma_verified_state(to)
}

fn validate_local_lemma_verified_to_available(
    from: &LocalLemmaVerified,
    to: &LocalLemmaAvailable,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_verified_common_identity(from, to)?;
    validate_local_lemma_verified_state(from)?;
    validate_task_identity(&to.task_identity)?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::TaskIdentityHash,
        from.task_identity.task_identity_hash,
        to.task_identity.task_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::VerifiedTheoremIdentityHash,
        from.proof_artifact_identity_hash,
        to.verified_theorem_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::VerifiedTheoremIdentityHash,
        to.verified_theorem_identity.hash(),
        to.verified_theorem_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ProofArtifactIdentityHash,
        from.proof_artifact_identity_hash,
        to.verified_theorem_identity.hash(),
    )?;
    validate_available_dependency_identity(&to.available_dependency_identity)?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::AvailableDependencyIdentityHash,
        to.verified_theorem_identity_hash,
        to.available_dependency_identity
            .verified_artifact_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        to.statement_hash,
        to.available_dependency_identity.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        to.environment_hash,
        to.available_dependency_identity.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        to.policy_hash,
        to.available_dependency_identity.policy_hash,
    )?;
    validate_verified_artifact_identity(&to.verified_theorem_identity).map_err(|error| {
        LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::VerifiedArtifactIdentityInvalid {
                error_kind: error.kind(),
            },
        )
    })?;
    validate_state_match(
        LocalLemmaLifecycleIdentityField::AvailableDependencyState,
        to.verified_theorem_identity.state,
        to.available_dependency_identity.state,
    )?;
    Ok(())
}

fn validate_local_lemma_verified_state(
    verified: &LocalLemmaVerified,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_task_identity(&verified.task_identity)?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        verified.statement_hash,
        verified.task_identity.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ExpectedTypeHash,
        verified.expected_type_hash,
        verified.task_identity.expected_type_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        verified.environment_hash,
        verified.task_identity.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        verified.policy_hash,
        verified.task_identity.policy_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ProofArtifactIdentityHash,
        verified.proof_artifact_identity.hash(),
        verified.proof_artifact_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        verified.statement_hash,
        verified.proof_artifact_identity.statement_hash,
    )?;
    validate_verified_artifact_identity(&verified.proof_artifact_identity).map_err(|error| {
        LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::VerifiedArtifactIdentityInvalid {
                error_kind: error.kind(),
            },
        )
    })?;
    validate_source_free_verifier_result(&verified.source_free_verifier_result)?;
    validate_state_match(
        LocalLemmaLifecycleIdentityField::SourceFreeVerifierResultStatus,
        verified.proof_artifact_identity.state,
        verified.source_free_verifier_result.status,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::TaskIdentityHash,
        verified.task_identity.task_identity_hash,
        verified.source_free_verifier_result.task_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ProofArtifactIdentityHash,
        verified.proof_artifact_identity_hash,
        verified
            .source_free_verifier_result
            .proof_artifact_identity_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        verified.statement_hash,
        verified.source_free_verifier_result.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        verified.environment_hash,
        verified.source_free_verifier_result.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        verified.policy_hash,
        verified.source_free_verifier_result.policy_hash,
    )?;
    Ok(())
}

fn validate_task_identity(
    task_identity: &LocalLemmaProofTaskIdentity,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::TaskIdentityHash,
        local_lemma_proof_task_identity_hash(task_identity),
        task_identity.task_identity_hash,
    )?;
    for dependency in &task_identity.available_dependency_identities {
        validate_available_dependency_identity(dependency)?;
    }
    Ok(())
}

fn validate_source_free_verifier_result(
    result: &LocalLemmaSourceFreeVerifierResult,
) -> Result<(), LocalLemmaLifecycleError> {
    if !result.status.is_verified_artifact_state() {
        return Err(LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::SourceFreeVerifierResultNotVerified {
                status: result.status,
            },
        ));
    }
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::SourceFreeVerifierResultHash,
        local_lemma_source_free_verifier_result_hash(result),
        result.result_hash,
    )
}

fn validate_available_dependency_identity(
    dependency: &LocalLemmaAvailableDependencyIdentity,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::AvailableDependencyIdentityHash,
        local_lemma_available_dependency_identity_hash(dependency),
        dependency.dependency_identity_hash,
    )?;
    validate_verified_only_sharing(VerifiedOnlySharingCheck {
        surface: VerifiedOnlySharingSurface::TaskDependencyRelease,
        artifact_kind: VerifiedOnlySharingArtifactKind::VerifiedArtifactIdentity,
        state: dependency.state,
        verified_artifact_identity_hash: Some(&dependency.verified_artifact_identity_hash),
        candidate_identity_hash: None,
    })
    .map_err(|error| {
        LocalLemmaLifecycleError::new(LocalLemmaLifecycleErrorKind::DependencyNotSharable {
            surface: VerifiedOnlySharingSurface::TaskDependencyRelease,
            error_kind: error.kind(),
        })
    })
}

fn validate_type_checked_common_identity(
    from: &LocalLemmaTypeChecked,
    to: &LocalLemmaProofTask,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::LemmaId,
        &from.lemma_id,
        &to.lemma_id,
    )?;
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::SketchNodeId,
        &from.sketch_node_id,
        &to.sketch_node_id,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::SketchHash,
        from.sketch_hash,
        to.sketch_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        from.statement_hash,
        to.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ExpectedTypeHash,
        from.expected_type_hash,
        to.expected_type_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        from.environment_hash,
        to.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        from.policy_hash,
        to.policy_hash,
    )
}

fn validate_proof_task_common_identity(
    from: &LocalLemmaProofTask,
    to: &LocalLemmaVerified,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::LemmaId,
        &from.lemma_id,
        &to.lemma_id,
    )?;
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::SketchNodeId,
        &from.sketch_node_id,
        &to.sketch_node_id,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::SketchHash,
        from.sketch_hash,
        to.sketch_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        from.statement_hash,
        to.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ExpectedTypeHash,
        from.expected_type_hash,
        to.expected_type_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        from.environment_hash,
        to.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        from.policy_hash,
        to.policy_hash,
    )
}

fn validate_verified_common_identity(
    from: &LocalLemmaVerified,
    to: &LocalLemmaAvailable,
) -> Result<(), LocalLemmaLifecycleError> {
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::LemmaId,
        &from.lemma_id,
        &to.lemma_id,
    )?;
    validate_identifier_match(
        LocalLemmaLifecycleIdentityField::SketchNodeId,
        &from.sketch_node_id,
        &to.sketch_node_id,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::SketchHash,
        from.sketch_hash,
        to.sketch_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::StatementHash,
        from.statement_hash,
        to.statement_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::ExpectedTypeHash,
        from.expected_type_hash,
        to.expected_type_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::EnvironmentHash,
        from.environment_hash,
        to.environment_hash,
    )?;
    validate_hash_match(
        LocalLemmaLifecycleIdentityField::PolicyHash,
        from.policy_hash,
        to.policy_hash,
    )
}

fn validate_identifier_match(
    field: LocalLemmaLifecycleIdentityField,
    expected: &str,
    actual: &str,
) -> Result<(), LocalLemmaLifecycleError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::IdentifierMismatch {
                field,
                expected: expected.to_owned(),
                actual: actual.to_owned(),
            },
        ))
    }
}

fn validate_hash_match(
    field: LocalLemmaLifecycleIdentityField,
    expected: Hash,
    actual: Hash,
) -> Result<(), LocalLemmaLifecycleError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::HashMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

fn validate_state_match(
    field: LocalLemmaLifecycleIdentityField,
    expected: ProofAcceptanceState,
    actual: ProofAcceptanceState,
) -> Result<(), LocalLemmaLifecycleError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LocalLemmaLifecycleError::new(
            LocalLemmaLifecycleErrorKind::StateMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

fn validate_expected_local_lemma_verification_commands(
    handoff: &LocalLemmaProofTaskHandoff,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    let mut has_build_module = false;
    let mut has_verify_module = false;
    for command in &handoff.expected_verification_commands {
        validate_handoff_hash_match(
            LocalLemmaProofTaskHandoffField::VerificationCommandHash,
            local_lemma_expected_verification_command_hash(command),
            command.command_hash,
        )?;
        validate_handoff_identifier_match(
            LocalLemmaProofTaskHandoffField::TargetProofCorpusModule,
            &handoff.target_proof_corpus_module,
            &command.module,
        )?;
        if command.package_metadata {
            return Err(LocalLemmaProofTaskHandoffError::new(
                LocalLemmaProofTaskHandoffErrorKind::PackageMetadataNotAllowed {
                    kind: command.kind,
                },
            ));
        }
        match command.kind {
            LocalLemmaVerificationCommandKind::BuildModule => {
                has_build_module = true;
                if command.verified_cache_authoring {
                    return Err(LocalLemmaProofTaskHandoffError::new(
                        LocalLemmaProofTaskHandoffErrorKind::VerifiedCacheAuthoringNotAllowed {
                            kind: command.kind,
                        },
                    ));
                }
            }
            LocalLemmaVerificationCommandKind::VerifyModuleSourceFree => {
                has_verify_module = true;
                if !command.verified_cache_authoring {
                    return Err(LocalLemmaProofTaskHandoffError::new(
                        LocalLemmaProofTaskHandoffErrorKind::VerifiedCacheAuthoringRequired {
                            kind: command.kind,
                        },
                    ));
                }
            }
        }
    }
    if !has_build_module {
        return Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::MissingExpectedVerificationCommand {
                kind: LocalLemmaVerificationCommandKind::BuildModule,
            },
        ));
    }
    if !has_verify_module {
        return Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::MissingExpectedVerificationCommand {
                kind: LocalLemmaVerificationCommandKind::VerifyModuleSourceFree,
            },
        ));
    }
    Ok(())
}

fn local_lemma_task_identity_from_handoff(
    handoff: &LocalLemmaProofTaskHandoff,
) -> LocalLemmaProofTaskIdentity {
    let mut task_identity = LocalLemmaProofTaskIdentity {
        task_identity_hash: [0; 32],
        statement_hash: handoff.statement_hash,
        expected_type_hash: handoff.expected_type_hash,
        environment_hash: handoff.environment_hash,
        policy_hash: handoff.axiom_policy_hash,
        available_dependency_identities: handoff.dependency_identities.clone(),
    };
    task_identity.task_identity_hash = local_lemma_proof_task_identity_hash(&task_identity);
    task_identity
}

fn validate_local_lemma_verified_artifact_record_inner(
    handoff: &LocalLemmaProofTaskHandoff,
    artifact: &LocalLemmaVerifiedArtifactRecord,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::Module,
        &artifact.module,
    )?;
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::DeclarationName,
        &artifact.declaration_name,
    )?;
    validate_non_empty_handoff_identifier(
        LocalLemmaProofTaskHandoffField::ReplayPath,
        &artifact.replay_path,
    )?;
    validate_handoff_identifier_match(
        LocalLemmaProofTaskHandoffField::Module,
        &handoff.module,
        &artifact.module,
    )?;
    validate_handoff_identifier_match(
        LocalLemmaProofTaskHandoffField::DeclarationName,
        &handoff.declaration_name,
        &artifact.declaration_name,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::StatementHash,
        handoff.statement_hash,
        artifact.statement_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::VerificationCommandHash,
        local_lemma_task_identity_from_handoff(handoff).task_identity_hash,
        artifact.task_identity_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::AxiomSummaryHash,
        local_lemma_axiom_summary_hash(&artifact.axiom_summary),
        artifact.axiom_summary_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::ArtifactRecordHash,
        local_lemma_verified_artifact_record_hash(artifact),
        artifact.artifact_record_hash,
    )?;
    validate_source_free_verifier_result(&artifact.source_free_verifier_result)
        .map_err(local_lemma_handoff_lifecycle_error)?;
    let identity = local_lemma_verified_artifact_identity(handoff, artifact)?;
    let identity_hash = identity.hash();
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::SourceFreeVerifierResultHash,
        identity_hash,
        artifact
            .source_free_verifier_result
            .proof_artifact_identity_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::VerificationCommandHash,
        artifact.task_identity_hash,
        artifact.source_free_verifier_result.task_identity_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::StatementHash,
        handoff.statement_hash,
        artifact.source_free_verifier_result.statement_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::EnvironmentHash,
        handoff.environment_hash,
        artifact.source_free_verifier_result.environment_hash,
    )?;
    validate_handoff_hash_match(
        LocalLemmaProofTaskHandoffField::AxiomPolicyHash,
        handoff.axiom_policy_hash,
        artifact.source_free_verifier_result.policy_hash,
    )?;
    Ok(())
}

fn local_lemma_verified_artifact_identity(
    handoff: &LocalLemmaProofTaskHandoff,
    artifact: &LocalLemmaVerifiedArtifactRecord,
) -> Result<VerifiedArtifactIdentity, LocalLemmaProofTaskHandoffError> {
    let identity = VerifiedArtifactIdentity {
        state: artifact.source_free_verifier_result.status,
        candidate_hash: handoff.handoff_hash,
        statement_hash: handoff.statement_hash,
        certificate_hash: artifact.certificate_hash,
        export_hash: artifact.export_hash,
        axiom_report_hash: artifact.axiom_summary_hash,
        package_manifest_hash: None,
        package_lock_hash: None,
        verifier_profile: None,
        verifier_binary_hash: None,
        verifier_version_or_build_hash: None,
        release_evidence_kind: None,
        release_evidence_hash: None,
    };
    validate_verified_artifact_identity(&identity).map_err(|error| {
        LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::VerifiedArtifactIdentityInvalid {
                error_kind: error.kind(),
            },
        )
    })?;
    Ok(identity)
}

fn local_lemma_handoff_lifecycle_error(
    error: LocalLemmaLifecycleError,
) -> LocalLemmaProofTaskHandoffError {
    LocalLemmaProofTaskHandoffError::new(LocalLemmaProofTaskHandoffErrorKind::Lifecycle {
        error_kind: error.kind.as_str(),
    })
}

fn validate_theorem_invention_verification_commands(
    artifact: &TheoremInventionArtifact,
) -> Result<(), TheoremInventionArtifactError> {
    let mut has_build_module = false;
    let mut has_verify_module = false;
    for command in &artifact.verification_commands {
        validate_theorem_invention_hash_match(
            TheoremInventionArtifactField::VerificationCommandHash,
            theorem_invention_verification_command_hash(command),
            command.command_hash,
        )?;
        validate_theorem_invention_identifier_match(
            TheoremInventionArtifactField::TargetProofCorpusModule,
            &artifact.target_proof_corpus_module,
            &command.module,
        )?;
        if command.package_metadata {
            return Err(TheoremInventionArtifactError::new(
                TheoremInventionArtifactErrorKind::PackageMetadataNotAllowed { kind: command.kind },
            ));
        }
        match command.kind {
            TheoremInventionVerificationCommandKind::BuildModule => {
                has_build_module = true;
                if command.verified_cache_authoring {
                    return Err(TheoremInventionArtifactError::new(
                        TheoremInventionArtifactErrorKind::VerifiedCacheAuthoringNotAllowed {
                            kind: command.kind,
                        },
                    ));
                }
            }
            TheoremInventionVerificationCommandKind::VerifyModuleSourceFree => {
                has_verify_module = true;
                if !command.verified_cache_authoring {
                    return Err(TheoremInventionArtifactError::new(
                        TheoremInventionArtifactErrorKind::VerifiedCacheAuthoringRequired {
                            kind: command.kind,
                        },
                    ));
                }
            }
        }
    }
    if !has_build_module {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::MissingExpectedVerificationCommand {
                kind: TheoremInventionVerificationCommandKind::BuildModule,
            },
        ));
    }
    if !has_verify_module {
        return Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::MissingExpectedVerificationCommand {
                kind: TheoremInventionVerificationCommandKind::VerifyModuleSourceFree,
            },
        ));
    }
    Ok(())
}

fn validate_invented_candidate_typecheck_request_shape(
    request: &InventedCandidateTypecheckRequest,
) -> Result<(), InventedCandidateTypecheckError> {
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::CandidateId,
        &request.candidate_id,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::SourceModule,
        &request.source_module,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::TargetProofCorpusModule,
        &request.target_proof_corpus_module,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::DeclarationName,
        &request.declaration_name,
    )?;
    validate_non_empty_invented_candidate_identifier(
        InventedCandidateTypecheckField::NormalizedStatement,
        &request.normalized_statement,
    )?;
    for import in &request.import_identities {
        validate_non_empty_invented_candidate_identifier(
            InventedCandidateTypecheckField::ImportModule,
            &import.module,
        )?;
    }
    for module in &request.required_import_modules {
        validate_non_empty_invented_candidate_identifier(
            InventedCandidateTypecheckField::ImportModule,
            module,
        )?;
    }
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::GeneralizedContextHash,
        theorem_invention_generalized_context_hash(&request.generalized_context),
        request.generalized_context.context_hash,
    )?;
    if let Some(witness) = request.typecheck_witness.as_ref() {
        validate_non_empty_invented_candidate_identifier(
            InventedCandidateTypecheckField::TargetProofCorpusModule,
            &witness.target_proof_corpus_module,
        )?;
        validate_invented_candidate_hash_match(
            InventedCandidateTypecheckField::WitnessHash,
            invented_candidate_typecheck_witness_hash(witness),
            witness.witness_hash,
        )?;
    }
    validate_invented_candidate_hash_match(
        InventedCandidateTypecheckField::RequestHash,
        invented_candidate_typecheck_request_hash(request),
        request.request_hash,
    )
}

fn validate_invented_candidate_authoring_commands(
    commands: &[TheoremInventionVerificationCommand],
    target_proof_corpus_module: &str,
) -> Result<(), InventedCandidateTypecheckError> {
    let mut has_build_module = false;
    let mut has_verify_module = false;
    for command in commands {
        validate_invented_candidate_hash_match(
            InventedCandidateTypecheckField::VerificationCommandHash,
            theorem_invention_verification_command_hash(command),
            command.command_hash,
        )?;
        validate_invented_candidate_identifier_match(
            InventedCandidateTypecheckField::TargetProofCorpusModule,
            target_proof_corpus_module,
            &command.module,
        )?;
        if command.package_metadata {
            return Err(InventedCandidateTypecheckError::new(
                InventedCandidateTypecheckErrorKind::PackageMetadataNotAllowed {
                    kind: command.kind,
                },
            ));
        }
        match command.kind {
            TheoremInventionVerificationCommandKind::BuildModule => {
                has_build_module = true;
                if command.verified_cache_authoring {
                    return Err(InventedCandidateTypecheckError::new(
                        InventedCandidateTypecheckErrorKind::VerifiedCacheAuthoringNotAllowed {
                            kind: command.kind,
                        },
                    ));
                }
            }
            TheoremInventionVerificationCommandKind::VerifyModuleSourceFree => {
                has_verify_module = true;
                if !command.verified_cache_authoring {
                    return Err(InventedCandidateTypecheckError::new(
                        InventedCandidateTypecheckErrorKind::VerifiedCacheAuthoringRequired {
                            kind: command.kind,
                        },
                    ));
                }
            }
        }
    }
    if !has_build_module {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::MissingExpectedVerificationCommand {
                kind: TheoremInventionVerificationCommandKind::BuildModule,
            },
        ));
    }
    if !has_verify_module {
        return Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::MissingExpectedVerificationCommand {
                kind: TheoremInventionVerificationCommandKind::VerifyModuleSourceFree,
            },
        ));
    }
    Ok(())
}

fn invented_candidate_missing_required_import(
    request: &InventedCandidateTypecheckRequest,
) -> Option<&str> {
    let mut available = request
        .import_identities
        .iter()
        .map(|import| import.module.as_str())
        .collect::<Vec<_>>();
    available.sort();
    available.dedup();
    request
        .required_import_modules
        .iter()
        .map(String::as_str)
        .find(|module| available.binary_search(module).is_err())
}

fn invented_candidate_typecheck_blocker(
    request: &InventedCandidateTypecheckRequest,
    reason: InventedCandidateTypecheckBlockerReason,
    evidence_hash: Option<Hash>,
) -> InventedCandidateTypecheckBlocker {
    let mut blocker = InventedCandidateTypecheckBlocker {
        blocker_hash: [0; 32],
        request_hash: request.request_hash,
        candidate_id: request.candidate_id.clone(),
        target_proof_corpus_module: request.target_proof_corpus_module.clone(),
        declaration_name: request.declaration_name.clone(),
        statement_hash: request.statement_hash,
        reason,
        evidence_hash,
        unproved_storage_kind: LocalLemmaUnprovedStorageKind::SketchSidecar,
        creates_theorem_declaration: false,
    };
    blocker.blocker_hash = invented_candidate_typecheck_blocker_hash(&blocker);
    blocker
}

fn validate_non_empty_invented_candidate_identifier(
    field: InventedCandidateTypecheckField,
    value: &str,
) -> Result<(), InventedCandidateTypecheckError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::EmptyIdentifier { field },
        ))
    } else {
        Ok(())
    }
}

fn validate_invented_candidate_identifier_match(
    field: InventedCandidateTypecheckField,
    expected: &str,
    actual: &str,
) -> Result<(), InventedCandidateTypecheckError> {
    if expected == actual {
        Ok(())
    } else {
        Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::IdentifierMismatch {
                field,
                expected: expected.to_owned(),
                actual: actual.to_owned(),
            },
        ))
    }
}

fn validate_invented_candidate_hash_match(
    field: InventedCandidateTypecheckField,
    expected: Hash,
    actual: Hash,
) -> Result<(), InventedCandidateTypecheckError> {
    if expected == actual {
        Ok(())
    } else {
        Err(InventedCandidateTypecheckError::new(
            InventedCandidateTypecheckErrorKind::HashMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

fn validate_invented_lemma_proof_task_shape(
    handoff: &InventedLemmaProofTaskHandoff,
) -> Result<(), InventedLemmaProofTaskError> {
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::CandidateId,
        &handoff.candidate_id,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::SourceModule,
        &handoff.source_module,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::TargetProofCorpusModule,
        &handoff.target_proof_corpus_module,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::DeclarationName,
        &handoff.declaration_name,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::TheoremStatement,
        &handoff.theorem_statement,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::SourcePath,
        &handoff.source_path,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::CertificatePath,
        &handoff.certificate_path,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::MetaPath,
        &handoff.meta_path,
    )?;
    validate_non_empty_invented_lemma_identifier(
        InventedLemmaProofTaskField::ReplayPath,
        &handoff.replay_path,
    )
}

fn validate_invented_lemma_authoring_commands(
    commands: &[InventedLemmaAuthoringCommand],
    target_proof_corpus_module: &str,
) -> Result<(), InventedLemmaProofTaskError> {
    let expected = invented_lemma_expected_authoring_commands(target_proof_corpus_module);
    if commands.len() != expected.len() {
        return Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::UnexpectedAuthoringCommandCount {
                expected: expected.len(),
                actual: commands.len(),
            },
        ));
    }
    for (index, (command, expected_command)) in commands.iter().zip(expected.iter()).enumerate() {
        if command.kind != expected_command.kind {
            return Err(InventedLemmaProofTaskError::new(
                InventedLemmaProofTaskErrorKind::AuthoringCommandKindMismatch {
                    index,
                    expected: expected_command.kind,
                    actual: command.kind,
                },
            ));
        }
        validate_invented_lemma_hash_match(
            InventedLemmaProofTaskField::AuthoringCommandHash,
            invented_lemma_authoring_command_hash(command),
            command.command_hash,
        )?;
        validate_invented_lemma_hash_match(
            InventedLemmaProofTaskField::AuthoringCommandHash,
            expected_command.command_hash,
            command.command_hash,
        )?;
        if command.package_metadata {
            return Err(InventedLemmaProofTaskError::new(
                InventedLemmaProofTaskErrorKind::PackageMetadataNotAllowed { kind: command.kind },
            ));
        }
        match command.kind {
            InventedLemmaAuthoringCommandKind::BuildModule => {
                validate_invented_lemma_command_module(command, target_proof_corpus_module, true)?;
                if command.verified_cache_authoring {
                    return Err(InventedLemmaProofTaskError::new(
                        InventedLemmaProofTaskErrorKind::VerifiedCacheAuthoringNotAllowed {
                            kind: command.kind,
                        },
                    ));
                }
            }
            InventedLemmaAuthoringCommandKind::VerifyModuleSourceFree => {
                validate_invented_lemma_command_module(command, target_proof_corpus_module, true)?;
                if !command.verified_cache_authoring {
                    return Err(InventedLemmaProofTaskError::new(
                        InventedLemmaProofTaskErrorKind::VerifiedCacheAuthoringRequired {
                            kind: command.kind,
                        },
                    ));
                }
            }
            InventedLemmaAuthoringCommandKind::VerifyChangedOnlySourceFree => {
                validate_invented_lemma_command_module(command, target_proof_corpus_module, false)?;
                if !command.verified_cache_authoring {
                    return Err(InventedLemmaProofTaskError::new(
                        InventedLemmaProofTaskErrorKind::VerifiedCacheAuthoringRequired {
                            kind: command.kind,
                        },
                    ));
                }
            }
            InventedLemmaAuthoringCommandKind::CheckCorpusAuthoring => {
                validate_invented_lemma_command_module(command, target_proof_corpus_module, false)?;
                if !command.verified_cache_authoring {
                    return Err(InventedLemmaProofTaskError::new(
                        InventedLemmaProofTaskErrorKind::VerifiedCacheAuthoringRequired {
                            kind: command.kind,
                        },
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_invented_lemma_command_module(
    command: &InventedLemmaAuthoringCommand,
    target_proof_corpus_module: &str,
    module_required: bool,
) -> Result<(), InventedLemmaProofTaskError> {
    match (module_required, command.module.as_deref()) {
        (true, Some(module)) => validate_invented_lemma_identifier_match(
            InventedLemmaProofTaskField::TargetProofCorpusModule,
            target_proof_corpus_module,
            module,
        ),
        (true, None) => Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::CommandModuleRequired { kind: command.kind },
        )),
        (false, Some(_)) => Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::CommandModuleNotAllowed { kind: command.kind },
        )),
        (false, None) => Ok(()),
    }
}

fn validate_invented_lemma_package_side_effect_policy(
    policy: &InventedLemmaPackageSideEffectPolicy,
) -> Result<(), InventedLemmaProofTaskError> {
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::PackageSideEffectPolicyHash,
        invented_lemma_package_side_effect_policy_hash(policy),
        policy.policy_hash,
    )?;
    for (updated, field) in [
        (
            policy.package_lock_updated,
            InventedLemmaProofTaskField::PackageLockUpdated,
        ),
        (
            policy.package_theorem_index_updated,
            InventedLemmaProofTaskField::PackageTheoremIndexUpdated,
        ),
        (
            policy.axiom_report_updated,
            InventedLemmaProofTaskField::AxiomReportUpdated,
        ),
        (
            policy.publish_plan_updated,
            InventedLemmaProofTaskField::PublishPlanUpdated,
        ),
    ] {
        if updated {
            return Err(InventedLemmaProofTaskError::new(
                InventedLemmaProofTaskErrorKind::PackageSideEffectNotAllowed { field },
            ));
        }
    }
    Ok(())
}

fn validate_invented_lemma_artifact_readiness(
    readiness: &InventedLemmaArtifactReadiness,
) -> Result<(), InventedLemmaProofTaskError> {
    validate_invented_lemma_hash_match(
        InventedLemmaProofTaskField::ReadinessHash,
        invented_lemma_artifact_readiness_hash(readiness),
        readiness.readiness_hash,
    )?;
    if !readiness.theorem_level.is_l2_derived_certificate() {
        return Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::NonL2Artifact {
                theorem_level: readiness.theorem_level,
            },
        ));
    }
    for (ready, field) in [
        (
            readiness.source_exists,
            InventedLemmaProofTaskField::SourceArtifact,
        ),
        (
            readiness.certificate_exists,
            InventedLemmaProofTaskField::CertificateArtifact,
        ),
        (
            readiness.meta_exists,
            InventedLemmaProofTaskField::MetaArtifact,
        ),
        (
            readiness.replay_exists,
            InventedLemmaProofTaskField::ReplayArtifact,
        ),
        (
            readiness.source_free_verified,
            InventedLemmaProofTaskField::SourceFreeVerifierResultStatus,
        ),
    ] {
        if !ready {
            return Err(InventedLemmaProofTaskError::new(
                InventedLemmaProofTaskErrorKind::ArtifactNotReady { field },
            ));
        }
    }
    Ok(())
}

fn invented_lemma_local_proof_task_handoff_unchecked(
    handoff: &InventedLemmaProofTaskHandoff,
) -> LocalLemmaProofTaskHandoff {
    LocalLemmaProofTaskHandoff {
        handoff_hash: handoff.local_lemma_handoff_hash,
        lemma_id: handoff.candidate_id.clone(),
        sketch_hash: handoff.typecheck_handoff_hash,
        sketch_node_id: handoff.candidate_id.clone(),
        module: handoff.target_proof_corpus_module.clone(),
        declaration_name: handoff.declaration_name.clone(),
        statement_hash: handoff.statement_hash,
        expected_type_hash: handoff.expected_type_hash,
        environment_hash: handoff.environment_hash,
        axiom_policy_hash: handoff.axiom_policy_hash,
        generalized_context: invented_lemma_local_generalized_context(&handoff.generalized_context),
        dependency_identities: handoff.dependency_identities.clone(),
        target_proof_corpus_module: handoff.target_proof_corpus_module.clone(),
        expected_verification_commands: invented_lemma_local_verification_commands(
            &handoff.target_proof_corpus_module,
        ),
        unproved_storage_kind: LocalLemmaUnprovedStorageKind::TaskSidecar,
    }
}

fn invented_lemma_local_type_checked(
    handoff: &InventedLemmaProofTaskHandoff,
) -> LocalLemmaTypeChecked {
    LocalLemmaTypeChecked {
        lemma_id: handoff.candidate_id.clone(),
        sketch_hash: handoff.typecheck_handoff_hash,
        sketch_node_id: handoff.candidate_id.clone(),
        statement_hash: handoff.statement_hash,
        expected_type_hash: handoff.expected_type_hash,
        environment_hash: handoff.environment_hash,
        policy_hash: handoff.axiom_policy_hash,
    }
}

fn invented_lemma_local_generalized_context(
    context: &TheoremInventionGeneralizedContext,
) -> LocalLemmaGeneralizedContext {
    let mut local = LocalLemmaGeneralizedContext {
        context_hash: [0; 32],
        binders: context
            .binders
            .iter()
            .map(|binder| LocalLemmaGeneralizedContextBinder {
                binder_id: binder.binder_id.clone(),
                type_hash: binder.type_hash,
                dependency_hashes: binder.dependency_hashes.clone(),
            })
            .collect(),
    };
    local.context_hash = local_lemma_generalized_context_hash(&local);
    local
}

fn invented_lemma_local_verification_commands(
    target_proof_corpus_module: &str,
) -> Vec<LocalLemmaExpectedVerificationCommand> {
    [
        LocalLemmaVerificationCommandKind::BuildModule,
        LocalLemmaVerificationCommandKind::VerifyModuleSourceFree,
    ]
    .into_iter()
    .map(|kind| {
        let mut command = LocalLemmaExpectedVerificationCommand {
            command_hash: [0; 32],
            kind,
            module: target_proof_corpus_module.to_owned(),
            verified_cache_authoring: kind
                == LocalLemmaVerificationCommandKind::VerifyModuleSourceFree,
            package_metadata: false,
        };
        command.command_hash = local_lemma_expected_verification_command_hash(&command);
        command
    })
    .collect()
}

fn validate_non_empty_invented_lemma_identifier(
    field: InventedLemmaProofTaskField,
    value: &str,
) -> Result<(), InventedLemmaProofTaskError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::EmptyIdentifier { field },
        ))
    } else {
        Ok(())
    }
}

fn validate_invented_lemma_identifier_match(
    field: InventedLemmaProofTaskField,
    expected: &str,
    actual: &str,
) -> Result<(), InventedLemmaProofTaskError> {
    if expected == actual {
        Ok(())
    } else {
        Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::IdentifierMismatch {
                field,
                expected: expected.to_owned(),
                actual: actual.to_owned(),
            },
        ))
    }
}

fn validate_invented_lemma_hash_match(
    field: InventedLemmaProofTaskField,
    expected: Hash,
    actual: Hash,
) -> Result<(), InventedLemmaProofTaskError> {
    if expected == actual {
        Ok(())
    } else {
        Err(InventedLemmaProofTaskError::new(
            InventedLemmaProofTaskErrorKind::HashMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

fn validate_non_empty_theorem_invention_identifier(
    field: TheoremInventionArtifactField,
    value: &str,
) -> Result<(), TheoremInventionArtifactError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::EmptyIdentifier { field },
        ))
    } else {
        Ok(())
    }
}

fn validate_theorem_invention_identifier_match(
    field: TheoremInventionArtifactField,
    expected: &str,
    actual: &str,
) -> Result<(), TheoremInventionArtifactError> {
    if expected == actual {
        Ok(())
    } else {
        Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::IdentifierMismatch {
                field,
                expected: expected.to_owned(),
                actual: actual.to_owned(),
            },
        ))
    }
}

fn validate_theorem_invention_hash_match(
    field: TheoremInventionArtifactField,
    expected: Hash,
    actual: Hash,
) -> Result<(), TheoremInventionArtifactError> {
    if expected == actual {
        Ok(())
    } else {
        Err(TheoremInventionArtifactError::new(
            TheoremInventionArtifactErrorKind::HashMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

fn validate_non_empty_handoff_identifier(
    field: LocalLemmaProofTaskHandoffField,
    value: &str,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::EmptyIdentifier { field },
        ))
    } else {
        Ok(())
    }
}

fn validate_handoff_identifier_match(
    field: LocalLemmaProofTaskHandoffField,
    expected: &str,
    actual: &str,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::IdentifierMismatch {
                field,
                expected: expected.to_owned(),
                actual: actual.to_owned(),
            },
        ))
    }
}

fn validate_handoff_hash_match(
    field: LocalLemmaProofTaskHandoffField,
    expected: Hash,
    actual: Hash,
) -> Result<(), LocalLemmaProofTaskHandoffError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LocalLemmaProofTaskHandoffError::new(
            LocalLemmaProofTaskHandoffErrorKind::HashMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

pub fn proof_candidate_goal_fingerprint(state_fingerprint: Hash, goal_id: GoalId) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.proof-candidate.goal-fingerprint.v1");
    encode_hash(&mut out, &state_fingerprint);
    out.extend(goal_id_canonical_bytes(goal_id));
    sha256(&out)
}

pub fn proof_candidate_import_closure_hash(context: &MachineImportCertificateContext) -> Hash {
    let mut direct_imports = context
        .direct_import_keys()
        .iter()
        .map(|key| name_canonical_bytes(&key.module))
        .collect::<Vec<_>>();
    direct_imports.sort();

    let mut entries = context
        .verified_modules()
        .iter()
        .map(|entry| {
            let mut out = Vec::new();
            encode_name(&mut out, &entry.key.module);

            let mut import_modules = entry
                .certificate_import_table
                .iter()
                .map(|key| name_canonical_bytes(&key.module))
                .collect::<Vec<_>>();
            import_modules.sort();
            encode_uvar(&mut out, import_modules.len() as u64);
            for import in import_modules {
                encode_uvar(&mut out, import.len() as u64);
                out.extend(import);
            }

            encode_uvar(&mut out, entry.decl_index_table.len() as u64);
            for decl in &entry.decl_index_table {
                encode_uvar(&mut out, decl.decl_index as u64);
                encode_name(&mut out, &decl.name);
                encode_hash(&mut out, &decl.hashes.decl_interface_hash);
            }

            let mut generated = entry.generated_decl_table.iter().collect::<Vec<_>>();
            generated.sort_by(|left, right| {
                left.parent_decl_index
                    .cmp(&right.parent_decl_index)
                    .then_with(|| {
                        name_canonical_bytes(&left.name).cmp(&name_canonical_bytes(&right.name))
                    })
                    .then_with(|| {
                        generated_decl_kind_tag(left.kind).cmp(&generated_decl_kind_tag(right.kind))
                    })
            });
            encode_uvar(&mut out, generated.len() as u64);
            for generated in generated {
                encode_uvar(&mut out, generated.parent_decl_index as u64);
                encode_name(&mut out, &generated.name);
                out.push(generated_decl_kind_tag(generated.kind));
                encode_hash(&mut out, &generated.export.decl_interface_hash);
            }

            encode_uvar(&mut out, entry.export_block.len() as u64);
            for export in &entry.export_block {
                let export_name = entry
                    .decoded_name_table
                    .get(export.name)
                    .expect("verified export names are decoded in the import context");
                encode_name(&mut out, export_name);
                out.push(export_kind_tag(export.kind));
                encode_uvar(&mut out, export.universe_params.len() as u64);
                for param in &export.universe_params {
                    let param_name = entry.decoded_name_table.get(*param).expect(
                        "verified export universe params are decoded in the import context",
                    );
                    encode_name(&mut out, param_name);
                }
                encode_hash(&mut out, &export.type_hash);
                encode_option_hash(&mut out, export.body_hash.as_ref());
                encode_option_reducibility(&mut out, export.reducibility);
                encode_option_opacity(&mut out, export.opacity);
                encode_hash(&mut out, &export.decl_interface_hash);
            }

            encode_uvar(&mut out, entry.decoded_name_table.len() as u64);
            for name in &entry.decoded_name_table {
                encode_name(&mut out, name);
            }
            out
        })
        .collect::<Vec<_>>();
    entries.sort();

    let mut out = Vec::new();
    encode_string(&mut out, "npa.proof-candidate.import-closure.v1");
    encode_uvar(&mut out, direct_imports.len() as u64);
    for import in direct_imports {
        encode_uvar(&mut out, import.len() as u64);
        out.extend(import);
    }
    encode_uvar(&mut out, entries.len() as u64);
    for entry in entries {
        encode_uvar(&mut out, entry.len() as u64);
        out.extend(entry);
    }
    sha256(&out)
}

pub fn proof_candidate_axiom_policy_hash(allow_axioms: &[MachineAxiomRefWire]) -> Hash {
    let mut entries = allow_axioms
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect::<Vec<_>>();
    entries.sort();
    entries.dedup();

    let mut out = Vec::new();
    encode_string(&mut out, "npa.proof-candidate.machine-axiom-policy.v1");
    encode_uvar(&mut out, entries.len() as u64);
    for entry in entries {
        encode_uvar(&mut out, entry.len() as u64);
        out.extend(entry);
    }
    sha256(&out)
}

pub fn proof_candidate_feature_profile_hash(
    kernel_check_profile: KernelCheckProfileId,
    tactic_options_fingerprint: Hash,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.proof-candidate.machine-feature-profile.v1");
    encode_string(&mut out, kernel_check_profile.as_str());
    encode_hash(&mut out, &tactic_options_fingerprint);
    sha256(&out)
}

pub fn proof_candidate_environment_hash(
    import_closure_hash: Hash,
    axiom_policy_hash: Hash,
    feature_profile_hash: Hash,
    statement_hash: Hash,
) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, "npa.proof-candidate.environment.v1");
    encode_hash(&mut out, &import_closure_hash);
    encode_hash(&mut out, &axiom_policy_hash);
    encode_hash(&mut out, &feature_profile_hash);
    encode_hash(&mut out, &statement_hash);
    sha256(&out)
}

pub const PROOF_ACCEPTANCE_TRANSITION_EDGES: [ProofAcceptanceTransitionEdge; 9] = [
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::Proposed,
        to_state: ProofAcceptanceState::Parsed,
        actor_role: ProofAcceptanceActorRole::AgentWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::Parsed,
        to_state: ProofAcceptanceState::TypeChecked,
        actor_role: ProofAcceptanceActorRole::AgentWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::TypeChecked,
        to_state: ProofAcceptanceState::ProofCandidate,
        actor_role: ProofAcceptanceActorRole::AgentWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::ProofCandidate,
        to_state: ProofAcceptanceState::ReplayVerified,
        actor_role: ProofAcceptanceActorRole::VerifierWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::ReplayVerified,
        to_state: ProofAcceptanceState::CertificateGenerated,
        actor_role: ProofAcceptanceActorRole::VerifierWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::CertificateGenerated,
        to_state: ProofAcceptanceState::CertificateVerified,
        actor_role: ProofAcceptanceActorRole::VerifierWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::CertificateVerified,
        to_state: ProofAcceptanceState::IndependentVerified,
        actor_role: ProofAcceptanceActorRole::VerifierWorker,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::IndependentVerified,
        to_state: ProofAcceptanceState::Integrated,
        actor_role: ProofAcceptanceActorRole::Integrator,
    },
    ProofAcceptanceTransitionEdge {
        from_state: ProofAcceptanceState::Integrated,
        to_state: ProofAcceptanceState::Published,
        actor_role: ProofAcceptanceActorRole::ReleaseController,
    },
];

pub const PROOF_TRUST_COMPONENTS: [ProofTrustComponent; 29] = [
    ProofTrustComponent::RustKernel,
    ProofTrustComponent::CanonicalCoreAst,
    ProofTrustComponent::CanonicalCertificate,
    ProofTrustComponent::CertificateVerifier,
    ProofTrustComponent::DesignatedIndependentChecker,
    ProofTrustComponent::DeterministicHashCheck,
    ProofTrustComponent::AxiomPolicyCheck,
    ProofTrustComponent::CoreFeatureCheck,
    ProofTrustComponent::Parser,
    ProofTrustComponent::Elaborator,
    ProofTrustComponent::Tactic,
    ProofTrustComponent::Automation,
    ProofTrustComponent::Plugin,
    ProofTrustComponent::AiModel,
    ProofTrustComponent::AgentWorker,
    ProofTrustComponent::TheoremSearch,
    ProofTrustComponent::PremiseRetrieval,
    ProofTrustComponent::SearchScore,
    ProofTrustComponent::TheoremGraphScore,
    ProofTrustComponent::Prompt,
    ProofTrustComponent::ModelOutput,
    ProofTrustComponent::ReplayLog,
    ProofTrustComponent::ReplaySidecar,
    ProofTrustComponent::TheoremIndex,
    ProofTrustComponent::SidecarIndex,
    ProofTrustComponent::Cache,
    ProofTrustComponent::SolverProcess,
    ProofTrustComponent::Diagnostic,
    ProofTrustComponent::BenchmarkSummary,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofTrustClassification {
    Trusted,
    DeterministicValidation,
    UntrustedSidecar,
}

impl ProofTrustClassification {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Trusted => "trusted",
            Self::DeterministicValidation => "deterministic_validation",
            Self::UntrustedSidecar => "untrusted_sidecar",
        }
    }

    pub fn parse(value: &str) -> Result<Self, ProofTrustClassificationParseError> {
        match value {
            "trusted" => Ok(Self::Trusted),
            "deterministic_validation" => Ok(Self::DeterministicValidation),
            "untrusted_sidecar" => Ok(Self::UntrustedSidecar),
            _ => Err(ProofTrustClassificationParseError {
                value: value.to_owned(),
            }),
        }
    }
}

impl FromStr for ProofTrustClassification {
    type Err = ProofTrustClassificationParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::parse(value)
    }
}

impl fmt::Display for ProofTrustClassification {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofTrustClassificationParseError {
    value: String,
}

impl ProofTrustClassificationParseError {
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl fmt::Display for ProofTrustClassificationParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unknown proof trust classification wire string {:?}",
            self.value
        )
    }
}

impl std::error::Error for ProofTrustClassificationParseError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofTrustContractSurface {
    Candidate,
    Verification,
    Integration,
}

impl ProofTrustContractSurface {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Candidate => "candidate",
            Self::Verification => "verification",
            Self::Integration => "integration",
        }
    }
}

impl fmt::Display for ProofTrustContractSurface {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofTrustComponent {
    RustKernel,
    CanonicalCoreAst,
    CanonicalCertificate,
    CertificateVerifier,
    DesignatedIndependentChecker,
    DeterministicHashCheck,
    AxiomPolicyCheck,
    CoreFeatureCheck,
    Parser,
    Elaborator,
    Tactic,
    Automation,
    Plugin,
    AiModel,
    AgentWorker,
    TheoremSearch,
    PremiseRetrieval,
    SearchScore,
    TheoremGraphScore,
    Prompt,
    ModelOutput,
    ReplayLog,
    ReplaySidecar,
    TheoremIndex,
    SidecarIndex,
    Cache,
    SolverProcess,
    Diagnostic,
    BenchmarkSummary,
}

impl ProofTrustComponent {
    pub const fn all() -> &'static [Self] {
        &PROOF_TRUST_COMPONENTS
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RustKernel => "rust_kernel",
            Self::CanonicalCoreAst => "canonical_core_ast",
            Self::CanonicalCertificate => "canonical_certificate",
            Self::CertificateVerifier => "certificate_verifier",
            Self::DesignatedIndependentChecker => "designated_independent_checker",
            Self::DeterministicHashCheck => "deterministic_hash_check",
            Self::AxiomPolicyCheck => "axiom_policy_check",
            Self::CoreFeatureCheck => "core_feature_check",
            Self::Parser => "parser",
            Self::Elaborator => "elaborator",
            Self::Tactic => "tactic",
            Self::Automation => "automation",
            Self::Plugin => "plugin",
            Self::AiModel => "ai_model",
            Self::AgentWorker => "agent_worker",
            Self::TheoremSearch => "theorem_search",
            Self::PremiseRetrieval => "premise_retrieval",
            Self::SearchScore => "search_score",
            Self::TheoremGraphScore => "theorem_graph_score",
            Self::Prompt => "prompt",
            Self::ModelOutput => "model_output",
            Self::ReplayLog => "replay_log",
            Self::ReplaySidecar => "replay_sidecar",
            Self::TheoremIndex => "theorem_index",
            Self::SidecarIndex => "sidecar_index",
            Self::Cache => "cache",
            Self::SolverProcess => "solver_process",
            Self::Diagnostic => "diagnostic",
            Self::BenchmarkSummary => "benchmark_summary",
        }
    }

    pub const fn classification(self) -> ProofTrustClassification {
        match self {
            Self::RustKernel
            | Self::CanonicalCoreAst
            | Self::CanonicalCertificate
            | Self::CertificateVerifier
            | Self::DesignatedIndependentChecker => ProofTrustClassification::Trusted,
            Self::DeterministicHashCheck | Self::AxiomPolicyCheck | Self::CoreFeatureCheck => {
                ProofTrustClassification::DeterministicValidation
            }
            Self::Parser
            | Self::Elaborator
            | Self::Tactic
            | Self::Automation
            | Self::Plugin
            | Self::AiModel
            | Self::AgentWorker
            | Self::TheoremSearch
            | Self::PremiseRetrieval
            | Self::SearchScore
            | Self::TheoremGraphScore
            | Self::Prompt
            | Self::ModelOutput
            | Self::ReplayLog
            | Self::ReplaySidecar
            | Self::TheoremIndex
            | Self::SidecarIndex
            | Self::Cache
            | Self::SolverProcess
            | Self::Diagnostic
            | Self::BenchmarkSummary => ProofTrustClassification::UntrustedSidecar,
        }
    }

    pub const fn may_serialize_as_trusted_evidence(self) -> bool {
        match self.classification() {
            ProofTrustClassification::Trusted
            | ProofTrustClassification::DeterministicValidation => true,
            ProofTrustClassification::UntrustedSidecar => false,
        }
    }

    pub const fn may_claim_verified_state_on(self, surface: ProofTrustContractSurface) -> bool {
        match surface {
            ProofTrustContractSurface::Candidate => false,
            ProofTrustContractSurface::Verification | ProofTrustContractSurface::Integration => {
                self.may_serialize_as_trusted_evidence()
            }
        }
    }

    pub fn parse(value: &str) -> Result<Self, ProofTrustComponentParseError> {
        match value {
            "rust_kernel" => Ok(Self::RustKernel),
            "canonical_core_ast" => Ok(Self::CanonicalCoreAst),
            "canonical_certificate" => Ok(Self::CanonicalCertificate),
            "certificate_verifier" => Ok(Self::CertificateVerifier),
            "designated_independent_checker" => Ok(Self::DesignatedIndependentChecker),
            "deterministic_hash_check" => Ok(Self::DeterministicHashCheck),
            "axiom_policy_check" => Ok(Self::AxiomPolicyCheck),
            "core_feature_check" => Ok(Self::CoreFeatureCheck),
            "parser" => Ok(Self::Parser),
            "elaborator" => Ok(Self::Elaborator),
            "tactic" => Ok(Self::Tactic),
            "automation" => Ok(Self::Automation),
            "plugin" => Ok(Self::Plugin),
            "ai_model" => Ok(Self::AiModel),
            "agent_worker" => Ok(Self::AgentWorker),
            "theorem_search" => Ok(Self::TheoremSearch),
            "premise_retrieval" => Ok(Self::PremiseRetrieval),
            "search_score" => Ok(Self::SearchScore),
            "theorem_graph_score" => Ok(Self::TheoremGraphScore),
            "prompt" => Ok(Self::Prompt),
            "model_output" => Ok(Self::ModelOutput),
            "replay_log" => Ok(Self::ReplayLog),
            "replay_sidecar" => Ok(Self::ReplaySidecar),
            "theorem_index" => Ok(Self::TheoremIndex),
            "sidecar_index" => Ok(Self::SidecarIndex),
            "cache" => Ok(Self::Cache),
            "solver_process" => Ok(Self::SolverProcess),
            "diagnostic" => Ok(Self::Diagnostic),
            "benchmark_summary" => Ok(Self::BenchmarkSummary),
            _ => Err(ProofTrustComponentParseError {
                value: value.to_owned(),
            }),
        }
    }
}

impl FromStr for ProofTrustComponent {
    type Err = ProofTrustComponentParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::parse(value)
    }
}

impl fmt::Display for ProofTrustComponent {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofTrustComponentParseError {
    value: String,
}

impl ProofTrustComponentParseError {
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl fmt::Display for ProofTrustComponentParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unknown proof trust component wire string {:?}",
            self.value
        )
    }
}

impl std::error::Error for ProofTrustComponentParseError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofAcceptanceActorRole {
    AgentWorker,
    VerifierWorker,
    Integrator,
    ReleaseController,
    HumanAdministrator,
}

impl ProofAcceptanceActorRole {
    /// Return the stable lower-case wire spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AgentWorker => "agent_worker",
            Self::VerifierWorker => "verifier_worker",
            Self::Integrator => "integrator",
            Self::ReleaseController => "release_controller",
            Self::HumanAdministrator => "human_administrator",
        }
    }

    /// Parse a stable actor-role wire string.
    pub fn parse(value: &str) -> Result<Self, ProofAcceptanceActorRoleParseError> {
        match value {
            "agent_worker" => Ok(Self::AgentWorker),
            "verifier_worker" => Ok(Self::VerifierWorker),
            "integrator" => Ok(Self::Integrator),
            "release_controller" => Ok(Self::ReleaseController),
            "human_administrator" => Ok(Self::HumanAdministrator),
            _ => Err(ProofAcceptanceActorRoleParseError {
                value: value.to_owned(),
            }),
        }
    }
}

impl FromStr for ProofAcceptanceActorRole {
    type Err = ProofAcceptanceActorRoleParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::parse(value)
    }
}

impl fmt::Display for ProofAcceptanceActorRole {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofAcceptanceActorRoleParseError {
    value: String,
}

impl ProofAcceptanceActorRoleParseError {
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl fmt::Display for ProofAcceptanceActorRoleParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unknown proof acceptance actor-role wire string {:?}",
            self.value
        )
    }
}

impl std::error::Error for ProofAcceptanceActorRoleParseError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofAcceptanceTransitionEdge {
    pub from_state: ProofAcceptanceState,
    pub to_state: ProofAcceptanceState,
    pub actor_role: ProofAcceptanceActorRole,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofAcceptanceTransition<'a> {
    pub from_state: ProofAcceptanceState,
    pub to_state: ProofAcceptanceState,
    pub actor_role: ProofAcceptanceActorRole,
    pub previous_artifact_hash: Option<&'a str>,
    pub expected_previous_artifact_hash: Option<&'a str>,
    pub next_artifact_hash: Option<&'a str>,
    pub policy_hash: Option<&'a str>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofAcceptanceTransitionError {
    ForbiddenTransition {
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
    },
    MissingPreviousArtifactHash {
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
    },
    MissingNextArtifactHash {
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
    },
    MissingPolicyHash {
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
    },
    RoleMismatch {
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
        expected_role: ProofAcceptanceActorRole,
        actual_role: ProofAcceptanceActorRole,
    },
    StaleInputHash {
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
        expected_previous_artifact_hash: String,
        actual_previous_artifact_hash: String,
    },
}

impl ProofAcceptanceTransitionError {
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::ForbiddenTransition { .. } => "forbidden_transition",
            Self::MissingPreviousArtifactHash { .. } => "missing_previous_artifact_hash",
            Self::MissingNextArtifactHash { .. } => "missing_next_artifact_hash",
            Self::MissingPolicyHash { .. } => "missing_policy_hash",
            Self::RoleMismatch { .. } => "role_mismatch",
            Self::StaleInputHash { .. } => "stale_input_hash",
        }
    }
}

impl fmt::Display for ProofAcceptanceTransitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind())
    }
}

impl std::error::Error for ProofAcceptanceTransitionError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProofAcceptanceTransitionSnapshotRow {
    pub from_state: &'static str,
    pub to_state: &'static str,
    pub actor_role: &'static str,
}

pub fn validate_proof_acceptance_transition(
    transition: ProofAcceptanceTransition<'_>,
) -> Result<(), ProofAcceptanceTransitionError> {
    if is_missing_hash(transition.previous_artifact_hash) {
        return Err(
            ProofAcceptanceTransitionError::MissingPreviousArtifactHash {
                from_state: transition.from_state,
                to_state: transition.to_state,
            },
        );
    }
    if is_missing_hash(transition.next_artifact_hash) {
        return Err(ProofAcceptanceTransitionError::MissingNextArtifactHash {
            from_state: transition.from_state,
            to_state: transition.to_state,
        });
    }
    if is_missing_hash(transition.policy_hash) {
        return Err(ProofAcceptanceTransitionError::MissingPolicyHash {
            from_state: transition.from_state,
            to_state: transition.to_state,
        });
    }
    if let (Some(expected), Some(actual)) = (
        transition
            .expected_previous_artifact_hash
            .filter(|value| !value.is_empty()),
        transition.previous_artifact_hash,
    ) {
        if expected != actual {
            return Err(ProofAcceptanceTransitionError::StaleInputHash {
                from_state: transition.from_state,
                to_state: transition.to_state,
                expected_previous_artifact_hash: expected.to_owned(),
                actual_previous_artifact_hash: actual.to_owned(),
            });
        }
    }

    let Some(edge) = expected_transition_edge(transition.from_state, transition.to_state) else {
        return Err(ProofAcceptanceTransitionError::ForbiddenTransition {
            from_state: transition.from_state,
            to_state: transition.to_state,
        });
    };
    if transition.actor_role != edge.actor_role {
        return Err(ProofAcceptanceTransitionError::RoleMismatch {
            from_state: transition.from_state,
            to_state: transition.to_state,
            expected_role: edge.actor_role,
            actual_role: transition.actor_role,
        });
    }

    Ok(())
}

pub fn proof_acceptance_transition_matrix_snapshot_rows(
) -> Vec<ProofAcceptanceTransitionSnapshotRow> {
    let mut rows = PROOF_ACCEPTANCE_TRANSITION_EDGES
        .iter()
        .map(|edge| ProofAcceptanceTransitionSnapshotRow {
            from_state: edge.from_state.as_str(),
            to_state: edge.to_state.as_str(),
            actor_role: edge.actor_role.as_str(),
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

pub fn expected_transition_edge(
    from_state: ProofAcceptanceState,
    to_state: ProofAcceptanceState,
) -> Option<ProofAcceptanceTransitionEdge> {
    PROOF_ACCEPTANCE_TRANSITION_EDGES
        .iter()
        .copied()
        .find(|edge| edge.from_state == from_state && edge.to_state == to_state)
}

fn is_missing_hash(value: Option<&str>) -> bool {
    value.map(str::is_empty).unwrap_or(true)
}

fn hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, domain);
    encode_uvar(&mut out, payload.len() as u64);
    out.extend(payload);
    sha256(&out)
}

fn sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn name_canonical_bytes(name: &Name) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, name);
    out
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_hash(out: &mut Vec<u8>, hash: &Hash) {
    out.extend(hash);
}

fn encode_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(0x01);
            encode_hash(out, hash);
        }
        None => out.push(0x00),
    }
}

fn encode_option_string(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_string(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_option_release_evidence_kind(
    out: &mut Vec<u8>,
    value: Option<VerifiedArtifactReleaseEvidenceKind>,
) {
    match value {
        Some(kind) => {
            out.push(0x01);
            encode_string(out, kind.as_str());
        }
        None => out.push(0x00),
    }
}

fn generated_decl_kind_tag(kind: GeneratedDeclKind) -> u8 {
    match kind {
        GeneratedDeclKind::Constructor => 0x00,
        GeneratedDeclKind::Recursor => 0x01,
    }
}

fn export_kind_tag(kind: ExportKind) -> u8 {
    match kind {
        ExportKind::Axiom => 0x00,
        ExportKind::Def => 0x01,
        ExportKind::Theorem => 0x02,
        ExportKind::Inductive => 0x03,
        ExportKind::Constructor => 0x04,
        ExportKind::Recursor => 0x05,
    }
}

fn encode_option_reducibility(out: &mut Vec<u8>, reducibility: Option<CertReducibility>) {
    match reducibility {
        Some(CertReducibility::Reducible) => {
            out.push(0x01);
            out.push(0x00);
        }
        Some(CertReducibility::Opaque) => {
            out.push(0x01);
            out.push(0x01);
        }
        None => out.push(0x00),
    }
}

fn encode_option_opacity(out: &mut Vec<u8>, opacity: Option<Opacity>) {
    match opacity {
        Some(Opacity::Opaque) => {
            out.push(0x01);
            out.push(0x00);
        }
        None => out.push(0x00),
    }
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

impl ProofAcceptanceState {
    /// Return every canonical proof-acceptance state in transition order.
    pub const fn all() -> &'static [Self] {
        &PROOF_ACCEPTANCE_STATES
    }

    /// Return every stable wire string in transition order.
    pub const fn wire_strings() -> &'static [&'static str] {
        &PROOF_ACCEPTANCE_STATE_WIRE_STRINGS
    }

    /// Return the stable lower-case wire spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Proposed => "proposed",
            Self::Parsed => "parsed",
            Self::TypeChecked => "type_checked",
            Self::ProofCandidate => "proof_candidate",
            Self::ReplayVerified => "replay_verified",
            Self::CertificateGenerated => "certificate_generated",
            Self::CertificateVerified => "certificate_verified",
            Self::IndependentVerified => "independent_verified",
            Self::Integrated => "integrated",
            Self::Published => "published",
        }
    }

    /// Parse a stable proof-acceptance state wire string.
    pub fn parse(value: &str) -> Result<Self, ProofAcceptanceStateParseError> {
        match value {
            "proposed" => Ok(Self::Proposed),
            "parsed" => Ok(Self::Parsed),
            "type_checked" => Ok(Self::TypeChecked),
            "proof_candidate" => Ok(Self::ProofCandidate),
            "replay_verified" => Ok(Self::ReplayVerified),
            "certificate_generated" => Ok(Self::CertificateGenerated),
            "certificate_verified" => Ok(Self::CertificateVerified),
            "independent_verified" => Ok(Self::IndependentVerified),
            "integrated" => Ok(Self::Integrated),
            "published" => Ok(Self::Published),
            _ => Err(ProofAcceptanceStateParseError {
                value: value.to_owned(),
            }),
        }
    }

    /// Return whether this state can back a verified artifact record.
    pub const fn is_verified_artifact_state(self) -> bool {
        match self {
            Self::CertificateVerified
            | Self::IndependentVerified
            | Self::Integrated
            | Self::Published => true,
            Self::Proposed
            | Self::Parsed
            | Self::TypeChecked
            | Self::ProofCandidate
            | Self::ReplayVerified
            | Self::CertificateGenerated => false,
        }
    }

    /// Map verification-result advancing statuses to canonical states.
    ///
    /// Terminal non-advancing statuses such as `rejected` and
    /// `checker_disagreement` intentionally return `None`.
    pub fn from_verification_result_status(value: &str) -> Option<Self> {
        match value {
            "replay_verified" => Some(Self::ReplayVerified),
            "certificate_generated" => Some(Self::CertificateGenerated),
            "certificate_verified" => Some(Self::CertificateVerified),
            "independent_verified" => Some(Self::IndependentVerified),
            _ => None,
        }
    }
}

pub fn verification_result_status_is_checker_disagreement(value: &str) -> bool {
    value == CHECKER_DISAGREEMENT_VERIFICATION_STATUS
}

pub fn checker_disagreement_blocks_automatic_acceptance(value: &str) -> bool {
    verification_result_status_is_checker_disagreement(value)
        && ProofAcceptanceState::from_verification_result_status(value).is_none()
}

impl FromStr for ProofAcceptanceState {
    type Err = ProofAcceptanceStateParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::parse(value)
    }
}

impl fmt::Display for ProofAcceptanceState {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofAcceptanceStateParseError {
    value: String,
}

impl ProofAcceptanceStateParseError {
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl fmt::Display for ProofAcceptanceStateParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unknown proof acceptance state wire string {:?}",
            self.value
        )
    }
}

impl std::error::Error for ProofAcceptanceStateParseError {}

#[cfg(test)]
mod tests {
    use super::*;

    const PREVIOUS_HASH: &str =
        "sha256:0000000000000000000000000000000000000000000000000000000000000001";
    const NEXT_HASH: &str =
        "sha256:0000000000000000000000000000000000000000000000000000000000000002";
    const POLICY_HASH: &str =
        "sha256:0000000000000000000000000000000000000000000000000000000000000003";
    const STALE_HASH: &str =
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    const NEXT_HASH_BYTES: Hash = [2; 32];
    const STALE_HASH_BYTES: Hash = [255; 32];

    fn valid_transition(
        from_state: ProofAcceptanceState,
        to_state: ProofAcceptanceState,
        actor_role: ProofAcceptanceActorRole,
    ) -> ProofAcceptanceTransition<'static> {
        ProofAcceptanceTransition {
            from_state,
            to_state,
            actor_role,
            previous_artifact_hash: Some(PREVIOUS_HASH),
            expected_previous_artifact_hash: Some(PREVIOUS_HASH),
            next_artifact_hash: Some(NEXT_HASH),
            policy_hash: Some(POLICY_HASH),
        }
    }

    fn assert_forbidden_transition(
        transition: ProofAcceptanceTransition<'static>,
    ) -> ProofAcceptanceTransitionError {
        let error = validate_proof_acceptance_transition(transition).unwrap_err();
        assert_eq!(error.kind(), "forbidden_transition");
        error
    }

    fn test_hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn hash_hex(hash: Hash) -> String {
        hash.iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    }

    fn error_artifact_kind(error: &VerifiedOnlySharingError) -> Option<&'static str> {
        match error {
            VerifiedOnlySharingError::ArtifactKindNotSharable { artifact_kind, .. } => {
                Some(artifact_kind.as_str())
            }
            _ => None,
        }
    }

    fn base_candidate_identity() -> ProofCandidateIdentity {
        ProofCandidateIdentity {
            task_kind: ProofCandidateKind::MachineTactic,
            source_kind: ProofCandidateSourceKind::Payload,
            canonical_source_or_payload_hash: test_hash(1),
            environment_hash: test_hash(2),
            import_closure_hash: test_hash(3),
            axiom_policy_hash: test_hash(4),
            feature_profile_hash: test_hash(5),
            statement_hash: test_hash(6),
            goal_fingerprint: test_hash(7),
            candidate_payload_hash: test_hash(8),
            deterministic_budget_hash: test_hash(9),
        }
    }

    fn base_verified_artifact_identity() -> VerifiedArtifactIdentity {
        VerifiedArtifactIdentity {
            state: ProofAcceptanceState::CertificateVerified,
            candidate_hash: base_candidate_identity().hash(),
            statement_hash: test_hash(6),
            certificate_hash: test_hash(20),
            export_hash: test_hash(21),
            axiom_report_hash: test_hash(22),
            package_manifest_hash: None,
            package_lock_hash: None,
            verifier_profile: None,
            verifier_binary_hash: None,
            verifier_version_or_build_hash: None,
            release_evidence_kind: None,
            release_evidence_hash: None,
        }
    }

    fn release_ready_verified_artifact_identity(
        state: ProofAcceptanceState,
        release_evidence_kind: VerifiedArtifactReleaseEvidenceKind,
    ) -> VerifiedArtifactIdentity {
        let mut identity = base_verified_artifact_identity();
        identity.state = state;
        identity.package_lock_hash = Some(test_hash(23));
        identity.verifier_profile = Some("reference".to_owned());
        identity.verifier_binary_hash = Some(test_hash(24));
        identity.verifier_version_or_build_hash = Some(test_hash(25));
        identity.release_evidence_kind = Some(release_evidence_kind);
        identity.release_evidence_hash = Some(test_hash(26));
        identity
    }

    fn verified_only_sharing_check(
        surface: VerifiedOnlySharingSurface,
    ) -> VerifiedOnlySharingCheck<'static> {
        VerifiedOnlySharingCheck {
            surface,
            artifact_kind: VerifiedOnlySharingArtifactKind::VerifiedArtifactIdentity,
            state: ProofAcceptanceState::CertificateVerified,
            verified_artifact_identity_hash: Some(&NEXT_HASH_BYTES),
            candidate_identity_hash: None,
        }
    }

    fn local_lemma_proposed() -> LocalLemmaProposed {
        LocalLemmaProposed {
            lemma_id: "local-lemma-1".to_owned(),
            sketch_hash: test_hash(0x30),
            sketch_node_id: "sketch-node-local-lemma".to_owned(),
            statement_hash: test_hash(0x31),
            environment_hash: test_hash(0x32),
            policy_hash: test_hash(0x33),
        }
    }

    fn local_lemma_type_checked() -> LocalLemmaTypeChecked {
        let proposed = local_lemma_proposed();
        LocalLemmaTypeChecked {
            lemma_id: proposed.lemma_id,
            sketch_hash: proposed.sketch_hash,
            sketch_node_id: proposed.sketch_node_id,
            statement_hash: proposed.statement_hash,
            expected_type_hash: test_hash(0x34),
            environment_hash: proposed.environment_hash,
            policy_hash: proposed.policy_hash,
        }
    }

    fn local_lemma_available_dependency(byte: u8) -> LocalLemmaAvailableDependencyIdentity {
        let mut dependency = LocalLemmaAvailableDependencyIdentity {
            dependency_identity_hash: [0; 32],
            verified_artifact_identity_hash: test_hash(byte),
            state: ProofAcceptanceState::CertificateVerified,
            statement_hash: test_hash(byte.wrapping_add(1)),
            environment_hash: test_hash(0x32),
            policy_hash: test_hash(0x33),
        };
        dependency.dependency_identity_hash =
            local_lemma_available_dependency_identity_hash(&dependency);
        dependency
    }

    fn local_lemma_task_identity() -> LocalLemmaProofTaskIdentity {
        let typed = local_lemma_type_checked();
        let mut task_identity = LocalLemmaProofTaskIdentity {
            task_identity_hash: [0; 32],
            statement_hash: typed.statement_hash,
            expected_type_hash: typed.expected_type_hash,
            environment_hash: typed.environment_hash,
            policy_hash: typed.policy_hash,
            available_dependency_identities: vec![local_lemma_available_dependency(0x50)],
        };
        task_identity.task_identity_hash = local_lemma_proof_task_identity_hash(&task_identity);
        task_identity
    }

    fn local_lemma_proof_task() -> LocalLemmaProofTask {
        let typed = local_lemma_type_checked();
        LocalLemmaProofTask {
            lemma_id: typed.lemma_id,
            sketch_hash: typed.sketch_hash,
            sketch_node_id: typed.sketch_node_id,
            statement_hash: typed.statement_hash,
            expected_type_hash: typed.expected_type_hash,
            environment_hash: typed.environment_hash,
            policy_hash: typed.policy_hash,
            task_identity: local_lemma_task_identity(),
        }
    }

    fn local_lemma_verified_with_status(status: ProofAcceptanceState) -> LocalLemmaVerified {
        let task = local_lemma_proof_task();
        let mut proof_artifact_identity = base_verified_artifact_identity();
        proof_artifact_identity.statement_hash = task.statement_hash;
        let proof_artifact_identity_hash = proof_artifact_identity.hash();
        let mut source_free_verifier_result = LocalLemmaSourceFreeVerifierResult {
            result_hash: [0; 32],
            status,
            task_identity_hash: task.task_identity.task_identity_hash,
            proof_artifact_identity_hash,
            statement_hash: task.statement_hash,
            environment_hash: task.environment_hash,
            policy_hash: task.policy_hash,
        };
        source_free_verifier_result.result_hash =
            local_lemma_source_free_verifier_result_hash(&source_free_verifier_result);
        LocalLemmaVerified {
            lemma_id: task.lemma_id,
            sketch_hash: task.sketch_hash,
            sketch_node_id: task.sketch_node_id,
            statement_hash: task.statement_hash,
            expected_type_hash: task.expected_type_hash,
            environment_hash: task.environment_hash,
            policy_hash: task.policy_hash,
            task_identity: task.task_identity,
            proof_artifact_identity,
            proof_artifact_identity_hash,
            source_free_verifier_result,
        }
    }

    fn local_lemma_verified() -> LocalLemmaVerified {
        local_lemma_verified_with_status(ProofAcceptanceState::CertificateVerified)
    }

    fn local_lemma_expected_command(
        kind: LocalLemmaVerificationCommandKind,
    ) -> LocalLemmaExpectedVerificationCommand {
        let mut command = LocalLemmaExpectedVerificationCommand {
            command_hash: [0; 32],
            kind,
            module: "Proofs.Ai.SketchLifecycle".to_owned(),
            verified_cache_authoring: kind
                == LocalLemmaVerificationCommandKind::VerifyModuleSourceFree,
            package_metadata: false,
        };
        command.command_hash = local_lemma_expected_verification_command_hash(&command);
        command
    }

    fn local_lemma_generalized_context() -> LocalLemmaGeneralizedContext {
        let mut context = LocalLemmaGeneralizedContext {
            context_hash: [0; 32],
            binders: vec![
                LocalLemmaGeneralizedContextBinder {
                    binder_id: "A".to_owned(),
                    type_hash: test_hash(0x90),
                    dependency_hashes: vec![],
                },
                LocalLemmaGeneralizedContextBinder {
                    binder_id: "x".to_owned(),
                    type_hash: test_hash(0x91),
                    dependency_hashes: vec![test_hash(0x90)],
                },
            ],
        };
        context.context_hash = local_lemma_generalized_context_hash(&context);
        context
    }

    fn local_lemma_proof_task_handoff() -> LocalLemmaProofTaskHandoff {
        let typed = local_lemma_type_checked();
        let mut handoff = LocalLemmaProofTaskHandoff {
            handoff_hash: [0; 32],
            lemma_id: typed.lemma_id,
            sketch_hash: typed.sketch_hash,
            sketch_node_id: typed.sketch_node_id,
            module: "Proofs.Ai.SketchLifecycle".to_owned(),
            declaration_name: "generated_local_lemma_identity".to_owned(),
            statement_hash: typed.statement_hash,
            expected_type_hash: typed.expected_type_hash,
            environment_hash: typed.environment_hash,
            axiom_policy_hash: typed.policy_hash,
            generalized_context: local_lemma_generalized_context(),
            dependency_identities: vec![local_lemma_available_dependency(0x50)],
            target_proof_corpus_module: "Proofs.Ai.SketchLifecycle".to_owned(),
            expected_verification_commands: vec![
                local_lemma_expected_command(LocalLemmaVerificationCommandKind::BuildModule),
                local_lemma_expected_command(
                    LocalLemmaVerificationCommandKind::VerifyModuleSourceFree,
                ),
            ],
            unproved_storage_kind: LocalLemmaUnprovedStorageKind::TaskSidecar,
        };
        handoff.handoff_hash = local_lemma_proof_task_handoff_hash(&handoff);
        handoff
    }

    fn theorem_invention_generalized_context() -> TheoremInventionGeneralizedContext {
        let mut context = TheoremInventionGeneralizedContext {
            context_hash: [0; 32],
            binders: vec![
                TheoremInventionGeneralizedContextBinder {
                    binder_id: "A".to_owned(),
                    type_hash: test_hash(0xb0),
                    dependency_hashes: vec![],
                },
                TheoremInventionGeneralizedContextBinder {
                    binder_id: "x".to_owned(),
                    type_hash: test_hash(0xb1),
                    dependency_hashes: vec![test_hash(0xb0)],
                },
            ],
        };
        context.context_hash = theorem_invention_generalized_context_hash(&context);
        context
    }

    fn theorem_invention_command(
        kind: TheoremInventionVerificationCommandKind,
    ) -> TheoremInventionVerificationCommand {
        let mut command = TheoremInventionVerificationCommand {
            command_hash: [0; 32],
            kind,
            module: "Proofs.Ai.LibraryGrowth".to_owned(),
            verified_cache_authoring: kind
                == TheoremInventionVerificationCommandKind::VerifyModuleSourceFree,
            package_metadata: false,
        };
        command.command_hash = theorem_invention_verification_command_hash(&command);
        command
    }

    fn refresh_theorem_invention_artifact_hash(artifact: &mut TheoremInventionArtifact) {
        artifact.artifact_identity_hash = theorem_invention_artifact_identity_hash(artifact);
    }

    fn theorem_invention_artifact(
        theorem_level: TheoremLevel,
        artifact_kind: TheoremInventionArtifactKind,
        promotion_intent: TheoremInventionPromotionIntent,
    ) -> TheoremInventionArtifact {
        let mut artifact = TheoremInventionArtifact {
            artifact_identity_hash: [0; 32],
            artifact_kind,
            theorem_level,
            statement_hash: test_hash(0xc0),
            normalized_statement: "forall (A : Type) (x : A), x = x".to_owned(),
            generalized_context: theorem_invention_generalized_context(),
            source_module: "Proofs.Ai.ParentGoal".to_owned(),
            target_proof_corpus_module: "Proofs.Ai.LibraryGrowth".to_owned(),
            declaration_name: "generated_reflexivity_library_growth".to_owned(),
            dependency_identities: vec![test_hash(0xc1), test_hash(0xc2)],
            import_closure: vec![
                "Proofs.Ai.Basic".to_owned(),
                "Proofs.Ai.Eq".to_owned(),
                "Proofs.Ai.LibraryGrowth".to_owned(),
            ],
            axiom_policy_hash: test_hash(0xc3),
            replay_path: Some("proofs/Proofs/Ai/LibraryGrowth/replay.json".to_owned()),
            replay_hash: Some(test_hash(0xc4)),
            certificate_path: Some("proofs/Proofs/Ai/LibraryGrowth/certificate.npcert".to_owned()),
            certificate_hash: Some(test_hash(0xc5)),
            verification_commands: vec![
                theorem_invention_command(TheoremInventionVerificationCommandKind::BuildModule),
                theorem_invention_command(
                    TheoremInventionVerificationCommandKind::VerifyModuleSourceFree,
                ),
            ],
            promotion_intent,
            prerequisite_blocker: None,
            conclusion_assuming: false,
            replay_is_stale: false,
            import_closure_is_stale: false,
            axiom_policy_widened: false,
        };
        refresh_theorem_invention_artifact_hash(&mut artifact);
        artifact
    }

    fn invented_candidate_imports() -> Vec<InventedCandidateImportIdentity> {
        vec![
            InventedCandidateImportIdentity {
                module: "Proofs.Ai.Basic".to_owned(),
                import_hash: test_hash(0xe0),
            },
            InventedCandidateImportIdentity {
                module: "Proofs.Ai.Eq".to_owned(),
                import_hash: test_hash(0xe1),
            },
        ]
    }

    fn refresh_invented_candidate_witness_hash(witness: &mut InventedCandidateTypecheckWitness) {
        witness.witness_hash = invented_candidate_typecheck_witness_hash(witness);
    }

    fn refresh_invented_candidate_request_hash(request: &mut InventedCandidateTypecheckRequest) {
        if let Some(witness) = request.typecheck_witness.as_mut() {
            refresh_invented_candidate_witness_hash(witness);
        }
        request.request_hash = invented_candidate_typecheck_request_hash(request);
    }

    fn invented_candidate_typecheck_request() -> InventedCandidateTypecheckRequest {
        let imports = invented_candidate_imports();
        let mut witness = InventedCandidateTypecheckWitness {
            witness_hash: [0; 32],
            status: InventedCandidateTypecheckStatus::TypeChecked,
            statement_hash: test_hash(0xf0),
            expected_type_hash: test_hash(0xf1),
            environment_hash: test_hash(0xf2),
            import_closure_hash: invented_candidate_import_closure_hash(&imports),
            axiom_policy_hash: test_hash(0xf3),
            target_proof_corpus_module: "Proofs.Ai.LibraryGrowth".to_owned(),
            diagnostic_hash: None,
        };
        refresh_invented_candidate_witness_hash(&mut witness);
        let mut request = InventedCandidateTypecheckRequest {
            request_hash: [0; 32],
            candidate_id: "pua-m14-generated-reflexivity".to_owned(),
            source_module: "Proofs.Ai.ParentGoal".to_owned(),
            target_proof_corpus_module: "Proofs.Ai.LibraryGrowth".to_owned(),
            declaration_name: "generated_reflexivity_library_growth".to_owned(),
            normalized_statement: "forall (A : Type) (x : A), x = x".to_owned(),
            statement_hash: test_hash(0xf0),
            generalized_context: theorem_invention_generalized_context(),
            environment_hash: test_hash(0xf2),
            import_identities: imports,
            required_import_modules: vec!["Proofs.Ai.Basic".to_owned(), "Proofs.Ai.Eq".to_owned()],
            axiom_policy_hash: test_hash(0xf3),
            expected_axiom_policy_hash: test_hash(0xf3),
            typecheck_witness: Some(witness),
            conclusion_assuming: false,
            axiom_policy_widened: false,
        };
        refresh_invented_candidate_request_hash(&mut request);
        request
    }

    fn invented_lemma_typecheck_request() -> InventedCandidateTypecheckRequest {
        let imports = Vec::new();
        let mut witness = InventedCandidateTypecheckWitness {
            witness_hash: [0; 32],
            status: InventedCandidateTypecheckStatus::TypeChecked,
            statement_hash: test_hash(0x80),
            expected_type_hash: test_hash(0x81),
            environment_hash: test_hash(0x82),
            import_closure_hash: invented_candidate_import_closure_hash(&imports),
            axiom_policy_hash: test_hash(0x83),
            target_proof_corpus_module: "Proofs.Ai.SketchLifecycle".to_owned(),
            diagnostic_hash: None,
        };
        refresh_invented_candidate_witness_hash(&mut witness);
        let mut request = InventedCandidateTypecheckRequest {
            request_hash: [0; 32],
            candidate_id: "pua-m14-generated-local-lemma-identity".to_owned(),
            source_module: "Proofs.Ai.ParentGoal".to_owned(),
            target_proof_corpus_module: "Proofs.Ai.SketchLifecycle".to_owned(),
            declaration_name: "generated_local_lemma_identity".to_owned(),
            normalized_statement: "forall (A : Type), forall (x : A), A".to_owned(),
            statement_hash: test_hash(0x80),
            generalized_context: theorem_invention_generalized_context(),
            environment_hash: test_hash(0x82),
            import_identities: imports,
            required_import_modules: vec![],
            axiom_policy_hash: test_hash(0x83),
            expected_axiom_policy_hash: test_hash(0x83),
            typecheck_witness: Some(witness),
            conclusion_assuming: false,
            axiom_policy_widened: false,
        };
        refresh_invented_candidate_request_hash(&mut request);
        request
    }

    fn invented_lemma_typecheck_handoff() -> (
        InventedCandidateTypecheckRequest,
        InventedCandidateTypecheckHandoff,
    ) {
        let request = invented_lemma_typecheck_request();
        let outcome = invented_candidate_typecheck(&request).unwrap();
        let InventedCandidateTypecheckOutcome::Accepted(typecheck_handoff) = outcome else {
            panic!("invented lemma fixture should typecheck");
        };
        (request, typecheck_handoff)
    }

    fn invented_lemma_proof_task_handoff_fixture() -> (
        InventedCandidateTypecheckRequest,
        InventedCandidateTypecheckHandoff,
        InventedLemmaProofTaskHandoff,
    ) {
        let (request, typecheck_handoff) = invented_lemma_typecheck_handoff();
        let task = invented_lemma_proof_task_handoff_from_typecheck(
            &request,
            &typecheck_handoff,
            vec![local_lemma_available_dependency(0x60)],
            "Proofs/Ai/SketchLifecycle/source.npa".to_owned(),
            "Proofs/Ai/SketchLifecycle/certificate.npcert".to_owned(),
            "Proofs/Ai/SketchLifecycle/meta.json".to_owned(),
            "Proofs/Ai/SketchLifecycle/replay.json".to_owned(),
        )
        .unwrap();
        (request, typecheck_handoff, task)
    }

    fn assert_typecheck_blocker(
        request: &InventedCandidateTypecheckRequest,
        reason: InventedCandidateTypecheckBlockerReason,
    ) {
        let outcome = invented_candidate_typecheck(request).unwrap();
        let InventedCandidateTypecheckOutcome::Blocked(blocker) = outcome else {
            panic!("candidate should be blocked");
        };
        validate_invented_candidate_typecheck_blocker(request, &blocker).unwrap();
        assert_eq!(blocker.reason, reason);
        assert!(!blocker.creates_theorem_declaration);
        assert!(blocker.unproved_storage_kind.is_unproved_sidecar());
    }

    fn local_lemma_verified_artifact_record(
        handoff: &LocalLemmaProofTaskHandoff,
    ) -> LocalLemmaVerifiedArtifactRecord {
        let task_identity = local_lemma_task_identity_from_handoff(handoff);
        let mut artifact = LocalLemmaVerifiedArtifactRecord {
            artifact_record_hash: [0; 32],
            module: handoff.module.clone(),
            declaration_name: handoff.declaration_name.clone(),
            statement_hash: handoff.statement_hash,
            task_identity_hash: task_identity.task_identity_hash,
            certificate_hash: test_hash(0xa0),
            export_hash: test_hash(0xa1),
            declaration_interface_hash: test_hash(0xa2),
            source_hash: test_hash(0xa3),
            replay_path: "Proofs/Ai/SketchLifecycle/replay.json".to_owned(),
            replay_hash: test_hash(0xa4),
            axiom_summary: vec![],
            axiom_summary_hash: local_lemma_axiom_summary_hash(&[]),
            source_free_verifier_result: LocalLemmaSourceFreeVerifierResult {
                result_hash: [0; 32],
                status: ProofAcceptanceState::CertificateVerified,
                task_identity_hash: task_identity.task_identity_hash,
                proof_artifact_identity_hash: [0; 32],
                statement_hash: handoff.statement_hash,
                environment_hash: handoff.environment_hash,
                policy_hash: handoff.axiom_policy_hash,
            },
        };
        let identity = local_lemma_verified_artifact_identity(handoff, &artifact).unwrap();
        artifact
            .source_free_verifier_result
            .proof_artifact_identity_hash = identity.hash();
        artifact.source_free_verifier_result.result_hash =
            local_lemma_source_free_verifier_result_hash(&artifact.source_free_verifier_result);
        artifact.artifact_record_hash = local_lemma_verified_artifact_record_hash(&artifact);
        artifact
    }

    #[test]
    fn trust_state_round_trips_stable_wire_strings() {
        assert_eq!(ProofAcceptanceState::all().len(), 10);
        assert_eq!(ProofAcceptanceState::wire_strings().len(), 10);

        for (state, wire) in ProofAcceptanceState::all()
            .iter()
            .copied()
            .zip(ProofAcceptanceState::wire_strings().iter().copied())
        {
            assert_eq!(state.as_str(), wire);
            assert_eq!(state.to_string(), wire);
            assert_eq!(ProofAcceptanceState::parse(wire).unwrap(), state);
            assert_eq!(wire.parse::<ProofAcceptanceState>().unwrap(), state);
        }
    }

    #[test]
    fn trust_state_rejects_task_service_status_strings() {
        for value in ["ready", "leased", "running", "verified"] {
            let error = ProofAcceptanceState::parse(value).unwrap_err();
            assert_eq!(error.value(), value);
        }
    }

    #[test]
    fn trust_state_verification_result_advancing_statuses_map_to_canonical_states() {
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status("replay_verified"),
            Some(ProofAcceptanceState::ReplayVerified)
        );
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status("certificate_generated"),
            Some(ProofAcceptanceState::CertificateGenerated)
        );
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status("certificate_verified"),
            Some(ProofAcceptanceState::CertificateVerified)
        );
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status("independent_verified"),
            Some(ProofAcceptanceState::IndependentVerified)
        );
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status("rejected"),
            None
        );
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status("checker_disagreement"),
            None
        );
    }

    #[test]
    fn checker_disagreement_record_status_blocks_automatic_acceptance_states() {
        assert!(verification_result_status_is_checker_disagreement(
            CHECKER_DISAGREEMENT_VERIFICATION_STATUS
        ));
        assert!(checker_disagreement_blocks_automatic_acceptance(
            CHECKER_DISAGREEMENT_VERIFICATION_STATUS
        ));
        assert_eq!(
            ProofAcceptanceState::from_verification_result_status(
                CHECKER_DISAGREEMENT_VERIFICATION_STATUS
            ),
            None
        );
        for verified_state in [
            ProofAcceptanceState::CertificateVerified,
            ProofAcceptanceState::IndependentVerified,
            ProofAcceptanceState::Integrated,
            ProofAcceptanceState::Published,
        ] {
            assert_ne!(
                Some(verified_state),
                ProofAcceptanceState::from_verification_result_status(
                    CHECKER_DISAGREEMENT_VERIFICATION_STATUS
                )
            );
        }
    }

    #[test]
    fn trust_state_verified_artifact_thresholds_are_explicit() {
        for state in [
            ProofAcceptanceState::Proposed,
            ProofAcceptanceState::Parsed,
            ProofAcceptanceState::TypeChecked,
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceState::CertificateGenerated,
        ] {
            assert!(!state.is_verified_artifact_state());
        }

        for state in [
            ProofAcceptanceState::CertificateVerified,
            ProofAcceptanceState::IndependentVerified,
            ProofAcceptanceState::Integrated,
            ProofAcceptanceState::Published,
        ] {
            assert!(state.is_verified_artifact_state());
        }
    }

    #[test]
    fn candidate_identity_hash_has_stable_snapshot() {
        let identity = base_candidate_identity();

        assert_eq!(
            hash_hex(identity.hash()),
            "fea34b2cec7d08149e5a1ba9fbd8847dd9d42f9c47238a228f45f98f0eadfd46"
        );
        assert_eq!(identity.canonical_bytes(), identity.canonical_bytes());
    }

    #[test]
    fn candidate_identity_changes_for_every_contract_input() {
        let base = base_candidate_identity();
        let base_hash = base.hash();

        let mut changed = base.clone();
        changed.task_kind = ProofCandidateKind::CoreTerm;
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.source_kind = ProofCandidateSourceKind::CanonicalSource;
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.canonical_source_or_payload_hash = test_hash(10);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.environment_hash = test_hash(11);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.import_closure_hash = test_hash(12);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.axiom_policy_hash = test_hash(13);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.feature_profile_hash = test_hash(14);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.statement_hash = test_hash(15);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.goal_fingerprint = test_hash(16);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.candidate_payload_hash = test_hash(17);
        assert_ne!(base_hash, changed.hash());

        let mut changed = base.clone();
        changed.deterministic_budget_hash = test_hash(18);
        assert_ne!(base_hash, changed.hash());
    }

    #[test]
    fn candidate_environment_hash_changes_for_environment_inputs() {
        let base = proof_candidate_environment_hash(
            test_hash(1),
            test_hash(2),
            test_hash(3),
            test_hash(4),
        );

        assert_ne!(
            base,
            proof_candidate_environment_hash(
                test_hash(5),
                test_hash(2),
                test_hash(3),
                test_hash(4)
            )
        );
        assert_ne!(
            base,
            proof_candidate_environment_hash(
                test_hash(1),
                test_hash(5),
                test_hash(3),
                test_hash(4)
            )
        );
        assert_ne!(
            base,
            proof_candidate_environment_hash(
                test_hash(1),
                test_hash(2),
                test_hash(5),
                test_hash(4)
            )
        );
        assert_ne!(
            base,
            proof_candidate_environment_hash(
                test_hash(1),
                test_hash(2),
                test_hash(3),
                test_hash(5)
            )
        );
    }

    #[test]
    fn candidate_identity_excludes_provider_scheduler_and_verified_artifact_metadata() {
        #[derive(Clone)]
        struct ExcludedSidecar {
            prompt: &'static str,
            model_name: &'static str,
            temperature_microunits: u32,
            wall_clock_ms: u64,
            display_name: &'static str,
            certificate_hash: Hash,
            export_hash: Hash,
            axiom_report_hash: Hash,
            package_hash: Hash,
            verifier_version_hash: Hash,
        }

        let identity = base_candidate_identity();
        let first = ExcludedSidecar {
            prompt: "prove it",
            model_name: "model-a",
            temperature_microunits: 0,
            wall_clock_ms: 10,
            display_name: "pretty candidate",
            certificate_hash: test_hash(20),
            export_hash: test_hash(21),
            axiom_report_hash: test_hash(22),
            package_hash: test_hash(23),
            verifier_version_hash: test_hash(24),
        };
        let second = ExcludedSidecar {
            prompt: "try a different proof",
            model_name: "model-b",
            temperature_microunits: 750_000,
            wall_clock_ms: 99_999,
            display_name: "renamed candidate",
            certificate_hash: test_hash(25),
            export_hash: test_hash(26),
            axiom_report_hash: test_hash(27),
            package_hash: test_hash(28),
            verifier_version_hash: test_hash(29),
        };

        assert_ne!(first.prompt, second.prompt);
        assert_ne!(first.model_name, second.model_name);
        assert_ne!(first.temperature_microunits, second.temperature_microunits);
        assert_ne!(first.wall_clock_ms, second.wall_clock_ms);
        assert_ne!(first.display_name, second.display_name);
        assert_ne!(first.certificate_hash, second.certificate_hash);
        assert_ne!(first.export_hash, second.export_hash);
        assert_ne!(first.axiom_report_hash, second.axiom_report_hash);
        assert_ne!(first.package_hash, second.package_hash);
        assert_ne!(first.verifier_version_hash, second.verifier_version_hash);
        assert_eq!(identity.hash(), identity.hash());
    }

    #[test]
    fn verified_artifact_identity_hash_has_stable_snapshot() {
        let identity = base_verified_artifact_identity();

        assert_eq!(
            hash_hex(identity.hash()),
            "570f2d6fb36f8e97a84f484ea65d02f15fd766571460b55078960b4f937f3c3c"
        );
        assert_eq!(identity.canonical_bytes(), identity.canonical_bytes());
    }

    #[test]
    fn verified_artifact_identity_is_distinct_from_candidate_identity() {
        let candidate = base_candidate_identity();
        let mut verified = base_verified_artifact_identity();
        verified.candidate_hash = candidate.hash();

        assert_ne!(candidate.hash(), verified.hash());
        assert_ne!(candidate.canonical_bytes(), verified.canonical_bytes());
        assert_eq!(verified.candidate_hash, candidate.hash());
    }

    #[test]
    fn verified_artifact_identity_rejects_states_below_certificate_verified() {
        for state in [
            ProofAcceptanceState::Proposed,
            ProofAcceptanceState::Parsed,
            ProofAcceptanceState::TypeChecked,
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceState::CertificateGenerated,
        ] {
            let mut identity = base_verified_artifact_identity();
            identity.state = state;

            let error = validate_verified_artifact_identity(&identity).unwrap_err();
            assert_eq!(error.kind(), "state_below_certificate_verified");
        }
    }

    #[test]
    fn verified_artifact_identity_requires_verifier_fields_after_independent_verification() {
        let mut identity = base_verified_artifact_identity();
        identity.state = ProofAcceptanceState::IndependentVerified;

        let error = identity.validate().unwrap_err();
        assert_eq!(error.kind(), "missing_verifier_profile");

        identity.verifier_profile = Some("reference".to_owned());
        let error = identity.validate().unwrap_err();
        assert_eq!(error.kind(), "missing_verifier_binary_hash");

        identity.verifier_binary_hash = Some(test_hash(24));
        let error = identity.validate().unwrap_err();
        assert_eq!(error.kind(), "missing_verifier_version_or_build_hash");

        identity.verifier_version_or_build_hash = Some(test_hash(25));
        identity.validate().unwrap();
    }

    #[test]
    fn verified_artifact_identity_requires_release_fields_for_integrated_and_published() {
        for state in [
            ProofAcceptanceState::Integrated,
            ProofAcceptanceState::Published,
        ] {
            let mut identity = base_verified_artifact_identity();
            identity.state = state;
            identity.verifier_profile = Some("reference".to_owned());
            identity.verifier_binary_hash = Some(test_hash(24));
            identity.verifier_version_or_build_hash = Some(test_hash(25));

            let error = identity.validate().unwrap_err();
            assert_eq!(error.kind(), "missing_package_manifest_or_lock_hash");

            identity.package_manifest_hash = Some(test_hash(23));
            let error = identity.validate().unwrap_err();
            assert_eq!(error.kind(), "missing_release_evidence_kind");

            identity.release_evidence_kind =
                Some(VerifiedArtifactReleaseEvidenceKind::ReferenceCheckerOnly);
            let error = identity.validate().unwrap_err();
            assert_eq!(error.kind(), "missing_release_evidence_hash");

            identity.release_evidence_hash = Some(test_hash(26));
            identity.validate().unwrap();
        }
    }

    #[test]
    fn verified_artifact_identity_distinguishes_reference_only_and_high_trust_release_evidence() {
        let reference_only = release_ready_verified_artifact_identity(
            ProofAcceptanceState::Published,
            VerifiedArtifactReleaseEvidenceKind::ReferenceCheckerOnly,
        );
        let high_trust = release_ready_verified_artifact_identity(
            ProofAcceptanceState::Published,
            VerifiedArtifactReleaseEvidenceKind::HighTrust,
        );

        reference_only.validate().unwrap();
        high_trust.validate().unwrap();
        assert_eq!(
            reference_only.release_evidence_kind.unwrap().as_str(),
            "reference_checker_only"
        );
        assert_eq!(
            VerifiedArtifactReleaseEvidenceKind::parse("high_trust").unwrap(),
            VerifiedArtifactReleaseEvidenceKind::HighTrust
        );
        assert_ne!(reference_only.hash(), high_trust.hash());
    }

    #[test]
    fn verified_only_sharing_accepts_verified_artifact_identity_at_default_threshold() {
        assert_eq!(
            VERIFIED_ONLY_SHARING_DEFAULT_MIN_STATE,
            ProofAcceptanceState::CertificateVerified
        );

        for surface in [
            VerifiedOnlySharingSurface::Premise,
            VerifiedOnlySharingSurface::BlackboardVerifiedFact,
            VerifiedOnlySharingSurface::TaskDependencyRelease,
            VerifiedOnlySharingSurface::ParentProofDependency,
        ] {
            let check = verified_only_sharing_check(surface);

            validate_verified_only_sharing(check).unwrap();
            assert!(is_verified_only_sharable(check));
        }
    }

    #[test]
    fn verified_only_sharing_rejects_states_below_certificate_verified() {
        for state in [
            ProofAcceptanceState::Proposed,
            ProofAcceptanceState::Parsed,
            ProofAcceptanceState::TypeChecked,
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceState::CertificateGenerated,
        ] {
            let mut check = verified_only_sharing_check(VerifiedOnlySharingSurface::Premise);
            check.state = state;

            let error = validate_verified_only_sharing(check).unwrap_err();
            assert_eq!(error.kind(), "state_below_sharing_threshold");
            assert!(!is_verified_only_sharable(check));
        }
    }

    #[test]
    fn verified_only_sharing_rejects_candidate_sidecar_cache_score_and_local_lemma_artifacts() {
        for artifact_kind in [
            VerifiedOnlySharingArtifactKind::CandidateArtifact,
            VerifiedOnlySharingArtifactKind::ReplaySidecar,
            VerifiedOnlySharingArtifactKind::Cache,
            VerifiedOnlySharingArtifactKind::SidecarIndex,
            VerifiedOnlySharingArtifactKind::SearchScore,
            VerifiedOnlySharingArtifactKind::UnverifiedLocalLemma,
            VerifiedOnlySharingArtifactKind::TheoremGraphAdvisoryOutput,
        ] {
            let mut check = verified_only_sharing_check(VerifiedOnlySharingSurface::Premise);
            check.artifact_kind = artifact_kind;

            let error = validate_verified_only_sharing(check).unwrap_err();
            assert_eq!(error.kind(), "artifact_kind_not_sharable");
            assert_eq!(artifact_kind.as_str(), error_artifact_kind(&error).unwrap());
        }
    }

    #[test]
    fn verified_only_sharing_requires_verified_artifact_identity_hash() {
        let mut check =
            verified_only_sharing_check(VerifiedOnlySharingSurface::BlackboardVerifiedFact);
        check.verified_artifact_identity_hash = None;

        let error = validate_verified_only_sharing(check).unwrap_err();
        assert_eq!(error.kind(), "missing_verified_artifact_identity_hash");
    }

    #[test]
    fn verified_only_sharing_task_dependency_release_rejects_candidate_identity_only() {
        let mut check =
            verified_only_sharing_check(VerifiedOnlySharingSurface::TaskDependencyRelease);
        check.verified_artifact_identity_hash = None;
        check.candidate_identity_hash = Some(&STALE_HASH_BYTES);

        let error = validate_verified_only_sharing(check).unwrap_err();
        assert_eq!(
            error.kind(),
            "candidate_identity_cannot_release_task_dependency"
        );
    }

    #[test]
    fn local_lemma_proof_task_handoff_builds_verified_artifact_before_available() {
        let typed = local_lemma_type_checked();
        let handoff = local_lemma_proof_task_handoff();
        validate_local_lemma_proof_task_handoff(&handoff).unwrap();
        assert_eq!(handoff.module, "Proofs.Ai.SketchLifecycle");
        assert_eq!(handoff.target_proof_corpus_module, handoff.module);
        assert!(handoff
            .expected_verification_commands
            .iter()
            .all(|command| !command.package_metadata));
        assert!(handoff
            .expected_verification_commands
            .iter()
            .any(|command| {
                command.kind == LocalLemmaVerificationCommandKind::VerifyModuleSourceFree
                    && command.verified_cache_authoring
            }));

        let task = local_lemma_proof_task_from_handoff(&typed, &handoff).unwrap();
        assert_eq!(task.task_identity.statement_hash, handoff.statement_hash);
        assert_eq!(
            task.task_identity.available_dependency_identities,
            handoff.dependency_identities
        );

        let artifact = local_lemma_verified_artifact_record(&handoff);
        let outcome = LocalLemmaProofTaskOutcome {
            handoff_hash: handoff.handoff_hash,
            status: LocalLemmaProofTaskStatus::SourceFreeVerified,
            parent_hole: LocalLemmaParentHoleDisposition::Available,
            verified_artifact: Some(artifact.clone()),
        };
        validate_local_lemma_proof_task_outcome(&handoff, &outcome).unwrap();

        let verified = local_lemma_verified_from_handoff(&handoff, &artifact).unwrap();
        assert_eq!(
            verified.proof_artifact_identity.candidate_hash,
            handoff.handoff_hash
        );
        assert_eq!(
            verified.proof_artifact_identity.certificate_hash,
            artifact.certificate_hash
        );
        assert_eq!(
            verified.proof_artifact_identity.export_hash,
            artifact.export_hash
        );
        assert_eq!(artifact.declaration_interface_hash, test_hash(0xa2));
        assert_eq!(artifact.source_hash, test_hash(0xa3));
        assert_eq!(
            artifact.replay_path,
            "Proofs/Ai/SketchLifecycle/replay.json"
        );

        let available = LocalLemmaLifecycleState::Available(
            local_lemma_available_from_verified(&verified).unwrap(),
        );
        validate_local_lemma_verified_only_sharing(
            &available,
            VerifiedOnlySharingSurface::ParentProofDependency,
        )
        .unwrap();
    }

    #[test]
    fn local_lemma_proof_task_handoff_rejects_unproved_theorem_storage() {
        for storage_kind in [
            LocalLemmaUnprovedStorageKind::ProofCorpusTheoremDeclaration,
            LocalLemmaUnprovedStorageKind::L1EvidencePackage,
            LocalLemmaUnprovedStorageKind::VerifiedArtifactIdentity,
        ] {
            let mut handoff = local_lemma_proof_task_handoff();
            handoff.unproved_storage_kind = storage_kind;
            handoff.handoff_hash = local_lemma_proof_task_handoff_hash(&handoff);
            let error = validate_local_lemma_proof_task_handoff(&handoff).unwrap_err();
            assert_eq!(
                error.kind(),
                &LocalLemmaProofTaskHandoffErrorKind::UnprovedStorageKindNotSidecar {
                    storage_kind,
                }
            );
        }
    }

    #[test]
    fn local_lemma_proof_task_handoff_rejects_package_metadata_and_stale_artifacts() {
        let mut handoff = local_lemma_proof_task_handoff();
        handoff.expected_verification_commands[0].package_metadata = true;
        handoff.expected_verification_commands[0].command_hash =
            local_lemma_expected_verification_command_hash(
                &handoff.expected_verification_commands[0],
            );
        handoff.handoff_hash = local_lemma_proof_task_handoff_hash(&handoff);
        let error = validate_local_lemma_proof_task_handoff(&handoff).unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaProofTaskHandoffErrorKind::PackageMetadataNotAllowed {
                kind: LocalLemmaVerificationCommandKind::BuildModule,
            }
        ));

        let mut handoff = local_lemma_proof_task_handoff();
        handoff.expected_verification_commands[0].verified_cache_authoring = true;
        handoff.expected_verification_commands[0].command_hash =
            local_lemma_expected_verification_command_hash(
                &handoff.expected_verification_commands[0],
            );
        handoff.handoff_hash = local_lemma_proof_task_handoff_hash(&handoff);
        let error = validate_local_lemma_proof_task_handoff(&handoff).unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaProofTaskHandoffErrorKind::VerifiedCacheAuthoringNotAllowed {
                kind: LocalLemmaVerificationCommandKind::BuildModule,
            }
        ));

        let handoff = local_lemma_proof_task_handoff();
        let mut artifact = local_lemma_verified_artifact_record(&handoff);
        artifact.source_hash = test_hash(0xfe);
        let error = validate_local_lemma_verified_artifact_record(&handoff, &artifact).unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaProofTaskHandoffErrorKind::HashMismatch {
                field: LocalLemmaProofTaskHandoffField::ArtifactRecordHash,
                ..
            }
        ));
    }

    #[test]
    fn local_lemma_proof_task_handoff_keeps_failed_cancelled_blocked_unresolved() {
        let handoff = local_lemma_proof_task_handoff();
        let artifact = local_lemma_verified_artifact_record(&handoff);

        for status in [
            LocalLemmaProofTaskStatus::Failed,
            LocalLemmaProofTaskStatus::Cancelled,
            LocalLemmaProofTaskStatus::Blocked,
        ] {
            let unresolved = LocalLemmaProofTaskOutcome {
                handoff_hash: handoff.handoff_hash,
                status,
                parent_hole: LocalLemmaParentHoleDisposition::Unresolved,
                verified_artifact: None,
            };
            validate_local_lemma_proof_task_outcome(&handoff, &unresolved).unwrap();

            let exposes_parent = LocalLemmaProofTaskOutcome {
                handoff_hash: handoff.handoff_hash,
                status,
                parent_hole: LocalLemmaParentHoleDisposition::Available,
                verified_artifact: None,
            };
            let error =
                validate_local_lemma_proof_task_outcome(&handoff, &exposes_parent).unwrap_err();
            assert!(matches!(
                error.kind(),
                LocalLemmaProofTaskHandoffErrorKind::ParentHoleMustRemainUnresolved { .. }
            ));

            let creates_artifact = LocalLemmaProofTaskOutcome {
                handoff_hash: handoff.handoff_hash,
                status,
                parent_hole: LocalLemmaParentHoleDisposition::Unresolved,
                verified_artifact: Some(artifact.clone()),
            };
            let error =
                validate_local_lemma_proof_task_outcome(&handoff, &creates_artifact).unwrap_err();
            assert!(matches!(
                error.kind(),
                LocalLemmaProofTaskHandoffErrorKind::TheoremArtifactNotAllowed { .. }
            ));
        }

        let missing_artifact = LocalLemmaProofTaskOutcome {
            handoff_hash: handoff.handoff_hash,
            status: LocalLemmaProofTaskStatus::SourceFreeVerified,
            parent_hole: LocalLemmaParentHoleDisposition::Available,
            verified_artifact: None,
        };
        let error =
            validate_local_lemma_proof_task_outcome(&handoff, &missing_artifact).unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaProofTaskHandoffErrorKind::MissingVerifiedArtifact { .. }
        ));
    }

    #[test]
    fn invented_candidate_typecheck_records_handoff_and_authoring_commands() {
        let request = invented_candidate_typecheck_request();

        let first = invented_candidate_typecheck(&request).unwrap();
        let second = invented_candidate_typecheck(&request).unwrap();
        assert_eq!(first, second);
        let InventedCandidateTypecheckOutcome::Accepted(handoff) = first else {
            panic!("valid typecheck witness should create a handoff");
        };
        validate_invented_candidate_typecheck_handoff(&request, &handoff).unwrap();

        assert!(handoff.can_create_proof_task());
        assert!(!handoff.creates_theorem_declaration);
        assert_eq!(handoff.statement_hash, request.statement_hash);
        assert_eq!(handoff.environment_hash, request.environment_hash);
        assert_eq!(handoff.axiom_policy_hash, request.axiom_policy_hash);
        assert_eq!(
            handoff.target_proof_corpus_module,
            "Proofs.Ai.LibraryGrowth"
        );
        assert_eq!(handoff.import_identities, request.import_identities);
        assert_eq!(
            handoff
                .expected_authoring_commands
                .iter()
                .map(|command| command.kind.as_str())
                .collect::<Vec<_>>(),
            vec!["build_module", "verify_module_source_free"]
        );
        assert!(handoff
            .expected_authoring_commands
            .iter()
            .all(|command| !command.package_metadata));
        assert!(handoff.expected_authoring_commands.iter().any(|command| {
            command.kind == TheoremInventionVerificationCommandKind::VerifyModuleSourceFree
                && command.verified_cache_authoring
        }));

        let mut tampered = handoff.clone();
        tampered.environment_hash = test_hash(0xfd);
        tampered.handoff_hash = invented_candidate_typecheck_handoff_hash(&tampered);
        let error = validate_invented_candidate_typecheck_handoff(&request, &tampered).unwrap_err();
        assert!(matches!(
            error.kind(),
            InventedCandidateTypecheckErrorKind::HashMismatch {
                field: InventedCandidateTypecheckField::EnvironmentHash,
                ..
            }
        ));

        let mut rejected_request = request.clone();
        rejected_request
            .typecheck_witness
            .as_mut()
            .expect("fixture has witness")
            .status = InventedCandidateTypecheckStatus::Rejected;
        refresh_invented_candidate_request_hash(&mut rejected_request);
        let mut rejected_handoff = handoff.clone();
        rejected_handoff.request_hash = rejected_request.request_hash;
        rejected_handoff.handoff_hash =
            invented_candidate_typecheck_handoff_hash(&rejected_handoff);
        let error =
            validate_invented_candidate_typecheck_handoff(&rejected_request, &rejected_handoff)
                .unwrap_err();
        assert!(matches!(
            error.kind(),
            InventedCandidateTypecheckErrorKind::TypecheckWitnessNotAccepted { .. }
        ));
    }

    #[test]
    fn invented_candidate_typecheck_blocks_repair_artifacts_without_theorem_declarations() {
        let mut ill_typed = invented_candidate_typecheck_request();
        let witness = ill_typed
            .typecheck_witness
            .as_mut()
            .expect("fixture has witness");
        witness.status = InventedCandidateTypecheckStatus::Rejected;
        witness.diagnostic_hash = Some(test_hash(0xfa));
        refresh_invented_candidate_request_hash(&mut ill_typed);
        assert_typecheck_blocker(
            &ill_typed,
            InventedCandidateTypecheckBlockerReason::IllTypedStatement,
        );

        let mut stale_environment = invented_candidate_typecheck_request();
        stale_environment
            .typecheck_witness
            .as_mut()
            .expect("fixture has witness")
            .environment_hash = test_hash(0xfb);
        refresh_invented_candidate_request_hash(&mut stale_environment);
        assert_typecheck_blocker(
            &stale_environment,
            InventedCandidateTypecheckBlockerReason::StaleEnvironment,
        );

        let mut missing_import = invented_candidate_typecheck_request();
        missing_import
            .import_identities
            .retain(|import| import.module != "Proofs.Ai.Eq");
        refresh_invented_candidate_request_hash(&mut missing_import);
        assert_typecheck_blocker(
            &missing_import,
            InventedCandidateTypecheckBlockerReason::MissingImport,
        );

        let mut widened_axiom = invented_candidate_typecheck_request();
        widened_axiom.axiom_policy_hash = test_hash(0xfc);
        widened_axiom.axiom_policy_widened = true;
        refresh_invented_candidate_request_hash(&mut widened_axiom);
        assert_typecheck_blocker(
            &widened_axiom,
            InventedCandidateTypecheckBlockerReason::WidenedAxiomPolicy,
        );
    }

    #[test]
    fn invented_candidate_rejects_conclusion_assumption_boundary() {
        let mut request = invented_candidate_typecheck_request();
        request.conclusion_assuming = true;
        refresh_invented_candidate_request_hash(&mut request);

        let outcome = invented_candidate_typecheck(&request).unwrap();
        let InventedCandidateTypecheckOutcome::Blocked(mut blocker) = outcome else {
            panic!("conclusion-assuming candidate must not be accepted");
        };
        assert_eq!(
            blocker.reason,
            InventedCandidateTypecheckBlockerReason::ConclusionAssumingBoundary
        );
        assert!(!blocker.creates_theorem_declaration);

        let mut mismatched_blocker = blocker.clone();
        mismatched_blocker.declaration_name = "wrong_boundary_name".to_owned();
        mismatched_blocker.blocker_hash =
            invented_candidate_typecheck_blocker_hash(&mismatched_blocker);
        let error = validate_invented_candidate_typecheck_blocker(&request, &mismatched_blocker)
            .unwrap_err();
        assert!(matches!(
            error.kind(),
            InventedCandidateTypecheckErrorKind::IdentifierMismatch {
                field: InventedCandidateTypecheckField::DeclarationName,
                ..
            }
        ));

        blocker.creates_theorem_declaration = true;
        blocker.blocker_hash = invented_candidate_typecheck_blocker_hash(&blocker);
        let error = validate_invented_candidate_typecheck_blocker(&request, &blocker).unwrap_err();
        assert_eq!(
            error.kind(),
            &InventedCandidateTypecheckErrorKind::BlockerCreatesTheoremDeclaration
        );
    }

    #[test]
    fn invented_lemma_proof_task_creation_reaches_available_after_source_free_artifact() {
        let (request, typecheck_handoff, task_handoff) =
            invented_lemma_proof_task_handoff_fixture();
        validate_invented_lemma_proof_task_handoff(&request, &typecheck_handoff, &task_handoff)
            .unwrap();
        assert_eq!(task_handoff.theorem_statement, request.normalized_statement);
        assert_eq!(
            task_handoff
                .expected_authoring_commands
                .iter()
                .map(|command| command.kind.as_str())
                .collect::<Vec<_>>(),
            vec![
                "build_module",
                "verify_module_source_free",
                "verify_changed_only_source_free",
                "check_corpus_authoring",
            ]
        );
        assert!(task_handoff
            .expected_authoring_commands
            .iter()
            .all(|command| !command.package_metadata));
        assert!(!task_handoff.package_side_effect_policy.package_lock_updated);
        assert!(
            !task_handoff
                .package_side_effect_policy
                .package_theorem_index_updated
        );
        assert!(!task_handoff.package_side_effect_policy.axiom_report_updated);
        assert!(!task_handoff.package_side_effect_policy.publish_plan_updated);
        assert!(!task_handoff.creates_theorem_declaration);

        let proof_task = invented_lemma_local_proof_task_from_handoff(
            &request,
            &typecheck_handoff,
            &task_handoff,
        )
        .unwrap();
        assert_eq!(
            proof_task.task_identity.available_dependency_identities,
            task_handoff.dependency_identities
        );
        let pre_verified = LocalLemmaLifecycleState::ProofTask(proof_task);
        let error = validate_local_lemma_verified_only_sharing(
            &pre_verified,
            VerifiedOnlySharingSurface::ParentProofDependency,
        )
        .unwrap_err();
        assert_eq!(error.kind(), "state_below_sharing_threshold");

        let local_handoff =
            invented_lemma_local_proof_task_handoff(&request, &typecheck_handoff, &task_handoff)
                .unwrap();
        let artifact = local_lemma_verified_artifact_record(&local_handoff);
        let readiness = invented_lemma_artifact_readiness(
            TheoremLevel::L2DerivedCertificate,
            true,
            true,
            true,
            true,
            true,
        );
        validate_invented_lemma_proof_task_outcome(
            &request,
            &typecheck_handoff,
            &task_handoff,
            LocalLemmaProofTaskStatus::SourceFreeVerified,
            LocalLemmaParentHoleDisposition::Available,
            Some(&artifact),
            Some(&readiness),
        )
        .unwrap();
        let verified = invented_lemma_verified_from_task(
            &request,
            &typecheck_handoff,
            &task_handoff,
            &artifact,
            &readiness,
        )
        .unwrap();
        let available = LocalLemmaLifecycleState::Available(
            local_lemma_available_from_verified(&verified).unwrap(),
        );
        validate_local_lemma_verified_only_sharing(
            &available,
            VerifiedOnlySharingSurface::ParentProofDependency,
        )
        .unwrap();
    }

    #[test]
    fn invented_lemma_proof_task_rejects_incomplete_artifact_readiness() {
        let (request, typecheck_handoff, task_handoff) =
            invented_lemma_proof_task_handoff_fixture();
        let local_handoff =
            invented_lemma_local_proof_task_handoff(&request, &typecheck_handoff, &task_handoff)
                .unwrap();
        let artifact = local_lemma_verified_artifact_record(&local_handoff);

        let missing_meta = invented_lemma_artifact_readiness(
            TheoremLevel::L2DerivedCertificate,
            true,
            true,
            false,
            true,
            true,
        );
        let error = invented_lemma_verified_from_task(
            &request,
            &typecheck_handoff,
            &task_handoff,
            &artifact,
            &missing_meta,
        )
        .unwrap_err();
        assert_eq!(
            error.kind(),
            &InventedLemmaProofTaskErrorKind::ArtifactNotReady {
                field: InventedLemmaProofTaskField::MetaArtifact,
            }
        );

        let non_l2 = invented_lemma_artifact_readiness(
            TheoremLevel::L1EvidencePackage,
            true,
            true,
            true,
            true,
            true,
        );
        let error = invented_lemma_verified_from_task(
            &request,
            &typecheck_handoff,
            &task_handoff,
            &artifact,
            &non_l2,
        )
        .unwrap_err();
        assert_eq!(
            error.kind(),
            &InventedLemmaProofTaskErrorKind::NonL2Artifact {
                theorem_level: TheoremLevel::L1EvidencePackage,
            }
        );

        let mut replay_mismatch = artifact.clone();
        replay_mismatch.replay_path = "Proofs/Ai/SketchLifecycle/other-replay.json".to_owned();
        replay_mismatch.artifact_record_hash =
            local_lemma_verified_artifact_record_hash(&replay_mismatch);
        let ready = invented_lemma_artifact_readiness(
            TheoremLevel::L2DerivedCertificate,
            true,
            true,
            true,
            true,
            true,
        );
        let error = invented_lemma_verified_from_task(
            &request,
            &typecheck_handoff,
            &task_handoff,
            &replay_mismatch,
            &ready,
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            InventedLemmaProofTaskErrorKind::IdentifierMismatch {
                field: InventedLemmaProofTaskField::ReplayPath,
                ..
            }
        ));
    }

    #[test]
    fn invented_lemma_proof_task_failed_cancelled_blocked_leave_no_artifact() {
        let (request, typecheck_handoff, task_handoff) =
            invented_lemma_proof_task_handoff_fixture();
        let local_handoff =
            invented_lemma_local_proof_task_handoff(&request, &typecheck_handoff, &task_handoff)
                .unwrap();
        let artifact = local_lemma_verified_artifact_record(&local_handoff);
        let readiness = invented_lemma_artifact_readiness(
            TheoremLevel::L2DerivedCertificate,
            true,
            true,
            true,
            true,
            true,
        );

        for status in [
            LocalLemmaProofTaskStatus::Failed,
            LocalLemmaProofTaskStatus::Cancelled,
            LocalLemmaProofTaskStatus::Blocked,
        ] {
            validate_invented_lemma_proof_task_outcome(
                &request,
                &typecheck_handoff,
                &task_handoff,
                status,
                LocalLemmaParentHoleDisposition::Unresolved,
                None,
                None,
            )
            .unwrap();

            let error = validate_invented_lemma_proof_task_outcome(
                &request,
                &typecheck_handoff,
                &task_handoff,
                status,
                LocalLemmaParentHoleDisposition::Unresolved,
                Some(&artifact),
                Some(&readiness),
            )
            .unwrap_err();
            assert_eq!(
                error.kind(),
                &InventedLemmaProofTaskErrorKind::TheoremArtifactNotAllowed { status }
            );
        }
    }

    #[test]
    fn invented_lemma_proof_task_rejects_package_metadata_side_effects() {
        let (request, typecheck_handoff, mut task_handoff) =
            invented_lemma_proof_task_handoff_fixture();
        task_handoff.package_side_effect_policy.axiom_report_updated = true;
        task_handoff.package_side_effect_policy.policy_hash =
            invented_lemma_package_side_effect_policy_hash(
                &task_handoff.package_side_effect_policy,
            );
        task_handoff.handoff_hash = invented_lemma_proof_task_handoff_hash(&task_handoff);

        let error =
            validate_invented_lemma_proof_task_handoff(&request, &typecheck_handoff, &task_handoff)
                .unwrap_err();
        assert_eq!(
            error.kind(),
            &InventedLemmaProofTaskErrorKind::PackageSideEffectNotAllowed {
                field: InventedLemmaProofTaskField::AxiomReportUpdated,
            }
        );

        let (request, typecheck_handoff, mut task_handoff) =
            invented_lemma_proof_task_handoff_fixture();
        task_handoff.expected_authoring_commands.swap(0, 1);
        task_handoff.handoff_hash = invented_lemma_proof_task_handoff_hash(&task_handoff);
        let error =
            validate_invented_lemma_proof_task_handoff(&request, &typecheck_handoff, &task_handoff)
                .unwrap_err();
        assert_eq!(
            error.kind(),
            &InventedLemmaProofTaskErrorKind::AuthoringCommandKindMismatch {
                index: 0,
                expected: InventedLemmaAuthoringCommandKind::BuildModule,
                actual: InventedLemmaAuthoringCommandKind::VerifyModuleSourceFree,
            }
        );
    }

    #[test]
    fn theorem_invention_artifact_contract_accepts_l2_and_hashes_inputs() {
        let artifact = theorem_invention_artifact(
            TheoremLevel::L2DerivedCertificate,
            TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
            TheoremInventionPromotionIntent::PromotionReady,
        );
        validate_theorem_invention_artifact(&artifact).unwrap();
        assert!(artifact.can_create_proof_corpus_theorem_artifact());
        let base_hash = artifact.identity_hash();

        let mut changed = artifact.clone();
        changed.statement_hash = test_hash(0xd0);
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.normalized_statement = "forall (A : Type) (x y : A), x = y -> y = x".to_owned();
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.generalized_context.binders[1].type_hash = test_hash(0xd1);
        changed.generalized_context.context_hash =
            theorem_invention_generalized_context_hash(&changed.generalized_context);
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.import_closure.push("Proofs.Ai.Prop".to_owned());
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.axiom_policy_hash = test_hash(0xd2);
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.replay_path = Some("proofs/Proofs/Ai/LibraryGrowth/replay-v2.json".to_owned());
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.certificate_path =
            Some("proofs/Proofs/Ai/LibraryGrowth/certificate-v2.npcert".to_owned());
        assert_ne!(base_hash, changed.identity_hash());

        let mut changed = artifact.clone();
        changed.theorem_level = TheoremLevel::L1EvidencePackage;
        assert_ne!(base_hash, changed.identity_hash());
    }

    #[test]
    fn theorem_invention_artifact_contract_rejects_non_l2_promotion_ready_candidates() {
        for theorem_level in [
            TheoremLevel::L0Statement,
            TheoremLevel::L1EvidencePackage,
            TheoremLevel::Unknown,
        ] {
            let mut artifact = theorem_invention_artifact(
                theorem_level,
                TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                TheoremInventionPromotionIntent::PromotionReady,
            );
            artifact.prerequisite_blocker = Some("missing upstream L2 theorem".to_owned());
            refresh_theorem_invention_artifact_hash(&mut artifact);
            let error = validate_theorem_invention_artifact(&artifact).unwrap_err();
            assert_eq!(
                error.kind(),
                &TheoremInventionArtifactErrorKind::ProofCorpusArtifactRequiresL2 { theorem_level }
            );
            assert!(!artifact.can_create_proof_corpus_theorem_artifact());
        }

        let mut unknown_without_blocker = theorem_invention_artifact(
            TheoremLevel::Unknown,
            TheoremInventionArtifactKind::CandidateSidecar,
            TheoremInventionPromotionIntent::AuthoringCandidate,
        );
        unknown_without_blocker.replay_path = None;
        unknown_without_blocker.replay_hash = None;
        unknown_without_blocker.certificate_path = None;
        unknown_without_blocker.certificate_hash = None;
        refresh_theorem_invention_artifact_hash(&mut unknown_without_blocker);
        let error = validate_theorem_invention_artifact(&unknown_without_blocker).unwrap_err();
        assert_eq!(
            error.kind(),
            &TheoremInventionArtifactErrorKind::NonL2CandidateNeedsPrerequisiteBlocker {
                theorem_level: TheoremLevel::Unknown
            }
        );

        let mut blocked_l1_sidecar = theorem_invention_artifact(
            TheoremLevel::L1EvidencePackage,
            TheoremInventionArtifactKind::CandidateSidecar,
            TheoremInventionPromotionIntent::BlockedPrerequisite,
        );
        blocked_l1_sidecar.prerequisite_blocker =
            Some("prove Proofs.Ai.Basic.generated_reflexivity first".to_owned());
        blocked_l1_sidecar.replay_path = None;
        blocked_l1_sidecar.replay_hash = None;
        blocked_l1_sidecar.certificate_path = None;
        blocked_l1_sidecar.certificate_hash = None;
        refresh_theorem_invention_artifact_hash(&mut blocked_l1_sidecar);
        validate_theorem_invention_artifact(&blocked_l1_sidecar).unwrap();
        assert!(!blocked_l1_sidecar.can_create_proof_corpus_theorem_artifact());

        let sidecar_ready = theorem_invention_artifact(
            TheoremLevel::L2DerivedCertificate,
            TheoremInventionArtifactKind::CandidateSidecar,
            TheoremInventionPromotionIntent::PromotionReady,
        );
        let error = validate_theorem_invention_artifact(&sidecar_ready).unwrap_err();
        assert_eq!(
            error.kind(),
            &TheoremInventionArtifactErrorKind::SidecarCannotBePromotionReady
        );
    }

    #[test]
    fn theorem_invention_artifact_contract_rejects_stale_or_unchecked_evidence() {
        let cases = [
            (
                "missing_replay",
                {
                    let mut artifact = theorem_invention_artifact(
                        TheoremLevel::L2DerivedCertificate,
                        TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                        TheoremInventionPromotionIntent::PromotionReady,
                    );
                    artifact.replay_path = None;
                    artifact.replay_hash = None;
                    refresh_theorem_invention_artifact_hash(&mut artifact);
                    artifact
                },
                TheoremInventionArtifactErrorKind::MissingReplay,
            ),
            (
                "missing_certificate",
                {
                    let mut artifact = theorem_invention_artifact(
                        TheoremLevel::L2DerivedCertificate,
                        TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                        TheoremInventionPromotionIntent::PromotionReady,
                    );
                    artifact.certificate_path = None;
                    artifact.certificate_hash = None;
                    refresh_theorem_invention_artifact_hash(&mut artifact);
                    artifact
                },
                TheoremInventionArtifactErrorKind::MissingCertificate,
            ),
            (
                "conclusion_assuming",
                {
                    let mut artifact = theorem_invention_artifact(
                        TheoremLevel::L2DerivedCertificate,
                        TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                        TheoremInventionPromotionIntent::PromotionReady,
                    );
                    artifact.conclusion_assuming = true;
                    refresh_theorem_invention_artifact_hash(&mut artifact);
                    artifact
                },
                TheoremInventionArtifactErrorKind::ConclusionAssuming,
            ),
            (
                "stale_replay",
                {
                    let mut artifact = theorem_invention_artifact(
                        TheoremLevel::L2DerivedCertificate,
                        TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                        TheoremInventionPromotionIntent::PromotionReady,
                    );
                    artifact.replay_is_stale = true;
                    refresh_theorem_invention_artifact_hash(&mut artifact);
                    artifact
                },
                TheoremInventionArtifactErrorKind::StaleReplay,
            ),
            (
                "stale_import",
                {
                    let mut artifact = theorem_invention_artifact(
                        TheoremLevel::L2DerivedCertificate,
                        TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                        TheoremInventionPromotionIntent::PromotionReady,
                    );
                    artifact.import_closure_is_stale = true;
                    refresh_theorem_invention_artifact_hash(&mut artifact);
                    artifact
                },
                TheoremInventionArtifactErrorKind::StaleImport,
            ),
            (
                "widened_axiom",
                {
                    let mut artifact = theorem_invention_artifact(
                        TheoremLevel::L2DerivedCertificate,
                        TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
                        TheoremInventionPromotionIntent::PromotionReady,
                    );
                    artifact.axiom_policy_widened = true;
                    refresh_theorem_invention_artifact_hash(&mut artifact);
                    artifact
                },
                TheoremInventionArtifactErrorKind::WidenedAxiomPolicy,
            ),
        ];

        for (name, artifact, expected_kind) in cases {
            let error = match validate_theorem_invention_artifact(&artifact) {
                Ok(()) => panic!("{name} should be rejected"),
                Err(error) => error,
            };
            assert_eq!(error.kind(), &expected_kind, "{name}");
        }

        let mut artifact = theorem_invention_artifact(
            TheoremLevel::L2DerivedCertificate,
            TheoremInventionArtifactKind::ProofCorpusTheoremArtifact,
            TheoremInventionPromotionIntent::PromotionReady,
        );
        artifact.verification_commands[0].package_metadata = true;
        artifact.verification_commands[0].command_hash =
            theorem_invention_verification_command_hash(&artifact.verification_commands[0]);
        refresh_theorem_invention_artifact_hash(&mut artifact);
        let error = validate_theorem_invention_artifact(&artifact).unwrap_err();
        assert!(matches!(
            error.kind(),
            TheoremInventionArtifactErrorKind::PackageMetadataNotAllowed {
                kind: TheoremInventionVerificationCommandKind::BuildModule,
            }
        ));
    }

    #[test]
    fn local_lemma_lifecycle_accepts_ordered_state_machine_and_available_sharing() {
        let proposed = LocalLemmaLifecycleState::Proposed(local_lemma_proposed());
        let typed = LocalLemmaLifecycleState::TypeChecked(local_lemma_type_checked());
        let task = LocalLemmaLifecycleState::ProofTask(local_lemma_proof_task());
        let verified = LocalLemmaLifecycleState::Verified(local_lemma_verified());
        let available = LocalLemmaLifecycleState::Available(
            local_lemma_available_from_verified(match &verified {
                LocalLemmaLifecycleState::Verified(verified) => verified,
                _ => unreachable!(),
            })
            .unwrap(),
        );

        validate_local_lemma_lifecycle_transition(&proposed, &typed).unwrap();
        validate_local_lemma_lifecycle_transition(&typed, &task).unwrap();
        validate_local_lemma_lifecycle_transition(&task, &verified).unwrap();
        validate_local_lemma_lifecycle_transition(&verified, &available).unwrap();

        let available_state = match &available {
            LocalLemmaLifecycleState::Available(available) => available,
            _ => unreachable!(),
        };
        assert_eq!(
            available_state.verified_theorem_identity_hash,
            available_state.verified_theorem_identity.hash()
        );
        assert_eq!(
            available_state.verified_theorem_identity.certificate_hash,
            test_hash(20)
        );
        assert_ne!(
            available_state
                .available_dependency_identity
                .dependency_identity_hash,
            available_state.sketch_hash
        );

        for surface in [
            VerifiedOnlySharingSurface::Premise,
            VerifiedOnlySharingSurface::BlackboardVerifiedFact,
            VerifiedOnlySharingSurface::TaskDependencyRelease,
            VerifiedOnlySharingSurface::ParentProofDependency,
        ] {
            let dependency =
                validate_local_lemma_verified_only_sharing(&available, surface).unwrap();
            assert_eq!(dependency, available_state.available_dependency_identity);
        }
    }

    #[test]
    fn local_lemma_lifecycle_rejects_invalid_transitions_and_identity_mismatches() {
        let proposed = LocalLemmaLifecycleState::Proposed(local_lemma_proposed());
        let task = LocalLemmaLifecycleState::ProofTask(local_lemma_proof_task());
        let error = validate_local_lemma_lifecycle_transition(&proposed, &task).unwrap_err();
        assert_eq!(
            error.kind(),
            &LocalLemmaLifecycleErrorKind::InvalidTransition {
                from: LocalLemmaLifecyclePhase::Proposed,
                to: LocalLemmaLifecyclePhase::ProofTask,
            }
        );

        let mut stale_type_checked = local_lemma_type_checked();
        stale_type_checked.statement_hash = test_hash(0xee);
        let error = validate_local_lemma_lifecycle_transition(
            &proposed,
            &LocalLemmaLifecycleState::TypeChecked(stale_type_checked),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaLifecycleErrorKind::HashMismatch {
                field: LocalLemmaLifecycleIdentityField::StatementHash,
                ..
            }
        ));

        let typed = LocalLemmaLifecycleState::TypeChecked(local_lemma_type_checked());
        let mut bad_task = local_lemma_proof_task();
        bad_task.task_identity.task_identity_hash = test_hash(0xef);
        let error = validate_local_lemma_lifecycle_transition(
            &typed,
            &LocalLemmaLifecycleState::ProofTask(bad_task),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaLifecycleErrorKind::HashMismatch {
                field: LocalLemmaLifecycleIdentityField::TaskIdentityHash,
                ..
            }
        ));

        let mut weak_dependency_task = local_lemma_proof_task();
        weak_dependency_task
            .task_identity
            .available_dependency_identities[0]
            .state = ProofAcceptanceState::ReplayVerified;
        weak_dependency_task
            .task_identity
            .available_dependency_identities[0]
            .dependency_identity_hash = local_lemma_available_dependency_identity_hash(
            &weak_dependency_task
                .task_identity
                .available_dependency_identities[0],
        );
        weak_dependency_task.task_identity.task_identity_hash =
            local_lemma_proof_task_identity_hash(&weak_dependency_task.task_identity);
        let error = validate_local_lemma_lifecycle_transition(
            &typed,
            &LocalLemmaLifecycleState::ProofTask(weak_dependency_task),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaLifecycleErrorKind::DependencyNotSharable {
                error_kind: "state_below_sharing_threshold",
                ..
            }
        ));

        let verified = local_lemma_verified();
        let mut available = local_lemma_available_from_verified(&verified).unwrap();
        available
            .task_identity
            .available_dependency_identities
            .push(local_lemma_available_dependency(0x70));
        available.task_identity.task_identity_hash =
            local_lemma_proof_task_identity_hash(&available.task_identity);
        let error = validate_local_lemma_lifecycle_transition(
            &LocalLemmaLifecycleState::Verified(verified),
            &LocalLemmaLifecycleState::Available(available),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaLifecycleErrorKind::HashMismatch {
                field: LocalLemmaLifecycleIdentityField::TaskIdentityHash,
                ..
            }
        ));

        let mut status_mismatch = local_lemma_verified();
        status_mismatch.source_free_verifier_result.status =
            ProofAcceptanceState::IndependentVerified;
        status_mismatch.source_free_verifier_result.result_hash =
            local_lemma_source_free_verifier_result_hash(
                &status_mismatch.source_free_verifier_result,
            );
        let error = validate_local_lemma_lifecycle_transition(
            &task,
            &LocalLemmaLifecycleState::Verified(status_mismatch),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaLifecycleErrorKind::StateMismatch {
                field: LocalLemmaLifecycleIdentityField::SourceFreeVerifierResultStatus,
                ..
            }
        ));

        let verified = local_lemma_verified();
        let mut available = local_lemma_available_from_verified(&verified).unwrap();
        available.available_dependency_identity.state = ProofAcceptanceState::IndependentVerified;
        available
            .available_dependency_identity
            .dependency_identity_hash = local_lemma_available_dependency_identity_hash(
            &available.available_dependency_identity,
        );
        let error = validate_local_lemma_lifecycle_transition(
            &LocalLemmaLifecycleState::Verified(verified),
            &LocalLemmaLifecycleState::Available(available),
        )
        .unwrap_err();
        assert!(matches!(
            error.kind(),
            LocalLemmaLifecycleErrorKind::StateMismatch {
                field: LocalLemmaLifecycleIdentityField::AvailableDependencyState,
                ..
            }
        ));
    }

    #[test]
    fn local_lemma_lifecycle_rejects_pre_verified_and_pre_available_sharing() {
        let states = [
            LocalLemmaLifecycleState::Proposed(local_lemma_proposed()),
            LocalLemmaLifecycleState::TypeChecked(local_lemma_type_checked()),
            LocalLemmaLifecycleState::ProofTask(local_lemma_proof_task()),
        ];

        for state in &states {
            for surface in [
                VerifiedOnlySharingSurface::Premise,
                VerifiedOnlySharingSurface::BlackboardVerifiedFact,
                VerifiedOnlySharingSurface::TaskDependencyRelease,
                VerifiedOnlySharingSurface::ParentProofDependency,
            ] {
                let error = validate_local_lemma_verified_only_sharing(state, surface).unwrap_err();
                assert_eq!(error.kind(), "state_below_sharing_threshold");
                let check = local_lemma_verified_only_sharing_check(state, surface);
                assert_eq!(
                    check.artifact_kind,
                    VerifiedOnlySharingArtifactKind::UnverifiedLocalLemma
                );
            }
        }

        let verified = LocalLemmaLifecycleState::Verified(local_lemma_verified());
        let error = validate_local_lemma_verified_only_sharing(
            &verified,
            VerifiedOnlySharingSurface::ParentProofDependency,
        )
        .unwrap_err();
        assert_eq!(error.kind(), "artifact_kind_not_sharable");
    }

    #[test]
    fn local_lemma_lifecycle_replay_verified_or_tactic_success_is_not_available() {
        let task = LocalLemmaLifecycleState::ProofTask(local_lemma_proof_task());
        let replay_only_verified = LocalLemmaLifecycleState::Verified(
            local_lemma_verified_with_status(ProofAcceptanceState::ReplayVerified),
        );
        let error =
            validate_local_lemma_lifecycle_transition(&task, &replay_only_verified).unwrap_err();
        assert_eq!(
            error.kind(),
            &LocalLemmaLifecycleErrorKind::SourceFreeVerifierResultNotVerified {
                status: ProofAcceptanceState::ReplayVerified,
            }
        );

        let replay_only = match &replay_only_verified {
            LocalLemmaLifecycleState::Verified(verified) => verified,
            _ => unreachable!(),
        };
        let error = local_lemma_available_from_verified(replay_only).unwrap_err();
        assert_eq!(
            error.kind(),
            &LocalLemmaLifecycleErrorKind::SourceFreeVerifierResultNotVerified {
                status: ProofAcceptanceState::ReplayVerified,
            }
        );
    }

    #[test]
    fn candidate_goal_fingerprint_changes_by_state_and_goal() {
        let base = proof_candidate_goal_fingerprint(test_hash(30), GoalId(0));

        assert_ne!(
            base,
            proof_candidate_goal_fingerprint(test_hash(31), GoalId(0))
        );
        assert_ne!(
            base,
            proof_candidate_goal_fingerprint(test_hash(30), GoalId(1))
        );
    }

    #[test]
    fn trust_component_inventory_round_trips_stable_wire_strings() {
        assert_eq!(ProofTrustComponent::all().len(), 29);

        for component in ProofTrustComponent::all().iter().copied() {
            let wire = component.as_str();
            assert_eq!(component.to_string(), wire);
            assert_eq!(ProofTrustComponent::parse(wire).unwrap(), component);
            assert_eq!(wire.parse::<ProofTrustComponent>().unwrap(), component);
        }

        for classification in [
            ProofTrustClassification::Trusted,
            ProofTrustClassification::DeterministicValidation,
            ProofTrustClassification::UntrustedSidecar,
        ] {
            let wire = classification.as_str();
            assert_eq!(classification.to_string(), wire);
            assert_eq!(
                ProofTrustClassification::parse(wire).unwrap(),
                classification
            );
        }
    }

    #[test]
    fn trust_component_trusted_evidence_is_limited_to_closed_boundary() {
        let trusted_evidence = ProofTrustComponent::all()
            .iter()
            .copied()
            .filter(|component| component.may_serialize_as_trusted_evidence())
            .collect::<Vec<_>>();

        assert_eq!(
            trusted_evidence,
            vec![
                ProofTrustComponent::RustKernel,
                ProofTrustComponent::CanonicalCoreAst,
                ProofTrustComponent::CanonicalCertificate,
                ProofTrustComponent::CertificateVerifier,
                ProofTrustComponent::DesignatedIndependentChecker,
                ProofTrustComponent::DeterministicHashCheck,
                ProofTrustComponent::AxiomPolicyCheck,
                ProofTrustComponent::CoreFeatureCheck,
            ]
        );
    }

    #[test]
    fn trust_component_untrusted_sidecars_cannot_be_trusted_evidence() {
        for component in [
            ProofTrustComponent::Parser,
            ProofTrustComponent::Elaborator,
            ProofTrustComponent::Tactic,
            ProofTrustComponent::Automation,
            ProofTrustComponent::Plugin,
            ProofTrustComponent::AiModel,
            ProofTrustComponent::AgentWorker,
            ProofTrustComponent::TheoremSearch,
            ProofTrustComponent::PremiseRetrieval,
            ProofTrustComponent::SearchScore,
            ProofTrustComponent::TheoremGraphScore,
            ProofTrustComponent::Prompt,
            ProofTrustComponent::ModelOutput,
            ProofTrustComponent::ReplayLog,
            ProofTrustComponent::ReplaySidecar,
            ProofTrustComponent::TheoremIndex,
            ProofTrustComponent::SidecarIndex,
            ProofTrustComponent::Cache,
            ProofTrustComponent::SolverProcess,
            ProofTrustComponent::Diagnostic,
            ProofTrustComponent::BenchmarkSummary,
        ] {
            assert_eq!(
                component.classification(),
                ProofTrustClassification::UntrustedSidecar
            );
            assert!(!component.may_serialize_as_trusted_evidence());
            assert!(!component.may_claim_verified_state_on(ProofTrustContractSurface::Verification));
            assert!(!component.may_claim_verified_state_on(ProofTrustContractSurface::Integration));
        }
    }

    #[test]
    fn trust_component_candidate_contract_cannot_claim_verified_state() {
        for component in ProofTrustComponent::all().iter().copied() {
            assert!(!component.may_claim_verified_state_on(ProofTrustContractSurface::Candidate));
        }

        for component in [
            ProofTrustComponent::RustKernel,
            ProofTrustComponent::CanonicalCoreAst,
            ProofTrustComponent::CanonicalCertificate,
            ProofTrustComponent::CertificateVerifier,
            ProofTrustComponent::DesignatedIndependentChecker,
            ProofTrustComponent::DeterministicHashCheck,
            ProofTrustComponent::AxiomPolicyCheck,
            ProofTrustComponent::CoreFeatureCheck,
        ] {
            assert!(component.may_claim_verified_state_on(ProofTrustContractSurface::Verification));
            assert!(component.may_claim_verified_state_on(ProofTrustContractSurface::Integration));
        }
    }

    #[test]
    fn trust_transition_accepts_every_ordered_edge() {
        for edge in PROOF_ACCEPTANCE_TRANSITION_EDGES {
            validate_proof_acceptance_transition(valid_transition(
                edge.from_state,
                edge.to_state,
                edge.actor_role,
            ))
            .unwrap();
        }
    }

    #[test]
    fn trust_transition_rejects_missing_previous_artifact_hash() {
        let mut transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceActorRole::VerifierWorker,
        );
        transition.previous_artifact_hash = None;

        assert_eq!(
            validate_proof_acceptance_transition(transition).unwrap_err(),
            ProofAcceptanceTransitionError::MissingPreviousArtifactHash {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::ReplayVerified,
            }
        );
    }

    #[test]
    fn trust_transition_rejects_missing_next_artifact_hash() {
        let mut transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceActorRole::VerifierWorker,
        );
        transition.next_artifact_hash = None;

        assert_eq!(
            validate_proof_acceptance_transition(transition).unwrap_err(),
            ProofAcceptanceTransitionError::MissingNextArtifactHash {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::ReplayVerified,
            }
        );
    }

    #[test]
    fn trust_transition_rejects_missing_policy_hash() {
        let mut transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceActorRole::VerifierWorker,
        );
        transition.policy_hash = Some("");

        assert_eq!(
            validate_proof_acceptance_transition(transition).unwrap_err(),
            ProofAcceptanceTransitionError::MissingPolicyHash {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::ReplayVerified,
            }
        );
    }

    #[test]
    fn trust_transition_rejects_role_mismatch() {
        let transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceActorRole::AgentWorker,
        );

        assert_eq!(
            validate_proof_acceptance_transition(transition).unwrap_err(),
            ProofAcceptanceTransitionError::RoleMismatch {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::ReplayVerified,
                expected_role: ProofAcceptanceActorRole::VerifierWorker,
                actual_role: ProofAcceptanceActorRole::AgentWorker,
            }
        );
    }

    #[test]
    fn trust_transition_rejects_stale_input_hash() {
        let mut transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceActorRole::VerifierWorker,
        );
        transition.expected_previous_artifact_hash = Some(STALE_HASH);

        assert_eq!(
            validate_proof_acceptance_transition(transition).unwrap_err(),
            ProofAcceptanceTransitionError::StaleInputHash {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::ReplayVerified,
                expected_previous_artifact_hash: STALE_HASH.to_owned(),
                actual_previous_artifact_hash: PREVIOUS_HASH.to_owned(),
            }
        );
    }

    #[test]
    fn trust_transition_matrix_snapshot_rows_are_sorted() {
        let rows = proof_acceptance_transition_matrix_snapshot_rows();
        let mut sorted = rows.clone();
        sorted.sort();
        assert_eq!(rows, sorted);
    }

    #[test]
    fn trust_forbidden_proof_candidate_to_integrated_is_rejected() {
        let transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::Integrated,
            ProofAcceptanceActorRole::Integrator,
        );

        assert_eq!(
            assert_forbidden_transition(transition),
            ProofAcceptanceTransitionError::ForbiddenTransition {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::Integrated,
            }
        );
    }

    #[test]
    fn trust_forbidden_smt_unsat_to_certificate_verified_is_rejected() {
        let transition = valid_transition(
            ProofAcceptanceState::ProofCandidate,
            ProofAcceptanceState::CertificateVerified,
            ProofAcceptanceActorRole::VerifierWorker,
        );

        assert_eq!(
            assert_forbidden_transition(transition),
            ProofAcceptanceTransitionError::ForbiddenTransition {
                from_state: ProofAcceptanceState::ProofCandidate,
                to_state: ProofAcceptanceState::CertificateVerified,
            }
        );
    }

    #[test]
    fn trust_forbidden_high_agent_confidence_to_verified_is_rejected() {
        assert!(ProofAcceptanceState::parse("verified").is_err());

        let transition = valid_transition(
            ProofAcceptanceState::TypeChecked,
            ProofAcceptanceState::CertificateVerified,
            ProofAcceptanceActorRole::AgentWorker,
        );
        assert_eq!(
            assert_forbidden_transition(transition),
            ProofAcceptanceTransitionError::ForbiddenTransition {
                from_state: ProofAcceptanceState::TypeChecked,
                to_state: ProofAcceptanceState::CertificateVerified,
            }
        );
    }

    #[test]
    fn trust_forbidden_replay_sidecar_exists_to_verified_is_rejected() {
        assert!(ProofAcceptanceState::parse("verified").is_err());

        let transition = valid_transition(
            ProofAcceptanceState::ReplayVerified,
            ProofAcceptanceState::CertificateVerified,
            ProofAcceptanceActorRole::VerifierWorker,
        );
        assert_eq!(
            assert_forbidden_transition(transition),
            ProofAcceptanceTransitionError::ForbiddenTransition {
                from_state: ProofAcceptanceState::ReplayVerified,
                to_state: ProofAcceptanceState::CertificateVerified,
            }
        );
    }

    #[test]
    fn trust_forbidden_cache_hit_to_published_is_rejected() {
        let transition = valid_transition(
            ProofAcceptanceState::CertificateVerified,
            ProofAcceptanceState::Published,
            ProofAcceptanceActorRole::ReleaseController,
        );

        assert_eq!(
            assert_forbidden_transition(transition),
            ProofAcceptanceTransitionError::ForbiddenTransition {
                from_state: ProofAcceptanceState::CertificateVerified,
                to_state: ProofAcceptanceState::Published,
            }
        );
    }
}
