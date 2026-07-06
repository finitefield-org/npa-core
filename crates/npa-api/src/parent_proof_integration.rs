use crate::proof_skeleton::{proof_skeleton_hash, ProofSkeleton};
use crate::trust::{
    local_lemma_available_dependency_identity_hash, validate_verified_artifact_identity,
    LocalLemmaAvailableDependencyIdentity, ProofAcceptanceState, VerifiedArtifactIdentity,
};
use npa_cert::Hash;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt;

pub const PARENT_PROOF_DECLARATION_IDENTITY_HASH_DOMAIN: &str =
    "npa.parent-proof.declaration-identity.v1";
pub const PARENT_PROOF_IMPORT_IDENTITY_HASH_DOMAIN: &str = "npa.parent-proof.import-identity.v1";
pub const PARENT_PROOF_DEPENDENCY_IDENTITY_HASH_DOMAIN: &str =
    "npa.parent-proof.dependency-identity.v1";
pub const PARENT_PROOF_IMPORT_CLOSURE_HASH_DOMAIN: &str = "npa.parent-proof.import-closure.v1";
pub const PARENT_PROOF_SUBSTITUTION_HASH_DOMAIN: &str = "npa.parent-proof.substitution.v1";
pub const PARENT_PROOF_COMPLETED_CANDIDATE_HASH_DOMAIN: &str =
    "npa.parent-proof.completed-candidate.v1";
pub const PARENT_PROOF_INTEGRATION_OUTPUT_HASH_DOMAIN: &str =
    "npa.parent-proof.integration-output.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParentProofDependencyKind {
    HoleProof,
    LocalLemma,
}

impl ParentProofDependencyKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::HoleProof => "hole_proof",
            Self::LocalLemma => "local_lemma",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParentProofVerifierStatus {
    CertificateVerified,
    IndependentVerified,
    Integrated,
    Published,
    CheckerDisagreement,
}

impl ParentProofVerifierStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CertificateVerified => "certificate_verified",
            Self::IndependentVerified => "independent_verified",
            Self::Integrated => "integrated",
            Self::Published => "published",
            Self::CheckerDisagreement => "checker_disagreement",
        }
    }

    pub const fn acceptance_state(self) -> Option<ProofAcceptanceState> {
        match self {
            Self::CertificateVerified => Some(ProofAcceptanceState::CertificateVerified),
            Self::IndependentVerified => Some(ProofAcceptanceState::IndependentVerified),
            Self::Integrated => Some(ProofAcceptanceState::Integrated),
            Self::Published => Some(ProofAcceptanceState::Published),
            Self::CheckerDisagreement => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParentProofTypecheckStatus {
    NotRun,
    Rejected,
    Accepted,
}

impl ParentProofTypecheckStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotRun => "not_run",
            Self::Rejected => "rejected",
            Self::Accepted => "accepted",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofDeclarationIdentity {
    pub module: String,
    pub declaration: String,
    pub declaration_interface_hash: Hash,
    pub declaration_identity_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofImportIdentity {
    pub module: String,
    pub certificate_hash: Hash,
    pub export_hash: Hash,
    pub import_identity_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofDependencyIdentity {
    pub dependency_hash: Hash,
    pub kind: ParentProofDependencyKind,
    pub dependency_id: String,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub environment_hash: Hash,
    pub declaration_identity: ParentProofDeclarationIdentity,
    pub certificate_hash: Hash,
    pub export_hash: Hash,
    pub import_identities: Vec<ParentProofImportIdentity>,
    pub axiom_policy_hash: Hash,
    pub axiom_report_hash: Hash,
    pub verifier_status: ParentProofVerifierStatus,
    pub source_free_verifier_result_hash: Option<Hash>,
    pub verified_artifact_identity: VerifiedArtifactIdentity,
    pub verified_artifact_identity_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParentProofSubstitutionSlot {
    Hole {
        hole_id: String,
        expected_output_hash: Hash,
    },
    LocalLemma {
        lemma_id: String,
        available_dependency_identity: Option<LocalLemmaAvailableDependencyIdentity>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofSubstitution {
    pub slot: ParentProofSubstitutionSlot,
    pub expected_dependency_hash: Hash,
    pub dependency: ParentProofDependencyIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofCompletedCandidate {
    pub candidate_hash: Hash,
    pub base_sketch_hash: Hash,
    pub skeleton_hash: Hash,
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub completed_core_expr_hash: Hash,
    pub environment_hash: Hash,
    pub import_closure_hash: Hash,
    pub axiom_policy_hash: Hash,
    pub dependency_identity_hashes: Vec<Hash>,
    pub substitution_hashes: Vec<Hash>,
    pub typecheck_status: ParentProofTypecheckStatus,
    pub typecheck_result_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofIntegrationInput {
    pub base_sketch_hash: Hash,
    pub skeleton: ProofSkeleton,
    pub substitutions: Vec<ParentProofSubstitution>,
    pub completed_candidate: ParentProofCompletedCandidate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofIntegrationOutput {
    pub integration_hash: Hash,
    pub base_sketch_hash: Hash,
    pub skeleton_hash: Hash,
    pub ordered_substitutions: Vec<ParentProofSubstitution>,
    pub completed_candidate: ParentProofCompletedCandidate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentProofIntegrationError {
    kind: Box<ParentProofIntegrationErrorKind>,
    affected: Box<ParentProofIntegrationAffected>,
}

impl ParentProofIntegrationError {
    fn new(
        kind: ParentProofIntegrationErrorKind,
        affected: ParentProofIntegrationAffected,
    ) -> Self {
        Self {
            kind: Box::new(kind),
            affected: Box::new(affected),
        }
    }

    pub fn kind(&self) -> &ParentProofIntegrationErrorKind {
        self.kind.as_ref()
    }

    pub fn affected(&self) -> &ParentProofIntegrationAffected {
        self.affected.as_ref()
    }
}

impl fmt::Display for ParentProofIntegrationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.as_str())
    }
}

impl std::error::Error for ParentProofIntegrationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParentProofIntegrationAffected {
    ParentCandidate,
    Hole { hole_id: String },
    LocalLemmaReference { lemma_id: String },
    Dependency { dependency_id: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParentProofIntegrationErrorKind {
    EmptyIdentifier {
        field: ParentProofIntegrationField,
    },
    DeclarationIdentityHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    ImportIdentityHashMismatch {
        module: String,
        expected: Hash,
        actual: Hash,
    },
    DependencyIdentityHashMismatch {
        dependency_id: String,
        expected: Hash,
        actual: Hash,
    },
    DuplicateSubstitutionSlot {
        slot_id: String,
    },
    UnknownHoleSubstitution {
        hole_id: String,
    },
    MissingHoleSubstitution {
        hole_id: String,
    },
    LocalLemmaNameOnly {
        lemma_id: String,
    },
    DependencyKindMismatch {
        dependency_id: String,
        expected: ParentProofDependencyKind,
        actual: ParentProofDependencyKind,
    },
    StaleLemmaIdentity {
        lemma_id: String,
    },
    StaleImportIdentity,
    CheckerDisagreement {
        dependency_id: String,
    },
    MissingSourceFreeVerifierResult {
        dependency_id: String,
    },
    WrongExpectedType {
        slot_id: String,
        expected: Hash,
        actual: Hash,
    },
    ChangedAxiomProfile {
        dependency_id: String,
        expected: Hash,
        actual: Hash,
    },
    VerifiedArtifactIdentityInvalid {
        dependency_id: String,
        error_kind: &'static str,
    },
    CandidateSkeletonMismatch {
        expected: Hash,
        actual: Hash,
    },
    CandidateDependencyOrderMismatch,
    CandidateHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    CandidateTypecheckRequired {
        status: ParentProofTypecheckStatus,
    },
}

impl ParentProofIntegrationErrorKind {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::EmptyIdentifier { .. } => "empty_identifier",
            Self::DeclarationIdentityHashMismatch { .. } => "declaration_identity_hash_mismatch",
            Self::ImportIdentityHashMismatch { .. } => "import_identity_hash_mismatch",
            Self::DependencyIdentityHashMismatch { .. } => "dependency_identity_hash_mismatch",
            Self::DuplicateSubstitutionSlot { .. } => "duplicate_substitution_slot",
            Self::UnknownHoleSubstitution { .. } => "unknown_hole_substitution",
            Self::MissingHoleSubstitution { .. } => "missing_hole_substitution",
            Self::LocalLemmaNameOnly { .. } => "local_lemma_name_only",
            Self::DependencyKindMismatch { .. } => "dependency_kind_mismatch",
            Self::StaleLemmaIdentity { .. } => "stale_lemma_identity",
            Self::StaleImportIdentity => "stale_import_identity",
            Self::CheckerDisagreement { .. } => "checker_disagreement",
            Self::MissingSourceFreeVerifierResult { .. } => "missing_source_free_verifier_result",
            Self::WrongExpectedType { .. } => "wrong_expected_type",
            Self::ChangedAxiomProfile { .. } => "changed_axiom_profile",
            Self::VerifiedArtifactIdentityInvalid { .. } => "verified_artifact_identity_invalid",
            Self::CandidateSkeletonMismatch { .. } => "candidate_skeleton_mismatch",
            Self::CandidateDependencyOrderMismatch => "candidate_dependency_order_mismatch",
            Self::CandidateHashMismatch { .. } => "candidate_hash_mismatch",
            Self::CandidateTypecheckRequired { .. } => "candidate_typecheck_required",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParentProofIntegrationField {
    Module,
    Declaration,
    DependencyId,
    HoleId,
    LemmaId,
}

pub fn parent_proof_declaration_identity_hash(identity: &ParentProofDeclarationIdentity) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_DECLARATION_IDENTITY_HASH_DOMAIN);
    encode_string(&mut out, &identity.module);
    encode_string(&mut out, &identity.declaration);
    encode_hash(&mut out, &identity.declaration_interface_hash);
    sha256_hash(&out)
}

pub fn parent_proof_import_identity_hash(identity: &ParentProofImportIdentity) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_IMPORT_IDENTITY_HASH_DOMAIN);
    encode_string(&mut out, &identity.module);
    encode_hash(&mut out, &identity.certificate_hash);
    encode_hash(&mut out, &identity.export_hash);
    sha256_hash(&out)
}

pub fn parent_proof_dependency_identity_hash(identity: &ParentProofDependencyIdentity) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_DEPENDENCY_IDENTITY_HASH_DOMAIN);
    encode_string(&mut out, identity.kind.as_str());
    encode_string(&mut out, &identity.dependency_id);
    encode_hash(&mut out, &identity.statement_hash);
    encode_hash(&mut out, &identity.expected_type_hash);
    encode_hash(&mut out, &identity.environment_hash);
    encode_hash(
        &mut out,
        &identity.declaration_identity.declaration_identity_hash,
    );
    encode_hash(&mut out, &identity.certificate_hash);
    encode_hash(&mut out, &identity.export_hash);
    let mut imports = identity.import_identities.clone();
    imports.sort_by_key(|import| import.import_identity_hash);
    encode_len(&mut out, imports.len());
    for import in &imports {
        encode_hash(&mut out, &import.import_identity_hash);
    }
    encode_hash(&mut out, &identity.axiom_policy_hash);
    encode_hash(&mut out, &identity.axiom_report_hash);
    encode_string(&mut out, identity.verifier_status.as_str());
    encode_option_hash(&mut out, identity.source_free_verifier_result_hash.as_ref());
    encode_hash(&mut out, &identity.verified_artifact_identity_hash);
    sha256_hash(&out)
}

pub fn parent_proof_import_closure_hash(substitutions: &[ParentProofSubstitution]) -> Hash {
    let mut imports = substitutions
        .iter()
        .flat_map(|substitution| substitution.dependency.import_identities.iter().cloned())
        .collect::<Vec<_>>();
    imports.sort_by(|left, right| {
        left.import_identity_hash
            .cmp(&right.import_identity_hash)
            .then_with(|| left.module.cmp(&right.module))
    });
    imports.dedup_by(|left, right| left.import_identity_hash == right.import_identity_hash);

    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_IMPORT_CLOSURE_HASH_DOMAIN);
    encode_len(&mut out, imports.len());
    for import in &imports {
        encode_hash(&mut out, &import.import_identity_hash);
    }
    sha256_hash(&out)
}

pub fn parent_proof_substitution_hash(substitution: &ParentProofSubstitution) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_SUBSTITUTION_HASH_DOMAIN);
    match &substitution.slot {
        ParentProofSubstitutionSlot::Hole {
            hole_id,
            expected_output_hash,
        } => {
            encode_string(&mut out, "hole");
            encode_string(&mut out, hole_id);
            encode_hash(&mut out, expected_output_hash);
        }
        ParentProofSubstitutionSlot::LocalLemma {
            lemma_id,
            available_dependency_identity,
        } => {
            encode_string(&mut out, "local_lemma");
            encode_string(&mut out, lemma_id);
            encode_option_hash(
                &mut out,
                available_dependency_identity
                    .as_ref()
                    .map(|identity| &identity.dependency_identity_hash),
            );
        }
    }
    encode_hash(&mut out, &substitution.expected_dependency_hash);
    encode_hash(&mut out, &substitution.dependency.dependency_hash);
    sha256_hash(&out)
}

pub fn parent_proof_completed_candidate_hash(candidate: &ParentProofCompletedCandidate) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_COMPLETED_CANDIDATE_HASH_DOMAIN);
    encode_hash(&mut out, &candidate.base_sketch_hash);
    encode_hash(&mut out, &candidate.skeleton_hash);
    encode_hash(&mut out, &candidate.statement_hash);
    encode_hash(&mut out, &candidate.expected_type_hash);
    encode_hash(&mut out, &candidate.completed_core_expr_hash);
    encode_hash(&mut out, &candidate.environment_hash);
    encode_hash(&mut out, &candidate.import_closure_hash);
    encode_hash(&mut out, &candidate.axiom_policy_hash);
    let mut dependencies = candidate.dependency_identity_hashes.clone();
    encode_len(&mut out, dependencies.len());
    for dependency_hash in dependencies.drain(..) {
        encode_hash(&mut out, &dependency_hash);
    }
    let mut substitution_hashes = candidate.substitution_hashes.clone();
    encode_len(&mut out, substitution_hashes.len());
    for substitution_hash in substitution_hashes.drain(..) {
        encode_hash(&mut out, &substitution_hash);
    }
    encode_string(&mut out, candidate.typecheck_status.as_str());
    encode_option_hash(&mut out, candidate.typecheck_result_hash.as_ref());
    sha256_hash(&out)
}

pub fn parent_proof_integration_output_hash(output: &ParentProofIntegrationOutput) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, PARENT_PROOF_INTEGRATION_OUTPUT_HASH_DOMAIN);
    encode_hash(&mut out, &output.base_sketch_hash);
    encode_hash(&mut out, &output.skeleton_hash);
    encode_len(&mut out, output.ordered_substitutions.len());
    for substitution in &output.ordered_substitutions {
        encode_hash(&mut out, &parent_proof_substitution_hash(substitution));
        encode_hash(&mut out, &substitution.dependency.dependency_hash);
    }
    encode_hash(&mut out, &output.completed_candidate.candidate_hash);
    sha256_hash(&out)
}

pub fn integrate_parent_proof(
    input: &ParentProofIntegrationInput,
) -> Result<ParentProofIntegrationOutput, ParentProofIntegrationError> {
    let skeleton_hash = proof_skeleton_hash(&input.skeleton);
    let ordered_substitutions = validate_and_order_substitutions(input)?;
    validate_completed_candidate(input, skeleton_hash, &ordered_substitutions)?;

    let mut output = ParentProofIntegrationOutput {
        integration_hash: [0; 32],
        base_sketch_hash: input.base_sketch_hash,
        skeleton_hash,
        ordered_substitutions,
        completed_candidate: input.completed_candidate.clone(),
    };
    output.integration_hash = parent_proof_integration_output_hash(&output);
    Ok(output)
}

fn validate_and_order_substitutions(
    input: &ParentProofIntegrationInput,
) -> Result<Vec<ParentProofSubstitution>, ParentProofIntegrationError> {
    let hole_by_id = input
        .skeleton
        .holes
        .iter()
        .map(|hole| (hole.hole_id.as_str(), hole))
        .collect::<BTreeMap<_, _>>();
    let mut substitution_by_slot = BTreeMap::new();

    for substitution in &input.substitutions {
        let slot_id = substitution_slot_key(&substitution.slot)?;
        if substitution_by_slot
            .insert(slot_id.clone(), substitution)
            .is_some()
        {
            return Err(ParentProofIntegrationError::new(
                ParentProofIntegrationErrorKind::DuplicateSubstitutionSlot { slot_id },
                ParentProofIntegrationAffected::ParentCandidate,
            ));
        }
    }

    for hole in &input.skeleton.holes {
        let slot_id = hole_slot_key(&hole.hole_id);
        if !substitution_by_slot.contains_key(&slot_id) {
            return Err(ParentProofIntegrationError::new(
                ParentProofIntegrationErrorKind::MissingHoleSubstitution {
                    hole_id: hole.hole_id.clone(),
                },
                ParentProofIntegrationAffected::Hole {
                    hole_id: hole.hole_id.clone(),
                },
            ));
        }
    }

    let mut local_lemma_substitutions = Vec::new();
    let mut hole_substitution_by_id = BTreeMap::new();

    for substitution in &input.substitutions {
        validate_substitution(substitution, input, &hole_by_id)?;
        match &substitution.slot {
            ParentProofSubstitutionSlot::Hole { hole_id, .. } => {
                hole_substitution_by_id.insert(hole_id.clone(), substitution.clone());
            }
            ParentProofSubstitutionSlot::LocalLemma { .. } => {
                local_lemma_substitutions.push(substitution.clone());
            }
        }
    }

    local_lemma_substitutions.sort_by(|left, right| {
        substitution_slot_order_key(&left.slot).cmp(&substitution_slot_order_key(&right.slot))
    });
    let mut ordered = local_lemma_substitutions;
    for hole_id in topological_hole_order(&input.skeleton)? {
        let Some(substitution) = hole_substitution_by_id.remove(&hole_id) else {
            continue;
        };
        ordered.push(substitution);
    }
    Ok(ordered)
}

fn validate_substitution(
    substitution: &ParentProofSubstitution,
    input: &ParentProofIntegrationInput,
    hole_by_id: &BTreeMap<&str, &crate::proof_skeleton::ProofSkeletonHole>,
) -> Result<(), ParentProofIntegrationError> {
    validate_dependency_identity(&substitution.dependency, input)?;
    if substitution.expected_dependency_hash != substitution.dependency.dependency_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::DependencyIdentityHashMismatch {
                dependency_id: substitution.dependency.dependency_id.clone(),
                expected: substitution.expected_dependency_hash,
                actual: substitution.dependency.dependency_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: substitution.dependency.dependency_id.clone(),
            },
        ));
    }

    match &substitution.slot {
        ParentProofSubstitutionSlot::Hole {
            hole_id,
            expected_output_hash: _,
        } => {
            validate_identifier(ParentProofIntegrationField::HoleId, hole_id)?;
            let Some(hole) = hole_by_id.get(hole_id.as_str()) else {
                return Err(ParentProofIntegrationError::new(
                    ParentProofIntegrationErrorKind::UnknownHoleSubstitution {
                        hole_id: hole_id.clone(),
                    },
                    ParentProofIntegrationAffected::Hole {
                        hole_id: hole_id.clone(),
                    },
                ));
            };
            if substitution.dependency.kind != ParentProofDependencyKind::HoleProof {
                return Err(kind_mismatch(
                    &substitution.dependency,
                    ParentProofDependencyKind::HoleProof,
                ));
            }
            if substitution.dependency.expected_type_hash
                != hole.expected_type_identity.expected_type_hash
            {
                return Err(ParentProofIntegrationError::new(
                    ParentProofIntegrationErrorKind::WrongExpectedType {
                        slot_id: hole_id.clone(),
                        expected: hole.expected_type_identity.expected_type_hash,
                        actual: substitution.dependency.expected_type_hash,
                    },
                    ParentProofIntegrationAffected::Hole {
                        hole_id: hole_id.clone(),
                    },
                ));
            }
        }
        ParentProofSubstitutionSlot::LocalLemma {
            lemma_id,
            available_dependency_identity,
        } => {
            validate_identifier(ParentProofIntegrationField::LemmaId, lemma_id)?;
            if substitution.dependency.kind != ParentProofDependencyKind::LocalLemma {
                return Err(kind_mismatch(
                    &substitution.dependency,
                    ParentProofDependencyKind::LocalLemma,
                ));
            }
            let Some(available) = available_dependency_identity else {
                return Err(ParentProofIntegrationError::new(
                    ParentProofIntegrationErrorKind::LocalLemmaNameOnly {
                        lemma_id: lemma_id.clone(),
                    },
                    ParentProofIntegrationAffected::LocalLemmaReference {
                        lemma_id: lemma_id.clone(),
                    },
                ));
            };
            validate_local_lemma_available_identity(lemma_id, available, &substitution.dependency)?;
        }
    }

    Ok(())
}

fn validate_dependency_identity(
    dependency: &ParentProofDependencyIdentity,
    input: &ParentProofIntegrationInput,
) -> Result<(), ParentProofIntegrationError> {
    validate_identifier(
        ParentProofIntegrationField::DependencyId,
        &dependency.dependency_id,
    )?;
    validate_identifier(
        ParentProofIntegrationField::Module,
        &dependency.declaration_identity.module,
    )?;
    validate_identifier(
        ParentProofIntegrationField::Declaration,
        &dependency.declaration_identity.declaration,
    )?;

    let declaration_hash = parent_proof_declaration_identity_hash(&dependency.declaration_identity);
    if declaration_hash != dependency.declaration_identity.declaration_identity_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::DeclarationIdentityHashMismatch {
                expected: declaration_hash,
                actual: dependency.declaration_identity.declaration_identity_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }

    for import in &dependency.import_identities {
        validate_identifier(ParentProofIntegrationField::Module, &import.module)?;
        let import_hash = parent_proof_import_identity_hash(import);
        if import_hash != import.import_identity_hash {
            return Err(ParentProofIntegrationError::new(
                ParentProofIntegrationErrorKind::ImportIdentityHashMismatch {
                    module: import.module.clone(),
                    expected: import_hash,
                    actual: import.import_identity_hash,
                },
                ParentProofIntegrationAffected::ParentCandidate,
            ));
        }
    }

    if dependency.source_free_verifier_result_hash.is_none() {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::MissingSourceFreeVerifierResult {
                dependency_id: dependency.dependency_id.clone(),
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }

    let Some(state) = dependency.verifier_status.acceptance_state() else {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CheckerDisagreement {
                dependency_id: dependency.dependency_id.clone(),
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    };

    if dependency.axiom_policy_hash != input.skeleton.policy_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::ChangedAxiomProfile {
                dependency_id: dependency.dependency_id.clone(),
                expected: input.skeleton.policy_hash,
                actual: dependency.axiom_policy_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }
    if dependency.environment_hash != input.skeleton.environment_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateSkeletonMismatch {
                expected: input.skeleton.environment_hash,
                actual: dependency.environment_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }

    let verified_hash = dependency.verified_artifact_identity.hash();
    if verified_hash != dependency.verified_artifact_identity_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::DependencyIdentityHashMismatch {
                dependency_id: dependency.dependency_id.clone(),
                expected: verified_hash,
                actual: dependency.verified_artifact_identity_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }
    validate_verified_artifact_identity(&dependency.verified_artifact_identity).map_err(
        |error| {
            ParentProofIntegrationError::new(
                ParentProofIntegrationErrorKind::VerifiedArtifactIdentityInvalid {
                    dependency_id: dependency.dependency_id.clone(),
                    error_kind: error.kind(),
                },
                ParentProofIntegrationAffected::Dependency {
                    dependency_id: dependency.dependency_id.clone(),
                },
            )
        },
    )?;
    if dependency.verified_artifact_identity.state != state
        || dependency.verified_artifact_identity.statement_hash != dependency.statement_hash
        || dependency.verified_artifact_identity.certificate_hash != dependency.certificate_hash
        || dependency.verified_artifact_identity.export_hash != dependency.export_hash
        || dependency.verified_artifact_identity.axiom_report_hash != dependency.axiom_report_hash
    {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::DependencyIdentityHashMismatch {
                dependency_id: dependency.dependency_id.clone(),
                expected: verified_hash,
                actual: dependency.verified_artifact_identity_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }

    let dependency_hash = parent_proof_dependency_identity_hash(dependency);
    if dependency_hash != dependency.dependency_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::DependencyIdentityHashMismatch {
                dependency_id: dependency.dependency_id.clone(),
                expected: dependency_hash,
                actual: dependency.dependency_hash,
            },
            ParentProofIntegrationAffected::Dependency {
                dependency_id: dependency.dependency_id.clone(),
            },
        ));
    }

    Ok(())
}

fn validate_local_lemma_available_identity(
    lemma_id: &str,
    available: &LocalLemmaAvailableDependencyIdentity,
    dependency: &ParentProofDependencyIdentity,
) -> Result<(), ParentProofIntegrationError> {
    if local_lemma_available_dependency_identity_hash(available)
        != available.dependency_identity_hash
        || available.verified_artifact_identity_hash != dependency.verified_artifact_identity_hash
        || available.statement_hash != dependency.statement_hash
        || available.environment_hash != dependency.environment_hash
        || available.policy_hash != dependency.axiom_policy_hash
    {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::StaleLemmaIdentity {
                lemma_id: lemma_id.to_owned(),
            },
            ParentProofIntegrationAffected::LocalLemmaReference {
                lemma_id: lemma_id.to_owned(),
            },
        ));
    }
    let Some(state) = dependency.verifier_status.acceptance_state() else {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CheckerDisagreement {
                dependency_id: dependency.dependency_id.clone(),
            },
            ParentProofIntegrationAffected::LocalLemmaReference {
                lemma_id: lemma_id.to_owned(),
            },
        ));
    };
    if available.state != state {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::StaleLemmaIdentity {
                lemma_id: lemma_id.to_owned(),
            },
            ParentProofIntegrationAffected::LocalLemmaReference {
                lemma_id: lemma_id.to_owned(),
            },
        ));
    }
    Ok(())
}

fn validate_completed_candidate(
    input: &ParentProofIntegrationInput,
    skeleton_hash: Hash,
    ordered_substitutions: &[ParentProofSubstitution],
) -> Result<(), ParentProofIntegrationError> {
    let candidate = &input.completed_candidate;
    if candidate.base_sketch_hash != input.base_sketch_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateSkeletonMismatch {
                expected: input.base_sketch_hash,
                actual: candidate.base_sketch_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    if candidate.skeleton_hash != skeleton_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateSkeletonMismatch {
                expected: skeleton_hash,
                actual: candidate.skeleton_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    if candidate.statement_hash != input.skeleton.target_statement_identity.statement_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::WrongExpectedType {
                slot_id: "parent".to_owned(),
                expected: input.skeleton.target_statement_identity.statement_hash,
                actual: candidate.statement_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    if candidate.expected_type_hash != input.skeleton.target_statement_identity.expected_type_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::WrongExpectedType {
                slot_id: "parent".to_owned(),
                expected: input.skeleton.target_statement_identity.expected_type_hash,
                actual: candidate.expected_type_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    if candidate.environment_hash != input.skeleton.environment_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateSkeletonMismatch {
                expected: input.skeleton.environment_hash,
                actual: candidate.environment_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    if candidate.axiom_policy_hash != input.skeleton.policy_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::ChangedAxiomProfile {
                dependency_id: "parent".to_owned(),
                expected: input.skeleton.policy_hash,
                actual: candidate.axiom_policy_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }

    let dependency_hashes = ordered_substitutions
        .iter()
        .map(|substitution| substitution.dependency.dependency_hash)
        .collect::<Vec<_>>();
    if candidate.dependency_identity_hashes != dependency_hashes {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateDependencyOrderMismatch,
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    let substitution_hashes = ordered_substitutions
        .iter()
        .map(parent_proof_substitution_hash)
        .collect::<Vec<_>>();
    if candidate.substitution_hashes != substitution_hashes {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateDependencyOrderMismatch,
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    let import_closure_hash = parent_proof_import_closure_hash(ordered_substitutions);
    if candidate.import_closure_hash != import_closure_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::StaleImportIdentity,
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    if candidate.typecheck_status != ParentProofTypecheckStatus::Accepted
        || candidate.typecheck_result_hash.is_none()
    {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateTypecheckRequired {
                status: candidate.typecheck_status,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    let candidate_hash = parent_proof_completed_candidate_hash(candidate);
    if candidate.candidate_hash != candidate_hash {
        return Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::CandidateHashMismatch {
                expected: candidate_hash,
                actual: candidate.candidate_hash,
            },
            ParentProofIntegrationAffected::ParentCandidate,
        ));
    }
    Ok(())
}

fn topological_hole_order(
    skeleton: &ProofSkeleton,
) -> Result<Vec<String>, ParentProofIntegrationError> {
    let hole_by_id = skeleton
        .holes
        .iter()
        .map(|hole| (hole.hole_id.as_str(), hole))
        .collect::<BTreeMap<_, _>>();
    let mut visits = BTreeMap::new();
    let mut ordered = Vec::new();
    for hole_id in hole_by_id.keys() {
        visit_hole(hole_id, &hole_by_id, &mut visits, &mut ordered)?;
    }
    Ok(ordered)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VisitState {
    Visiting,
    Visited,
}

fn visit_hole(
    hole_id: &str,
    hole_by_id: &BTreeMap<&str, &crate::proof_skeleton::ProofSkeletonHole>,
    visits: &mut BTreeMap<String, VisitState>,
    ordered: &mut Vec<String>,
) -> Result<(), ParentProofIntegrationError> {
    match visits.get(hole_id) {
        Some(VisitState::Visited) => return Ok(()),
        Some(VisitState::Visiting) => {
            return Err(ParentProofIntegrationError::new(
                ParentProofIntegrationErrorKind::UnknownHoleSubstitution {
                    hole_id: hole_id.to_owned(),
                },
                ParentProofIntegrationAffected::Hole {
                    hole_id: hole_id.to_owned(),
                },
            ));
        }
        None => {}
    }
    visits.insert(hole_id.to_owned(), VisitState::Visiting);
    let hole = hole_by_id
        .get(hole_id)
        .expect("topological traversal starts from known hole ids");
    let mut dependencies = hole.dependent_hole_ids.clone();
    dependencies.sort();
    for dependency_hole_id in dependencies {
        if !hole_by_id.contains_key(dependency_hole_id.as_str()) {
            return Err(ParentProofIntegrationError::new(
                ParentProofIntegrationErrorKind::UnknownHoleSubstitution {
                    hole_id: dependency_hole_id,
                },
                ParentProofIntegrationAffected::Hole {
                    hole_id: hole_id.to_owned(),
                },
            ));
        }
        visit_hole(&dependency_hole_id, hole_by_id, visits, ordered)?;
    }
    visits.insert(hole_id.to_owned(), VisitState::Visited);
    ordered.push(hole_id.to_owned());
    Ok(())
}

fn kind_mismatch(
    dependency: &ParentProofDependencyIdentity,
    expected: ParentProofDependencyKind,
) -> ParentProofIntegrationError {
    ParentProofIntegrationError::new(
        ParentProofIntegrationErrorKind::DependencyKindMismatch {
            dependency_id: dependency.dependency_id.clone(),
            expected,
            actual: dependency.kind,
        },
        ParentProofIntegrationAffected::Dependency {
            dependency_id: dependency.dependency_id.clone(),
        },
    )
}

fn substitution_slot_key(
    slot: &ParentProofSubstitutionSlot,
) -> Result<String, ParentProofIntegrationError> {
    Ok(match slot {
        ParentProofSubstitutionSlot::Hole { hole_id, .. } => {
            validate_identifier(ParentProofIntegrationField::HoleId, hole_id)?;
            hole_slot_key(hole_id)
        }
        ParentProofSubstitutionSlot::LocalLemma { lemma_id, .. } => {
            validate_identifier(ParentProofIntegrationField::LemmaId, lemma_id)?;
            format!("lemma:{lemma_id}")
        }
    })
}

fn substitution_slot_order_key(slot: &ParentProofSubstitutionSlot) -> String {
    match slot {
        ParentProofSubstitutionSlot::Hole { hole_id, .. } => hole_slot_key(hole_id),
        ParentProofSubstitutionSlot::LocalLemma { lemma_id, .. } => {
            format!("lemma:{lemma_id}")
        }
    }
}

fn hole_slot_key(hole_id: &str) -> String {
    format!("hole:{hole_id}")
}

fn validate_identifier(
    field: ParentProofIntegrationField,
    value: &str,
) -> Result<(), ParentProofIntegrationError> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err(ParentProofIntegrationError::new(
            ParentProofIntegrationErrorKind::EmptyIdentifier { field },
            ParentProofIntegrationAffected::ParentCandidate,
        ))
    } else {
        Ok(())
    }
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    out.push(b's');
    encode_len(out, value.len());
    out.extend(value.as_bytes());
}

fn encode_hash(out: &mut Vec<u8>, hash: &Hash) {
    out.push(b'h');
    out.extend(hash);
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(1);
            encode_hash(out, hash);
        }
        None => out.push(0),
    }
}

fn encode_len(out: &mut Vec<u8>, len: usize) {
    out.push(b'u');
    out.extend((len as u64).to_be_bytes());
}

fn sha256_hash(bytes: &[u8]) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::projection::{
        project_import_certificate_context, VerifiedImportDeclIndexEntry, VerifiedImportKey,
        VerifiedModuleCertificateInput, VerifiedModuleContextEntry,
    };
    use crate::proof_skeleton::{
        ProofSkeletonBudget, ProofSkeletonCoreExpr, ProofSkeletonExpectedTypeIdentity,
        ProofSkeletonHole, ProofSkeletonLocalContextIdentity, ProofSkeletonPreferredNodeKind,
        ProofSkeletonPremiseIdentity, ProofSkeletonPremiseSource,
        ProofSkeletonStaleSolutionRejection, ProofSkeletonStrategyProfile,
        ProofSkeletonStrategyProfileId, ProofSkeletonTargetStatementIdentity, ProofSkeletonTerm,
        PROOF_SKELETON_API_VERSION,
    };
    use npa_cert::{AxiomPolicy, ExportEntry, Name, VerifierSession};
    use std::fs;
    use std::path::PathBuf;

    const SKETCH_LIFECYCLE_MODULE: &str = "Proofs.Ai.SketchLifecycle";
    const SKETCH_PARENT_LEMMA_A: &str = "sketch_parent_lemma_a";
    const SKETCH_PARENT_LEMMA_B: &str = "sketch_parent_lemma_b_depends_on_a";
    const SKETCH_PARENT_FINAL: &str = "sketch_parent_final_depends_on_a_b";

    fn corpus_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("npa-api crate lives under crates/")
            .parent()
            .expect("crates/ lives under the npa repository")
            .join("../npa-corpus")
    }

    fn sketch_lifecycle_certificate() -> Vec<u8> {
        fs::read(corpus_root().join("proofs/Proofs/Ai/SketchLifecycle/certificate.npcert"))
            .expect("SketchLifecycle certificate should exist in ../npa-corpus")
    }

    fn sketch_lifecycle_replay() -> String {
        fs::read_to_string(corpus_root().join("proofs/Proofs/Ai/SketchLifecycle/replay.json"))
            .expect("SketchLifecycle replay should exist in ../npa-corpus")
    }

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn declaration(module: &str, declaration: &str, byte: u8) -> ParentProofDeclarationIdentity {
        let mut identity = ParentProofDeclarationIdentity {
            module: module.to_owned(),
            declaration: declaration.to_owned(),
            declaration_interface_hash: hash(byte),
            declaration_identity_hash: [0; 32],
        };
        identity.declaration_identity_hash = parent_proof_declaration_identity_hash(&identity);
        identity
    }

    fn import(module: &str, byte: u8) -> ParentProofImportIdentity {
        let mut identity = ParentProofImportIdentity {
            module: module.to_owned(),
            certificate_hash: hash(byte),
            export_hash: hash(byte.wrapping_add(1)),
            import_identity_hash: [0; 32],
        };
        identity.import_identity_hash = parent_proof_import_identity_hash(&identity);
        identity
    }

    fn verified_identity(
        statement_hash: Hash,
        certificate_hash: Hash,
        export_hash: Hash,
        axiom_report_hash: Hash,
    ) -> VerifiedArtifactIdentity {
        VerifiedArtifactIdentity {
            state: ProofAcceptanceState::CertificateVerified,
            candidate_hash: hash(0xee),
            statement_hash,
            certificate_hash,
            export_hash,
            axiom_report_hash,
            package_manifest_hash: None,
            package_lock_hash: None,
            verifier_profile: None,
            verifier_binary_hash: None,
            verifier_version_or_build_hash: None,
            release_evidence_kind: None,
            release_evidence_hash: None,
        }
    }

    fn dependency(
        kind: ParentProofDependencyKind,
        dependency_id: &str,
        statement_hash: Hash,
        expected_type_hash: Hash,
        policy_hash: Hash,
        declaration: ParentProofDeclarationIdentity,
        import_byte: u8,
    ) -> ParentProofDependencyIdentity {
        let certificate_hash = hash(import_byte.wrapping_add(0x20));
        let export_hash = hash(import_byte.wrapping_add(0x21));
        let axiom_report_hash = hash(0);
        let verified_artifact_identity = verified_identity(
            statement_hash,
            certificate_hash,
            export_hash,
            axiom_report_hash,
        );
        let mut identity = ParentProofDependencyIdentity {
            dependency_hash: [0; 32],
            kind,
            dependency_id: dependency_id.to_owned(),
            statement_hash,
            expected_type_hash,
            environment_hash: hash(0xe0),
            declaration_identity: declaration,
            certificate_hash,
            export_hash,
            import_identities: vec![import("Proofs.Ai.Foundation", import_byte)],
            axiom_policy_hash: policy_hash,
            axiom_report_hash,
            verifier_status: ParentProofVerifierStatus::CertificateVerified,
            source_free_verifier_result_hash: Some(hash(import_byte.wrapping_add(0x30))),
            verified_artifact_identity_hash: [0; 32],
            verified_artifact_identity,
        };
        identity.verified_artifact_identity_hash = identity.verified_artifact_identity.hash();
        identity.dependency_hash = parent_proof_dependency_identity_hash(&identity);
        identity
    }

    fn available_from_dependency(
        dependency: &ParentProofDependencyIdentity,
    ) -> LocalLemmaAvailableDependencyIdentity {
        let mut available = LocalLemmaAvailableDependencyIdentity {
            dependency_identity_hash: [0; 32],
            verified_artifact_identity_hash: dependency.verified_artifact_identity_hash,
            state: ProofAcceptanceState::CertificateVerified,
            statement_hash: dependency.statement_hash,
            environment_hash: dependency.environment_hash,
            policy_hash: dependency.axiom_policy_hash,
        };
        available.dependency_identity_hash =
            local_lemma_available_dependency_identity_hash(&available);
        available
    }

    fn premise(byte: u8, policy_hash: Hash) -> ProofSkeletonPremiseIdentity {
        ProofSkeletonPremiseIdentity {
            premise_hash: hash(byte),
            source: ProofSkeletonPremiseSource::VerifiedImport,
            axiom_profile_hash: policy_hash,
        }
    }

    fn hole(hole_id: &str, target: Hash, dependencies: &[&str]) -> ProofSkeletonHole {
        let policy_hash = hash(0xf0);
        ProofSkeletonHole {
            hole_id: hole_id.to_owned(),
            local_context_identity: ProofSkeletonLocalContextIdentity {
                context_hash: hash(0xc0),
                binder_fingerprint_hash: hash(0xc1),
            },
            expected_type_identity: ProofSkeletonExpectedTypeIdentity {
                expected_type_hash: target,
                expected_type: ProofSkeletonCoreExpr::Inline {
                    core_expr_hash: target,
                    canonical_bytes: vec![target[0]],
                },
            },
            dependent_hole_ids: dependencies.iter().map(|id| (*id).to_owned()).collect(),
            allowed_premise_identities: vec![premise(0x70, policy_hash)],
            strategy_profile: ProofSkeletonStrategyProfile {
                profile_id: ProofSkeletonStrategyProfileId::Exact,
                preferred_node_kinds: vec![ProofSkeletonPreferredNodeKind::CloseByExact],
            },
            budget: ProofSkeletonBudget {
                max_candidates: 2,
                max_search_nodes: 4,
                max_depth: Some(1),
                max_repair_steps: Some(0),
            },
            stale_solution_rejection: ProofSkeletonStaleSolutionRejection {
                required_context_hash: hash(0xc0),
                required_expected_type_hash: target,
                required_environment_hash: hash(0xe0),
                required_policy_hash: policy_hash,
            },
        }
    }

    fn skeleton() -> ProofSkeleton {
        ProofSkeleton {
            api_version: PROOF_SKELETON_API_VERSION.to_owned(),
            skeleton_id: hash(0xa0),
            target_statement_identity: ProofSkeletonTargetStatementIdentity {
                statement_hash: hash(0x11),
                expected_type_hash: hash(0x12),
                root_context_hash: hash(0x13),
                module: Some("Proofs.Ai.SketchLifecycle".to_owned()),
                declaration: Some("parent_target".to_owned()),
            },
            environment_hash: hash(0xe0),
            policy_hash: hash(0xf0),
            root: ProofSkeletonTerm::Hole {
                hole_id: "h_parent".to_owned(),
            },
            holes: vec![
                hole("h_parent", hash(0x52), &["h_local"]),
                hole("h_local", hash(0x51), &[]),
            ],
        }
    }

    fn substitution(
        slot: ParentProofSubstitutionSlot,
        dependency: ParentProofDependencyIdentity,
    ) -> ParentProofSubstitution {
        ParentProofSubstitution {
            expected_dependency_hash: dependency.dependency_hash,
            slot,
            dependency,
        }
    }

    fn sample_input() -> ParentProofIntegrationInput {
        let skeleton = skeleton();
        let base_sketch_hash = hash(0xb0);
        let lemma_dependency = dependency(
            ParentProofDependencyKind::LocalLemma,
            "lemma_a",
            hash(0x31),
            hash(0x31),
            skeleton.policy_hash,
            declaration("Proofs.Ai.SketchLifecycle", "lemma_a", 0x81),
            0x90,
        );
        let h_local_dependency = dependency(
            ParentProofDependencyKind::HoleProof,
            "h_local",
            hash(0x51),
            hash(0x51),
            skeleton.policy_hash,
            declaration("Proofs.Ai.SketchLifecycle", "h_local", 0x82),
            0x91,
        );
        let h_parent_dependency = dependency(
            ParentProofDependencyKind::HoleProof,
            "h_parent",
            hash(0x52),
            hash(0x52),
            skeleton.policy_hash,
            declaration("Proofs.Ai.SketchLifecycle", "h_parent", 0x83),
            0x92,
        );
        let substitutions = vec![
            substitution(
                ParentProofSubstitutionSlot::Hole {
                    hole_id: "h_parent".to_owned(),
                    expected_output_hash: hash(0xd2),
                },
                h_parent_dependency,
            ),
            substitution(
                ParentProofSubstitutionSlot::LocalLemma {
                    lemma_id: "lemma_a".to_owned(),
                    available_dependency_identity: Some(available_from_dependency(
                        &lemma_dependency,
                    )),
                },
                lemma_dependency,
            ),
            substitution(
                ParentProofSubstitutionSlot::Hole {
                    hole_id: "h_local".to_owned(),
                    expected_output_hash: hash(0xd1),
                },
                h_local_dependency,
            ),
        ];
        let skeleton_hash = proof_skeleton_hash(&skeleton);
        let ordered_substitutions = vec![
            substitutions[1].clone(),
            substitutions[2].clone(),
            substitutions[0].clone(),
        ];
        let ordered_hashes = ordered_substitutions
            .iter()
            .map(|substitution| substitution.dependency.dependency_hash)
            .collect::<Vec<_>>();
        let substitution_hashes = ordered_substitutions
            .iter()
            .map(parent_proof_substitution_hash)
            .collect::<Vec<_>>();
        let mut completed_candidate = ParentProofCompletedCandidate {
            candidate_hash: [0; 32],
            base_sketch_hash,
            skeleton_hash,
            statement_hash: skeleton.target_statement_identity.statement_hash,
            expected_type_hash: skeleton.target_statement_identity.expected_type_hash,
            completed_core_expr_hash: hash(0xc5),
            environment_hash: skeleton.environment_hash,
            import_closure_hash: parent_proof_import_closure_hash(&ordered_substitutions),
            axiom_policy_hash: skeleton.policy_hash,
            dependency_identity_hashes: ordered_hashes,
            substitution_hashes,
            typecheck_status: ParentProofTypecheckStatus::Accepted,
            typecheck_result_hash: Some(hash(0xcc)),
        };
        completed_candidate.candidate_hash =
            parent_proof_completed_candidate_hash(&completed_candidate);
        ParentProofIntegrationInput {
            base_sketch_hash,
            skeleton,
            substitutions,
            completed_candidate,
        }
    }

    fn sketch_lifecycle_context() -> VerifiedModuleContextEntry {
        let policy = AxiomPolicy::high_trust();
        let mut session = VerifierSession::new();
        let certificate = sketch_lifecycle_certificate();
        let verified = npa_cert::verify_module_cert(&certificate, &mut session, &policy)
            .expect("SketchLifecycle certificate should verify source-free");
        let key = VerifiedImportKey::new(
            verified.module().clone(),
            verified.export_hash(),
            verified.certificate_hash(),
        );
        let input = VerifiedModuleCertificateInput {
            module: verified.module(),
            expected_export_hash: verified.export_hash(),
            expected_certificate_hash: verified.certificate_hash(),
            certificate_bytes: &certificate,
        };
        let context =
            project_import_certificate_context(&[input], std::slice::from_ref(&key), &policy)
                .expect("SketchLifecycle projection should verify source-free");
        context
            .verified_modules()
            .iter()
            .find(|entry| entry.key == key)
            .expect("projected context should contain SketchLifecycle")
            .clone()
    }

    fn sketch_parent_policy_hash() -> Hash {
        sha256_hash(b"npa.sketch-parent-e2e.policy.high-trust.no-axioms.v1")
    }

    fn sketch_parent_source_free_result_hash(context: &VerifiedModuleContextEntry) -> Hash {
        let mut out = Vec::new();
        encode_string(&mut out, "npa.sketch-parent-e2e.source-free-result.v1");
        encode_string(&mut out, &context.key.module.as_dotted());
        encode_hash(&mut out, &context.key.export_hash);
        encode_hash(&mut out, &context.key.certificate_hash);
        encode_hash(&mut out, &context.axiom_report_hash);
        sha256_hash(&out)
    }

    fn name_matches(name: &Name, module: &str, declaration: &str) -> bool {
        let dotted = name.as_dotted();
        dotted == declaration || dotted == format!("{module}.{declaration}")
    }

    fn sketch_decl<'a>(
        context: &'a VerifiedModuleContextEntry,
        declaration: &str,
    ) -> &'a VerifiedImportDeclIndexEntry {
        context
            .decl_index_table
            .iter()
            .find(|entry| name_matches(&entry.name, SKETCH_LIFECYCLE_MODULE, declaration))
            .unwrap_or_else(|| panic!("missing SketchLifecycle declaration {declaration}"))
    }

    fn sketch_export<'a>(
        context: &'a VerifiedModuleContextEntry,
        declaration: &str,
    ) -> &'a ExportEntry {
        context
            .export_block
            .iter()
            .find(|entry| {
                name_matches(
                    &context.decoded_name_table[entry.name],
                    SKETCH_LIFECYCLE_MODULE,
                    declaration,
                )
            })
            .unwrap_or_else(|| panic!("missing SketchLifecycle export {declaration}"))
    }

    fn sketch_parent_import_identity(
        context: &VerifiedModuleContextEntry,
    ) -> ParentProofImportIdentity {
        let mut identity = ParentProofImportIdentity {
            module: context.key.module.as_dotted(),
            certificate_hash: context.key.certificate_hash,
            export_hash: context.key.export_hash,
            import_identity_hash: [0; 32],
        };
        identity.import_identity_hash = parent_proof_import_identity_hash(&identity);
        identity
    }

    fn sketch_parent_dependency(
        context: &VerifiedModuleContextEntry,
        kind: ParentProofDependencyKind,
        dependency_id: &str,
        declaration_name: &str,
        environment_hash: Hash,
        policy_hash: Hash,
    ) -> ParentProofDependencyIdentity {
        let decl = sketch_decl(context, declaration_name);
        let export = sketch_export(context, declaration_name);
        let mut declaration_identity = ParentProofDeclarationIdentity {
            module: context.key.module.as_dotted(),
            declaration: declaration_name.to_owned(),
            declaration_interface_hash: decl.hashes.decl_interface_hash,
            declaration_identity_hash: [0; 32],
        };
        declaration_identity.declaration_identity_hash =
            parent_proof_declaration_identity_hash(&declaration_identity);
        let verified_artifact_identity = VerifiedArtifactIdentity {
            state: ProofAcceptanceState::CertificateVerified,
            candidate_hash: decl.hashes.decl_certificate_hash,
            statement_hash: export.type_hash,
            certificate_hash: context.key.certificate_hash,
            export_hash: context.key.export_hash,
            axiom_report_hash: context.axiom_report_hash,
            package_manifest_hash: None,
            package_lock_hash: None,
            verifier_profile: None,
            verifier_binary_hash: None,
            verifier_version_or_build_hash: None,
            release_evidence_kind: None,
            release_evidence_hash: None,
        };
        let mut dependency = ParentProofDependencyIdentity {
            dependency_hash: [0; 32],
            kind,
            dependency_id: dependency_id.to_owned(),
            statement_hash: export.type_hash,
            expected_type_hash: export.type_hash,
            environment_hash,
            declaration_identity,
            certificate_hash: context.key.certificate_hash,
            export_hash: context.key.export_hash,
            import_identities: vec![sketch_parent_import_identity(context)],
            axiom_policy_hash: policy_hash,
            axiom_report_hash: context.axiom_report_hash,
            verifier_status: ParentProofVerifierStatus::CertificateVerified,
            source_free_verifier_result_hash: Some(sketch_parent_source_free_result_hash(context)),
            verified_artifact_identity_hash: [0; 32],
            verified_artifact_identity,
        };
        dependency.verified_artifact_identity_hash = dependency.verified_artifact_identity.hash();
        dependency.dependency_hash = parent_proof_dependency_identity_hash(&dependency);
        dependency
    }

    fn sketch_parent_hole(
        hole_id: &str,
        target: Hash,
        context_hash: Hash,
        environment_hash: Hash,
        policy_hash: Hash,
    ) -> ProofSkeletonHole {
        ProofSkeletonHole {
            hole_id: hole_id.to_owned(),
            local_context_identity: ProofSkeletonLocalContextIdentity {
                context_hash,
                binder_fingerprint_hash: sha256_hash(b"sketch-parent-e2e.root-binders"),
            },
            expected_type_identity: ProofSkeletonExpectedTypeIdentity {
                expected_type_hash: target,
                expected_type: ProofSkeletonCoreExpr::Inline {
                    core_expr_hash: target,
                    canonical_bytes: target.to_vec(),
                },
            },
            dependent_hole_ids: Vec::new(),
            allowed_premise_identities: Vec::new(),
            strategy_profile: ProofSkeletonStrategyProfile {
                profile_id: ProofSkeletonStrategyProfileId::Exact,
                preferred_node_kinds: vec![ProofSkeletonPreferredNodeKind::CloseByExact],
            },
            budget: ProofSkeletonBudget {
                max_candidates: 1,
                max_search_nodes: 1,
                max_depth: Some(1),
                max_repair_steps: Some(0),
            },
            stale_solution_rejection: ProofSkeletonStaleSolutionRejection {
                required_context_hash: context_hash,
                required_expected_type_hash: target,
                required_environment_hash: environment_hash,
                required_policy_hash: policy_hash,
            },
        }
    }

    fn sketch_parent_e2e_skeleton(context: &VerifiedModuleContextEntry) -> ProofSkeleton {
        let final_export = sketch_export(context, SKETCH_PARENT_FINAL);
        let environment_hash = context.certified_env_decl_hashes_summary_hash;
        let policy_hash = sketch_parent_policy_hash();
        ProofSkeleton {
            api_version: PROOF_SKELETON_API_VERSION.to_owned(),
            skeleton_id: sha256_hash(b"npa.sketch-parent-e2e.skeleton.v1"),
            target_statement_identity: ProofSkeletonTargetStatementIdentity {
                statement_hash: final_export.type_hash,
                expected_type_hash: final_export.type_hash,
                root_context_hash: context.decl_index_table_hash,
                module: Some(SKETCH_LIFECYCLE_MODULE.to_owned()),
                declaration: Some(SKETCH_PARENT_FINAL.to_owned()),
            },
            environment_hash,
            policy_hash,
            root: ProofSkeletonTerm::Hole {
                hole_id: "h_sketch_parent_final".to_owned(),
            },
            holes: vec![sketch_parent_hole(
                "h_sketch_parent_final",
                final_export.type_hash,
                context.decl_index_table_hash,
                environment_hash,
                policy_hash,
            )],
        }
    }

    fn sketch_parent_e2e_input() -> (ParentProofIntegrationInput, VerifiedModuleContextEntry) {
        let context = sketch_lifecycle_context();
        let skeleton = sketch_parent_e2e_skeleton(&context);
        let base_sketch_hash = sha256_hash(b"npa.sketch-parent-e2e.base-sketch.v1");
        let lemma_a_dependency = sketch_parent_dependency(
            &context,
            ParentProofDependencyKind::LocalLemma,
            "lemma_a",
            SKETCH_PARENT_LEMMA_A,
            skeleton.environment_hash,
            skeleton.policy_hash,
        );
        let lemma_b_dependency = sketch_parent_dependency(
            &context,
            ParentProofDependencyKind::LocalLemma,
            "lemma_b",
            SKETCH_PARENT_LEMMA_B,
            skeleton.environment_hash,
            skeleton.policy_hash,
        );
        let final_dependency = sketch_parent_dependency(
            &context,
            ParentProofDependencyKind::HoleProof,
            "h_sketch_parent_final",
            SKETCH_PARENT_FINAL,
            skeleton.environment_hash,
            skeleton.policy_hash,
        );
        let substitutions = vec![
            substitution(
                ParentProofSubstitutionSlot::Hole {
                    hole_id: "h_sketch_parent_final".to_owned(),
                    expected_output_hash: sketch_decl(&context, SKETCH_PARENT_FINAL)
                        .hashes
                        .decl_certificate_hash,
                },
                final_dependency,
            ),
            substitution(
                ParentProofSubstitutionSlot::LocalLemma {
                    lemma_id: "lemma_b".to_owned(),
                    available_dependency_identity: Some(available_from_dependency(
                        &lemma_b_dependency,
                    )),
                },
                lemma_b_dependency,
            ),
            substitution(
                ParentProofSubstitutionSlot::LocalLemma {
                    lemma_id: "lemma_a".to_owned(),
                    available_dependency_identity: Some(available_from_dependency(
                        &lemma_a_dependency,
                    )),
                },
                lemma_a_dependency,
            ),
        ];
        let ordered_substitutions = vec![
            substitutions[2].clone(),
            substitutions[1].clone(),
            substitutions[0].clone(),
        ];
        let dependency_identity_hashes = ordered_substitutions
            .iter()
            .map(|substitution| substitution.dependency.dependency_hash)
            .collect::<Vec<_>>();
        let substitution_hashes = ordered_substitutions
            .iter()
            .map(parent_proof_substitution_hash)
            .collect::<Vec<_>>();
        let mut completed_candidate = ParentProofCompletedCandidate {
            candidate_hash: [0; 32],
            base_sketch_hash,
            skeleton_hash: proof_skeleton_hash(&skeleton),
            statement_hash: skeleton.target_statement_identity.statement_hash,
            expected_type_hash: skeleton.target_statement_identity.expected_type_hash,
            completed_core_expr_hash: sketch_decl(&context, SKETCH_PARENT_FINAL)
                .hashes
                .decl_certificate_hash,
            environment_hash: skeleton.environment_hash,
            import_closure_hash: parent_proof_import_closure_hash(&ordered_substitutions),
            axiom_policy_hash: skeleton.policy_hash,
            dependency_identity_hashes,
            substitution_hashes,
            typecheck_status: ParentProofTypecheckStatus::Accepted,
            typecheck_result_hash: Some(sketch_parent_source_free_result_hash(&context)),
        };
        completed_candidate.candidate_hash =
            parent_proof_completed_candidate_hash(&completed_candidate);
        (
            ParentProofIntegrationInput {
                base_sketch_hash,
                skeleton,
                substitutions,
                completed_candidate,
            },
            context,
        )
    }

    fn refresh_substitution_identity(substitution: &mut ParentProofSubstitution) {
        substitution.dependency.verified_artifact_identity_hash =
            substitution.dependency.verified_artifact_identity.hash();
        substitution.dependency.dependency_hash =
            parent_proof_dependency_identity_hash(&substitution.dependency);
        substitution.expected_dependency_hash = substitution.dependency.dependency_hash;
        if let ParentProofSubstitutionSlot::LocalLemma {
            available_dependency_identity: Some(available),
            ..
        } = &mut substitution.slot
        {
            available.verified_artifact_identity_hash =
                substitution.dependency.verified_artifact_identity_hash;
            available.statement_hash = substitution.dependency.statement_hash;
            available.environment_hash = substitution.dependency.environment_hash;
            available.policy_hash = substitution.dependency.axiom_policy_hash;
            available.state = substitution
                .dependency
                .verifier_status
                .acceptance_state()
                .unwrap_or(ProofAcceptanceState::Proposed);
            available.dependency_identity_hash =
                local_lemma_available_dependency_identity_hash(available);
        }
    }

    fn sketch_parent_local_lemma_mut<'a>(
        input: &'a mut ParentProofIntegrationInput,
        lemma_id: &str,
    ) -> &'a mut ParentProofSubstitution {
        input
            .substitutions
            .iter_mut()
            .find(|substitution| {
                matches!(
                    &substitution.slot,
                    ParentProofSubstitutionSlot::LocalLemma { lemma_id: id, .. } if id == lemma_id
                )
            })
            .unwrap_or_else(|| panic!("missing local lemma substitution {lemma_id}"))
    }

    #[test]
    fn sketch_parent_e2e_integrates_source_free_verified_local_lemmas() {
        let (input, context) = sketch_parent_e2e_input();
        let replay = sketch_lifecycle_replay();
        for declaration in [
            SKETCH_PARENT_LEMMA_A,
            SKETCH_PARENT_LEMMA_B,
            SKETCH_PARENT_FINAL,
        ] {
            assert!(
                replay.contains(&format!("\"declaration\": \"{declaration}\"")),
                "SketchLifecycle replay should contain {declaration}"
            );
        }
        assert!(
            replay.contains("\"term\": \"fun A => fun x => sketch_parent_lemma_a A x\""),
            "Lemma B replay should depend on Lemma A"
        );
        assert!(
            replay.contains(
                "\"term\": \"fun A => fun x => sketch_parent_lemma_b_depends_on_a A (sketch_parent_lemma_a A x)\""
            ),
            "Final parent replay should depend on Lemma A and Lemma B"
        );

        let output = integrate_parent_proof(&input).unwrap();
        assert_eq!(
            output
                .ordered_substitutions
                .iter()
                .map(|substitution| substitution.dependency.dependency_id.as_str())
                .collect::<Vec<_>>(),
            vec!["lemma_a", "lemma_b", "h_sketch_parent_final"]
        );
        assert_eq!(
            output
                .ordered_substitutions
                .iter()
                .map(|substitution| substitution.dependency.dependency_hash)
                .collect::<Vec<_>>(),
            output.completed_candidate.dependency_identity_hashes
        );
        assert_eq!(
            output
                .ordered_substitutions
                .iter()
                .map(parent_proof_substitution_hash)
                .collect::<Vec<_>>(),
            output.completed_candidate.substitution_hashes
        );
        assert_eq!(
            output.completed_candidate.typecheck_result_hash,
            Some(sketch_parent_source_free_result_hash(&context))
        );
        for substitution in &output.ordered_substitutions {
            assert_eq!(
                substitution.dependency.certificate_hash,
                context.key.certificate_hash
            );
            assert_eq!(substitution.dependency.export_hash, context.key.export_hash);
            assert_eq!(
                substitution.dependency.axiom_report_hash,
                context.axiom_report_hash
            );
            assert_eq!(
                substitution.dependency.source_free_verifier_result_hash,
                Some(sketch_parent_source_free_result_hash(&context))
            );
            assert_eq!(
                substitution.dependency.verified_artifact_identity_hash,
                substitution.dependency.verified_artifact_identity.hash()
            );
        }
        assert_eq!(
            output.integration_hash,
            parent_proof_integration_output_hash(&output)
        );
    }

    #[test]
    fn sketch_parent_e2e_rejects_unverified_or_stale_local_lemma_fixture() {
        let (mut unverified, _) = sketch_parent_e2e_input();
        let lemma_a = sketch_parent_local_lemma_mut(&mut unverified, "lemma_a");
        lemma_a.dependency.source_free_verifier_result_hash = None;
        refresh_substitution_identity(lemma_a);
        let error = integrate_parent_proof(&unverified).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::MissingSourceFreeVerifierResult { .. }
        ));
        assert!(matches!(
            error.affected(),
            ParentProofIntegrationAffected::Dependency { dependency_id }
                if dependency_id == "lemma_a"
        ));

        let (mut stale_certificate, _) = sketch_parent_e2e_input();
        let lemma_a = sketch_parent_local_lemma_mut(&mut stale_certificate, "lemma_a");
        lemma_a.dependency.certificate_hash = hash(0xa7);
        lemma_a
            .dependency
            .verified_artifact_identity
            .certificate_hash = hash(0xa7);
        refresh_substitution_identity(lemma_a);
        let error = integrate_parent_proof(&stale_certificate).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::CandidateDependencyOrderMismatch
        ));
        assert_eq!(
            error.affected(),
            &ParentProofIntegrationAffected::ParentCandidate
        );

        let (mut stale_import, _) = sketch_parent_e2e_input();
        let lemma_b = sketch_parent_local_lemma_mut(&mut stale_import, "lemma_b");
        lemma_b.dependency.import_identities[0].export_hash = hash(0xb7);
        lemma_b.dependency.import_identities[0].import_identity_hash =
            parent_proof_import_identity_hash(&lemma_b.dependency.import_identities[0]);
        refresh_substitution_identity(lemma_b);
        let error = integrate_parent_proof(&stale_import).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::CandidateDependencyOrderMismatch
        ));
        assert_eq!(
            error.affected(),
            &ParentProofIntegrationAffected::ParentCandidate
        );
    }

    #[test]
    fn parent_proof_integration_substitutes_dependencies_and_hashes_candidate() {
        let input = sample_input();
        let output = integrate_parent_proof(&input).unwrap();
        assert_eq!(output.skeleton_hash, proof_skeleton_hash(&input.skeleton));
        assert_eq!(
            output
                .ordered_substitutions
                .iter()
                .map(|substitution| substitution.dependency.dependency_id.as_str())
                .collect::<Vec<_>>(),
            vec!["lemma_a", "h_local", "h_parent"]
        );
        assert_eq!(
            output.completed_candidate.candidate_hash,
            parent_proof_completed_candidate_hash(&output.completed_candidate)
        );
        assert_eq!(
            output.integration_hash,
            parent_proof_integration_output_hash(&output)
        );
    }

    #[test]
    fn parent_proof_integration_rejects_name_only_and_stale_lemma_identity() {
        let mut input = sample_input();
        let lemma = input
            .substitutions
            .iter_mut()
            .find(|substitution| {
                matches!(
                    substitution.slot,
                    ParentProofSubstitutionSlot::LocalLemma { .. }
                )
            })
            .unwrap();
        let ParentProofSubstitutionSlot::LocalLemma {
            available_dependency_identity,
            ..
        } = &mut lemma.slot
        else {
            unreachable!();
        };
        *available_dependency_identity = None;
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::LocalLemmaNameOnly { .. }
        ));

        let mut input = sample_input();
        let lemma = input
            .substitutions
            .iter_mut()
            .find(|substitution| {
                matches!(
                    substitution.slot,
                    ParentProofSubstitutionSlot::LocalLemma { .. }
                )
            })
            .unwrap();
        let ParentProofSubstitutionSlot::LocalLemma {
            available_dependency_identity: Some(available),
            ..
        } = &mut lemma.slot
        else {
            unreachable!();
        };
        available.verified_artifact_identity_hash = hash(0xfe);
        available.dependency_identity_hash =
            local_lemma_available_dependency_identity_hash(available);
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::StaleLemmaIdentity { .. }
        ));
    }

    #[test]
    fn parent_proof_integration_rejects_stale_import_checker_disagreement_and_missing_source_free()
    {
        let mut input = sample_input();
        input.substitutions[0].dependency.import_identities[0].export_hash = hash(0xfa);
        input.substitutions[0].dependency.dependency_hash =
            parent_proof_dependency_identity_hash(&input.substitutions[0].dependency);
        input.substitutions[0].expected_dependency_hash =
            input.substitutions[0].dependency.dependency_hash;
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::ImportIdentityHashMismatch { .. }
        ));

        let mut input = sample_input();
        input.substitutions[0].dependency.verifier_status =
            ParentProofVerifierStatus::CheckerDisagreement;
        input.substitutions[0].dependency.dependency_hash =
            parent_proof_dependency_identity_hash(&input.substitutions[0].dependency);
        input.substitutions[0].expected_dependency_hash =
            input.substitutions[0].dependency.dependency_hash;
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::CheckerDisagreement { .. }
        ));

        let mut input = sample_input();
        input.substitutions[0]
            .dependency
            .source_free_verifier_result_hash = None;
        input.substitutions[0].dependency.dependency_hash =
            parent_proof_dependency_identity_hash(&input.substitutions[0].dependency);
        input.substitutions[0].expected_dependency_hash =
            input.substitutions[0].dependency.dependency_hash;
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::MissingSourceFreeVerifierResult { .. }
        ));
    }

    #[test]
    fn parent_proof_integration_rejects_wrong_expected_type_and_changed_axiom_profile() {
        let mut input = sample_input();
        input.substitutions[0].dependency.expected_type_hash = hash(0xfd);
        input.substitutions[0].dependency.dependency_hash =
            parent_proof_dependency_identity_hash(&input.substitutions[0].dependency);
        input.substitutions[0].expected_dependency_hash =
            input.substitutions[0].dependency.dependency_hash;
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::WrongExpectedType { .. }
        ));

        let mut input = sample_input();
        input.substitutions[0].dependency.axiom_policy_hash = hash(0xfc);
        input.substitutions[0].dependency.dependency_hash =
            parent_proof_dependency_identity_hash(&input.substitutions[0].dependency);
        input.substitutions[0].expected_dependency_hash =
            input.substitutions[0].dependency.dependency_hash;
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::ChangedAxiomProfile { .. }
        ));

        let mut input = sample_input();
        input.completed_candidate.typecheck_status = ParentProofTypecheckStatus::NotRun;
        input.completed_candidate.typecheck_result_hash = None;
        input.completed_candidate.candidate_hash =
            parent_proof_completed_candidate_hash(&input.completed_candidate);
        let error = integrate_parent_proof(&input).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParentProofIntegrationErrorKind::CandidateTypecheckRequired { .. }
        ));
    }

    #[derive(Clone, Copy)]
    enum DependencyMutation {
        Certificate,
        Export,
        Statement,
        DeclarationInterface,
        AxiomReport,
    }

    #[test]
    fn parent_proof_integration_requires_parent_revalidation_for_changed_dependency_identity() {
        for mutation in [
            DependencyMutation::Certificate,
            DependencyMutation::Export,
            DependencyMutation::Statement,
            DependencyMutation::DeclarationInterface,
            DependencyMutation::AxiomReport,
        ] {
            let mut input = sample_input();
            let lemma = &mut input.substitutions[1];
            match mutation {
                DependencyMutation::Certificate => {
                    lemma.dependency.certificate_hash = hash(0xa1);
                    lemma.dependency.verified_artifact_identity.certificate_hash = hash(0xa1);
                }
                DependencyMutation::Export => {
                    lemma.dependency.export_hash = hash(0xa2);
                    lemma.dependency.verified_artifact_identity.export_hash = hash(0xa2);
                }
                DependencyMutation::Statement => {
                    lemma.dependency.statement_hash = hash(0xa3);
                    lemma.dependency.verified_artifact_identity.statement_hash = hash(0xa3);
                }
                DependencyMutation::DeclarationInterface => {
                    lemma
                        .dependency
                        .declaration_identity
                        .declaration_interface_hash = hash(0xa4);
                    lemma
                        .dependency
                        .declaration_identity
                        .declaration_identity_hash = parent_proof_declaration_identity_hash(
                        &lemma.dependency.declaration_identity,
                    );
                }
                DependencyMutation::AxiomReport => {
                    lemma.dependency.axiom_report_hash = hash(0xa5);
                    lemma
                        .dependency
                        .verified_artifact_identity
                        .axiom_report_hash = hash(0xa5);
                }
            }
            lemma.dependency.verified_artifact_identity_hash =
                lemma.dependency.verified_artifact_identity.hash();
            if let ParentProofSubstitutionSlot::LocalLemma {
                available_dependency_identity: Some(available),
                ..
            } = &mut lemma.slot
            {
                available.verified_artifact_identity_hash =
                    lemma.dependency.verified_artifact_identity_hash;
                available.statement_hash = lemma.dependency.statement_hash;
                available.dependency_identity_hash =
                    local_lemma_available_dependency_identity_hash(available);
            }
            lemma.dependency.dependency_hash =
                parent_proof_dependency_identity_hash(&lemma.dependency);
            lemma.expected_dependency_hash = lemma.dependency.dependency_hash;

            let error = integrate_parent_proof(&input).unwrap_err();
            assert!(matches!(
                error.kind(),
                ParentProofIntegrationErrorKind::CandidateDependencyOrderMismatch
            ));
            assert_eq!(
                error.affected(),
                &ParentProofIntegrationAffected::ParentCandidate
            );
        }
    }
}
