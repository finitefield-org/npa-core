use crate::proof_skeleton::{proof_skeleton_hash, ProofSkeleton, ProofSkeletonPremiseSource};
use crate::proof_sketch::{
    proof_sketch_hash, validate_proof_sketch, ProofSketch, ProofSketchGeneralizationPolicy,
    ProofSketchNodeKind,
};
use crate::types::format_hash_string;
use npa_cert::Hash;
use npa_kernel::{Expr, Level};
use npa_tactic::{
    core_expr_hash, machine_local_context_hash, machine_local_decl_hash, MachineLocalDecl,
};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub const PROOF_LOCAL_CONTEXT_BINDER_FINGERPRINT_HASH_DOMAIN: &str =
    "npa.proof.local-context-binder-fingerprint.v1";
pub const PROOF_LOCAL_STATEMENT_GENERALIZATION_HASH_DOMAIN: &str =
    "npa.proof.local-statement-generalization.v1";

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProofSemanticValidationProfile {
    pub expected_environment_hash: Option<Hash>,
    pub expected_policy_hash: Option<Hash>,
    pub parent_statement_hash: Option<Hash>,
    pub allowed_axiom_profile_hashes: BTreeSet<Hash>,
    pub typed_statements: BTreeMap<Hash, ProofTypedStatementArtifact>,
    pub typed_core_expr_hashes: BTreeSet<Hash>,
    pub verified_import_premise_hashes: BTreeSet<Hash>,
    pub verified_local_lemma_hashes: BTreeSet<Hash>,
    pub local_context_captures: BTreeMap<Hash, ProofLocalContextCapture>,
    pub generalized_local_statements: BTreeMap<Hash, ProofLocalStatementGeneralization>,
}

impl ProofSemanticValidationProfile {
    pub fn strict(
        expected_environment_hash: Hash,
        expected_policy_hash: Hash,
        parent_statement_hash: Hash,
    ) -> Self {
        let mut profile = Self {
            expected_environment_hash: Some(expected_environment_hash),
            expected_policy_hash: Some(expected_policy_hash),
            parent_statement_hash: Some(parent_statement_hash),
            ..Self::default()
        };
        profile
            .allowed_axiom_profile_hashes
            .insert(expected_policy_hash);
        profile
    }

    pub fn with_allowed_axiom_profile(mut self, axiom_profile_hash: Hash) -> Self {
        self.allowed_axiom_profile_hashes.insert(axiom_profile_hash);
        self
    }

    pub fn with_typed_statement(mut self, artifact: ProofTypedStatementArtifact) -> Self {
        self.typed_core_expr_hashes
            .insert(artifact.expected_type_hash);
        self.typed_statements
            .insert(artifact.statement_hash, artifact);
        self
    }

    pub fn with_typed_core_expr_hash(mut self, core_expr_hash: Hash) -> Self {
        self.typed_core_expr_hashes.insert(core_expr_hash);
        self
    }

    pub fn with_verified_import_premise(mut self, premise_hash: Hash) -> Self {
        self.verified_import_premise_hashes.insert(premise_hash);
        self
    }

    pub fn with_verified_local_lemma(mut self, statement_hash: Hash) -> Self {
        self.verified_local_lemma_hashes.insert(statement_hash);
        self
    }

    pub fn with_local_context_capture(mut self, capture: ProofLocalContextCapture) -> Self {
        self.local_context_captures
            .insert(capture.context_hash, capture);
        self
    }

    pub fn with_generalized_local_statement(
        mut self,
        generalization: ProofLocalStatementGeneralization,
    ) -> Self {
        self.generalized_local_statements
            .insert(generalization.generalized_statement_hash, generalization);
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofTypedStatementArtifact {
    pub statement_hash: Hash,
    pub expected_type_hash: Hash,
    pub context_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub axiom_profile_hash: Hash,
}

impl ProofTypedStatementArtifact {
    pub const fn new(
        statement_hash: Hash,
        expected_type_hash: Hash,
        context_hash: Hash,
        environment_hash: Hash,
        policy_hash: Hash,
        axiom_profile_hash: Hash,
    ) -> Self {
        Self {
            statement_hash,
            expected_type_hash,
            context_hash,
            environment_hash,
            policy_hash,
            axiom_profile_hash,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSemanticValidationReport {
    pub sketch_hash: Hash,
    pub skeleton_hash: Hash,
    pub typed_statement_hashes: Vec<Hash>,
    pub typed_core_expr_hashes: Vec<Hash>,
    pub local_context_hashes: Vec<Hash>,
    pub hole_ids: Vec<String>,
    pub allowed_premise_hashes: Vec<Hash>,
    pub generalized_statement_hashes: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofSemanticValidationError {
    kind: ProofSemanticValidationErrorKind,
}

impl ProofSemanticValidationError {
    fn new(kind: ProofSemanticValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ProofSemanticValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofSemanticValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofSemanticValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSemanticValidationErrorKind {
    SketchGraphInvalid {
        reason: String,
    },
    EnvironmentMismatch {
        expected: Hash,
        actual: Hash,
    },
    PolicyMismatch {
        expected: Hash,
        actual: Hash,
    },
    SketchSkeletonTargetMismatch {
        sketch_statement_hash: Hash,
        skeleton_statement_hash: Hash,
    },
    SketchSkeletonRootContextMismatch {
        sketch_context_hash: Hash,
        skeleton_context_hash: Hash,
    },
    ParentStatementMismatch {
        expected: Hash,
        actual: Hash,
    },
    StatementNotTypeChecked {
        statement_hash: Hash,
    },
    ExpectedTypeNotTypeChecked {
        core_expr_hash: Hash,
    },
    StatementEnvironmentMismatch {
        statement_hash: Hash,
        expected: Hash,
        actual: Hash,
    },
    StatementPolicyMismatch {
        statement_hash: Hash,
        expected: Hash,
        actual: Hash,
    },
    StatementContextMismatch {
        statement_hash: Hash,
        expected: Hash,
        actual: Hash,
    },
    StatementExpectedTypeMismatch {
        statement_hash: Hash,
        expected: Hash,
        actual: Hash,
    },
    MissingLocalContextCapture {
        context_hash: Hash,
    },
    BinderFingerprintMismatch {
        context_hash: Hash,
        expected: Hash,
        actual: Hash,
    },
    ParentConclusionAssumption {
        proposal_id: String,
        statement_hash: Hash,
    },
    MissingGeneralizedStatement {
        proposal_id: String,
        statement_hash: Hash,
    },
    GeneralizedStatementHashMismatch {
        proposal_id: String,
        expected: Hash,
        actual: Hash,
    },
    GeneralizedStatementContextMismatch {
        statement_hash: Hash,
        expected: Hash,
        actual: Hash,
    },
    AxiomProfileExpansion {
        axiom_profile_hash: Hash,
    },
    AssertLemmaMissingStatementProposal {
        node_id: String,
    },
    UnknownStatementProposal {
        node_id: String,
        proposal_id: String,
    },
    FutureUnprovedLocalLemmaReference {
        node_id: String,
        statement_hash: Hash,
    },
    LocalContextPremiseNotCaptured {
        hole_id: String,
        premise_hash: Hash,
        context_hash: Hash,
    },
    PremiseNotVerified {
        hole_id: String,
        premise_hash: Hash,
        source: ProofSkeletonPremiseSource,
    },
}

impl fmt::Display for ProofSemanticValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SketchGraphInvalid { reason } => {
                write!(
                    f,
                    "sketch semantic validation requires a valid graph: {reason}"
                )
            }
            Self::EnvironmentMismatch { expected, actual } => write!(
                f,
                "environment mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::PolicyMismatch { expected, actual } => write!(
                f,
                "policy mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::SketchSkeletonTargetMismatch {
                sketch_statement_hash,
                skeleton_statement_hash,
            } => write!(
                f,
                "sketch target {} does not match skeleton target {}",
                format_hash_string(sketch_statement_hash),
                format_hash_string(skeleton_statement_hash)
            ),
            Self::SketchSkeletonRootContextMismatch {
                sketch_context_hash,
                skeleton_context_hash,
            } => write!(
                f,
                "sketch root context {} does not match skeleton root context {}",
                format_hash_string(sketch_context_hash),
                format_hash_string(skeleton_context_hash)
            ),
            Self::ParentStatementMismatch { expected, actual } => write!(
                f,
                "parent statement mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::StatementNotTypeChecked { statement_hash } => write!(
                f,
                "statement {} has no type-checked artifact",
                format_hash_string(statement_hash)
            ),
            Self::ExpectedTypeNotTypeChecked { core_expr_hash } => write!(
                f,
                "expected type {} has no type-checked core expression artifact",
                format_hash_string(core_expr_hash)
            ),
            Self::StatementEnvironmentMismatch {
                statement_hash,
                expected,
                actual,
            } => write!(
                f,
                "statement {} environment mismatch: expected {}, got {}",
                format_hash_string(statement_hash),
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::StatementPolicyMismatch {
                statement_hash,
                expected,
                actual,
            } => write!(
                f,
                "statement {} policy mismatch: expected {}, got {}",
                format_hash_string(statement_hash),
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::StatementContextMismatch {
                statement_hash,
                expected,
                actual,
            } => write!(
                f,
                "statement {} context mismatch: expected {}, got {}",
                format_hash_string(statement_hash),
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::StatementExpectedTypeMismatch {
                statement_hash,
                expected,
                actual,
            } => write!(
                f,
                "statement {} expected type mismatch: expected {}, got {}",
                format_hash_string(statement_hash),
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::MissingLocalContextCapture { context_hash } => write!(
                f,
                "missing local context capture {}",
                format_hash_string(context_hash)
            ),
            Self::BinderFingerprintMismatch {
                context_hash,
                expected,
                actual,
            } => write!(
                f,
                "local context {} binder fingerprint mismatch: expected {}, got {}",
                format_hash_string(context_hash),
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::ParentConclusionAssumption {
                proposal_id,
                statement_hash,
            } => write!(
                f,
                "local lemma proposal `{proposal_id}` assumes parent conclusion {}",
                format_hash_string(statement_hash)
            ),
            Self::MissingGeneralizedStatement {
                proposal_id,
                statement_hash,
            } => write!(
                f,
                "local lemma proposal `{proposal_id}` statement {} has no generalization record",
                format_hash_string(statement_hash)
            ),
            Self::GeneralizedStatementHashMismatch {
                proposal_id,
                expected,
                actual,
            } => write!(
                f,
                "local lemma proposal `{proposal_id}` generalized statement hash mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::GeneralizedStatementContextMismatch {
                statement_hash,
                expected,
                actual,
            } => write!(
                f,
                "generalized statement {} source context mismatch: expected {}, got {}",
                format_hash_string(statement_hash),
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::AxiomProfileExpansion { axiom_profile_hash } => write!(
                f,
                "axiom profile {} is not allowed by the parent policy",
                format_hash_string(axiom_profile_hash)
            ),
            Self::AssertLemmaMissingStatementProposal { node_id } => {
                write!(f, "assert-lemma node `{node_id}` has no statement proposal")
            }
            Self::UnknownStatementProposal {
                node_id,
                proposal_id,
            } => write!(
                f,
                "node `{node_id}` references unknown statement proposal `{proposal_id}`"
            ),
            Self::FutureUnprovedLocalLemmaReference {
                node_id,
                statement_hash,
            } => write!(
                f,
                "node `{node_id}` references future unverified local lemma {}",
                format_hash_string(statement_hash)
            ),
            Self::LocalContextPremiseNotCaptured {
                hole_id,
                premise_hash,
                context_hash,
            } => write!(
                f,
                "hole `{hole_id}` local premise {} is not captured in context {}",
                format_hash_string(premise_hash),
                format_hash_string(context_hash)
            ),
            Self::PremiseNotVerified {
                hole_id,
                premise_hash,
                source,
            } => write!(
                f,
                "hole `{hole_id}` premise {} from {:?} is not verified",
                format_hash_string(premise_hash),
                source
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofLocalContextCapture {
    pub context_hash: Hash,
    pub binder_fingerprint_hash: Hash,
    pub local_premise_hashes: Vec<Hash>,
    pub local_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofLocalStatementGeneralizationPolicy {
    pub unfold_local_definitions: bool,
}

impl Default for ProofLocalStatementGeneralizationPolicy {
    fn default() -> Self {
        Self {
            unfold_local_definitions: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofLocalStatementGeneralization {
    pub source_context_hash: Hash,
    pub source_statement_hash: Hash,
    pub captured_local_indices: Vec<u32>,
    pub binders: Vec<ProofLocalStatementGeneralizationBinder>,
    pub minimized_universe_params: Vec<String>,
    pub unfold_local_definitions: bool,
    pub generalized_statement_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofLocalStatementGeneralizationBinder {
    pub local_index: u32,
    pub local_decl_hash: Hash,
    pub type_hash: Hash,
    pub value_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofLocalContextValidationError {
    kind: ProofLocalContextValidationErrorKind,
}

impl ProofLocalContextValidationError {
    fn new(kind: ProofLocalContextValidationErrorKind) -> Self {
        Self { kind }
    }

    pub const fn kind(&self) -> &ProofLocalContextValidationErrorKind {
        &self.kind
    }
}

impl fmt::Display for ProofLocalContextValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for ProofLocalContextValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofLocalContextValidationErrorKind {
    ContextHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    BinderFingerprintMismatch {
        expected: Hash,
        actual: Hash,
    },
    LocalPremiseHashMismatch {
        expected: Vec<Hash>,
        actual: Vec<Hash>,
    },
    LocalScopeEscape {
        local_index: Option<u32>,
        bvar_index: u32,
        binder_depth: usize,
        local_count: usize,
    },
    CapturedLocalOutOfScope {
        local_index: u32,
        local_count: usize,
    },
    DuplicateCapturedLocal {
        local_index: u32,
    },
    MissingGeneralization {
        local_index: u32,
        dependency_local_index: u32,
    },
    DependencyOrderViolation {
        local_index: u32,
        dependency_local_index: u32,
    },
    MalformedGeneralizedBinderOrder {
        previous_local_index: u32,
        local_index: u32,
    },
    IrrelevantGeneralizationBinder {
        local_index: u32,
    },
    StatementHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    GeneralizedStatementHashMismatch {
        expected: Hash,
        actual: Hash,
    },
}

impl fmt::Display for ProofLocalContextValidationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ContextHashMismatch { expected, actual } => write!(
                f,
                "local context hash mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::BinderFingerprintMismatch { expected, actual } => write!(
                f,
                "local context binder fingerprint mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::LocalPremiseHashMismatch { .. } => {
                write!(f, "local premise hash set mismatch")
            }
            Self::LocalScopeEscape {
                local_index,
                bvar_index,
                binder_depth,
                local_count,
            } => write!(
                f,
                "local scope escape at {:?}: bvar {}, binder depth {}, local count {}",
                local_index, bvar_index, binder_depth, local_count
            ),
            Self::CapturedLocalOutOfScope {
                local_index,
                local_count,
            } => write!(
                f,
                "captured local index {} is outside local count {}",
                local_index, local_count
            ),
            Self::DuplicateCapturedLocal { local_index } => {
                write!(f, "duplicate captured local index {local_index}")
            }
            Self::MissingGeneralization {
                local_index,
                dependency_local_index,
            } => write!(
                f,
                "captured local {} requires local {} to be generalized",
                local_index, dependency_local_index
            ),
            Self::DependencyOrderViolation {
                local_index,
                dependency_local_index,
            } => write!(
                f,
                "captured local {} appears before dependency {}",
                local_index, dependency_local_index
            ),
            Self::MalformedGeneralizedBinderOrder {
                previous_local_index,
                local_index,
            } => write!(
                f,
                "generalized binder order {} then {} is not dependency order",
                previous_local_index, local_index
            ),
            Self::IrrelevantGeneralizationBinder { local_index } => {
                write!(f, "irrelevant generalized binder local {local_index}")
            }
            Self::StatementHashMismatch { expected, actual } => write!(
                f,
                "statement hash mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
            Self::GeneralizedStatementHashMismatch { expected, actual } => write!(
                f,
                "generalized statement hash mismatch: expected {}, got {}",
                format_hash_string(expected),
                format_hash_string(actual)
            ),
        }
    }
}

pub fn validate_proof_sketch_semantics(
    sketch: &ProofSketch,
    skeleton: &ProofSkeleton,
    profile: &ProofSemanticValidationProfile,
) -> Result<ProofSemanticValidationReport, ProofSemanticValidationError> {
    validate_proof_sketch(sketch).map_err(|err| {
        ProofSemanticValidationError::new(ProofSemanticValidationErrorKind::SketchGraphInvalid {
            reason: err.to_string(),
        })
    })?;

    check_hash_option(
        profile.expected_environment_hash,
        sketch.environment_hash,
        |expected, actual| ProofSemanticValidationErrorKind::EnvironmentMismatch {
            expected,
            actual,
        },
    )?;
    check_hash_option(
        profile.expected_policy_hash,
        sketch.policy_hash,
        |expected, actual| ProofSemanticValidationErrorKind::PolicyMismatch { expected, actual },
    )?;
    if sketch.environment_hash != skeleton.environment_hash {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::EnvironmentMismatch {
                expected: sketch.environment_hash,
                actual: skeleton.environment_hash,
            },
        ));
    }
    if sketch.policy_hash != skeleton.policy_hash {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::PolicyMismatch {
                expected: sketch.policy_hash,
                actual: skeleton.policy_hash,
            },
        ));
    }

    let sketch_statement_hash = sketch.target_statement_identity.statement_hash;
    let skeleton_statement_hash = skeleton.target_statement_identity.statement_hash;
    if sketch_statement_hash != skeleton_statement_hash {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::SketchSkeletonTargetMismatch {
                sketch_statement_hash,
                skeleton_statement_hash,
            },
        ));
    }
    let sketch_root_context_hash = sketch.target_statement_identity.input_context_hash;
    let skeleton_root_context_hash = skeleton.target_statement_identity.root_context_hash;
    if sketch_root_context_hash != skeleton_root_context_hash {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::SketchSkeletonRootContextMismatch {
                sketch_context_hash: sketch_root_context_hash,
                skeleton_context_hash: skeleton_root_context_hash,
            },
        ));
    }
    if let Some(expected) = profile.parent_statement_hash {
        if expected != sketch_statement_hash {
            return Err(ProofSemanticValidationError::new(
                ProofSemanticValidationErrorKind::ParentStatementMismatch {
                    expected,
                    actual: sketch_statement_hash,
                },
            ));
        }
    }

    let target_statement = checked_statement(
        profile,
        sketch_statement_hash,
        skeleton.environment_hash,
        skeleton.policy_hash,
    )?;
    check_statement_expected_type(
        target_statement,
        skeleton.target_statement_identity.expected_type_hash,
    )?;
    check_statement_context(
        target_statement,
        skeleton.target_statement_identity.root_context_hash,
    )?;
    check_typed_core_expr(
        profile,
        skeleton.target_statement_identity.expected_type_hash,
    )?;
    check_axiom_profile(profile, target_statement.axiom_profile_hash)?;
    check_context_capture(
        profile,
        skeleton.target_statement_identity.root_context_hash,
        None,
    )?;
    check_context_capture(
        profile,
        sketch.target_statement_identity.output_context_hash,
        None,
    )?;

    let proposals = sketch
        .sublemma_statement_proposals
        .iter()
        .map(|proposal| (proposal.proposal_id.as_str(), proposal))
        .collect::<BTreeMap<_, _>>();
    let parent_statement_hash = profile
        .parent_statement_hash
        .unwrap_or(sketch.target_statement_identity.statement_hash);
    let proposal_statement_hashes = sketch
        .sublemma_statement_proposals
        .iter()
        .map(|proposal| proposal.statement_hash)
        .collect::<BTreeSet<_>>();

    for proposal in &sketch.sublemma_statement_proposals {
        if proposal.statement_hash == parent_statement_hash {
            return Err(ProofSemanticValidationError::new(
                ProofSemanticValidationErrorKind::ParentConclusionAssumption {
                    proposal_id: proposal.proposal_id.clone(),
                    statement_hash: proposal.statement_hash,
                },
            ));
        }
        let statement = checked_statement(
            profile,
            proposal.statement_hash,
            sketch.environment_hash,
            sketch.policy_hash,
        )?;
        check_statement_context(statement, proposal.input_context_hash)?;
        check_typed_core_expr(profile, statement.expected_type_hash)?;
        check_axiom_profile(profile, statement.axiom_profile_hash)?;
        check_context_capture(profile, proposal.input_context_hash, None)?;
        if proposal.generalization_policy != ProofSketchGeneralizationPolicy::None {
            let Some(generalization) = profile
                .generalized_local_statements
                .get(&proposal.statement_hash)
            else {
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::MissingGeneralizedStatement {
                        proposal_id: proposal.proposal_id.clone(),
                        statement_hash: proposal.statement_hash,
                    },
                ));
            };
            if generalization.generalized_statement_hash != proposal.statement_hash {
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::GeneralizedStatementHashMismatch {
                        proposal_id: proposal.proposal_id.clone(),
                        expected: proposal.statement_hash,
                        actual: generalization.generalized_statement_hash,
                    },
                ));
            }
            if generalization.source_context_hash != proposal.input_context_hash {
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::GeneralizedStatementContextMismatch {
                        statement_hash: proposal.statement_hash,
                        expected: proposal.input_context_hash,
                        actual: generalization.source_context_hash,
                    },
                ));
            }
        }
    }

    for node in &sketch.nodes {
        check_context_capture(profile, node.input_context_hash, None)?;
        check_context_capture(profile, node.output_context_hash, None)?;
        match (&node.kind, &node.statement_proposal_id) {
            (ProofSketchNodeKind::AssertLemma, None) => {
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::AssertLemmaMissingStatementProposal {
                        node_id: node.node_id.clone(),
                    },
                ));
            }
            (_, Some(proposal_id)) if !proposals.contains_key(proposal_id.as_str()) => {
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::UnknownStatementProposal {
                        node_id: node.node_id.clone(),
                        proposal_id: proposal_id.clone(),
                    },
                ));
            }
            _ => {}
        }

        for premise_hash in &node.premise_hashes {
            if node.kind == ProofSketchNodeKind::AssertLemma
                && *premise_hash == parent_statement_hash
            {
                let proposal_id = node
                    .statement_proposal_id
                    .clone()
                    .unwrap_or_else(|| node.node_id.clone());
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::ParentConclusionAssumption {
                        proposal_id,
                        statement_hash: parent_statement_hash,
                    },
                ));
            }
            if proposal_statement_hashes.contains(premise_hash)
                && !profile.verified_local_lemma_hashes.contains(premise_hash)
            {
                return Err(ProofSemanticValidationError::new(
                    ProofSemanticValidationErrorKind::FutureUnprovedLocalLemmaReference {
                        node_id: node.node_id.clone(),
                        statement_hash: *premise_hash,
                    },
                ));
            }
        }
    }

    for hole in &skeleton.holes {
        let capture = check_context_capture(
            profile,
            hole.local_context_identity.context_hash,
            Some(hole.local_context_identity.binder_fingerprint_hash),
        )?;
        check_typed_core_expr(profile, hole.expected_type_identity.expected_type_hash)?;
        for premise in &hole.allowed_premise_identities {
            check_axiom_profile(profile, premise.axiom_profile_hash)?;
            match premise.source {
                ProofSkeletonPremiseSource::LocalContext => {
                    if !capture.local_premise_hashes.contains(&premise.premise_hash) {
                        return Err(ProofSemanticValidationError::new(
                            ProofSemanticValidationErrorKind::LocalContextPremiseNotCaptured {
                                hole_id: hole.hole_id.clone(),
                                premise_hash: premise.premise_hash,
                                context_hash: capture.context_hash,
                            },
                        ));
                    }
                }
                ProofSkeletonPremiseSource::VerifiedImport => {
                    if !profile
                        .verified_import_premise_hashes
                        .contains(&premise.premise_hash)
                    {
                        return Err(ProofSemanticValidationError::new(
                            ProofSemanticValidationErrorKind::PremiseNotVerified {
                                hole_id: hole.hole_id.clone(),
                                premise_hash: premise.premise_hash,
                                source: premise.source,
                            },
                        ));
                    }
                }
                ProofSkeletonPremiseSource::VerifiedLocalLemma => {
                    if !profile
                        .verified_local_lemma_hashes
                        .contains(&premise.premise_hash)
                    {
                        return Err(ProofSemanticValidationError::new(
                            ProofSemanticValidationErrorKind::PremiseNotVerified {
                                hole_id: hole.hole_id.clone(),
                                premise_hash: premise.premise_hash,
                                source: premise.source,
                            },
                        ));
                    }
                }
            }
        }
    }

    Ok(ProofSemanticValidationReport {
        sketch_hash: proof_sketch_hash(sketch),
        skeleton_hash: proof_skeleton_hash(skeleton),
        typed_statement_hashes: sorted_hashes(profile.typed_statements.keys().copied()),
        typed_core_expr_hashes: sorted_hashes(profile.typed_core_expr_hashes.iter().copied()),
        local_context_hashes: sorted_hashes(profile.local_context_captures.keys().copied()),
        hole_ids: skeleton
            .holes
            .iter()
            .map(|hole| hole.hole_id.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
        allowed_premise_hashes: sorted_hashes(
            skeleton
                .holes
                .iter()
                .flat_map(|hole| hole.allowed_premise_identities.iter())
                .map(|premise| premise.premise_hash),
        ),
        generalized_statement_hashes: sorted_hashes(
            profile.generalized_local_statements.keys().copied(),
        ),
    })
}

pub fn proof_local_context_capture(
    context: &[MachineLocalDecl],
) -> Result<ProofLocalContextCapture, ProofLocalContextValidationError> {
    validate_context_declarations(context)?;
    let context_hash = machine_local_context_hash(context);
    let binder_fingerprint_hash = proof_local_context_binder_fingerprint_hash(context);
    let local_premise_hashes = context.iter().map(machine_local_decl_hash).collect();
    Ok(ProofLocalContextCapture {
        context_hash,
        binder_fingerprint_hash,
        local_premise_hashes,
        local_count: context.len(),
    })
}

pub fn proof_local_context_binder_fingerprint_hash(context: &[MachineLocalDecl]) -> Hash {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_LOCAL_CONTEXT_BINDER_FINGERPRINT_HASH_DOMAIN);
    encode_len_to(&mut out, context.len());
    for local in context {
        encode_hash_to(&mut out, &machine_local_decl_hash(local));
    }
    sha256_hash(&out)
}

pub fn validate_proof_local_context_capture(
    context: &[MachineLocalDecl],
    expected: &ProofLocalContextCapture,
) -> Result<(), ProofLocalContextValidationError> {
    let actual = proof_local_context_capture(context)?;
    if expected.context_hash != actual.context_hash {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::ContextHashMismatch {
                expected: expected.context_hash,
                actual: actual.context_hash,
            },
        ));
    }
    if expected.binder_fingerprint_hash != actual.binder_fingerprint_hash {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::BinderFingerprintMismatch {
                expected: expected.binder_fingerprint_hash,
                actual: actual.binder_fingerprint_hash,
            },
        ));
    }
    if expected.local_premise_hashes != actual.local_premise_hashes {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::LocalPremiseHashMismatch {
                expected: expected.local_premise_hashes.clone(),
                actual: actual.local_premise_hashes,
            },
        ));
    }
    Ok(())
}

pub fn generalize_local_context_statement(
    context: &[MachineLocalDecl],
    statement: &Expr,
    policy: &ProofLocalStatementGeneralizationPolicy,
) -> Result<ProofLocalStatementGeneralization, ProofLocalContextValidationError> {
    validate_context_declarations(context)?;
    let mut captured = BTreeSet::new();
    collect_expr_local_indices(statement, context.len(), 0, None, &mut captured)?;
    let mut queue = captured.iter().copied().collect::<Vec<_>>();
    while let Some(local_index) = queue.pop() {
        let deps = local_dependency_indices(context, local_index as usize)?;
        for dependency in deps {
            if captured.insert(dependency) {
                queue.push(dependency);
            }
        }
    }

    let captured_local_indices = captured.iter().copied().collect::<Vec<_>>();
    validate_captured_local_indices(context, &captured_local_indices)?;

    let mut universe_params = BTreeSet::new();
    collect_expr_universe_params(statement, &mut universe_params);
    let binders = captured_local_indices
        .iter()
        .map(|local_index| {
            let local = &context[*local_index as usize];
            collect_expr_universe_params(&local.ty, &mut universe_params);
            if policy.unfold_local_definitions {
                if let Some(value) = &local.value {
                    collect_expr_universe_params(value, &mut universe_params);
                }
            }
            ProofLocalStatementGeneralizationBinder {
                local_index: *local_index,
                local_decl_hash: machine_local_decl_hash(local),
                type_hash: core_expr_hash(&local.ty),
                value_hash: local.value.as_ref().map(core_expr_hash),
            }
        })
        .collect::<Vec<_>>();

    let mut generalization = ProofLocalStatementGeneralization {
        source_context_hash: machine_local_context_hash(context),
        source_statement_hash: core_expr_hash(statement),
        captured_local_indices,
        binders,
        minimized_universe_params: universe_params.into_iter().collect(),
        unfold_local_definitions: policy.unfold_local_definitions,
        generalized_statement_hash: [0; 32],
    };
    generalization.generalized_statement_hash =
        proof_local_statement_generalization_hash(&generalization);
    Ok(generalization)
}

pub fn validate_local_context_generalization(
    context: &[MachineLocalDecl],
    statement: &Expr,
    generalization: &ProofLocalStatementGeneralization,
) -> Result<(), ProofLocalContextValidationError> {
    validate_context_declarations(context)?;
    validate_captured_local_indices(context, &generalization.captured_local_indices)?;
    let policy = ProofLocalStatementGeneralizationPolicy {
        unfold_local_definitions: generalization.unfold_local_definitions,
    };
    let expected = generalize_local_context_statement(context, statement, &policy)?;
    if generalization.source_context_hash != expected.source_context_hash {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::ContextHashMismatch {
                expected: expected.source_context_hash,
                actual: generalization.source_context_hash,
            },
        ));
    }
    if generalization.source_statement_hash != expected.source_statement_hash {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::StatementHashMismatch {
                expected: expected.source_statement_hash,
                actual: generalization.source_statement_hash,
            },
        ));
    }
    let expected_set = expected
        .captured_local_indices
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let actual_set = generalization
        .captured_local_indices
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if let Some(local_index) = expected_set.difference(&actual_set).next() {
        let dependency = local_dependency_indices(context, *local_index as usize)?
            .into_iter()
            .find(|dependency| actual_set.contains(dependency))
            .unwrap_or(*local_index);
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::MissingGeneralization {
                local_index: *local_index,
                dependency_local_index: dependency,
            },
        ));
    }
    if let Some(local_index) = actual_set.difference(&expected_set).next() {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::IrrelevantGeneralizationBinder {
                local_index: *local_index,
            },
        ));
    }
    if generalization.captured_local_indices != expected.captured_local_indices {
        let (previous_local_index, local_index) = first_order_mismatch(
            &expected.captured_local_indices,
            &generalization.captured_local_indices,
        );
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::MalformedGeneralizedBinderOrder {
                previous_local_index,
                local_index,
            },
        ));
    }
    let actual_hash = proof_local_statement_generalization_hash(generalization);
    if generalization.generalized_statement_hash != expected.generalized_statement_hash
        || actual_hash != expected.generalized_statement_hash
    {
        return Err(ProofLocalContextValidationError::new(
            ProofLocalContextValidationErrorKind::GeneralizedStatementHashMismatch {
                expected: expected.generalized_statement_hash,
                actual: generalization.generalized_statement_hash,
            },
        ));
    }
    Ok(())
}

pub fn proof_local_statement_generalization_hash(
    generalization: &ProofLocalStatementGeneralization,
) -> Hash {
    let mut out = Vec::new();
    encode_string_to(&mut out, PROOF_LOCAL_STATEMENT_GENERALIZATION_HASH_DOMAIN);
    encode_string_to(&mut out, "source_context_hash");
    encode_hash_to(&mut out, &generalization.source_context_hash);
    encode_string_to(&mut out, "source_statement_hash");
    encode_hash_to(&mut out, &generalization.source_statement_hash);
    encode_string_to(&mut out, "captured_local_indices");
    encode_len_to(&mut out, generalization.captured_local_indices.len());
    for local_index in &generalization.captured_local_indices {
        encode_u64_to(&mut out, u64::from(*local_index));
    }
    encode_string_to(&mut out, "binders");
    encode_len_to(&mut out, generalization.binders.len());
    for binder in &generalization.binders {
        encode_u64_to(&mut out, u64::from(binder.local_index));
        encode_hash_to(&mut out, &binder.local_decl_hash);
        encode_hash_to(&mut out, &binder.type_hash);
        encode_option_hash_to(&mut out, binder.value_hash.as_ref());
    }
    encode_string_to(&mut out, "minimized_universe_params");
    encode_len_to(&mut out, generalization.minimized_universe_params.len());
    for param in &generalization.minimized_universe_params {
        encode_string_to(&mut out, param);
    }
    encode_string_to(&mut out, "unfold_local_definitions");
    out.push(u8::from(generalization.unfold_local_definitions));
    sha256_hash(&out)
}

fn check_hash_option(
    expected: Option<Hash>,
    actual: Hash,
    ctor: fn(Hash, Hash) -> ProofSemanticValidationErrorKind,
) -> Result<(), ProofSemanticValidationError> {
    if let Some(expected) = expected {
        if expected != actual {
            return Err(ProofSemanticValidationError::new(ctor(expected, actual)));
        }
    }
    Ok(())
}

fn checked_statement(
    profile: &ProofSemanticValidationProfile,
    statement_hash: Hash,
    environment_hash: Hash,
    policy_hash: Hash,
) -> Result<&ProofTypedStatementArtifact, ProofSemanticValidationError> {
    let Some(statement) = profile.typed_statements.get(&statement_hash) else {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::StatementNotTypeChecked { statement_hash },
        ));
    };
    if statement.environment_hash != environment_hash {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::StatementEnvironmentMismatch {
                statement_hash,
                expected: environment_hash,
                actual: statement.environment_hash,
            },
        ));
    }
    if statement.policy_hash != policy_hash {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::StatementPolicyMismatch {
                statement_hash,
                expected: policy_hash,
                actual: statement.policy_hash,
            },
        ));
    }
    Ok(statement)
}

fn check_statement_context(
    statement: &ProofTypedStatementArtifact,
    expected: Hash,
) -> Result<(), ProofSemanticValidationError> {
    if statement.context_hash != expected {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::StatementContextMismatch {
                statement_hash: statement.statement_hash,
                expected,
                actual: statement.context_hash,
            },
        ));
    }
    Ok(())
}

fn check_statement_expected_type(
    statement: &ProofTypedStatementArtifact,
    expected: Hash,
) -> Result<(), ProofSemanticValidationError> {
    if statement.expected_type_hash != expected {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::StatementExpectedTypeMismatch {
                statement_hash: statement.statement_hash,
                expected,
                actual: statement.expected_type_hash,
            },
        ));
    }
    Ok(())
}

fn check_typed_core_expr(
    profile: &ProofSemanticValidationProfile,
    core_expr_hash: Hash,
) -> Result<(), ProofSemanticValidationError> {
    if !profile.typed_core_expr_hashes.contains(&core_expr_hash) {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::ExpectedTypeNotTypeChecked { core_expr_hash },
        ));
    }
    Ok(())
}

fn check_axiom_profile(
    profile: &ProofSemanticValidationProfile,
    axiom_profile_hash: Hash,
) -> Result<(), ProofSemanticValidationError> {
    if profile
        .allowed_axiom_profile_hashes
        .contains(&axiom_profile_hash)
        || profile.expected_policy_hash == Some(axiom_profile_hash)
    {
        return Ok(());
    }
    Err(ProofSemanticValidationError::new(
        ProofSemanticValidationErrorKind::AxiomProfileExpansion { axiom_profile_hash },
    ))
}

fn check_context_capture(
    profile: &ProofSemanticValidationProfile,
    context_hash: Hash,
    expected_binder_fingerprint_hash: Option<Hash>,
) -> Result<&ProofLocalContextCapture, ProofSemanticValidationError> {
    let Some(capture) = profile.local_context_captures.get(&context_hash) else {
        return Err(ProofSemanticValidationError::new(
            ProofSemanticValidationErrorKind::MissingLocalContextCapture { context_hash },
        ));
    };
    if let Some(expected) = expected_binder_fingerprint_hash {
        if capture.binder_fingerprint_hash != expected {
            return Err(ProofSemanticValidationError::new(
                ProofSemanticValidationErrorKind::BinderFingerprintMismatch {
                    context_hash,
                    expected,
                    actual: capture.binder_fingerprint_hash,
                },
            ));
        }
    }
    Ok(capture)
}

fn validate_context_declarations(
    context: &[MachineLocalDecl],
) -> Result<(), ProofLocalContextValidationError> {
    for (index, local) in context.iter().enumerate() {
        let mut refs = BTreeSet::new();
        collect_expr_local_indices(&local.ty, index, 0, Some(index as u32), &mut refs)?;
        if let Some(value) = &local.value {
            collect_expr_local_indices(value, index, 0, Some(index as u32), &mut refs)?;
        }
    }
    Ok(())
}

fn validate_captured_local_indices(
    context: &[MachineLocalDecl],
    captured_local_indices: &[u32],
) -> Result<(), ProofLocalContextValidationError> {
    let mut seen = BTreeSet::new();
    let mut position = BTreeMap::new();
    let mut previous = None;
    for (index, local_index) in captured_local_indices.iter().copied().enumerate() {
        if local_index as usize >= context.len() {
            return Err(ProofLocalContextValidationError::new(
                ProofLocalContextValidationErrorKind::CapturedLocalOutOfScope {
                    local_index,
                    local_count: context.len(),
                },
            ));
        }
        if !seen.insert(local_index) {
            return Err(ProofLocalContextValidationError::new(
                ProofLocalContextValidationErrorKind::DuplicateCapturedLocal { local_index },
            ));
        }
        if let Some(previous_local_index) = previous {
            if previous_local_index >= local_index {
                return Err(ProofLocalContextValidationError::new(
                    ProofLocalContextValidationErrorKind::MalformedGeneralizedBinderOrder {
                        previous_local_index,
                        local_index,
                    },
                ));
            }
        }
        previous = Some(local_index);
        position.insert(local_index, index);
    }

    for local_index in captured_local_indices {
        for dependency in local_dependency_indices(context, *local_index as usize)? {
            if !seen.contains(&dependency) {
                return Err(ProofLocalContextValidationError::new(
                    ProofLocalContextValidationErrorKind::MissingGeneralization {
                        local_index: *local_index,
                        dependency_local_index: dependency,
                    },
                ));
            }
            if position[&dependency] >= position[local_index] {
                return Err(ProofLocalContextValidationError::new(
                    ProofLocalContextValidationErrorKind::DependencyOrderViolation {
                        local_index: *local_index,
                        dependency_local_index: dependency,
                    },
                ));
            }
        }
    }
    Ok(())
}

fn local_dependency_indices(
    context: &[MachineLocalDecl],
    local_index: usize,
) -> Result<BTreeSet<u32>, ProofLocalContextValidationError> {
    let local = &context[local_index];
    let mut deps = BTreeSet::new();
    collect_expr_local_indices(
        &local.ty,
        local_index,
        0,
        Some(local_index as u32),
        &mut deps,
    )?;
    if let Some(value) = &local.value {
        collect_expr_local_indices(value, local_index, 0, Some(local_index as u32), &mut deps)?;
    }
    Ok(deps)
}

fn collect_expr_local_indices(
    expr: &Expr,
    local_count: usize,
    binder_depth: usize,
    owner_local_index: Option<u32>,
    ids: &mut BTreeSet<u32>,
) -> Result<(), ProofLocalContextValidationError> {
    match expr {
        Expr::Sort(_) | Expr::Const { .. } => {}
        Expr::BVar(index) => {
            let index_usize = *index as usize;
            if index_usize >= binder_depth {
                let local_offset = index_usize - binder_depth;
                if local_offset < local_count {
                    let local_index = local_count - 1 - local_offset;
                    ids.insert(local_index as u32);
                } else {
                    return Err(ProofLocalContextValidationError::new(
                        ProofLocalContextValidationErrorKind::LocalScopeEscape {
                            local_index: owner_local_index,
                            bvar_index: *index,
                            binder_depth,
                            local_count,
                        },
                    ));
                }
            }
        }
        Expr::App(fun, arg) => {
            collect_expr_local_indices(fun, local_count, binder_depth, owner_local_index, ids)?;
            collect_expr_local_indices(arg, local_count, binder_depth, owner_local_index, ids)?;
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_expr_local_indices(ty, local_count, binder_depth, owner_local_index, ids)?;
            collect_expr_local_indices(
                body,
                local_count,
                binder_depth + 1,
                owner_local_index,
                ids,
            )?;
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expr_local_indices(ty, local_count, binder_depth, owner_local_index, ids)?;
            collect_expr_local_indices(value, local_count, binder_depth, owner_local_index, ids)?;
            collect_expr_local_indices(
                body,
                local_count,
                binder_depth + 1,
                owner_local_index,
                ids,
            )?;
        }
    }
    Ok(())
}

fn collect_expr_universe_params(expr: &Expr, params: &mut BTreeSet<String>) {
    match expr {
        Expr::Sort(level) => collect_level_universe_params(level, params),
        Expr::BVar(_) => {}
        Expr::Const { levels, .. } => {
            for level in levels {
                collect_level_universe_params(level, params);
            }
        }
        Expr::App(fun, arg) => {
            collect_expr_universe_params(fun, params);
            collect_expr_universe_params(arg, params);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_expr_universe_params(ty, params);
            collect_expr_universe_params(body, params);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expr_universe_params(ty, params);
            collect_expr_universe_params(value, params);
            collect_expr_universe_params(body, params);
        }
    }
}

fn collect_level_universe_params(level: &Level, params: &mut BTreeSet<String>) {
    match level {
        Level::Zero => {}
        Level::Succ(inner) => collect_level_universe_params(inner, params),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            collect_level_universe_params(lhs, params);
            collect_level_universe_params(rhs, params);
        }
        Level::Param(name) => {
            params.insert(name.clone());
        }
    }
}

fn first_order_mismatch(expected: &[u32], actual: &[u32]) -> (u32, u32) {
    for (left, right) in expected.iter().zip(actual) {
        if left != right {
            return (*left, *right);
        }
    }
    (
        expected.first().copied().unwrap_or_default(),
        actual.first().copied().unwrap_or_default(),
    )
}

fn sorted_hashes(values: impl IntoIterator<Item = Hash>) -> Vec<Hash> {
    values
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    out.push(b's');
    encode_len_to(out, value.len());
    out.extend(value.as_bytes());
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.push(b'h');
    out.extend(hash);
}

fn encode_option_hash_to(out: &mut Vec<u8>, hash: Option<&Hash>) {
    match hash {
        Some(hash) => {
            out.push(1);
            encode_hash_to(out, hash);
        }
        None => out.push(0),
    }
}

fn encode_u64_to(out: &mut Vec<u8>, value: u64) {
    out.push(b'u');
    out.extend(value.to_be_bytes());
}

fn encode_len_to(out: &mut Vec<u8>, len: usize) {
    encode_u64_to(out, len as u64);
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
    use crate::proof_skeleton::{
        ProofSkeletonBudget, ProofSkeletonCoreExpr, ProofSkeletonExpectedTypeIdentity,
        ProofSkeletonHole, ProofSkeletonLocalContextIdentity, ProofSkeletonPremiseIdentity,
        ProofSkeletonStaleSolutionRejection, ProofSkeletonStrategyProfile,
        ProofSkeletonStrategyProfileId, ProofSkeletonTargetStatementIdentity, ProofSkeletonTerm,
        PROOF_SKELETON_API_VERSION,
    };
    use crate::proof_sketch::{
        ProofSketchBudget, ProofSketchEdge, ProofSketchEdgeKind, ProofSketchExpectedEffect,
        ProofSketchExpectedEffectKind, ProofSketchFallbackAction, ProofSketchFallbackPolicy,
        ProofSketchRepairProfile, ProofSketchSublemmaStatementProposal,
        ProofSketchTargetStatementIdentity, PROOF_SKETCH_API_VERSION,
    };

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    fn type0() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }

    fn capture(context_hash: Hash, binder_fingerprint_hash: Hash) -> ProofLocalContextCapture {
        ProofLocalContextCapture {
            context_hash,
            binder_fingerprint_hash,
            local_premise_hashes: Vec::new(),
            local_count: 0,
        }
    }

    fn sketch(statement_hash: Hash, env: Hash, policy: Hash) -> ProofSketch {
        ProofSketch {
            api_version: PROOF_SKETCH_API_VERSION.to_owned(),
            sketch_id: hash(0xa0),
            target_statement_identity: ProofSketchTargetStatementIdentity {
                statement_hash,
                input_context_hash: hash(0x20),
                output_context_hash: hash(0x23),
                module: Some("Proofs.Ai.Semantic".to_owned()),
                declaration: Some("target".to_owned()),
            },
            environment_hash: env,
            policy_hash: policy,
            sublemma_statement_proposals: Vec::new(),
            nodes: vec![
                sketch_node("n1", ProofSketchNodeKind::Introduce, hash(0x20), hash(0x21)),
                sketch_node(
                    "n2",
                    ProofSketchNodeKind::CloseByExact,
                    hash(0x21),
                    hash(0x23),
                ),
            ],
            edges: vec![ProofSketchEdge {
                from: "n1".to_owned(),
                to: "n2".to_owned(),
                kind: ProofSketchEdgeKind::DependsOn,
            }],
            advisory: None,
        }
    }

    fn sketch_node(
        node_id: &str,
        kind: ProofSketchNodeKind,
        input_context_hash: Hash,
        output_context_hash: Hash,
    ) -> crate::proof_sketch::ProofSketchNode {
        crate::proof_sketch::ProofSketchNode {
            node_id: node_id.to_owned(),
            kind,
            input_context_hash,
            output_context_hash,
            expected_effect: ProofSketchExpectedEffect {
                kind: if kind == ProofSketchNodeKind::CloseByExact {
                    ProofSketchExpectedEffectKind::ClosesGoal
                } else {
                    ProofSketchExpectedEffectKind::IntroducesLocals
                },
                goal_delta: if kind == ProofSketchNodeKind::CloseByExact {
                    -1
                } else {
                    0
                },
                effect_hash: Some(hash(0x31)),
            },
            strategy_hints: Vec::new(),
            budget: ProofSketchBudget {
                max_candidates: 1,
                max_search_nodes: 8,
                max_depth: Some(2),
                max_repair_steps: Some(0),
            },
            fallback_policy: ProofSketchFallbackPolicy {
                action: ProofSketchFallbackAction::Fail,
                fallback_node_id: None,
                repair_profile: Some(ProofSketchRepairProfile::None),
            },
            statement_proposal_id: None,
            premise_hashes: Vec::new(),
            display: None,
        }
    }

    fn skeleton(
        statement_hash: Hash,
        expected_type_hash: Hash,
        env: Hash,
        policy: Hash,
    ) -> ProofSkeleton {
        ProofSkeleton {
            api_version: PROOF_SKELETON_API_VERSION.to_owned(),
            skeleton_id: hash(0xb0),
            target_statement_identity: ProofSkeletonTargetStatementIdentity {
                statement_hash,
                expected_type_hash,
                root_context_hash: hash(0x20),
                module: Some("Proofs.Ai.Semantic".to_owned()),
                declaration: Some("target".to_owned()),
            },
            environment_hash: env,
            policy_hash: policy,
            root: ProofSkeletonTerm::Hole {
                hole_id: "h1".to_owned(),
            },
            holes: vec![ProofSkeletonHole {
                hole_id: "h1".to_owned(),
                local_context_identity: ProofSkeletonLocalContextIdentity {
                    context_hash: hash(0x21),
                    binder_fingerprint_hash: hash(0x22),
                },
                expected_type_identity: ProofSkeletonExpectedTypeIdentity {
                    expected_type_hash,
                    expected_type: ProofSkeletonCoreExpr::Inline {
                        core_expr_hash: expected_type_hash,
                        canonical_bytes: vec![1],
                    },
                },
                dependent_hole_ids: Vec::new(),
                allowed_premise_identities: vec![ProofSkeletonPremiseIdentity {
                    premise_hash: hash(0x70),
                    source: ProofSkeletonPremiseSource::VerifiedImport,
                    axiom_profile_hash: policy,
                }],
                strategy_profile: ProofSkeletonStrategyProfile {
                    profile_id: ProofSkeletonStrategyProfileId::Exact,
                    preferred_node_kinds: Vec::new(),
                },
                budget: ProofSkeletonBudget {
                    max_candidates: 1,
                    max_search_nodes: 8,
                    max_depth: Some(2),
                    max_repair_steps: Some(0),
                },
                stale_solution_rejection: ProofSkeletonStaleSolutionRejection {
                    required_context_hash: hash(0x21),
                    required_expected_type_hash: expected_type_hash,
                    required_environment_hash: env,
                    required_policy_hash: policy,
                },
            }],
        }
    }

    fn semantic_profile(
        statement_hash: Hash,
        expected_type_hash: Hash,
        env: Hash,
        policy: Hash,
    ) -> ProofSemanticValidationProfile {
        ProofSemanticValidationProfile::strict(env, policy, statement_hash)
            .with_typed_statement(ProofTypedStatementArtifact::new(
                statement_hash,
                expected_type_hash,
                hash(0x20),
                env,
                policy,
                policy,
            ))
            .with_local_context_capture(capture(hash(0x20), hash(0x24)))
            .with_local_context_capture(capture(hash(0x21), hash(0x22)))
            .with_local_context_capture(capture(hash(0x23), hash(0x25)))
            .with_verified_import_premise(hash(0x70))
    }

    #[test]
    fn sketch_validator_semantic_accepts_typed_context_policy_contract() {
        let statement_hash = hash(0x11);
        let expected_type_hash = hash(0x12);
        let env = hash(0x01);
        let policy = hash(0x02);
        let sketch = sketch(statement_hash, env, policy);
        let skeleton = skeleton(statement_hash, expected_type_hash, env, policy);
        let profile = semantic_profile(statement_hash, expected_type_hash, env, policy);

        let report = validate_proof_sketch_semantics(&sketch, &skeleton, &profile)
            .expect("semantic contract should validate");
        assert_eq!(report.hole_ids, vec!["h1".to_owned()]);
        assert_eq!(report.allowed_premise_hashes, vec![hash(0x70)]);
        assert!(report.typed_statement_hashes.contains(&statement_hash));
    }

    #[test]
    fn sketch_validator_semantic_rejects_negative_fixtures() {
        let statement_hash = hash(0x11);
        let expected_type_hash = hash(0x12);
        let env = hash(0x01);
        let policy = hash(0x02);
        let base_sketch = sketch(statement_hash, env, policy);
        let base_skeleton = skeleton(statement_hash, expected_type_hash, env, policy);
        let base_profile = semantic_profile(statement_hash, expected_type_hash, env, policy);

        let mut parent_assumption = base_sketch.clone();
        parent_assumption
            .sublemma_statement_proposals
            .push(ProofSketchSublemmaStatementProposal {
                proposal_id: "p-parent".to_owned(),
                statement_hash,
                input_context_hash: hash(0x20),
                output_context_hash: hash(0x21),
                generalization_policy: ProofSketchGeneralizationPolicy::LocalsOnly,
                display: None,
            });
        let err =
            validate_proof_sketch_semantics(&parent_assumption, &base_skeleton, &base_profile)
                .expect_err("parent conclusion assumption should reject");
        assert!(matches!(
            err.kind(),
            ProofSemanticValidationErrorKind::ParentConclusionAssumption { .. }
        ));

        let lemma_hash = hash(0x44);
        let generalized = ProofLocalStatementGeneralization {
            source_context_hash: hash(0x20),
            source_statement_hash: hash(0x45),
            captured_local_indices: Vec::new(),
            binders: Vec::new(),
            minimized_universe_params: Vec::new(),
            unfold_local_definitions: true,
            generalized_statement_hash: lemma_hash,
        };
        let mut future_lemma = base_sketch.clone();
        future_lemma
            .sublemma_statement_proposals
            .push(ProofSketchSublemmaStatementProposal {
                proposal_id: "p-future".to_owned(),
                statement_hash: lemma_hash,
                input_context_hash: hash(0x20),
                output_context_hash: hash(0x21),
                generalization_policy: ProofSketchGeneralizationPolicy::LocalsOnly,
                display: None,
            });
        future_lemma.nodes[1].premise_hashes.push(lemma_hash);
        let future_profile = base_profile
            .clone()
            .with_typed_statement(ProofTypedStatementArtifact::new(
                lemma_hash,
                expected_type_hash,
                hash(0x20),
                env,
                policy,
                policy,
            ))
            .with_generalized_local_statement(generalized);
        let err = validate_proof_sketch_semantics(&future_lemma, &base_skeleton, &future_profile)
            .expect_err("future unproved local lemma should reject");
        assert!(matches!(
            err.kind(),
            ProofSemanticValidationErrorKind::FutureUnprovedLocalLemmaReference { .. }
        ));

        let mut stronger_axiom = base_skeleton.clone();
        stronger_axiom.holes[0].allowed_premise_identities[0].axiom_profile_hash = hash(0xaa);
        let err = validate_proof_sketch_semantics(&base_sketch, &stronger_axiom, &base_profile)
            .expect_err("axiom-profile expansion should reject");
        assert!(matches!(
            err.kind(),
            ProofSemanticValidationErrorKind::AxiomProfileExpansion { .. }
        ));

        let mut stale_context = base_sketch;
        stale_context.nodes[0].input_context_hash = hash(0xee);
        let err = validate_proof_sketch_semantics(&stale_context, &base_skeleton, &base_profile)
            .expect_err("stale context hash should reject");
        assert!(matches!(
            err.kind(),
            ProofSemanticValidationErrorKind::MissingLocalContextCapture { .. }
        ));
    }

    #[test]
    fn local_context_generalization_enumerates_dependency_ordered_binders() {
        let context = vec![
            MachineLocalDecl::assumption("A", type0()),
            MachineLocalDecl::assumption("x", Expr::bvar(0)),
        ];
        let statement = Expr::bvar(0);
        let generalization = generalize_local_context_statement(
            &context,
            &statement,
            &ProofLocalStatementGeneralizationPolicy::default(),
        )
        .expect("generalization should be computed");
        assert_eq!(generalization.captured_local_indices, vec![0, 1]);
        assert_eq!(generalization.binders.len(), 2);
        validate_local_context_generalization(&context, &statement, &generalization)
            .expect("computed generalization should validate");

        let mut missing = generalization.clone();
        missing.captured_local_indices = vec![1];
        let err = validate_local_context_generalization(&context, &statement, &missing)
            .expect_err("missing captured dependency should reject");
        assert!(matches!(
            err.kind(),
            ProofLocalContextValidationErrorKind::MissingGeneralization { .. }
        ));

        let mut malformed_order = generalization.clone();
        malformed_order.captured_local_indices = vec![1, 0];
        let err = validate_local_context_generalization(&context, &statement, &malformed_order)
            .expect_err("malformed binder order should reject");
        assert!(matches!(
            err.kind(),
            ProofLocalContextValidationErrorKind::MalformedGeneralizedBinderOrder { .. }
        ));

        let mut stale = generalization;
        stale.source_context_hash = hash(0xee);
        let err = validate_local_context_generalization(&context, &statement, &stale)
            .expect_err("stale context hash should reject");
        assert!(matches!(
            err.kind(),
            ProofLocalContextValidationErrorKind::ContextHashMismatch { .. }
        ));
    }

    #[test]
    fn local_context_generalization_rejects_local_scope_escape() {
        let bad_context = vec![MachineLocalDecl::assumption("bad", Expr::bvar(0))];
        let err = proof_local_context_capture(&bad_context)
            .expect_err("local type cannot reference itself or a future local");
        assert!(matches!(
            err.kind(),
            ProofLocalContextValidationErrorKind::LocalScopeEscape { .. }
        ));

        let empty_context = Vec::new();
        let err = generalize_local_context_statement(
            &empty_context,
            &Expr::bvar(0),
            &ProofLocalStatementGeneralizationPolicy::default(),
        )
        .expect_err("statement cannot reference locals outside context");
        assert!(matches!(
            err.kind(),
            ProofLocalContextValidationErrorKind::LocalScopeEscape { .. }
        ));
    }

    #[test]
    fn local_context_generalization_capture_hashes_are_deterministic() {
        let context = vec![MachineLocalDecl::assumption("P", prop())];
        let capture = proof_local_context_capture(&context).expect("context capture should build");
        assert_eq!(capture.local_count, 1);
        assert_eq!(capture.local_premise_hashes.len(), 1);
        validate_proof_local_context_capture(&context, &capture)
            .expect("capture should validate against source context");

        let mut stale = capture;
        stale.binder_fingerprint_hash = hash(0x99);
        let err = validate_proof_local_context_capture(&context, &stale)
            .expect_err("stale binder fingerprint should reject");
        assert!(matches!(
            err.kind(),
            ProofLocalContextValidationErrorKind::BinderFingerprintMismatch { .. }
        ));
    }
}
