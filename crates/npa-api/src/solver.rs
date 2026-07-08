//! Proof-producing solver request/response contracts.
//!
//! This module is an untrusted API/tactic-side contract layer. It binds solver
//! attempts to deterministic identities and checked payload references, but it
//! does not execute solvers or create proof acceptance by itself.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::{core_expr_hash, Hash};
use npa_kernel::{expr::collect_apps, Expr};
use sha2::{Digest, Sha256};

use crate::advanced_ai::{
    advanced_ai_smt_candidate_canonical_bytes, advanced_ai_smt_nat_to_int_side_condition,
    advanced_ai_smt_nat_to_int_side_condition_hash, advanced_ai_smt_problem_canonical_bytes,
    AdvancedMachineSmtCertificateCandidate, AdvancedMachineSmtEncodedProblem,
    AdvancedMachineSmtProblemRef, AdvancedMachineSmtProofPayloadRef, AdvancedSmtCertificateFormat,
    AdvancedSmtCertificateMetadata, AdvancedSmtLogic, AdvancedSmtSymbol,
};

pub const SOLVER_CONTRACT_VERSION: &str = "npa.solver-contract.v1";
pub const SOLVER_REQUEST_HASH_TAG: &str = "npa.solver.request.v1";
pub const SOLVER_RESPONSE_METADATA_HASH_TAG: &str = "npa.solver.response-metadata.v1";
pub const SOLVER_RESPONSE_IDENTITY_HASH_TAG: &str = "npa.solver.response-identity.v1";
pub const SOLVER_PROOF_PAYLOAD_REF_HASH_TAG: &str = "npa.solver.proof-payload-ref.v1";
pub const SOLVER_CERTIFICATE_METADATA_HASH_TAG: &str = "npa.solver.certificate-metadata.v1";
pub const SOLVER_RECONSTRUCTION_PLAN_HASH_TAG: &str = "npa.solver.reconstruction-plan.v1";
pub const SOLVER_RESOURCE_POLICY_HASH_TAG: &str = "npa.solver.resource-policy.v1";
pub const SOLVER_INLINE_PAYLOAD_HASH_TAG: &str = "npa.solver.inline-payload.v1";
pub const SOLVER_REPLAY_METADATA_HASH_TAG: &str = "npa.solver.replay-metadata.v1";
pub const FINITE_DECIDE_CARRIER_HASH_TAG: &str = "npa.solver.finite-decide.carrier.v1";
pub const FINITE_DECIDE_ENUMERATION_HASH_TAG: &str = "npa.solver.finite-decide.enumeration.v1";
pub const FINITE_DECIDE_PREDICATE_REF_HASH_TAG: &str = "npa.solver.finite-decide.predicate-ref.v1";
pub const FINITE_DECIDE_REFLECTION_CONTRACT_HASH_TAG: &str =
    "npa.solver.finite-decide.reflection-contract.v1";
pub const FINITE_DECIDE_COUNTEREXAMPLE_HASH_TAG: &str =
    "npa.solver.finite-decide.counterexample.v1";
pub const FINITE_DECIDE_PROOF_ARTIFACT_HASH_TAG: &str =
    "npa.solver.finite-decide.proof-artifact.v1";
pub const OMEGA_NORMALIZED_PROBLEM_HASH_TAG: &str = "npa.solver.omega.normalized-problem.v1";
pub const OMEGA_NAT_TO_INT_PROOF_OBLIGATION_HASH_TAG: &str =
    "npa.solver.omega.nat-to-int-proof-obligation.v1";
pub const OMEGA_RECONSTRUCTION_STEP_HASH_TAG: &str = "npa.solver.omega.reconstruction-step.v1";
pub const OMEGA_CERTIFICATE_ARTIFACT_HASH_TAG: &str = "npa.solver.omega.certificate-artifact.v1";
pub const OMEGA_RECONSTRUCTION_PLAN_REF_HASH_TAG: &str =
    "npa.solver.omega.reconstruction-plan-ref.v1";
pub const RING_NF_REFLECTED_EXPR_HASH_TAG: &str = "npa.solver.ring-nf.reflected-expr.v1";
pub const RING_NF_POLYNOMIAL_HASH_TAG: &str = "npa.solver.ring-nf.polynomial.v1";
pub const RING_NF_NORMALIZED_PROBLEM_HASH_TAG: &str = "npa.solver.ring-nf.normalized-problem.v1";
pub const RING_NF_PROFILE_HASH_TAG: &str = "npa.solver.ring-nf.profile.v1";
pub const RING_NF_VARIABLE_ENVIRONMENT_HASH_TAG: &str =
    "npa.solver.ring-nf.variable-environment.v1";
pub const RING_NF_PROOF_ARTIFACT_HASH_TAG: &str = "npa.solver.ring-nf.proof-artifact.v1";
pub const BITBLAST_REFLECTED_EXPR_HASH_TAG: &str = "npa.solver.bitblast.reflected-expr.v1";
pub const BITBLAST_VARIABLE_MAP_HASH_TAG: &str = "npa.solver.bitblast.variable-map.v1";
pub const BITBLAST_CIRCUIT_HASH_TAG: &str = "npa.solver.bitblast.circuit.v1";
pub const BITBLAST_SEMANTIC_PLAN_HASH_TAG: &str = "npa.solver.bitblast.semantic-plan.v1";
pub const BITBLAST_CNF_ARTIFACT_HASH_TAG: &str = "npa.solver.bitblast.cnf-artifact.v1";
pub const BITBLAST_ENCODED_PROBLEM_HASH_TAG: &str = "npa.solver.bitblast.encoded-problem.v1";
pub const BITBLAST_RECONSTRUCTION_STEP_HASH_TAG: &str =
    "npa.solver.bitblast.reconstruction-step.v1";
pub const BITBLAST_SEMANTIC_PROOF_ARTIFACT_HASH_TAG: &str =
    "npa.solver.bitblast.semantic-proof-artifact.v1";
pub const BITBLAST_CANONICAL_CNF_HASH_TAG: &str = "npa.solver.bitblast.canonical-cnf.v1";
pub const BITBLAST_SAT_HANDOFF_HASH_TAG: &str = "npa.solver.bitblast.sat-handoff.v1";
pub const BITBLAST_SAT_MODEL_HASH_TAG: &str = "npa.solver.bitblast.sat-model.v1";
pub const LRAT_CNF_HASH_TAG: &str = "npa.solver.lrat.cnf.v1";
pub const LRAT_CERTIFICATE_HASH_TAG: &str = "npa.solver.lrat.certificate.v1";
pub const LRAT_CHECK_ARTIFACT_HASH_TAG: &str = "npa.solver.lrat.check-artifact.v1";
pub const LRAT_CNF_UNSAT_THEOREM_HASH_TAG: &str = "npa.solver.lrat.cnf-unsat-theorem.v1";
pub const LRAT_CNF_UNSAT_BRIDGE_HASH_TAG: &str = "npa.solver.lrat.cnf-unsat-bridge.v1";
pub const BITBLAST_LRAT_SOUNDNESS_BRIDGE_HASH_TAG: &str =
    "npa.solver.bitblast.lrat-soundness-bridge.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverContractVersion {
    V1,
}

impl SolverContractVersion {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::V1 => SOLVER_CONTRACT_VERSION,
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::V1 => 0,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            SOLVER_CONTRACT_VERSION => Ok(Self::V1),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "version",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverFamily {
    FiniteDecide,
    Omega,
    Ring,
    Bitblast,
    Lrat,
    Smt,
}

impl SolverFamily {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FiniteDecide => "finite_decide",
            Self::Omega => "omega",
            Self::Ring => "ring_nf",
            Self::Bitblast => "bitblast",
            Self::Lrat => "lrat",
            Self::Smt => "smt",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::FiniteDecide => 0,
            Self::Omega => 1,
            Self::Ring => 2,
            Self::Bitblast => 3,
            Self::Lrat => 4,
            Self::Smt => 5,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "finite_decide" | "finite-decide" => Ok(Self::FiniteDecide),
            "omega" => Ok(Self::Omega),
            "ring_nf" | "ring" => Ok(Self::Ring),
            "bitblast" => Ok(Self::Bitblast),
            "lrat" => Ok(Self::Lrat),
            "smt" => Ok(Self::Smt),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "solver_family",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverFragment {
    FiniteEnumerationV1,
    PresburgerLinearArithmeticV1,
    SemiringNormalizationV1,
    BitVectorBitblastV1,
    LratUnsatV1,
    SmtQfUfV1,
    SmtQfLiaV1,
    SmtQfBvV1,
    SmtQfUfLiaBvV1,
}

impl SolverFragment {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FiniteEnumerationV1 => "finite-enumeration.v1",
            Self::PresburgerLinearArithmeticV1 => "presburger-linear-arithmetic.v1",
            Self::SemiringNormalizationV1 => "semiring-normalization.v1",
            Self::BitVectorBitblastV1 => "bitvector-bitblast.v1",
            Self::LratUnsatV1 => "lrat-unsat.v1",
            Self::SmtQfUfV1 => "smt-qf-uf.v1",
            Self::SmtQfLiaV1 => "smt-qf-lia.v1",
            Self::SmtQfBvV1 => "smt-qf-bv.v1",
            Self::SmtQfUfLiaBvV1 => "smt-qf-uf-lia-bv.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::FiniteEnumerationV1 => 0,
            Self::PresburgerLinearArithmeticV1 => 1,
            Self::SemiringNormalizationV1 => 2,
            Self::BitVectorBitblastV1 => 3,
            Self::LratUnsatV1 => 4,
            Self::SmtQfUfV1 => 5,
            Self::SmtQfLiaV1 => 6,
            Self::SmtQfBvV1 => 7,
            Self::SmtQfUfLiaBvV1 => 8,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "finite-enumeration.v1" => Ok(Self::FiniteEnumerationV1),
            "presburger-linear-arithmetic.v1" => Ok(Self::PresburgerLinearArithmeticV1),
            "semiring-normalization.v1" => Ok(Self::SemiringNormalizationV1),
            "bitvector-bitblast.v1" => Ok(Self::BitVectorBitblastV1),
            "lrat-unsat.v1" => Ok(Self::LratUnsatV1),
            "smt-qf-uf.v1" => Ok(Self::SmtQfUfV1),
            "smt-qf-lia.v1" => Ok(Self::SmtQfLiaV1),
            "smt-qf-bv.v1" => Ok(Self::SmtQfBvV1),
            "smt-qf-uf-lia-bv.v1" => Ok(Self::SmtQfUfLiaBvV1),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "fragment",
                tag: value.to_owned(),
            }),
        }
    }

    fn from_advanced_smt_logic(logic: AdvancedSmtLogic) -> Self {
        match logic {
            AdvancedSmtLogic::MvpQfUf => Self::SmtQfUfV1,
            AdvancedSmtLogic::MvpQfLia => Self::SmtQfLiaV1,
            AdvancedSmtLogic::MvpQfBv => Self::SmtQfBvV1,
            AdvancedSmtLogic::MvpQfUfLiaBv => Self::SmtQfUfLiaBvV1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverProfile {
    DirectProofTermV1,
    CheckedCertificateV1,
    AdvancedSmtMvpV1,
    ExternalSidecarV1,
}

impl SolverProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DirectProofTermV1 => "direct-proof-term.v1",
            Self::CheckedCertificateV1 => "checked-certificate.v1",
            Self::AdvancedSmtMvpV1 => "advanced-smt-mvp.v1",
            Self::ExternalSidecarV1 => "external-sidecar.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::DirectProofTermV1 => 0,
            Self::CheckedCertificateV1 => 1,
            Self::AdvancedSmtMvpV1 => 2,
            Self::ExternalSidecarV1 => 3,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "direct-proof-term.v1" => Ok(Self::DirectProofTermV1),
            "checked-certificate.v1" => Ok(Self::CheckedCertificateV1),
            "advanced-smt-mvp.v1" => Ok(Self::AdvancedSmtMvpV1),
            "external-sidecar.v1" => Ok(Self::ExternalSidecarV1),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "profile",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverResourcePolicyProfile {
    PlaceholderV1,
    FamilyDefaultV1,
    FiniteDecideDefaultV1,
    OmegaDefaultV1,
    RingNfDefaultV1,
    BitblastDefaultV1,
    LratDefaultV1,
    SmtReconstructionDefaultV1,
}

impl SolverResourcePolicyProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PlaceholderV1 => "placeholder.v1",
            Self::FamilyDefaultV1 => "family-default.v1",
            Self::FiniteDecideDefaultV1 => "finite_decide.default.v1",
            Self::OmegaDefaultV1 => "omega.default.v1",
            Self::RingNfDefaultV1 => "ring_nf.default.v1",
            Self::BitblastDefaultV1 => "bitblast.default.v1",
            Self::LratDefaultV1 => "lrat.default.v1",
            Self::SmtReconstructionDefaultV1 => "smt-reconstruction.default.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::PlaceholderV1 => 0,
            Self::FamilyDefaultV1 => 1,
            Self::FiniteDecideDefaultV1 => 2,
            Self::OmegaDefaultV1 => 3,
            Self::RingNfDefaultV1 => 4,
            Self::BitblastDefaultV1 => 5,
            Self::LratDefaultV1 => 6,
            Self::SmtReconstructionDefaultV1 => 7,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "placeholder.v1" => Ok(Self::PlaceholderV1),
            "family-default.v1" => Ok(Self::FamilyDefaultV1),
            "finite_decide.default.v1" | "finite-decide.default.v1" => {
                Ok(Self::FiniteDecideDefaultV1)
            }
            "omega.default.v1" => Ok(Self::OmegaDefaultV1),
            "ring_nf.default.v1" | "ring.default.v1" => Ok(Self::RingNfDefaultV1),
            "bitblast.default.v1" => Ok(Self::BitblastDefaultV1),
            "lrat.default.v1" => Ok(Self::LratDefaultV1),
            "smt-reconstruction.default.v1" | "smt.default.v1" => {
                Ok(Self::SmtReconstructionDefaultV1)
            }
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "resource_policy_profile",
                tag: value.to_owned(),
            }),
        }
    }

    pub const fn default_family(self) -> Option<SolverFamily> {
        match self {
            Self::FiniteDecideDefaultV1 => Some(SolverFamily::FiniteDecide),
            Self::OmegaDefaultV1 => Some(SolverFamily::Omega),
            Self::RingNfDefaultV1 => Some(SolverFamily::Ring),
            Self::BitblastDefaultV1 => Some(SolverFamily::Bitblast),
            Self::LratDefaultV1 => Some(SolverFamily::Lrat),
            Self::SmtReconstructionDefaultV1 => Some(SolverFamily::Smt),
            Self::PlaceholderV1 | Self::FamilyDefaultV1 => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverCertificateFormat {
    DirectNpaProofTermV1,
    LratV1,
    MvpSmtProofNodeTableV1,
    AletheOpaqueV1,
    LfscOpaqueV1,
    SolverResultOnlyV1,
    OmegaPresburgerTraceV1,
}

impl SolverCertificateFormat {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DirectNpaProofTermV1 => "direct-npa-proof-term.v1",
            Self::LratV1 => "lrat.v1",
            Self::MvpSmtProofNodeTableV1 => "mvp-smt-proof-node-table.v1",
            Self::AletheOpaqueV1 => "alethe-opaque.v1",
            Self::LfscOpaqueV1 => "lfsc-opaque.v1",
            Self::SolverResultOnlyV1 => "solver-result-only.v1",
            Self::OmegaPresburgerTraceV1 => "omega-presburger-trace.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::DirectNpaProofTermV1 => 0,
            Self::LratV1 => 1,
            Self::MvpSmtProofNodeTableV1 => 2,
            Self::AletheOpaqueV1 => 3,
            Self::LfscOpaqueV1 => 4,
            Self::SolverResultOnlyV1 => 5,
            Self::OmegaPresburgerTraceV1 => 6,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "direct-npa-proof-term.v1" => Ok(Self::DirectNpaProofTermV1),
            "lrat.v1" => Ok(Self::LratV1),
            "mvp-smt-proof-node-table.v1" => Ok(Self::MvpSmtProofNodeTableV1),
            "alethe-opaque.v1" => Ok(Self::AletheOpaqueV1),
            "lfsc-opaque.v1" => Ok(Self::LfscOpaqueV1),
            "solver-result-only.v1" => Ok(Self::SolverResultOnlyV1),
            "omega-presburger-trace.v1" => Ok(Self::OmegaPresburgerTraceV1),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "certificate_format",
                tag: value.to_owned(),
            }),
        }
    }

    fn from_advanced_smt(format: AdvancedSmtCertificateFormat) -> Self {
        match format {
            AdvancedSmtCertificateFormat::MvpProofNodeTableV1 => Self::MvpSmtProofNodeTableV1,
            AdvancedSmtCertificateFormat::AletheOpaqueV1 => Self::AletheOpaqueV1,
            AdvancedSmtCertificateFormat::LfscOpaqueV1 => Self::LfscOpaqueV1,
            AdvancedSmtCertificateFormat::SolverResultOnlyV1 => Self::SolverResultOnlyV1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FiniteDecideCarrierKind {
    Bool,
    Fin,
    VectorBool,
    SmallExplicitFinite,
    ExplicitFinite,
}

impl FiniteDecideCarrierKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Bool => "Bool",
            Self::Fin => "Fin",
            Self::VectorBool => "Vector Bool",
            Self::SmallExplicitFinite => "small-explicit-finite",
            Self::ExplicitFinite => "ExplicitFinite",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Bool => 0,
            Self::Fin => 1,
            Self::VectorBool => 2,
            Self::SmallExplicitFinite => 3,
            Self::ExplicitFinite => 4,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "Bool" | "bool" => Ok(Self::Bool),
            "Fin" | "fin" => Ok(Self::Fin),
            "Vector Bool" | "vector-bool" | "Vector.Bool" => Ok(Self::VectorBool),
            "small-explicit-finite" => Ok(Self::SmallExplicitFinite),
            "ExplicitFinite" | "explicit-finite" => Ok(Self::ExplicitFinite),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "finite_decide_carrier",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FiniteDecideSmallCarrierKind {
    Empty,
    Unit,
    Option,
    Product,
    Sum,
}

impl FiniteDecideSmallCarrierKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Empty => "Empty",
            Self::Unit => "Unit",
            Self::Option => "Option",
            Self::Product => "Product",
            Self::Sum => "Sum",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Empty => 0,
            Self::Unit => 1,
            Self::Option => 2,
            Self::Product => 3,
            Self::Sum => 4,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "Empty" | "empty" => Ok(Self::Empty),
            "Unit" | "unit" => Ok(Self::Unit),
            "Option" | "option" => Ok(Self::Option),
            "Product" | "product" | "Prod" | "prod" => Ok(Self::Product),
            "Sum" | "sum" => Ok(Self::Sum),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "finite_decide_small_carrier",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FiniteDecideElementOrigin {
    BoolFalse,
    BoolTrue,
    FinOrdinal(u64),
    VectorBoolBits(Vec<bool>),
    ExplicitIndex { index_hash: Hash },
    SmallExplicitOrdinal { ordinal: u64 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideCarrierRef {
    pub version: SolverContractVersion,
    pub kind: FiniteDecideCarrierKind,
    pub small_kind: Option<FiniteDecideSmallCarrierKind>,
    pub carrier_type_hash: Hash,
    pub universe_params: Vec<String>,
    pub cardinality: u64,
    pub fin_bound: Option<u64>,
    pub vector_bool_length: Option<u64>,
    pub explicit_finite_evidence_hash: Option<Hash>,
    pub no_duplicate_evidence_hash: Option<Hash>,
    pub complete_evidence_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideElement {
    pub ordinal: u64,
    pub element_hash: Hash,
    pub element_type_hash: Hash,
    pub origin: FiniteDecideElementOrigin,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideEnumeration {
    pub carrier: FiniteDecideCarrierRef,
    pub elements: Vec<FiniteDecideElement>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecidePredicateRef {
    pub predicate_hash: Hash,
    pub predicate_type_hash: Hash,
    pub reflected_decidable_hash: Hash,
    pub local_context_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub universe_params: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideReflectionContract {
    pub version: SolverContractVersion,
    pub request: SolverRequest,
    pub enumeration: FiniteDecideEnumeration,
    pub predicate: FiniteDecidePredicateRef,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideCounterexampleArtifact {
    pub version: SolverContractVersion,
    pub reflection_contract_hash: Hash,
    pub enumeration_hash: Hash,
    pub element: FiniteDecideElement,
    pub predicate_hash: Hash,
    pub predicate_evidence_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FiniteDecideGoalKind {
    Universal,
    Existential,
    Equality,
    BooleanDecision,
}

impl FiniteDecideGoalKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Universal => "universal",
            Self::Existential => "existential",
            Self::Equality => "equality",
            Self::BooleanDecision => "boolean-decision",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Universal => 0,
            Self::Existential => 1,
            Self::Equality => 2,
            Self::BooleanDecision => 3,
        }
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "universal" => Ok(Self::Universal),
            "existential" => Ok(Self::Existential),
            "equality" => Ok(Self::Equality),
            "boolean-decision" => Ok(Self::BooleanDecision),
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "finite_decide_goal_kind",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FiniteDecideDecisionValue {
    PredicateTrue,
    PredicateFalse,
}

impl FiniteDecideDecisionValue {
    fn tag(self) -> u8 {
        match self {
            Self::PredicateTrue => 0,
            Self::PredicateFalse => 1,
        }
    }

    fn is_true(self) -> bool {
        matches!(self, Self::PredicateTrue)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideElementDecision {
    pub element: FiniteDecideElement,
    pub value: FiniteDecideDecisionValue,
    pub predicate_evidence_hash: Hash,
    pub proof_term_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDecideProofArtifact {
    pub version: SolverContractVersion,
    pub reflection_contract_hash: Hash,
    pub enumeration_hash: Hash,
    pub predicate_hash: Hash,
    pub goal_kind: FiniteDecideGoalKind,
    pub fold_result: bool,
    pub element_decisions: Vec<FiniteDecideElementDecision>,
    pub proof_identity: SolverCheckedProofTermIdentity,
    pub generated_term_nodes: u64,
    pub proof_bytes: u64,
    pub proof_steps: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaFragmentProfile {
    LinearArithmeticV1,
    BoundedQuantifierExpansionV1,
}

impl OmegaFragmentProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LinearArithmeticV1 => "linear-arithmetic.v1",
            Self::BoundedQuantifierExpansionV1 => "bounded-quantifier-expansion.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::LinearArithmeticV1 => 0,
            Self::BoundedQuantifierExpansionV1 => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaTermSort {
    Int,
    Nat,
}

impl OmegaTermSort {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Int => "Int",
            Self::Nat => "Nat",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Int => 0,
            Self::Nat => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaComparisonOp {
    Le,
    Lt,
    Eq,
}

impl OmegaComparisonOp {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Le => "<=",
            Self::Lt => "<",
            Self::Eq => "=",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Le => 0,
            Self::Lt => 1,
            Self::Eq => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaBooleanOp {
    And,
    Or,
    Not,
}

impl OmegaBooleanOp {
    fn tag(self) -> u8 {
        match self {
            Self::And => 0,
            Self::Or => 1,
            Self::Not => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaBoundedQuantifierKind {
    Forall,
    Exists,
}

impl OmegaBoundedQuantifierKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Forall => "bounded-forall",
            Self::Exists => "bounded-exists",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Forall => 0,
            Self::Exists => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaNatToIntDischarge {
    ProofObligation { obligation_hash: Hash },
    ImportedTheorem { theorem_hash: Hash },
    Missing,
}

impl OmegaNatToIntDischarge {
    fn tag(self) -> u8 {
        match self {
            Self::ProofObligation { .. } => 0,
            Self::ImportedTheorem { .. } => 1,
            Self::Missing => 2,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaNormalizationOptions {
    pub max_input_nodes: u64,
    pub max_variables: u64,
    pub max_bounded_quantifier_cases: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaLocalContextEntry {
    pub name: String,
    pub ty: Expr,
    pub sort: OmegaTermSort,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaVariable {
    pub ordinal: u64,
    pub local_index: u64,
    pub name: String,
    pub sort: OmegaTermSort,
    pub source_core_expr_hash: Hash,
    pub type_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaLinearTerm {
    pub coefficients: Vec<i64>,
    pub constant: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaAtom {
    pub relation: OmegaComparisonOp,
    pub lhs: OmegaLinearTerm,
    pub rhs: OmegaLinearTerm,
    pub normalized_lhs_minus_rhs: OmegaLinearTerm,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OmegaFormula {
    Atom(OmegaAtom),
    Boolean {
        op: OmegaBooleanOp,
        args: Vec<OmegaFormula>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaNatToIntSideCondition {
    pub variable_ordinal: u64,
    pub source_core_expr_hash: Hash,
    pub int_symbol: AdvancedSmtSymbol,
    pub smt_side_condition_hash: Hash,
    pub discharge: OmegaNatToIntDischarge,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaBoundedQuantifierExpansion {
    pub kind: OmegaBoundedQuantifierKind,
    pub binder_name: String,
    pub bound: u64,
    pub expanded_case_hashes: Vec<Hash>,
    pub source_core_expr_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaNormalizedProblem {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub fragment_profile: OmegaFragmentProfile,
    pub input_nodes: u64,
    pub normalized_nodes: u64,
    pub variables: Vec<OmegaVariable>,
    pub formula: OmegaFormula,
    pub nat_to_int_side_conditions: Vec<OmegaNatToIntSideCondition>,
    pub bounded_expansions: Vec<OmegaBoundedQuantifierExpansion>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaCertificateConclusion {
    Contradiction,
}

impl OmegaCertificateConclusion {
    fn tag(self) -> u8 {
        match self {
            Self::Contradiction => 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OmegaReconstructionRule {
    ComparisonNormalization,
    BooleanSplit,
    NatSideConditionDischarge,
    LinearCombination,
    Contradiction,
}

impl OmegaReconstructionRule {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ComparisonNormalization => "comparison-normalization",
            Self::BooleanSplit => "boolean-split",
            Self::NatSideConditionDischarge => "nat-side-condition-discharge",
            Self::LinearCombination => "linear-combination",
            Self::Contradiction => "contradiction",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::ComparisonNormalization => 0,
            Self::BooleanSplit => 1,
            Self::NatSideConditionDischarge => 2,
            Self::LinearCombination => 3,
            Self::Contradiction => 4,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaReconstructionStep {
    pub step_id: String,
    pub rule: OmegaReconstructionRule,
    pub input_step_ids: Vec<String>,
    pub atom_indices: Vec<u64>,
    pub coefficients: Vec<i64>,
    pub constant: i64,
    pub side_condition_ordinals: Vec<u64>,
    pub result_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmegaCertificateArtifact {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub normalized_problem_hash: Hash,
    pub policy_hash: Hash,
    pub conclusion: OmegaCertificateConclusion,
    pub steps: Vec<OmegaReconstructionStep>,
    pub final_step_id: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RingNfAlgebraProfile {
    SemiringV1,
    RingV1,
    CommutativeSemiringV1,
    CommutativeRingV1,
}

impl RingNfAlgebraProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SemiringV1 => "semiring.v1",
            Self::RingV1 => "ring.v1",
            Self::CommutativeSemiringV1 => "commutative-semiring.v1",
            Self::CommutativeRingV1 => "commutative-ring.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::SemiringV1 => 0,
            Self::RingV1 => 1,
            Self::CommutativeSemiringV1 => 2,
            Self::CommutativeRingV1 => 3,
        }
    }

    pub const fn is_commutative(self) -> bool {
        matches!(self, Self::CommutativeSemiringV1 | Self::CommutativeRingV1)
    }

    pub const fn allows_signed_coefficients(self) -> bool {
        matches!(self, Self::RingV1 | Self::CommutativeRingV1)
    }

    pub fn from_wire(value: &str) -> Result<Self, SolverContractError> {
        match value {
            "semiring.v1" | "semiring" => Ok(Self::SemiringV1),
            "ring.v1" | "ring" => Ok(Self::RingV1),
            "commutative-semiring.v1" | "comm-semiring.v1" | "commutative semiring" => {
                Ok(Self::CommutativeSemiringV1)
            }
            "commutative-ring.v1" | "comm-ring.v1" | "commutative ring" => {
                Ok(Self::CommutativeRingV1)
            }
            _ => Err(SolverContractError::UnknownProfileTag {
                field: "ring_nf_algebra_profile",
                tag: value.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RingNfCoefficientDomain {
    Nat,
    Int,
}

impl RingNfCoefficientDomain {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Nat => "Nat",
            Self::Int => "Int",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Nat => 0,
            Self::Int => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfNormalizationOptions {
    pub algebra_profile: RingNfAlgebraProfile,
    pub max_input_nodes: u64,
    pub max_variables: u64,
    pub max_monomials: u64,
    pub max_total_degree: u64,
    pub max_coefficient_abs: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfLocalContextEntry {
    pub name: String,
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfVariable {
    pub ordinal: u64,
    pub local_index: u64,
    pub name: String,
    pub source_core_expr_hash: Hash,
    pub type_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RingNfReflectedExpr {
    Constant {
        value: i64,
        source_core_expr_hash: Hash,
    },
    Variable {
        variable_ordinal: u64,
        source_core_expr_hash: Hash,
    },
    Add {
        args: Vec<RingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Mul {
        args: Vec<RingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Neg {
        arg: Box<RingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Sub {
        lhs: Box<RingNfReflectedExpr>,
        rhs: Box<RingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Pow {
        base: Box<RingNfReflectedExpr>,
        exponent: u64,
        source_core_expr_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfMonomial {
    pub coefficient: i64,
    pub exponents: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfPolynomial {
    pub monomials: Vec<RingNfMonomial>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfEquation {
    pub carrier_type_hash: Hash,
    pub lhs_reflected: RingNfReflectedExpr,
    pub rhs_reflected: RingNfReflectedExpr,
    pub lhs_normal_form: RingNfPolynomial,
    pub rhs_normal_form: RingNfPolynomial,
    pub difference_normal_form: Option<RingNfPolynomial>,
    pub normal_forms_equal: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfNormalizedProblem {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub algebra_profile: RingNfAlgebraProfile,
    pub coefficient_domain: RingNfCoefficientDomain,
    pub input_nodes: u64,
    pub normalized_nodes: u64,
    pub variables: Vec<RingNfVariable>,
    pub equation: RingNfEquation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RingNfAlgebraLawKind {
    ReflectionSoundness,
    VariableEnvironment,
    CoefficientEvaluation,
    AdditionNormalization,
    MultiplicationNormalization,
    NegationNormalization,
    SubtractionNormalization,
    PowerNormalization,
    CommutativeReordering,
}

impl RingNfAlgebraLawKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReflectionSoundness => "reflection-soundness",
            Self::VariableEnvironment => "variable-environment",
            Self::CoefficientEvaluation => "coefficient-evaluation",
            Self::AdditionNormalization => "addition-normalization",
            Self::MultiplicationNormalization => "multiplication-normalization",
            Self::NegationNormalization => "negation-normalization",
            Self::SubtractionNormalization => "subtraction-normalization",
            Self::PowerNormalization => "power-normalization",
            Self::CommutativeReordering => "commutative-reordering",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::ReflectionSoundness => 0,
            Self::VariableEnvironment => 1,
            Self::CoefficientEvaluation => 2,
            Self::AdditionNormalization => 3,
            Self::MultiplicationNormalization => 4,
            Self::NegationNormalization => 5,
            Self::SubtractionNormalization => 6,
            Self::PowerNormalization => 7,
            Self::CommutativeReordering => 8,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfVariableEnvironmentEntry {
    pub variable_ordinal: u64,
    pub source_core_expr_hash: Hash,
    pub type_hash: Hash,
    pub value_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfAlgebraLawRef {
    pub law: RingNfAlgebraLawKind,
    pub profile: RingNfAlgebraProfile,
    pub theorem_hash: Hash,
    pub theorem_type_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNfProofArtifact {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub normalized_problem_hash: Hash,
    pub profile_hash: Hash,
    pub variable_environment_hash: Hash,
    pub policy_hash: Hash,
    pub lhs_reflected_expr_hash: Hash,
    pub rhs_reflected_expr_hash: Hash,
    pub lhs_normal_form_hash: Hash,
    pub rhs_normal_form_hash: Hash,
    pub difference_normal_form_hash: Option<Hash>,
    pub variable_environment: Vec<RingNfVariableEnvironmentEntry>,
    pub algebra_law_refs: Vec<RingNfAlgebraLawRef>,
    pub proof_identity: SolverCheckedProofTermIdentity,
    pub generated_term_nodes: u64,
    pub proof_bytes: u64,
    pub proof_steps: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastSort {
    Bool,
    BitVector { width: u64 },
}

impl BitblastSort {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Bool => "Bool",
            Self::BitVector { .. } => "BitVector",
        }
    }

    fn tag(&self) -> u8 {
        match self {
            Self::Bool => 0,
            Self::BitVector { .. } => 1,
        }
    }

    fn width_bits(&self) -> u64 {
        match self {
            Self::Bool => 1,
            Self::BitVector { width } => *width,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastOperationProfile {
    BoolFormulaV1,
    FixedWidthBitVectorV1,
    MixedBoolBitVectorV1,
}

impl BitblastOperationProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BoolFormulaV1 => "bool-formula.v1",
            Self::FixedWidthBitVectorV1 => "fixed-width-bitvector.v1",
            Self::MixedBoolBitVectorV1 => "mixed-bool-bitvector.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::BoolFormulaV1 => 0,
            Self::FixedWidthBitVectorV1 => 1,
            Self::MixedBoolBitVectorV1 => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastBackendProfile {
    CnfTseitinV1,
    BddV1,
}

impl BitblastBackendProfile {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CnfTseitinV1 => "cnf-tseitin.v1",
            Self::BddV1 => "bdd.v1",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::CnfTseitinV1 => 0,
            Self::BddV1 => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastUnaryOp {
    Not,
    BvNot,
}

impl BitblastUnaryOp {
    fn tag(self) -> u8 {
        match self {
            Self::Not => 0,
            Self::BvNot => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastBinaryOp {
    And,
    Or,
    Xor,
    Iff,
    Implies,
    BvAnd,
    BvOr,
    BvXor,
}

impl BitblastBinaryOp {
    fn tag(self) -> u8 {
        match self {
            Self::And => 0,
            Self::Or => 1,
            Self::Xor => 2,
            Self::Iff => 3,
            Self::Implies => 4,
            Self::BvAnd => 5,
            Self::BvOr => 6,
            Self::BvXor => 7,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastCircuitNodeKind {
    Input,
    Constant,
    Not,
    And,
    Or,
    Xor,
    Iff,
    Implies,
    Equal,
    OutputAssertion,
}

impl BitblastCircuitNodeKind {
    fn tag(self) -> u8 {
        match self {
            Self::Input => 0,
            Self::Constant => 1,
            Self::Not => 2,
            Self::And => 3,
            Self::Or => 4,
            Self::Xor => 5,
            Self::Iff => 6,
            Self::Implies => 7,
            Self::Equal => 8,
            Self::OutputAssertion => 9,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastClauseRole {
    ConstantDefinition,
    TseitinDefinition,
    OutputAssertion,
}

impl BitblastClauseRole {
    fn tag(self) -> u8 {
        match self {
            Self::ConstantDefinition => 0,
            Self::TseitinDefinition => 1,
            Self::OutputAssertion => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastSemanticStepKind {
    ReflectInputAst,
    BuildVariableMap,
    TranslateAstToCircuit,
    TranslateCircuitToCnf,
    AssertOutputLiteral,
}

impl BitblastSemanticStepKind {
    fn tag(self) -> u8 {
        match self {
            Self::ReflectInputAst => 0,
            Self::BuildVariableMap => 1,
            Self::TranslateAstToCircuit => 2,
            Self::TranslateCircuitToCnf => 3,
            Self::AssertOutputLiteral => 4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitblastReconstructionStepKind {
    ExpressionToCircuitSemantics,
    VariableMapCorrectness,
    TseitinEquisatisfiability,
    CnfOutputAssertion,
    CnfUnsatImpliesOriginalGoal,
}

impl BitblastReconstructionStepKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExpressionToCircuitSemantics => "expression-to-circuit-semantics",
            Self::VariableMapCorrectness => "variable-map-correctness",
            Self::TseitinEquisatisfiability => "tseitin-equisatisfiability",
            Self::CnfOutputAssertion => "cnf-output-assertion",
            Self::CnfUnsatImpliesOriginalGoal => "cnf-unsat-implies-original-goal",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::ExpressionToCircuitSemantics => 0,
            Self::VariableMapCorrectness => 1,
            Self::TseitinEquisatisfiability => 2,
            Self::CnfOutputAssertion => 3,
            Self::CnfUnsatImpliesOriginalGoal => 4,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastEncodingOptions {
    pub backend_profile: BitblastBackendProfile,
    pub max_input_nodes: u64,
    pub max_variables: u64,
    pub max_bitvector_width: u64,
    pub max_cnf_variables: u64,
    pub max_cnf_clauses: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastLocalContextEntry {
    pub name: String,
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastVariable {
    pub ordinal: u64,
    pub local_index: u64,
    pub name: String,
    pub sort: BitblastSort,
    pub source_core_expr_hash: Hash,
    pub type_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BitblastReflectedExpr {
    BoolConstant {
        value: bool,
        source_core_expr_hash: Hash,
    },
    Variable {
        variable_ordinal: u64,
        sort: BitblastSort,
        source_core_expr_hash: Hash,
    },
    Unary {
        op: BitblastUnaryOp,
        arg: Box<BitblastReflectedExpr>,
        result_sort: BitblastSort,
        source_core_expr_hash: Hash,
    },
    Binary {
        op: BitblastBinaryOp,
        lhs: Box<BitblastReflectedExpr>,
        rhs: Box<BitblastReflectedExpr>,
        result_sort: BitblastSort,
        source_core_expr_hash: Hash,
    },
    Equal {
        sort: BitblastSort,
        lhs: Box<BitblastReflectedExpr>,
        rhs: Box<BitblastReflectedExpr>,
        source_core_expr_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastVariableMapEntry {
    pub variable_ordinal: u64,
    pub sort: BitblastSort,
    pub source_core_expr_hash: Hash,
    pub type_hash: Hash,
    pub bit_offset: u64,
    pub bit_width: u64,
    pub tseitin_variable_start: u64,
    pub cnf_literal_start: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastCircuitNode {
    pub node_id: u64,
    pub kind: BitblastCircuitNodeKind,
    pub result_sort: BitblastSort,
    pub input_node_ids: Vec<u64>,
    pub source_reflected_expr_hash: Hash,
    pub output_tseitin_start: u64,
    pub output_width: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitblastCnfLiteral {
    pub variable: u64,
    pub positive: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastCnfClause {
    pub ordinal: u64,
    pub literals: Vec<BitblastCnfLiteral>,
    pub role: BitblastClauseRole,
    pub source_reflected_expr_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastCnfArtifact {
    pub backend_profile: BitblastBackendProfile,
    pub root_reflected_expr_hash: Hash,
    pub variable_map_hash: Hash,
    pub circuit_hash: Hash,
    pub semantic_plan_hash: Hash,
    pub variable_count: u64,
    pub clauses: Vec<BitblastCnfClause>,
    pub output_literal: BitblastCnfLiteral,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastSemanticStep {
    pub ordinal: u64,
    pub kind: BitblastSemanticStepKind,
    pub input_hash: Hash,
    pub output_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastSemanticPlan {
    pub operation_profile: BitblastOperationProfile,
    pub backend_profile: BitblastBackendProfile,
    pub root_reflected_expr_hash: Hash,
    pub variable_map_hash: Hash,
    pub circuit_hash: Hash,
    pub steps: Vec<BitblastSemanticStep>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastEncodedProblem {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub operation_profile: BitblastOperationProfile,
    pub backend_profile: BitblastBackendProfile,
    pub input_nodes: u64,
    pub encoded_nodes: u64,
    pub variables: Vec<BitblastVariable>,
    pub root: BitblastReflectedExpr,
    pub variable_map: Vec<BitblastVariableMapEntry>,
    pub circuit_nodes: Vec<BitblastCircuitNode>,
    pub semantic_plan: BitblastSemanticPlan,
    pub cnf_artifact: BitblastCnfArtifact,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastReconstructionStep {
    pub ordinal: u64,
    pub kind: BitblastReconstructionStepKind,
    pub input_hash: Hash,
    pub output_hash: Hash,
    pub checked_rule_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastSemanticProofArtifact {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub encoded_problem_hash: Hash,
    pub root_reflected_expr_hash: Hash,
    pub variable_map_hash: Hash,
    pub circuit_hash: Hash,
    pub semantic_plan_hash: Hash,
    pub cnf_artifact_hash: Hash,
    pub final_goal_hash: Hash,
    pub steps: Vec<BitblastReconstructionStep>,
    pub proof_identity: SolverCheckedProofTermIdentity,
    pub generated_term_nodes: u64,
    pub proof_bytes: u64,
    pub proof_steps: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastSatHandoff {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub policy_hash: Hash,
    pub encoded_problem_hash: Hash,
    pub root_reflected_expr_hash: Hash,
    pub variable_map_hash: Hash,
    pub cnf_artifact_hash: Hash,
    pub canonical_cnf_hash: Hash,
    pub canonical_cnf_bytes: Vec<u8>,
    pub cnf_variable_count: u64,
    pub cnf_clause_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastSatModelAssignment {
    pub cnf_variable: u64,
    pub value: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastSatModelArtifact {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub encoded_problem_hash: Hash,
    pub cnf_artifact_hash: Hash,
    pub variable_map_hash: Hash,
    pub assignments: Vec<BitblastSatModelAssignment>,
    pub output_literal_value: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LratLiteral {
    pub variable: u64,
    pub positive: bool,
}

impl LratLiteral {
    pub const fn negated(self) -> Self {
        Self {
            variable: self.variable,
            positive: !self.positive,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratClause {
    pub line_id: u64,
    pub literals: Vec<LratLiteral>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratCnf {
    pub version: SolverContractVersion,
    pub variable_count: u64,
    pub clauses: Vec<LratClause>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratRatCheck {
    pub clause_id: u64,
    pub rup_hints: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LratProofRule {
    Rup {
        hints: Vec<u64>,
    },
    Rat {
        pivot: Option<LratLiteral>,
        checks: Vec<LratRatCheck>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LratProofLineKind {
    Add {
        clause: LratClause,
        rule: LratProofRule,
    },
    Delete {
        clause_ids: Vec<u64>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratProofLine {
    pub ordinal: u64,
    pub kind: LratProofLineKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratCertificate {
    pub version: SolverContractVersion,
    pub cnf_hash: Hash,
    pub proof_lines: Vec<LratProofLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratCheckArtifact {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub policy_hash: Hash,
    pub cnf_hash: Hash,
    pub certificate_hash: Hash,
    pub proof_payload_ref_hash: Hash,
    pub empty_clause_line_id: u64,
    pub original_clause_count: u64,
    pub proof_line_count: u64,
    pub rup_step_count: u64,
    pub rat_step_count: u64,
    pub deletion_step_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LratCnfUnsatBridgeArtifact {
    pub version: SolverContractVersion,
    pub lrat_request_hash: Hash,
    pub lrat_policy_hash: Hash,
    pub cnf_hash: Hash,
    pub certificate_hash: Hash,
    pub payload_hash: Hash,
    pub proof_payload_ref_hash: Hash,
    pub lrat_check_artifact_hash: Hash,
    pub empty_clause_line_id: u64,
    pub cnf_unsat_theorem_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitblastLratSoundnessBridgeArtifact {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub policy_hash: Hash,
    pub lrat_request_hash: Hash,
    pub lrat_policy_hash: Hash,
    pub solver_profile: SolverProfile,
    pub certificate_format: SolverCertificateFormat,
    pub encoded_problem_hash: Hash,
    pub root_reflected_expr_hash: Hash,
    pub variable_map_hash: Hash,
    pub cnf_artifact_hash: Hash,
    pub canonical_cnf_hash: Hash,
    pub lrat_cnf_hash: Hash,
    pub lrat_certificate_hash: Hash,
    pub lrat_payload_hash: Hash,
    pub lrat_proof_payload_ref_hash: Hash,
    pub lrat_check_artifact_hash: Hash,
    pub lrat_cnf_unsat_bridge_hash: Hash,
    pub cnf_unsat_theorem_hash: Hash,
    pub semantic_proof_artifact_hash: Hash,
    pub final_goal_hash: Hash,
}

#[derive(Clone, Copy, Debug)]
pub struct BitblastLratSoundnessBridgeInput<'a> {
    pub request: &'a SolverRequest,
    pub policy: &'a SolverResourcePolicy,
    pub lrat_request: &'a SolverRequest,
    pub lrat_policy: &'a SolverResourcePolicy,
    pub problem: &'a BitblastEncodedProblem,
    pub semantic_proof: &'a BitblastSemanticProofArtifact,
    pub lrat_cnf: &'a LratCnf,
    pub lrat_certificate: &'a LratCertificate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LratCheckError {
    MissingEvidence {
        field: &'static str,
    },
    CnfHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    NonCanonicalClauseId {
        expected: u64,
        actual: u64,
    },
    NonCanonicalProofLine {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    NonCanonicalLiteralOrder {
        line_id: u64,
    },
    DuplicateLiteral {
        line_id: u64,
        literal: LratLiteral,
    },
    TautologicalClause {
        line_id: u64,
        variable: u64,
    },
    LiteralVariableOutOfRange {
        line_id: u64,
        variable: u64,
        max_variable: u64,
    },
    EmptyInitialClause {
        line_id: u64,
    },
    ProofLineIdNotIncreasing {
        line_id: u64,
        previous_max: u64,
    },
    HintOutOfBounds {
        line_id: u64,
        hint_id: u64,
    },
    ClauseNotActive {
        line_id: u64,
        referenced_id: u64,
    },
    BadRupHint {
        line_id: u64,
        hint_id: u64,
    },
    RupDidNotDeriveConflict {
        line_id: u64,
    },
    MissingRatPivot {
        line_id: u64,
    },
    RatPivotNotInClause {
        line_id: u64,
        pivot: LratLiteral,
    },
    RatMissingResolvent {
        line_id: u64,
        clause_id: u64,
    },
    RatUnexpectedResolvent {
        line_id: u64,
        clause_id: u64,
    },
    InvalidDeletion {
        ordinal: u64,
        clause_id: u64,
    },
    NoEmptyClause,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverResponseStatus {
    Proposed,
    Unsupported,
    Counterexample,
    Certificate,
}

impl SolverResponseStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Proposed => "Proposed",
            Self::Unsupported => "Unsupported",
            Self::Counterexample => "Counterexample",
            Self::Certificate => "Certificate",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Proposed => 0,
            Self::Unsupported => 1,
            Self::Counterexample => 2,
            Self::Certificate => 3,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolverGoalIdentity {
    pub goal_hash: Hash,
    pub target_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverRequest {
    pub version: SolverContractVersion,
    pub family: SolverFamily,
    pub fragment: SolverFragment,
    pub profile: SolverProfile,
    pub goal_identity: SolverGoalIdentity,
    pub local_context_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverResourcePolicy {
    pub version: SolverContractVersion,
    pub profile: SolverResourcePolicyProfile,
    pub family: SolverFamily,
    pub max_input_nodes: u64,
    pub max_input_bytes: u64,
    pub max_generated_term_nodes: u64,
    pub max_proof_bytes: u64,
    pub max_certificate_bytes: u64,
    pub max_cnf_variables: u64,
    pub max_cnf_clauses: u64,
    pub max_solver_steps: u64,
    pub max_proof_steps: u64,
    pub max_rule_count: u64,
    pub max_memory_bytes: u64,
    pub max_cpu_millis: u64,
    /// Operational wall-clock limit. Measured wall-clock time is never proof evidence.
    pub max_wall_clock_millis: u64,
    /// Maximum stdout/stderr or sidecar output bytes accepted from an untrusted solver.
    pub max_output_bytes: u64,
    /// Maximum nested solver calls allowed while executing this solver attempt.
    pub max_nested_solver_calls: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverResourcePolicyRef {
    pub profile: SolverResourcePolicyProfile,
    pub policy_hash: Hash,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SolverResourceUsage {
    pub input_nodes: u64,
    pub input_bytes: u64,
    pub generated_term_nodes: u64,
    pub proof_bytes: u64,
    pub certificate_bytes: u64,
    pub cnf_variables: u64,
    pub cnf_clauses: u64,
    pub solver_steps: u64,
    pub proof_steps: u64,
    pub rule_count: u64,
    pub memory_bytes: u64,
    pub cpu_millis: u64,
    pub wall_clock_millis: u64,
    pub output_bytes: u64,
    pub nested_solver_calls: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolverResourceField {
    InputNodes,
    InputBytes,
    GeneratedTermNodes,
    ProofBytes,
    CertificateBytes,
    CnfVariables,
    CnfClauses,
    SolverSteps,
    ProofSteps,
    RuleCount,
    MemoryBytes,
    CpuMillis,
    WallClockMillis,
    OutputBytes,
    NestedSolverCalls,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverReplayMetadata {
    pub version: SolverContractVersion,
    pub request_hash: Hash,
    pub response_identity_hash: Hash,
    pub resource_policy_profile: SolverResourcePolicyProfile,
    pub resource_policy_hash: Hash,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverProofPayloadRef {
    pub certificate_format: SolverCertificateFormat,
    pub payload_hash: Hash,
    pub size_bytes: u64,
    pub canonical_bytes: Option<Vec<u8>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverReconstructionPlanRef {
    pub profile: SolverProfile,
    pub reconstruction_plan_hash: Hash,
    pub imported_theory_count: u64,
    pub step_count: u64,
    pub step_ids: Vec<String>,
    pub final_step_id: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverCertificateMetadata {
    pub family: SolverFamily,
    pub fragment: SolverFragment,
    pub profile: SolverProfile,
    pub certificate_format: SolverCertificateFormat,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub payload_hash: Hash,
    pub proof_payload_ref_hash: Hash,
    pub reconstruction_plan_hash: Hash,
}

impl SolverCertificateMetadata {
    pub fn from_advanced_smt_metadata(
        metadata: &AdvancedSmtCertificateMetadata,
        environment_hash: Hash,
        policy_hash: Hash,
    ) -> Result<Self, SolverContractError> {
        let certificate_format = SolverCertificateFormat::from_advanced_smt(metadata.format);
        let payload_ref = SolverProofPayloadRef {
            certificate_format,
            payload_hash: metadata.proof_hash,
            size_bytes: 0,
            canonical_bytes: None,
        };
        let solver_metadata = Self {
            family: SolverFamily::Smt,
            fragment: SolverFragment::from_advanced_smt_logic(metadata.logic),
            profile: SolverProfile::AdvancedSmtMvpV1,
            certificate_format,
            environment_hash,
            policy_hash,
            payload_hash: metadata.proof_hash,
            proof_payload_ref_hash: solver_proof_payload_ref_hash(&payload_ref)?,
            reconstruction_plan_hash: metadata.reconstruction.reconstruction_plan_hash,
        };
        validate_solver_certificate_metadata(&solver_metadata)?;
        Ok(solver_metadata)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverCheckedProofTermIdentity {
    pub environment_hash: Hash,
    pub proof_term_hash: Hash,
    pub proof_type_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverAcceptingPayload {
    CheckedProofTerm(SolverCheckedProofTermIdentity),
    CheckedCertificateReconstruction(SolverCertificateMetadata),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverResponsePayload {
    Proposed {
        proposal_hash: Option<Hash>,
        reconstruction_plan: Option<SolverReconstructionPlanRef>,
    },
    Unsupported {
        reason_code: Option<String>,
    },
    Counterexample {
        counterexample_hash: Hash,
    },
    Certificate(SolverAcceptingPayload),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SolverResponseAdvisory {
    pub display_text: Option<String>,
    pub diagnostic_prose: Option<String>,
    pub raw_solver_stdout: Option<String>,
    pub raw_solver_stderr: Option<String>,
    pub measured_wall_clock_ms: Option<u64>,
    pub ranking_score: Option<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverResponseMetadata {
    pub request_hash: Hash,
    pub family: SolverFamily,
    pub fragment: SolverFragment,
    pub profile: SolverProfile,
    pub environment_hash: Hash,
    pub policy_hash: Hash,
    pub payload_hash: Option<Hash>,
    pub proof_payload_ref_hash: Option<Hash>,
    pub certificate_format: Option<SolverCertificateFormat>,
    pub certificate_metadata_hash: Option<Hash>,
    pub reconstruction_plan_hash: Option<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverResponse {
    pub version: SolverContractVersion,
    pub status: SolverResponseStatus,
    pub metadata: SolverResponseMetadata,
    pub payload: SolverResponsePayload,
    pub advisory: SolverResponseAdvisory,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverContractError {
    DuplicateIdentifier {
        field: &'static str,
        identifier: String,
    },
    UnknownProfileTag {
        field: &'static str,
        tag: String,
    },
    MismatchedHash {
        field: &'static str,
        expected: Hash,
        actual: Hash,
    },
    MissingEnvironmentHash,
    MissingPolicyHash,
    MissingGoalIdentity,
    MissingLocalContextIdentity,
    MissingPayloadHash,
    MissingReconstructionPlanHash,
    NonCanonicalPayloadBytes {
        field: &'static str,
    },
    ResponseStatusPayloadMismatch {
        status: SolverResponseStatus,
        payload: &'static str,
    },
    NonAcceptingStatusCannotVerify {
        status: SolverResponseStatus,
    },
    RequestResponseHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    RequestMetadataMismatch {
        field: &'static str,
    },
    UnsupportedFragment {
        family: SolverFamily,
        fragment: SolverFragment,
    },
    ProofSearchExhausted {
        field: SolverResourceField,
        limit: u64,
        actual: u64,
    },
    CertificateTooLarge {
        limit_bytes: u64,
        actual_bytes: u64,
    },
    ReconstructionTermTooLarge {
        limit_nodes: u64,
        actual_nodes: u64,
    },
    Timeout {
        field: SolverResourceField,
        limit_millis: u64,
        actual_millis: u64,
    },
    MemoryLimit {
        limit_bytes: u64,
        actual_bytes: u64,
    },
    OutputLimit {
        limit_bytes: u64,
        actual_bytes: u64,
    },
    ResourceLimitExceeded {
        field: SolverResourceField,
        limit: u64,
        actual: u64,
    },
    FiniteCarrierCardinalityMismatch {
        expected_cardinality: u64,
        actual_cardinality: u64,
    },
    DuplicateFiniteEnumerationElement {
        ordinal: u64,
        element_hash: Hash,
    },
    MissingFiniteEnumerationElement {
        expected_cardinality: u64,
        actual_cardinality: u64,
    },
    NonCanonicalFiniteEnumerationOrder {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    MissingFiniteEvidence {
        field: &'static str,
    },
    CounterexampleWitnessNotInEnumeration {
        ordinal: u64,
    },
    FalseFiniteDecisionCannotProduceProof {
        goal_kind: FiniteDecideGoalKind,
        witness_ordinal: Option<u64>,
    },
    UnsupportedOmegaFragment {
        reason: &'static str,
    },
    UnsupportedOmegaOperator {
        operator: String,
    },
    NonlinearOmegaTerm {
        operator: String,
    },
    MissingOmegaSideCondition {
        variable_ordinal: u64,
    },
    MissingOmegaSideConditionDischarge {
        variable_ordinal: u64,
    },
    NonCanonicalOmegaVariableOrder {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    OmegaBoundedExpansionOverBudget {
        limit_cases: u64,
        actual_cases: u64,
    },
    MissingOmegaCertificateStep {
        step_id: String,
    },
    UnsupportedRingNfFragment {
        reason: &'static str,
    },
    UnsupportedRingNfOperation {
        profile: RingNfAlgebraProfile,
        operator: String,
    },
    NonCommutativeRingNfTerm {
        operator: String,
    },
    NonCanonicalRingNfVariableOrder {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    RingNfCoefficientOverflow,
    RingNfMonomialOverBudget {
        limit: u64,
        actual: u64,
    },
    RingNfDegreeOverBudget {
        limit: u64,
        actual: u64,
    },
    MissingRingNfEvidence {
        field: &'static str,
    },
    RingNfNormalFormsMismatch,
    MissingRingNfVariableEnvironmentEntry {
        expected_count: u64,
        actual_count: u64,
    },
    NonCanonicalRingNfVariableEnvironment {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    DuplicateRingNfAlgebraLaw {
        law: RingNfAlgebraLawKind,
    },
    MissingRingNfAlgebraLaw {
        law: RingNfAlgebraLawKind,
    },
    MismatchedRingNfAlgebraLawProfile {
        law: RingNfAlgebraLawKind,
        expected: RingNfAlgebraProfile,
        actual: RingNfAlgebraProfile,
    },
    UnsupportedBitblastFragment {
        reason: &'static str,
    },
    UnsupportedBitblastOperator {
        operator: String,
    },
    BitblastWidthMismatch {
        expected_width: u64,
        actual_width: u64,
    },
    NonCanonicalBitblastVariableOrder {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    MissingBitblastEvidence {
        field: &'static str,
    },
    NonCanonicalBitblastVariableMap {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    NonCanonicalBitblastCircuitNode {
        expected_node_id: u64,
        actual_node_id: u64,
    },
    NonCanonicalBitblastClause {
        expected_ordinal: u64,
        actual_ordinal: u64,
    },
    LratCheckFailed {
        error: LratCheckError,
    },
}

pub fn validate_solver_request(request: &SolverRequest) -> Result<(), SolverContractError> {
    if is_zero_hash(&request.goal_identity.goal_hash)
        || is_zero_hash(&request.goal_identity.target_hash)
    {
        return Err(SolverContractError::MissingGoalIdentity);
    }
    if is_zero_hash(&request.local_context_hash) {
        return Err(SolverContractError::MissingLocalContextIdentity);
    }
    validate_environment_and_policy_hashes(request.environment_hash, request.policy_hash)
}

pub fn solver_request_canonical_bytes(
    request: &SolverRequest,
) -> Result<Vec<u8>, SolverContractError> {
    validate_solver_request(request)?;
    let mut out = vec![
        request.version.tag(),
        request.family.tag(),
        request.fragment.tag(),
        request.profile.tag(),
    ];
    encode_hash_to(&mut out, &request.goal_identity.goal_hash);
    encode_hash_to(&mut out, &request.goal_identity.target_hash);
    encode_hash_to(&mut out, &request.local_context_hash);
    encode_hash_to(&mut out, &request.environment_hash);
    encode_hash_to(&mut out, &request.policy_hash);
    Ok(out)
}

pub fn solver_request_hash(request: &SolverRequest) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_REQUEST_HASH_TAG,
        &solver_request_canonical_bytes(request)?,
    ))
}

pub fn solver_inline_payload_hash(
    certificate_format: SolverCertificateFormat,
    canonical_bytes: &[u8],
) -> Result<Hash, SolverContractError> {
    validate_canonical_payload_bytes(certificate_format, canonical_bytes)?;
    let mut out = Vec::new();
    out.push(certificate_format.tag());
    encode_bytes_to(&mut out, canonical_bytes);
    Ok(hash_with_domain(SOLVER_INLINE_PAYLOAD_HASH_TAG, &out))
}

pub fn validate_lrat_cnf(cnf: &LratCnf) -> Result<(), SolverContractError> {
    if cnf.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "lrat_cnf_version",
            tag: cnf.version.as_str().to_owned(),
        });
    }
    if cnf.variable_count == 0 {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_variable_count",
        }));
    }
    if cnf.clauses.is_empty() {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_cnf_clauses",
        }));
    }
    for (index, clause) in cnf.clauses.iter().enumerate() {
        let expected = index as u64 + 1;
        if clause.line_id != expected {
            return Err(lrat_error(LratCheckError::NonCanonicalClauseId {
                expected,
                actual: clause.line_id,
            }));
        }
        validate_lrat_clause_shape(clause, cnf.variable_count, false)?;
    }
    Ok(())
}

pub fn lrat_cnf_canonical_bytes(cnf: &LratCnf) -> Result<Vec<u8>, SolverContractError> {
    validate_lrat_cnf(cnf)?;
    let mut out = Vec::new();
    out.push(cnf.version.tag());
    encode_u64_to(&mut out, cnf.variable_count);
    encode_len_to(&mut out, cnf.clauses.len());
    for clause in &cnf.clauses {
        encode_lrat_clause_to(&mut out, clause);
    }
    Ok(out)
}

pub fn lrat_cnf_hash(cnf: &LratCnf) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        LRAT_CNF_HASH_TAG,
        &lrat_cnf_canonical_bytes(cnf)?,
    ))
}

pub fn validate_lrat_certificate_shape(
    certificate: &LratCertificate,
) -> Result<(), SolverContractError> {
    if certificate.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "lrat_certificate_version",
            tag: certificate.version.as_str().to_owned(),
        });
    }
    if is_zero_hash(&certificate.cnf_hash) {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_certificate_cnf_hash",
        }));
    }
    if certificate.proof_lines.is_empty() {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_proof_lines",
        }));
    }
    for (index, line) in certificate.proof_lines.iter().enumerate() {
        let expected = index as u64;
        if line.ordinal != expected {
            return Err(lrat_error(LratCheckError::NonCanonicalProofLine {
                expected_ordinal: expected,
                actual_ordinal: line.ordinal,
            }));
        }
        validate_lrat_proof_line_shape(line)?;
    }
    Ok(())
}

pub fn lrat_certificate_canonical_bytes(
    certificate: &LratCertificate,
) -> Result<Vec<u8>, SolverContractError> {
    validate_lrat_certificate_shape(certificate)?;
    let mut out = Vec::new();
    out.push(certificate.version.tag());
    encode_hash_to(&mut out, &certificate.cnf_hash);
    encode_len_to(&mut out, certificate.proof_lines.len());
    for line in &certificate.proof_lines {
        encode_lrat_proof_line_to(&mut out, line);
    }
    Ok(out)
}

pub fn lrat_certificate_hash(certificate: &LratCertificate) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        LRAT_CERTIFICATE_HASH_TAG,
        &lrat_certificate_canonical_bytes(certificate)?,
    ))
}

pub fn lrat_proof_payload_ref(
    certificate: &LratCertificate,
) -> Result<SolverProofPayloadRef, SolverContractError> {
    let canonical_bytes = lrat_certificate_canonical_bytes(certificate)?;
    Ok(SolverProofPayloadRef {
        certificate_format: SolverCertificateFormat::LratV1,
        payload_hash: solver_inline_payload_hash(
            SolverCertificateFormat::LratV1,
            &canonical_bytes,
        )?,
        size_bytes: canonical_bytes.len() as u64,
        canonical_bytes: Some(canonical_bytes),
    })
}

pub fn validate_lrat_proof_payload_ref(
    payload: &SolverProofPayloadRef,
) -> Result<(), SolverContractError> {
    if payload.certificate_format != SolverCertificateFormat::LratV1 {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        });
    }
    validate_solver_proof_payload_ref(payload)?;
    let Some(canonical_bytes) = payload.canonical_bytes.as_deref() else {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_payload_canonical_bytes",
        }));
    };
    if matches!(
        canonical_bytes,
        b"unsat\n" | b"UNSAT\n" | b"sat\n" | b"SAT\n"
    ) {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "lrat_payload_canonical_bytes",
        });
    }
    Ok(())
}

pub fn lrat_resource_usage_from_certificate(
    cnf: &LratCnf,
    certificate: &LratCertificate,
) -> Result<SolverResourceUsage, SolverContractError> {
    let cnf_bytes = lrat_cnf_canonical_bytes(cnf)?;
    let certificate_bytes = lrat_certificate_canonical_bytes(certificate)?;
    let cnf_literal_count = lrat_cnf_literal_count(cnf);
    let proof_literal_count = lrat_certificate_literal_count(certificate);
    let hint_count = lrat_certificate_hint_count(certificate);
    let proof_lines = certificate.proof_lines.len() as u64;
    let memory_bytes = lrat_memory_estimate_bytes(cnf, certificate);
    Ok(SolverResourceUsage {
        input_nodes: cnf_literal_count.saturating_add(proof_literal_count),
        input_bytes: (cnf_bytes.len() as u64).saturating_add(certificate_bytes.len() as u64),
        certificate_bytes: certificate_bytes.len() as u64,
        cnf_variables: cnf.variable_count,
        cnf_clauses: cnf.clauses.len() as u64,
        solver_steps: proof_lines.saturating_add(hint_count),
        proof_steps: proof_lines,
        rule_count: hint_count,
        memory_bytes,
        output_bytes: certificate_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn lrat_check_artifact_canonical_bytes(
    artifact: &LratCheckArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_lrat_check_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.request_hash);
    encode_hash_to(&mut out, &artifact.policy_hash);
    encode_hash_to(&mut out, &artifact.cnf_hash);
    encode_hash_to(&mut out, &artifact.certificate_hash);
    encode_hash_to(&mut out, &artifact.proof_payload_ref_hash);
    encode_u64_to(&mut out, artifact.empty_clause_line_id);
    encode_u64_to(&mut out, artifact.original_clause_count);
    encode_u64_to(&mut out, artifact.proof_line_count);
    encode_u64_to(&mut out, artifact.rup_step_count);
    encode_u64_to(&mut out, artifact.rat_step_count);
    encode_u64_to(&mut out, artifact.deletion_step_count);
    Ok(out)
}

pub fn lrat_check_artifact_hash(artifact: &LratCheckArtifact) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        LRAT_CHECK_ARTIFACT_HASH_TAG,
        &lrat_check_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn lrat_check_certificate(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    cnf: &LratCnf,
    certificate: &LratCertificate,
) -> Result<LratCheckArtifact, SolverContractError> {
    validate_lrat_solver_request(request)?;
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_lrat_cnf(cnf)?;
    validate_lrat_certificate_shape(certificate)?;
    let expected_cnf_hash = lrat_cnf_hash(cnf)?;
    if certificate.cnf_hash != expected_cnf_hash {
        return Err(lrat_error(LratCheckError::CnfHashMismatch {
            expected: expected_cnf_hash,
            actual: certificate.cnf_hash,
        }));
    }
    enforce_solver_resource_usage(
        policy,
        lrat_resource_usage_from_certificate(cnf, certificate)?,
    )?;
    let check = run_lrat_checker(cnf, certificate)?;
    let payload_ref = lrat_proof_payload_ref(certificate)?;
    validate_lrat_proof_payload_ref(&payload_ref)?;
    let artifact = LratCheckArtifact {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        policy_hash: solver_resource_policy_hash(policy)?,
        cnf_hash: expected_cnf_hash,
        certificate_hash: lrat_certificate_hash(certificate)?,
        proof_payload_ref_hash: solver_proof_payload_ref_hash(&payload_ref)?,
        empty_clause_line_id: check.empty_clause_line_id,
        original_clause_count: cnf.clauses.len() as u64,
        proof_line_count: certificate.proof_lines.len() as u64,
        rup_step_count: check.rup_step_count,
        rat_step_count: check.rat_step_count,
        deletion_step_count: check.deletion_step_count,
    };
    validate_lrat_check_artifact_shape(&artifact)?;
    Ok(artifact)
}

pub fn lrat_cnf_unsat_theorem_hash(
    cnf_hash: Hash,
    lrat_check_artifact_hash: Hash,
    empty_clause_line_id: u64,
) -> Result<Hash, SolverContractError> {
    if is_zero_hash(&cnf_hash) {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_cnf_hash",
        }));
    }
    if is_zero_hash(&lrat_check_artifact_hash) {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_check_artifact_hash",
        }));
    }
    if empty_clause_line_id == 0 {
        return Err(lrat_error(LratCheckError::NoEmptyClause));
    }
    let mut out = Vec::new();
    encode_hash_to(&mut out, &cnf_hash);
    encode_hash_to(&mut out, &lrat_check_artifact_hash);
    encode_u64_to(&mut out, empty_clause_line_id);
    Ok(hash_with_domain(LRAT_CNF_UNSAT_THEOREM_HASH_TAG, &out))
}

pub fn lrat_cnf_unsat_bridge_artifact(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    cnf: &LratCnf,
    certificate: &LratCertificate,
) -> Result<LratCnfUnsatBridgeArtifact, SolverContractError> {
    let check_artifact = lrat_check_certificate(request, policy, cnf, certificate)?;
    let payload_ref = lrat_proof_payload_ref(certificate)?;
    let lrat_check_artifact_hash = lrat_check_artifact_hash(&check_artifact)?;
    let artifact = LratCnfUnsatBridgeArtifact {
        version: SolverContractVersion::V1,
        lrat_request_hash: solver_request_hash(request)?,
        lrat_policy_hash: solver_resource_policy_hash(policy)?,
        cnf_hash: lrat_cnf_hash(cnf)?,
        certificate_hash: lrat_certificate_hash(certificate)?,
        payload_hash: payload_ref.payload_hash,
        proof_payload_ref_hash: solver_proof_payload_ref_hash(&payload_ref)?,
        lrat_check_artifact_hash,
        empty_clause_line_id: check_artifact.empty_clause_line_id,
        cnf_unsat_theorem_hash: lrat_cnf_unsat_theorem_hash(
            check_artifact.cnf_hash,
            lrat_check_artifact_hash,
            check_artifact.empty_clause_line_id,
        )?,
    };
    validate_lrat_cnf_unsat_bridge_artifact(request, policy, cnf, certificate, &artifact)?;
    Ok(artifact)
}

pub fn lrat_cnf_unsat_bridge_canonical_bytes(
    artifact: &LratCnfUnsatBridgeArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_lrat_cnf_unsat_bridge_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.lrat_request_hash);
    encode_hash_to(&mut out, &artifact.lrat_policy_hash);
    encode_hash_to(&mut out, &artifact.cnf_hash);
    encode_hash_to(&mut out, &artifact.certificate_hash);
    encode_hash_to(&mut out, &artifact.payload_hash);
    encode_hash_to(&mut out, &artifact.proof_payload_ref_hash);
    encode_hash_to(&mut out, &artifact.lrat_check_artifact_hash);
    encode_u64_to(&mut out, artifact.empty_clause_line_id);
    encode_hash_to(&mut out, &artifact.cnf_unsat_theorem_hash);
    Ok(out)
}

pub fn lrat_cnf_unsat_bridge_hash(
    artifact: &LratCnfUnsatBridgeArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        LRAT_CNF_UNSAT_BRIDGE_HASH_TAG,
        &lrat_cnf_unsat_bridge_canonical_bytes(artifact)?,
    ))
}

pub fn validate_lrat_cnf_unsat_bridge_artifact(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    cnf: &LratCnf,
    certificate: &LratCertificate,
    artifact: &LratCnfUnsatBridgeArtifact,
) -> Result<(), SolverContractError> {
    validate_lrat_cnf_unsat_bridge_artifact_shape(artifact)?;
    let check_artifact = lrat_check_certificate(request, policy, cnf, certificate)?;
    let check_artifact_hash = lrat_check_artifact_hash(&check_artifact)?;
    let payload_ref = lrat_proof_payload_ref(certificate)?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_request_hash",
        artifact.lrat_request_hash,
        solver_request_hash(request)?,
    )?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_policy_hash",
        artifact.lrat_policy_hash,
        solver_resource_policy_hash(policy)?,
    )?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_cnf_hash",
        artifact.cnf_hash,
        check_artifact.cnf_hash,
    )?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_certificate_hash",
        artifact.certificate_hash,
        check_artifact.certificate_hash,
    )?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_payload_hash",
        artifact.payload_hash,
        payload_ref.payload_hash,
    )?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_payload_ref_hash",
        artifact.proof_payload_ref_hash,
        check_artifact.proof_payload_ref_hash,
    )?;
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_check_artifact_hash",
        artifact.lrat_check_artifact_hash,
        check_artifact_hash,
    )?;
    if artifact.empty_clause_line_id != check_artifact.empty_clause_line_id {
        return Err(lrat_error(LratCheckError::NoEmptyClause));
    }
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_theorem_hash",
        artifact.cnf_unsat_theorem_hash,
        lrat_cnf_unsat_theorem_hash(
            check_artifact.cnf_hash,
            check_artifact_hash,
            check_artifact.empty_clause_line_id,
        )?,
    )
}

pub fn finite_decide_carrier_canonical_bytes(
    carrier: &FiniteDecideCarrierRef,
) -> Result<Vec<u8>, SolverContractError> {
    validate_finite_decide_carrier_ref(carrier)?;
    let mut out = Vec::new();
    out.push(carrier.version.tag());
    out.push(carrier.kind.tag());
    encode_option_small_carrier_kind(&mut out, carrier.small_kind);
    encode_hash_to(&mut out, &carrier.carrier_type_hash);
    encode_string_list_to(&mut out, &carrier.universe_params);
    encode_u64_to(&mut out, carrier.cardinality);
    encode_option_u64(&mut out, carrier.fin_bound);
    encode_option_u64(&mut out, carrier.vector_bool_length);
    encode_option_hash(&mut out, carrier.explicit_finite_evidence_hash.as_ref());
    encode_option_hash(&mut out, carrier.no_duplicate_evidence_hash.as_ref());
    encode_option_hash(&mut out, carrier.complete_evidence_hash.as_ref());
    Ok(out)
}

pub fn finite_decide_carrier_hash(
    carrier: &FiniteDecideCarrierRef,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        FINITE_DECIDE_CARRIER_HASH_TAG,
        &finite_decide_carrier_canonical_bytes(carrier)?,
    ))
}

pub fn finite_decide_enumeration_canonical_bytes(
    enumeration: &FiniteDecideEnumeration,
) -> Result<Vec<u8>, SolverContractError> {
    validate_finite_decide_enumeration(enumeration)?;
    let mut out = Vec::new();
    encode_hash_to(&mut out, &finite_decide_carrier_hash(&enumeration.carrier)?);
    encode_len_to(&mut out, enumeration.elements.len());
    for element in &enumeration.elements {
        encode_finite_decide_element_to(&mut out, element);
    }
    Ok(out)
}

pub fn finite_decide_enumeration_hash(
    enumeration: &FiniteDecideEnumeration,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        FINITE_DECIDE_ENUMERATION_HASH_TAG,
        &finite_decide_enumeration_canonical_bytes(enumeration)?,
    ))
}

pub fn finite_decide_predicate_ref_canonical_bytes(
    predicate: &FiniteDecidePredicateRef,
) -> Result<Vec<u8>, SolverContractError> {
    validate_finite_decide_predicate_ref(predicate)?;
    let mut out = Vec::new();
    encode_hash_to(&mut out, &predicate.predicate_hash);
    encode_hash_to(&mut out, &predicate.predicate_type_hash);
    encode_hash_to(&mut out, &predicate.reflected_decidable_hash);
    encode_hash_to(&mut out, &predicate.local_context_hash);
    encode_hash_to(&mut out, &predicate.environment_hash);
    encode_hash_to(&mut out, &predicate.policy_hash);
    encode_string_list_to(&mut out, &predicate.universe_params);
    Ok(out)
}

pub fn finite_decide_predicate_ref_hash(
    predicate: &FiniteDecidePredicateRef,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        FINITE_DECIDE_PREDICATE_REF_HASH_TAG,
        &finite_decide_predicate_ref_canonical_bytes(predicate)?,
    ))
}

pub fn finite_decide_reflection_contract_canonical_bytes(
    contract: &FiniteDecideReflectionContract,
) -> Result<Vec<u8>, SolverContractError> {
    validate_finite_decide_reflection_contract(contract)?;
    let mut out = Vec::new();
    out.push(contract.version.tag());
    encode_hash_to(&mut out, &solver_request_hash(&contract.request)?);
    encode_hash_to(
        &mut out,
        &finite_decide_enumeration_hash(&contract.enumeration)?,
    );
    encode_hash_to(
        &mut out,
        &finite_decide_predicate_ref_hash(&contract.predicate)?,
    );
    Ok(out)
}

pub fn finite_decide_reflection_contract_hash(
    contract: &FiniteDecideReflectionContract,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        FINITE_DECIDE_REFLECTION_CONTRACT_HASH_TAG,
        &finite_decide_reflection_contract_canonical_bytes(contract)?,
    ))
}

pub fn finite_decide_counterexample_canonical_bytes(
    counterexample: &FiniteDecideCounterexampleArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_finite_decide_counterexample_shape(counterexample)?;
    let mut out = Vec::new();
    out.push(counterexample.version.tag());
    encode_hash_to(&mut out, &counterexample.reflection_contract_hash);
    encode_hash_to(&mut out, &counterexample.enumeration_hash);
    encode_finite_decide_element_to(&mut out, &counterexample.element);
    encode_hash_to(&mut out, &counterexample.predicate_hash);
    encode_hash_to(&mut out, &counterexample.predicate_evidence_hash);
    Ok(out)
}

pub fn finite_decide_counterexample_hash(
    counterexample: &FiniteDecideCounterexampleArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        FINITE_DECIDE_COUNTEREXAMPLE_HASH_TAG,
        &finite_decide_counterexample_canonical_bytes(counterexample)?,
    ))
}

pub fn finite_decide_proof_artifact_canonical_bytes(
    artifact: &FiniteDecideProofArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_finite_decide_proof_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.reflection_contract_hash);
    encode_hash_to(&mut out, &artifact.enumeration_hash);
    encode_hash_to(&mut out, &artifact.predicate_hash);
    out.push(artifact.goal_kind.tag());
    out.push(u8::from(artifact.fold_result));
    encode_len_to(&mut out, artifact.element_decisions.len());
    for decision in &artifact.element_decisions {
        encode_finite_decide_element_to(&mut out, &decision.element);
        out.push(decision.value.tag());
        encode_hash_to(&mut out, &decision.predicate_evidence_hash);
        encode_option_hash(&mut out, decision.proof_term_hash.as_ref());
    }
    encode_hash_to(&mut out, &artifact.proof_identity.environment_hash);
    encode_hash_to(&mut out, &artifact.proof_identity.proof_term_hash);
    encode_hash_to(&mut out, &artifact.proof_identity.proof_type_hash);
    encode_u64_to(&mut out, artifact.generated_term_nodes);
    encode_u64_to(&mut out, artifact.proof_bytes);
    encode_u64_to(&mut out, artifact.proof_steps);
    Ok(out)
}

pub fn finite_decide_proof_artifact_hash(
    artifact: &FiniteDecideProofArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        FINITE_DECIDE_PROOF_ARTIFACT_HASH_TAG,
        &finite_decide_proof_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn finite_decide_counterexample_for_reflection(
    contract: &FiniteDecideReflectionContract,
    witness_ordinal: u64,
    predicate_evidence_hash: Hash,
) -> Result<FiniteDecideCounterexampleArtifact, SolverContractError> {
    validate_finite_decide_reflection_contract(contract)?;
    if is_zero_hash(&predicate_evidence_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "predicate_evidence_hash",
        });
    }
    let Some(element) = contract
        .enumeration
        .elements
        .iter()
        .find(|element| element.ordinal == witness_ordinal)
        .cloned()
    else {
        return Err(SolverContractError::CounterexampleWitnessNotInEnumeration {
            ordinal: witness_ordinal,
        });
    };
    let counterexample = FiniteDecideCounterexampleArtifact {
        version: SolverContractVersion::V1,
        reflection_contract_hash: finite_decide_reflection_contract_hash(contract)?,
        enumeration_hash: finite_decide_enumeration_hash(&contract.enumeration)?,
        element,
        predicate_hash: contract.predicate.predicate_hash,
        predicate_evidence_hash,
    };
    validate_finite_decide_counterexample_for_reflection(contract, &counterexample)?;
    Ok(counterexample)
}

pub fn finite_decide_counterexample_response(
    contract: &FiniteDecideReflectionContract,
    counterexample: &FiniteDecideCounterexampleArtifact,
) -> Result<SolverResponse, SolverContractError> {
    validate_finite_decide_counterexample_for_reflection(contract, counterexample)?;
    let counterexample_hash = finite_decide_counterexample_hash(counterexample)?;
    let response = SolverResponse {
        version: SolverContractVersion::V1,
        status: SolverResponseStatus::Counterexample,
        metadata: SolverResponseMetadata {
            request_hash: solver_request_hash(&contract.request)?,
            family: contract.request.family,
            fragment: contract.request.fragment,
            profile: contract.request.profile,
            environment_hash: contract.request.environment_hash,
            policy_hash: contract.request.policy_hash,
            payload_hash: Some(counterexample_hash),
            proof_payload_ref_hash: None,
            certificate_format: None,
            certificate_metadata_hash: None,
            reconstruction_plan_hash: None,
        },
        payload: SolverResponsePayload::Counterexample {
            counterexample_hash,
        },
        advisory: SolverResponseAdvisory::default(),
    };
    validate_solver_response_for_request(&contract.request, &response)?;
    Ok(response)
}

pub fn finite_decide_checked_proof_response(
    contract: &FiniteDecideReflectionContract,
    proof_artifact: &FiniteDecideProofArtifact,
    policy: &SolverResourcePolicy,
) -> Result<SolverResponse, SolverContractError> {
    validate_finite_decide_proof_artifact_for_reflection(contract, proof_artifact)?;
    validate_solver_resource_policy_for_request(policy, &contract.request)?;
    let response = SolverResponse {
        version: SolverContractVersion::V1,
        status: SolverResponseStatus::Certificate,
        metadata: SolverResponseMetadata {
            request_hash: solver_request_hash(&contract.request)?,
            family: contract.request.family,
            fragment: contract.request.fragment,
            profile: contract.request.profile,
            environment_hash: contract.request.environment_hash,
            policy_hash: contract.request.policy_hash,
            payload_hash: Some(proof_artifact.proof_identity.proof_term_hash),
            proof_payload_ref_hash: None,
            certificate_format: Some(SolverCertificateFormat::DirectNpaProofTermV1),
            certificate_metadata_hash: None,
            reconstruction_plan_hash: None,
        },
        payload: SolverResponsePayload::Certificate(SolverAcceptingPayload::CheckedProofTerm(
            proof_artifact.proof_identity.clone(),
        )),
        advisory: SolverResponseAdvisory {
            display_text: None,
            diagnostic_prose: None,
            raw_solver_stdout: None,
            raw_solver_stderr: None,
            measured_wall_clock_ms: None,
            ranking_score: None,
        },
    };
    validate_solver_response_for_request(&contract.request, &response)?;
    enforce_solver_generated_artifact_resource_policy(
        policy,
        &contract.request,
        &response,
        finite_decide_resource_usage_from_proof_artifact(proof_artifact)?,
    )?;
    Ok(response)
}

pub fn finite_decide_resource_usage_from_proof_artifact(
    artifact: &FiniteDecideProofArtifact,
) -> Result<SolverResourceUsage, SolverContractError> {
    let canonical_bytes = finite_decide_proof_artifact_canonical_bytes(artifact)?;
    Ok(SolverResourceUsage {
        input_nodes: artifact.element_decisions.len() as u64,
        input_bytes: canonical_bytes.len() as u64,
        generated_term_nodes: artifact.generated_term_nodes,
        proof_bytes: artifact.proof_bytes,
        solver_steps: artifact.element_decisions.len() as u64,
        proof_steps: artifact.proof_steps,
        rule_count: artifact.element_decisions.len() as u64,
        output_bytes: canonical_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn omega_normalization_options_from_policy(
    policy: &SolverResourcePolicy,
    request: &SolverRequest,
) -> Result<OmegaNormalizationOptions, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    Ok(OmegaNormalizationOptions {
        max_input_nodes: policy.max_input_nodes,
        max_variables: policy.max_rule_count,
        max_bounded_quantifier_cases: policy.max_solver_steps,
    })
}

pub fn omega_normalize_problem(
    request: &SolverRequest,
    local_context: &[OmegaLocalContextEntry],
    target: &Expr,
    options: &OmegaNormalizationOptions,
) -> Result<OmegaNormalizedProblem, SolverContractError> {
    validate_omega_solver_request(request)?;
    let input_nodes = omega_expr_node_count(target, options.max_input_nodes)?;
    let mut parser = OmegaParser {
        local_context,
        options,
        used_locals: BTreeSet::new(),
        bounded_expansions: Vec::new(),
    };
    let parsed = parser.parse_formula(target)?;
    let used_indices: Vec<usize> = parser.used_locals.iter().copied().collect();
    if used_indices.len() as u64 > options.max_variables {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::RuleCount,
            limit: options.max_variables,
            actual: used_indices.len() as u64,
        });
    }
    let mut local_to_ordinal = BTreeMap::new();
    let mut variables = Vec::with_capacity(used_indices.len());
    for (ordinal, local_index) in used_indices.iter().copied().enumerate() {
        let Some(entry) = local_context.get(local_index) else {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "de Bruijn index outside omega local context",
            });
        };
        let expected_sort = omega_type_expr_sort(&entry.ty)?;
        if expected_sort != entry.sort {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "omega local context sort does not match its core type",
            });
        }
        let source_core_expr = omega_bvar_for_local(local_context.len(), local_index)?;
        let ordinal_u64 = ordinal as u64;
        local_to_ordinal.insert(local_index, ordinal_u64);
        variables.push(OmegaVariable {
            ordinal: ordinal_u64,
            local_index: local_index as u64,
            name: entry.name.clone(),
            sort: entry.sort,
            source_core_expr_hash: core_expr_hash(&source_core_expr),
            type_hash: core_expr_hash(&entry.ty),
        });
    }
    let formula = omega_remap_formula(&parsed, &local_to_ordinal, variables.len())?;
    let nat_to_int_side_conditions =
        omega_nat_to_int_side_conditions(local_context.len(), &variables)?;
    let bounded_expansions = parser.bounded_expansions;
    let normalized_nodes = omega_formula_node_count(&formula)
        .saturating_add(variables.len() as u64)
        .saturating_add(nat_to_int_side_conditions.len() as u64)
        .saturating_add(
            bounded_expansions
                .iter()
                .map(|expansion| expansion.expanded_case_hashes.len() as u64 + 1)
                .sum::<u64>(),
        );
    let problem = OmegaNormalizedProblem {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        fragment_profile: if bounded_expansions.is_empty() {
            OmegaFragmentProfile::LinearArithmeticV1
        } else {
            OmegaFragmentProfile::BoundedQuantifierExpansionV1
        },
        input_nodes,
        normalized_nodes,
        variables,
        formula,
        nat_to_int_side_conditions,
        bounded_expansions,
    };
    validate_omega_normalized_problem(&problem)?;
    Ok(problem)
}

pub fn omega_normalized_problem_canonical_bytes(
    problem: &OmegaNormalizedProblem,
) -> Result<Vec<u8>, SolverContractError> {
    validate_omega_normalized_problem(problem)?;
    let mut out = Vec::new();
    out.push(problem.version.tag());
    out.push(problem.fragment_profile.tag());
    encode_hash_to(&mut out, &problem.request_hash);
    encode_u64_to(&mut out, problem.input_nodes);
    encode_u64_to(&mut out, problem.normalized_nodes);
    encode_len_to(&mut out, problem.variables.len());
    for variable in &problem.variables {
        encode_omega_variable_to(&mut out, variable);
    }
    encode_omega_formula_to(&mut out, &problem.formula);
    encode_len_to(&mut out, problem.nat_to_int_side_conditions.len());
    for side_condition in &problem.nat_to_int_side_conditions {
        encode_omega_nat_to_int_side_condition_to(&mut out, side_condition);
    }
    encode_len_to(&mut out, problem.bounded_expansions.len());
    for expansion in &problem.bounded_expansions {
        encode_omega_bounded_expansion_to(&mut out, expansion);
    }
    Ok(out)
}

pub fn omega_normalized_problem_hash(
    problem: &OmegaNormalizedProblem,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        OMEGA_NORMALIZED_PROBLEM_HASH_TAG,
        &omega_normalized_problem_canonical_bytes(problem)?,
    ))
}

pub fn omega_resource_usage_from_normalized_problem(
    problem: &OmegaNormalizedProblem,
) -> Result<SolverResourceUsage, SolverContractError> {
    let canonical_bytes = omega_normalized_problem_canonical_bytes(problem)?;
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: canonical_bytes.len() as u64,
        certificate_bytes: canonical_bytes.len() as u64,
        solver_steps: problem.normalized_nodes,
        rule_count: problem.variables.len() as u64
            + problem.nat_to_int_side_conditions.len() as u64
            + problem.bounded_expansions.len() as u64,
        output_bytes: canonical_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn ring_nf_normalization_options_from_policy(
    policy: &SolverResourcePolicy,
    request: &SolverRequest,
    algebra_profile: RingNfAlgebraProfile,
) -> Result<RingNfNormalizationOptions, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_ring_nf_solver_request(request)?;
    let max_coefficient_abs = i64::try_from(policy.max_output_bytes.min(i64::MAX as u64))
        .unwrap_or(i64::MAX)
        .max(1);
    Ok(RingNfNormalizationOptions {
        algebra_profile,
        max_input_nodes: policy.max_input_nodes,
        max_variables: policy.max_rule_count,
        max_monomials: policy.max_solver_steps.max(1),
        max_total_degree: policy.max_proof_steps.max(1),
        max_coefficient_abs,
    })
}

pub fn ring_nf_normalize_problem(
    request: &SolverRequest,
    local_context: &[RingNfLocalContextEntry],
    target: &Expr,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfNormalizedProblem, SolverContractError> {
    validate_ring_nf_solver_request(request)?;
    let input_nodes = ring_nf_expr_node_count(target, options.max_input_nodes)?;
    let (carrier_type, lhs, rhs) = ring_nf_parse_eq_target(target)?;
    let coefficient_domain =
        ring_nf_coefficient_domain_for_type(&carrier_type, options.algebra_profile)?;
    let carrier_type_hash = core_expr_hash(&carrier_type);
    let mut parser = RingNfParser {
        local_context,
        carrier_type_hash,
        coefficient_domain,
        options,
        used_locals: BTreeSet::new(),
    };
    let lhs_parsed = parser.parse_expr(&lhs)?;
    let rhs_parsed = parser.parse_expr(&rhs)?;
    let used_indices = parser.used_locals.iter().copied().collect::<Vec<_>>();
    if used_indices.len() as u64 > options.max_variables {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::RuleCount,
            limit: options.max_variables,
            actual: used_indices.len() as u64,
        });
    }

    let mut local_to_ordinal = BTreeMap::new();
    let mut variables = Vec::with_capacity(used_indices.len());
    for (ordinal, local_index) in used_indices.iter().copied().enumerate() {
        let Some(entry) = local_context.get(local_index) else {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "de Bruijn index outside ring_nf local context",
            });
        };
        if core_expr_hash(&entry.ty) != carrier_type_hash {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "ring_nf variable type does not match the equality carrier",
            });
        }
        let source_core_expr = ring_nf_bvar_for_local(local_context.len(), local_index)?;
        let ordinal_u64 = ordinal as u64;
        local_to_ordinal.insert(local_index, ordinal_u64);
        variables.push(RingNfVariable {
            ordinal: ordinal_u64,
            local_index: local_index as u64,
            name: entry.name.clone(),
            source_core_expr_hash: core_expr_hash(&source_core_expr),
            type_hash: core_expr_hash(&entry.ty),
        });
    }

    let lhs_reflected = ring_nf_remap_reflected(&lhs_parsed, &local_to_ordinal)?;
    let rhs_reflected = ring_nf_remap_reflected(&rhs_parsed, &local_to_ordinal)?;
    let variable_count = variables.len();
    let lhs_normal_form =
        ring_nf_polynomial_from_reflected(&lhs_reflected, options, variable_count)?;
    let rhs_normal_form =
        ring_nf_polynomial_from_reflected(&rhs_reflected, options, variable_count)?;
    let difference_normal_form = if options.algebra_profile.allows_signed_coefficients() {
        Some(ring_nf_polynomial_sub(
            &lhs_normal_form,
            &rhs_normal_form,
            options,
        )?)
    } else {
        None
    };
    let normal_forms_equal = lhs_normal_form == rhs_normal_form;
    let normalized_nodes = ring_nf_reflected_expr_node_count(&lhs_reflected)
        .saturating_add(ring_nf_reflected_expr_node_count(&rhs_reflected))
        .saturating_add(variables.len() as u64)
        .saturating_add(lhs_normal_form.monomials.len() as u64)
        .saturating_add(rhs_normal_form.monomials.len() as u64)
        .saturating_add(
            difference_normal_form
                .as_ref()
                .map(|poly| poly.monomials.len() as u64)
                .unwrap_or_default(),
        );
    let problem = RingNfNormalizedProblem {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        algebra_profile: options.algebra_profile,
        coefficient_domain,
        input_nodes,
        normalized_nodes,
        variables,
        equation: RingNfEquation {
            carrier_type_hash,
            lhs_reflected,
            rhs_reflected,
            lhs_normal_form,
            rhs_normal_form,
            difference_normal_form,
            normal_forms_equal,
        },
    };
    validate_ring_nf_normalized_problem(&problem)?;
    Ok(problem)
}

pub fn ring_nf_reflected_expr_canonical_bytes(
    expr: &RingNfReflectedExpr,
) -> Result<Vec<u8>, SolverContractError> {
    validate_ring_nf_reflected_expr_shape(expr, None)?;
    let mut out = Vec::new();
    encode_ring_nf_reflected_expr_to(&mut out, expr);
    Ok(out)
}

pub fn ring_nf_reflected_expr_hash(
    expr: &RingNfReflectedExpr,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        RING_NF_REFLECTED_EXPR_HASH_TAG,
        &ring_nf_reflected_expr_canonical_bytes(expr)?,
    ))
}

pub fn ring_nf_polynomial_canonical_bytes(
    polynomial: &RingNfPolynomial,
) -> Result<Vec<u8>, SolverContractError> {
    validate_ring_nf_polynomial_shape(polynomial, None, RingNfCoefficientDomain::Int)?;
    let mut out = Vec::new();
    encode_ring_nf_polynomial_to(&mut out, polynomial);
    Ok(out)
}

pub fn ring_nf_polynomial_hash(polynomial: &RingNfPolynomial) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        RING_NF_POLYNOMIAL_HASH_TAG,
        &ring_nf_polynomial_canonical_bytes(polynomial)?,
    ))
}

pub fn ring_nf_normalized_problem_canonical_bytes(
    problem: &RingNfNormalizedProblem,
) -> Result<Vec<u8>, SolverContractError> {
    validate_ring_nf_normalized_problem(problem)?;
    let mut out = Vec::new();
    out.push(problem.version.tag());
    out.push(problem.algebra_profile.tag());
    out.push(problem.coefficient_domain.tag());
    encode_hash_to(&mut out, &problem.request_hash);
    encode_u64_to(&mut out, problem.input_nodes);
    encode_u64_to(&mut out, problem.normalized_nodes);
    encode_len_to(&mut out, problem.variables.len());
    for variable in &problem.variables {
        encode_ring_nf_variable_to(&mut out, variable);
    }
    encode_ring_nf_equation_to(&mut out, &problem.equation);
    Ok(out)
}

pub fn ring_nf_normalized_problem_hash(
    problem: &RingNfNormalizedProblem,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        RING_NF_NORMALIZED_PROBLEM_HASH_TAG,
        &ring_nf_normalized_problem_canonical_bytes(problem)?,
    ))
}

pub fn ring_nf_profile_canonical_bytes(
    algebra_profile: RingNfAlgebraProfile,
    coefficient_domain: RingNfCoefficientDomain,
) -> Result<Vec<u8>, SolverContractError> {
    validate_ring_nf_profile_domain(algebra_profile, coefficient_domain)?;
    Ok(vec![algebra_profile.tag(), coefficient_domain.tag()])
}

pub fn ring_nf_profile_hash(
    algebra_profile: RingNfAlgebraProfile,
    coefficient_domain: RingNfCoefficientDomain,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        RING_NF_PROFILE_HASH_TAG,
        &ring_nf_profile_canonical_bytes(algebra_profile, coefficient_domain)?,
    ))
}

pub fn ring_nf_variable_environment_canonical_bytes(
    entries: &[RingNfVariableEnvironmentEntry],
) -> Result<Vec<u8>, SolverContractError> {
    validate_ring_nf_variable_environment_shape(entries)?;
    let mut out = Vec::new();
    encode_len_to(&mut out, entries.len());
    for entry in entries {
        encode_ring_nf_variable_environment_entry_to(&mut out, entry);
    }
    Ok(out)
}

pub fn ring_nf_variable_environment_hash(
    entries: &[RingNfVariableEnvironmentEntry],
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        RING_NF_VARIABLE_ENVIRONMENT_HASH_TAG,
        &ring_nf_variable_environment_canonical_bytes(entries)?,
    ))
}

pub fn ring_nf_proof_artifact_canonical_bytes(
    artifact: &RingNfProofArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_ring_nf_proof_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.request_hash);
    encode_hash_to(&mut out, &artifact.normalized_problem_hash);
    encode_hash_to(&mut out, &artifact.profile_hash);
    encode_hash_to(&mut out, &artifact.variable_environment_hash);
    encode_hash_to(&mut out, &artifact.policy_hash);
    encode_hash_to(&mut out, &artifact.lhs_reflected_expr_hash);
    encode_hash_to(&mut out, &artifact.rhs_reflected_expr_hash);
    encode_hash_to(&mut out, &artifact.lhs_normal_form_hash);
    encode_hash_to(&mut out, &artifact.rhs_normal_form_hash);
    encode_option_hash(&mut out, artifact.difference_normal_form_hash.as_ref());
    encode_len_to(&mut out, artifact.variable_environment.len());
    for entry in &artifact.variable_environment {
        encode_ring_nf_variable_environment_entry_to(&mut out, entry);
    }
    encode_len_to(&mut out, artifact.algebra_law_refs.len());
    for law_ref in &artifact.algebra_law_refs {
        encode_ring_nf_algebra_law_ref_to(&mut out, law_ref);
    }
    encode_hash_to(&mut out, &artifact.proof_identity.environment_hash);
    encode_hash_to(&mut out, &artifact.proof_identity.proof_term_hash);
    encode_hash_to(&mut out, &artifact.proof_identity.proof_type_hash);
    encode_u64_to(&mut out, artifact.generated_term_nodes);
    encode_u64_to(&mut out, artifact.proof_bytes);
    encode_u64_to(&mut out, artifact.proof_steps);
    Ok(out)
}

pub fn ring_nf_proof_artifact_hash(
    artifact: &RingNfProofArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        RING_NF_PROOF_ARTIFACT_HASH_TAG,
        &ring_nf_proof_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn ring_nf_resource_usage_from_normalized_problem(
    problem: &RingNfNormalizedProblem,
) -> Result<SolverResourceUsage, SolverContractError> {
    let canonical_bytes = ring_nf_normalized_problem_canonical_bytes(problem)?;
    let monomial_count = problem.equation.lhs_normal_form.monomials.len()
        + problem.equation.rhs_normal_form.monomials.len()
        + problem
            .equation
            .difference_normal_form
            .as_ref()
            .map(|poly| poly.monomials.len())
            .unwrap_or_default();
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: canonical_bytes.len() as u64,
        solver_steps: problem.normalized_nodes,
        rule_count: problem.variables.len() as u64 + monomial_count as u64,
        output_bytes: canonical_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn ring_nf_resource_usage_from_proof_artifact(
    problem: &RingNfNormalizedProblem,
    artifact: &RingNfProofArtifact,
) -> Result<SolverResourceUsage, SolverContractError> {
    let problem_bytes = ring_nf_normalized_problem_canonical_bytes(problem)?;
    let artifact_bytes = ring_nf_proof_artifact_canonical_bytes(artifact)?;
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: problem_bytes.len() as u64,
        generated_term_nodes: artifact.generated_term_nodes,
        proof_bytes: artifact.proof_bytes,
        solver_steps: problem.normalized_nodes,
        proof_steps: artifact.proof_steps,
        rule_count: artifact.algebra_law_refs.len() as u64,
        output_bytes: artifact_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn ring_nf_checked_proof_response(
    request: &SolverRequest,
    problem: &RingNfNormalizedProblem,
    proof_artifact: &RingNfProofArtifact,
    policy: &SolverResourcePolicy,
) -> Result<SolverResponse, SolverContractError> {
    validate_ring_nf_proof_artifact_for_problem(request, problem, proof_artifact)?;
    validate_solver_resource_policy_for_request(policy, request)?;
    let response = SolverResponse {
        version: SolverContractVersion::V1,
        status: SolverResponseStatus::Certificate,
        metadata: SolverResponseMetadata {
            request_hash: solver_request_hash(request)?,
            family: request.family,
            fragment: request.fragment,
            profile: request.profile,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            payload_hash: Some(proof_artifact.proof_identity.proof_term_hash),
            proof_payload_ref_hash: None,
            certificate_format: Some(SolverCertificateFormat::DirectNpaProofTermV1),
            certificate_metadata_hash: None,
            reconstruction_plan_hash: None,
        },
        payload: SolverResponsePayload::Certificate(SolverAcceptingPayload::CheckedProofTerm(
            proof_artifact.proof_identity.clone(),
        )),
        advisory: SolverResponseAdvisory::default(),
    };
    validate_solver_response_for_request(request, &response)?;
    enforce_solver_generated_artifact_resource_policy(
        policy,
        request,
        &response,
        ring_nf_resource_usage_from_proof_artifact(problem, proof_artifact)?,
    )?;
    Ok(response)
}

pub fn bitblast_encoding_options_from_policy(
    policy: &SolverResourcePolicy,
    request: &SolverRequest,
    backend_profile: BitblastBackendProfile,
) -> Result<BitblastEncodingOptions, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_solver_request(request)?;
    Ok(BitblastEncodingOptions {
        backend_profile,
        max_input_nodes: policy.max_input_nodes,
        max_variables: policy.max_rule_count.max(1),
        max_bitvector_width: policy.max_solver_steps.max(1),
        max_cnf_variables: policy.max_cnf_variables.max(1),
        max_cnf_clauses: policy.max_cnf_clauses.max(1),
    })
}

pub fn bitblast_encode_problem(
    request: &SolverRequest,
    local_context: &[BitblastLocalContextEntry],
    target: &Expr,
    options: &BitblastEncodingOptions,
) -> Result<BitblastEncodedProblem, SolverContractError> {
    validate_bitblast_solver_request(request)?;
    if options.backend_profile != BitblastBackendProfile::CnfTseitinV1 {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast BDD artifacts are reserved for a later backend contract",
        });
    }
    let input_nodes = bitblast_expr_node_count(target, options.max_input_nodes)?;
    let mut parser = BitblastParser {
        local_context,
        options,
        used_locals: BTreeSet::new(),
    };
    let parsed = parser.parse_target(target)?;
    let used_indices = parser.used_locals.iter().copied().collect::<Vec<_>>();
    if used_indices.len() as u64 > options.max_variables {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::RuleCount,
            limit: options.max_variables,
            actual: used_indices.len() as u64,
        });
    }

    let mut local_to_ordinal = BTreeMap::new();
    let mut variables = Vec::with_capacity(used_indices.len());
    for (ordinal, local_index) in used_indices.iter().copied().enumerate() {
        let Some(entry) = local_context.get(local_index) else {
            return Err(SolverContractError::UnsupportedBitblastFragment {
                reason: "de Bruijn index outside bitblast local context",
            });
        };
        let sort = bitblast_sort_for_type(&entry.ty, options)?;
        let source_core_expr = bitblast_bvar_for_local(local_context.len(), local_index)?;
        let ordinal_u64 = ordinal as u64;
        local_to_ordinal.insert(local_index, ordinal_u64);
        variables.push(BitblastVariable {
            ordinal: ordinal_u64,
            local_index: local_index as u64,
            name: entry.name.clone(),
            sort,
            source_core_expr_hash: core_expr_hash(&source_core_expr),
            type_hash: core_expr_hash(&entry.ty),
        });
    }

    let root = bitblast_remap_reflected(&parsed, &local_to_ordinal)?;
    if bitblast_reflected_expr_sort(&root)? != BitblastSort::Bool {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast root must be a Bool formula",
        });
    }
    let variable_map = bitblast_variable_map_from_variables(&variables)?;
    let mut encoder = BitblastCnfEncoder::new(&variable_map);
    let output = encoder.encode_expr(&root)?;
    if output.sort != BitblastSort::Bool || output.literals.len() != 1 {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast encoded root did not produce one Bool output literal",
        });
    }
    let output_literal = output.literals[0];
    encoder.add_output_assertion(
        output_literal,
        output.root_node_id,
        bitblast_reflected_expr_hash(&root)?,
    )?;
    let (circuit_nodes, clauses, variable_count) = encoder.finish();
    if variable_count > options.max_cnf_variables {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::CnfVariables,
            limit: options.max_cnf_variables,
            actual: variable_count,
        });
    }
    if clauses.len() as u64 > options.max_cnf_clauses {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::CnfClauses,
            limit: options.max_cnf_clauses,
            actual: clauses.len() as u64,
        });
    }

    let operation_profile = bitblast_operation_profile_for_root(&root)?;
    let root_hash = bitblast_reflected_expr_hash(&root)?;
    let variable_map_hash = bitblast_variable_map_hash(&variable_map)?;
    let circuit_hash = bitblast_circuit_hash(&circuit_nodes)?;
    let semantic_plan = bitblast_semantic_plan_for_encoding(
        operation_profile,
        options.backend_profile,
        root_hash,
        variable_map_hash,
        circuit_hash,
        clauses.len() as u64,
    )?;
    let semantic_plan_hash = bitblast_semantic_plan_hash(&semantic_plan)?;
    let cnf_artifact = BitblastCnfArtifact {
        backend_profile: options.backend_profile,
        root_reflected_expr_hash: root_hash,
        variable_map_hash,
        circuit_hash,
        semantic_plan_hash,
        variable_count,
        clauses,
        output_literal,
    };
    let encoded_nodes = bitblast_reflected_expr_node_count(&root)
        .saturating_add(variables.len() as u64)
        .saturating_add(variable_map.len() as u64)
        .saturating_add(circuit_nodes.len() as u64)
        .saturating_add(cnf_artifact.clauses.len() as u64)
        .saturating_add(semantic_plan.steps.len() as u64);
    let problem = BitblastEncodedProblem {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        operation_profile,
        backend_profile: options.backend_profile,
        input_nodes,
        encoded_nodes,
        variables,
        root,
        variable_map,
        circuit_nodes,
        semantic_plan,
        cnf_artifact,
    };
    validate_bitblast_encoded_problem(&problem)?;
    Ok(problem)
}

pub fn bitblast_reflected_expr_canonical_bytes(
    expr: &BitblastReflectedExpr,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_reflected_expr_shape(expr, None)?;
    let mut out = Vec::new();
    encode_bitblast_reflected_expr_to(&mut out, expr);
    Ok(out)
}

pub fn bitblast_reflected_expr_hash(
    expr: &BitblastReflectedExpr,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_REFLECTED_EXPR_HASH_TAG,
        &bitblast_reflected_expr_canonical_bytes(expr)?,
    ))
}

pub fn bitblast_variable_map_canonical_bytes(
    entries: &[BitblastVariableMapEntry],
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_variable_map_shape(entries)?;
    let mut out = Vec::new();
    encode_len_to(&mut out, entries.len());
    for entry in entries {
        encode_bitblast_variable_map_entry_to(&mut out, entry);
    }
    Ok(out)
}

pub fn bitblast_variable_map_hash(
    entries: &[BitblastVariableMapEntry],
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_VARIABLE_MAP_HASH_TAG,
        &bitblast_variable_map_canonical_bytes(entries)?,
    ))
}

pub fn bitblast_circuit_canonical_bytes(
    nodes: &[BitblastCircuitNode],
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_circuit_shape(nodes)?;
    let mut out = Vec::new();
    encode_len_to(&mut out, nodes.len());
    for node in nodes {
        encode_bitblast_circuit_node_to(&mut out, node);
    }
    Ok(out)
}

pub fn bitblast_circuit_hash(nodes: &[BitblastCircuitNode]) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_CIRCUIT_HASH_TAG,
        &bitblast_circuit_canonical_bytes(nodes)?,
    ))
}

pub fn bitblast_semantic_plan_canonical_bytes(
    plan: &BitblastSemanticPlan,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_semantic_plan_shape(plan)?;
    let mut out = Vec::new();
    out.push(plan.operation_profile.tag());
    out.push(plan.backend_profile.tag());
    encode_hash_to(&mut out, &plan.root_reflected_expr_hash);
    encode_hash_to(&mut out, &plan.variable_map_hash);
    encode_hash_to(&mut out, &plan.circuit_hash);
    encode_len_to(&mut out, plan.steps.len());
    for step in &plan.steps {
        encode_bitblast_semantic_step_to(&mut out, step);
    }
    Ok(out)
}

pub fn bitblast_semantic_plan_hash(
    plan: &BitblastSemanticPlan,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_SEMANTIC_PLAN_HASH_TAG,
        &bitblast_semantic_plan_canonical_bytes(plan)?,
    ))
}

pub fn bitblast_cnf_artifact_canonical_bytes(
    artifact: &BitblastCnfArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_cnf_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.backend_profile.tag());
    encode_hash_to(&mut out, &artifact.root_reflected_expr_hash);
    encode_hash_to(&mut out, &artifact.variable_map_hash);
    encode_hash_to(&mut out, &artifact.circuit_hash);
    encode_hash_to(&mut out, &artifact.semantic_plan_hash);
    encode_u64_to(&mut out, artifact.variable_count);
    encode_len_to(&mut out, artifact.clauses.len());
    for clause in &artifact.clauses {
        encode_bitblast_cnf_clause_to(&mut out, clause);
    }
    encode_bitblast_cnf_literal_to(&mut out, artifact.output_literal);
    Ok(out)
}

pub fn bitblast_cnf_artifact_hash(
    artifact: &BitblastCnfArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_CNF_ARTIFACT_HASH_TAG,
        &bitblast_cnf_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn bitblast_encoded_problem_canonical_bytes(
    problem: &BitblastEncodedProblem,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_encoded_problem(problem)?;
    let mut out = Vec::new();
    out.push(problem.version.tag());
    out.push(problem.operation_profile.tag());
    out.push(problem.backend_profile.tag());
    encode_hash_to(&mut out, &problem.request_hash);
    encode_u64_to(&mut out, problem.input_nodes);
    encode_u64_to(&mut out, problem.encoded_nodes);
    encode_len_to(&mut out, problem.variables.len());
    for variable in &problem.variables {
        encode_bitblast_variable_to(&mut out, variable);
    }
    encode_hash_to(&mut out, &bitblast_reflected_expr_hash(&problem.root)?);
    encode_hash_to(
        &mut out,
        &bitblast_variable_map_hash(&problem.variable_map)?,
    );
    encode_hash_to(&mut out, &bitblast_circuit_hash(&problem.circuit_nodes)?);
    encode_hash_to(
        &mut out,
        &bitblast_semantic_plan_hash(&problem.semantic_plan)?,
    );
    encode_hash_to(
        &mut out,
        &bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
    );
    Ok(out)
}

pub fn bitblast_encoded_problem_hash(
    problem: &BitblastEncodedProblem,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_ENCODED_PROBLEM_HASH_TAG,
        &bitblast_encoded_problem_canonical_bytes(problem)?,
    ))
}

pub fn bitblast_resource_usage_from_encoded_problem(
    problem: &BitblastEncodedProblem,
) -> Result<SolverResourceUsage, SolverContractError> {
    let canonical_bytes = bitblast_encoded_problem_canonical_bytes(problem)?;
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: canonical_bytes.len() as u64,
        generated_term_nodes: problem.cnf_artifact.variable_count,
        certificate_bytes: bitblast_cnf_artifact_canonical_bytes(&problem.cnf_artifact)?.len()
            as u64,
        cnf_variables: problem.cnf_artifact.variable_count,
        cnf_clauses: problem.cnf_artifact.clauses.len() as u64,
        solver_steps: problem.encoded_nodes,
        rule_count: problem.variables.len() as u64,
        output_bytes: canonical_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn bitblast_semantic_proof_artifact_for_encoded_problem(
    request: &SolverRequest,
    problem: &BitblastEncodedProblem,
    proof_identity: SolverCheckedProofTermIdentity,
    generated_term_nodes: u64,
    proof_bytes: u64,
    proof_steps: u64,
) -> Result<BitblastSemanticProofArtifact, SolverContractError> {
    validate_bitblast_solver_request(request)?;
    validate_bitblast_encoded_problem(problem)?;
    require_bitblast_hash(
        "bitblast_request_hash",
        problem.request_hash,
        solver_request_hash(request)?,
    )?;
    let root_hash = bitblast_reflected_expr_hash(&problem.root)?;
    let variable_map_hash = bitblast_variable_map_hash(&problem.variable_map)?;
    let circuit_hash = bitblast_circuit_hash(&problem.circuit_nodes)?;
    let semantic_plan_hash = bitblast_semantic_plan_hash(&problem.semantic_plan)?;
    let cnf_artifact_hash = bitblast_cnf_artifact_hash(&problem.cnf_artifact)?;
    let steps = bitblast_reconstruction_steps_for_hashes(
        root_hash,
        variable_map_hash,
        circuit_hash,
        semantic_plan_hash,
        cnf_artifact_hash,
        request.goal_identity.target_hash,
    );
    let artifact = BitblastSemanticProofArtifact {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        encoded_problem_hash: bitblast_encoded_problem_hash(problem)?,
        root_reflected_expr_hash: root_hash,
        variable_map_hash,
        circuit_hash,
        semantic_plan_hash,
        cnf_artifact_hash,
        final_goal_hash: request.goal_identity.target_hash,
        steps,
        proof_identity,
        generated_term_nodes,
        proof_bytes,
        proof_steps,
    };
    validate_bitblast_semantic_proof_artifact_for_problem(request, problem, &artifact)?;
    Ok(artifact)
}

pub fn bitblast_semantic_proof_artifact_canonical_bytes(
    artifact: &BitblastSemanticProofArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_semantic_proof_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.request_hash);
    encode_hash_to(&mut out, &artifact.encoded_problem_hash);
    encode_hash_to(&mut out, &artifact.root_reflected_expr_hash);
    encode_hash_to(&mut out, &artifact.variable_map_hash);
    encode_hash_to(&mut out, &artifact.circuit_hash);
    encode_hash_to(&mut out, &artifact.semantic_plan_hash);
    encode_hash_to(&mut out, &artifact.cnf_artifact_hash);
    encode_hash_to(&mut out, &artifact.final_goal_hash);
    encode_len_to(&mut out, artifact.steps.len());
    for step in &artifact.steps {
        encode_bitblast_reconstruction_step_to(&mut out, step);
    }
    encode_hash_to(&mut out, &artifact.proof_identity.environment_hash);
    encode_hash_to(&mut out, &artifact.proof_identity.proof_term_hash);
    encode_hash_to(&mut out, &artifact.proof_identity.proof_type_hash);
    encode_u64_to(&mut out, artifact.generated_term_nodes);
    encode_u64_to(&mut out, artifact.proof_bytes);
    encode_u64_to(&mut out, artifact.proof_steps);
    Ok(out)
}

pub fn bitblast_semantic_proof_artifact_hash(
    artifact: &BitblastSemanticProofArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_SEMANTIC_PROOF_ARTIFACT_HASH_TAG,
        &bitblast_semantic_proof_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn validate_bitblast_semantic_proof_artifact_for_problem(
    request: &SolverRequest,
    problem: &BitblastEncodedProblem,
    artifact: &BitblastSemanticProofArtifact,
) -> Result<(), SolverContractError> {
    validate_bitblast_solver_request(request)?;
    validate_bitblast_encoded_problem(problem)?;
    validate_bitblast_semantic_proof_artifact_shape(artifact)?;
    require_bitblast_hash(
        "bitblast_semantic_proof_request_hash",
        artifact.request_hash,
        solver_request_hash(request)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_encoded_problem_hash",
        artifact.encoded_problem_hash,
        bitblast_encoded_problem_hash(problem)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_root_hash",
        artifact.root_reflected_expr_hash,
        bitblast_reflected_expr_hash(&problem.root)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_variable_map_hash",
        artifact.variable_map_hash,
        bitblast_variable_map_hash(&problem.variable_map)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_circuit_hash",
        artifact.circuit_hash,
        bitblast_circuit_hash(&problem.circuit_nodes)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_semantic_plan_hash",
        artifact.semantic_plan_hash,
        bitblast_semantic_plan_hash(&problem.semantic_plan)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_cnf_artifact_hash",
        artifact.cnf_artifact_hash,
        bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
    )?;
    require_bitblast_hash(
        "bitblast_semantic_proof_final_goal_hash",
        artifact.final_goal_hash,
        request.goal_identity.target_hash,
    )?;
    if artifact.proof_identity.environment_hash != request.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "environment_hash",
            expected: request.environment_hash,
            actual: artifact.proof_identity.environment_hash,
        });
    }
    if artifact.proof_identity.proof_type_hash != request.goal_identity.target_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "proof_type_hash",
            expected: request.goal_identity.target_hash,
            actual: artifact.proof_identity.proof_type_hash,
        });
    }
    Ok(())
}

pub fn bitblast_reconstruction_plan_from_semantic_proof(
    artifact: &BitblastSemanticProofArtifact,
) -> Result<SolverReconstructionPlanRef, SolverContractError> {
    validate_bitblast_semantic_proof_artifact_shape(artifact)?;
    let step_ids = artifact
        .steps
        .iter()
        .map(|step| step.kind.as_str().to_owned())
        .collect::<Vec<_>>();
    let final_step_id = step_ids.last().cloned();
    let plan = SolverReconstructionPlanRef {
        profile: SolverProfile::CheckedCertificateV1,
        reconstruction_plan_hash: bitblast_semantic_proof_artifact_hash(artifact)?,
        imported_theory_count: 0,
        step_count: step_ids.len() as u64,
        step_ids,
        final_step_id,
    };
    validate_solver_reconstruction_plan(&plan)?;
    Ok(plan)
}

pub fn bitblast_canonical_cnf_bytes(
    artifact: &BitblastCnfArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_cnf_artifact_shape(artifact)?;
    let mut text = format!(
        "p cnf {} {}\n",
        artifact.variable_count,
        artifact.clauses.len()
    );
    for clause in &artifact.clauses {
        for literal in &clause.literals {
            if !literal.positive {
                text.push('-');
            }
            text.push_str(&literal.variable.to_string());
            text.push(' ');
        }
        text.push_str("0\n");
    }
    Ok(text.into_bytes())
}

pub fn bitblast_canonical_cnf_hash(
    artifact: &BitblastCnfArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_CANONICAL_CNF_HASH_TAG,
        &bitblast_canonical_cnf_bytes(artifact)?,
    ))
}

pub fn bitblast_sat_handoff_for_encoded_problem(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    problem: &BitblastEncodedProblem,
) -> Result<BitblastSatHandoff, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_encoded_problem(problem)?;
    require_bitblast_hash(
        "bitblast_handoff_request_hash",
        problem.request_hash,
        solver_request_hash(request)?,
    )?;
    let handoff = BitblastSatHandoff {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        policy_hash: solver_resource_policy_hash(policy)?,
        encoded_problem_hash: bitblast_encoded_problem_hash(problem)?,
        root_reflected_expr_hash: bitblast_reflected_expr_hash(&problem.root)?,
        variable_map_hash: bitblast_variable_map_hash(&problem.variable_map)?,
        cnf_artifact_hash: bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
        canonical_cnf_hash: bitblast_canonical_cnf_hash(&problem.cnf_artifact)?,
        canonical_cnf_bytes: bitblast_canonical_cnf_bytes(&problem.cnf_artifact)?,
        cnf_variable_count: problem.cnf_artifact.variable_count,
        cnf_clause_count: problem.cnf_artifact.clauses.len() as u64,
    };
    validate_bitblast_sat_handoff_for_problem(request, policy, problem, &handoff)?;
    Ok(handoff)
}

pub fn bitblast_sat_handoff_canonical_bytes(
    handoff: &BitblastSatHandoff,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_sat_handoff_shape(handoff)?;
    let mut out = Vec::new();
    out.push(handoff.version.tag());
    encode_hash_to(&mut out, &handoff.request_hash);
    encode_hash_to(&mut out, &handoff.policy_hash);
    encode_hash_to(&mut out, &handoff.encoded_problem_hash);
    encode_hash_to(&mut out, &handoff.root_reflected_expr_hash);
    encode_hash_to(&mut out, &handoff.variable_map_hash);
    encode_hash_to(&mut out, &handoff.cnf_artifact_hash);
    encode_hash_to(&mut out, &handoff.canonical_cnf_hash);
    encode_u64_to(&mut out, handoff.cnf_variable_count);
    encode_u64_to(&mut out, handoff.cnf_clause_count);
    encode_len_to(&mut out, handoff.canonical_cnf_bytes.len());
    out.extend_from_slice(&handoff.canonical_cnf_bytes);
    Ok(out)
}

pub fn bitblast_sat_handoff_hash(
    handoff: &BitblastSatHandoff,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_SAT_HANDOFF_HASH_TAG,
        &bitblast_sat_handoff_canonical_bytes(handoff)?,
    ))
}

pub fn validate_bitblast_sat_handoff_for_problem(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    problem: &BitblastEncodedProblem,
    handoff: &BitblastSatHandoff,
) -> Result<(), SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_encoded_problem(problem)?;
    validate_bitblast_sat_handoff_shape(handoff)?;
    require_bitblast_hash(
        "bitblast_handoff_request_hash",
        handoff.request_hash,
        solver_request_hash(request)?,
    )?;
    require_bitblast_hash(
        "bitblast_handoff_policy_hash",
        handoff.policy_hash,
        solver_resource_policy_hash(policy)?,
    )?;
    require_bitblast_hash(
        "bitblast_handoff_encoded_problem_hash",
        handoff.encoded_problem_hash,
        bitblast_encoded_problem_hash(problem)?,
    )?;
    require_bitblast_hash(
        "bitblast_handoff_root_hash",
        handoff.root_reflected_expr_hash,
        bitblast_reflected_expr_hash(&problem.root)?,
    )?;
    require_bitblast_hash(
        "bitblast_handoff_variable_map_hash",
        handoff.variable_map_hash,
        bitblast_variable_map_hash(&problem.variable_map)?,
    )?;
    require_bitblast_hash(
        "bitblast_handoff_cnf_artifact_hash",
        handoff.cnf_artifact_hash,
        bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
    )?;
    require_bitblast_hash(
        "bitblast_handoff_canonical_cnf_hash",
        handoff.canonical_cnf_hash,
        bitblast_canonical_cnf_hash(&problem.cnf_artifact)?,
    )?;
    if handoff.canonical_cnf_bytes != bitblast_canonical_cnf_bytes(&problem.cnf_artifact)? {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "bitblast_canonical_cnf_bytes",
        });
    }
    if handoff.cnf_variable_count != problem.cnf_artifact.variable_count {
        return Err(SolverContractError::MismatchedHash {
            field: "bitblast_handoff_cnf_variable_count",
            expected: hash_u64(problem.cnf_artifact.variable_count),
            actual: hash_u64(handoff.cnf_variable_count),
        });
    }
    if handoff.cnf_clause_count != problem.cnf_artifact.clauses.len() as u64 {
        return Err(SolverContractError::MismatchedHash {
            field: "bitblast_handoff_cnf_clause_count",
            expected: hash_u64(problem.cnf_artifact.clauses.len() as u64),
            actual: hash_u64(handoff.cnf_clause_count),
        });
    }
    let mut usage = bitblast_resource_usage_from_encoded_problem(problem)?;
    usage.output_bytes = handoff.canonical_cnf_bytes.len() as u64;
    usage.nested_solver_calls = 1;
    enforce_solver_resource_usage(policy, usage)?;
    Ok(())
}

pub fn bitblast_sat_model_canonical_bytes(
    model: &BitblastSatModelArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_sat_model_shape(model)?;
    let mut out = Vec::new();
    out.push(model.version.tag());
    encode_hash_to(&mut out, &model.request_hash);
    encode_hash_to(&mut out, &model.encoded_problem_hash);
    encode_hash_to(&mut out, &model.cnf_artifact_hash);
    encode_hash_to(&mut out, &model.variable_map_hash);
    encode_len_to(&mut out, model.assignments.len());
    for assignment in &model.assignments {
        encode_u64_to(&mut out, assignment.cnf_variable);
        out.push(u8::from(assignment.value));
    }
    out.push(u8::from(model.output_literal_value));
    Ok(out)
}

pub fn bitblast_sat_model_hash(
    model: &BitblastSatModelArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_SAT_MODEL_HASH_TAG,
        &bitblast_sat_model_canonical_bytes(model)?,
    ))
}

pub fn validate_bitblast_sat_model_for_problem(
    request: &SolverRequest,
    problem: &BitblastEncodedProblem,
    model: &BitblastSatModelArtifact,
) -> Result<(), SolverContractError> {
    validate_bitblast_solver_request(request)?;
    validate_bitblast_encoded_problem(problem)?;
    validate_bitblast_sat_model_shape(model)?;
    require_bitblast_hash(
        "bitblast_model_request_hash",
        model.request_hash,
        solver_request_hash(request)?,
    )?;
    require_bitblast_hash(
        "bitblast_model_encoded_problem_hash",
        model.encoded_problem_hash,
        bitblast_encoded_problem_hash(problem)?,
    )?;
    require_bitblast_hash(
        "bitblast_model_cnf_artifact_hash",
        model.cnf_artifact_hash,
        bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
    )?;
    require_bitblast_hash(
        "bitblast_model_variable_map_hash",
        model.variable_map_hash,
        bitblast_variable_map_hash(&problem.variable_map)?,
    )?;
    if model.assignments.len() as u64 != problem.cnf_artifact.variable_count {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_sat_model_assignment_count",
        });
    }
    for (index, assignment) in model.assignments.iter().enumerate() {
        let expected = index as u64 + 1;
        if assignment.cnf_variable != expected {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_sat_model_assignment_order",
            });
        }
    }
    let output_value =
        bitblast_model_literal_value(&model.assignments, problem.cnf_artifact.output_literal)?;
    if output_value != model.output_literal_value || !output_value {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "bitblast_sat_model_output_literal",
        });
    }
    for clause in &problem.cnf_artifact.clauses {
        let satisfied = clause
            .literals
            .iter()
            .map(|literal| bitblast_model_literal_value(&model.assignments, *literal))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .any(|value| value);
        if !satisfied {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_sat_model_clause",
            });
        }
    }
    Ok(())
}

pub fn bitblast_counterexample_response_from_model(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    problem: &BitblastEncodedProblem,
    model: &BitblastSatModelArtifact,
) -> Result<SolverResponse, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_sat_model_for_problem(request, problem, model)?;
    let model_hash = bitblast_sat_model_hash(model)?;
    let response = SolverResponse {
        version: SolverContractVersion::V1,
        status: SolverResponseStatus::Counterexample,
        metadata: SolverResponseMetadata {
            request_hash: solver_request_hash(request)?,
            family: request.family,
            fragment: request.fragment,
            profile: request.profile,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            payload_hash: Some(model_hash),
            proof_payload_ref_hash: None,
            certificate_format: None,
            certificate_metadata_hash: None,
            reconstruction_plan_hash: None,
        },
        payload: SolverResponsePayload::Counterexample {
            counterexample_hash: model_hash,
        },
        advisory: SolverResponseAdvisory {
            display_text: Some("bitblast SAT model is diagnostic only".to_owned()),
            ..SolverResponseAdvisory::default()
        },
    };
    validate_solver_response_for_request(request, &response)?;
    enforce_solver_generated_artifact_resource_policy(
        policy,
        request,
        &response,
        bitblast_resource_usage_from_sat_model(problem, model)?,
    )?;
    Ok(response)
}

pub fn bitblast_checked_certificate_response_from_artifacts(
    request: &SolverRequest,
    policy: &SolverResourcePolicy,
    problem: &BitblastEncodedProblem,
    semantic_proof: &BitblastSemanticProofArtifact,
    proof_payload: &SolverProofPayloadRef,
) -> Result<SolverResponse, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_semantic_proof_artifact_for_problem(request, problem, semantic_proof)?;
    validate_solver_proof_payload_ref(proof_payload)?;
    if proof_payload.certificate_format != SolverCertificateFormat::LratV1 {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        });
    }
    validate_lrat_proof_payload_ref(proof_payload)?;
    Err(SolverContractError::UnsupportedBitblastFragment {
        reason: "bitblast LRAT acceptance requires a checked LRAT soundness bridge",
    })
}

pub fn lrat_cnf_from_bitblast_cnf_artifact(
    artifact: &BitblastCnfArtifact,
) -> Result<LratCnf, SolverContractError> {
    validate_bitblast_cnf_artifact_shape(artifact)?;
    let clauses = artifact
        .clauses
        .iter()
        .map(|clause| {
            let mut literals = clause
                .literals
                .iter()
                .map(|literal| LratLiteral {
                    variable: literal.variable,
                    positive: literal.positive,
                })
                .collect::<Vec<_>>();
            literals.sort();
            LratClause {
                line_id: clause.ordinal + 1,
                literals,
            }
        })
        .collect::<Vec<_>>();
    let cnf = LratCnf {
        version: SolverContractVersion::V1,
        variable_count: artifact.variable_count,
        clauses,
    };
    validate_lrat_cnf(&cnf)?;
    Ok(cnf)
}

pub fn bitblast_lrat_soundness_bridge_artifact(
    input: BitblastLratSoundnessBridgeInput<'_>,
) -> Result<BitblastLratSoundnessBridgeArtifact, SolverContractError> {
    let request = input.request;
    let policy = input.policy;
    let lrat_request = input.lrat_request;
    let lrat_policy = input.lrat_policy;
    let problem = input.problem;
    let semantic_proof = input.semantic_proof;
    let lrat_cnf = input.lrat_cnf;
    let lrat_certificate = input.lrat_certificate;
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_lrat_request_pair(request, lrat_request)?;
    validate_bitblast_semantic_proof_artifact_for_problem(request, problem, semantic_proof)?;
    let handoff = bitblast_sat_handoff_for_encoded_problem(request, policy, problem)?;
    let expected_lrat_cnf = lrat_cnf_from_bitblast_cnf_artifact(&problem.cnf_artifact)?;
    require_bitblast_hash(
        "bitblast_lrat_cnf_hash",
        lrat_cnf_hash(lrat_cnf)?,
        lrat_cnf_hash(&expected_lrat_cnf)?,
    )?;
    let lrat_bridge =
        lrat_cnf_unsat_bridge_artifact(lrat_request, lrat_policy, lrat_cnf, lrat_certificate)?;
    let artifact = BitblastLratSoundnessBridgeArtifact {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        policy_hash: solver_resource_policy_hash(policy)?,
        lrat_request_hash: solver_request_hash(lrat_request)?,
        lrat_policy_hash: solver_resource_policy_hash(lrat_policy)?,
        solver_profile: request.profile,
        certificate_format: SolverCertificateFormat::LratV1,
        encoded_problem_hash: bitblast_encoded_problem_hash(problem)?,
        root_reflected_expr_hash: bitblast_reflected_expr_hash(&problem.root)?,
        variable_map_hash: bitblast_variable_map_hash(&problem.variable_map)?,
        cnf_artifact_hash: bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
        canonical_cnf_hash: handoff.canonical_cnf_hash,
        lrat_cnf_hash: lrat_bridge.cnf_hash,
        lrat_certificate_hash: lrat_bridge.certificate_hash,
        lrat_payload_hash: lrat_bridge.payload_hash,
        lrat_proof_payload_ref_hash: lrat_bridge.proof_payload_ref_hash,
        lrat_check_artifact_hash: lrat_bridge.lrat_check_artifact_hash,
        lrat_cnf_unsat_bridge_hash: lrat_cnf_unsat_bridge_hash(&lrat_bridge)?,
        cnf_unsat_theorem_hash: lrat_bridge.cnf_unsat_theorem_hash,
        semantic_proof_artifact_hash: bitblast_semantic_proof_artifact_hash(semantic_proof)?,
        final_goal_hash: semantic_proof.final_goal_hash,
    };
    validate_bitblast_lrat_soundness_bridge_artifact(input, &artifact)?;
    Ok(artifact)
}

pub fn bitblast_lrat_soundness_bridge_canonical_bytes(
    artifact: &BitblastLratSoundnessBridgeArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_bitblast_lrat_soundness_bridge_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.request_hash);
    encode_hash_to(&mut out, &artifact.policy_hash);
    encode_hash_to(&mut out, &artifact.lrat_request_hash);
    encode_hash_to(&mut out, &artifact.lrat_policy_hash);
    out.push(artifact.solver_profile.tag());
    out.push(artifact.certificate_format.tag());
    encode_hash_to(&mut out, &artifact.encoded_problem_hash);
    encode_hash_to(&mut out, &artifact.root_reflected_expr_hash);
    encode_hash_to(&mut out, &artifact.variable_map_hash);
    encode_hash_to(&mut out, &artifact.cnf_artifact_hash);
    encode_hash_to(&mut out, &artifact.canonical_cnf_hash);
    encode_hash_to(&mut out, &artifact.lrat_cnf_hash);
    encode_hash_to(&mut out, &artifact.lrat_certificate_hash);
    encode_hash_to(&mut out, &artifact.lrat_payload_hash);
    encode_hash_to(&mut out, &artifact.lrat_proof_payload_ref_hash);
    encode_hash_to(&mut out, &artifact.lrat_check_artifact_hash);
    encode_hash_to(&mut out, &artifact.lrat_cnf_unsat_bridge_hash);
    encode_hash_to(&mut out, &artifact.cnf_unsat_theorem_hash);
    encode_hash_to(&mut out, &artifact.semantic_proof_artifact_hash);
    encode_hash_to(&mut out, &artifact.final_goal_hash);
    Ok(out)
}

pub fn bitblast_lrat_soundness_bridge_hash(
    artifact: &BitblastLratSoundnessBridgeArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        BITBLAST_LRAT_SOUNDNESS_BRIDGE_HASH_TAG,
        &bitblast_lrat_soundness_bridge_canonical_bytes(artifact)?,
    ))
}

pub fn validate_bitblast_lrat_soundness_bridge_artifact(
    input: BitblastLratSoundnessBridgeInput<'_>,
    artifact: &BitblastLratSoundnessBridgeArtifact,
) -> Result<(), SolverContractError> {
    let request = input.request;
    let policy = input.policy;
    let lrat_request = input.lrat_request;
    let lrat_policy = input.lrat_policy;
    let problem = input.problem;
    let semantic_proof = input.semantic_proof;
    let lrat_cnf = input.lrat_cnf;
    let lrat_certificate = input.lrat_certificate;
    validate_bitblast_lrat_soundness_bridge_artifact_shape(artifact)?;
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_bitblast_lrat_request_pair(request, lrat_request)?;
    validate_bitblast_semantic_proof_artifact_for_problem(request, problem, semantic_proof)?;
    let handoff = bitblast_sat_handoff_for_encoded_problem(request, policy, problem)?;
    let expected_lrat_cnf = lrat_cnf_from_bitblast_cnf_artifact(&problem.cnf_artifact)?;
    require_bitblast_hash(
        "bitblast_lrat_cnf_hash",
        lrat_cnf_hash(lrat_cnf)?,
        lrat_cnf_hash(&expected_lrat_cnf)?,
    )?;
    let lrat_bridge =
        lrat_cnf_unsat_bridge_artifact(lrat_request, lrat_policy, lrat_cnf, lrat_certificate)?;
    let payload_ref = lrat_proof_payload_ref(lrat_certificate)?;
    require_bitblast_hash(
        "bitblast_lrat_request_hash",
        artifact.request_hash,
        solver_request_hash(request)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_policy_hash",
        artifact.policy_hash,
        solver_resource_policy_hash(policy)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_checker_request_hash",
        artifact.lrat_request_hash,
        solver_request_hash(lrat_request)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_checker_policy_hash",
        artifact.lrat_policy_hash,
        solver_resource_policy_hash(lrat_policy)?,
    )?;
    if artifact.solver_profile != request.profile {
        return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
    }
    if artifact.certificate_format != SolverCertificateFormat::LratV1 {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        });
    }
    require_bitblast_hash(
        "bitblast_lrat_encoded_problem_hash",
        artifact.encoded_problem_hash,
        bitblast_encoded_problem_hash(problem)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_root_hash",
        artifact.root_reflected_expr_hash,
        bitblast_reflected_expr_hash(&problem.root)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_variable_map_hash",
        artifact.variable_map_hash,
        bitblast_variable_map_hash(&problem.variable_map)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_cnf_artifact_hash",
        artifact.cnf_artifact_hash,
        bitblast_cnf_artifact_hash(&problem.cnf_artifact)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_canonical_cnf_hash",
        artifact.canonical_cnf_hash,
        handoff.canonical_cnf_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_lrat_cnf_hash",
        artifact.lrat_cnf_hash,
        lrat_bridge.cnf_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_certificate_hash",
        artifact.lrat_certificate_hash,
        lrat_bridge.certificate_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_payload_hash",
        artifact.lrat_payload_hash,
        payload_ref.payload_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_payload_ref_hash",
        artifact.lrat_proof_payload_ref_hash,
        lrat_bridge.proof_payload_ref_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_check_artifact_hash",
        artifact.lrat_check_artifact_hash,
        lrat_bridge.lrat_check_artifact_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_cnf_unsat_bridge_hash",
        artifact.lrat_cnf_unsat_bridge_hash,
        lrat_cnf_unsat_bridge_hash(&lrat_bridge)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_cnf_unsat_theorem_hash",
        artifact.cnf_unsat_theorem_hash,
        lrat_bridge.cnf_unsat_theorem_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_semantic_proof_hash",
        artifact.semantic_proof_artifact_hash,
        bitblast_semantic_proof_artifact_hash(semantic_proof)?,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_final_goal_hash",
        artifact.final_goal_hash,
        request.goal_identity.target_hash,
    )
}

pub fn bitblast_lrat_reconstruction_plan_from_bridge(
    semantic_proof: &BitblastSemanticProofArtifact,
    bridge: &BitblastLratSoundnessBridgeArtifact,
) -> Result<SolverReconstructionPlanRef, SolverContractError> {
    validate_bitblast_semantic_proof_artifact_shape(semantic_proof)?;
    validate_bitblast_lrat_soundness_bridge_artifact_shape(bridge)?;
    let expected_semantic_hash = bitblast_semantic_proof_artifact_hash(semantic_proof)?;
    require_bitblast_hash(
        "bitblast_lrat_semantic_proof_hash",
        bridge.semantic_proof_artifact_hash,
        expected_semantic_hash,
    )?;
    require_bitblast_hash(
        "bitblast_lrat_final_goal_hash",
        bridge.final_goal_hash,
        semantic_proof.final_goal_hash,
    )?;
    let mut step_ids = semantic_proof
        .steps
        .iter()
        .take(4)
        .map(|step| step.kind.as_str().to_owned())
        .collect::<Vec<_>>();
    step_ids.push("lrat-cnf-unsat-soundness".to_owned());
    step_ids.push(
        BitblastReconstructionStepKind::CnfUnsatImpliesOriginalGoal
            .as_str()
            .to_owned(),
    );
    let final_step_id = step_ids.last().cloned();
    let plan = SolverReconstructionPlanRef {
        profile: SolverProfile::CheckedCertificateV1,
        reconstruction_plan_hash: bitblast_lrat_soundness_bridge_hash(bridge)?,
        imported_theory_count: 1,
        step_count: step_ids.len() as u64,
        step_ids,
        final_step_id,
    };
    validate_solver_reconstruction_plan(&plan)?;
    Ok(plan)
}

pub fn bitblast_lrat_checked_certificate_response_from_artifacts(
    input: BitblastLratSoundnessBridgeInput<'_>,
) -> Result<SolverResponse, SolverContractError> {
    let request = input.request;
    let policy = input.policy;
    let problem = input.problem;
    let semantic_proof = input.semantic_proof;
    let lrat_certificate = input.lrat_certificate;
    let bridge = bitblast_lrat_soundness_bridge_artifact(input)?;
    let proof_payload = lrat_proof_payload_ref(lrat_certificate)?;
    validate_lrat_proof_payload_ref(&proof_payload)?;
    let reconstruction_plan =
        bitblast_lrat_reconstruction_plan_from_bridge(semantic_proof, &bridge)?;
    let reconstruction_plan_hash = solver_reconstruction_plan_hash(&reconstruction_plan)?;
    let proof_payload_ref_hash = solver_proof_payload_ref_hash(&proof_payload)?;
    let certificate = SolverCertificateMetadata {
        family: request.family,
        fragment: request.fragment,
        profile: request.profile,
        certificate_format: proof_payload.certificate_format,
        environment_hash: request.environment_hash,
        policy_hash: request.policy_hash,
        payload_hash: proof_payload.payload_hash,
        proof_payload_ref_hash,
        reconstruction_plan_hash,
    };
    validate_solver_certificate_metadata(&certificate)?;
    let response = SolverResponse {
        version: SolverContractVersion::V1,
        status: SolverResponseStatus::Certificate,
        metadata: SolverResponseMetadata {
            request_hash: solver_request_hash(request)?,
            family: request.family,
            fragment: request.fragment,
            profile: request.profile,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            payload_hash: Some(certificate.payload_hash),
            proof_payload_ref_hash: Some(certificate.proof_payload_ref_hash),
            certificate_format: Some(certificate.certificate_format),
            certificate_metadata_hash: Some(solver_certificate_metadata_hash(&certificate)?),
            reconstruction_plan_hash: Some(certificate.reconstruction_plan_hash),
        },
        payload: SolverResponsePayload::Certificate(
            SolverAcceptingPayload::CheckedCertificateReconstruction(certificate),
        ),
        advisory: SolverResponseAdvisory::default(),
    };
    validate_solver_response_for_request(request, &response)?;
    enforce_solver_generated_artifact_resource_policy(
        policy,
        request,
        &response,
        bitblast_resource_usage_from_checked_certificate(problem, semantic_proof, &proof_payload)?,
    )?;
    Ok(response)
}

pub fn validate_bitblast_encoded_problem(
    problem: &BitblastEncodedProblem,
) -> Result<(), SolverContractError> {
    if problem.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "bitblast_version",
            tag: problem.version.as_str().to_owned(),
        });
    }
    if is_zero_hash(&problem.request_hash) {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "request_hash",
        });
    }
    if problem.backend_profile != BitblastBackendProfile::CnfTseitinV1 {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "only CNF/Tseitin bitblast encoded problems are supported in this contract",
        });
    }
    validate_bitblast_variables(&problem.variables)?;
    validate_bitblast_reflected_expr_shape(&problem.root, Some(problem.variables.len()))?;
    validate_bitblast_reflected_expr_for_variables(&problem.root, &problem.variables)?;
    if bitblast_reflected_expr_sort(&problem.root)? != BitblastSort::Bool {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast encoded problem root must be Bool",
        });
    }
    let expected_operation_profile = bitblast_operation_profile_for_root(&problem.root)?;
    if problem.operation_profile != expected_operation_profile {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "bitblast_operation_profile",
        });
    }
    validate_bitblast_variable_map_for_variables(&problem.variables, &problem.variable_map)?;
    validate_bitblast_circuit_shape(&problem.circuit_nodes)?;
    validate_bitblast_semantic_plan_shape(&problem.semantic_plan)?;
    validate_bitblast_cnf_artifact_shape(&problem.cnf_artifact)?;
    let root_hash = bitblast_reflected_expr_hash(&problem.root)?;
    let variable_map_hash = bitblast_variable_map_hash(&problem.variable_map)?;
    let circuit_hash = bitblast_circuit_hash(&problem.circuit_nodes)?;
    let semantic_plan_hash = bitblast_semantic_plan_hash(&problem.semantic_plan)?;
    require_bitblast_hash(
        "bitblast_plan_root_reflected_expr_hash",
        problem.semantic_plan.root_reflected_expr_hash,
        root_hash,
    )?;
    require_bitblast_hash(
        "bitblast_plan_variable_map_hash",
        problem.semantic_plan.variable_map_hash,
        variable_map_hash,
    )?;
    require_bitblast_hash(
        "bitblast_plan_circuit_hash",
        problem.semantic_plan.circuit_hash,
        circuit_hash,
    )?;
    require_bitblast_hash(
        "bitblast_cnf_root_reflected_expr_hash",
        problem.cnf_artifact.root_reflected_expr_hash,
        root_hash,
    )?;
    require_bitblast_hash(
        "bitblast_cnf_variable_map_hash",
        problem.cnf_artifact.variable_map_hash,
        variable_map_hash,
    )?;
    require_bitblast_hash(
        "bitblast_cnf_circuit_hash",
        problem.cnf_artifact.circuit_hash,
        circuit_hash,
    )?;
    require_bitblast_hash(
        "bitblast_cnf_semantic_plan_hash",
        problem.cnf_artifact.semantic_plan_hash,
        semantic_plan_hash,
    )?;
    if problem.operation_profile != problem.semantic_plan.operation_profile {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "bitblast_operation_profile",
        });
    }
    if problem.backend_profile != problem.semantic_plan.backend_profile
        || problem.backend_profile != problem.cnf_artifact.backend_profile
    {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "bitblast_backend_profile",
        });
    }
    let expected_nodes = bitblast_reflected_expr_node_count(&problem.root)
        .saturating_add(problem.variables.len() as u64)
        .saturating_add(problem.variable_map.len() as u64)
        .saturating_add(problem.circuit_nodes.len() as u64)
        .saturating_add(problem.cnf_artifact.clauses.len() as u64)
        .saturating_add(problem.semantic_plan.steps.len() as u64);
    if problem.encoded_nodes != expected_nodes {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::SolverSteps,
            limit: expected_nodes,
            actual: problem.encoded_nodes,
        });
    }
    Ok(())
}

pub fn validate_ring_nf_normalized_problem(
    problem: &RingNfNormalizedProblem,
) -> Result<(), SolverContractError> {
    if problem.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "ring_nf_version",
            tag: problem.version.as_str().to_owned(),
        });
    }
    if is_zero_hash(&problem.request_hash) {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "ring_nf_request_hash",
        });
    }
    validate_ring_nf_profile_domain(problem.algebra_profile, problem.coefficient_domain)?;
    validate_ring_nf_variables(&problem.variables)?;
    if is_zero_hash(&problem.equation.carrier_type_hash) {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "ring_nf equality carrier hash is missing",
        });
    }
    let variable_count = problem.variables.len();
    validate_ring_nf_reflected_expr_shape(&problem.equation.lhs_reflected, Some(variable_count))?;
    validate_ring_nf_reflected_expr_shape(&problem.equation.rhs_reflected, Some(variable_count))?;
    validate_ring_nf_polynomial_shape(
        &problem.equation.lhs_normal_form,
        Some(variable_count),
        problem.coefficient_domain,
    )?;
    validate_ring_nf_polynomial_shape(
        &problem.equation.rhs_normal_form,
        Some(variable_count),
        problem.coefficient_domain,
    )?;

    let validation_options = ring_nf_validation_options(problem.algebra_profile);
    let expected_lhs = ring_nf_polynomial_from_reflected(
        &problem.equation.lhs_reflected,
        &validation_options,
        variable_count,
    )?;
    let expected_rhs = ring_nf_polynomial_from_reflected(
        &problem.equation.rhs_reflected,
        &validation_options,
        variable_count,
    )?;
    if expected_lhs != problem.equation.lhs_normal_form {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "ring_nf_lhs_normal_form",
        });
    }
    if expected_rhs != problem.equation.rhs_normal_form {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "ring_nf_rhs_normal_form",
        });
    }

    match (
        problem.algebra_profile.allows_signed_coefficients(),
        &problem.equation.difference_normal_form,
    ) {
        (true, Some(difference)) => {
            validate_ring_nf_polynomial_shape(
                difference,
                Some(variable_count),
                problem.coefficient_domain,
            )?;
            let expected_difference =
                ring_nf_polynomial_sub(&expected_lhs, &expected_rhs, &validation_options)?;
            if &expected_difference != difference {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "ring_nf_difference_normal_form",
                });
            }
        }
        (true, None) => {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "ring_nf_difference_normal_form",
            });
        }
        (false, Some(_)) => {
            return Err(SolverContractError::UnsupportedRingNfOperation {
                profile: problem.algebra_profile,
                operator: "difference-normal-form".to_owned(),
            });
        }
        (false, None) => {}
    }

    if problem.equation.normal_forms_equal != (expected_lhs == expected_rhs) {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "ring_nf_normal_forms_equal",
        });
    }
    Ok(())
}

pub fn validate_ring_nf_proof_artifact_for_problem(
    request: &SolverRequest,
    problem: &RingNfNormalizedProblem,
    artifact: &RingNfProofArtifact,
) -> Result<(), SolverContractError> {
    validate_ring_nf_solver_request(request)?;
    validate_ring_nf_normalized_problem(problem)?;
    validate_ring_nf_proof_artifact_shape(artifact)?;
    let request_hash = solver_request_hash(request)?;
    if problem.request_hash != request_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_problem_request_hash",
            expected: request_hash,
            actual: problem.request_hash,
        });
    }
    if artifact.request_hash != request_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_request_hash",
            expected: request_hash,
            actual: artifact.request_hash,
        });
    }
    let normalized_problem_hash = ring_nf_normalized_problem_hash(problem)?;
    if artifact.normalized_problem_hash != normalized_problem_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_normalized_problem_hash",
            expected: normalized_problem_hash,
            actual: artifact.normalized_problem_hash,
        });
    }
    let profile_hash = ring_nf_profile_hash(problem.algebra_profile, problem.coefficient_domain)?;
    if artifact.profile_hash != profile_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_profile_hash",
            expected: profile_hash,
            actual: artifact.profile_hash,
        });
    }
    if artifact.policy_hash != request.policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_policy_hash",
            expected: request.policy_hash,
            actual: artifact.policy_hash,
        });
    }
    if artifact.proof_identity.environment_hash != request.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "proof_environment_hash",
            expected: request.environment_hash,
            actual: artifact.proof_identity.environment_hash,
        });
    }
    if artifact.proof_identity.proof_type_hash != request.goal_identity.target_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "proof_type_hash",
            expected: request.goal_identity.target_hash,
            actual: artifact.proof_identity.proof_type_hash,
        });
    }
    require_ring_nf_hash(
        "ring_nf_lhs_reflected_expr_hash",
        artifact.lhs_reflected_expr_hash,
        ring_nf_reflected_expr_hash(&problem.equation.lhs_reflected)?,
    )?;
    require_ring_nf_hash(
        "ring_nf_rhs_reflected_expr_hash",
        artifact.rhs_reflected_expr_hash,
        ring_nf_reflected_expr_hash(&problem.equation.rhs_reflected)?,
    )?;
    require_ring_nf_hash(
        "ring_nf_lhs_normal_form_hash",
        artifact.lhs_normal_form_hash,
        ring_nf_polynomial_hash(&problem.equation.lhs_normal_form)?,
    )?;
    require_ring_nf_hash(
        "ring_nf_rhs_normal_form_hash",
        artifact.rhs_normal_form_hash,
        ring_nf_polynomial_hash(&problem.equation.rhs_normal_form)?,
    )?;
    let expected_difference_hash = problem
        .equation
        .difference_normal_form
        .as_ref()
        .map(ring_nf_polynomial_hash)
        .transpose()?;
    if artifact.difference_normal_form_hash != expected_difference_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_difference_normal_form_hash",
            expected: expected_difference_hash.unwrap_or([0; 32]),
            actual: artifact.difference_normal_form_hash.unwrap_or([0; 32]),
        });
    }
    if !problem.equation.normal_forms_equal {
        return Err(SolverContractError::RingNfNormalFormsMismatch);
    }
    let variable_environment_hash =
        ring_nf_variable_environment_hash(&artifact.variable_environment)?;
    if artifact.variable_environment_hash != variable_environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "ring_nf_variable_environment_hash",
            expected: variable_environment_hash,
            actual: artifact.variable_environment_hash,
        });
    }
    validate_ring_nf_variable_environment_for_problem(problem, &artifact.variable_environment)?;
    validate_ring_nf_algebra_law_refs_for_problem(problem, &artifact.algebra_law_refs)
}

pub fn omega_reconstruction_step_result_hash(
    step: &OmegaReconstructionStep,
) -> Result<Hash, SolverContractError> {
    validate_omega_reconstruction_step_identity_shape(step)?;
    let mut out = Vec::new();
    encode_omega_reconstruction_step_identity_to(&mut out, step);
    Ok(hash_with_domain(OMEGA_RECONSTRUCTION_STEP_HASH_TAG, &out))
}

pub fn omega_certificate_artifact_canonical_bytes(
    artifact: &OmegaCertificateArtifact,
) -> Result<Vec<u8>, SolverContractError> {
    validate_omega_certificate_artifact_shape(artifact)?;
    let mut out = Vec::new();
    out.push(artifact.version.tag());
    encode_hash_to(&mut out, &artifact.request_hash);
    encode_hash_to(&mut out, &artifact.normalized_problem_hash);
    encode_hash_to(&mut out, &artifact.policy_hash);
    out.push(artifact.conclusion.tag());
    encode_len_to(&mut out, artifact.steps.len());
    for step in &artifact.steps {
        encode_omega_reconstruction_step_to(&mut out, step);
    }
    encode_string_to(&mut out, &artifact.final_step_id);
    Ok(out)
}

pub fn omega_certificate_artifact_hash(
    artifact: &OmegaCertificateArtifact,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        OMEGA_CERTIFICATE_ARTIFACT_HASH_TAG,
        &omega_certificate_artifact_canonical_bytes(artifact)?,
    ))
}

pub fn omega_reconstruction_plan_for_certificate(
    artifact: &OmegaCertificateArtifact,
) -> Result<SolverReconstructionPlanRef, SolverContractError> {
    validate_omega_certificate_artifact_shape(artifact)?;
    let mut out = Vec::new();
    encode_hash_to(&mut out, &omega_certificate_artifact_hash(artifact)?);
    encode_string_to(&mut out, &artifact.final_step_id);
    let reconstruction_plan_hash = hash_with_domain(OMEGA_RECONSTRUCTION_PLAN_REF_HASH_TAG, &out);
    let step_ids = artifact
        .steps
        .iter()
        .map(|step| step.step_id.clone())
        .collect::<Vec<_>>();
    let imported_theory_count = artifact
        .steps
        .iter()
        .map(|step| step.side_condition_ordinals.len() as u64)
        .sum::<u64>();
    let plan = SolverReconstructionPlanRef {
        profile: SolverProfile::CheckedCertificateV1,
        reconstruction_plan_hash,
        imported_theory_count,
        step_count: step_ids.len() as u64,
        step_ids,
        final_step_id: Some(artifact.final_step_id.clone()),
    };
    validate_solver_reconstruction_plan(&plan)?;
    Ok(plan)
}

pub fn omega_resource_usage_from_certificate(
    problem: &OmegaNormalizedProblem,
    artifact: &OmegaCertificateArtifact,
) -> Result<SolverResourceUsage, SolverContractError> {
    let problem_bytes = omega_normalized_problem_canonical_bytes(problem)?;
    let artifact_bytes = omega_certificate_artifact_canonical_bytes(artifact)?;
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: problem_bytes.len() as u64,
        generated_term_nodes: problem
            .normalized_nodes
            .saturating_add(artifact.steps.len() as u64),
        proof_bytes: artifact_bytes.len() as u64,
        certificate_bytes: artifact_bytes.len() as u64,
        solver_steps: artifact.steps.len() as u64,
        proof_steps: artifact.steps.len() as u64,
        rule_count: artifact.steps.len() as u64,
        output_bytes: artifact_bytes.len() as u64,
        ..SolverResourceUsage::default()
    })
}

pub fn validate_omega_certificate_artifact_for_problem(
    request: &SolverRequest,
    problem: &OmegaNormalizedProblem,
    artifact: &OmegaCertificateArtifact,
) -> Result<(), SolverContractError> {
    validate_omega_solver_request(request)?;
    validate_omega_normalized_problem(problem)?;
    validate_omega_certificate_artifact_shape(artifact)?;
    if problem.fragment_profile != OmegaFragmentProfile::LinearArithmeticV1 {
        return Err(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega reconstruction accepts only linear arithmetic normalized problems",
        });
    }
    let request_hash = solver_request_hash(request)?;
    if artifact.request_hash != request_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "omega_request_hash",
            expected: request_hash,
            actual: artifact.request_hash,
        });
    }
    if problem.request_hash != request_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "omega_problem_request_hash",
            expected: request_hash,
            actual: problem.request_hash,
        });
    }
    let normalized_problem_hash = omega_normalized_problem_hash(problem)?;
    if artifact.normalized_problem_hash != normalized_problem_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "omega_normalized_problem_hash",
            expected: normalized_problem_hash,
            actual: artifact.normalized_problem_hash,
        });
    }
    if artifact.policy_hash != request.policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "omega_policy_hash",
            expected: request.policy_hash,
            actual: artifact.policy_hash,
        });
    }
    validate_omega_reconstruction_steps_for_problem(problem, artifact)
}

pub fn omega_checked_certificate_response(
    request: &SolverRequest,
    problem: &OmegaNormalizedProblem,
    artifact: &OmegaCertificateArtifact,
    policy: &SolverResourcePolicy,
) -> Result<SolverResponse, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_omega_certificate_artifact_for_problem(request, problem, artifact)?;
    let canonical_bytes = omega_certificate_artifact_canonical_bytes(artifact)?;
    let payload_hash = solver_inline_payload_hash(
        SolverCertificateFormat::OmegaPresburgerTraceV1,
        &canonical_bytes,
    )?;
    let payload_ref = SolverProofPayloadRef {
        certificate_format: SolverCertificateFormat::OmegaPresburgerTraceV1,
        payload_hash,
        size_bytes: canonical_bytes.len() as u64,
        canonical_bytes: Some(canonical_bytes),
    };
    let reconstruction_plan = omega_reconstruction_plan_for_certificate(artifact)?;
    let reconstruction_plan_hash = solver_reconstruction_plan_hash(&reconstruction_plan)?;
    let certificate = SolverCertificateMetadata {
        family: SolverFamily::Omega,
        fragment: SolverFragment::PresburgerLinearArithmeticV1,
        profile: SolverProfile::CheckedCertificateV1,
        certificate_format: SolverCertificateFormat::OmegaPresburgerTraceV1,
        environment_hash: request.environment_hash,
        policy_hash: request.policy_hash,
        payload_hash,
        proof_payload_ref_hash: solver_proof_payload_ref_hash(&payload_ref)?,
        reconstruction_plan_hash,
    };
    let response = SolverResponse {
        version: SolverContractVersion::V1,
        status: SolverResponseStatus::Certificate,
        metadata: SolverResponseMetadata {
            request_hash: solver_request_hash(request)?,
            family: request.family,
            fragment: request.fragment,
            profile: request.profile,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            payload_hash: Some(certificate.payload_hash),
            proof_payload_ref_hash: Some(certificate.proof_payload_ref_hash),
            certificate_format: Some(certificate.certificate_format),
            certificate_metadata_hash: Some(solver_certificate_metadata_hash(&certificate)?),
            reconstruction_plan_hash: Some(certificate.reconstruction_plan_hash),
        },
        payload: SolverResponsePayload::Certificate(
            SolverAcceptingPayload::CheckedCertificateReconstruction(certificate),
        ),
        advisory: SolverResponseAdvisory::default(),
    };
    validate_solver_response_for_request(request, &response)?;
    enforce_solver_generated_artifact_resource_policy(
        policy,
        request,
        &response,
        omega_resource_usage_from_certificate(problem, artifact)?,
    )?;
    Ok(response)
}

pub fn validate_omega_normalized_problem(
    problem: &OmegaNormalizedProblem,
) -> Result<(), SolverContractError> {
    if problem.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "omega_version",
            tag: problem.version.as_str().to_owned(),
        });
    }
    if is_zero_hash(&problem.request_hash) {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "omega_request_hash",
        });
    }
    validate_omega_variables(&problem.variables)?;
    let variable_count = problem.variables.len();
    validate_omega_formula(&problem.formula, variable_count)?;
    let mut nat_variables = BTreeSet::new();
    for variable in &problem.variables {
        if variable.sort == OmegaTermSort::Nat {
            nat_variables.insert(variable.ordinal);
        }
    }
    let mut covered_nat_variables = BTreeSet::new();
    let mut previous_side_condition_ordinal = None;
    for side_condition in &problem.nat_to_int_side_conditions {
        if let Some(previous) = previous_side_condition_ordinal {
            if side_condition.variable_ordinal <= previous {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_nat_to_int_side_condition_order",
                });
            }
        }
        previous_side_condition_ordinal = Some(side_condition.variable_ordinal);
        if !nat_variables.contains(&side_condition.variable_ordinal) {
            return Err(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: side_condition.variable_ordinal,
            });
        }
        let variable = problem
            .variables
            .get(side_condition.variable_ordinal as usize)
            .ok_or(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: side_condition.variable_ordinal,
            })?;
        if side_condition.source_core_expr_hash != variable.source_core_expr_hash {
            return Err(SolverContractError::MismatchedHash {
                field: "omega_nat_to_int_source_core_expr_hash",
                expected: variable.source_core_expr_hash,
                actual: side_condition.source_core_expr_hash,
            });
        }
        if side_condition.int_symbol != omega_smt_symbol_for_variable(variable) {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "omega_nat_to_int_symbol",
            });
        }
        if is_zero_hash(&side_condition.source_core_expr_hash)
            || is_zero_hash(&side_condition.smt_side_condition_hash)
            || side_condition.int_symbol.ascii.is_empty()
        {
            return Err(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: side_condition.variable_ordinal,
            });
        }
        match side_condition.discharge {
            OmegaNatToIntDischarge::ProofObligation { obligation_hash }
            | OmegaNatToIntDischarge::ImportedTheorem {
                theorem_hash: obligation_hash,
            } if !is_zero_hash(&obligation_hash) => {}
            OmegaNatToIntDischarge::ProofObligation { .. }
            | OmegaNatToIntDischarge::ImportedTheorem { .. }
            | OmegaNatToIntDischarge::Missing => {
                return Err(SolverContractError::MissingOmegaSideConditionDischarge {
                    variable_ordinal: side_condition.variable_ordinal,
                });
            }
        }
        covered_nat_variables.insert(side_condition.variable_ordinal);
    }
    for ordinal in nat_variables {
        if !covered_nat_variables.contains(&ordinal) {
            return Err(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: ordinal,
            });
        }
    }
    for expansion in &problem.bounded_expansions {
        if expansion.bound != expansion.expanded_case_hashes.len() as u64 {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "bounded expansion case count does not match bound",
            });
        }
        if expansion.binder_name.is_empty()
            || is_zero_hash(&expansion.source_core_expr_hash)
            || expansion.expanded_case_hashes.iter().any(is_zero_hash)
        {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "bounded expansion identity is incomplete",
            });
        }
    }
    Ok(())
}

fn validate_omega_certificate_artifact_shape(
    artifact: &OmegaCertificateArtifact,
) -> Result<(), SolverContractError> {
    if artifact.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "omega_certificate_version",
            tag: artifact.version.as_str().to_owned(),
        });
    }
    if is_zero_hash(&artifact.request_hash) {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "omega_request_hash",
        });
    }
    if is_zero_hash(&artifact.normalized_problem_hash) {
        return Err(SolverContractError::MissingPayloadHash);
    }
    if is_zero_hash(&artifact.policy_hash) {
        return Err(SolverContractError::MissingPolicyHash);
    }
    if artifact.final_step_id.is_empty() || artifact.steps.is_empty() {
        return Err(SolverContractError::MissingOmegaCertificateStep {
            step_id: artifact.final_step_id.clone(),
        });
    }
    let mut seen = BTreeSet::new();
    for step in &artifact.steps {
        validate_omega_reconstruction_step_shape(step)?;
        if !seen.insert(step.step_id.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "omega_step_id",
                identifier: step.step_id.clone(),
            });
        }
    }
    if !seen.contains(artifact.final_step_id.as_str()) {
        return Err(SolverContractError::MissingOmegaCertificateStep {
            step_id: artifact.final_step_id.clone(),
        });
    }
    if artifact.steps.last().map(|step| step.step_id.as_str())
        != Some(artifact.final_step_id.as_str())
    {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "omega_final_step_id",
        });
    }
    Ok(())
}

fn validate_omega_reconstruction_step_shape(
    step: &OmegaReconstructionStep,
) -> Result<(), SolverContractError> {
    validate_omega_reconstruction_step_identity_shape(step)?;
    if is_zero_hash(&step.result_hash) {
        return Err(SolverContractError::MissingPayloadHash);
    }
    Ok(())
}

fn validate_omega_reconstruction_step_identity_shape(
    step: &OmegaReconstructionStep,
) -> Result<(), SolverContractError> {
    if step.step_id.is_empty() {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "omega_step_id",
        });
    }
    validate_string_list("omega_input_step_id", &step.input_step_ids)?;
    validate_u64_list("omega_atom_index", &step.atom_indices)?;
    validate_u64_list(
        "omega_side_condition_ordinal",
        &step.side_condition_ordinals,
    )
}

fn validate_omega_reconstruction_steps_for_problem(
    problem: &OmegaNormalizedProblem,
    artifact: &OmegaCertificateArtifact,
) -> Result<(), SolverContractError> {
    let mut atoms = Vec::new();
    collect_omega_atoms(&problem.formula, &mut atoms);
    let mut seen_steps = BTreeSet::new();
    let mut saw_comparison = false;
    let mut saw_boolean = false;
    let mut saw_nat_side_condition = problem.nat_to_int_side_conditions.is_empty();
    let mut saw_linear_combination = false;
    let mut derived_terms: BTreeMap<String, Option<OmegaLinearTerm>> = BTreeMap::new();

    for step in &artifact.steps {
        let expected_result_hash = omega_reconstruction_step_result_hash(step)?;
        if step.result_hash != expected_result_hash {
            return Err(SolverContractError::MismatchedHash {
                field: "omega_step_result_hash",
                expected: expected_result_hash,
                actual: step.result_hash,
            });
        }
        for input_step_id in &step.input_step_ids {
            if !seen_steps.contains(input_step_id.as_str()) {
                return Err(SolverContractError::MissingOmegaCertificateStep {
                    step_id: input_step_id.clone(),
                });
            }
        }
        let derived_term =
            validate_omega_reconstruction_rule_for_problem(problem, &atoms, &derived_terms, step)?;
        match step.rule {
            OmegaReconstructionRule::ComparisonNormalization => saw_comparison = true,
            OmegaReconstructionRule::BooleanSplit => saw_boolean = true,
            OmegaReconstructionRule::NatSideConditionDischarge => {
                saw_nat_side_condition = true;
            }
            OmegaReconstructionRule::LinearCombination => saw_linear_combination = true,
            OmegaReconstructionRule::Contradiction => {}
        }
        derived_terms.insert(step.step_id.clone(), derived_term);
        seen_steps.insert(step.step_id.as_str());
    }

    let Some(final_step) = artifact.steps.last() else {
        return Err(SolverContractError::MissingOmegaCertificateStep {
            step_id: artifact.final_step_id.clone(),
        });
    };
    if final_step.rule != OmegaReconstructionRule::Contradiction {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "omega_final_step_rule",
        });
    }
    if !(saw_comparison && saw_boolean && saw_nat_side_condition && saw_linear_combination) {
        return Err(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega certificate is missing a required reconstruction rule",
        });
    }
    Ok(())
}

fn validate_omega_reconstruction_rule_for_problem(
    problem: &OmegaNormalizedProblem,
    atoms: &[&OmegaAtom],
    derived_terms: &BTreeMap<String, Option<OmegaLinearTerm>>,
    step: &OmegaReconstructionStep,
) -> Result<Option<OmegaLinearTerm>, SolverContractError> {
    match step.rule {
        OmegaReconstructionRule::ComparisonNormalization => {
            require_empty_string_list("omega_comparison_inputs", &step.input_step_ids)?;
            require_empty_u64_list(
                "omega_comparison_side_conditions",
                &step.side_condition_ordinals,
            )?;
            if step.atom_indices.len() != 1 {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_comparison_atom_index",
                });
            }
            validate_omega_atom_indices(atoms, &step.atom_indices)?;
            validate_omega_step_coefficients(problem, step)?;
            let atom = atoms[step.atom_indices[0] as usize];
            if step.coefficients != atom.normalized_lhs_minus_rhs.coefficients
                || step.constant != atom.normalized_lhs_minus_rhs.constant
            {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_comparison_normal_form",
                });
            }
            Ok(Some(omega_step_output_term(step)))
        }
        OmegaReconstructionRule::BooleanSplit => {
            if step.input_step_ids.is_empty() {
                return Err(SolverContractError::MissingOmegaCertificateStep {
                    step_id: step.step_id.clone(),
                });
            }
            require_empty_u64_list("omega_boolean_atom_index", &step.atom_indices)?;
            require_empty_u64_list(
                "omega_boolean_side_conditions",
                &step.side_condition_ordinals,
            )?;
            validate_omega_step_coefficients(problem, step)?;
            if !omega_formula_has_boolean(&problem.formula) {
                return Err(SolverContractError::UnsupportedOmegaFragment {
                    reason: "omega Boolean split requires a normalized Boolean formula",
                });
            }
            let input_term = omega_single_input_term(derived_terms, step, "omega_boolean_inputs")?;
            if omega_step_output_term(step) != input_term {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_boolean_split_output",
                });
            }
            Ok(Some(input_term))
        }
        OmegaReconstructionRule::NatSideConditionDischarge => {
            require_empty_string_list("omega_nat_side_condition_inputs", &step.input_step_ids)?;
            require_empty_u64_list("omega_nat_side_condition_atom_index", &step.atom_indices)?;
            validate_omega_step_coefficients(problem, step)?;
            if step.side_condition_ordinals.is_empty() {
                return Err(SolverContractError::MissingOmegaSideCondition {
                    variable_ordinal: 0,
                });
            }
            for ordinal in &step.side_condition_ordinals {
                let side_condition = problem
                    .nat_to_int_side_conditions
                    .iter()
                    .find(|side_condition| side_condition.variable_ordinal == *ordinal)
                    .ok_or(SolverContractError::MissingOmegaSideCondition {
                        variable_ordinal: *ordinal,
                    })?;
                match side_condition.discharge {
                    OmegaNatToIntDischarge::ProofObligation { obligation_hash }
                    | OmegaNatToIntDischarge::ImportedTheorem {
                        theorem_hash: obligation_hash,
                    } if !is_zero_hash(&obligation_hash) => {}
                    OmegaNatToIntDischarge::ProofObligation { .. }
                    | OmegaNatToIntDischarge::ImportedTheorem { .. }
                    | OmegaNatToIntDischarge::Missing => {
                        return Err(SolverContractError::MissingOmegaSideConditionDischarge {
                            variable_ordinal: *ordinal,
                        });
                    }
                }
            }
            Ok(None)
        }
        OmegaReconstructionRule::LinearCombination => {
            if step.input_step_ids.is_empty() {
                return Err(SolverContractError::MissingOmegaCertificateStep {
                    step_id: step.step_id.clone(),
                });
            }
            validate_omega_atom_indices(atoms, &step.atom_indices)?;
            require_empty_u64_list(
                "omega_linear_side_conditions",
                &step.side_condition_ordinals,
            )?;
            validate_omega_step_coefficients(problem, step)?;
            let input_sum =
                omega_sum_input_terms(derived_terms, step, "omega_linear_combination_inputs")?;
            if omega_step_output_term(step) != input_sum {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_linear_combination_output",
                });
            }
            Ok(Some(input_sum))
        }
        OmegaReconstructionRule::Contradiction => {
            if step.input_step_ids.is_empty() {
                return Err(SolverContractError::MissingOmegaCertificateStep {
                    step_id: step.step_id.clone(),
                });
            }
            require_empty_u64_list("omega_contradiction_atom_index", &step.atom_indices)?;
            require_empty_u64_list(
                "omega_contradiction_side_conditions",
                &step.side_condition_ordinals,
            )?;
            validate_omega_step_coefficients(problem, step)?;
            let input_term =
                omega_single_input_term(derived_terms, step, "omega_contradiction_inputs")?;
            let output_term = omega_step_output_term(step);
            if output_term != input_term {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_contradiction_output",
                });
            }
            if output_term
                .coefficients
                .iter()
                .any(|coefficient| *coefficient != 0)
                || output_term.constant <= 0
            {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_contradiction_linear_term",
                });
            }
            Ok(Some(output_term))
        }
    }
}

fn validate_omega_step_coefficients(
    problem: &OmegaNormalizedProblem,
    step: &OmegaReconstructionStep,
) -> Result<(), SolverContractError> {
    if step.coefficients.len() != problem.variables.len() {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "omega_step_coefficients",
        });
    }
    Ok(())
}

fn omega_step_output_term(step: &OmegaReconstructionStep) -> OmegaLinearTerm {
    OmegaLinearTerm {
        coefficients: step.coefficients.clone(),
        constant: step.constant,
    }
}

fn omega_single_input_term(
    derived_terms: &BTreeMap<String, Option<OmegaLinearTerm>>,
    step: &OmegaReconstructionStep,
    field: &'static str,
) -> Result<OmegaLinearTerm, SolverContractError> {
    let mut terms = omega_input_terms(derived_terms, step)?;
    if terms.len() != 1 {
        return Err(SolverContractError::NonCanonicalPayloadBytes { field });
    }
    Ok(terms.remove(0))
}

fn omega_sum_input_terms(
    derived_terms: &BTreeMap<String, Option<OmegaLinearTerm>>,
    step: &OmegaReconstructionStep,
    field: &'static str,
) -> Result<OmegaLinearTerm, SolverContractError> {
    let terms = omega_input_terms(derived_terms, step)?;
    let Some(first) = terms.first() else {
        return Err(SolverContractError::NonCanonicalPayloadBytes { field });
    };
    let mut sum = OmegaLinearTerm {
        coefficients: vec![0; first.coefficients.len()],
        constant: 0,
    };
    for term in terms {
        if term.coefficients.len() != sum.coefficients.len() {
            return Err(SolverContractError::NonCanonicalPayloadBytes { field });
        }
        for (sum_coefficient, coefficient) in sum.coefficients.iter_mut().zip(term.coefficients) {
            *sum_coefficient = omega_checked_i64_add(*sum_coefficient, coefficient)?;
        }
        sum.constant = omega_checked_i64_add(sum.constant, term.constant)?;
    }
    Ok(sum)
}

fn omega_input_terms(
    derived_terms: &BTreeMap<String, Option<OmegaLinearTerm>>,
    step: &OmegaReconstructionStep,
) -> Result<Vec<OmegaLinearTerm>, SolverContractError> {
    let mut terms = Vec::new();
    for input_step_id in &step.input_step_ids {
        match derived_terms.get(input_step_id) {
            Some(Some(term)) => terms.push(term.clone()),
            Some(None) => {}
            None => {
                return Err(SolverContractError::MissingOmegaCertificateStep {
                    step_id: input_step_id.clone(),
                });
            }
        }
    }
    Ok(terms)
}

fn validate_omega_atom_indices(
    atoms: &[&OmegaAtom],
    atom_indices: &[u64],
) -> Result<(), SolverContractError> {
    for index in atom_indices {
        if (*index as usize) >= atoms.len() {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "omega_atom_index",
            });
        }
    }
    Ok(())
}

fn collect_omega_atoms<'a>(formula: &'a OmegaFormula, atoms: &mut Vec<&'a OmegaAtom>) {
    match formula {
        OmegaFormula::Atom(atom) => atoms.push(atom),
        OmegaFormula::Boolean { args, .. } => {
            for arg in args {
                collect_omega_atoms(arg, atoms);
            }
        }
    }
}

fn omega_formula_has_boolean(formula: &OmegaFormula) -> bool {
    matches!(formula, OmegaFormula::Boolean { .. })
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ParsedBitblastReflectedExpr {
    BoolConstant {
        value: bool,
        source_core_expr_hash: Hash,
    },
    Variable {
        local_index: usize,
        sort: BitblastSort,
        source_core_expr_hash: Hash,
    },
    Unary {
        op: BitblastUnaryOp,
        arg: Box<ParsedBitblastReflectedExpr>,
        result_sort: BitblastSort,
        source_core_expr_hash: Hash,
    },
    Binary {
        op: BitblastBinaryOp,
        lhs: Box<ParsedBitblastReflectedExpr>,
        rhs: Box<ParsedBitblastReflectedExpr>,
        result_sort: BitblastSort,
        source_core_expr_hash: Hash,
    },
    Equal {
        sort: BitblastSort,
        lhs: Box<ParsedBitblastReflectedExpr>,
        rhs: Box<ParsedBitblastReflectedExpr>,
        source_core_expr_hash: Hash,
    },
}

struct BitblastParser<'a> {
    local_context: &'a [BitblastLocalContextEntry],
    options: &'a BitblastEncodingOptions,
    used_locals: BTreeSet<usize>,
}

impl BitblastParser<'_> {
    fn parse_target(
        &mut self,
        expr: &Expr,
    ) -> Result<ParsedBitblastReflectedExpr, SolverContractError> {
        if let Some((carrier, lhs, rhs)) = bitblast_parse_eq_target(expr)? {
            let sort = bitblast_sort_for_type(&carrier, self.options)?;
            let lhs = self.parse_expr(&lhs)?;
            bitblast_require_parsed_sort(&lhs, &sort)?;
            let rhs = self.parse_expr(&rhs)?;
            bitblast_require_parsed_sort(&rhs, &sort)?;
            return Ok(ParsedBitblastReflectedExpr::Equal {
                sort,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                source_core_expr_hash: core_expr_hash(expr),
            });
        }
        let parsed = self.parse_expr(expr)?;
        bitblast_require_parsed_sort(&parsed, &BitblastSort::Bool)?;
        Ok(parsed)
    }

    fn parse_expr(
        &mut self,
        expr: &Expr,
    ) -> Result<ParsedBitblastReflectedExpr, SolverContractError> {
        if let Some(value) = bitblast_bool_literal(expr) {
            return Ok(ParsedBitblastReflectedExpr::BoolConstant {
                value,
                source_core_expr_hash: core_expr_hash(expr),
            });
        }
        if let Expr::BVar(index) = expr {
            let local_index = bitblast_local_index_for_bvar(self.local_context.len(), *index)?;
            let entry = self.local_context.get(local_index).ok_or(
                SolverContractError::UnsupportedBitblastFragment {
                    reason: "de Bruijn index outside bitblast local context",
                },
            )?;
            let sort = bitblast_sort_for_type(&entry.ty, self.options)?;
            self.used_locals.insert(local_index);
            return Ok(ParsedBitblastReflectedExpr::Variable {
                local_index,
                sort,
                source_core_expr_hash: core_expr_hash(expr),
            });
        }

        let (head, args) = collect_apps(expr);
        let Some(name) = bitblast_head_const_name(&head) else {
            return Err(SolverContractError::UnsupportedBitblastFragment {
                reason: "bitblast expression head is not a constant",
            });
        };
        if matches!(
            name,
            "BitVector.add"
                | "BitVec.add"
                | "BitVector.mul"
                | "BitVec.mul"
                | "BitVector.sub"
                | "BitVec.sub"
                | "BitVector.udiv"
                | "BitVec.udiv"
                | "BitVector.sdiv"
                | "BitVec.sdiv"
                | "BitVector.shl"
                | "BitVec.shl"
                | "BitVector.lshr"
                | "BitVec.lshr"
        ) {
            return Err(SolverContractError::UnsupportedBitblastOperator {
                operator: name.to_owned(),
            });
        }
        match name {
            "Bool.not" | "not" => {
                if args.len() != 1 {
                    return Err(SolverContractError::UnsupportedBitblastFragment {
                        reason: "Bool.not must have exactly one argument",
                    });
                }
                let arg = self.parse_expr(&args[0])?;
                bitblast_require_parsed_sort(&arg, &BitblastSort::Bool)?;
                Ok(ParsedBitblastReflectedExpr::Unary {
                    op: BitblastUnaryOp::Not,
                    arg: Box::new(arg),
                    result_sort: BitblastSort::Bool,
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            "Bool.and" | "and" | "Bool.or" | "or" | "Bool.xor" | "Bool.iff" | "Bool.implies"
            | "implies" => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedBitblastFragment {
                        reason: "Bool binary operator must have exactly two arguments",
                    });
                }
                let op = bitblast_bool_binary_operator(name).ok_or_else(|| {
                    SolverContractError::UnsupportedBitblastOperator {
                        operator: name.to_owned(),
                    }
                })?;
                let lhs = self.parse_expr(&args[0])?;
                bitblast_require_parsed_sort(&lhs, &BitblastSort::Bool)?;
                let rhs = self.parse_expr(&args[1])?;
                bitblast_require_parsed_sort(&rhs, &BitblastSort::Bool)?;
                Ok(ParsedBitblastReflectedExpr::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    result_sort: BitblastSort::Bool,
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            "BitVector.not" | "BitVec.not" => {
                if args.len() != 1 {
                    return Err(SolverContractError::UnsupportedBitblastFragment {
                        reason: "BitVector.not must have exactly one argument",
                    });
                }
                let arg = self.parse_expr(&args[0])?;
                let result_sort = bitblast_require_parsed_bitvector_sort(&arg)?;
                Ok(ParsedBitblastReflectedExpr::Unary {
                    op: BitblastUnaryOp::BvNot,
                    arg: Box::new(arg),
                    result_sort,
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            "BitVector.and" | "BitVec.and" | "BitVector.or" | "BitVec.or" | "BitVector.xor"
            | "BitVec.xor" => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedBitblastFragment {
                        reason: "BitVector binary operator must have exactly two arguments",
                    });
                }
                let op = bitblast_bitvector_binary_operator(name).ok_or_else(|| {
                    SolverContractError::UnsupportedBitblastOperator {
                        operator: name.to_owned(),
                    }
                })?;
                let lhs = self.parse_expr(&args[0])?;
                let lhs_sort = bitblast_require_parsed_bitvector_sort(&lhs)?;
                let rhs = self.parse_expr(&args[1])?;
                bitblast_require_parsed_sort(&rhs, &lhs_sort)?;
                Ok(ParsedBitblastReflectedExpr::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    result_sort: lhs_sort,
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            _ => Err(SolverContractError::UnsupportedBitblastOperator {
                operator: name.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct EncodedBitblastBits {
    sort: BitblastSort,
    literals: Vec<BitblastCnfLiteral>,
    literal_node_ids: Vec<u64>,
    root_node_id: u64,
}

struct BitblastCnfEncoder {
    variable_map: BTreeMap<u64, BitblastVariableMapEntry>,
    input_node_ids: BTreeMap<u64, u64>,
    next_var: u64,
    circuit_nodes: Vec<BitblastCircuitNode>,
    clauses: Vec<BitblastCnfClause>,
}

impl BitblastCnfEncoder {
    fn new(variable_map: &[BitblastVariableMapEntry]) -> Self {
        let mut encoder = Self {
            variable_map: BTreeMap::new(),
            input_node_ids: BTreeMap::new(),
            next_var: 1,
            circuit_nodes: Vec::new(),
            clauses: Vec::new(),
        };
        for entry in variable_map {
            encoder.next_var = encoder
                .next_var
                .max(entry.tseitin_variable_start.saturating_add(entry.bit_width));
            let node_id = encoder.push_node(
                BitblastCircuitNodeKind::Input,
                entry.sort.clone(),
                Vec::new(),
                entry.source_core_expr_hash,
                entry.tseitin_variable_start,
                entry.bit_width,
            );
            encoder
                .variable_map
                .insert(entry.variable_ordinal, entry.clone());
            encoder
                .input_node_ids
                .insert(entry.variable_ordinal, node_id);
        }
        encoder
    }

    fn encode_expr(
        &mut self,
        expr: &BitblastReflectedExpr,
    ) -> Result<EncodedBitblastBits, SolverContractError> {
        match expr {
            BitblastReflectedExpr::BoolConstant {
                value,
                source_core_expr_hash,
            } => {
                let lit = self.alloc_literal();
                self.add_clause(
                    vec![if *value { lit } else { lit.negated() }],
                    BitblastClauseRole::ConstantDefinition,
                    *source_core_expr_hash,
                );
                let node_id = self.push_node(
                    BitblastCircuitNodeKind::Constant,
                    BitblastSort::Bool,
                    Vec::new(),
                    *source_core_expr_hash,
                    lit.variable,
                    1,
                );
                Ok(EncodedBitblastBits {
                    sort: BitblastSort::Bool,
                    literals: vec![lit],
                    literal_node_ids: vec![node_id],
                    root_node_id: node_id,
                })
            }
            BitblastReflectedExpr::Variable {
                variable_ordinal,
                sort,
                ..
            } => {
                let Some(entry) = self.variable_map.get(variable_ordinal) else {
                    return Err(SolverContractError::UnsupportedBitblastFragment {
                        reason: "bitblast variable missing from variable map",
                    });
                };
                let literals = (0..entry.bit_width)
                    .map(|offset| BitblastCnfLiteral {
                        variable: entry.tseitin_variable_start + offset,
                        positive: true,
                    })
                    .collect::<Vec<_>>();
                let node_id = *self.input_node_ids.get(variable_ordinal).ok_or(
                    SolverContractError::UnsupportedBitblastFragment {
                        reason: "bitblast variable input node missing",
                    },
                )?;
                Ok(EncodedBitblastBits {
                    sort: sort.clone(),
                    literals,
                    literal_node_ids: vec![node_id; entry.bit_width as usize],
                    root_node_id: node_id,
                })
            }
            BitblastReflectedExpr::Unary {
                op,
                arg,
                result_sort,
                source_core_expr_hash,
            } => {
                let arg = self.encode_expr(arg)?;
                match op {
                    BitblastUnaryOp::Not => {
                        let input = bitblast_single_bool_literal(&arg)?;
                        let (output, node_id) = self.encode_not_literal(
                            input,
                            *source_core_expr_hash,
                            vec![arg.root_node_id],
                        );
                        Ok(EncodedBitblastBits {
                            sort: result_sort.clone(),
                            literals: vec![output],
                            literal_node_ids: vec![node_id],
                            root_node_id: node_id,
                        })
                    }
                    BitblastUnaryOp::BvNot => {
                        let mut literals = Vec::with_capacity(arg.literals.len());
                        let mut literal_node_ids = Vec::with_capacity(arg.literal_node_ids.len());
                        for (input, input_node_id) in
                            arg.literals.into_iter().zip(arg.literal_node_ids)
                        {
                            let (output, node_id) = self.encode_not_literal(
                                input,
                                *source_core_expr_hash,
                                vec![input_node_id],
                            );
                            literals.push(output);
                            literal_node_ids.push(node_id);
                        }
                        let root_node_id =
                            literal_node_ids.last().copied().unwrap_or(arg.root_node_id);
                        Ok(EncodedBitblastBits {
                            sort: result_sort.clone(),
                            literals,
                            literal_node_ids,
                            root_node_id,
                        })
                    }
                }
            }
            BitblastReflectedExpr::Binary {
                op,
                lhs,
                rhs,
                result_sort,
                source_core_expr_hash,
            } => {
                let lhs = self.encode_expr(lhs)?;
                let rhs = self.encode_expr(rhs)?;
                match op {
                    BitblastBinaryOp::And
                    | BitblastBinaryOp::Or
                    | BitblastBinaryOp::Xor
                    | BitblastBinaryOp::Iff
                    | BitblastBinaryOp::Implies => {
                        let lhs_lit = bitblast_single_bool_literal(&lhs)?;
                        let rhs_lit = bitblast_single_bool_literal(&rhs)?;
                        let (output, node_id) = self.encode_binary_literal(
                            *op,
                            lhs_lit,
                            rhs_lit,
                            *source_core_expr_hash,
                            vec![lhs.root_node_id, rhs.root_node_id],
                        )?;
                        Ok(EncodedBitblastBits {
                            sort: result_sort.clone(),
                            literals: vec![output],
                            literal_node_ids: vec![node_id],
                            root_node_id: node_id,
                        })
                    }
                    BitblastBinaryOp::BvAnd | BitblastBinaryOp::BvOr | BitblastBinaryOp::BvXor => {
                        if lhs.literals.len() != rhs.literals.len() {
                            return Err(SolverContractError::BitblastWidthMismatch {
                                expected_width: lhs.literals.len() as u64,
                                actual_width: rhs.literals.len() as u64,
                            });
                        }
                        let mut literals = Vec::with_capacity(lhs.literals.len());
                        let mut literal_node_ids = Vec::with_capacity(lhs.literal_node_ids.len());
                        for (((lhs_lit, lhs_node_id), rhs_lit), rhs_node_id) in lhs
                            .literals
                            .into_iter()
                            .zip(lhs.literal_node_ids)
                            .zip(rhs.literals)
                            .zip(rhs.literal_node_ids)
                        {
                            let bool_op = match op {
                                BitblastBinaryOp::BvAnd => BitblastBinaryOp::And,
                                BitblastBinaryOp::BvOr => BitblastBinaryOp::Or,
                                BitblastBinaryOp::BvXor => BitblastBinaryOp::Xor,
                                _ => unreachable!("checked above"),
                            };
                            let (output, node_id) = self.encode_binary_literal(
                                bool_op,
                                lhs_lit,
                                rhs_lit,
                                *source_core_expr_hash,
                                vec![lhs_node_id, rhs_node_id],
                            )?;
                            literals.push(output);
                            literal_node_ids.push(node_id);
                        }
                        let root_node_id = literal_node_ids
                            .last()
                            .copied()
                            .unwrap_or(lhs.root_node_id.max(rhs.root_node_id));
                        Ok(EncodedBitblastBits {
                            sort: result_sort.clone(),
                            literals,
                            literal_node_ids,
                            root_node_id,
                        })
                    }
                }
            }
            BitblastReflectedExpr::Equal {
                sort,
                lhs,
                rhs,
                source_core_expr_hash,
            } => {
                let lhs = self.encode_expr(lhs)?;
                let rhs = self.encode_expr(rhs)?;
                match sort {
                    BitblastSort::Bool => {
                        let lhs_lit = bitblast_single_bool_literal(&lhs)?;
                        let rhs_lit = bitblast_single_bool_literal(&rhs)?;
                        let (output, node_id) = self.encode_binary_literal(
                            BitblastBinaryOp::Iff,
                            lhs_lit,
                            rhs_lit,
                            *source_core_expr_hash,
                            vec![lhs.root_node_id, rhs.root_node_id],
                        )?;
                        Ok(EncodedBitblastBits {
                            sort: BitblastSort::Bool,
                            literals: vec![output],
                            literal_node_ids: vec![node_id],
                            root_node_id: node_id,
                        })
                    }
                    BitblastSort::BitVector { width } => {
                        if lhs.literals.len() != *width as usize
                            || rhs.literals.len() != *width as usize
                        {
                            return Err(SolverContractError::BitblastWidthMismatch {
                                expected_width: *width,
                                actual_width: lhs.literals.len().max(rhs.literals.len()) as u64,
                            });
                        }
                        let mut equal_bits = Vec::with_capacity(*width as usize);
                        for (((lhs_lit, lhs_node_id), rhs_lit), rhs_node_id) in lhs
                            .literals
                            .into_iter()
                            .zip(lhs.literal_node_ids)
                            .zip(rhs.literals)
                            .zip(rhs.literal_node_ids)
                        {
                            let (bit_equal, node_id) = self.encode_binary_literal(
                                BitblastBinaryOp::Iff,
                                lhs_lit,
                                rhs_lit,
                                *source_core_expr_hash,
                                vec![lhs_node_id, rhs_node_id],
                            )?;
                            equal_bits.push((bit_equal, node_id));
                        }
                        let (output, node_id) =
                            self.and_reduce_literals(equal_bits, *source_core_expr_hash)?;
                        Ok(EncodedBitblastBits {
                            sort: BitblastSort::Bool,
                            literals: vec![output],
                            literal_node_ids: vec![node_id],
                            root_node_id: node_id,
                        })
                    }
                }
            }
        }
    }

    fn add_output_assertion(
        &mut self,
        literal: BitblastCnfLiteral,
        input_node_id: u64,
        source_reflected_expr_hash: Hash,
    ) -> Result<(), SolverContractError> {
        self.add_clause(
            vec![literal],
            BitblastClauseRole::OutputAssertion,
            source_reflected_expr_hash,
        );
        self.push_node(
            BitblastCircuitNodeKind::OutputAssertion,
            BitblastSort::Bool,
            vec![input_node_id],
            source_reflected_expr_hash,
            literal.variable,
            1,
        );
        Ok(())
    }

    fn finish(self) -> (Vec<BitblastCircuitNode>, Vec<BitblastCnfClause>, u64) {
        let variable_count = self.next_var.saturating_sub(1);
        (self.circuit_nodes, self.clauses, variable_count)
    }

    fn alloc_literal(&mut self) -> BitblastCnfLiteral {
        let literal = BitblastCnfLiteral {
            variable: self.next_var,
            positive: true,
        };
        self.next_var = self.next_var.saturating_add(1);
        literal
    }

    fn encode_not_literal(
        &mut self,
        input: BitblastCnfLiteral,
        source_hash: Hash,
        input_node_ids: Vec<u64>,
    ) -> (BitblastCnfLiteral, u64) {
        let output = self.alloc_literal();
        self.add_clause(
            vec![output.negated(), input.negated()],
            BitblastClauseRole::TseitinDefinition,
            source_hash,
        );
        self.add_clause(
            vec![output, input],
            BitblastClauseRole::TseitinDefinition,
            source_hash,
        );
        let node_id = self.push_node(
            BitblastCircuitNodeKind::Not,
            BitblastSort::Bool,
            input_node_ids,
            source_hash,
            output.variable,
            1,
        );
        (output, node_id)
    }

    fn encode_binary_literal(
        &mut self,
        op: BitblastBinaryOp,
        lhs: BitblastCnfLiteral,
        rhs: BitblastCnfLiteral,
        source_hash: Hash,
        input_node_ids: Vec<u64>,
    ) -> Result<(BitblastCnfLiteral, u64), SolverContractError> {
        let output = self.alloc_literal();
        match op {
            BitblastBinaryOp::And => {
                self.add_clause(
                    vec![output.negated(), lhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output.negated(), rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, lhs.negated(), rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
            }
            BitblastBinaryOp::Or => {
                self.add_clause(
                    vec![output, lhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output.negated(), lhs, rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
            }
            BitblastBinaryOp::Xor => {
                self.add_clause(
                    vec![output.negated(), lhs, rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output.negated(), lhs.negated(), rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, lhs, rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, lhs.negated(), rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
            }
            BitblastBinaryOp::Iff => {
                self.add_clause(
                    vec![output.negated(), lhs.negated(), rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output.negated(), lhs, rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, lhs, rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, lhs.negated(), rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
            }
            BitblastBinaryOp::Implies => {
                self.add_clause(
                    vec![output.negated(), lhs.negated(), rhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, lhs],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
                self.add_clause(
                    vec![output, rhs.negated()],
                    BitblastClauseRole::TseitinDefinition,
                    source_hash,
                );
            }
            BitblastBinaryOp::BvAnd | BitblastBinaryOp::BvOr | BitblastBinaryOp::BvXor => {
                return Err(SolverContractError::UnsupportedBitblastOperator {
                    operator: "bitvector aggregate op in Bool encoder".to_owned(),
                });
            }
        }
        let kind = match op {
            BitblastBinaryOp::And => BitblastCircuitNodeKind::And,
            BitblastBinaryOp::Or => BitblastCircuitNodeKind::Or,
            BitblastBinaryOp::Xor => BitblastCircuitNodeKind::Xor,
            BitblastBinaryOp::Iff => BitblastCircuitNodeKind::Iff,
            BitblastBinaryOp::Implies => BitblastCircuitNodeKind::Implies,
            BitblastBinaryOp::BvAnd | BitblastBinaryOp::BvOr | BitblastBinaryOp::BvXor => {
                unreachable!("checked above")
            }
        };
        let node_id = self.push_node(
            kind,
            BitblastSort::Bool,
            input_node_ids,
            source_hash,
            output.variable,
            1,
        );
        Ok((output, node_id))
    }

    fn and_reduce_literals(
        &mut self,
        literals: Vec<(BitblastCnfLiteral, u64)>,
        source_hash: Hash,
    ) -> Result<(BitblastCnfLiteral, u64), SolverContractError> {
        let mut iter = literals.into_iter();
        let Some((mut acc, mut acc_node_id)) = iter.next() else {
            return Err(SolverContractError::UnsupportedBitblastFragment {
                reason: "zero-width bit-vector equality is not supported",
            });
        };
        for (next, next_node_id) in iter {
            let (out, node_id) = self.encode_binary_literal(
                BitblastBinaryOp::And,
                acc,
                next,
                source_hash,
                vec![acc_node_id, next_node_id],
            )?;
            acc = out;
            acc_node_id = node_id;
        }
        Ok((acc, acc_node_id))
    }

    fn add_clause(
        &mut self,
        literals: Vec<BitblastCnfLiteral>,
        role: BitblastClauseRole,
        source_reflected_expr_hash: Hash,
    ) {
        let ordinal = self.clauses.len() as u64;
        self.clauses.push(BitblastCnfClause {
            ordinal,
            literals,
            role,
            source_reflected_expr_hash,
        });
    }

    fn push_node(
        &mut self,
        kind: BitblastCircuitNodeKind,
        result_sort: BitblastSort,
        input_node_ids: Vec<u64>,
        source_reflected_expr_hash: Hash,
        output_tseitin_start: u64,
        output_width: u64,
    ) -> u64 {
        let node_id = self.circuit_nodes.len() as u64;
        self.circuit_nodes.push(BitblastCircuitNode {
            node_id,
            kind,
            result_sort,
            input_node_ids,
            source_reflected_expr_hash,
            output_tseitin_start,
            output_width,
        });
        node_id
    }
}

impl BitblastCnfLiteral {
    fn negated(self) -> Self {
        Self {
            variable: self.variable,
            positive: !self.positive,
        }
    }
}

fn validate_bitblast_solver_request(request: &SolverRequest) -> Result<(), SolverContractError> {
    validate_solver_request(request)?;
    if request.family != SolverFamily::Bitblast {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if request.fragment != SolverFragment::BitVectorBitblastV1 {
        return Err(SolverContractError::UnsupportedFragment {
            family: request.family,
            fragment: request.fragment,
        });
    }
    if request.profile != SolverProfile::ExternalSidecarV1 {
        return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
    }
    Ok(())
}

fn bitblast_parse_eq_target(
    expr: &Expr,
) -> Result<Option<(Expr, Expr, Expr)>, SolverContractError> {
    let (head, args) = collect_apps(expr);
    let Expr::Const { name, levels } = head else {
        return Ok(None);
    };
    if name == "Eq" && levels.len() == 1 && args.len() == 3 {
        return Ok(Some((args[0].clone(), args[1].clone(), args[2].clone())));
    }
    if name == "Eq" && levels.is_empty() && args.len() == 4 {
        return Ok(Some((args[1].clone(), args[2].clone(), args[3].clone())));
    }
    if name == "Eq" {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast Eq target must carry a structurally encoded carrier",
        });
    }
    Ok(None)
}

fn bitblast_sort_for_type(
    expr: &Expr,
    options: &BitblastEncodingOptions,
) -> Result<BitblastSort, SolverContractError> {
    let (head, args) = collect_apps(expr);
    let Some(name) = bitblast_head_const_name(&head) else {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast type head is not a constant",
        });
    };
    match name {
        "Bool" | "Bool.Bool" if args.is_empty() => Ok(BitblastSort::Bool),
        "BitVector" | "BitVec" | "BitVector.BitVector" | "BitVec.BitVec" if args.len() == 1 => {
            let Some(width) = bitblast_width_literal(&args[0]) else {
                return Err(SolverContractError::UnsupportedBitblastFragment {
                    reason: "BitVector width must be a structural nonnegative literal",
                });
            };
            if width == 0 {
                return Err(SolverContractError::UnsupportedBitblastFragment {
                    reason: "zero-width BitVector is not supported",
                });
            }
            if width > options.max_bitvector_width {
                return Err(SolverContractError::ResourceLimitExceeded {
                    field: SolverResourceField::SolverSteps,
                    limit: options.max_bitvector_width,
                    actual: width,
                });
            }
            Ok(BitblastSort::BitVector { width })
        }
        "BitVector" | "BitVec" | "BitVector.BitVector" | "BitVec.BitVec" => {
            Err(SolverContractError::UnsupportedBitblastFragment {
                reason: "BitVector type must have exactly one width argument",
            })
        }
        _ => Err(SolverContractError::UnsupportedBitblastOperator {
            operator: name.to_owned(),
        }),
    }
}

fn bitblast_width_literal(expr: &Expr) -> Option<u64> {
    let (head, args) = collect_apps(expr);
    if !args.is_empty() {
        return None;
    }
    let name = bitblast_head_const_name(&head)?;
    match name {
        "Nat.zero" | "BitVector.Width.z" | "BitVec.Width.z" => Some(0),
        "Nat.one" | "BitVector.Width.p1" | "BitVec.Width.p1" => Some(1),
        _ => bitblast_prefixed_width_literal(name, "BitVector.Width.")
            .or_else(|| bitblast_prefixed_width_literal(name, "BitVec.Width."))
            .or_else(|| bitblast_prefixed_width_literal(name, "Ring.NatLit."))
            .or_else(|| bitblast_prefixed_width_literal(name, "Omega.NatLit.")),
    }
}

fn bitblast_prefixed_width_literal(name: &str, prefix: &str) -> Option<u64> {
    let suffix = name.strip_prefix(prefix)?;
    if suffix == "z" {
        return Some(0);
    }
    let digits = suffix.strip_prefix('p')?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn bitblast_bool_literal(expr: &Expr) -> Option<bool> {
    let (head, args) = collect_apps(expr);
    if !args.is_empty() {
        return None;
    }
    match bitblast_head_const_name(&head)? {
        "Bool.true" | "true" => Some(true),
        "Bool.false" | "false" => Some(false),
        _ => None,
    }
}

fn bitblast_head_const_name(head: &Expr) -> Option<&str> {
    match head {
        Expr::Const { name, levels } if levels.is_empty() => Some(name.as_str()),
        _ => None,
    }
}

fn bitblast_bool_binary_operator(name: &str) -> Option<BitblastBinaryOp> {
    match name {
        "Bool.and" | "and" => Some(BitblastBinaryOp::And),
        "Bool.or" | "or" => Some(BitblastBinaryOp::Or),
        "Bool.xor" => Some(BitblastBinaryOp::Xor),
        "Bool.iff" => Some(BitblastBinaryOp::Iff),
        "Bool.implies" | "implies" => Some(BitblastBinaryOp::Implies),
        _ => None,
    }
}

fn bitblast_bitvector_binary_operator(name: &str) -> Option<BitblastBinaryOp> {
    match name {
        "BitVector.and" | "BitVec.and" => Some(BitblastBinaryOp::BvAnd),
        "BitVector.or" | "BitVec.or" => Some(BitblastBinaryOp::BvOr),
        "BitVector.xor" | "BitVec.xor" => Some(BitblastBinaryOp::BvXor),
        _ => None,
    }
}

fn bitblast_local_index_for_bvar(
    context_len: usize,
    de_bruijn_index: u32,
) -> Result<usize, SolverContractError> {
    let index = de_bruijn_index as usize;
    if index >= context_len {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "de Bruijn index outside bitblast local context",
        });
    }
    Ok(context_len - 1 - index)
}

fn bitblast_bvar_for_local(
    context_len: usize,
    local_index: usize,
) -> Result<Expr, SolverContractError> {
    if local_index >= context_len {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast local index outside local context",
        });
    }
    let index = context_len - 1 - local_index;
    let index = u32::try_from(index).map_err(|_| SolverContractError::ResourceLimitExceeded {
        field: SolverResourceField::InputNodes,
        limit: u32::MAX as u64,
        actual: index as u64,
    })?;
    Ok(Expr::bvar(index))
}

fn bitblast_remap_reflected(
    expr: &ParsedBitblastReflectedExpr,
    local_to_ordinal: &BTreeMap<usize, u64>,
) -> Result<BitblastReflectedExpr, SolverContractError> {
    match expr {
        ParsedBitblastReflectedExpr::BoolConstant {
            value,
            source_core_expr_hash,
        } => Ok(BitblastReflectedExpr::BoolConstant {
            value: *value,
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedBitblastReflectedExpr::Variable {
            local_index,
            sort,
            source_core_expr_hash,
        } => {
            let Some(variable_ordinal) = local_to_ordinal.get(local_index) else {
                return Err(SolverContractError::UnsupportedBitblastFragment {
                    reason: "bitblast variable missing from variable map",
                });
            };
            Ok(BitblastReflectedExpr::Variable {
                variable_ordinal: *variable_ordinal,
                sort: sort.clone(),
                source_core_expr_hash: *source_core_expr_hash,
            })
        }
        ParsedBitblastReflectedExpr::Unary {
            op,
            arg,
            result_sort,
            source_core_expr_hash,
        } => Ok(BitblastReflectedExpr::Unary {
            op: *op,
            arg: Box::new(bitblast_remap_reflected(arg, local_to_ordinal)?),
            result_sort: result_sort.clone(),
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedBitblastReflectedExpr::Binary {
            op,
            lhs,
            rhs,
            result_sort,
            source_core_expr_hash,
        } => Ok(BitblastReflectedExpr::Binary {
            op: *op,
            lhs: Box::new(bitblast_remap_reflected(lhs, local_to_ordinal)?),
            rhs: Box::new(bitblast_remap_reflected(rhs, local_to_ordinal)?),
            result_sort: result_sort.clone(),
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedBitblastReflectedExpr::Equal {
            sort,
            lhs,
            rhs,
            source_core_expr_hash,
        } => Ok(BitblastReflectedExpr::Equal {
            sort: sort.clone(),
            lhs: Box::new(bitblast_remap_reflected(lhs, local_to_ordinal)?),
            rhs: Box::new(bitblast_remap_reflected(rhs, local_to_ordinal)?),
            source_core_expr_hash: *source_core_expr_hash,
        }),
    }
}

fn bitblast_require_parsed_bitvector_sort(
    expr: &ParsedBitblastReflectedExpr,
) -> Result<BitblastSort, SolverContractError> {
    let sort = bitblast_parsed_expr_sort(expr)?;
    match sort {
        BitblastSort::BitVector { .. } => Ok(sort),
        BitblastSort::Bool => Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "expected BitVector expression",
        }),
    }
}

fn bitblast_require_parsed_sort(
    expr: &ParsedBitblastReflectedExpr,
    expected: &BitblastSort,
) -> Result<(), SolverContractError> {
    let actual = bitblast_parsed_expr_sort(expr)?;
    bitblast_require_sort_match(expected, &actual)
}

fn bitblast_require_sort_match(
    expected: &BitblastSort,
    actual: &BitblastSort,
) -> Result<(), SolverContractError> {
    if expected == actual {
        return Ok(());
    }
    match (expected, actual) {
        (
            BitblastSort::BitVector { width: expected },
            BitblastSort::BitVector { width: actual },
        ) => Err(SolverContractError::BitblastWidthMismatch {
            expected_width: *expected,
            actual_width: *actual,
        }),
        _ => Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast expression sort mismatch",
        }),
    }
}

fn bitblast_parsed_expr_sort(
    expr: &ParsedBitblastReflectedExpr,
) -> Result<BitblastSort, SolverContractError> {
    match expr {
        ParsedBitblastReflectedExpr::BoolConstant { .. } => Ok(BitblastSort::Bool),
        ParsedBitblastReflectedExpr::Variable { sort, .. }
        | ParsedBitblastReflectedExpr::Unary {
            result_sort: sort, ..
        }
        | ParsedBitblastReflectedExpr::Binary {
            result_sort: sort, ..
        } => Ok(sort.clone()),
        ParsedBitblastReflectedExpr::Equal { .. } => Ok(BitblastSort::Bool),
    }
}

fn bitblast_reflected_expr_sort(
    expr: &BitblastReflectedExpr,
) -> Result<BitblastSort, SolverContractError> {
    match expr {
        BitblastReflectedExpr::BoolConstant { .. } => Ok(BitblastSort::Bool),
        BitblastReflectedExpr::Variable { sort, .. }
        | BitblastReflectedExpr::Unary {
            result_sort: sort, ..
        }
        | BitblastReflectedExpr::Binary {
            result_sort: sort, ..
        } => Ok(sort.clone()),
        BitblastReflectedExpr::Equal { .. } => Ok(BitblastSort::Bool),
    }
}

fn bitblast_single_bool_literal(
    bits: &EncodedBitblastBits,
) -> Result<BitblastCnfLiteral, SolverContractError> {
    if bits.sort == BitblastSort::Bool
        && bits.literals.len() == 1
        && bits.literal_node_ids.len() == 1
    {
        Ok(bits.literals[0])
    } else {
        Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "expected one Bool literal",
        })
    }
}

fn bitblast_variable_map_from_variables(
    variables: &[BitblastVariable],
) -> Result<Vec<BitblastVariableMapEntry>, SolverContractError> {
    let mut bit_offset = 0u64;
    let mut entries = Vec::with_capacity(variables.len());
    for variable in variables {
        let bit_width = variable.sort.width_bits();
        if bit_width == 0 {
            return Err(SolverContractError::UnsupportedBitblastFragment {
                reason: "bitblast variable width must be nonzero",
            });
        }
        let tseitin_variable_start = bit_offset.saturating_add(1);
        entries.push(BitblastVariableMapEntry {
            variable_ordinal: variable.ordinal,
            sort: variable.sort.clone(),
            source_core_expr_hash: variable.source_core_expr_hash,
            type_hash: variable.type_hash,
            bit_offset,
            bit_width,
            tseitin_variable_start,
            cnf_literal_start: tseitin_variable_start,
        });
        bit_offset = bit_offset.saturating_add(bit_width);
    }
    Ok(entries)
}

fn bitblast_semantic_plan_for_encoding(
    operation_profile: BitblastOperationProfile,
    backend_profile: BitblastBackendProfile,
    root_hash: Hash,
    variable_map_hash: Hash,
    circuit_hash: Hash,
    clause_count: u64,
) -> Result<BitblastSemanticPlan, SolverContractError> {
    let cnf_shape_hash = bitblast_cnf_shape_hash(circuit_hash, variable_map_hash, clause_count);
    Ok(BitblastSemanticPlan {
        operation_profile,
        backend_profile,
        root_reflected_expr_hash: root_hash,
        variable_map_hash,
        circuit_hash,
        steps: vec![
            BitblastSemanticStep {
                ordinal: 0,
                kind: BitblastSemanticStepKind::ReflectInputAst,
                input_hash: root_hash,
                output_hash: root_hash,
            },
            BitblastSemanticStep {
                ordinal: 1,
                kind: BitblastSemanticStepKind::BuildVariableMap,
                input_hash: root_hash,
                output_hash: variable_map_hash,
            },
            BitblastSemanticStep {
                ordinal: 2,
                kind: BitblastSemanticStepKind::TranslateAstToCircuit,
                input_hash: root_hash,
                output_hash: circuit_hash,
            },
            BitblastSemanticStep {
                ordinal: 3,
                kind: BitblastSemanticStepKind::TranslateCircuitToCnf,
                input_hash: circuit_hash,
                output_hash: cnf_shape_hash,
            },
            BitblastSemanticStep {
                ordinal: 4,
                kind: BitblastSemanticStepKind::AssertOutputLiteral,
                input_hash: cnf_shape_hash,
                output_hash: hash_u64(clause_count),
            },
        ],
    })
}

fn bitblast_cnf_shape_hash(circuit_hash: Hash, variable_map_hash: Hash, clause_count: u64) -> Hash {
    let mut out = Vec::new();
    encode_hash_to(&mut out, &circuit_hash);
    encode_hash_to(&mut out, &variable_map_hash);
    encode_u64_to(&mut out, clause_count);
    hash_with_domain("npa.solver.bitblast.cnf-shape.v1", &out)
}

fn bitblast_operation_profile_for_root(
    root: &BitblastReflectedExpr,
) -> Result<BitblastOperationProfile, SolverContractError> {
    let mut has_bool = false;
    let mut has_bv = false;
    bitblast_collect_profile_flags(root, &mut has_bool, &mut has_bv)?;
    Ok(match (has_bool, has_bv) {
        (true, true) => BitblastOperationProfile::MixedBoolBitVectorV1,
        (false, true) => BitblastOperationProfile::FixedWidthBitVectorV1,
        _ => BitblastOperationProfile::BoolFormulaV1,
    })
}

fn bitblast_collect_profile_flags(
    expr: &BitblastReflectedExpr,
    has_bool: &mut bool,
    has_bv: &mut bool,
) -> Result<(), SolverContractError> {
    match expr {
        BitblastReflectedExpr::BoolConstant { .. } => *has_bool = true,
        BitblastReflectedExpr::Variable { sort, .. } => match sort {
            BitblastSort::Bool => *has_bool = true,
            BitblastSort::BitVector { .. } => *has_bv = true,
        },
        BitblastReflectedExpr::Unary {
            op,
            arg,
            result_sort,
            ..
        } => {
            match op {
                BitblastUnaryOp::Not => *has_bool = true,
                BitblastUnaryOp::BvNot => *has_bv = true,
            }
            if matches!(result_sort, BitblastSort::Bool) {
                *has_bool = true;
            }
            bitblast_collect_profile_flags(arg, has_bool, has_bv)?;
        }
        BitblastReflectedExpr::Binary {
            op,
            lhs,
            rhs,
            result_sort,
            ..
        } => {
            match op {
                BitblastBinaryOp::And
                | BitblastBinaryOp::Or
                | BitblastBinaryOp::Xor
                | BitblastBinaryOp::Iff
                | BitblastBinaryOp::Implies => *has_bool = true,
                BitblastBinaryOp::BvAnd | BitblastBinaryOp::BvOr | BitblastBinaryOp::BvXor => {
                    *has_bv = true
                }
            }
            if matches!(result_sort, BitblastSort::Bool) {
                *has_bool = true;
            }
            bitblast_collect_profile_flags(lhs, has_bool, has_bv)?;
            bitblast_collect_profile_flags(rhs, has_bool, has_bv)?;
        }
        BitblastReflectedExpr::Equal { sort, lhs, rhs, .. } => {
            *has_bool = true;
            if matches!(sort, BitblastSort::BitVector { .. }) {
                *has_bv = true;
            }
            bitblast_collect_profile_flags(lhs, has_bool, has_bv)?;
            bitblast_collect_profile_flags(rhs, has_bool, has_bv)?;
        }
    }
    Ok(())
}

fn bitblast_expr_node_count(expr: &Expr, limit: u64) -> Result<u64, SolverContractError> {
    fn visit(expr: &Expr, count: &mut u64, limit: u64) -> Result<(), SolverContractError> {
        *count = (*count).saturating_add(1);
        if *count > limit {
            return Err(SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                limit,
                actual: *count,
            });
        }
        match expr {
            Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => Ok(()),
            Expr::App(fun, arg) => {
                visit(fun, count, limit)?;
                visit(arg, count, limit)
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                visit(ty, count, limit)?;
                visit(body, count, limit)
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                visit(ty, count, limit)?;
                visit(value, count, limit)?;
                visit(body, count, limit)
            }
        }
    }
    let mut count = 0;
    visit(expr, &mut count, limit)?;
    Ok(count)
}

fn bitblast_reflected_expr_node_count(expr: &BitblastReflectedExpr) -> u64 {
    match expr {
        BitblastReflectedExpr::BoolConstant { .. } | BitblastReflectedExpr::Variable { .. } => 1,
        BitblastReflectedExpr::Unary { arg, .. } => 1 + bitblast_reflected_expr_node_count(arg),
        BitblastReflectedExpr::Binary { lhs, rhs, .. }
        | BitblastReflectedExpr::Equal { lhs, rhs, .. } => {
            1 + bitblast_reflected_expr_node_count(lhs) + bitblast_reflected_expr_node_count(rhs)
        }
    }
}

fn validate_bitblast_variables(variables: &[BitblastVariable]) -> Result<(), SolverContractError> {
    let mut last_local_index = None;
    let mut seen_names = BTreeSet::new();
    for (index, variable) in variables.iter().enumerate() {
        let expected = index as u64;
        if variable.ordinal != expected {
            return Err(SolverContractError::NonCanonicalBitblastVariableOrder {
                expected_ordinal: expected,
                actual_ordinal: variable.ordinal,
            });
        }
        if let Some(previous) = last_local_index {
            if variable.local_index <= previous {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "bitblast_variable_local_order",
                });
            }
        }
        last_local_index = Some(variable.local_index);
        if variable.name.is_empty() || !seen_names.insert(variable.name.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "bitblast_variable",
                identifier: variable.name.clone(),
            });
        }
        validate_bitblast_sort(&variable.sort)?;
        if is_zero_hash(&variable.source_core_expr_hash) || is_zero_hash(&variable.type_hash) {
            return Err(SolverContractError::MissingBitblastEvidence {
                field: "bitblast_variable_identity",
            });
        }
    }
    Ok(())
}

fn validate_bitblast_sort(sort: &BitblastSort) -> Result<(), SolverContractError> {
    match sort {
        BitblastSort::Bool => Ok(()),
        BitblastSort::BitVector { width } if *width > 0 => Ok(()),
        BitblastSort::BitVector { .. } => Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "zero-width BitVector is not supported",
        }),
    }
}

fn validate_bitblast_reflected_expr_shape(
    expr: &BitblastReflectedExpr,
    variable_count: Option<usize>,
) -> Result<(), SolverContractError> {
    match expr {
        BitblastReflectedExpr::BoolConstant {
            source_core_expr_hash,
            ..
        }
        | BitblastReflectedExpr::Variable {
            source_core_expr_hash,
            ..
        }
        | BitblastReflectedExpr::Unary {
            source_core_expr_hash,
            ..
        }
        | BitblastReflectedExpr::Binary {
            source_core_expr_hash,
            ..
        }
        | BitblastReflectedExpr::Equal {
            source_core_expr_hash,
            ..
        } if is_zero_hash(source_core_expr_hash) => {
            return Err(SolverContractError::MissingBitblastEvidence {
                field: "bitblast_reflected_expr_source_hash",
            });
        }
        _ => {}
    }
    match expr {
        BitblastReflectedExpr::BoolConstant { .. } => Ok(()),
        BitblastReflectedExpr::Variable {
            variable_ordinal,
            sort,
            ..
        } => {
            validate_bitblast_sort(sort)?;
            if let Some(variable_count) = variable_count {
                if (*variable_ordinal as usize) >= variable_count {
                    return Err(SolverContractError::NonCanonicalPayloadBytes {
                        field: "bitblast_variable_ordinal",
                    });
                }
            }
            Ok(())
        }
        BitblastReflectedExpr::Unary {
            op,
            arg,
            result_sort,
            ..
        } => {
            validate_bitblast_reflected_expr_shape(arg, variable_count)?;
            validate_bitblast_sort(result_sort)?;
            let arg_sort = bitblast_reflected_expr_sort(arg)?;
            match op {
                BitblastUnaryOp::Not => {
                    bitblast_require_sort_match(&BitblastSort::Bool, &arg_sort)?;
                    bitblast_require_sort_match(&BitblastSort::Bool, result_sort)
                }
                BitblastUnaryOp::BvNot => {
                    if matches!(arg_sort, BitblastSort::BitVector { .. }) {
                        bitblast_require_sort_match(result_sort, &arg_sort)
                    } else {
                        Err(SolverContractError::UnsupportedBitblastFragment {
                            reason: "BitVector.not argument must be BitVector",
                        })
                    }
                }
            }
        }
        BitblastReflectedExpr::Binary {
            op,
            lhs,
            rhs,
            result_sort,
            ..
        } => {
            validate_bitblast_reflected_expr_shape(lhs, variable_count)?;
            validate_bitblast_reflected_expr_shape(rhs, variable_count)?;
            validate_bitblast_sort(result_sort)?;
            let lhs_sort = bitblast_reflected_expr_sort(lhs)?;
            let rhs_sort = bitblast_reflected_expr_sort(rhs)?;
            match op {
                BitblastBinaryOp::And
                | BitblastBinaryOp::Or
                | BitblastBinaryOp::Xor
                | BitblastBinaryOp::Iff
                | BitblastBinaryOp::Implies => {
                    bitblast_require_sort_match(&BitblastSort::Bool, &lhs_sort)?;
                    bitblast_require_sort_match(&BitblastSort::Bool, &rhs_sort)?;
                    bitblast_require_sort_match(&BitblastSort::Bool, result_sort)
                }
                BitblastBinaryOp::BvAnd | BitblastBinaryOp::BvOr | BitblastBinaryOp::BvXor => {
                    if !matches!(lhs_sort, BitblastSort::BitVector { .. }) {
                        return Err(SolverContractError::UnsupportedBitblastFragment {
                            reason: "BitVector binary argument must be BitVector",
                        });
                    }
                    bitblast_require_sort_match(&lhs_sort, &rhs_sort)?;
                    bitblast_require_sort_match(&lhs_sort, result_sort)
                }
            }
        }
        BitblastReflectedExpr::Equal { sort, lhs, rhs, .. } => {
            validate_bitblast_sort(sort)?;
            validate_bitblast_reflected_expr_shape(lhs, variable_count)?;
            validate_bitblast_reflected_expr_shape(rhs, variable_count)?;
            bitblast_require_sort_match(sort, &bitblast_reflected_expr_sort(lhs)?)?;
            bitblast_require_sort_match(sort, &bitblast_reflected_expr_sort(rhs)?)
        }
    }
}

fn validate_bitblast_reflected_expr_for_variables(
    expr: &BitblastReflectedExpr,
    variables: &[BitblastVariable],
) -> Result<(), SolverContractError> {
    match expr {
        BitblastReflectedExpr::BoolConstant { .. } => Ok(()),
        BitblastReflectedExpr::Variable {
            variable_ordinal,
            sort,
            source_core_expr_hash,
        } => {
            let Some(variable) = variables.get(*variable_ordinal as usize) else {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "bitblast_variable_ordinal",
                });
            };
            if variable.ordinal != *variable_ordinal {
                return Err(SolverContractError::NonCanonicalBitblastVariableOrder {
                    expected_ordinal: *variable_ordinal,
                    actual_ordinal: variable.ordinal,
                });
            }
            if variable.sort != *sort {
                return Err(SolverContractError::RequestMetadataMismatch {
                    field: "bitblast_variable_sort",
                });
            }
            require_bitblast_hash(
                "bitblast_variable_source_core_expr_hash",
                *source_core_expr_hash,
                variable.source_core_expr_hash,
            )
        }
        BitblastReflectedExpr::Unary { arg, .. } => {
            validate_bitblast_reflected_expr_for_variables(arg, variables)
        }
        BitblastReflectedExpr::Binary { lhs, rhs, .. }
        | BitblastReflectedExpr::Equal { lhs, rhs, .. } => {
            validate_bitblast_reflected_expr_for_variables(lhs, variables)?;
            validate_bitblast_reflected_expr_for_variables(rhs, variables)
        }
    }
}

fn validate_bitblast_variable_map_shape(
    entries: &[BitblastVariableMapEntry],
) -> Result<(), SolverContractError> {
    let mut expected_offset = 0u64;
    for (index, entry) in entries.iter().enumerate() {
        let expected = index as u64;
        if entry.variable_ordinal != expected {
            return Err(SolverContractError::NonCanonicalBitblastVariableMap {
                expected_ordinal: expected,
                actual_ordinal: entry.variable_ordinal,
            });
        }
        validate_bitblast_sort(&entry.sort)?;
        if entry.bit_width != entry.sort.width_bits() || entry.bit_width == 0 {
            return Err(SolverContractError::BitblastWidthMismatch {
                expected_width: entry.sort.width_bits(),
                actual_width: entry.bit_width,
            });
        }
        if entry.bit_offset != expected_offset {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_variable_map_bit_offset",
            });
        }
        let expected_start = expected_offset.saturating_add(1);
        if entry.tseitin_variable_start != expected_start
            || entry.cnf_literal_start != expected_start
        {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_variable_map_tseitin_start",
            });
        }
        if is_zero_hash(&entry.source_core_expr_hash) || is_zero_hash(&entry.type_hash) {
            return Err(SolverContractError::MissingBitblastEvidence {
                field: "bitblast_variable_map_identity",
            });
        }
        expected_offset = expected_offset.saturating_add(entry.bit_width);
    }
    Ok(())
}

fn validate_bitblast_variable_map_for_variables(
    variables: &[BitblastVariable],
    entries: &[BitblastVariableMapEntry],
) -> Result<(), SolverContractError> {
    validate_bitblast_variable_map_shape(entries)?;
    if variables.len() != entries.len() {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_variable_map_entry_count",
        });
    }
    for (variable, entry) in variables.iter().zip(entries) {
        if variable.ordinal != entry.variable_ordinal {
            return Err(SolverContractError::NonCanonicalBitblastVariableMap {
                expected_ordinal: variable.ordinal,
                actual_ordinal: entry.variable_ordinal,
            });
        }
        if variable.sort != entry.sort {
            return Err(SolverContractError::BitblastWidthMismatch {
                expected_width: variable.sort.width_bits(),
                actual_width: entry.sort.width_bits(),
            });
        }
        require_bitblast_hash(
            "bitblast_variable_map_source_core_expr_hash",
            entry.source_core_expr_hash,
            variable.source_core_expr_hash,
        )?;
        require_bitblast_hash(
            "bitblast_variable_map_type_hash",
            entry.type_hash,
            variable.type_hash,
        )?;
    }
    Ok(())
}

fn validate_bitblast_circuit_shape(
    nodes: &[BitblastCircuitNode],
) -> Result<(), SolverContractError> {
    for (index, node) in nodes.iter().enumerate() {
        let expected = index as u64;
        if node.node_id != expected {
            return Err(SolverContractError::NonCanonicalBitblastCircuitNode {
                expected_node_id: expected,
                actual_node_id: node.node_id,
            });
        }
        validate_bitblast_sort(&node.result_sort)?;
        if node.output_width == 0 || node.output_width != node.result_sort.width_bits() {
            return Err(SolverContractError::BitblastWidthMismatch {
                expected_width: node.result_sort.width_bits(),
                actual_width: node.output_width,
            });
        }
        if node.output_tseitin_start == 0 || is_zero_hash(&node.source_reflected_expr_hash) {
            return Err(SolverContractError::MissingBitblastEvidence {
                field: "bitblast_circuit_node_identity",
            });
        }
        if node
            .input_node_ids
            .iter()
            .any(|input| *input >= node.node_id)
        {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_circuit_input_node_order",
            });
        }
    }
    Ok(())
}

fn validate_bitblast_semantic_plan_shape(
    plan: &BitblastSemanticPlan,
) -> Result<(), SolverContractError> {
    for (field, value) in [
        (
            "bitblast_plan_root_reflected_expr_hash",
            plan.root_reflected_expr_hash,
        ),
        ("bitblast_plan_variable_map_hash", plan.variable_map_hash),
        ("bitblast_plan_circuit_hash", plan.circuit_hash),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingBitblastEvidence { field });
        }
    }
    let expected_kinds = [
        BitblastSemanticStepKind::ReflectInputAst,
        BitblastSemanticStepKind::BuildVariableMap,
        BitblastSemanticStepKind::TranslateAstToCircuit,
        BitblastSemanticStepKind::TranslateCircuitToCnf,
        BitblastSemanticStepKind::AssertOutputLiteral,
    ];
    if plan.steps.len() != expected_kinds.len() {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_semantic_plan_steps",
        });
    }
    for (index, (step, expected_kind)) in plan.steps.iter().zip(expected_kinds).enumerate() {
        if step.ordinal != index as u64 || step.kind != expected_kind {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_semantic_step_order",
            });
        }
        if is_zero_hash(&step.input_hash) || is_zero_hash(&step.output_hash) {
            return Err(SolverContractError::MissingBitblastEvidence {
                field: "bitblast_semantic_step_hash",
            });
        }
    }
    Ok(())
}

fn validate_bitblast_cnf_artifact_shape(
    artifact: &BitblastCnfArtifact,
) -> Result<(), SolverContractError> {
    if artifact.backend_profile != BitblastBackendProfile::CnfTseitinV1 {
        return Err(SolverContractError::UnsupportedBitblastFragment {
            reason: "bitblast CNF artifact must use the CNF/Tseitin backend profile",
        });
    }
    for (field, value) in [
        (
            "bitblast_cnf_root_reflected_expr_hash",
            artifact.root_reflected_expr_hash,
        ),
        ("bitblast_cnf_variable_map_hash", artifact.variable_map_hash),
        ("bitblast_cnf_circuit_hash", artifact.circuit_hash),
        (
            "bitblast_cnf_semantic_plan_hash",
            artifact.semantic_plan_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingBitblastEvidence { field });
        }
    }
    if artifact.variable_count == 0
        || artifact.output_literal.variable == 0
        || artifact.output_literal.variable > artifact.variable_count
    {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_cnf_output_literal",
        });
    }
    for (index, clause) in artifact.clauses.iter().enumerate() {
        let expected = index as u64;
        if clause.ordinal != expected {
            return Err(SolverContractError::NonCanonicalBitblastClause {
                expected_ordinal: expected,
                actual_ordinal: clause.ordinal,
            });
        }
        if clause.literals.is_empty() || is_zero_hash(&clause.source_reflected_expr_hash) {
            return Err(SolverContractError::MissingBitblastEvidence {
                field: "bitblast_cnf_clause",
            });
        }
        for literal in &clause.literals {
            if literal.variable == 0 || literal.variable > artifact.variable_count {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "bitblast_cnf_literal_variable",
                });
            }
        }
    }
    let Some(output_assertion) = artifact.clauses.last() else {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_cnf_output_assertion",
        });
    };
    if output_assertion.role != BitblastClauseRole::OutputAssertion
        || output_assertion.literals.as_slice() != [artifact.output_literal]
    {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "bitblast_cnf_output_assertion",
        });
    }
    require_bitblast_hash(
        "bitblast_cnf_output_assertion_hash",
        output_assertion.source_reflected_expr_hash,
        artifact.root_reflected_expr_hash,
    )?;
    Ok(())
}

fn bitblast_reconstruction_steps_for_hashes(
    root_hash: Hash,
    variable_map_hash: Hash,
    circuit_hash: Hash,
    semantic_plan_hash: Hash,
    cnf_artifact_hash: Hash,
    final_goal_hash: Hash,
) -> Vec<BitblastReconstructionStep> {
    [
        (
            BitblastReconstructionStepKind::ExpressionToCircuitSemantics,
            root_hash,
            circuit_hash,
        ),
        (
            BitblastReconstructionStepKind::VariableMapCorrectness,
            root_hash,
            variable_map_hash,
        ),
        (
            BitblastReconstructionStepKind::TseitinEquisatisfiability,
            circuit_hash,
            cnf_artifact_hash,
        ),
        (
            BitblastReconstructionStepKind::CnfOutputAssertion,
            semantic_plan_hash,
            cnf_artifact_hash,
        ),
        (
            BitblastReconstructionStepKind::CnfUnsatImpliesOriginalGoal,
            cnf_artifact_hash,
            final_goal_hash,
        ),
    ]
    .into_iter()
    .enumerate()
    .map(
        |(ordinal, (kind, input_hash, output_hash))| BitblastReconstructionStep {
            ordinal: ordinal as u64,
            kind,
            input_hash,
            output_hash,
            checked_rule_hash: bitblast_reconstruction_rule_hash(kind, input_hash, output_hash),
        },
    )
    .collect()
}

fn bitblast_reconstruction_rule_hash(
    kind: BitblastReconstructionStepKind,
    input_hash: Hash,
    output_hash: Hash,
) -> Hash {
    let mut out = Vec::new();
    out.push(kind.tag());
    encode_hash_to(&mut out, &input_hash);
    encode_hash_to(&mut out, &output_hash);
    hash_with_domain(BITBLAST_RECONSTRUCTION_STEP_HASH_TAG, &out)
}

fn validate_bitblast_semantic_proof_artifact_shape(
    artifact: &BitblastSemanticProofArtifact,
) -> Result<(), SolverContractError> {
    if artifact.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "bitblast_semantic_proof_version",
            tag: artifact.version.as_str().to_owned(),
        });
    }
    for (field, value) in [
        (
            "bitblast_semantic_proof_request_hash",
            artifact.request_hash,
        ),
        (
            "bitblast_semantic_proof_encoded_problem_hash",
            artifact.encoded_problem_hash,
        ),
        (
            "bitblast_semantic_proof_root_hash",
            artifact.root_reflected_expr_hash,
        ),
        (
            "bitblast_semantic_proof_variable_map_hash",
            artifact.variable_map_hash,
        ),
        (
            "bitblast_semantic_proof_circuit_hash",
            artifact.circuit_hash,
        ),
        (
            "bitblast_semantic_proof_semantic_plan_hash",
            artifact.semantic_plan_hash,
        ),
        (
            "bitblast_semantic_proof_cnf_artifact_hash",
            artifact.cnf_artifact_hash,
        ),
        (
            "bitblast_semantic_proof_final_goal_hash",
            artifact.final_goal_hash,
        ),
        (
            "bitblast_semantic_proof_environment_hash",
            artifact.proof_identity.environment_hash,
        ),
        (
            "bitblast_semantic_proof_term_hash",
            artifact.proof_identity.proof_term_hash,
        ),
        (
            "bitblast_semantic_proof_type_hash",
            artifact.proof_identity.proof_type_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingBitblastEvidence { field });
        }
    }
    let expected = bitblast_reconstruction_steps_for_hashes(
        artifact.root_reflected_expr_hash,
        artifact.variable_map_hash,
        artifact.circuit_hash,
        artifact.semantic_plan_hash,
        artifact.cnf_artifact_hash,
        artifact.final_goal_hash,
    );
    if artifact.steps.len() != expected.len() {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_semantic_proof_steps",
        });
    }
    for (actual, expected) in artifact.steps.iter().zip(expected) {
        if actual.ordinal != expected.ordinal
            || actual.kind != expected.kind
            || actual.input_hash != expected.input_hash
            || actual.output_hash != expected.output_hash
            || actual.checked_rule_hash != expected.checked_rule_hash
        {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_semantic_proof_step",
            });
        }
    }
    if artifact.generated_term_nodes < artifact.steps.len() as u64 {
        return Err(SolverContractError::ReconstructionTermTooLarge {
            limit_nodes: artifact.generated_term_nodes,
            actual_nodes: artifact.steps.len() as u64,
        });
    }
    if artifact.proof_bytes == 0 {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_semantic_proof_bytes",
        });
    }
    if artifact.proof_steps < artifact.steps.len() as u64 {
        return Err(SolverContractError::ProofSearchExhausted {
            field: SolverResourceField::ProofSteps,
            limit: artifact.proof_steps,
            actual: artifact.steps.len() as u64,
        });
    }
    Ok(())
}

fn validate_bitblast_sat_handoff_shape(
    handoff: &BitblastSatHandoff,
) -> Result<(), SolverContractError> {
    if handoff.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "bitblast_sat_handoff_version",
            tag: handoff.version.as_str().to_owned(),
        });
    }
    for (field, value) in [
        ("bitblast_sat_handoff_request_hash", handoff.request_hash),
        ("bitblast_sat_handoff_policy_hash", handoff.policy_hash),
        (
            "bitblast_sat_handoff_encoded_problem_hash",
            handoff.encoded_problem_hash,
        ),
        (
            "bitblast_sat_handoff_root_hash",
            handoff.root_reflected_expr_hash,
        ),
        (
            "bitblast_sat_handoff_variable_map_hash",
            handoff.variable_map_hash,
        ),
        (
            "bitblast_sat_handoff_cnf_artifact_hash",
            handoff.cnf_artifact_hash,
        ),
        (
            "bitblast_sat_handoff_canonical_cnf_hash",
            handoff.canonical_cnf_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingBitblastEvidence { field });
        }
    }
    if handoff.canonical_cnf_bytes.is_empty()
        || handoff.cnf_variable_count == 0
        || handoff.cnf_clause_count == 0
    {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_sat_handoff_cnf",
        });
    }
    Ok(())
}

fn validate_bitblast_sat_model_shape(
    model: &BitblastSatModelArtifact,
) -> Result<(), SolverContractError> {
    if model.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "bitblast_sat_model_version",
            tag: model.version.as_str().to_owned(),
        });
    }
    for (field, value) in [
        ("bitblast_sat_model_request_hash", model.request_hash),
        (
            "bitblast_sat_model_encoded_problem_hash",
            model.encoded_problem_hash,
        ),
        (
            "bitblast_sat_model_cnf_artifact_hash",
            model.cnf_artifact_hash,
        ),
        (
            "bitblast_sat_model_variable_map_hash",
            model.variable_map_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingBitblastEvidence { field });
        }
    }
    if model.assignments.is_empty() {
        return Err(SolverContractError::MissingBitblastEvidence {
            field: "bitblast_sat_model_assignments",
        });
    }
    Ok(())
}

fn validate_bitblast_lrat_soundness_bridge_artifact_shape(
    artifact: &BitblastLratSoundnessBridgeArtifact,
) -> Result<(), SolverContractError> {
    if artifact.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "bitblast_lrat_bridge_version",
            tag: artifact.version.as_str().to_owned(),
        });
    }
    if artifact.certificate_format != SolverCertificateFormat::LratV1 {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        });
    }
    for (field, value) in [
        ("bitblast_lrat_request_hash", artifact.request_hash),
        ("bitblast_lrat_policy_hash", artifact.policy_hash),
        (
            "bitblast_lrat_checker_request_hash",
            artifact.lrat_request_hash,
        ),
        (
            "bitblast_lrat_checker_policy_hash",
            artifact.lrat_policy_hash,
        ),
        (
            "bitblast_lrat_encoded_problem_hash",
            artifact.encoded_problem_hash,
        ),
        ("bitblast_lrat_root_hash", artifact.root_reflected_expr_hash),
        (
            "bitblast_lrat_variable_map_hash",
            artifact.variable_map_hash,
        ),
        (
            "bitblast_lrat_cnf_artifact_hash",
            artifact.cnf_artifact_hash,
        ),
        (
            "bitblast_lrat_canonical_cnf_hash",
            artifact.canonical_cnf_hash,
        ),
        ("bitblast_lrat_cnf_hash", artifact.lrat_cnf_hash),
        (
            "bitblast_lrat_certificate_hash",
            artifact.lrat_certificate_hash,
        ),
        ("bitblast_lrat_payload_hash", artifact.lrat_payload_hash),
        (
            "bitblast_lrat_payload_ref_hash",
            artifact.lrat_proof_payload_ref_hash,
        ),
        (
            "bitblast_lrat_check_artifact_hash",
            artifact.lrat_check_artifact_hash,
        ),
        (
            "bitblast_lrat_cnf_unsat_bridge_hash",
            artifact.lrat_cnf_unsat_bridge_hash,
        ),
        (
            "bitblast_lrat_cnf_unsat_theorem_hash",
            artifact.cnf_unsat_theorem_hash,
        ),
        (
            "bitblast_lrat_semantic_proof_hash",
            artifact.semantic_proof_artifact_hash,
        ),
        ("bitblast_lrat_final_goal_hash", artifact.final_goal_hash),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingBitblastEvidence { field });
        }
    }
    Ok(())
}

fn validate_bitblast_lrat_request_pair(
    bitblast_request: &SolverRequest,
    lrat_request: &SolverRequest,
) -> Result<(), SolverContractError> {
    validate_bitblast_solver_request(bitblast_request)?;
    validate_lrat_solver_request(lrat_request)?;
    if bitblast_request.goal_identity.goal_hash != lrat_request.goal_identity.goal_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "bitblast_lrat_goal_hash",
            expected: bitblast_request.goal_identity.goal_hash,
            actual: lrat_request.goal_identity.goal_hash,
        });
    }
    if bitblast_request.goal_identity.target_hash != lrat_request.goal_identity.target_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "bitblast_lrat_target_hash",
            expected: bitblast_request.goal_identity.target_hash,
            actual: lrat_request.goal_identity.target_hash,
        });
    }
    if bitblast_request.local_context_hash != lrat_request.local_context_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "bitblast_lrat_local_context_hash",
            expected: bitblast_request.local_context_hash,
            actual: lrat_request.local_context_hash,
        });
    }
    if bitblast_request.environment_hash != lrat_request.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "bitblast_lrat_environment_hash",
            expected: bitblast_request.environment_hash,
            actual: lrat_request.environment_hash,
        });
    }
    Ok(())
}

fn bitblast_model_literal_value(
    assignments: &[BitblastSatModelAssignment],
    literal: BitblastCnfLiteral,
) -> Result<bool, SolverContractError> {
    let Some(assignment) = assignments.get(literal.variable.saturating_sub(1) as usize) else {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "bitblast_sat_model_literal_variable",
        });
    };
    if assignment.cnf_variable != literal.variable {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "bitblast_sat_model_assignment_order",
        });
    }
    Ok(if literal.positive {
        assignment.value
    } else {
        !assignment.value
    })
}

fn bitblast_resource_usage_from_sat_model(
    problem: &BitblastEncodedProblem,
    model: &BitblastSatModelArtifact,
) -> Result<SolverResourceUsage, SolverContractError> {
    let model_bytes = bitblast_sat_model_canonical_bytes(model)?.len() as u64;
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: bitblast_encoded_problem_canonical_bytes(problem)?.len() as u64,
        generated_term_nodes: problem.encoded_nodes,
        cnf_variables: problem.cnf_artifact.variable_count,
        cnf_clauses: problem.cnf_artifact.clauses.len() as u64,
        solver_steps: problem.encoded_nodes,
        output_bytes: model_bytes,
        nested_solver_calls: 1,
        ..SolverResourceUsage::default()
    })
}

fn bitblast_resource_usage_from_checked_certificate(
    problem: &BitblastEncodedProblem,
    semantic_proof: &BitblastSemanticProofArtifact,
    proof_payload: &SolverProofPayloadRef,
) -> Result<SolverResourceUsage, SolverContractError> {
    let encoded_bytes = bitblast_encoded_problem_canonical_bytes(problem)?.len() as u64;
    let proof_artifact_bytes =
        bitblast_semantic_proof_artifact_canonical_bytes(semantic_proof)?.len() as u64;
    Ok(SolverResourceUsage {
        input_nodes: problem.input_nodes,
        input_bytes: encoded_bytes.saturating_add(proof_artifact_bytes),
        generated_term_nodes: semantic_proof.generated_term_nodes,
        proof_bytes: semantic_proof.proof_bytes,
        certificate_bytes: proof_payload.size_bytes,
        cnf_variables: problem.cnf_artifact.variable_count,
        cnf_clauses: problem.cnf_artifact.clauses.len() as u64,
        solver_steps: problem.encoded_nodes,
        proof_steps: semantic_proof.proof_steps,
        rule_count: semantic_proof.steps.len() as u64,
        output_bytes: proof_payload.size_bytes,
        nested_solver_calls: 1,
        ..SolverResourceUsage::default()
    })
}

fn require_bitblast_hash(
    field: &'static str,
    actual: Hash,
    expected: Hash,
) -> Result<(), SolverContractError> {
    if actual == expected {
        Ok(())
    } else {
        Err(SolverContractError::MismatchedHash {
            field,
            expected,
            actual,
        })
    }
}

fn require_lrat_bridge_hash(
    field: &'static str,
    actual: Hash,
    expected: Hash,
) -> Result<(), SolverContractError> {
    if actual == expected {
        Ok(())
    } else {
        Err(SolverContractError::MismatchedHash {
            field,
            expected,
            actual,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ParsedRingNfReflectedExpr {
    Constant {
        value: i64,
        source_core_expr_hash: Hash,
    },
    Variable {
        local_index: usize,
        source_core_expr_hash: Hash,
    },
    Add {
        args: Vec<ParsedRingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Mul {
        args: Vec<ParsedRingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Neg {
        arg: Box<ParsedRingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Sub {
        lhs: Box<ParsedRingNfReflectedExpr>,
        rhs: Box<ParsedRingNfReflectedExpr>,
        source_core_expr_hash: Hash,
    },
    Pow {
        base: Box<ParsedRingNfReflectedExpr>,
        exponent: u64,
        source_core_expr_hash: Hash,
    },
}

struct RingNfParser<'a> {
    local_context: &'a [RingNfLocalContextEntry],
    carrier_type_hash: Hash,
    coefficient_domain: RingNfCoefficientDomain,
    options: &'a RingNfNormalizationOptions,
    used_locals: BTreeSet<usize>,
}

impl RingNfParser<'_> {
    fn parse_expr(
        &mut self,
        expr: &Expr,
    ) -> Result<ParsedRingNfReflectedExpr, SolverContractError> {
        if let Some(value) = ring_nf_numeric_literal(expr) {
            self.validate_literal(value)?;
            return Ok(ParsedRingNfReflectedExpr::Constant {
                value,
                source_core_expr_hash: core_expr_hash(expr),
            });
        }
        if let Expr::BVar(index) = expr {
            let local_index = ring_nf_local_index_for_bvar(self.local_context.len(), *index)?;
            let entry = self.local_context.get(local_index).ok_or(
                SolverContractError::UnsupportedRingNfFragment {
                    reason: "de Bruijn index outside ring_nf local context",
                },
            )?;
            if core_expr_hash(&entry.ty) != self.carrier_type_hash {
                return Err(SolverContractError::UnsupportedRingNfFragment {
                    reason: "ring_nf variable type does not match the equality carrier",
                });
            }
            self.used_locals.insert(local_index);
            return Ok(ParsedRingNfReflectedExpr::Variable {
                local_index,
                source_core_expr_hash: core_expr_hash(expr),
            });
        }

        let (head, args) = collect_apps(expr);
        let Some(name) = ring_nf_head_const_name(&head) else {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "ring_nf term head is not a constant",
            });
        };
        let Some(operator) = ring_nf_arithmetic_operator(name) else {
            return Err(SolverContractError::UnsupportedRingNfOperation {
                profile: self.options.algebra_profile,
                operator: name.to_owned(),
            });
        };
        match operator {
            RingNfArithmeticOperator::Add => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedRingNfFragment {
                        reason: "ring_nf addition must have exactly two arguments",
                    });
                }
                Ok(ParsedRingNfReflectedExpr::Add {
                    args: vec![self.parse_expr(&args[0])?, self.parse_expr(&args[1])?],
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            RingNfArithmeticOperator::Mul => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedRingNfFragment {
                        reason: "ring_nf multiplication must have exactly two arguments",
                    });
                }
                Ok(ParsedRingNfReflectedExpr::Mul {
                    args: vec![self.parse_expr(&args[0])?, self.parse_expr(&args[1])?],
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            RingNfArithmeticOperator::Neg => {
                if !self.options.algebra_profile.allows_signed_coefficients() {
                    return Err(SolverContractError::UnsupportedRingNfOperation {
                        profile: self.options.algebra_profile,
                        operator: name.to_owned(),
                    });
                }
                if args.len() != 1 {
                    return Err(SolverContractError::UnsupportedRingNfFragment {
                        reason: "ring_nf negation must have exactly one argument",
                    });
                }
                Ok(ParsedRingNfReflectedExpr::Neg {
                    arg: Box::new(self.parse_expr(&args[0])?),
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            RingNfArithmeticOperator::Sub => {
                if !self.options.algebra_profile.allows_signed_coefficients() {
                    return Err(SolverContractError::UnsupportedRingNfOperation {
                        profile: self.options.algebra_profile,
                        operator: name.to_owned(),
                    });
                }
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedRingNfFragment {
                        reason: "ring_nf subtraction must have exactly two arguments",
                    });
                }
                Ok(ParsedRingNfReflectedExpr::Sub {
                    lhs: Box::new(self.parse_expr(&args[0])?),
                    rhs: Box::new(self.parse_expr(&args[1])?),
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
            RingNfArithmeticOperator::Pow => {
                if !self.options.algebra_profile.is_commutative() {
                    return Err(SolverContractError::UnsupportedRingNfOperation {
                        profile: self.options.algebra_profile,
                        operator: name.to_owned(),
                    });
                }
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedRingNfFragment {
                        reason: "ring_nf power must have base and literal exponent arguments",
                    });
                }
                let Some(exponent) = ring_nf_nonnegative_literal(&args[1]) else {
                    return Err(SolverContractError::UnsupportedRingNfFragment {
                        reason: "ring_nf exponent must be a nonnegative literal",
                    });
                };
                Ok(ParsedRingNfReflectedExpr::Pow {
                    base: Box::new(self.parse_expr(&args[0])?),
                    exponent,
                    source_core_expr_hash: core_expr_hash(expr),
                })
            }
        }
    }

    fn validate_literal(&self, value: i64) -> Result<(), SolverContractError> {
        if value < 0 && !self.options.algebra_profile.allows_signed_coefficients() {
            return Err(SolverContractError::UnsupportedRingNfOperation {
                profile: self.options.algebra_profile,
                operator: "negative-literal".to_owned(),
            });
        }
        if self.coefficient_domain == RingNfCoefficientDomain::Nat && value < 0 {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "Nat ring_nf coefficients must be nonnegative",
            });
        }
        ring_nf_check_coefficient_bound(value, self.options)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RingNfArithmeticOperator {
    Add,
    Mul,
    Neg,
    Sub,
    Pow,
}

type RingNfPolynomialMap = BTreeMap<Vec<u64>, i64>;

fn validate_ring_nf_solver_request(request: &SolverRequest) -> Result<(), SolverContractError> {
    validate_solver_request(request)?;
    if request.family != SolverFamily::Ring {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if request.fragment != SolverFragment::SemiringNormalizationV1 {
        return Err(SolverContractError::UnsupportedFragment {
            family: request.family,
            fragment: request.fragment,
        });
    }
    if request.profile != SolverProfile::ExternalSidecarV1 {
        return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
    }
    Ok(())
}

fn ring_nf_parse_eq_target(expr: &Expr) -> Result<(Expr, Expr, Expr), SolverContractError> {
    let (head, args) = collect_apps(expr);
    let Expr::Const { name, levels } = head else {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "ring_nf target head is not Eq",
        });
    };
    if name == "Eq" && levels.len() == 1 && args.len() == 3 {
        return Ok((args[0].clone(), args[1].clone(), args[2].clone()));
    }
    if name == "Eq" && levels.is_empty() && args.len() == 4 {
        return Ok((args[1].clone(), args[2].clone(), args[3].clone()));
    }
    Err(SolverContractError::UnsupportedRingNfFragment {
        reason: "ring_nf target must be an Eq over a first-order carrier",
    })
}

fn ring_nf_coefficient_domain_for_type(
    expr: &Expr,
    profile: RingNfAlgebraProfile,
) -> Result<RingNfCoefficientDomain, SolverContractError> {
    let (head, args) = collect_apps(expr);
    if !args.is_empty() {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "ring_nf carrier must be a first-order Nat or Int",
        });
    }
    let Some(name) = ring_nf_head_const_name(&head) else {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "ring_nf carrier head is not a constant",
        });
    };
    let domain = match name {
        "Nat" | "Nat.Nat" => RingNfCoefficientDomain::Nat,
        "Int" | "Int.Int" => RingNfCoefficientDomain::Int,
        _ => {
            return Err(SolverContractError::UnsupportedRingNfOperation {
                profile,
                operator: name.to_owned(),
            });
        }
    };
    validate_ring_nf_profile_domain(profile, domain)?;
    Ok(domain)
}

fn validate_ring_nf_profile_domain(
    profile: RingNfAlgebraProfile,
    domain: RingNfCoefficientDomain,
) -> Result<(), SolverContractError> {
    if profile.allows_signed_coefficients() && domain != RingNfCoefficientDomain::Int {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "ring_nf ring profiles require an Int carrier in this contract",
        });
    }
    Ok(())
}

fn ring_nf_remap_reflected(
    expr: &ParsedRingNfReflectedExpr,
    local_to_ordinal: &BTreeMap<usize, u64>,
) -> Result<RingNfReflectedExpr, SolverContractError> {
    match expr {
        ParsedRingNfReflectedExpr::Constant {
            value,
            source_core_expr_hash,
        } => Ok(RingNfReflectedExpr::Constant {
            value: *value,
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedRingNfReflectedExpr::Variable {
            local_index,
            source_core_expr_hash,
        } => {
            let Some(variable_ordinal) = local_to_ordinal.get(local_index) else {
                return Err(SolverContractError::UnsupportedRingNfFragment {
                    reason: "ring_nf variable missing from the variable map",
                });
            };
            Ok(RingNfReflectedExpr::Variable {
                variable_ordinal: *variable_ordinal,
                source_core_expr_hash: *source_core_expr_hash,
            })
        }
        ParsedRingNfReflectedExpr::Add {
            args,
            source_core_expr_hash,
        } => Ok(RingNfReflectedExpr::Add {
            args: args
                .iter()
                .map(|arg| ring_nf_remap_reflected(arg, local_to_ordinal))
                .collect::<Result<Vec<_>, _>>()?,
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedRingNfReflectedExpr::Mul {
            args,
            source_core_expr_hash,
        } => Ok(RingNfReflectedExpr::Mul {
            args: args
                .iter()
                .map(|arg| ring_nf_remap_reflected(arg, local_to_ordinal))
                .collect::<Result<Vec<_>, _>>()?,
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedRingNfReflectedExpr::Neg {
            arg,
            source_core_expr_hash,
        } => Ok(RingNfReflectedExpr::Neg {
            arg: Box::new(ring_nf_remap_reflected(arg, local_to_ordinal)?),
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedRingNfReflectedExpr::Sub {
            lhs,
            rhs,
            source_core_expr_hash,
        } => Ok(RingNfReflectedExpr::Sub {
            lhs: Box::new(ring_nf_remap_reflected(lhs, local_to_ordinal)?),
            rhs: Box::new(ring_nf_remap_reflected(rhs, local_to_ordinal)?),
            source_core_expr_hash: *source_core_expr_hash,
        }),
        ParsedRingNfReflectedExpr::Pow {
            base,
            exponent,
            source_core_expr_hash,
        } => Ok(RingNfReflectedExpr::Pow {
            base: Box::new(ring_nf_remap_reflected(base, local_to_ordinal)?),
            exponent: *exponent,
            source_core_expr_hash: *source_core_expr_hash,
        }),
    }
}

fn ring_nf_polynomial_from_reflected(
    expr: &RingNfReflectedExpr,
    options: &RingNfNormalizationOptions,
    variable_count: usize,
) -> Result<RingNfPolynomial, SolverContractError> {
    match expr {
        RingNfReflectedExpr::Constant { value, .. } => {
            ring_nf_polynomial_constant(*value, variable_count, options)
        }
        RingNfReflectedExpr::Variable {
            variable_ordinal, ..
        } => ring_nf_polynomial_variable(*variable_ordinal, variable_count, options),
        RingNfReflectedExpr::Add { args, .. } => {
            if args.len() != 2 {
                return Err(SolverContractError::UnsupportedRingNfFragment {
                    reason: "ring_nf reflected addition must be binary",
                });
            }
            let lhs = ring_nf_polynomial_from_reflected(&args[0], options, variable_count)?;
            let rhs = ring_nf_polynomial_from_reflected(&args[1], options, variable_count)?;
            ring_nf_polynomial_add(&lhs, &rhs, options)
        }
        RingNfReflectedExpr::Mul { args, .. } => {
            if args.len() != 2 {
                return Err(SolverContractError::UnsupportedRingNfFragment {
                    reason: "ring_nf reflected multiplication must be binary",
                });
            }
            let lhs = ring_nf_polynomial_from_reflected(&args[0], options, variable_count)?;
            let rhs = ring_nf_polynomial_from_reflected(&args[1], options, variable_count)?;
            ring_nf_polynomial_mul(&lhs, &rhs, options)
        }
        RingNfReflectedExpr::Neg { arg, .. } => {
            if !options.algebra_profile.allows_signed_coefficients() {
                return Err(SolverContractError::UnsupportedRingNfOperation {
                    profile: options.algebra_profile,
                    operator: "neg".to_owned(),
                });
            }
            let poly = ring_nf_polynomial_from_reflected(arg, options, variable_count)?;
            ring_nf_polynomial_neg(&poly, options)
        }
        RingNfReflectedExpr::Sub { lhs, rhs, .. } => {
            if !options.algebra_profile.allows_signed_coefficients() {
                return Err(SolverContractError::UnsupportedRingNfOperation {
                    profile: options.algebra_profile,
                    operator: "sub".to_owned(),
                });
            }
            let lhs = ring_nf_polynomial_from_reflected(lhs, options, variable_count)?;
            let rhs = ring_nf_polynomial_from_reflected(rhs, options, variable_count)?;
            ring_nf_polynomial_sub(&lhs, &rhs, options)
        }
        RingNfReflectedExpr::Pow { base, exponent, .. } => {
            if !options.algebra_profile.is_commutative() {
                return Err(SolverContractError::UnsupportedRingNfOperation {
                    profile: options.algebra_profile,
                    operator: "pow".to_owned(),
                });
            }
            let base = ring_nf_polynomial_from_reflected(base, options, variable_count)?;
            ring_nf_polynomial_pow(&base, *exponent, variable_count, options)
        }
    }
}

fn ring_nf_polynomial_constant(
    value: i64,
    variable_count: usize,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    if value < 0 && !options.algebra_profile.allows_signed_coefficients() {
        return Err(SolverContractError::UnsupportedRingNfOperation {
            profile: options.algebra_profile,
            operator: "negative-literal".to_owned(),
        });
    }
    ring_nf_check_coefficient_bound(value, options)?;
    if value == 0 {
        return Ok(RingNfPolynomial {
            monomials: Vec::new(),
        });
    }
    Ok(RingNfPolynomial {
        monomials: vec![RingNfMonomial {
            coefficient: value,
            exponents: vec![0; variable_count],
        }],
    })
}

fn ring_nf_polynomial_variable(
    variable_ordinal: u64,
    variable_count: usize,
    _options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    let index = variable_ordinal as usize;
    if index >= variable_count {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "ring_nf_variable_ordinal",
        });
    }
    let mut exponents = vec![0; variable_count];
    exponents[index] = 1;
    Ok(RingNfPolynomial {
        monomials: vec![RingNfMonomial {
            coefficient: 1,
            exponents,
        }],
    })
}

fn ring_nf_polynomial_add(
    lhs: &RingNfPolynomial,
    rhs: &RingNfPolynomial,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    let mut map = ring_nf_polynomial_to_map(lhs)?;
    for monomial in &rhs.monomials {
        let previous = map.get(&monomial.exponents).copied().unwrap_or(0);
        let next = ring_nf_checked_i64_add(previous, monomial.coefficient, options)?;
        if next == 0 {
            map.remove(&monomial.exponents);
        } else {
            map.insert(monomial.exponents.clone(), next);
        }
    }
    ring_nf_polynomial_from_map(map, options)
}

fn ring_nf_polynomial_neg(
    polynomial: &RingNfPolynomial,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    let mut map = BTreeMap::new();
    for monomial in &polynomial.monomials {
        map.insert(
            monomial.exponents.clone(),
            ring_nf_checked_i64_mul(monomial.coefficient, -1, options)?,
        );
    }
    ring_nf_polynomial_from_map(map, options)
}

fn ring_nf_polynomial_sub(
    lhs: &RingNfPolynomial,
    rhs: &RingNfPolynomial,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    ring_nf_polynomial_add(lhs, &ring_nf_polynomial_neg(rhs, options)?, options)
}

fn ring_nf_polynomial_mul(
    lhs: &RingNfPolynomial,
    rhs: &RingNfPolynomial,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    if !options.algebra_profile.is_commutative()
        && !ring_nf_polynomial_is_constant(lhs)
        && !ring_nf_polynomial_is_constant(rhs)
    {
        return Err(SolverContractError::NonCommutativeRingNfTerm {
            operator: "mul".to_owned(),
        });
    }
    let mut map = BTreeMap::new();
    for lhs_monomial in &lhs.monomials {
        for rhs_monomial in &rhs.monomials {
            if lhs_monomial.exponents.len() != rhs_monomial.exponents.len() {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "ring_nf_monomial_exponents",
                });
            }
            let coeff = ring_nf_checked_i64_mul(
                lhs_monomial.coefficient,
                rhs_monomial.coefficient,
                options,
            )?;
            let exponents = lhs_monomial
                .exponents
                .iter()
                .zip(&rhs_monomial.exponents)
                .map(|(lhs, rhs)| {
                    lhs.checked_add(*rhs)
                        .ok_or(SolverContractError::RingNfDegreeOverBudget {
                            limit: options.max_total_degree,
                            actual: u64::MAX,
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let previous = map.get(&exponents).copied().unwrap_or(0);
            let next = ring_nf_checked_i64_add(previous, coeff, options)?;
            if next == 0 {
                map.remove(&exponents);
            } else {
                map.insert(exponents, next);
            }
        }
    }
    ring_nf_polynomial_from_map(map, options)
}

fn ring_nf_polynomial_pow(
    base: &RingNfPolynomial,
    exponent: u64,
    variable_count: usize,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    if exponent == 0 {
        return ring_nf_polynomial_constant(1, variable_count, options);
    }
    if exponent > options.max_total_degree {
        return Err(SolverContractError::RingNfDegreeOverBudget {
            limit: options.max_total_degree,
            actual: exponent,
        });
    }
    let mut result = ring_nf_polynomial_constant(1, variable_count, options)?;
    for _ in 0..exponent {
        result = ring_nf_polynomial_mul(&result, base, options)?;
    }
    Ok(result)
}

fn ring_nf_polynomial_to_map(
    polynomial: &RingNfPolynomial,
) -> Result<RingNfPolynomialMap, SolverContractError> {
    let mut map = BTreeMap::new();
    for monomial in &polynomial.monomials {
        if monomial.coefficient == 0 {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "ring_nf_zero_monomial",
            });
        }
        if map
            .insert(monomial.exponents.clone(), monomial.coefficient)
            .is_some()
        {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "ring_nf_duplicate_monomial",
            });
        }
    }
    Ok(map)
}

fn ring_nf_polynomial_from_map(
    map: RingNfPolynomialMap,
    options: &RingNfNormalizationOptions,
) -> Result<RingNfPolynomial, SolverContractError> {
    let mut monomials = Vec::new();
    for (exponents, coefficient) in map {
        if coefficient == 0 {
            continue;
        }
        ring_nf_check_coefficient_bound(coefficient, options)?;
        ring_nf_check_degree(&exponents, options)?;
        monomials.push(RingNfMonomial {
            coefficient,
            exponents,
        });
    }
    if monomials.len() as u64 > options.max_monomials {
        return Err(SolverContractError::RingNfMonomialOverBudget {
            limit: options.max_monomials,
            actual: monomials.len() as u64,
        });
    }
    Ok(RingNfPolynomial { monomials })
}

fn ring_nf_polynomial_is_constant(polynomial: &RingNfPolynomial) -> bool {
    polynomial
        .monomials
        .iter()
        .all(|monomial| monomial.exponents.iter().all(|exponent| *exponent == 0))
}

fn ring_nf_check_degree(
    exponents: &[u64],
    options: &RingNfNormalizationOptions,
) -> Result<(), SolverContractError> {
    let mut degree = 0u64;
    for exponent in exponents {
        degree =
            degree
                .checked_add(*exponent)
                .ok_or(SolverContractError::RingNfDegreeOverBudget {
                    limit: options.max_total_degree,
                    actual: u64::MAX,
                })?;
    }
    if degree > options.max_total_degree {
        return Err(SolverContractError::RingNfDegreeOverBudget {
            limit: options.max_total_degree,
            actual: degree,
        });
    }
    Ok(())
}

fn ring_nf_check_coefficient_bound(
    value: i64,
    options: &RingNfNormalizationOptions,
) -> Result<(), SolverContractError> {
    let magnitude = i128::from(value).abs();
    if magnitude > i128::from(options.max_coefficient_abs) {
        return Err(SolverContractError::RingNfCoefficientOverflow);
    }
    Ok(())
}

fn ring_nf_checked_i64_add(
    lhs: i64,
    rhs: i64,
    options: &RingNfNormalizationOptions,
) -> Result<i64, SolverContractError> {
    let value = lhs
        .checked_add(rhs)
        .ok_or(SolverContractError::RingNfCoefficientOverflow)?;
    ring_nf_check_coefficient_bound(value, options)?;
    Ok(value)
}

fn ring_nf_checked_i64_mul(
    lhs: i64,
    rhs: i64,
    options: &RingNfNormalizationOptions,
) -> Result<i64, SolverContractError> {
    let value = lhs
        .checked_mul(rhs)
        .ok_or(SolverContractError::RingNfCoefficientOverflow)?;
    ring_nf_check_coefficient_bound(value, options)?;
    Ok(value)
}

fn validate_ring_nf_variables(variables: &[RingNfVariable]) -> Result<(), SolverContractError> {
    let mut last_local_index = None;
    let mut seen_names = BTreeSet::new();
    for (index, variable) in variables.iter().enumerate() {
        let expected = index as u64;
        if variable.ordinal != expected {
            return Err(SolverContractError::NonCanonicalRingNfVariableOrder {
                expected_ordinal: expected,
                actual_ordinal: variable.ordinal,
            });
        }
        if let Some(previous) = last_local_index {
            if variable.local_index <= previous {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "ring_nf_variable_local_order",
                });
            }
        }
        last_local_index = Some(variable.local_index);
        if variable.name.is_empty() || !seen_names.insert(variable.name.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "ring_nf_variable",
                identifier: variable.name.clone(),
            });
        }
        if is_zero_hash(&variable.source_core_expr_hash) || is_zero_hash(&variable.type_hash) {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "ring_nf variable identity is incomplete",
            });
        }
    }
    Ok(())
}

fn validate_ring_nf_reflected_expr_shape(
    expr: &RingNfReflectedExpr,
    variable_count: Option<usize>,
) -> Result<(), SolverContractError> {
    match expr {
        RingNfReflectedExpr::Constant {
            source_core_expr_hash,
            ..
        }
        | RingNfReflectedExpr::Variable {
            source_core_expr_hash,
            ..
        }
        | RingNfReflectedExpr::Add {
            source_core_expr_hash,
            ..
        }
        | RingNfReflectedExpr::Mul {
            source_core_expr_hash,
            ..
        }
        | RingNfReflectedExpr::Neg {
            source_core_expr_hash,
            ..
        }
        | RingNfReflectedExpr::Sub {
            source_core_expr_hash,
            ..
        }
        | RingNfReflectedExpr::Pow {
            source_core_expr_hash,
            ..
        } if is_zero_hash(source_core_expr_hash) => {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "ring_nf reflected expression source hash is missing",
            });
        }
        _ => {}
    }
    match expr {
        RingNfReflectedExpr::Constant { .. } => Ok(()),
        RingNfReflectedExpr::Variable {
            variable_ordinal, ..
        } => {
            if let Some(variable_count) = variable_count {
                if (*variable_ordinal as usize) >= variable_count {
                    return Err(SolverContractError::NonCanonicalPayloadBytes {
                        field: "ring_nf_variable_ordinal",
                    });
                }
            }
            Ok(())
        }
        RingNfReflectedExpr::Add { args, .. } | RingNfReflectedExpr::Mul { args, .. } => {
            if args.len() != 2 {
                return Err(SolverContractError::UnsupportedRingNfFragment {
                    reason: "ring_nf reflected binary operator has unsupported arity",
                });
            }
            for arg in args {
                validate_ring_nf_reflected_expr_shape(arg, variable_count)?;
            }
            Ok(())
        }
        RingNfReflectedExpr::Neg { arg, .. } => {
            validate_ring_nf_reflected_expr_shape(arg, variable_count)
        }
        RingNfReflectedExpr::Sub { lhs, rhs, .. } => {
            validate_ring_nf_reflected_expr_shape(lhs, variable_count)?;
            validate_ring_nf_reflected_expr_shape(rhs, variable_count)
        }
        RingNfReflectedExpr::Pow { base, .. } => {
            validate_ring_nf_reflected_expr_shape(base, variable_count)
        }
    }
}

fn validate_ring_nf_polynomial_shape(
    polynomial: &RingNfPolynomial,
    variable_count: Option<usize>,
    coefficient_domain: RingNfCoefficientDomain,
) -> Result<(), SolverContractError> {
    let mut previous_exponents: Option<&Vec<u64>> = None;
    for monomial in &polynomial.monomials {
        if monomial.coefficient == 0 {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "ring_nf_zero_monomial",
            });
        }
        if coefficient_domain == RingNfCoefficientDomain::Nat && monomial.coefficient < 0 {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "Nat ring_nf coefficients must be nonnegative",
            });
        }
        if let Some(variable_count) = variable_count {
            if monomial.exponents.len() != variable_count {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "ring_nf_monomial_exponents",
                });
            }
        }
        if let Some(previous) = previous_exponents {
            if monomial.exponents <= *previous {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "ring_nf_monomial_order",
                });
            }
        }
        previous_exponents = Some(&monomial.exponents);
    }
    Ok(())
}

fn validate_ring_nf_variable_environment_shape(
    entries: &[RingNfVariableEnvironmentEntry],
) -> Result<(), SolverContractError> {
    for (index, entry) in entries.iter().enumerate() {
        let expected = index as u64;
        if entry.variable_ordinal != expected {
            return Err(SolverContractError::NonCanonicalRingNfVariableEnvironment {
                expected_ordinal: expected,
                actual_ordinal: entry.variable_ordinal,
            });
        }
        if is_zero_hash(&entry.source_core_expr_hash)
            || is_zero_hash(&entry.type_hash)
            || is_zero_hash(&entry.value_hash)
        {
            return Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "ring_nf variable environment entry is incomplete",
            });
        }
    }
    Ok(())
}

fn validate_ring_nf_algebra_law_ref_shape(
    law_ref: &RingNfAlgebraLawRef,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&law_ref.theorem_hash) || is_zero_hash(&law_ref.theorem_type_hash) {
        return Err(SolverContractError::MissingRingNfAlgebraLaw { law: law_ref.law });
    }
    Ok(())
}

fn validate_ring_nf_proof_artifact_shape(
    artifact: &RingNfProofArtifact,
) -> Result<(), SolverContractError> {
    if artifact.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "ring_nf_proof_artifact_version",
            tag: artifact.version.as_str().to_owned(),
        });
    }
    for (field, value) in [
        ("ring_nf_request_hash", artifact.request_hash),
        (
            "ring_nf_normalized_problem_hash",
            artifact.normalized_problem_hash,
        ),
        ("ring_nf_profile_hash", artifact.profile_hash),
        (
            "ring_nf_variable_environment_hash",
            artifact.variable_environment_hash,
        ),
        ("ring_nf_policy_hash", artifact.policy_hash),
        (
            "ring_nf_lhs_reflected_expr_hash",
            artifact.lhs_reflected_expr_hash,
        ),
        (
            "ring_nf_rhs_reflected_expr_hash",
            artifact.rhs_reflected_expr_hash,
        ),
        (
            "ring_nf_lhs_normal_form_hash",
            artifact.lhs_normal_form_hash,
        ),
        (
            "ring_nf_rhs_normal_form_hash",
            artifact.rhs_normal_form_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(SolverContractError::MissingRingNfEvidence { field });
        }
    }
    if artifact
        .difference_normal_form_hash
        .as_ref()
        .is_some_and(is_zero_hash)
    {
        return Err(SolverContractError::MissingRingNfEvidence {
            field: "ring_nf_difference_normal_form_hash",
        });
    }
    validate_ring_nf_variable_environment_shape(&artifact.variable_environment)?;
    if artifact.algebra_law_refs.is_empty() {
        return Err(SolverContractError::MissingRingNfAlgebraLaw {
            law: RingNfAlgebraLawKind::ReflectionSoundness,
        });
    }
    let mut seen = BTreeSet::new();
    for law_ref in &artifact.algebra_law_refs {
        validate_ring_nf_algebra_law_ref_shape(law_ref)?;
        if !seen.insert(law_ref.law) {
            return Err(SolverContractError::DuplicateRingNfAlgebraLaw { law: law_ref.law });
        }
    }
    if is_zero_hash(&artifact.proof_identity.environment_hash) {
        return Err(SolverContractError::MissingEnvironmentHash);
    }
    if is_zero_hash(&artifact.proof_identity.proof_term_hash)
        || is_zero_hash(&artifact.proof_identity.proof_type_hash)
    {
        return Err(SolverContractError::MissingPayloadHash);
    }
    if artifact.generated_term_nodes == 0 {
        return Err(SolverContractError::MissingRingNfEvidence {
            field: "generated_term_nodes",
        });
    }
    if artifact.proof_bytes == 0 {
        return Err(SolverContractError::MissingRingNfEvidence {
            field: "proof_bytes",
        });
    }
    if artifact.proof_steps == 0 {
        return Err(SolverContractError::MissingRingNfEvidence {
            field: "proof_steps",
        });
    }
    Ok(())
}

fn validate_ring_nf_variable_environment_for_problem(
    problem: &RingNfNormalizedProblem,
    entries: &[RingNfVariableEnvironmentEntry],
) -> Result<(), SolverContractError> {
    if entries.len() != problem.variables.len() {
        return Err(SolverContractError::MissingRingNfVariableEnvironmentEntry {
            expected_count: problem.variables.len() as u64,
            actual_count: entries.len() as u64,
        });
    }
    for (variable, entry) in problem.variables.iter().zip(entries) {
        if entry.variable_ordinal != variable.ordinal {
            return Err(SolverContractError::NonCanonicalRingNfVariableEnvironment {
                expected_ordinal: variable.ordinal,
                actual_ordinal: entry.variable_ordinal,
            });
        }
        require_ring_nf_hash(
            "ring_nf_variable_source_hash",
            entry.source_core_expr_hash,
            variable.source_core_expr_hash,
        )?;
        require_ring_nf_hash(
            "ring_nf_variable_type_hash",
            entry.type_hash,
            variable.type_hash,
        )?;
    }
    Ok(())
}

fn validate_ring_nf_algebra_law_refs_for_problem(
    problem: &RingNfNormalizedProblem,
    law_refs: &[RingNfAlgebraLawRef],
) -> Result<(), SolverContractError> {
    let expected_laws = ring_nf_required_algebra_laws(problem);
    let mut seen = BTreeSet::new();
    for law_ref in law_refs {
        if law_ref.profile != problem.algebra_profile {
            return Err(SolverContractError::MismatchedRingNfAlgebraLawProfile {
                law: law_ref.law,
                expected: problem.algebra_profile,
                actual: law_ref.profile,
            });
        }
        seen.insert(law_ref.law);
    }
    for law in expected_laws {
        if !seen.contains(&law) {
            return Err(SolverContractError::MissingRingNfAlgebraLaw { law });
        }
    }
    Ok(())
}

fn ring_nf_required_algebra_laws(
    problem: &RingNfNormalizedProblem,
) -> BTreeSet<RingNfAlgebraLawKind> {
    let mut laws = BTreeSet::from([
        RingNfAlgebraLawKind::ReflectionSoundness,
        RingNfAlgebraLawKind::VariableEnvironment,
        RingNfAlgebraLawKind::CoefficientEvaluation,
    ]);
    ring_nf_collect_required_laws_from_expr(
        problem.algebra_profile,
        &problem.equation.lhs_reflected,
        &mut laws,
    );
    ring_nf_collect_required_laws_from_expr(
        problem.algebra_profile,
        &problem.equation.rhs_reflected,
        &mut laws,
    );
    laws
}

fn ring_nf_collect_required_laws_from_expr(
    profile: RingNfAlgebraProfile,
    expr: &RingNfReflectedExpr,
    laws: &mut BTreeSet<RingNfAlgebraLawKind>,
) {
    match expr {
        RingNfReflectedExpr::Constant { .. } | RingNfReflectedExpr::Variable { .. } => {}
        RingNfReflectedExpr::Add { args, .. } => {
            laws.insert(RingNfAlgebraLawKind::AdditionNormalization);
            for arg in args {
                ring_nf_collect_required_laws_from_expr(profile, arg, laws);
            }
        }
        RingNfReflectedExpr::Mul { args, .. } => {
            laws.insert(RingNfAlgebraLawKind::MultiplicationNormalization);
            if profile.is_commutative() {
                laws.insert(RingNfAlgebraLawKind::CommutativeReordering);
            }
            for arg in args {
                ring_nf_collect_required_laws_from_expr(profile, arg, laws);
            }
        }
        RingNfReflectedExpr::Neg { arg, .. } => {
            laws.insert(RingNfAlgebraLawKind::NegationNormalization);
            ring_nf_collect_required_laws_from_expr(profile, arg, laws);
        }
        RingNfReflectedExpr::Sub { lhs, rhs, .. } => {
            laws.insert(RingNfAlgebraLawKind::SubtractionNormalization);
            ring_nf_collect_required_laws_from_expr(profile, lhs, laws);
            ring_nf_collect_required_laws_from_expr(profile, rhs, laws);
        }
        RingNfReflectedExpr::Pow { base, .. } => {
            laws.insert(RingNfAlgebraLawKind::PowerNormalization);
            if profile.is_commutative() {
                laws.insert(RingNfAlgebraLawKind::CommutativeReordering);
            }
            ring_nf_collect_required_laws_from_expr(profile, base, laws);
        }
    }
}

fn require_ring_nf_hash(
    field: &'static str,
    actual: Hash,
    expected: Hash,
) -> Result<(), SolverContractError> {
    if actual == expected {
        Ok(())
    } else {
        Err(SolverContractError::MismatchedHash {
            field,
            expected,
            actual,
        })
    }
}

fn ring_nf_validation_options(profile: RingNfAlgebraProfile) -> RingNfNormalizationOptions {
    RingNfNormalizationOptions {
        algebra_profile: profile,
        max_input_nodes: u64::MAX,
        max_variables: u64::MAX,
        max_monomials: u64::MAX,
        max_total_degree: u64::MAX,
        max_coefficient_abs: i64::MAX,
    }
}

fn ring_nf_expr_node_count(expr: &Expr, limit: u64) -> Result<u64, SolverContractError> {
    fn visit(expr: &Expr, count: &mut u64, limit: u64) -> Result<(), SolverContractError> {
        *count = (*count).saturating_add(1);
        if *count > limit {
            return Err(SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                limit,
                actual: *count,
            });
        }
        match expr {
            Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => Ok(()),
            Expr::App(fun, arg) => {
                visit(fun, count, limit)?;
                visit(arg, count, limit)
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                visit(ty, count, limit)?;
                visit(body, count, limit)
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                visit(ty, count, limit)?;
                visit(value, count, limit)?;
                visit(body, count, limit)
            }
        }
    }
    let mut count = 0;
    visit(expr, &mut count, limit)?;
    Ok(count)
}

fn ring_nf_reflected_expr_node_count(expr: &RingNfReflectedExpr) -> u64 {
    match expr {
        RingNfReflectedExpr::Constant { .. } | RingNfReflectedExpr::Variable { .. } => 1,
        RingNfReflectedExpr::Add { args, .. } | RingNfReflectedExpr::Mul { args, .. } => {
            1 + args
                .iter()
                .map(ring_nf_reflected_expr_node_count)
                .sum::<u64>()
        }
        RingNfReflectedExpr::Neg { arg, .. } => 1 + ring_nf_reflected_expr_node_count(arg),
        RingNfReflectedExpr::Sub { lhs, rhs, .. } => {
            1 + ring_nf_reflected_expr_node_count(lhs) + ring_nf_reflected_expr_node_count(rhs)
        }
        RingNfReflectedExpr::Pow { base, .. } => 1 + ring_nf_reflected_expr_node_count(base),
    }
}

fn ring_nf_head_const_name(head: &Expr) -> Option<&str> {
    match head {
        Expr::Const { name, levels } if levels.is_empty() => Some(name.as_str()),
        _ => None,
    }
}

fn ring_nf_numeric_literal(expr: &Expr) -> Option<i64> {
    let (head, args) = collect_apps(expr);
    if !args.is_empty() {
        return None;
    }
    let name = ring_nf_head_const_name(&head)?;
    match name {
        "Int.zero" | "Nat.zero" | "Ring.IntLit.z" | "Ring.NatLit.z" => Some(0),
        "Int.one" | "Nat.one" | "Ring.IntLit.p1" | "Ring.NatLit.p1" => Some(1),
        _ => ring_nf_prefixed_literal(name, "Ring.IntLit.")
            .or_else(|| ring_nf_nonnegative_prefixed_literal(name, "Ring.NatLit."))
            .or_else(|| ring_nf_prefixed_literal(name, "Omega.IntLit."))
            .or_else(|| ring_nf_nonnegative_prefixed_literal(name, "Omega.NatLit.")),
    }
}

fn ring_nf_nonnegative_literal(expr: &Expr) -> Option<u64> {
    ring_nf_numeric_literal(expr).and_then(|value| u64::try_from(value).ok())
}

fn ring_nf_prefixed_literal(name: &str, prefix: &str) -> Option<i64> {
    let suffix = name.strip_prefix(prefix)?;
    if suffix == "z" {
        return Some(0);
    }
    let (sign, digits) = suffix.split_at(1);
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let magnitude = digits.parse::<i64>().ok()?;
    match sign {
        "p" => Some(magnitude),
        "n" => magnitude.checked_neg(),
        _ => None,
    }
}

fn ring_nf_nonnegative_prefixed_literal(name: &str, prefix: &str) -> Option<i64> {
    let value = ring_nf_prefixed_literal(name, prefix)?;
    (value >= 0).then_some(value)
}

fn ring_nf_arithmetic_operator(name: &str) -> Option<RingNfArithmeticOperator> {
    match name {
        "Nat.add" | "Int.add" | "Ring.add" | "Semiring.add" | "CommSemiring.add"
        | "CommRing.add" => Some(RingNfArithmeticOperator::Add),
        "Nat.mul" | "Int.mul" | "Ring.mul" | "Semiring.mul" | "CommSemiring.mul"
        | "CommRing.mul" => Some(RingNfArithmeticOperator::Mul),
        "Int.neg" | "Ring.neg" | "CommRing.neg" => Some(RingNfArithmeticOperator::Neg),
        "Int.sub" | "Nat.sub" | "Ring.sub" | "CommRing.sub" => Some(RingNfArithmeticOperator::Sub),
        "Nat.pow" | "Int.pow" | "Ring.pow" | "Semiring.pow" | "CommSemiring.pow"
        | "CommRing.pow" => Some(RingNfArithmeticOperator::Pow),
        _ => None,
    }
}

fn ring_nf_local_index_for_bvar(
    context_len: usize,
    de_bruijn_index: u32,
) -> Result<usize, SolverContractError> {
    let index = de_bruijn_index as usize;
    if index >= context_len {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "de Bruijn index outside ring_nf local context",
        });
    }
    Ok(context_len - 1 - index)
}

fn ring_nf_bvar_for_local(
    context_len: usize,
    local_index: usize,
) -> Result<Expr, SolverContractError> {
    if local_index >= context_len {
        return Err(SolverContractError::UnsupportedRingNfFragment {
            reason: "ring_nf local index outside local context",
        });
    }
    let index = context_len - 1 - local_index;
    let index = u32::try_from(index).map_err(|_| SolverContractError::ResourceLimitExceeded {
        field: SolverResourceField::InputNodes,
        limit: u32::MAX as u64,
        actual: index as u64,
    })?;
    Ok(Expr::bvar(index))
}

fn encode_bitblast_sort_to(out: &mut Vec<u8>, sort: &BitblastSort) {
    out.push(sort.tag());
    if let BitblastSort::BitVector { width } = sort {
        encode_u64_to(out, *width);
    }
}

fn encode_bitblast_variable_to(out: &mut Vec<u8>, variable: &BitblastVariable) {
    encode_u64_to(out, variable.ordinal);
    encode_u64_to(out, variable.local_index);
    encode_string_to(out, &variable.name);
    encode_bitblast_sort_to(out, &variable.sort);
    encode_hash_to(out, &variable.source_core_expr_hash);
    encode_hash_to(out, &variable.type_hash);
}

fn encode_bitblast_variable_map_entry_to(out: &mut Vec<u8>, entry: &BitblastVariableMapEntry) {
    encode_u64_to(out, entry.variable_ordinal);
    encode_bitblast_sort_to(out, &entry.sort);
    encode_hash_to(out, &entry.source_core_expr_hash);
    encode_hash_to(out, &entry.type_hash);
    encode_u64_to(out, entry.bit_offset);
    encode_u64_to(out, entry.bit_width);
    encode_u64_to(out, entry.tseitin_variable_start);
    encode_u64_to(out, entry.cnf_literal_start);
}

fn encode_bitblast_reflected_expr_to(out: &mut Vec<u8>, expr: &BitblastReflectedExpr) {
    match expr {
        BitblastReflectedExpr::BoolConstant {
            value,
            source_core_expr_hash,
        } => {
            out.push(0);
            out.push(u8::from(*value));
            encode_hash_to(out, source_core_expr_hash);
        }
        BitblastReflectedExpr::Variable {
            variable_ordinal,
            sort,
            source_core_expr_hash,
        } => {
            out.push(1);
            encode_u64_to(out, *variable_ordinal);
            encode_bitblast_sort_to(out, sort);
            encode_hash_to(out, source_core_expr_hash);
        }
        BitblastReflectedExpr::Unary {
            op,
            arg,
            result_sort,
            source_core_expr_hash,
        } => {
            out.push(2);
            out.push(op.tag());
            encode_bitblast_sort_to(out, result_sort);
            encode_hash_to(out, source_core_expr_hash);
            encode_bitblast_reflected_expr_to(out, arg);
        }
        BitblastReflectedExpr::Binary {
            op,
            lhs,
            rhs,
            result_sort,
            source_core_expr_hash,
        } => {
            out.push(3);
            out.push(op.tag());
            encode_bitblast_sort_to(out, result_sort);
            encode_hash_to(out, source_core_expr_hash);
            encode_bitblast_reflected_expr_to(out, lhs);
            encode_bitblast_reflected_expr_to(out, rhs);
        }
        BitblastReflectedExpr::Equal {
            sort,
            lhs,
            rhs,
            source_core_expr_hash,
        } => {
            out.push(4);
            encode_bitblast_sort_to(out, sort);
            encode_hash_to(out, source_core_expr_hash);
            encode_bitblast_reflected_expr_to(out, lhs);
            encode_bitblast_reflected_expr_to(out, rhs);
        }
    }
}

fn encode_bitblast_circuit_node_to(out: &mut Vec<u8>, node: &BitblastCircuitNode) {
    encode_u64_to(out, node.node_id);
    out.push(node.kind.tag());
    encode_bitblast_sort_to(out, &node.result_sort);
    encode_len_to(out, node.input_node_ids.len());
    for input_node_id in &node.input_node_ids {
        encode_u64_to(out, *input_node_id);
    }
    encode_hash_to(out, &node.source_reflected_expr_hash);
    encode_u64_to(out, node.output_tseitin_start);
    encode_u64_to(out, node.output_width);
}

fn encode_bitblast_cnf_literal_to(out: &mut Vec<u8>, literal: BitblastCnfLiteral) {
    encode_u64_to(out, literal.variable);
    out.push(u8::from(literal.positive));
}

fn encode_bitblast_cnf_clause_to(out: &mut Vec<u8>, clause: &BitblastCnfClause) {
    encode_u64_to(out, clause.ordinal);
    out.push(clause.role.tag());
    encode_hash_to(out, &clause.source_reflected_expr_hash);
    encode_len_to(out, clause.literals.len());
    for literal in &clause.literals {
        encode_bitblast_cnf_literal_to(out, *literal);
    }
}

fn encode_bitblast_semantic_step_to(out: &mut Vec<u8>, step: &BitblastSemanticStep) {
    encode_u64_to(out, step.ordinal);
    out.push(step.kind.tag());
    encode_hash_to(out, &step.input_hash);
    encode_hash_to(out, &step.output_hash);
}

fn encode_bitblast_reconstruction_step_to(out: &mut Vec<u8>, step: &BitblastReconstructionStep) {
    encode_u64_to(out, step.ordinal);
    out.push(step.kind.tag());
    encode_hash_to(out, &step.input_hash);
    encode_hash_to(out, &step.output_hash);
    encode_hash_to(out, &step.checked_rule_hash);
}

fn encode_ring_nf_variable_to(out: &mut Vec<u8>, variable: &RingNfVariable) {
    encode_u64_to(out, variable.ordinal);
    encode_u64_to(out, variable.local_index);
    encode_string_to(out, &variable.name);
    encode_hash_to(out, &variable.source_core_expr_hash);
    encode_hash_to(out, &variable.type_hash);
}

fn encode_ring_nf_variable_environment_entry_to(
    out: &mut Vec<u8>,
    entry: &RingNfVariableEnvironmentEntry,
) {
    encode_u64_to(out, entry.variable_ordinal);
    encode_hash_to(out, &entry.source_core_expr_hash);
    encode_hash_to(out, &entry.type_hash);
    encode_hash_to(out, &entry.value_hash);
}

fn encode_ring_nf_algebra_law_ref_to(out: &mut Vec<u8>, law_ref: &RingNfAlgebraLawRef) {
    out.push(law_ref.law.tag());
    out.push(law_ref.profile.tag());
    encode_hash_to(out, &law_ref.theorem_hash);
    encode_hash_to(out, &law_ref.theorem_type_hash);
}

fn encode_ring_nf_reflected_expr_to(out: &mut Vec<u8>, expr: &RingNfReflectedExpr) {
    match expr {
        RingNfReflectedExpr::Constant {
            value,
            source_core_expr_hash,
        } => {
            out.push(0);
            encode_i64_to(out, *value);
            encode_hash_to(out, source_core_expr_hash);
        }
        RingNfReflectedExpr::Variable {
            variable_ordinal,
            source_core_expr_hash,
        } => {
            out.push(1);
            encode_u64_to(out, *variable_ordinal);
            encode_hash_to(out, source_core_expr_hash);
        }
        RingNfReflectedExpr::Add {
            args,
            source_core_expr_hash,
        } => {
            out.push(2);
            encode_hash_to(out, source_core_expr_hash);
            encode_len_to(out, args.len());
            for arg in args {
                encode_ring_nf_reflected_expr_to(out, arg);
            }
        }
        RingNfReflectedExpr::Mul {
            args,
            source_core_expr_hash,
        } => {
            out.push(3);
            encode_hash_to(out, source_core_expr_hash);
            encode_len_to(out, args.len());
            for arg in args {
                encode_ring_nf_reflected_expr_to(out, arg);
            }
        }
        RingNfReflectedExpr::Neg {
            arg,
            source_core_expr_hash,
        } => {
            out.push(4);
            encode_hash_to(out, source_core_expr_hash);
            encode_ring_nf_reflected_expr_to(out, arg);
        }
        RingNfReflectedExpr::Sub {
            lhs,
            rhs,
            source_core_expr_hash,
        } => {
            out.push(5);
            encode_hash_to(out, source_core_expr_hash);
            encode_ring_nf_reflected_expr_to(out, lhs);
            encode_ring_nf_reflected_expr_to(out, rhs);
        }
        RingNfReflectedExpr::Pow {
            base,
            exponent,
            source_core_expr_hash,
        } => {
            out.push(6);
            encode_hash_to(out, source_core_expr_hash);
            encode_ring_nf_reflected_expr_to(out, base);
            encode_u64_to(out, *exponent);
        }
    }
}

fn encode_ring_nf_polynomial_to(out: &mut Vec<u8>, polynomial: &RingNfPolynomial) {
    encode_len_to(out, polynomial.monomials.len());
    for monomial in &polynomial.monomials {
        encode_i64_to(out, monomial.coefficient);
        encode_len_to(out, monomial.exponents.len());
        for exponent in &monomial.exponents {
            encode_u64_to(out, *exponent);
        }
    }
}

fn encode_ring_nf_equation_to(out: &mut Vec<u8>, equation: &RingNfEquation) {
    encode_hash_to(out, &equation.carrier_type_hash);
    encode_hash_to(
        out,
        &ring_nf_reflected_expr_hash(&equation.lhs_reflected)
            .expect("ring_nf equation was validated before canonical encoding"),
    );
    encode_hash_to(
        out,
        &ring_nf_reflected_expr_hash(&equation.rhs_reflected)
            .expect("ring_nf equation was validated before canonical encoding"),
    );
    encode_hash_to(
        out,
        &ring_nf_polynomial_hash(&equation.lhs_normal_form)
            .expect("ring_nf equation was validated before canonical encoding"),
    );
    encode_hash_to(
        out,
        &ring_nf_polynomial_hash(&equation.rhs_normal_form)
            .expect("ring_nf equation was validated before canonical encoding"),
    );
    match &equation.difference_normal_form {
        Some(difference) => {
            out.push(1);
            encode_hash_to(
                out,
                &ring_nf_polynomial_hash(difference)
                    .expect("ring_nf equation was validated before canonical encoding"),
            );
        }
        None => out.push(0),
    }
    out.push(u8::from(equation.normal_forms_equal));
}

pub fn validate_finite_decide_carrier_ref(
    carrier: &FiniteDecideCarrierRef,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&carrier.carrier_type_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "carrier_type_hash",
        });
    }
    validate_universe_params("carrier_universe_param", &carrier.universe_params)?;
    match carrier.kind {
        FiniteDecideCarrierKind::Bool => {
            require_no_small_kind(carrier)?;
            require_no_explicit_finite_evidence(carrier)?;
            require_no_size_parameter("fin_bound", carrier.fin_bound)?;
            require_no_size_parameter("vector_bool_length", carrier.vector_bool_length)?;
            require_cardinality(2, carrier.cardinality)
        }
        FiniteDecideCarrierKind::Fin => {
            require_no_small_kind(carrier)?;
            require_no_explicit_finite_evidence(carrier)?;
            require_no_size_parameter("vector_bool_length", carrier.vector_bool_length)?;
            let Some(bound) = carrier.fin_bound else {
                return Err(SolverContractError::MissingFiniteEvidence { field: "fin_bound" });
            };
            require_cardinality(bound, carrier.cardinality)
        }
        FiniteDecideCarrierKind::VectorBool => {
            require_no_small_kind(carrier)?;
            require_no_explicit_finite_evidence(carrier)?;
            require_no_size_parameter("fin_bound", carrier.fin_bound)?;
            let Some(length) = carrier.vector_bool_length else {
                return Err(SolverContractError::MissingFiniteEvidence {
                    field: "vector_bool_length",
                });
            };
            let cardinality = vector_bool_cardinality(length)?;
            require_cardinality(cardinality, carrier.cardinality)
        }
        FiniteDecideCarrierKind::SmallExplicitFinite => {
            if carrier.small_kind.is_none() {
                return Err(SolverContractError::MissingFiniteEvidence {
                    field: "small_kind",
                });
            }
            require_no_size_parameter("fin_bound", carrier.fin_bound)?;
            require_no_size_parameter("vector_bool_length", carrier.vector_bool_length)?;
            require_explicit_finite_evidence(carrier)?;
            match carrier.small_kind {
                Some(FiniteDecideSmallCarrierKind::Empty) => {
                    require_cardinality(0, carrier.cardinality)
                }
                Some(FiniteDecideSmallCarrierKind::Unit) => {
                    require_cardinality(1, carrier.cardinality)
                }
                Some(
                    FiniteDecideSmallCarrierKind::Option
                    | FiniteDecideSmallCarrierKind::Product
                    | FiniteDecideSmallCarrierKind::Sum,
                ) => Ok(()),
                None => unreachable!("checked above"),
            }
        }
        FiniteDecideCarrierKind::ExplicitFinite => {
            require_no_small_kind(carrier)?;
            require_no_size_parameter("fin_bound", carrier.fin_bound)?;
            require_no_size_parameter("vector_bool_length", carrier.vector_bool_length)?;
            require_explicit_finite_evidence(carrier)
        }
    }
}

pub fn validate_finite_decide_enumeration(
    enumeration: &FiniteDecideEnumeration,
) -> Result<(), SolverContractError> {
    validate_finite_decide_carrier_ref(&enumeration.carrier)?;
    let actual = enumeration.elements.len() as u64;
    if actual != enumeration.carrier.cardinality {
        return Err(SolverContractError::MissingFiniteEnumerationElement {
            expected_cardinality: enumeration.carrier.cardinality,
            actual_cardinality: actual,
        });
    }
    let mut seen_elements = BTreeSet::new();
    let mut seen_indexes = BTreeSet::new();
    for (index, element) in enumeration.elements.iter().enumerate() {
        validate_finite_decide_element_shape(element)?;
        let expected_ordinal = index as u64;
        if element.ordinal != expected_ordinal {
            return Err(SolverContractError::NonCanonicalFiniteEnumerationOrder {
                expected_ordinal,
                actual_ordinal: element.ordinal,
            });
        }
        if element.element_type_hash != enumeration.carrier.carrier_type_hash {
            return Err(SolverContractError::MismatchedHash {
                field: "element_type_hash",
                expected: enumeration.carrier.carrier_type_hash,
                actual: element.element_type_hash,
            });
        }
        if !seen_elements.insert(element.element_hash) {
            return Err(SolverContractError::DuplicateFiniteEnumerationElement {
                ordinal: element.ordinal,
                element_hash: element.element_hash,
            });
        }
        validate_finite_decide_element_origin_for_carrier(
            &enumeration.carrier,
            element,
            &mut seen_indexes,
        )?;
    }
    Ok(())
}

pub fn validate_finite_decide_predicate_ref(
    predicate: &FiniteDecidePredicateRef,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&predicate.predicate_hash)
        || is_zero_hash(&predicate.predicate_type_hash)
        || is_zero_hash(&predicate.reflected_decidable_hash)
    {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "predicate_ref",
        });
    }
    validate_environment_and_policy_hashes(predicate.environment_hash, predicate.policy_hash)?;
    if is_zero_hash(&predicate.local_context_hash) {
        return Err(SolverContractError::MissingLocalContextIdentity);
    }
    validate_universe_params("predicate_universe_param", &predicate.universe_params)
}

pub fn validate_finite_decide_reflection_contract(
    contract: &FiniteDecideReflectionContract,
) -> Result<(), SolverContractError> {
    validate_finite_decide_solver_request(&contract.request)?;
    validate_finite_decide_enumeration(&contract.enumeration)?;
    validate_finite_decide_predicate_ref(&contract.predicate)?;
    if contract.request.local_context_hash != contract.predicate.local_context_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "local_context_hash",
            expected: contract.request.local_context_hash,
            actual: contract.predicate.local_context_hash,
        });
    }
    if contract.request.environment_hash != contract.predicate.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "environment_hash",
            expected: contract.request.environment_hash,
            actual: contract.predicate.environment_hash,
        });
    }
    if contract.request.policy_hash != contract.predicate.policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "policy_hash",
            expected: contract.request.policy_hash,
            actual: contract.predicate.policy_hash,
        });
    }
    Ok(())
}

pub fn validate_finite_decide_counterexample_for_reflection(
    contract: &FiniteDecideReflectionContract,
    counterexample: &FiniteDecideCounterexampleArtifact,
) -> Result<(), SolverContractError> {
    validate_finite_decide_reflection_contract(contract)?;
    validate_finite_decide_counterexample_shape(counterexample)?;
    let expected_reflection_hash = finite_decide_reflection_contract_hash(contract)?;
    if counterexample.reflection_contract_hash != expected_reflection_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "reflection_contract_hash",
            expected: expected_reflection_hash,
            actual: counterexample.reflection_contract_hash,
        });
    }
    let expected_enumeration_hash = finite_decide_enumeration_hash(&contract.enumeration)?;
    if counterexample.enumeration_hash != expected_enumeration_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "enumeration_hash",
            expected: expected_enumeration_hash,
            actual: counterexample.enumeration_hash,
        });
    }
    if counterexample.predicate_hash != contract.predicate.predicate_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "predicate_hash",
            expected: contract.predicate.predicate_hash,
            actual: counterexample.predicate_hash,
        });
    }
    let matches_enumeration = contract
        .enumeration
        .elements
        .iter()
        .any(|element| element == &counterexample.element);
    if !matches_enumeration {
        return Err(SolverContractError::CounterexampleWitnessNotInEnumeration {
            ordinal: counterexample.element.ordinal,
        });
    }
    Ok(())
}

pub fn validate_finite_decide_proof_artifact_for_reflection(
    contract: &FiniteDecideReflectionContract,
    artifact: &FiniteDecideProofArtifact,
) -> Result<(), SolverContractError> {
    validate_finite_decide_reflection_contract(contract)?;
    validate_finite_decide_proof_artifact_shape(artifact)?;
    let expected_reflection_hash = finite_decide_reflection_contract_hash(contract)?;
    if artifact.reflection_contract_hash != expected_reflection_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "reflection_contract_hash",
            expected: expected_reflection_hash,
            actual: artifact.reflection_contract_hash,
        });
    }
    let expected_enumeration_hash = finite_decide_enumeration_hash(&contract.enumeration)?;
    if artifact.enumeration_hash != expected_enumeration_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "enumeration_hash",
            expected: expected_enumeration_hash,
            actual: artifact.enumeration_hash,
        });
    }
    if artifact.predicate_hash != contract.predicate.predicate_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "predicate_hash",
            expected: contract.predicate.predicate_hash,
            actual: artifact.predicate_hash,
        });
    }
    if artifact.proof_identity.environment_hash != contract.request.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "proof_environment_hash",
            expected: contract.request.environment_hash,
            actual: artifact.proof_identity.environment_hash,
        });
    }
    if artifact.proof_identity.proof_type_hash != contract.request.goal_identity.target_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "proof_type_hash",
            expected: contract.request.goal_identity.target_hash,
            actual: artifact.proof_identity.proof_type_hash,
        });
    }
    if artifact.element_decisions.len() != contract.enumeration.elements.len() {
        return Err(SolverContractError::MissingFiniteEnumerationElement {
            expected_cardinality: contract.enumeration.elements.len() as u64,
            actual_cardinality: artifact.element_decisions.len() as u64,
        });
    }
    for (expected, decision) in contract
        .enumeration
        .elements
        .iter()
        .zip(&artifact.element_decisions)
    {
        if &decision.element != expected {
            return Err(SolverContractError::CounterexampleWitnessNotInEnumeration {
                ordinal: decision.element.ordinal,
            });
        }
    }
    let all_true = artifact
        .element_decisions
        .iter()
        .all(|decision| decision.value.is_true());
    let first_false = artifact
        .element_decisions
        .iter()
        .find(|decision| !decision.value.is_true())
        .map(|decision| decision.element.ordinal);
    let any_true = artifact
        .element_decisions
        .iter()
        .any(|decision| decision.value.is_true());
    match artifact.goal_kind {
        FiniteDecideGoalKind::Universal
        | FiniteDecideGoalKind::Equality
        | FiniteDecideGoalKind::BooleanDecision => {
            if !artifact.fold_result || !all_true {
                return Err(SolverContractError::FalseFiniteDecisionCannotProduceProof {
                    goal_kind: artifact.goal_kind,
                    witness_ordinal: first_false,
                });
            }
        }
        FiniteDecideGoalKind::Existential => {
            if !artifact.fold_result || !any_true {
                return Err(SolverContractError::FalseFiniteDecisionCannotProduceProof {
                    goal_kind: artifact.goal_kind,
                    witness_ordinal: None,
                });
            }
        }
    }
    Ok(())
}

pub fn solver_proof_payload_ref_canonical_bytes(
    payload: &SolverProofPayloadRef,
) -> Result<Vec<u8>, SolverContractError> {
    validate_solver_proof_payload_ref(payload)?;
    let mut out = Vec::new();
    out.push(payload.certificate_format.tag());
    encode_hash_to(&mut out, &payload.payload_hash);
    encode_u64_to(&mut out, payload.size_bytes);
    match &payload.canonical_bytes {
        Some(bytes) => {
            out.push(1);
            encode_bytes_to(&mut out, bytes);
        }
        None => out.push(0),
    }
    Ok(out)
}

pub fn solver_proof_payload_ref_hash(
    payload: &SolverProofPayloadRef,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_PROOF_PAYLOAD_REF_HASH_TAG,
        &solver_proof_payload_ref_canonical_bytes(payload)?,
    ))
}

pub fn solver_reconstruction_plan_canonical_bytes(
    plan: &SolverReconstructionPlanRef,
) -> Result<Vec<u8>, SolverContractError> {
    validate_solver_reconstruction_plan(plan)?;
    let mut out = Vec::new();
    out.push(plan.profile.tag());
    encode_hash_to(&mut out, &plan.reconstruction_plan_hash);
    encode_u64_to(&mut out, plan.imported_theory_count);
    encode_u64_to(&mut out, plan.step_count);
    encode_len_to(&mut out, plan.step_ids.len());
    for step_id in &plan.step_ids {
        encode_string_to(&mut out, step_id);
    }
    encode_option_string(&mut out, plan.final_step_id.as_deref());
    Ok(out)
}

pub fn solver_reconstruction_plan_hash(
    plan: &SolverReconstructionPlanRef,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_RECONSTRUCTION_PLAN_HASH_TAG,
        &solver_reconstruction_plan_canonical_bytes(plan)?,
    ))
}

pub fn solver_certificate_metadata_canonical_bytes(
    metadata: &SolverCertificateMetadata,
) -> Result<Vec<u8>, SolverContractError> {
    validate_solver_certificate_metadata(metadata)?;
    let mut out = vec![
        metadata.family.tag(),
        metadata.fragment.tag(),
        metadata.profile.tag(),
        metadata.certificate_format.tag(),
    ];
    encode_hash_to(&mut out, &metadata.environment_hash);
    encode_hash_to(&mut out, &metadata.policy_hash);
    encode_hash_to(&mut out, &metadata.payload_hash);
    encode_hash_to(&mut out, &metadata.proof_payload_ref_hash);
    encode_hash_to(&mut out, &metadata.reconstruction_plan_hash);
    Ok(out)
}

pub fn solver_certificate_metadata_hash(
    metadata: &SolverCertificateMetadata,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_CERTIFICATE_METADATA_HASH_TAG,
        &solver_certificate_metadata_canonical_bytes(metadata)?,
    ))
}

pub trait SolverResourcePolicyCanonical {
    fn canonical_resource_policy_bytes(&self) -> Result<Vec<u8>, SolverContractError>;
}

impl SolverResourcePolicyCanonical for SolverResourcePolicyRef {
    fn canonical_resource_policy_bytes(&self) -> Result<Vec<u8>, SolverContractError> {
        if is_zero_hash(&self.policy_hash) {
            return Err(SolverContractError::MissingPolicyHash);
        }
        let mut out = Vec::new();
        out.push(self.profile.tag());
        encode_hash_to(&mut out, &self.policy_hash);
        Ok(out)
    }
}

impl SolverResourcePolicyCanonical for SolverResourcePolicy {
    fn canonical_resource_policy_bytes(&self) -> Result<Vec<u8>, SolverContractError> {
        validate_solver_resource_policy(self)?;
        let mut out = vec![self.version.tag(), self.profile.tag(), self.family.tag()];
        encode_u64_to(&mut out, self.max_input_nodes);
        encode_u64_to(&mut out, self.max_input_bytes);
        encode_u64_to(&mut out, self.max_generated_term_nodes);
        encode_u64_to(&mut out, self.max_proof_bytes);
        encode_u64_to(&mut out, self.max_certificate_bytes);
        encode_u64_to(&mut out, self.max_cnf_variables);
        encode_u64_to(&mut out, self.max_cnf_clauses);
        encode_u64_to(&mut out, self.max_solver_steps);
        encode_u64_to(&mut out, self.max_proof_steps);
        encode_u64_to(&mut out, self.max_rule_count);
        encode_u64_to(&mut out, self.max_memory_bytes);
        encode_u64_to(&mut out, self.max_cpu_millis);
        encode_u64_to(&mut out, self.max_wall_clock_millis);
        encode_u64_to(&mut out, self.max_output_bytes);
        encode_u64_to(&mut out, self.max_nested_solver_calls);
        Ok(out)
    }
}

pub fn solver_resource_policy_canonical_bytes<T: SolverResourcePolicyCanonical + ?Sized>(
    policy: &T,
) -> Result<Vec<u8>, SolverContractError> {
    policy.canonical_resource_policy_bytes()
}

pub fn solver_resource_policy_hash<T: SolverResourcePolicyCanonical + ?Sized>(
    policy: &T,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_RESOURCE_POLICY_HASH_TAG,
        &solver_resource_policy_canonical_bytes(policy)?,
    ))
}

pub fn solver_resource_policy_ref(
    policy: &SolverResourcePolicy,
) -> Result<SolverResourcePolicyRef, SolverContractError> {
    Ok(SolverResourcePolicyRef {
        profile: policy.profile,
        policy_hash: solver_resource_policy_hash(policy)?,
    })
}

pub fn solver_default_resource_policy(
    profile: SolverResourcePolicyProfile,
) -> SolverResourcePolicy {
    match profile {
        SolverResourcePolicyProfile::FiniteDecideDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::FiniteDecide,
            max_input_nodes: 8_192,
            max_input_bytes: 1_048_576,
            max_generated_term_nodes: 65_536,
            max_proof_bytes: 2_097_152,
            max_certificate_bytes: 0,
            max_cnf_variables: 0,
            max_cnf_clauses: 0,
            max_solver_steps: 65_536,
            max_proof_steps: 65_536,
            max_rule_count: 512,
            max_memory_bytes: 134_217_728,
            max_cpu_millis: 1_000,
            max_wall_clock_millis: 2_000,
            max_output_bytes: 1_048_576,
            max_nested_solver_calls: 0,
        },
        SolverResourcePolicyProfile::OmegaDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::Omega,
            max_input_nodes: 65_536,
            max_input_bytes: 4_194_304,
            max_generated_term_nodes: 262_144,
            max_proof_bytes: 8_388_608,
            max_certificate_bytes: 4_194_304,
            max_cnf_variables: 0,
            max_cnf_clauses: 0,
            max_solver_steps: 262_144,
            max_proof_steps: 262_144,
            max_rule_count: 4_096,
            max_memory_bytes: 268_435_456,
            max_cpu_millis: 5_000,
            max_wall_clock_millis: 10_000,
            max_output_bytes: 4_194_304,
            max_nested_solver_calls: 0,
        },
        SolverResourcePolicyProfile::RingNfDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::Ring,
            max_input_nodes: 65_536,
            max_input_bytes: 4_194_304,
            max_generated_term_nodes: 262_144,
            max_proof_bytes: 8_388_608,
            max_certificate_bytes: 0,
            max_cnf_variables: 0,
            max_cnf_clauses: 0,
            max_solver_steps: 262_144,
            max_proof_steps: 262_144,
            max_rule_count: 4_096,
            max_memory_bytes: 268_435_456,
            max_cpu_millis: 5_000,
            max_wall_clock_millis: 10_000,
            max_output_bytes: 4_194_304,
            max_nested_solver_calls: 0,
        },
        SolverResourcePolicyProfile::BitblastDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::Bitblast,
            max_input_nodes: 262_144,
            max_input_bytes: 16_777_216,
            max_generated_term_nodes: 524_288,
            max_proof_bytes: 33_554_432,
            max_certificate_bytes: 67_108_864,
            max_cnf_variables: 1_000_000,
            max_cnf_clauses: 4_000_000,
            max_solver_steps: 1_000_000,
            max_proof_steps: 1_000_000,
            max_rule_count: 65_536,
            max_memory_bytes: 1_073_741_824,
            max_cpu_millis: 30_000,
            max_wall_clock_millis: 60_000,
            max_output_bytes: 67_108_864,
            max_nested_solver_calls: 1,
        },
        SolverResourcePolicyProfile::LratDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::Lrat,
            max_input_nodes: 262_144,
            max_input_bytes: 16_777_216,
            max_generated_term_nodes: 524_288,
            max_proof_bytes: 67_108_864,
            max_certificate_bytes: 67_108_864,
            max_cnf_variables: 1_000_000,
            max_cnf_clauses: 4_000_000,
            max_solver_steps: 2_000_000,
            max_proof_steps: 2_000_000,
            max_rule_count: 65_536,
            max_memory_bytes: 1_073_741_824,
            max_cpu_millis: 30_000,
            max_wall_clock_millis: 60_000,
            max_output_bytes: 67_108_864,
            max_nested_solver_calls: 0,
        },
        SolverResourcePolicyProfile::SmtReconstructionDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::Smt,
            max_input_nodes: 1_000_000,
            max_input_bytes: 67_108_864,
            max_generated_term_nodes: 1_000_000,
            max_proof_bytes: 67_108_864,
            max_certificate_bytes: 67_108_864,
            max_cnf_variables: 0,
            max_cnf_clauses: 0,
            max_solver_steps: 1_000_000,
            max_proof_steps: 1_000_000,
            max_rule_count: 65_536,
            max_memory_bytes: 1_073_741_824,
            max_cpu_millis: 30_000,
            max_wall_clock_millis: 60_000,
            max_output_bytes: 67_108_864,
            max_nested_solver_calls: 1,
        },
        SolverResourcePolicyProfile::PlaceholderV1
        | SolverResourcePolicyProfile::FamilyDefaultV1 => SolverResourcePolicy {
            version: SolverContractVersion::V1,
            profile,
            family: SolverFamily::Smt,
            max_input_nodes: 1,
            max_input_bytes: 1,
            max_generated_term_nodes: 1,
            max_proof_bytes: 1,
            max_certificate_bytes: 1,
            max_cnf_variables: 0,
            max_cnf_clauses: 0,
            max_solver_steps: 1,
            max_proof_steps: 1,
            max_rule_count: 1,
            max_memory_bytes: 1,
            max_cpu_millis: 1,
            max_wall_clock_millis: 1,
            max_output_bytes: 1,
            max_nested_solver_calls: 0,
        },
    }
}

pub fn solver_default_resource_policy_for_family(family: SolverFamily) -> SolverResourcePolicy {
    solver_default_resource_policy(match family {
        SolverFamily::FiniteDecide => SolverResourcePolicyProfile::FiniteDecideDefaultV1,
        SolverFamily::Omega => SolverResourcePolicyProfile::OmegaDefaultV1,
        SolverFamily::Ring => SolverResourcePolicyProfile::RingNfDefaultV1,
        SolverFamily::Bitblast => SolverResourcePolicyProfile::BitblastDefaultV1,
        SolverFamily::Lrat => SolverResourcePolicyProfile::LratDefaultV1,
        SolverFamily::Smt => SolverResourcePolicyProfile::SmtReconstructionDefaultV1,
    })
}

pub fn validate_solver_resource_policy(
    policy: &SolverResourcePolicy,
) -> Result<(), SolverContractError> {
    if let Some(family) = policy.profile.default_family() {
        if family != policy.family {
            return Err(SolverContractError::RequestMetadataMismatch {
                field: "resource_policy_profile",
            });
        }
    }
    Ok(())
}

pub fn validate_solver_resource_policy_for_request(
    policy: &SolverResourcePolicy,
    request: &SolverRequest,
) -> Result<(), SolverContractError> {
    validate_solver_request(request)?;
    validate_solver_resource_policy(policy)?;
    if policy.family != request.family {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if !solver_resource_policy_supports_fragment(policy, request.fragment) {
        return Err(SolverContractError::UnsupportedFragment {
            family: request.family,
            fragment: request.fragment,
        });
    }
    let expected = solver_resource_policy_hash(policy)?;
    if request.policy_hash != expected {
        return Err(SolverContractError::MismatchedHash {
            field: "policy_hash",
            expected,
            actual: request.policy_hash,
        });
    }
    Ok(())
}

pub fn solver_resource_policy_supports_fragment(
    policy: &SolverResourcePolicy,
    fragment: SolverFragment,
) -> bool {
    match policy.family {
        SolverFamily::FiniteDecide => fragment == SolverFragment::FiniteEnumerationV1,
        SolverFamily::Omega => fragment == SolverFragment::PresburgerLinearArithmeticV1,
        SolverFamily::Ring => fragment == SolverFragment::SemiringNormalizationV1,
        SolverFamily::Bitblast => fragment == SolverFragment::BitVectorBitblastV1,
        SolverFamily::Lrat => fragment == SolverFragment::LratUnsatV1,
        SolverFamily::Smt => matches!(
            fragment,
            SolverFragment::SmtQfUfV1
                | SolverFragment::SmtQfLiaV1
                | SolverFragment::SmtQfBvV1
                | SolverFragment::SmtQfUfLiaBvV1
        ),
    }
}

pub fn enforce_solver_pre_execution_resource_policy(
    policy: &SolverResourcePolicy,
    request: &SolverRequest,
    usage: SolverResourceUsage,
) -> Result<(), SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    enforce_resource_limit(
        SolverResourceField::InputNodes,
        usage.input_nodes,
        policy.max_input_nodes,
    )?;
    enforce_resource_limit(
        SolverResourceField::InputBytes,
        usage.input_bytes,
        policy.max_input_bytes,
    )?;
    enforce_resource_limit(
        SolverResourceField::NestedSolverCalls,
        usage.nested_solver_calls,
        policy.max_nested_solver_calls,
    )
}

pub fn enforce_solver_generated_artifact_resource_policy(
    policy: &SolverResourcePolicy,
    request: &SolverRequest,
    response: &SolverResponse,
    usage: SolverResourceUsage,
) -> Result<(), SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_solver_response_for_request(request, response)?;
    enforce_solver_resource_usage(policy, usage)
}

pub fn enforce_solver_resource_usage(
    policy: &SolverResourcePolicy,
    usage: SolverResourceUsage,
) -> Result<(), SolverContractError> {
    validate_solver_resource_policy(policy)?;
    enforce_resource_limit(
        SolverResourceField::InputNodes,
        usage.input_nodes,
        policy.max_input_nodes,
    )?;
    enforce_resource_limit(
        SolverResourceField::InputBytes,
        usage.input_bytes,
        policy.max_input_bytes,
    )?;
    enforce_resource_limit(
        SolverResourceField::GeneratedTermNodes,
        usage.generated_term_nodes,
        policy.max_generated_term_nodes,
    )?;
    enforce_resource_limit(
        SolverResourceField::ProofBytes,
        usage.proof_bytes,
        policy.max_proof_bytes,
    )?;
    enforce_resource_limit(
        SolverResourceField::CertificateBytes,
        usage.certificate_bytes,
        policy.max_certificate_bytes,
    )?;
    enforce_resource_limit(
        SolverResourceField::CnfVariables,
        usage.cnf_variables,
        policy.max_cnf_variables,
    )?;
    enforce_resource_limit(
        SolverResourceField::CnfClauses,
        usage.cnf_clauses,
        policy.max_cnf_clauses,
    )?;
    enforce_resource_limit(
        SolverResourceField::SolverSteps,
        usage.solver_steps,
        policy.max_solver_steps,
    )?;
    enforce_resource_limit(
        SolverResourceField::ProofSteps,
        usage.proof_steps,
        policy.max_proof_steps,
    )?;
    enforce_resource_limit(
        SolverResourceField::RuleCount,
        usage.rule_count,
        policy.max_rule_count,
    )?;
    enforce_resource_limit(
        SolverResourceField::MemoryBytes,
        usage.memory_bytes,
        policy.max_memory_bytes,
    )?;
    enforce_resource_limit(
        SolverResourceField::CpuMillis,
        usage.cpu_millis,
        policy.max_cpu_millis,
    )?;
    enforce_resource_limit(
        SolverResourceField::WallClockMillis,
        usage.wall_clock_millis,
        policy.max_wall_clock_millis,
    )?;
    enforce_resource_limit(
        SolverResourceField::OutputBytes,
        usage.output_bytes,
        policy.max_output_bytes,
    )?;
    enforce_resource_limit(
        SolverResourceField::NestedSolverCalls,
        usage.nested_solver_calls,
        policy.max_nested_solver_calls,
    )
}

pub fn solver_resource_usage_from_advanced_smt_candidate(
    candidate: &AdvancedMachineSmtCertificateCandidate,
    problem: Option<&AdvancedMachineSmtEncodedProblem>,
) -> Result<SolverResourceUsage, SolverContractError> {
    let candidate_bytes = advanced_ai_smt_candidate_canonical_bytes(candidate).map_err(|_| {
        SolverContractError::NonCanonicalPayloadBytes {
            field: "advanced_smt_candidate",
        }
    })?;
    let declared_problem_bytes = smt_problem_ref_size_bytes(&candidate.encoded_problem);
    let problem_bytes = match problem {
        Some(problem) => {
            let canonical_problem_bytes = advanced_ai_smt_problem_canonical_bytes(problem)
                .map_err(|_| SolverContractError::NonCanonicalPayloadBytes {
                    field: "advanced_smt_problem",
                })?
                .len() as u64;
            canonical_problem_bytes.max(declared_problem_bytes)
        }
        None => declared_problem_bytes,
    };
    let proof_bytes = smt_proof_payload_ref_size_bytes(&candidate.proof_payload);
    let step_count = candidate.reconstruction_plan.steps.len() as u64;
    let imported_theory_count = candidate.reconstruction_plan.imported_theory_refs.len() as u64;
    Ok(SolverResourceUsage {
        input_nodes: problem
            .map(|problem| problem.commands.len() as u64)
            .unwrap_or(0)
            .saturating_add(step_count)
            .saturating_add(imported_theory_count),
        input_bytes: (candidate_bytes.len() as u64).saturating_add(problem_bytes),
        generated_term_nodes: step_count.saturating_add(1),
        proof_bytes,
        certificate_bytes: proof_bytes,
        cnf_variables: 0,
        cnf_clauses: 0,
        solver_steps: step_count,
        proof_steps: step_count,
        rule_count: step_count,
        memory_bytes: 0,
        cpu_millis: 0,
        wall_clock_millis: 0,
        output_bytes: 0,
        nested_solver_calls: 0,
    })
}

pub fn solver_replay_metadata_for_response(
    request: &SolverRequest,
    response: &SolverResponse,
    policy: &SolverResourcePolicy,
) -> Result<SolverReplayMetadata, SolverContractError> {
    validate_solver_resource_policy_for_request(policy, request)?;
    validate_solver_response_for_request(request, response)?;
    let policy_hash = solver_resource_policy_hash(policy)?;
    Ok(SolverReplayMetadata {
        version: SolverContractVersion::V1,
        request_hash: solver_request_hash(request)?,
        response_identity_hash: solver_response_identity_hash(response)?,
        resource_policy_profile: policy.profile,
        resource_policy_hash: policy_hash,
        environment_hash: request.environment_hash,
        policy_hash,
    })
}

pub fn solver_replay_metadata_canonical_bytes(
    metadata: &SolverReplayMetadata,
) -> Result<Vec<u8>, SolverContractError> {
    validate_solver_replay_metadata_shape(metadata)?;
    let mut out = Vec::new();
    out.push(metadata.version.tag());
    encode_hash_to(&mut out, &metadata.request_hash);
    encode_hash_to(&mut out, &metadata.response_identity_hash);
    out.push(metadata.resource_policy_profile.tag());
    encode_hash_to(&mut out, &metadata.resource_policy_hash);
    encode_hash_to(&mut out, &metadata.environment_hash);
    encode_hash_to(&mut out, &metadata.policy_hash);
    Ok(out)
}

pub fn solver_replay_metadata_hash(
    metadata: &SolverReplayMetadata,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_REPLAY_METADATA_HASH_TAG,
        &solver_replay_metadata_canonical_bytes(metadata)?,
    ))
}

pub fn validate_solver_replay_metadata(
    request: &SolverRequest,
    response: &SolverResponse,
    policy: &SolverResourcePolicy,
    metadata: &SolverReplayMetadata,
) -> Result<(), SolverContractError> {
    let expected = solver_replay_metadata_for_response(request, response, policy)?;
    if metadata.request_hash != expected.request_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "replay_request_hash",
            expected: expected.request_hash,
            actual: metadata.request_hash,
        });
    }
    if metadata.response_identity_hash != expected.response_identity_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "replay_response_identity_hash",
            expected: expected.response_identity_hash,
            actual: metadata.response_identity_hash,
        });
    }
    if metadata.resource_policy_profile != expected.resource_policy_profile {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "resource_policy_profile",
        });
    }
    if metadata.resource_policy_hash != expected.resource_policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "resource_policy_hash",
            expected: expected.resource_policy_hash,
            actual: metadata.resource_policy_hash,
        });
    }
    if metadata.policy_hash != expected.policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "policy_hash",
            expected: expected.policy_hash,
            actual: metadata.policy_hash,
        });
    }
    if metadata.environment_hash != expected.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "environment_hash",
            expected: expected.environment_hash,
            actual: metadata.environment_hash,
        });
    }
    Ok(())
}

pub fn solver_response_metadata_canonical_bytes(
    metadata: &SolverResponseMetadata,
) -> Result<Vec<u8>, SolverContractError> {
    validate_environment_and_policy_hashes(metadata.environment_hash, metadata.policy_hash)?;
    if is_zero_hash(&metadata.request_hash) {
        return Err(SolverContractError::MismatchedHash {
            field: "request_hash",
            expected: [0; 32],
            actual: metadata.request_hash,
        });
    }
    let mut out = Vec::new();
    encode_hash_to(&mut out, &metadata.request_hash);
    out.push(metadata.family.tag());
    out.push(metadata.fragment.tag());
    out.push(metadata.profile.tag());
    encode_hash_to(&mut out, &metadata.environment_hash);
    encode_hash_to(&mut out, &metadata.policy_hash);
    encode_option_hash(&mut out, metadata.payload_hash.as_ref());
    encode_option_hash(&mut out, metadata.proof_payload_ref_hash.as_ref());
    encode_option_certificate_format(&mut out, metadata.certificate_format);
    encode_option_hash(&mut out, metadata.certificate_metadata_hash.as_ref());
    encode_option_hash(&mut out, metadata.reconstruction_plan_hash.as_ref());
    Ok(out)
}

pub fn solver_response_metadata_hash(
    metadata: &SolverResponseMetadata,
) -> Result<Hash, SolverContractError> {
    Ok(hash_with_domain(
        SOLVER_RESPONSE_METADATA_HASH_TAG,
        &solver_response_metadata_canonical_bytes(metadata)?,
    ))
}

pub fn solver_response_identity_hash(
    response: &SolverResponse,
) -> Result<Hash, SolverContractError> {
    validate_solver_response(response)?;
    let mut out = Vec::new();
    out.push(response.version.tag());
    out.push(response.status.tag());
    encode_hash_to(
        &mut out,
        &solver_response_metadata_hash(&response.metadata)?,
    );
    encode_response_payload_identity_to(&mut out, &response.payload)?;
    Ok(hash_with_domain(SOLVER_RESPONSE_IDENTITY_HASH_TAG, &out))
}

pub fn validate_solver_response_for_request(
    request: &SolverRequest,
    response: &SolverResponse,
) -> Result<(), SolverContractError> {
    let expected = solver_request_hash(request)?;
    let actual = response.metadata.request_hash;
    if expected != actual {
        return Err(SolverContractError::RequestResponseHashMismatch { expected, actual });
    }
    validate_solver_response_metadata_matches_request(request, &response.metadata)?;
    validate_solver_response(response)
}

pub fn validate_solver_response(response: &SolverResponse) -> Result<(), SolverContractError> {
    solver_response_metadata_canonical_bytes(&response.metadata)?;
    match (&response.status, &response.payload) {
        (
            SolverResponseStatus::Proposed,
            SolverResponsePayload::Proposed {
                proposal_hash,
                reconstruction_plan,
            },
        ) => {
            if let Some(plan) = reconstruction_plan {
                validate_solver_reconstruction_plan(plan)?;
            }
            validate_solver_response_metadata_for_proposed(
                &response.metadata,
                *proposal_hash,
                reconstruction_plan.as_ref(),
            )?;
            Ok(())
        }
        (SolverResponseStatus::Unsupported, SolverResponsePayload::Unsupported { .. }) => {
            validate_solver_response_metadata_for_unsupported(&response.metadata)?;
            Ok(())
        }
        (
            SolverResponseStatus::Counterexample,
            SolverResponsePayload::Counterexample {
                counterexample_hash,
            },
        ) => {
            if is_zero_hash(counterexample_hash) {
                Err(SolverContractError::MissingPayloadHash)
            } else {
                validate_solver_response_metadata_for_counterexample(
                    &response.metadata,
                    *counterexample_hash,
                )?;
                Ok(())
            }
        }
        (SolverResponseStatus::Certificate, SolverResponsePayload::Certificate(payload)) => {
            validate_solver_accepting_payload(payload)?;
            validate_solver_response_metadata_for_certificate(&response.metadata, payload)
        }
        (status, payload) => Err(SolverContractError::ResponseStatusPayloadMismatch {
            status: *status,
            payload: solver_response_payload_name(payload),
        }),
    }
}

pub fn solver_response_accepting_payload(
    response: &SolverResponse,
) -> Result<&SolverAcceptingPayload, SolverContractError> {
    validate_solver_response(response)?;
    match (&response.status, &response.payload) {
        (SolverResponseStatus::Certificate, SolverResponsePayload::Certificate(payload)) => {
            Ok(payload)
        }
        (status, _) => Err(SolverContractError::NonAcceptingStatusCannotVerify { status: *status }),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedOmegaLinearTerm {
    coefficients_by_local: BTreeMap<usize, i64>,
    constant: i64,
}

impl ParsedOmegaLinearTerm {
    fn zero() -> Self {
        Self {
            coefficients_by_local: BTreeMap::new(),
            constant: 0,
        }
    }

    fn constant(value: i64) -> Self {
        Self {
            coefficients_by_local: BTreeMap::new(),
            constant: value,
        }
    }

    fn variable(local_index: usize) -> Self {
        let mut coefficients_by_local = BTreeMap::new();
        coefficients_by_local.insert(local_index, 1);
        Self {
            coefficients_by_local,
            constant: 0,
        }
    }

    fn is_constant(&self) -> bool {
        self.coefficients_by_local.is_empty()
    }

    fn add(&self, rhs: &Self) -> Result<Self, SolverContractError> {
        let mut out = self.clone();
        out.constant = omega_checked_i64_add(out.constant, rhs.constant)?;
        for (local_index, coeff) in &rhs.coefficients_by_local {
            let next = omega_checked_i64_add(
                out.coefficients_by_local
                    .get(local_index)
                    .copied()
                    .unwrap_or(0),
                *coeff,
            )?;
            if next == 0 {
                out.coefficients_by_local.remove(local_index);
            } else {
                out.coefficients_by_local.insert(*local_index, next);
            }
        }
        Ok(out)
    }

    fn sub(&self, rhs: &Self) -> Result<Self, SolverContractError> {
        self.add(&rhs.mul_const(-1)?)
    }

    fn mul_const(&self, scalar: i64) -> Result<Self, SolverContractError> {
        if scalar == 0 {
            return Ok(Self::zero());
        }
        let mut coefficients_by_local = BTreeMap::new();
        for (local_index, coeff) in &self.coefficients_by_local {
            let next = omega_checked_i64_mul(*coeff, scalar)?;
            if next != 0 {
                coefficients_by_local.insert(*local_index, next);
            }
        }
        Ok(Self {
            coefficients_by_local,
            constant: omega_checked_i64_mul(self.constant, scalar)?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedOmegaAtom {
    relation: OmegaComparisonOp,
    lhs: ParsedOmegaLinearTerm,
    rhs: ParsedOmegaLinearTerm,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ParsedOmegaFormula {
    Atom(ParsedOmegaAtom),
    Boolean {
        op: OmegaBooleanOp,
        args: Vec<ParsedOmegaFormula>,
    },
}

struct OmegaParser<'a> {
    local_context: &'a [OmegaLocalContextEntry],
    options: &'a OmegaNormalizationOptions,
    used_locals: BTreeSet<usize>,
    bounded_expansions: Vec<OmegaBoundedQuantifierExpansion>,
}

impl OmegaParser<'_> {
    fn parse_formula(&mut self, expr: &Expr) -> Result<ParsedOmegaFormula, SolverContractError> {
        let (head, args) = collect_apps(expr);
        let Some(name) = omega_head_const_name(&head) else {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "omega formula head is not a constant",
            });
        };
        if name == "Eq" {
            if args.len() != 4 {
                return Err(SolverContractError::UnsupportedOmegaFragment {
                    reason: "omega Eq must have level, type, lhs, and rhs arguments",
                });
            }
            omega_type_expr_sort(&args[1])?;
            return Ok(ParsedOmegaFormula::Atom(ParsedOmegaAtom {
                relation: OmegaComparisonOp::Eq,
                lhs: self.parse_linear_term(&args[2])?,
                rhs: self.parse_linear_term(&args[3])?,
            }));
        }
        if let Some(op) = omega_comparison_operator(name) {
            if args.len() != 2 {
                return Err(SolverContractError::UnsupportedOmegaFragment {
                    reason: "omega comparison must have exactly two arguments",
                });
            }
            return Ok(ParsedOmegaFormula::Atom(ParsedOmegaAtom {
                relation: op,
                lhs: self.parse_linear_term(&args[0])?,
                rhs: self.parse_linear_term(&args[1])?,
            }));
        }
        if let Some(op) = omega_boolean_operator(name) {
            let expected = match op {
                OmegaBooleanOp::Not => 1,
                OmegaBooleanOp::And | OmegaBooleanOp::Or => 2,
            };
            if args.len() < expected || (op == OmegaBooleanOp::Not && args.len() != 1) {
                return Err(SolverContractError::UnsupportedOmegaFragment {
                    reason: "omega Boolean connective has an unsupported arity",
                });
            }
            let parsed_args = args
                .iter()
                .map(|arg| self.parse_formula(arg))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(ParsedOmegaFormula::Boolean {
                op,
                args: parsed_args,
            });
        }
        if let Some(kind) = omega_bounded_quantifier_operator(name) {
            return self.parse_bounded_expansion(kind, expr, &args);
        }
        Err(SolverContractError::UnsupportedOmegaOperator {
            operator: name.to_owned(),
        })
    }

    fn parse_bounded_expansion(
        &mut self,
        kind: OmegaBoundedQuantifierKind,
        source: &Expr,
        args: &[Expr],
    ) -> Result<ParsedOmegaFormula, SolverContractError> {
        if args.is_empty() {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "bounded expansion is missing its bound",
            });
        }
        let Some(bound) = omega_nonnegative_literal(&args[0]) else {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "bounded expansion bound must be a nonnegative literal",
            });
        };
        let case_count = args.len().saturating_sub(1) as u64;
        if case_count == 0 {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "bounded expansion must provide explicit cases",
            });
        }
        if case_count != bound {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "bounded expansion case count does not match bound",
            });
        }
        if case_count > self.options.max_bounded_quantifier_cases {
            return Err(SolverContractError::OmegaBoundedExpansionOverBudget {
                limit_cases: self.options.max_bounded_quantifier_cases,
                actual_cases: case_count,
            });
        }
        let cases = args[1..]
            .iter()
            .map(|arg| self.parse_formula(arg))
            .collect::<Result<Vec<_>, _>>()?;
        self.bounded_expansions
            .push(OmegaBoundedQuantifierExpansion {
                kind,
                binder_name: "_".to_owned(),
                bound,
                expanded_case_hashes: args[1..].iter().map(core_expr_hash).collect(),
                source_core_expr_hash: core_expr_hash(source),
            });
        Ok(ParsedOmegaFormula::Boolean {
            op: match kind {
                OmegaBoundedQuantifierKind::Forall => OmegaBooleanOp::And,
                OmegaBoundedQuantifierKind::Exists => OmegaBooleanOp::Or,
            },
            args: cases,
        })
    }

    fn parse_linear_term(
        &mut self,
        expr: &Expr,
    ) -> Result<ParsedOmegaLinearTerm, SolverContractError> {
        if let Some(value) = omega_numeric_literal(expr) {
            return Ok(ParsedOmegaLinearTerm::constant(value));
        }
        if let Expr::BVar(index) = expr {
            let local_index = omega_local_index_for_bvar(self.local_context.len(), *index)?;
            let entry = self.local_context.get(local_index).ok_or(
                SolverContractError::UnsupportedOmegaFragment {
                    reason: "de Bruijn index outside omega local context",
                },
            )?;
            omega_type_expr_sort(&entry.ty)?;
            self.used_locals.insert(local_index);
            return Ok(ParsedOmegaLinearTerm::variable(local_index));
        }
        let (head, args) = collect_apps(expr);
        let Some(name) = omega_head_const_name(&head) else {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "omega term head is not a constant",
            });
        };
        match omega_arithmetic_operator(name) {
            Some(OmegaArithmeticOperator::Add) => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedOmegaFragment {
                        reason: "omega addition must have exactly two arguments",
                    });
                }
                self.parse_linear_term(&args[0])?
                    .add(&self.parse_linear_term(&args[1])?)
            }
            Some(OmegaArithmeticOperator::Sub) => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedOmegaFragment {
                        reason: "omega subtraction must have exactly two arguments",
                    });
                }
                self.parse_linear_term(&args[0])?
                    .sub(&self.parse_linear_term(&args[1])?)
            }
            Some(OmegaArithmeticOperator::Neg) => {
                if args.len() != 1 {
                    return Err(SolverContractError::UnsupportedOmegaFragment {
                        reason: "omega negation must have exactly one argument",
                    });
                }
                self.parse_linear_term(&args[0])?.mul_const(-1)
            }
            Some(OmegaArithmeticOperator::Mul) => {
                if args.len() != 2 {
                    return Err(SolverContractError::UnsupportedOmegaFragment {
                        reason: "omega multiplication must have exactly two arguments",
                    });
                }
                let lhs = self.parse_linear_term(&args[0])?;
                let rhs = self.parse_linear_term(&args[1])?;
                match (lhs.is_constant(), rhs.is_constant()) {
                    (true, _) => rhs.mul_const(lhs.constant),
                    (_, true) => lhs.mul_const(rhs.constant),
                    (false, false) => Err(SolverContractError::NonlinearOmegaTerm {
                        operator: name.to_owned(),
                    }),
                }
            }
            None => Err(SolverContractError::UnsupportedOmegaOperator {
                operator: name.to_owned(),
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OmegaArithmeticOperator {
    Add,
    Sub,
    Neg,
    Mul,
}

fn validate_omega_solver_request(request: &SolverRequest) -> Result<(), SolverContractError> {
    validate_solver_request(request)?;
    if request.family != SolverFamily::Omega {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if request.fragment != SolverFragment::PresburgerLinearArithmeticV1 {
        return Err(SolverContractError::UnsupportedFragment {
            family: request.family,
            fragment: request.fragment,
        });
    }
    Ok(())
}

fn validate_omega_variables(variables: &[OmegaVariable]) -> Result<(), SolverContractError> {
    let mut last_local_index = None;
    let mut seen_names = BTreeSet::new();
    for (index, variable) in variables.iter().enumerate() {
        let expected = index as u64;
        if variable.ordinal != expected {
            return Err(SolverContractError::NonCanonicalOmegaVariableOrder {
                expected_ordinal: expected,
                actual_ordinal: variable.ordinal,
            });
        }
        if let Some(previous) = last_local_index {
            if variable.local_index <= previous {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_variable_local_order",
                });
            }
        }
        last_local_index = Some(variable.local_index);
        if variable.name.is_empty() || !seen_names.insert(variable.name.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "omega_variable",
                identifier: variable.name.clone(),
            });
        }
        if is_zero_hash(&variable.source_core_expr_hash) || is_zero_hash(&variable.type_hash) {
            return Err(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: variable.ordinal,
            });
        }
    }
    Ok(())
}

fn validate_omega_formula(
    formula: &OmegaFormula,
    variable_count: usize,
) -> Result<(), SolverContractError> {
    match formula {
        OmegaFormula::Atom(atom) => {
            validate_omega_linear_term(&atom.lhs, variable_count)?;
            validate_omega_linear_term(&atom.rhs, variable_count)?;
            validate_omega_linear_term(&atom.normalized_lhs_minus_rhs, variable_count)?;
            let expected = omega_linear_term_sub(&atom.lhs, &atom.rhs)?;
            if expected != atom.normalized_lhs_minus_rhs {
                return Err(SolverContractError::NonCanonicalPayloadBytes {
                    field: "omega_atom_normal_form",
                });
            }
        }
        OmegaFormula::Boolean { op, args } => {
            match op {
                OmegaBooleanOp::Not if args.len() != 1 => {
                    return Err(SolverContractError::UnsupportedOmegaFragment {
                        reason: "omega not must have exactly one argument",
                    });
                }
                OmegaBooleanOp::And | OmegaBooleanOp::Or if args.len() < 2 => {
                    return Err(SolverContractError::UnsupportedOmegaFragment {
                        reason: "omega and/or must have at least two arguments",
                    });
                }
                _ => {}
            }
            for arg in args {
                validate_omega_formula(arg, variable_count)?;
            }
        }
    }
    Ok(())
}

fn validate_omega_linear_term(
    term: &OmegaLinearTerm,
    variable_count: usize,
) -> Result<(), SolverContractError> {
    if term.coefficients.len() != variable_count {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "omega_coefficient_vector",
        });
    }
    Ok(())
}

fn omega_remap_formula(
    formula: &ParsedOmegaFormula,
    local_to_ordinal: &BTreeMap<usize, u64>,
    variable_count: usize,
) -> Result<OmegaFormula, SolverContractError> {
    match formula {
        ParsedOmegaFormula::Atom(atom) => {
            let lhs = omega_remap_linear_term(&atom.lhs, local_to_ordinal, variable_count)?;
            let rhs = omega_remap_linear_term(&atom.rhs, local_to_ordinal, variable_count)?;
            let normalized_lhs_minus_rhs = omega_linear_term_sub(&lhs, &rhs)?;
            Ok(OmegaFormula::Atom(OmegaAtom {
                relation: atom.relation,
                lhs,
                rhs,
                normalized_lhs_minus_rhs,
            }))
        }
        ParsedOmegaFormula::Boolean { op, args } => Ok(OmegaFormula::Boolean {
            op: *op,
            args: args
                .iter()
                .map(|arg| omega_remap_formula(arg, local_to_ordinal, variable_count))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

fn omega_remap_linear_term(
    term: &ParsedOmegaLinearTerm,
    local_to_ordinal: &BTreeMap<usize, u64>,
    variable_count: usize,
) -> Result<OmegaLinearTerm, SolverContractError> {
    let mut coefficients = vec![0; variable_count];
    for (local_index, coeff) in &term.coefficients_by_local {
        let Some(ordinal) = local_to_ordinal.get(local_index) else {
            return Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "omega term referenced a local missing from the variable map",
            });
        };
        let slot = coefficients.get_mut(*ordinal as usize).ok_or(
            SolverContractError::NonCanonicalPayloadBytes {
                field: "omega_variable_ordinal",
            },
        )?;
        *slot = *coeff;
    }
    Ok(OmegaLinearTerm {
        coefficients,
        constant: term.constant,
    })
}

fn omega_linear_term_sub(
    lhs: &OmegaLinearTerm,
    rhs: &OmegaLinearTerm,
) -> Result<OmegaLinearTerm, SolverContractError> {
    if lhs.coefficients.len() != rhs.coefficients.len() {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "omega_coefficient_vector",
        });
    }
    let coefficients = lhs
        .coefficients
        .iter()
        .zip(rhs.coefficients.iter())
        .map(|(lhs, rhs)| omega_checked_i64_add(*lhs, omega_checked_i64_mul(*rhs, -1)?))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(OmegaLinearTerm {
        coefficients,
        constant: omega_checked_i64_add(lhs.constant, omega_checked_i64_mul(rhs.constant, -1)?)?,
    })
}

fn omega_nat_to_int_side_conditions(
    context_len: usize,
    variables: &[OmegaVariable],
) -> Result<Vec<OmegaNatToIntSideCondition>, SolverContractError> {
    variables
        .iter()
        .filter(|variable| variable.sort == OmegaTermSort::Nat)
        .map(|variable| {
            let source_core_expr =
                omega_bvar_for_local(context_len, variable.local_index as usize)?;
            let int_symbol = omega_smt_symbol_for_variable(variable);
            let smt_side_condition =
                advanced_ai_smt_nat_to_int_side_condition(source_core_expr, int_symbol.clone());
            let smt_side_condition_hash =
                advanced_ai_smt_nat_to_int_side_condition_hash(&smt_side_condition);
            let mut payload = Vec::new();
            encode_u64_to(&mut payload, variable.ordinal);
            encode_hash_to(&mut payload, &smt_side_condition_hash);
            Ok(OmegaNatToIntSideCondition {
                variable_ordinal: variable.ordinal,
                source_core_expr_hash: variable.source_core_expr_hash,
                int_symbol,
                smt_side_condition_hash,
                discharge: OmegaNatToIntDischarge::ProofObligation {
                    obligation_hash: hash_with_domain(
                        OMEGA_NAT_TO_INT_PROOF_OBLIGATION_HASH_TAG,
                        &payload,
                    ),
                },
            })
        })
        .collect()
}

fn omega_smt_symbol_for_variable(variable: &OmegaVariable) -> AdvancedSmtSymbol {
    let mut sanitized = String::new();
    for byte in variable.name.bytes() {
        if byte.is_ascii_alphanumeric() || byte == b'_' {
            sanitized.push(byte as char);
        } else {
            sanitized.push('_');
        }
        if sanitized.len() >= 64 {
            break;
        }
    }
    if sanitized.is_empty() {
        sanitized.push('v');
    }
    AdvancedSmtSymbol {
        ascii: format!("lc:omega_{}_{}", variable.ordinal, sanitized).into_bytes(),
    }
}

fn omega_expr_node_count(expr: &Expr, limit: u64) -> Result<u64, SolverContractError> {
    fn visit(expr: &Expr, count: &mut u64, limit: u64) -> Result<(), SolverContractError> {
        *count = (*count).saturating_add(1);
        if *count > limit {
            return Err(SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                limit,
                actual: *count,
            });
        }
        match expr {
            Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => Ok(()),
            Expr::App(fun, arg) => {
                visit(fun, count, limit)?;
                visit(arg, count, limit)
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                visit(ty, count, limit)?;
                visit(body, count, limit)
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                visit(ty, count, limit)?;
                visit(value, count, limit)?;
                visit(body, count, limit)
            }
        }
    }
    let mut count = 0;
    visit(expr, &mut count, limit)?;
    Ok(count)
}

fn omega_formula_node_count(formula: &OmegaFormula) -> u64 {
    match formula {
        OmegaFormula::Atom(_) => 1,
        OmegaFormula::Boolean { args, .. } => {
            1 + args.iter().map(omega_formula_node_count).sum::<u64>()
        }
    }
}

fn omega_head_const_name(head: &Expr) -> Option<&str> {
    match head {
        Expr::Const { name, levels } if levels.is_empty() => Some(name.as_str()),
        _ => None,
    }
}

fn omega_type_expr_sort(expr: &Expr) -> Result<OmegaTermSort, SolverContractError> {
    let (head, args) = collect_apps(expr);
    if !args.is_empty() {
        return Err(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega local type must be a first-order Nat or Int",
        });
    }
    let Some(name) = omega_head_const_name(&head) else {
        return Err(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega local type head is not a constant",
        });
    };
    match name {
        "Int" | "Int.Int" => Ok(OmegaTermSort::Int),
        "Nat" | "Nat.Nat" => Ok(OmegaTermSort::Nat),
        _ => Err(SolverContractError::UnsupportedOmegaOperator {
            operator: name.to_owned(),
        }),
    }
}

fn omega_numeric_literal(expr: &Expr) -> Option<i64> {
    let (head, args) = collect_apps(expr);
    if !args.is_empty() {
        return None;
    }
    let name = omega_head_const_name(&head)?;
    match name {
        "Int.zero" | "Nat.zero" | "Omega.IntLit.z" | "Omega.NatLit.z" => Some(0),
        "Int.one" | "Nat.one" | "Omega.IntLit.p1" | "Omega.NatLit.p1" => Some(1),
        _ => omega_prefixed_literal(name, "Omega.IntLit.")
            .or_else(|| omega_nonnegative_prefixed_literal(name, "Omega.NatLit.")),
    }
}

fn omega_nonnegative_literal(expr: &Expr) -> Option<u64> {
    omega_numeric_literal(expr).and_then(|value| u64::try_from(value).ok())
}

fn omega_prefixed_literal(name: &str, prefix: &str) -> Option<i64> {
    let suffix = name.strip_prefix(prefix)?;
    if suffix == "z" {
        return Some(0);
    }
    let (sign, digits) = suffix.split_at(1);
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let magnitude = digits.parse::<i64>().ok()?;
    match sign {
        "p" => Some(magnitude),
        "n" => magnitude.checked_neg(),
        _ => None,
    }
}

fn omega_nonnegative_prefixed_literal(name: &str, prefix: &str) -> Option<i64> {
    let value = omega_prefixed_literal(name, prefix)?;
    (value >= 0).then_some(value)
}

fn omega_arithmetic_operator(name: &str) -> Option<OmegaArithmeticOperator> {
    match name {
        "Int.add" | "Nat.add" | "Omega.add" => Some(OmegaArithmeticOperator::Add),
        "Int.sub" | "Omega.sub" => Some(OmegaArithmeticOperator::Sub),
        "Int.neg" | "Omega.neg" => Some(OmegaArithmeticOperator::Neg),
        "Int.mul" | "Nat.mul" | "Omega.mul" => Some(OmegaArithmeticOperator::Mul),
        _ => None,
    }
}

fn omega_comparison_operator(name: &str) -> Option<OmegaComparisonOp> {
    match name {
        "Int.le" | "Nat.le" | "Omega.le" => Some(OmegaComparisonOp::Le),
        "Int.lt" | "Nat.lt" | "Omega.lt" => Some(OmegaComparisonOp::Lt),
        "Int.eq" | "Nat.eq" | "Omega.eq" => Some(OmegaComparisonOp::Eq),
        _ => None,
    }
}

fn omega_boolean_operator(name: &str) -> Option<OmegaBooleanOp> {
    match name {
        "Bool.and" | "Prop.and" | "Omega.and" | "And" => Some(OmegaBooleanOp::And),
        "Bool.or" | "Prop.or" | "Omega.or" | "Or" => Some(OmegaBooleanOp::Or),
        "Bool.not" | "Prop.not" | "Omega.not" | "Not" => Some(OmegaBooleanOp::Not),
        _ => None,
    }
}

fn omega_bounded_quantifier_operator(name: &str) -> Option<OmegaBoundedQuantifierKind> {
    match name {
        "Omega.bforall" | "Omega.bounded_forall" => Some(OmegaBoundedQuantifierKind::Forall),
        "Omega.bexists" | "Omega.bounded_exists" => Some(OmegaBoundedQuantifierKind::Exists),
        _ => None,
    }
}

fn omega_local_index_for_bvar(
    context_len: usize,
    de_bruijn_index: u32,
) -> Result<usize, SolverContractError> {
    let index = de_bruijn_index as usize;
    if index >= context_len {
        return Err(SolverContractError::UnsupportedOmegaFragment {
            reason: "de Bruijn index outside omega local context",
        });
    }
    Ok(context_len - 1 - index)
}

fn omega_bvar_for_local(
    context_len: usize,
    local_index: usize,
) -> Result<Expr, SolverContractError> {
    if local_index >= context_len {
        return Err(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega local index outside local context",
        });
    }
    let index = context_len - 1 - local_index;
    let index = u32::try_from(index).map_err(|_| SolverContractError::ResourceLimitExceeded {
        field: SolverResourceField::InputNodes,
        limit: u32::MAX as u64,
        actual: index as u64,
    })?;
    Ok(Expr::bvar(index))
}

fn omega_checked_i64_add(lhs: i64, rhs: i64) -> Result<i64, SolverContractError> {
    lhs.checked_add(rhs)
        .ok_or(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega integer coefficient overflow",
        })
}

fn omega_checked_i64_mul(lhs: i64, rhs: i64) -> Result<i64, SolverContractError> {
    lhs.checked_mul(rhs)
        .ok_or(SolverContractError::UnsupportedOmegaFragment {
            reason: "omega integer coefficient overflow",
        })
}

fn encode_omega_variable_to(out: &mut Vec<u8>, variable: &OmegaVariable) {
    encode_u64_to(out, variable.ordinal);
    encode_u64_to(out, variable.local_index);
    encode_string_to(out, &variable.name);
    out.push(variable.sort.tag());
    encode_hash_to(out, &variable.source_core_expr_hash);
    encode_hash_to(out, &variable.type_hash);
}

fn encode_omega_linear_term_to(out: &mut Vec<u8>, term: &OmegaLinearTerm) {
    encode_len_to(out, term.coefficients.len());
    for coeff in &term.coefficients {
        encode_i64_to(out, *coeff);
    }
    encode_i64_to(out, term.constant);
}

fn encode_omega_formula_to(out: &mut Vec<u8>, formula: &OmegaFormula) {
    match formula {
        OmegaFormula::Atom(atom) => {
            out.push(0);
            out.push(atom.relation.tag());
            encode_omega_linear_term_to(out, &atom.lhs);
            encode_omega_linear_term_to(out, &atom.rhs);
            encode_omega_linear_term_to(out, &atom.normalized_lhs_minus_rhs);
        }
        OmegaFormula::Boolean { op, args } => {
            out.push(1);
            out.push(op.tag());
            encode_len_to(out, args.len());
            for arg in args {
                encode_omega_formula_to(out, arg);
            }
        }
    }
}

fn encode_omega_nat_to_int_side_condition_to(
    out: &mut Vec<u8>,
    side_condition: &OmegaNatToIntSideCondition,
) {
    encode_u64_to(out, side_condition.variable_ordinal);
    encode_hash_to(out, &side_condition.source_core_expr_hash);
    encode_bytes_to(out, &side_condition.int_symbol.ascii);
    encode_hash_to(out, &side_condition.smt_side_condition_hash);
    out.push(side_condition.discharge.tag());
    match side_condition.discharge {
        OmegaNatToIntDischarge::ProofObligation { obligation_hash } => {
            encode_hash_to(out, &obligation_hash);
        }
        OmegaNatToIntDischarge::ImportedTheorem { theorem_hash } => {
            encode_hash_to(out, &theorem_hash);
        }
        OmegaNatToIntDischarge::Missing => {}
    }
}

fn encode_omega_bounded_expansion_to(
    out: &mut Vec<u8>,
    expansion: &OmegaBoundedQuantifierExpansion,
) {
    out.push(expansion.kind.tag());
    encode_string_to(out, &expansion.binder_name);
    encode_u64_to(out, expansion.bound);
    encode_len_to(out, expansion.expanded_case_hashes.len());
    for hash in &expansion.expanded_case_hashes {
        encode_hash_to(out, hash);
    }
    encode_hash_to(out, &expansion.source_core_expr_hash);
}

fn encode_omega_reconstruction_step_identity_to(out: &mut Vec<u8>, step: &OmegaReconstructionStep) {
    encode_string_to(out, &step.step_id);
    out.push(step.rule.tag());
    encode_string_list_to(out, &step.input_step_ids);
    encode_len_to(out, step.atom_indices.len());
    for index in &step.atom_indices {
        encode_u64_to(out, *index);
    }
    encode_len_to(out, step.coefficients.len());
    for coefficient in &step.coefficients {
        encode_i64_to(out, *coefficient);
    }
    encode_i64_to(out, step.constant);
    encode_len_to(out, step.side_condition_ordinals.len());
    for ordinal in &step.side_condition_ordinals {
        encode_u64_to(out, *ordinal);
    }
}

fn encode_omega_reconstruction_step_to(out: &mut Vec<u8>, step: &OmegaReconstructionStep) {
    encode_omega_reconstruction_step_identity_to(out, step);
    encode_hash_to(out, &step.result_hash);
}

fn enforce_resource_limit(
    field: SolverResourceField,
    actual: u64,
    limit: u64,
) -> Result<(), SolverContractError> {
    if actual <= limit {
        return Ok(());
    }
    Err(match field {
        SolverResourceField::CertificateBytes => SolverContractError::CertificateTooLarge {
            limit_bytes: limit,
            actual_bytes: actual,
        },
        SolverResourceField::GeneratedTermNodes => {
            SolverContractError::ReconstructionTermTooLarge {
                limit_nodes: limit,
                actual_nodes: actual,
            }
        }
        SolverResourceField::SolverSteps
        | SolverResourceField::ProofSteps
        | SolverResourceField::RuleCount => SolverContractError::ProofSearchExhausted {
            field,
            limit,
            actual,
        },
        SolverResourceField::MemoryBytes => SolverContractError::MemoryLimit {
            limit_bytes: limit,
            actual_bytes: actual,
        },
        SolverResourceField::CpuMillis | SolverResourceField::WallClockMillis => {
            SolverContractError::Timeout {
                field,
                limit_millis: limit,
                actual_millis: actual,
            }
        }
        SolverResourceField::OutputBytes => SolverContractError::OutputLimit {
            limit_bytes: limit,
            actual_bytes: actual,
        },
        SolverResourceField::InputNodes
        | SolverResourceField::InputBytes
        | SolverResourceField::ProofBytes
        | SolverResourceField::CnfVariables
        | SolverResourceField::CnfClauses
        | SolverResourceField::NestedSolverCalls => SolverContractError::ResourceLimitExceeded {
            field,
            limit,
            actual,
        },
    })
}

fn smt_problem_ref_size_bytes(source: &AdvancedMachineSmtProblemRef) -> u64 {
    match source {
        AdvancedMachineSmtProblemRef::Inline {
            canonical_bytes, ..
        } => canonical_bytes.len() as u64,
        AdvancedMachineSmtProblemRef::Artifact { size_bytes, .. } => *size_bytes,
    }
}

fn smt_proof_payload_ref_size_bytes(source: &AdvancedMachineSmtProofPayloadRef) -> u64 {
    match source {
        AdvancedMachineSmtProofPayloadRef::Inline {
            canonical_bytes, ..
        } => canonical_bytes.len() as u64,
        AdvancedMachineSmtProofPayloadRef::Artifact { size_bytes, .. } => *size_bytes,
    }
}

fn validate_solver_replay_metadata_shape(
    metadata: &SolverReplayMetadata,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&metadata.request_hash) {
        return Err(SolverContractError::MismatchedHash {
            field: "replay_request_hash",
            expected: [0; 32],
            actual: metadata.request_hash,
        });
    }
    if is_zero_hash(&metadata.response_identity_hash) {
        return Err(SolverContractError::MismatchedHash {
            field: "replay_response_identity_hash",
            expected: [0; 32],
            actual: metadata.response_identity_hash,
        });
    }
    validate_environment_and_policy_hashes(metadata.environment_hash, metadata.policy_hash)?;
    if is_zero_hash(&metadata.resource_policy_hash) {
        return Err(SolverContractError::MissingPolicyHash);
    }
    if metadata.resource_policy_hash != metadata.policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "resource_policy_hash",
            expected: metadata.policy_hash,
            actual: metadata.resource_policy_hash,
        });
    }
    Ok(())
}

fn validate_solver_response_metadata_matches_request(
    request: &SolverRequest,
    metadata: &SolverResponseMetadata,
) -> Result<(), SolverContractError> {
    if request.family != metadata.family {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if request.fragment != metadata.fragment {
        return Err(SolverContractError::RequestMetadataMismatch { field: "fragment" });
    }
    if request.profile != metadata.profile {
        return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
    }
    if request.environment_hash != metadata.environment_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "environment_hash",
            expected: request.environment_hash,
            actual: metadata.environment_hash,
        });
    }
    if request.policy_hash != metadata.policy_hash {
        return Err(SolverContractError::MismatchedHash {
            field: "policy_hash",
            expected: request.policy_hash,
            actual: metadata.policy_hash,
        });
    }
    Ok(())
}

fn validate_solver_response_metadata_for_proposed(
    metadata: &SolverResponseMetadata,
    proposal_hash: Option<Hash>,
    reconstruction_plan: Option<&SolverReconstructionPlanRef>,
) -> Result<(), SolverContractError> {
    validate_optional_hash_field("payload_hash", metadata.payload_hash, proposal_hash)?;
    match reconstruction_plan {
        Some(plan) => require_hash_field(
            "reconstruction_plan_hash",
            metadata.reconstruction_plan_hash,
            solver_reconstruction_plan_hash(plan)?,
        )?,
        None => validate_optional_hash_field(
            "reconstruction_plan_hash",
            metadata.reconstruction_plan_hash,
            None,
        )?,
    }
    reject_verified_response_metadata(metadata)
}

fn validate_solver_response_metadata_for_unsupported(
    metadata: &SolverResponseMetadata,
) -> Result<(), SolverContractError> {
    validate_optional_hash_field("payload_hash", metadata.payload_hash, None)?;
    validate_optional_hash_field(
        "reconstruction_plan_hash",
        metadata.reconstruction_plan_hash,
        None,
    )?;
    reject_verified_response_metadata(metadata)
}

fn validate_solver_response_metadata_for_counterexample(
    metadata: &SolverResponseMetadata,
    counterexample_hash: Hash,
) -> Result<(), SolverContractError> {
    require_hash_field("payload_hash", metadata.payload_hash, counterexample_hash)?;
    validate_optional_hash_field(
        "reconstruction_plan_hash",
        metadata.reconstruction_plan_hash,
        None,
    )?;
    reject_verified_response_metadata(metadata)
}

fn validate_solver_response_metadata_for_certificate(
    metadata: &SolverResponseMetadata,
    payload: &SolverAcceptingPayload,
) -> Result<(), SolverContractError> {
    match payload {
        SolverAcceptingPayload::CheckedProofTerm(identity) => {
            if metadata.environment_hash != identity.environment_hash {
                return Err(SolverContractError::MismatchedHash {
                    field: "environment_hash",
                    expected: identity.environment_hash,
                    actual: metadata.environment_hash,
                });
            }
            require_hash_field(
                "payload_hash",
                metadata.payload_hash,
                identity.proof_term_hash,
            )?;
            require_certificate_format_field(
                metadata.certificate_format,
                SolverCertificateFormat::DirectNpaProofTermV1,
            )?;
            validate_optional_hash_field(
                "proof_payload_ref_hash",
                metadata.proof_payload_ref_hash,
                None,
            )?;
            validate_optional_hash_field(
                "certificate_metadata_hash",
                metadata.certificate_metadata_hash,
                None,
            )?;
            validate_optional_hash_field(
                "reconstruction_plan_hash",
                metadata.reconstruction_plan_hash,
                None,
            )
        }
        SolverAcceptingPayload::CheckedCertificateReconstruction(certificate) => {
            if metadata.family != certificate.family {
                return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
            }
            if metadata.fragment != certificate.fragment {
                return Err(SolverContractError::RequestMetadataMismatch { field: "fragment" });
            }
            if metadata.profile != certificate.profile {
                return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
            }
            if metadata.environment_hash != certificate.environment_hash {
                return Err(SolverContractError::MismatchedHash {
                    field: "environment_hash",
                    expected: certificate.environment_hash,
                    actual: metadata.environment_hash,
                });
            }
            if metadata.policy_hash != certificate.policy_hash {
                return Err(SolverContractError::MismatchedHash {
                    field: "policy_hash",
                    expected: certificate.policy_hash,
                    actual: metadata.policy_hash,
                });
            }
            require_hash_field(
                "payload_hash",
                metadata.payload_hash,
                certificate.payload_hash,
            )?;
            require_hash_field(
                "proof_payload_ref_hash",
                metadata.proof_payload_ref_hash,
                certificate.proof_payload_ref_hash,
            )?;
            require_certificate_format_field(
                metadata.certificate_format,
                certificate.certificate_format,
            )?;
            require_hash_field(
                "certificate_metadata_hash",
                metadata.certificate_metadata_hash,
                solver_certificate_metadata_hash(certificate)?,
            )?;
            require_hash_field(
                "reconstruction_plan_hash",
                metadata.reconstruction_plan_hash,
                certificate.reconstruction_plan_hash,
            )
        }
    }
}

fn reject_verified_response_metadata(
    metadata: &SolverResponseMetadata,
) -> Result<(), SolverContractError> {
    validate_optional_hash_field(
        "proof_payload_ref_hash",
        metadata.proof_payload_ref_hash,
        None,
    )?;
    if metadata.certificate_format.is_some() {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        });
    }
    validate_optional_hash_field(
        "certificate_metadata_hash",
        metadata.certificate_metadata_hash,
        None,
    )
}

fn require_hash_field(
    field: &'static str,
    actual: Option<Hash>,
    expected: Hash,
) -> Result<(), SolverContractError> {
    let Some(actual) = actual else {
        return Err(if field == "reconstruction_plan_hash" {
            SolverContractError::MissingReconstructionPlanHash
        } else {
            SolverContractError::MissingPayloadHash
        });
    };
    if actual != expected {
        return Err(SolverContractError::MismatchedHash {
            field,
            expected,
            actual,
        });
    }
    Ok(())
}

fn validate_optional_hash_field(
    field: &'static str,
    actual: Option<Hash>,
    expected: Option<Hash>,
) -> Result<(), SolverContractError> {
    match (actual, expected) {
        (Some(actual), Some(expected)) if actual == expected => Ok(()),
        (Some(actual), Some(expected)) => Err(SolverContractError::MismatchedHash {
            field,
            expected,
            actual,
        }),
        (None, Some(_)) => Err(if field == "reconstruction_plan_hash" {
            SolverContractError::MissingReconstructionPlanHash
        } else {
            SolverContractError::MissingPayloadHash
        }),
        (Some(_), None) => Err(SolverContractError::RequestMetadataMismatch { field }),
        (None, None) => Ok(()),
    }
}

fn require_certificate_format_field(
    actual: Option<SolverCertificateFormat>,
    expected: SolverCertificateFormat,
) -> Result<(), SolverContractError> {
    match actual {
        Some(actual) if actual == expected => Ok(()),
        Some(_) | None => Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        }),
    }
}

fn validate_solver_accepting_payload(
    payload: &SolverAcceptingPayload,
) -> Result<(), SolverContractError> {
    match payload {
        SolverAcceptingPayload::CheckedProofTerm(identity) => {
            if is_zero_hash(&identity.environment_hash) {
                return Err(SolverContractError::MissingEnvironmentHash);
            }
            if is_zero_hash(&identity.proof_term_hash) || is_zero_hash(&identity.proof_type_hash) {
                return Err(SolverContractError::MissingPayloadHash);
            }
            Ok(())
        }
        SolverAcceptingPayload::CheckedCertificateReconstruction(metadata) => {
            validate_solver_certificate_metadata(metadata)
        }
    }
}

fn validate_solver_certificate_metadata(
    metadata: &SolverCertificateMetadata,
) -> Result<(), SolverContractError> {
    validate_environment_and_policy_hashes(metadata.environment_hash, metadata.policy_hash)?;
    if metadata.certificate_format == SolverCertificateFormat::SolverResultOnlyV1 {
        return Err(SolverContractError::RequestMetadataMismatch {
            field: "certificate_format",
        });
    }
    if is_zero_hash(&metadata.payload_hash) || is_zero_hash(&metadata.proof_payload_ref_hash) {
        return Err(SolverContractError::MissingPayloadHash);
    }
    if is_zero_hash(&metadata.reconstruction_plan_hash) {
        return Err(SolverContractError::MissingReconstructionPlanHash);
    }
    Ok(())
}

fn validate_solver_proof_payload_ref(
    payload: &SolverProofPayloadRef,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&payload.payload_hash) {
        return Err(SolverContractError::MissingPayloadHash);
    }
    if let Some(bytes) = &payload.canonical_bytes {
        let expected = solver_inline_payload_hash(payload.certificate_format, bytes)?;
        if expected != payload.payload_hash {
            return Err(SolverContractError::MismatchedHash {
                field: "payload_hash",
                expected,
                actual: payload.payload_hash,
            });
        }
    }
    Ok(())
}

fn validate_solver_reconstruction_plan(
    plan: &SolverReconstructionPlanRef,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&plan.reconstruction_plan_hash) {
        return Err(SolverContractError::MissingReconstructionPlanHash);
    }
    if plan.step_count != plan.step_ids.len() as u64 {
        return Err(SolverContractError::MismatchedHash {
            field: "reconstruction_step_count",
            expected: hash_u64(plan.step_ids.len() as u64),
            actual: hash_u64(plan.step_count),
        });
    }
    let mut seen = BTreeSet::new();
    for step_id in &plan.step_ids {
        if step_id.is_empty() {
            return Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "reconstruction_step_id",
            });
        }
        if !seen.insert(step_id.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "reconstruction_step_id",
                identifier: step_id.clone(),
            });
        }
    }
    if let Some(final_step_id) = &plan.final_step_id {
        if !seen.contains(final_step_id.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "reconstruction_final_step_id",
                identifier: final_step_id.clone(),
            });
        }
    }
    Ok(())
}

fn validate_canonical_payload_bytes(
    certificate_format: SolverCertificateFormat,
    canonical_bytes: &[u8],
) -> Result<(), SolverContractError> {
    if canonical_bytes.is_empty() {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "canonical_bytes",
        });
    }
    if certificate_format == SolverCertificateFormat::SolverResultOnlyV1
        && canonical_bytes != b"unsat\n"
    {
        return Err(SolverContractError::NonCanonicalPayloadBytes {
            field: "solver_result_only",
        });
    }
    Ok(())
}

fn lrat_error(error: LratCheckError) -> SolverContractError {
    SolverContractError::LratCheckFailed { error }
}

fn validate_lrat_solver_request(request: &SolverRequest) -> Result<(), SolverContractError> {
    validate_solver_request(request)?;
    if request.family != SolverFamily::Lrat {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if request.fragment != SolverFragment::LratUnsatV1 {
        return Err(SolverContractError::UnsupportedFragment {
            family: request.family,
            fragment: request.fragment,
        });
    }
    if request.profile != SolverProfile::CheckedCertificateV1 {
        return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
    }
    Ok(())
}

fn validate_lrat_clause_shape(
    clause: &LratClause,
    variable_count: u64,
    allow_empty: bool,
) -> Result<(), SolverContractError> {
    if clause.line_id == 0 {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_clause_line_id",
        }));
    }
    if clause.literals.is_empty() && !allow_empty {
        return Err(lrat_error(LratCheckError::EmptyInitialClause {
            line_id: clause.line_id,
        }));
    }
    let mut seen_by_variable = BTreeMap::new();
    let mut previous = None;
    for literal in &clause.literals {
        if literal.variable == 0 || literal.variable > variable_count {
            return Err(lrat_error(LratCheckError::LiteralVariableOutOfRange {
                line_id: clause.line_id,
                variable: literal.variable,
                max_variable: variable_count,
            }));
        }
        if let Some(previous_polarity) = seen_by_variable.insert(literal.variable, literal.positive)
        {
            if previous_polarity == literal.positive {
                return Err(lrat_error(LratCheckError::DuplicateLiteral {
                    line_id: clause.line_id,
                    literal: *literal,
                }));
            }
            return Err(lrat_error(LratCheckError::TautologicalClause {
                line_id: clause.line_id,
                variable: literal.variable,
            }));
        }
        if let Some(previous_literal) = previous {
            if previous_literal >= *literal {
                return Err(lrat_error(LratCheckError::NonCanonicalLiteralOrder {
                    line_id: clause.line_id,
                }));
            }
        }
        previous = Some(*literal);
    }
    Ok(())
}

fn validate_lrat_hint_list_shape(line_id: u64, hints: &[u64]) -> Result<(), SolverContractError> {
    let mut seen = BTreeSet::new();
    for hint_id in hints {
        if *hint_id == 0 {
            return Err(lrat_error(LratCheckError::HintOutOfBounds {
                line_id,
                hint_id: *hint_id,
            }));
        }
        if !seen.insert(*hint_id) {
            return Err(SolverContractError::DuplicateIdentifier {
                field: "lrat_hint",
                identifier: hint_id.to_string(),
            });
        }
    }
    Ok(())
}

fn validate_lrat_rat_checks_shape(
    line_id: u64,
    checks: &[LratRatCheck],
) -> Result<(), SolverContractError> {
    let mut previous = None;
    for check in checks {
        if check.clause_id == 0 {
            return Err(lrat_error(LratCheckError::HintOutOfBounds {
                line_id,
                hint_id: check.clause_id,
            }));
        }
        if let Some(previous_clause_id) = previous {
            if previous_clause_id >= check.clause_id {
                return Err(SolverContractError::DuplicateIdentifier {
                    field: "lrat_rat_check_clause",
                    identifier: check.clause_id.to_string(),
                });
            }
        }
        previous = Some(check.clause_id);
        validate_lrat_hint_list_shape(line_id, &check.rup_hints)?;
    }
    Ok(())
}

fn validate_lrat_proof_line_shape(line: &LratProofLine) -> Result<(), SolverContractError> {
    match &line.kind {
        LratProofLineKind::Add { clause, rule } => {
            validate_lrat_clause_shape(clause, u64::MAX, true)?;
            match rule {
                LratProofRule::Rup { hints } => {
                    validate_lrat_hint_list_shape(clause.line_id, hints)
                }
                LratProofRule::Rat { pivot, checks } => {
                    if let Some(pivot) = pivot {
                        if pivot.variable == 0 {
                            return Err(lrat_error(LratCheckError::MissingRatPivot {
                                line_id: clause.line_id,
                            }));
                        }
                    }
                    validate_lrat_rat_checks_shape(clause.line_id, checks)
                }
            }
        }
        LratProofLineKind::Delete { clause_ids } => {
            if clause_ids.is_empty() {
                return Err(lrat_error(LratCheckError::MissingEvidence {
                    field: "lrat_delete_clause_ids",
                }));
            }
            let mut previous = None;
            for clause_id in clause_ids {
                if *clause_id == 0 {
                    return Err(lrat_error(LratCheckError::InvalidDeletion {
                        ordinal: line.ordinal,
                        clause_id: *clause_id,
                    }));
                }
                if let Some(previous_clause_id) = previous {
                    if previous_clause_id >= *clause_id {
                        return Err(SolverContractError::DuplicateIdentifier {
                            field: "lrat_delete_clause",
                            identifier: clause_id.to_string(),
                        });
                    }
                }
                previous = Some(*clause_id);
            }
            Ok(())
        }
    }
}

fn validate_lrat_check_artifact_shape(
    artifact: &LratCheckArtifact,
) -> Result<(), SolverContractError> {
    if artifact.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "lrat_check_artifact_version",
            tag: artifact.version.as_str().to_owned(),
        });
    }
    for (field, value) in [
        ("lrat_check_request_hash", artifact.request_hash),
        ("lrat_check_policy_hash", artifact.policy_hash),
        ("lrat_check_cnf_hash", artifact.cnf_hash),
        ("lrat_check_certificate_hash", artifact.certificate_hash),
        (
            "lrat_check_proof_payload_ref_hash",
            artifact.proof_payload_ref_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(lrat_error(LratCheckError::MissingEvidence { field }));
        }
    }
    if artifact.empty_clause_line_id == 0 {
        return Err(lrat_error(LratCheckError::NoEmptyClause));
    }
    if artifact.original_clause_count == 0 || artifact.proof_line_count == 0 {
        return Err(lrat_error(LratCheckError::MissingEvidence {
            field: "lrat_check_counts",
        }));
    }
    Ok(())
}

fn validate_lrat_cnf_unsat_bridge_artifact_shape(
    artifact: &LratCnfUnsatBridgeArtifact,
) -> Result<(), SolverContractError> {
    if artifact.version != SolverContractVersion::V1 {
        return Err(SolverContractError::UnknownProfileTag {
            field: "lrat_cnf_unsat_bridge_version",
            tag: artifact.version.as_str().to_owned(),
        });
    }
    for (field, value) in [
        ("lrat_cnf_unsat_request_hash", artifact.lrat_request_hash),
        ("lrat_cnf_unsat_policy_hash", artifact.lrat_policy_hash),
        ("lrat_cnf_unsat_cnf_hash", artifact.cnf_hash),
        ("lrat_cnf_unsat_certificate_hash", artifact.certificate_hash),
        ("lrat_cnf_unsat_payload_hash", artifact.payload_hash),
        (
            "lrat_cnf_unsat_payload_ref_hash",
            artifact.proof_payload_ref_hash,
        ),
        (
            "lrat_cnf_unsat_check_artifact_hash",
            artifact.lrat_check_artifact_hash,
        ),
        (
            "lrat_cnf_unsat_theorem_hash",
            artifact.cnf_unsat_theorem_hash,
        ),
    ] {
        if is_zero_hash(&value) {
            return Err(lrat_error(LratCheckError::MissingEvidence { field }));
        }
    }
    if artifact.empty_clause_line_id == 0 {
        return Err(lrat_error(LratCheckError::NoEmptyClause));
    }
    require_lrat_bridge_hash(
        "lrat_cnf_unsat_theorem_hash",
        artifact.cnf_unsat_theorem_hash,
        lrat_cnf_unsat_theorem_hash(
            artifact.cnf_hash,
            artifact.lrat_check_artifact_hash,
            artifact.empty_clause_line_id,
        )?,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LratCheckSummary {
    empty_clause_line_id: u64,
    rup_step_count: u64,
    rat_step_count: u64,
    deletion_step_count: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LratClauseStatus {
    Satisfied,
    Conflict,
    Unit(LratLiteral),
    Unresolved,
}

fn run_lrat_checker(
    cnf: &LratCnf,
    certificate: &LratCertificate,
) -> Result<LratCheckSummary, SolverContractError> {
    let mut active = BTreeMap::new();
    let mut max_line_id = 0;
    for clause in &cnf.clauses {
        validate_lrat_clause_shape(clause, cnf.variable_count, false)?;
        active.insert(clause.line_id, clause.literals.clone());
        max_line_id = clause.line_id;
    }

    let mut empty_clause_line_id = None;
    let mut rup_step_count = 0;
    let mut rat_step_count = 0;
    let mut deletion_step_count = 0;

    for line in &certificate.proof_lines {
        match &line.kind {
            LratProofLineKind::Add { clause, rule } => {
                validate_lrat_clause_shape(clause, cnf.variable_count, true)?;
                if clause.line_id <= max_line_id {
                    return Err(lrat_error(LratCheckError::ProofLineIdNotIncreasing {
                        line_id: clause.line_id,
                        previous_max: max_line_id,
                    }));
                }
                match rule {
                    LratProofRule::Rup { hints } => {
                        lrat_check_rup(&active, &clause.literals, hints, clause.line_id)?;
                        rup_step_count += 1;
                    }
                    LratProofRule::Rat { pivot, checks } => {
                        lrat_check_rat(&active, &clause.literals, *pivot, checks, clause.line_id)?;
                        rat_step_count += 1;
                    }
                }
                if clause.literals.is_empty() && empty_clause_line_id.is_none() {
                    empty_clause_line_id = Some(clause.line_id);
                }
                active.insert(clause.line_id, clause.literals.clone());
                max_line_id = clause.line_id;
            }
            LratProofLineKind::Delete { clause_ids } => {
                for clause_id in clause_ids {
                    if active.remove(clause_id).is_none() {
                        return Err(lrat_error(LratCheckError::InvalidDeletion {
                            ordinal: line.ordinal,
                            clause_id: *clause_id,
                        }));
                    }
                }
                deletion_step_count += 1;
            }
        }
    }

    let Some(empty_clause_line_id) = empty_clause_line_id else {
        return Err(lrat_error(LratCheckError::NoEmptyClause));
    };
    Ok(LratCheckSummary {
        empty_clause_line_id,
        rup_step_count,
        rat_step_count,
        deletion_step_count,
    })
}

fn lrat_check_rup(
    active: &BTreeMap<u64, Vec<LratLiteral>>,
    candidate_clause: &[LratLiteral],
    hints: &[u64],
    line_id: u64,
) -> Result<(), SolverContractError> {
    validate_lrat_hint_list_shape(line_id, hints)?;
    let mut assignments = BTreeMap::new();
    for literal in candidate_clause {
        let assumed_value = !literal.positive;
        if let Some(previous) = assignments.insert(literal.variable, assumed_value) {
            if previous != assumed_value {
                return Ok(());
            }
        }
    }
    for hint_id in hints {
        let hint_clause = lrat_active_clause(active, line_id, *hint_id)?;
        match lrat_eval_clause(hint_clause, &assignments) {
            LratClauseStatus::Conflict => return Ok(()),
            LratClauseStatus::Unit(unit) => {
                if let Some(previous) = assignments.insert(unit.variable, unit.positive) {
                    if previous != unit.positive {
                        return Ok(());
                    }
                }
            }
            LratClauseStatus::Satisfied | LratClauseStatus::Unresolved => {
                return Err(lrat_error(LratCheckError::BadRupHint {
                    line_id,
                    hint_id: *hint_id,
                }));
            }
        }
    }
    Err(lrat_error(LratCheckError::RupDidNotDeriveConflict {
        line_id,
    }))
}

fn lrat_check_rat(
    active: &BTreeMap<u64, Vec<LratLiteral>>,
    candidate_clause: &[LratLiteral],
    pivot: Option<LratLiteral>,
    checks: &[LratRatCheck],
    line_id: u64,
) -> Result<(), SolverContractError> {
    let Some(pivot) = pivot else {
        return Err(lrat_error(LratCheckError::MissingRatPivot { line_id }));
    };
    if !candidate_clause.contains(&pivot) {
        return Err(lrat_error(LratCheckError::RatPivotNotInClause {
            line_id,
            pivot,
        }));
    }

    let mut check_by_clause = BTreeMap::new();
    for check in checks {
        let active_clause = lrat_active_clause(active, line_id, check.clause_id)?;
        if !active_clause.contains(&pivot.negated()) {
            return Err(lrat_error(LratCheckError::RatUnexpectedResolvent {
                line_id,
                clause_id: check.clause_id,
            }));
        }
        if lrat_resolvent(candidate_clause, active_clause, pivot).is_none() {
            return Err(lrat_error(LratCheckError::RatUnexpectedResolvent {
                line_id,
                clause_id: check.clause_id,
            }));
        }
        check_by_clause.insert(check.clause_id, check);
    }

    for (clause_id, active_clause) in active {
        if !active_clause.contains(&pivot.negated()) {
            continue;
        }
        let Some(resolvent) = lrat_resolvent(candidate_clause, active_clause, pivot) else {
            continue;
        };
        let Some(check) = check_by_clause.get(clause_id) else {
            return Err(lrat_error(LratCheckError::RatMissingResolvent {
                line_id,
                clause_id: *clause_id,
            }));
        };
        lrat_check_rup(active, &resolvent, &check.rup_hints, line_id)?;
    }
    Ok(())
}

fn lrat_active_clause(
    active: &BTreeMap<u64, Vec<LratLiteral>>,
    line_id: u64,
    hint_id: u64,
) -> Result<&[LratLiteral], SolverContractError> {
    if hint_id == 0 || hint_id >= line_id {
        return Err(lrat_error(LratCheckError::HintOutOfBounds {
            line_id,
            hint_id,
        }));
    }
    active.get(&hint_id).map(Vec::as_slice).ok_or_else(|| {
        lrat_error(LratCheckError::ClauseNotActive {
            line_id,
            referenced_id: hint_id,
        })
    })
}

fn lrat_eval_clause(clause: &[LratLiteral], assignments: &BTreeMap<u64, bool>) -> LratClauseStatus {
    let mut unit = None;
    for literal in clause {
        match assignments.get(&literal.variable) {
            Some(value) if *value == literal.positive => return LratClauseStatus::Satisfied,
            Some(_) => {}
            None => {
                if unit.replace(*literal).is_some() {
                    return LratClauseStatus::Unresolved;
                }
            }
        }
    }
    match unit {
        Some(literal) => LratClauseStatus::Unit(literal),
        None => LratClauseStatus::Conflict,
    }
}

fn lrat_resolvent(
    candidate_clause: &[LratLiteral],
    active_clause: &[LratLiteral],
    pivot: LratLiteral,
) -> Option<Vec<LratLiteral>> {
    let mut literals_by_variable = BTreeMap::new();
    let mut tautological = false;
    for literal in candidate_clause
        .iter()
        .copied()
        .filter(|literal| *literal != pivot)
        .chain(
            active_clause
                .iter()
                .copied()
                .filter(|literal| *literal != pivot.negated()),
        )
    {
        if let Some(previous) = literals_by_variable.insert(literal.variable, literal.positive) {
            if previous != literal.positive {
                tautological = true;
            }
        }
    }
    if tautological {
        None
    } else {
        Some(
            literals_by_variable
                .into_iter()
                .map(|(variable, positive)| LratLiteral { variable, positive })
                .collect(),
        )
    }
}

fn lrat_cnf_literal_count(cnf: &LratCnf) -> u64 {
    cnf.clauses
        .iter()
        .map(|clause| clause.literals.len() as u64)
        .sum()
}

fn lrat_certificate_literal_count(certificate: &LratCertificate) -> u64 {
    certificate
        .proof_lines
        .iter()
        .map(|line| match &line.kind {
            LratProofLineKind::Add { clause, .. } => clause.literals.len() as u64,
            LratProofLineKind::Delete { .. } => 0,
        })
        .sum()
}

fn lrat_certificate_hint_count(certificate: &LratCertificate) -> u64 {
    certificate
        .proof_lines
        .iter()
        .map(|line| match &line.kind {
            LratProofLineKind::Add { rule, .. } => match rule {
                LratProofRule::Rup { hints } => hints.len() as u64,
                LratProofRule::Rat { checks, .. } => checks
                    .iter()
                    .map(|check| check.rup_hints.len() as u64)
                    .sum(),
            },
            LratProofLineKind::Delete { clause_ids } => clause_ids.len() as u64,
        })
        .sum()
}

fn lrat_memory_estimate_bytes(cnf: &LratCnf, certificate: &LratCertificate) -> u64 {
    let clause_count = cnf.clauses.len().saturating_add(
        certificate
            .proof_lines
            .iter()
            .filter(|line| matches!(line.kind, LratProofLineKind::Add { .. }))
            .count(),
    ) as u64;
    let literal_count =
        lrat_cnf_literal_count(cnf).saturating_add(lrat_certificate_literal_count(certificate));
    let hint_count = lrat_certificate_hint_count(certificate);
    clause_count
        .saturating_mul(32)
        .saturating_add(literal_count.saturating_mul(16))
        .saturating_add(hint_count.saturating_mul(8))
}

fn encode_lrat_literal_to(out: &mut Vec<u8>, literal: LratLiteral) {
    encode_u64_to(out, literal.variable);
    out.push(u8::from(literal.positive));
}

fn encode_lrat_clause_to(out: &mut Vec<u8>, clause: &LratClause) {
    encode_u64_to(out, clause.line_id);
    encode_len_to(out, clause.literals.len());
    for literal in &clause.literals {
        encode_lrat_literal_to(out, *literal);
    }
}

fn encode_lrat_rat_check_to(out: &mut Vec<u8>, check: &LratRatCheck) {
    encode_u64_to(out, check.clause_id);
    encode_len_to(out, check.rup_hints.len());
    for hint in &check.rup_hints {
        encode_u64_to(out, *hint);
    }
}

fn encode_lrat_proof_rule_to(out: &mut Vec<u8>, rule: &LratProofRule) {
    match rule {
        LratProofRule::Rup { hints } => {
            out.push(0);
            encode_len_to(out, hints.len());
            for hint in hints {
                encode_u64_to(out, *hint);
            }
        }
        LratProofRule::Rat { pivot, checks } => {
            out.push(1);
            match pivot {
                Some(pivot) => {
                    out.push(1);
                    encode_lrat_literal_to(out, *pivot);
                }
                None => out.push(0),
            }
            encode_len_to(out, checks.len());
            for check in checks {
                encode_lrat_rat_check_to(out, check);
            }
        }
    }
}

fn encode_lrat_proof_line_to(out: &mut Vec<u8>, line: &LratProofLine) {
    encode_u64_to(out, line.ordinal);
    match &line.kind {
        LratProofLineKind::Add { clause, rule } => {
            out.push(0);
            encode_lrat_clause_to(out, clause);
            encode_lrat_proof_rule_to(out, rule);
        }
        LratProofLineKind::Delete { clause_ids } => {
            out.push(1);
            encode_len_to(out, clause_ids.len());
            for clause_id in clause_ids {
                encode_u64_to(out, *clause_id);
            }
        }
    }
}

fn validate_finite_decide_solver_request(
    request: &SolverRequest,
) -> Result<(), SolverContractError> {
    validate_solver_request(request)?;
    if request.family != SolverFamily::FiniteDecide {
        return Err(SolverContractError::RequestMetadataMismatch { field: "family" });
    }
    if request.fragment != SolverFragment::FiniteEnumerationV1 {
        return Err(SolverContractError::UnsupportedFragment {
            family: request.family,
            fragment: request.fragment,
        });
    }
    if request.profile != SolverProfile::DirectProofTermV1 {
        return Err(SolverContractError::RequestMetadataMismatch { field: "profile" });
    }
    Ok(())
}

fn validate_finite_decide_element_shape(
    element: &FiniteDecideElement,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&element.element_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "element_hash",
        });
    }
    if is_zero_hash(&element.element_type_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "element_type_hash",
        });
    }
    if let FiniteDecideElementOrigin::ExplicitIndex { index_hash } = element.origin {
        if is_zero_hash(&index_hash) {
            return Err(SolverContractError::MissingFiniteEvidence {
                field: "explicit_index_hash",
            });
        }
    }
    Ok(())
}

fn validate_finite_decide_element_origin_for_carrier(
    carrier: &FiniteDecideCarrierRef,
    element: &FiniteDecideElement,
    seen_indexes: &mut BTreeSet<Hash>,
) -> Result<(), SolverContractError> {
    match (&carrier.kind, &element.origin) {
        (FiniteDecideCarrierKind::Bool, FiniteDecideElementOrigin::BoolFalse)
            if element.ordinal == 0 =>
        {
            Ok(())
        }
        (FiniteDecideCarrierKind::Bool, FiniteDecideElementOrigin::BoolTrue)
            if element.ordinal == 1 =>
        {
            Ok(())
        }
        (FiniteDecideCarrierKind::Fin, FiniteDecideElementOrigin::FinOrdinal(ordinal))
            if *ordinal == element.ordinal =>
        {
            Ok(())
        }
        (FiniteDecideCarrierKind::VectorBool, FiniteDecideElementOrigin::VectorBoolBits(bits)) => {
            let Some(length) = carrier.vector_bool_length else {
                return Err(SolverContractError::MissingFiniteEvidence {
                    field: "vector_bool_length",
                });
            };
            if bits.len() as u64 != length {
                return Err(SolverContractError::NonCanonicalFiniteEnumerationOrder {
                    expected_ordinal: element.ordinal,
                    actual_ordinal: u64::MAX,
                });
            }
            let actual_ordinal = vector_bool_bits_ordinal(bits)?;
            if actual_ordinal != element.ordinal {
                return Err(SolverContractError::NonCanonicalFiniteEnumerationOrder {
                    expected_ordinal: element.ordinal,
                    actual_ordinal,
                });
            }
            Ok(())
        }
        (
            FiniteDecideCarrierKind::ExplicitFinite,
            FiniteDecideElementOrigin::ExplicitIndex { index_hash },
        ) => {
            if !seen_indexes.insert(*index_hash) {
                return Err(SolverContractError::DuplicateFiniteEnumerationElement {
                    ordinal: element.ordinal,
                    element_hash: *index_hash,
                });
            }
            Ok(())
        }
        (
            FiniteDecideCarrierKind::SmallExplicitFinite,
            FiniteDecideElementOrigin::SmallExplicitOrdinal { ordinal },
        ) if *ordinal == element.ordinal => Ok(()),
        _ => Err(SolverContractError::NonCanonicalFiniteEnumerationOrder {
            expected_ordinal: element.ordinal,
            actual_ordinal: origin_debug_ordinal(&element.origin),
        }),
    }
}

fn validate_finite_decide_counterexample_shape(
    counterexample: &FiniteDecideCounterexampleArtifact,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&counterexample.reflection_contract_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "reflection_contract_hash",
        });
    }
    if is_zero_hash(&counterexample.enumeration_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "enumeration_hash",
        });
    }
    validate_finite_decide_element_shape(&counterexample.element)?;
    if is_zero_hash(&counterexample.predicate_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "predicate_hash",
        });
    }
    if is_zero_hash(&counterexample.predicate_evidence_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "predicate_evidence_hash",
        });
    }
    Ok(())
}

fn validate_finite_decide_proof_artifact_shape(
    artifact: &FiniteDecideProofArtifact,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&artifact.reflection_contract_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "reflection_contract_hash",
        });
    }
    if is_zero_hash(&artifact.enumeration_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "enumeration_hash",
        });
    }
    if is_zero_hash(&artifact.predicate_hash) {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "predicate_hash",
        });
    }
    if is_zero_hash(&artifact.proof_identity.environment_hash) {
        return Err(SolverContractError::MissingEnvironmentHash);
    }
    if is_zero_hash(&artifact.proof_identity.proof_term_hash)
        || is_zero_hash(&artifact.proof_identity.proof_type_hash)
    {
        return Err(SolverContractError::MissingPayloadHash);
    }
    if artifact.generated_term_nodes == 0 {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "generated_term_nodes",
        });
    }
    if artifact.proof_bytes == 0 {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "proof_bytes",
        });
    }
    if artifact.proof_steps == 0 {
        return Err(SolverContractError::MissingFiniteEvidence {
            field: "proof_steps",
        });
    }
    for decision in &artifact.element_decisions {
        validate_finite_decide_element_shape(&decision.element)?;
        if is_zero_hash(&decision.predicate_evidence_hash) {
            return Err(SolverContractError::MissingFiniteEvidence {
                field: "predicate_evidence_hash",
            });
        }
        match (decision.value, decision.proof_term_hash) {
            (FiniteDecideDecisionValue::PredicateTrue, Some(hash)) if !is_zero_hash(&hash) => {}
            (FiniteDecideDecisionValue::PredicateTrue, Some(_) | None) => {
                return Err(SolverContractError::MissingFiniteEvidence {
                    field: "element_proof_term_hash",
                });
            }
            (FiniteDecideDecisionValue::PredicateFalse, Some(_)) => {
                return Err(SolverContractError::FalseFiniteDecisionCannotProduceProof {
                    goal_kind: artifact.goal_kind,
                    witness_ordinal: Some(decision.element.ordinal),
                });
            }
            (FiniteDecideDecisionValue::PredicateFalse, None) => {}
        }
    }
    Ok(())
}

fn require_cardinality(expected: u64, actual: u64) -> Result<(), SolverContractError> {
    if expected == actual {
        Ok(())
    } else {
        Err(SolverContractError::FiniteCarrierCardinalityMismatch {
            expected_cardinality: expected,
            actual_cardinality: actual,
        })
    }
}

fn require_no_small_kind(carrier: &FiniteDecideCarrierRef) -> Result<(), SolverContractError> {
    if carrier.small_kind.is_none() {
        Ok(())
    } else {
        Err(SolverContractError::RequestMetadataMismatch {
            field: "small_kind",
        })
    }
}

fn require_no_size_parameter(
    field: &'static str,
    value: Option<u64>,
) -> Result<(), SolverContractError> {
    if value.is_none() {
        Ok(())
    } else {
        Err(SolverContractError::RequestMetadataMismatch { field })
    }
}

fn require_no_explicit_finite_evidence(
    carrier: &FiniteDecideCarrierRef,
) -> Result<(), SolverContractError> {
    if carrier.explicit_finite_evidence_hash.is_none()
        && carrier.no_duplicate_evidence_hash.is_none()
        && carrier.complete_evidence_hash.is_none()
    {
        Ok(())
    } else {
        Err(SolverContractError::RequestMetadataMismatch {
            field: "explicit_finite_evidence",
        })
    }
}

fn require_explicit_finite_evidence(
    carrier: &FiniteDecideCarrierRef,
) -> Result<(), SolverContractError> {
    require_present_hash(
        "explicit_finite_evidence_hash",
        carrier.explicit_finite_evidence_hash,
    )?;
    require_present_hash(
        "no_duplicate_evidence_hash",
        carrier.no_duplicate_evidence_hash,
    )?;
    require_present_hash("complete_evidence_hash", carrier.complete_evidence_hash)
}

fn require_present_hash(
    field: &'static str,
    value: Option<Hash>,
) -> Result<(), SolverContractError> {
    match value {
        Some(hash) if !is_zero_hash(&hash) => Ok(()),
        Some(_) | None => Err(SolverContractError::MissingFiniteEvidence { field }),
    }
}

fn validate_universe_params(
    field: &'static str,
    universe_params: &[String],
) -> Result<(), SolverContractError> {
    validate_string_list(field, universe_params)
}

fn validate_string_list(field: &'static str, values: &[String]) -> Result<(), SolverContractError> {
    let mut seen = BTreeSet::new();
    for value in values {
        if value.is_empty() {
            return Err(SolverContractError::NonCanonicalPayloadBytes { field });
        }
        if !seen.insert(value.as_str()) {
            return Err(SolverContractError::DuplicateIdentifier {
                field,
                identifier: value.clone(),
            });
        }
    }
    Ok(())
}

fn validate_u64_list(field: &'static str, values: &[u64]) -> Result<(), SolverContractError> {
    let mut previous = None;
    for value in values {
        if let Some(previous) = previous {
            if *value <= previous {
                return Err(SolverContractError::NonCanonicalPayloadBytes { field });
            }
        }
        previous = Some(*value);
    }
    Ok(())
}

fn require_empty_string_list(
    field: &'static str,
    values: &[String],
) -> Result<(), SolverContractError> {
    if values.is_empty() {
        Ok(())
    } else {
        Err(SolverContractError::NonCanonicalPayloadBytes { field })
    }
}

fn require_empty_u64_list(field: &'static str, values: &[u64]) -> Result<(), SolverContractError> {
    if values.is_empty() {
        Ok(())
    } else {
        Err(SolverContractError::NonCanonicalPayloadBytes { field })
    }
}

fn vector_bool_cardinality(length: u64) -> Result<u64, SolverContractError> {
    if length >= 64 {
        return Err(SolverContractError::ResourceLimitExceeded {
            field: SolverResourceField::InputNodes,
            limit: 63,
            actual: length,
        });
    }
    Ok(1u64 << (length as u32))
}

fn vector_bool_bits_ordinal(bits: &[bool]) -> Result<u64, SolverContractError> {
    let mut ordinal = 0u64;
    for bit in bits {
        ordinal = ordinal
            .checked_mul(2)
            .and_then(|value| value.checked_add(if *bit { 1 } else { 0 }))
            .ok_or(SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                limit: 63,
                actual: bits.len() as u64,
            })?;
    }
    Ok(ordinal)
}

fn origin_debug_ordinal(origin: &FiniteDecideElementOrigin) -> u64 {
    match origin {
        FiniteDecideElementOrigin::BoolFalse => 0,
        FiniteDecideElementOrigin::BoolTrue => 1,
        FiniteDecideElementOrigin::FinOrdinal(ordinal)
        | FiniteDecideElementOrigin::SmallExplicitOrdinal { ordinal } => *ordinal,
        FiniteDecideElementOrigin::VectorBoolBits(bits) => {
            vector_bool_bits_ordinal(bits).unwrap_or(u64::MAX)
        }
        FiniteDecideElementOrigin::ExplicitIndex { .. } => u64::MAX,
    }
}

fn validate_environment_and_policy_hashes(
    environment_hash: Hash,
    policy_hash: Hash,
) -> Result<(), SolverContractError> {
    if is_zero_hash(&environment_hash) {
        return Err(SolverContractError::MissingEnvironmentHash);
    }
    if is_zero_hash(&policy_hash) {
        return Err(SolverContractError::MissingPolicyHash);
    }
    Ok(())
}

fn encode_response_payload_identity_to(
    out: &mut Vec<u8>,
    payload: &SolverResponsePayload,
) -> Result<(), SolverContractError> {
    match payload {
        SolverResponsePayload::Proposed {
            proposal_hash,
            reconstruction_plan,
        } => {
            out.push(0);
            encode_option_hash(out, proposal_hash.as_ref());
            match reconstruction_plan {
                Some(plan) => {
                    out.push(1);
                    encode_hash_to(out, &solver_reconstruction_plan_hash(plan)?);
                }
                None => out.push(0),
            }
        }
        SolverResponsePayload::Unsupported { .. } => out.push(1),
        SolverResponsePayload::Counterexample {
            counterexample_hash,
        } => {
            out.push(2);
            encode_hash_to(out, counterexample_hash);
        }
        SolverResponsePayload::Certificate(SolverAcceptingPayload::CheckedProofTerm(identity)) => {
            out.push(3);
            encode_hash_to(out, &identity.environment_hash);
            encode_hash_to(out, &identity.proof_term_hash);
            encode_hash_to(out, &identity.proof_type_hash);
        }
        SolverResponsePayload::Certificate(
            SolverAcceptingPayload::CheckedCertificateReconstruction(metadata),
        ) => {
            out.push(4);
            encode_hash_to(out, &solver_certificate_metadata_hash(metadata)?);
        }
    }
    Ok(())
}

fn solver_response_payload_name(payload: &SolverResponsePayload) -> &'static str {
    match payload {
        SolverResponsePayload::Proposed { .. } => "Proposed",
        SolverResponsePayload::Unsupported { .. } => "Unsupported",
        SolverResponsePayload::Counterexample { .. } => "Counterexample",
        SolverResponsePayload::Certificate(_) => "Certificate",
    }
}

fn encode_finite_decide_element_to(out: &mut Vec<u8>, element: &FiniteDecideElement) {
    encode_u64_to(out, element.ordinal);
    encode_hash_to(out, &element.element_hash);
    encode_hash_to(out, &element.element_type_hash);
    encode_finite_decide_element_origin_to(out, &element.origin);
}

fn encode_finite_decide_element_origin_to(out: &mut Vec<u8>, origin: &FiniteDecideElementOrigin) {
    match origin {
        FiniteDecideElementOrigin::BoolFalse => out.push(0),
        FiniteDecideElementOrigin::BoolTrue => out.push(1),
        FiniteDecideElementOrigin::FinOrdinal(ordinal) => {
            out.push(2);
            encode_u64_to(out, *ordinal);
        }
        FiniteDecideElementOrigin::VectorBoolBits(bits) => {
            out.push(3);
            encode_len_to(out, bits.len());
            for bit in bits {
                out.push(u8::from(*bit));
            }
        }
        FiniteDecideElementOrigin::ExplicitIndex { index_hash } => {
            out.push(4);
            encode_hash_to(out, index_hash);
        }
        FiniteDecideElementOrigin::SmallExplicitOrdinal { ordinal } => {
            out.push(5);
            encode_u64_to(out, *ordinal);
        }
    }
}

fn encode_option_small_carrier_kind(
    out: &mut Vec<u8>,
    value: Option<FiniteDecideSmallCarrierKind>,
) {
    match value {
        Some(kind) => {
            out.push(1);
            out.push(kind.tag());
        }
        None => out.push(0),
    }
}

fn encode_option_certificate_format(out: &mut Vec<u8>, value: Option<SolverCertificateFormat>) {
    match value {
        Some(format) => {
            out.push(1);
            out.push(format.tag());
        }
        None => out.push(0),
    }
}

fn encode_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            out.push(1);
            encode_u64_to(out, value);
        }
        None => out.push(0),
    }
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(hash) => {
            out.push(1);
            encode_hash_to(out, hash);
        }
        None => out.push(0),
    }
}

fn encode_option_string(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            out.push(1);
            encode_string_to(out, value);
        }
        None => out.push(0),
    }
}

fn encode_string_list_to(out: &mut Vec<u8>, values: &[String]) {
    encode_len_to(out, values.len());
    for value in values {
        encode_string_to(out, value);
    }
}

fn encode_hash_to(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_bytes_to(out: &mut Vec<u8>, bytes: &[u8]) {
    encode_len_to(out, bytes.len());
    out.extend_from_slice(bytes);
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_bytes_to(out, value.as_bytes());
}

fn encode_len_to(out: &mut Vec<u8>, value: usize) {
    encode_u64_to(out, value as u64);
}

fn encode_u64_to(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn encode_i64_to(out: &mut Vec<u8>, value: i64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn hash_with_domain(domain: &str, payload: &[u8]) -> Hash {
    let mut bytes = Vec::with_capacity(domain.len() + 1 + payload.len());
    bytes.extend_from_slice(domain.as_bytes());
    bytes.push(0);
    bytes.extend_from_slice(payload);
    sha256(&bytes)
}

fn sha256(bytes: &[u8]) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut out = [0; 32];
    out.copy_from_slice(&digest);
    out
}

fn hash_u64(value: u64) -> Hash {
    hash_with_domain("npa.solver.u64-debug.v1", &value.to_le_bytes())
}

fn is_zero_hash(hash: &Hash) -> bool {
    hash.iter().all(|byte| *byte == 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::advanced_ai::{
        advanced_ai_smt_certificate_metadata_hash, advanced_ai_smt_encoding_hash,
        advanced_ai_smt_nat_to_int_side_condition, advanced_ai_smt_nat_to_int_side_condition_hash,
        advanced_ai_smt_problem_canonical_bytes, advanced_ai_smt_problem_hash, AdvancedAiGoal,
        AdvancedMachineSmtCertificateCandidate, AdvancedMachineSmtEncodedProblem,
        AdvancedMachineSmtProblemRef, AdvancedMachineSmtProofPayloadRef,
        AdvancedMachineSmtReconstructionPlan, AdvancedSmtCommandProfile, AdvancedSmtEncoderVersion,
        AdvancedSmtReconstructionMetadata, AdvancedSmtRuleRegistryProfile, AdvancedSmtSolver,
    };
    use npa_kernel::{Expr, Level};

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn request() -> SolverRequest {
        SolverRequest {
            version: SolverContractVersion::V1,
            family: SolverFamily::Smt,
            fragment: SolverFragment::SmtQfUfV1,
            profile: SolverProfile::AdvancedSmtMvpV1,
            goal_identity: SolverGoalIdentity {
                goal_hash: hash(1),
                target_hash: hash(2),
            },
            local_context_hash: hash(3),
            environment_hash: hash(4),
            policy_hash: hash(5),
        }
    }

    fn proof_payload_ref() -> SolverProofPayloadRef {
        let canonical_bytes = b"proof-node-table-v1".to_vec();
        SolverProofPayloadRef {
            certificate_format: SolverCertificateFormat::MvpSmtProofNodeTableV1,
            payload_hash: solver_inline_payload_hash(
                SolverCertificateFormat::MvpSmtProofNodeTableV1,
                &canonical_bytes,
            )
            .unwrap(),
            size_bytes: canonical_bytes.len() as u64,
            canonical_bytes: Some(canonical_bytes),
        }
    }

    fn reconstruction_plan() -> SolverReconstructionPlanRef {
        SolverReconstructionPlanRef {
            profile: SolverProfile::AdvancedSmtMvpV1,
            reconstruction_plan_hash: hash(6),
            imported_theory_count: 0,
            step_count: 2,
            step_ids: vec!["s0".to_owned(), "s1".to_owned()],
            final_step_id: Some("s1".to_owned()),
        }
    }

    fn certificate_metadata() -> SolverCertificateMetadata {
        let payload_ref = proof_payload_ref();
        SolverCertificateMetadata {
            family: SolverFamily::Smt,
            fragment: SolverFragment::SmtQfUfV1,
            profile: SolverProfile::AdvancedSmtMvpV1,
            certificate_format: SolverCertificateFormat::MvpSmtProofNodeTableV1,
            environment_hash: hash(4),
            policy_hash: hash(5),
            payload_hash: payload_ref.payload_hash,
            proof_payload_ref_hash: solver_proof_payload_ref_hash(&payload_ref).unwrap(),
            reconstruction_plan_hash: solver_reconstruction_plan_hash(&reconstruction_plan())
                .unwrap(),
        }
    }

    fn certificate_response() -> SolverResponse {
        let certificate = certificate_metadata();
        SolverResponse {
            version: SolverContractVersion::V1,
            status: SolverResponseStatus::Certificate,
            metadata: SolverResponseMetadata {
                request_hash: solver_request_hash(&request()).unwrap(),
                family: certificate.family,
                fragment: certificate.fragment,
                profile: certificate.profile,
                environment_hash: certificate.environment_hash,
                policy_hash: certificate.policy_hash,
                payload_hash: Some(certificate.payload_hash),
                proof_payload_ref_hash: Some(certificate.proof_payload_ref_hash),
                certificate_format: Some(certificate.certificate_format),
                certificate_metadata_hash: Some(
                    solver_certificate_metadata_hash(&certificate).unwrap(),
                ),
                reconstruction_plan_hash: Some(certificate.reconstruction_plan_hash),
            },
            payload: SolverResponsePayload::Certificate(
                SolverAcceptingPayload::CheckedCertificateReconstruction(certificate),
            ),
            advisory: SolverResponseAdvisory::default(),
        }
    }

    fn request_for_resource_policy(policy: &SolverResourcePolicy) -> SolverRequest {
        let mut request = request();
        request.family = policy.family;
        request.fragment = match policy.family {
            SolverFamily::FiniteDecide => SolverFragment::FiniteEnumerationV1,
            SolverFamily::Omega => SolverFragment::PresburgerLinearArithmeticV1,
            SolverFamily::Ring => SolverFragment::SemiringNormalizationV1,
            SolverFamily::Bitblast => SolverFragment::BitVectorBitblastV1,
            SolverFamily::Lrat => SolverFragment::LratUnsatV1,
            SolverFamily::Smt => SolverFragment::SmtQfUfV1,
        };
        request.policy_hash = solver_resource_policy_hash(policy).unwrap();
        request
    }

    fn omega_policy() -> SolverResourcePolicy {
        solver_default_resource_policy(SolverResourcePolicyProfile::OmegaDefaultV1)
    }

    fn omega_request_for_policy(policy: &SolverResourcePolicy) -> SolverRequest {
        let mut request = request_for_resource_policy(policy);
        request.profile = SolverProfile::CheckedCertificateV1;
        request
    }

    fn omega_context(entries: &[(&str, OmegaTermSort)]) -> Vec<OmegaLocalContextEntry> {
        entries
            .iter()
            .map(|(name, sort)| OmegaLocalContextEntry {
                name: (*name).to_owned(),
                ty: match sort {
                    OmegaTermSort::Int => Expr::konst("Int", vec![]),
                    OmegaTermSort::Nat => Expr::konst("Nat", vec![]),
                },
                sort: *sort,
            })
            .collect()
    }

    fn omega_app2(name: &str, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst(name, vec![]), [lhs, rhs])
    }

    fn omega_appn(name: &str, args: Vec<Expr>) -> Expr {
        Expr::apps(Expr::konst(name, vec![]), args)
    }

    fn omega_int_lit(value: i64) -> Expr {
        let name = if value == 0 {
            "Omega.IntLit.z".to_owned()
        } else if value > 0 {
            format!("Omega.IntLit.p{value}")
        } else {
            format!("Omega.IntLit.n{}", value.checked_neg().unwrap())
        };
        Expr::konst(name, vec![])
    }

    fn omega_nat_lit(value: u64) -> Expr {
        let name = if value == 0 {
            "Omega.NatLit.z".to_owned()
        } else {
            format!("Omega.NatLit.p{value}")
        };
        Expr::konst(name, vec![])
    }

    fn ring_nf_policy() -> SolverResourcePolicy {
        solver_default_resource_policy(SolverResourcePolicyProfile::RingNfDefaultV1)
    }

    fn ring_nf_request_for_policy(policy: &SolverResourcePolicy) -> SolverRequest {
        let mut request = request_for_resource_policy(policy);
        request.profile = SolverProfile::ExternalSidecarV1;
        request
    }

    fn ring_nf_context(entries: &[(&str, &str)]) -> Vec<RingNfLocalContextEntry> {
        entries
            .iter()
            .map(|(name, ty)| RingNfLocalContextEntry {
                name: (*name).to_owned(),
                ty: Expr::konst(*ty, vec![]),
            })
            .collect()
    }

    fn ring_nf_app2(name: &str, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst(name, vec![]), [lhs, rhs])
    }

    fn ring_nf_eq(ty: &str, lhs: Expr, rhs: Expr) -> Expr {
        npa_kernel::eq(Level::zero(), Expr::konst(ty, vec![]), lhs, rhs)
    }

    fn ring_nf_int_lit(value: i64) -> Expr {
        let name = if value == 0 {
            "Ring.IntLit.z".to_owned()
        } else if value > 0 {
            format!("Ring.IntLit.p{value}")
        } else {
            format!("Ring.IntLit.n{}", value.checked_neg().unwrap())
        };
        Expr::konst(name, vec![])
    }

    fn ring_nf_nat_lit(value: u64) -> Expr {
        let name = if value == 0 {
            "Ring.NatLit.z".to_owned()
        } else {
            format!("Ring.NatLit.p{value}")
        };
        Expr::konst(name, vec![])
    }

    fn bitblast_policy() -> SolverResourcePolicy {
        solver_default_resource_policy(SolverResourcePolicyProfile::BitblastDefaultV1)
    }

    fn bitblast_request_for_policy(policy: &SolverResourcePolicy) -> SolverRequest {
        let mut request = request_for_resource_policy(policy);
        request.profile = SolverProfile::ExternalSidecarV1;
        request
    }

    fn bitblast_options(
        policy: &SolverResourcePolicy,
        request: &SolverRequest,
    ) -> BitblastEncodingOptions {
        bitblast_encoding_options_from_policy(policy, request, BitblastBackendProfile::CnfTseitinV1)
            .unwrap()
    }

    fn bitblast_bool_type() -> Expr {
        Expr::konst("Bool", vec![])
    }

    fn bitblast_width_lit(width: u64) -> Expr {
        if width == 0 {
            Expr::konst("BitVector.Width.z", vec![])
        } else {
            Expr::konst(format!("BitVector.Width.p{width}"), vec![])
        }
    }

    fn bitblast_bitvector_type(width: u64) -> Expr {
        Expr::apps(
            Expr::konst("BitVector", vec![]),
            [bitblast_width_lit(width)],
        )
    }

    fn bitblast_context(entries: &[(&str, Expr)]) -> Vec<BitblastLocalContextEntry> {
        entries
            .iter()
            .map(|(name, ty)| BitblastLocalContextEntry {
                name: (*name).to_owned(),
                ty: ty.clone(),
            })
            .collect()
    }

    fn bitblast_app1(name: &str, arg: Expr) -> Expr {
        Expr::apps(Expr::konst(name, vec![]), [arg])
    }

    fn bitblast_app2(name: &str, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst(name, vec![]), [lhs, rhs])
    }

    fn bitblast_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
        npa_kernel::eq(Level::zero(), ty, lhs, rhs)
    }

    fn bitblast_bool_problem_fixture(
    ) -> (SolverResourcePolicy, SolverRequest, BitblastEncodedProblem) {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2(
            "Bool.and",
            Expr::bvar(1),
            bitblast_app1("Bool.not", Expr::bvar(0)),
        );
        let problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();
        (policy, request, problem)
    }

    fn bitblast_unsat_problem_fixture_with_policy(
        policy: SolverResourcePolicy,
    ) -> (SolverResourcePolicy, SolverRequest, BitblastEncodedProblem) {
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = Vec::new();
        let target = Expr::konst("Bool.false", vec![]);
        let problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();
        (policy, request, problem)
    }

    fn bitblast_unsat_problem_fixture(
    ) -> (SolverResourcePolicy, SolverRequest, BitblastEncodedProblem) {
        bitblast_unsat_problem_fixture_with_policy(bitblast_policy())
    }

    fn bitblast_proof_identity(
        request: &SolverRequest,
        salt: u8,
    ) -> SolverCheckedProofTermIdentity {
        SolverCheckedProofTermIdentity {
            environment_hash: request.environment_hash,
            proof_term_hash: hash(salt),
            proof_type_hash: request.goal_identity.target_hash,
        }
    }

    fn bitblast_semantic_proof_fixture(
        request: &SolverRequest,
        problem: &BitblastEncodedProblem,
    ) -> BitblastSemanticProofArtifact {
        bitblast_semantic_proof_artifact_for_encoded_problem(
            request,
            problem,
            bitblast_proof_identity(request, 231),
            17,
            512,
            9,
        )
        .unwrap()
    }

    fn bitblast_lrat_payload(bytes: &[u8]) -> SolverProofPayloadRef {
        SolverProofPayloadRef {
            certificate_format: SolverCertificateFormat::LratV1,
            payload_hash: solver_inline_payload_hash(SolverCertificateFormat::LratV1, bytes)
                .unwrap(),
            size_bytes: bytes.len() as u64,
            canonical_bytes: Some(bytes.to_vec()),
        }
    }

    fn bitblast_sat_model_fixture(
        request: &SolverRequest,
        problem: &BitblastEncodedProblem,
    ) -> BitblastSatModelArtifact {
        let variable_count = problem.cnf_artifact.variable_count;
        assert!(
            variable_count <= 16,
            "fixture brute force stays intentionally small"
        );
        for mask in 0..(1u64 << variable_count) {
            let assignments = (1..=variable_count)
                .map(|cnf_variable| BitblastSatModelAssignment {
                    cnf_variable,
                    value: ((mask >> (cnf_variable - 1)) & 1) == 1,
                })
                .collect::<Vec<_>>();
            let output_literal_value =
                bitblast_model_literal_value(&assignments, problem.cnf_artifact.output_literal)
                    .unwrap();
            let model = BitblastSatModelArtifact {
                version: SolverContractVersion::V1,
                request_hash: solver_request_hash(request).unwrap(),
                encoded_problem_hash: bitblast_encoded_problem_hash(problem).unwrap(),
                cnf_artifact_hash: bitblast_cnf_artifact_hash(&problem.cnf_artifact).unwrap(),
                variable_map_hash: bitblast_variable_map_hash(&problem.variable_map).unwrap(),
                assignments,
                output_literal_value,
            };
            if validate_bitblast_sat_model_for_problem(request, problem, &model).is_ok() {
                return model;
            }
        }
        panic!("fixture CNF should be satisfiable");
    }

    fn lrat_policy() -> SolverResourcePolicy {
        solver_default_resource_policy(SolverResourcePolicyProfile::LratDefaultV1)
    }

    fn lrat_request_for_policy(policy: &SolverResourcePolicy) -> SolverRequest {
        let mut request = request_for_resource_policy(policy);
        request.profile = SolverProfile::CheckedCertificateV1;
        request
    }

    fn lrat_lit(variable: u64, positive: bool) -> LratLiteral {
        LratLiteral { variable, positive }
    }

    fn lrat_clause(line_id: u64, literals: Vec<LratLiteral>) -> LratClause {
        LratClause { line_id, literals }
    }

    fn lrat_minimal_unsat_cnf() -> LratCnf {
        LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 1,
            clauses: vec![
                lrat_clause(1, vec![lrat_lit(1, true)]),
                lrat_clause(2, vec![lrat_lit(1, false)]),
            ],
        }
    }

    fn lrat_minimal_unsat_certificate(cnf: &LratCnf) -> LratCertificate {
        LratCertificate {
            version: SolverContractVersion::V1,
            cnf_hash: lrat_cnf_hash(cnf).unwrap(),
            proof_lines: vec![LratProofLine {
                ordinal: 0,
                kind: LratProofLineKind::Add {
                    clause: lrat_clause(3, vec![]),
                    rule: LratProofRule::Rup { hints: vec![1, 2] },
                },
            }],
        }
    }

    fn lrat_rat_cnf() -> LratCnf {
        LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 2,
            clauses: vec![
                lrat_clause(1, vec![lrat_lit(1, true)]),
                lrat_clause(2, vec![lrat_lit(1, false), lrat_lit(2, true)]),
                lrat_clause(3, vec![lrat_lit(2, false)]),
            ],
        }
    }

    fn lrat_rat_deletion_certificate(cnf: &LratCnf) -> LratCertificate {
        LratCertificate {
            version: SolverContractVersion::V1,
            cnf_hash: lrat_cnf_hash(cnf).unwrap(),
            proof_lines: vec![
                LratProofLine {
                    ordinal: 0,
                    kind: LratProofLineKind::Add {
                        clause: lrat_clause(4, vec![lrat_lit(2, true)]),
                        rule: LratProofRule::Rat {
                            pivot: Some(lrat_lit(2, true)),
                            checks: vec![LratRatCheck {
                                clause_id: 3,
                                rup_hints: vec![1, 2, 3],
                            }],
                        },
                    },
                },
                LratProofLine {
                    ordinal: 1,
                    kind: LratProofLineKind::Delete {
                        clause_ids: vec![2],
                    },
                },
                LratProofLine {
                    ordinal: 2,
                    kind: LratProofLineKind::Add {
                        clause: lrat_clause(5, vec![]),
                        rule: LratProofRule::Rup { hints: vec![4, 3] },
                    },
                },
            ],
        }
    }

    fn lrat_empty_clause_rup_certificate(cnf: &LratCnf) -> LratCertificate {
        LratCertificate {
            version: SolverContractVersion::V1,
            cnf_hash: lrat_cnf_hash(cnf).unwrap(),
            proof_lines: vec![LratProofLine {
                ordinal: 0,
                kind: LratProofLineKind::Add {
                    clause: lrat_clause(cnf.clauses.len() as u64 + 1, vec![]),
                    rule: LratProofRule::Rup {
                        hints: (1..=cnf.clauses.len() as u64).collect(),
                    },
                },
            }],
        }
    }

    fn bitblast_lrat_bridge_fixture() -> (
        SolverResourcePolicy,
        SolverRequest,
        SolverResourcePolicy,
        SolverRequest,
        BitblastEncodedProblem,
        BitblastSemanticProofArtifact,
        LratCnf,
        LratCertificate,
    ) {
        let (policy, request, problem) = bitblast_unsat_problem_fixture();
        let semantic_proof = bitblast_semantic_proof_fixture(&request, &problem);
        let lrat_policy = lrat_policy();
        let lrat_request = lrat_request_for_policy(&lrat_policy);
        let lrat_cnf = lrat_cnf_from_bitblast_cnf_artifact(&problem.cnf_artifact).unwrap();
        let lrat_certificate = lrat_empty_clause_rup_certificate(&lrat_cnf);
        (
            policy,
            request,
            lrat_policy,
            lrat_request,
            problem,
            semantic_proof,
            lrat_cnf,
            lrat_certificate,
        )
    }

    fn ring_nf_reconstruction_problem(
        policy: &SolverResourcePolicy,
        request: &SolverRequest,
        profile: RingNfAlgebraProfile,
        context: &[RingNfLocalContextEntry],
        target: &Expr,
    ) -> RingNfNormalizedProblem {
        let options = ring_nf_normalization_options_from_policy(policy, request, profile).unwrap();
        ring_nf_normalize_problem(request, context, target, &options).unwrap()
    }

    fn ring_nf_variable_environment(
        problem: &RingNfNormalizedProblem,
    ) -> Vec<RingNfVariableEnvironmentEntry> {
        problem
            .variables
            .iter()
            .map(|variable| RingNfVariableEnvironmentEntry {
                variable_ordinal: variable.ordinal,
                source_core_expr_hash: variable.source_core_expr_hash,
                type_hash: variable.type_hash,
                value_hash: hash(160 + variable.ordinal as u8),
            })
            .collect()
    }

    fn ring_nf_algebra_law_refs(problem: &RingNfNormalizedProblem) -> Vec<RingNfAlgebraLawRef> {
        ring_nf_required_algebra_laws(problem)
            .into_iter()
            .map(|law| RingNfAlgebraLawRef {
                law,
                profile: problem.algebra_profile,
                theorem_hash: hash(180 + law.tag()),
                theorem_type_hash: hash(200 + law.tag()),
            })
            .collect()
    }

    fn ring_nf_proof_artifact(
        request: &SolverRequest,
        problem: &RingNfNormalizedProblem,
    ) -> RingNfProofArtifact {
        let variable_environment = ring_nf_variable_environment(problem);
        let algebra_law_refs = ring_nf_algebra_law_refs(problem);
        RingNfProofArtifact {
            version: SolverContractVersion::V1,
            request_hash: solver_request_hash(request).unwrap(),
            normalized_problem_hash: ring_nf_normalized_problem_hash(problem).unwrap(),
            profile_hash: ring_nf_profile_hash(problem.algebra_profile, problem.coefficient_domain)
                .unwrap(),
            variable_environment_hash: ring_nf_variable_environment_hash(&variable_environment)
                .unwrap(),
            policy_hash: request.policy_hash,
            lhs_reflected_expr_hash: ring_nf_reflected_expr_hash(&problem.equation.lhs_reflected)
                .unwrap(),
            rhs_reflected_expr_hash: ring_nf_reflected_expr_hash(&problem.equation.rhs_reflected)
                .unwrap(),
            lhs_normal_form_hash: ring_nf_polynomial_hash(&problem.equation.lhs_normal_form)
                .unwrap(),
            rhs_normal_form_hash: ring_nf_polynomial_hash(&problem.equation.rhs_normal_form)
                .unwrap(),
            difference_normal_form_hash: problem
                .equation
                .difference_normal_form
                .as_ref()
                .map(ring_nf_polynomial_hash)
                .transpose()
                .unwrap(),
            variable_environment,
            algebra_law_refs,
            proof_identity: SolverCheckedProofTermIdentity {
                environment_hash: request.environment_hash,
                proof_term_hash: hash(220),
                proof_type_hash: request.goal_identity.target_hash,
            },
            generated_term_nodes: problem.normalized_nodes + 17,
            proof_bytes: 512,
            proof_steps: problem.normalized_nodes + 3,
        }
    }

    #[test]
    fn bitblast_encoding_bool_formula_has_stable_variable_map_and_cnf_identity() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2(
            "Bool.and",
            Expr::bvar(1),
            bitblast_app1("Bool.not", Expr::bvar(0)),
        );

        let problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();
        let again = bitblast_encode_problem(&request, &context, &target, &options).unwrap();

        validate_bitblast_encoded_problem(&problem).unwrap();
        assert_eq!(
            bitblast_encoded_problem_hash(&problem).unwrap(),
            bitblast_encoded_problem_hash(&again).unwrap()
        );
        assert_eq!(
            problem.operation_profile,
            BitblastOperationProfile::BoolFormulaV1
        );
        assert_eq!(problem.variable_map.len(), 2);
        assert_eq!(problem.variable_map[0].variable_ordinal, 0);
        assert_eq!(problem.variable_map[0].bit_width, 1);
        assert_eq!(problem.variable_map[0].tseitin_variable_start, 1);
        assert_eq!(problem.variable_map[1].variable_ordinal, 1);
        assert_eq!(problem.variable_map[1].tseitin_variable_start, 2);
        assert_eq!(
            problem.cnf_artifact.root_reflected_expr_hash,
            bitblast_reflected_expr_hash(&problem.root).unwrap()
        );
        assert_eq!(
            problem.cnf_artifact.variable_map_hash,
            bitblast_variable_map_hash(&problem.variable_map).unwrap()
        );
        assert_eq!(
            problem.cnf_artifact.semantic_plan_hash,
            bitblast_semantic_plan_hash(&problem.semantic_plan).unwrap()
        );
        assert!(matches!(
            problem.cnf_artifact.clauses.last().unwrap().role,
            BitblastClauseRole::OutputAssertion
        ));
        let usage = bitblast_resource_usage_from_encoded_problem(&problem).unwrap();
        assert_eq!(usage.cnf_variables, problem.cnf_artifact.variable_count);
        assert_eq!(usage.cnf_clauses, problem.cnf_artifact.clauses.len() as u64);
    }

    #[test]
    fn bitblast_encoding_fixed_width_bitvector_equality_tracks_bits() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let bv4 = bitblast_bitvector_type(4);
        let context = bitblast_context(&[("x", bv4.clone()), ("y", bv4.clone())]);
        let target = bitblast_eq(bv4, Expr::bvar(1), Expr::bvar(0));

        let problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();

        validate_bitblast_encoded_problem(&problem).unwrap();
        assert_eq!(
            problem.operation_profile,
            BitblastOperationProfile::MixedBoolBitVectorV1
        );
        assert_eq!(problem.variable_map.len(), 2);
        assert_eq!(problem.variable_map[0].bit_width, 4);
        assert_eq!(problem.variable_map[0].bit_offset, 0);
        assert_eq!(problem.variable_map[0].tseitin_variable_start, 1);
        assert_eq!(problem.variable_map[1].bit_width, 4);
        assert_eq!(problem.variable_map[1].bit_offset, 4);
        assert_eq!(problem.variable_map[1].tseitin_variable_start, 5);
        assert!(problem.cnf_artifact.variable_count >= 8);
        assert!(problem
            .cnf_artifact
            .clauses
            .iter()
            .any(|clause| clause.role == BitblastClauseRole::TseitinDefinition));
        assert_eq!(
            bitblast_variable_map_hash(&problem.variable_map).unwrap(),
            problem.semantic_plan.variable_map_hash
        );
    }

    #[test]
    fn bitblast_encoding_rejects_structural_width_mismatch() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let bv4 = bitblast_bitvector_type(4);
        let bv8 = bitblast_bitvector_type(8);
        let context = bitblast_context(&[("x", bv4.clone()), ("y", bv8)]);
        let target = bitblast_eq(bv4, Expr::bvar(1), Expr::bvar(0));

        let err = bitblast_encode_problem(&request, &context, &target, &options)
            .expect_err("bitblast should reject mismatched structural widths");

        assert!(matches!(
            err,
            SolverContractError::BitblastWidthMismatch {
                expected_width: 4,
                actual_width: 8
            }
        ));
    }

    #[test]
    fn bitblast_encoding_rejects_unsupported_operator_before_handoff() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let bv4 = bitblast_bitvector_type(4);
        let context = bitblast_context(&[("x", bv4.clone()), ("y", bv4.clone())]);
        let target = bitblast_eq(
            bv4,
            bitblast_app2("BitVector.add", Expr::bvar(1), Expr::bvar(0)),
            Expr::bvar(1),
        );

        let err = bitblast_encode_problem(&request, &context, &target, &options)
            .expect_err("unsupported bit-vector add must fail before SAT handoff");

        assert!(matches!(
            err,
            SolverContractError::UnsupportedBitblastOperator { operator }
                if operator == "BitVector.add"
        ));
    }

    #[test]
    fn bitblast_encoding_rejects_stale_variable_map() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2("Bool.or", Expr::bvar(1), Expr::bvar(0));
        let mut problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();
        problem.variable_map[1].tseitin_variable_start += 1;

        let err = validate_bitblast_encoded_problem(&problem)
            .expect_err("stale variable map ordering must reject");

        assert!(matches!(
            err,
            SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_variable_map_tseitin_start"
            }
        ));
    }

    #[test]
    fn bitblast_encoding_rejects_stale_reflected_variable_identity() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2("Bool.or", Expr::bvar(1), Expr::bvar(0));
        let mut problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();

        let BitblastReflectedExpr::Binary { lhs, .. } = &mut problem.root else {
            panic!("fixture should encode as a binary Bool formula");
        };
        let BitblastReflectedExpr::Variable {
            source_core_expr_hash,
            ..
        } = lhs.as_mut()
        else {
            panic!("fixture lhs should be a reflected variable");
        };
        *source_core_expr_hash = hash(250);

        let err = validate_bitblast_encoded_problem(&problem)
            .expect_err("stale reflected variable identity must reject");

        assert!(matches!(
            err,
            SolverContractError::MismatchedHash {
                field: "bitblast_variable_source_core_expr_hash",
                ..
            }
        ));
    }

    #[test]
    fn bitblast_encoding_rejects_missing_output_assertion_clause() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2("Bool.and", Expr::bvar(1), Expr::bvar(0));
        let mut problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();
        problem.cnf_artifact.clauses.pop();

        let err = validate_bitblast_encoded_problem(&problem)
            .expect_err("CNF artifacts must end with the declared output assertion");

        assert!(matches!(
            err,
            SolverContractError::NonCanonicalPayloadBytes {
                field: "bitblast_cnf_output_assertion"
            }
        ));
    }

    #[test]
    fn bitblast_encoding_rejects_input_and_cnf_budget_exhaustion() {
        let policy = bitblast_policy();
        let request = bitblast_request_for_policy(&policy);
        let mut options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2("Bool.and", Expr::bvar(1), Expr::bvar(0));

        options.max_input_nodes = 2;
        let input_err = bitblast_encode_problem(&request, &context, &target, &options)
            .expect_err("bitblast should charge input AST nodes");
        assert!(matches!(
            input_err,
            SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                ..
            }
        ));

        let mut options = bitblast_options(&policy, &request);
        options.max_cnf_clauses = 1;
        let cnf_err = bitblast_encode_problem(&request, &context, &target, &options)
            .expect_err("bitblast should charge generated CNF clauses");
        assert!(matches!(
            cnf_err,
            SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::CnfClauses,
                ..
            }
        ));
    }

    #[test]
    fn bitblast_reconstruction_rejects_unbridged_lrat_payload_contract() {
        let (policy, request, problem) = bitblast_bool_problem_fixture();
        let semantic_proof = bitblast_semantic_proof_fixture(&request, &problem);
        let handoff = bitblast_sat_handoff_for_encoded_problem(&request, &policy, &problem)
            .expect("bitblast handoff should bind canonical CNF and request metadata");
        let payload = bitblast_lrat_payload(b"lrat checked elsewhere\n");

        validate_bitblast_sat_handoff_for_problem(&request, &policy, &problem, &handoff).unwrap();
        assert!(handoff.canonical_cnf_bytes.starts_with(b"p cnf "));
        assert_eq!(
            handoff.canonical_cnf_hash,
            bitblast_canonical_cnf_hash(&problem.cnf_artifact).unwrap()
        );
        validate_bitblast_semantic_proof_artifact_for_problem(&request, &problem, &semantic_proof)
            .unwrap();

        let err = bitblast_checked_certificate_response_from_artifacts(
            &request,
            &policy,
            &problem,
            &semantic_proof,
            &payload,
        )
        .expect_err("unbridged LRAT payloads must not produce accepting bitblast evidence");

        assert!(matches!(
            err,
            SolverContractError::UnsupportedBitblastFragment { reason }
                if reason.contains("checked LRAT soundness bridge")
        ));
    }

    #[test]
    fn bitblast_reconstruction_sat_model_is_diagnostic_counterexample_not_accepting() {
        let (policy, request, problem) = bitblast_bool_problem_fixture();
        let model = bitblast_sat_model_fixture(&request, &problem);

        let response =
            bitblast_counterexample_response_from_model(&request, &policy, &problem, &model)
                .expect("satisfying SAT model should become a diagnostic counterexample artifact");

        assert_eq!(response.status, SolverResponseStatus::Counterexample);
        assert_eq!(
            solver_response_accepting_payload(&response),
            Err(SolverContractError::NonAcceptingStatusCannotVerify {
                status: SolverResponseStatus::Counterexample
            })
        );
        assert!(response.metadata.certificate_format.is_none());
        assert!(response.metadata.reconstruction_plan_hash.is_none());
    }

    #[test]
    fn bitblast_reconstruction_rejects_cnf_hash_mismatch() {
        let (policy, request, problem) = bitblast_bool_problem_fixture();
        let mut handoff =
            bitblast_sat_handoff_for_encoded_problem(&request, &policy, &problem).unwrap();
        handoff.cnf_artifact_hash = hash(232);

        let err = validate_bitblast_sat_handoff_for_problem(&request, &policy, &problem, &handoff)
            .expect_err("stale CNF hash must reject before SAT handoff");

        assert!(matches!(
            err,
            SolverContractError::MismatchedHash {
                field: "bitblast_handoff_cnf_artifact_hash",
                ..
            }
        ));
    }

    #[test]
    fn bitblast_reconstruction_enforces_cnf_handoff_output_budget() {
        let mut policy = bitblast_policy();
        policy.max_output_bytes = 4;
        let request = bitblast_request_for_policy(&policy);
        let options = bitblast_options(&policy, &request);
        let context = bitblast_context(&[("x", bitblast_bool_type()), ("y", bitblast_bool_type())]);
        let target = bitblast_app2("Bool.or", Expr::bvar(1), Expr::bvar(0));
        let problem = bitblast_encode_problem(&request, &context, &target, &options).unwrap();

        let err = bitblast_sat_handoff_for_encoded_problem(&request, &policy, &problem)
            .expect_err("canonical CNF handoff bytes must respect output budget");

        assert!(matches!(
            err,
            SolverContractError::OutputLimit {
                limit_bytes: 4,
                actual_bytes
            } if actual_bytes > 4
        ));
    }

    #[test]
    fn bitblast_reconstruction_rejects_variable_map_mismatch() {
        let (_policy, request, problem) = bitblast_bool_problem_fixture();
        let mut semantic_proof = bitblast_semantic_proof_fixture(&request, &problem);
        semantic_proof.variable_map_hash = hash(233);
        semantic_proof.steps = bitblast_reconstruction_steps_for_hashes(
            semantic_proof.root_reflected_expr_hash,
            semantic_proof.variable_map_hash,
            semantic_proof.circuit_hash,
            semantic_proof.semantic_plan_hash,
            semantic_proof.cnf_artifact_hash,
            semantic_proof.final_goal_hash,
        );

        let err = validate_bitblast_semantic_proof_artifact_for_problem(
            &request,
            &problem,
            &semantic_proof,
        )
        .expect_err("semantic proof must bind the variable map identity");

        assert!(matches!(
            err,
            SolverContractError::MismatchedHash {
                field: "bitblast_semantic_proof_variable_map_hash",
                ..
            }
        ));
    }

    #[test]
    fn bitblast_reconstruction_rejects_malformed_model() {
        let (_policy, request, problem) = bitblast_bool_problem_fixture();
        let mut model = bitblast_sat_model_fixture(&request, &problem);
        model.assignments.pop();

        let err = validate_bitblast_sat_model_for_problem(&request, &problem, &model)
            .expect_err("SAT models must assign every CNF variable in canonical order");

        assert_eq!(
            err,
            SolverContractError::MissingBitblastEvidence {
                field: "bitblast_sat_model_assignment_count"
            }
        );
    }

    #[test]
    fn bitblast_reconstruction_rejects_missing_semantic_preservation_proof() {
        let (_policy, request, problem) = bitblast_bool_problem_fixture();
        let mut semantic_proof = bitblast_semantic_proof_fixture(&request, &problem);
        semantic_proof.steps.clear();

        let err = validate_bitblast_semantic_proof_artifact_for_problem(
            &request,
            &problem,
            &semantic_proof,
        )
        .expect_err("semantic-preservation proof steps are mandatory");

        assert_eq!(
            err,
            SolverContractError::MissingBitblastEvidence {
                field: "bitblast_semantic_proof_steps"
            }
        );
    }

    #[test]
    fn bitblast_reconstruction_enforces_certificate_size_budget() {
        let mut policy = bitblast_policy();
        policy.max_certificate_bytes = 4;
        let (policy, request, problem) = bitblast_unsat_problem_fixture_with_policy(policy);
        let semantic_proof = bitblast_semantic_proof_fixture(&request, &problem);
        let lrat_policy = lrat_policy();
        let lrat_request = lrat_request_for_policy(&lrat_policy);
        let lrat_cnf = lrat_cnf_from_bitblast_cnf_artifact(&problem.cnf_artifact).unwrap();
        let lrat_certificate = lrat_empty_clause_rup_certificate(&lrat_cnf);

        let err = bitblast_lrat_checked_certificate_response_from_artifacts(
            BitblastLratSoundnessBridgeInput {
                request: &request,
                policy: &policy,
                lrat_request: &lrat_request,
                lrat_policy: &lrat_policy,
                problem: &problem,
                semantic_proof: &semantic_proof,
                lrat_cnf: &lrat_cnf,
                lrat_certificate: &lrat_certificate,
            },
        )
        .expect_err("certificate bytes must be checked before accepting bitblast output");

        assert!(matches!(
            err,
            SolverContractError::CertificateTooLarge {
                limit_bytes: 4,
                actual_bytes,
            } if actual_bytes > 4
        ));
    }

    #[test]
    fn solver_raw_unsat_rejected_for_bitblast_reconstruction() {
        let (policy, request, problem) = bitblast_bool_problem_fixture();
        let semantic_proof = bitblast_semantic_proof_fixture(&request, &problem);
        let raw_unsat = SolverProofPayloadRef {
            certificate_format: SolverCertificateFormat::SolverResultOnlyV1,
            payload_hash: solver_inline_payload_hash(
                SolverCertificateFormat::SolverResultOnlyV1,
                b"unsat\n",
            )
            .unwrap(),
            size_bytes: b"unsat\n".len() as u64,
            canonical_bytes: Some(b"unsat\n".to_vec()),
        };

        let err = bitblast_checked_certificate_response_from_artifacts(
            &request,
            &policy,
            &problem,
            &semantic_proof,
            &raw_unsat,
        )
        .expect_err("raw UNSAT is not a checked SAT/LRAT certificate");

        assert_eq!(
            err,
            SolverContractError::RequestMetadataMismatch {
                field: "certificate_format",
            }
        );

        let metadata = SolverCertificateMetadata {
            family: SolverFamily::Bitblast,
            fragment: SolverFragment::BitVectorBitblastV1,
            profile: request.profile,
            certificate_format: SolverCertificateFormat::SolverResultOnlyV1,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            payload_hash: raw_unsat.payload_hash,
            proof_payload_ref_hash: solver_proof_payload_ref_hash(&raw_unsat).unwrap(),
            reconstruction_plan_hash: bitblast_semantic_proof_artifact_hash(&semantic_proof)
                .unwrap(),
        };
        assert_eq!(
            validate_solver_certificate_metadata(&metadata),
            Err(SolverContractError::RequestMetadataMismatch {
                field: "certificate_format",
            })
        );
    }

    #[test]
    fn lrat_soundness_bridge_derives_cnf_unsat_theorem_from_checked_lrat() {
        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let cnf = lrat_minimal_unsat_cnf();
        let certificate = lrat_minimal_unsat_certificate(&cnf);

        let bridge = lrat_cnf_unsat_bridge_artifact(&request, &policy, &cnf, &certificate)
            .expect("checked LRAT certificate should derive a CNF-unsat bridge");
        let check = lrat_check_certificate(&request, &policy, &cnf, &certificate).unwrap();
        let check_hash = lrat_check_artifact_hash(&check).unwrap();

        assert_eq!(bridge.cnf_hash, lrat_cnf_hash(&cnf).unwrap());
        assert_eq!(
            bridge.certificate_hash,
            lrat_certificate_hash(&certificate).unwrap()
        );
        assert_eq!(bridge.lrat_check_artifact_hash, check_hash);
        assert_eq!(bridge.empty_clause_line_id, check.empty_clause_line_id);
        assert_eq!(
            bridge.cnf_unsat_theorem_hash,
            lrat_cnf_unsat_theorem_hash(bridge.cnf_hash, check_hash, bridge.empty_clause_line_id)
                .unwrap()
        );
        validate_lrat_cnf_unsat_bridge_artifact(&request, &policy, &cnf, &certificate, &bridge)
            .unwrap();
        assert_eq!(
            lrat_cnf_unsat_bridge_hash(&bridge).unwrap(),
            lrat_cnf_unsat_bridge_hash(&bridge).unwrap()
        );
    }

    #[test]
    fn lrat_soundness_bridge_rejects_malformed_lrat_certificate() {
        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let cnf = lrat_minimal_unsat_cnf();
        let mut certificate = lrat_minimal_unsat_certificate(&cnf);
        let LratProofLineKind::Add {
            rule: LratProofRule::Rup { hints },
            ..
        } = &mut certificate.proof_lines[0].kind
        else {
            panic!("fixture should use a RUP line");
        };
        hints[0] = 99;

        assert_eq!(
            lrat_cnf_unsat_bridge_artifact(&request, &policy, &cnf, &certificate),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::HintOutOfBounds {
                    line_id: 3,
                    hint_id: 99,
                },
            })
        );
    }

    #[test]
    fn bitblast_lrat_end_to_end_accepts_checked_lrat_and_binds_bridge_metadata() {
        let (
            policy,
            request,
            lrat_policy,
            lrat_request,
            problem,
            semantic_proof,
            lrat_cnf,
            lrat_certificate,
        ) = bitblast_lrat_bridge_fixture();

        let bridge = bitblast_lrat_soundness_bridge_artifact(BitblastLratSoundnessBridgeInput {
            request: &request,
            policy: &policy,
            lrat_request: &lrat_request,
            lrat_policy: &lrat_policy,
            problem: &problem,
            semantic_proof: &semantic_proof,
            lrat_cnf: &lrat_cnf,
            lrat_certificate: &lrat_certificate,
        })
        .expect("bitblast LRAT bridge should bind the checked CNF proof to the original goal");
        let response = bitblast_lrat_checked_certificate_response_from_artifacts(
            BitblastLratSoundnessBridgeInput {
                request: &request,
                policy: &policy,
                lrat_request: &lrat_request,
                lrat_policy: &lrat_policy,
                problem: &problem,
                semantic_proof: &semantic_proof,
                lrat_cnf: &lrat_cnf,
                lrat_certificate: &lrat_certificate,
            },
        )
        .expect("bridged bitblast LRAT proof should produce accepting certificate metadata");

        assert_eq!(response.status, SolverResponseStatus::Certificate);
        let SolverResponsePayload::Certificate(
            SolverAcceptingPayload::CheckedCertificateReconstruction(metadata),
        ) = &response.payload
        else {
            panic!("bitblast LRAT bridge should return checked certificate metadata");
        };
        let payload = lrat_proof_payload_ref(&lrat_certificate).unwrap();
        let plan = bitblast_lrat_reconstruction_plan_from_bridge(&semantic_proof, &bridge).unwrap();
        assert_eq!(metadata.family, SolverFamily::Bitblast);
        assert_eq!(metadata.certificate_format, SolverCertificateFormat::LratV1);
        assert_eq!(metadata.profile, request.profile);
        assert_eq!(metadata.policy_hash, request.policy_hash);
        assert_eq!(metadata.payload_hash, payload.payload_hash);
        assert_eq!(
            metadata.proof_payload_ref_hash,
            solver_proof_payload_ref_hash(&payload).unwrap()
        );
        assert_eq!(
            metadata.reconstruction_plan_hash,
            solver_reconstruction_plan_hash(&plan).unwrap()
        );
        assert_eq!(
            bridge.variable_map_hash,
            bitblast_variable_map_hash(&problem.variable_map).unwrap()
        );
        assert_eq!(bridge.lrat_cnf_hash, lrat_cnf_hash(&lrat_cnf).unwrap());
        assert_eq!(bridge.final_goal_hash, request.goal_identity.target_hash);
        assert!(solver_response_accepting_payload(&response).is_ok());
    }

    #[test]
    fn bitblast_lrat_end_to_end_rejects_malformed_lrat_wrong_cnf_and_raw_unsat() {
        let (
            policy,
            request,
            lrat_policy,
            lrat_request,
            problem,
            semantic_proof,
            lrat_cnf,
            mut lrat_certificate,
        ) = bitblast_lrat_bridge_fixture();

        let LratProofLineKind::Add {
            rule: LratProofRule::Rup { hints },
            ..
        } = &mut lrat_certificate.proof_lines[0].kind
        else {
            panic!("fixture should use a RUP line");
        };
        hints[1] = 99;
        assert!(matches!(
            bitblast_lrat_checked_certificate_response_from_artifacts(
                BitblastLratSoundnessBridgeInput {
                    request: &request,
                    policy: &policy,
                    lrat_request: &lrat_request,
                    lrat_policy: &lrat_policy,
                    problem: &problem,
                    semantic_proof: &semantic_proof,
                    lrat_cnf: &lrat_cnf,
                    lrat_certificate: &lrat_certificate,
                },
            ),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::HintOutOfBounds { .. }
            })
        ));

        let wrong_cnf = lrat_minimal_unsat_cnf();
        let wrong_certificate = lrat_minimal_unsat_certificate(&wrong_cnf);
        assert!(matches!(
            bitblast_lrat_checked_certificate_response_from_artifacts(
                BitblastLratSoundnessBridgeInput {
                    request: &request,
                    policy: &policy,
                    lrat_request: &lrat_request,
                    lrat_policy: &lrat_policy,
                    problem: &problem,
                    semantic_proof: &semantic_proof,
                    lrat_cnf: &wrong_cnf,
                    lrat_certificate: &wrong_certificate,
                },
            ),
            Err(SolverContractError::MismatchedHash {
                field: "bitblast_lrat_cnf_hash",
                ..
            })
        ));

        let raw_unsat = SolverProofPayloadRef {
            certificate_format: SolverCertificateFormat::SolverResultOnlyV1,
            payload_hash: solver_inline_payload_hash(
                SolverCertificateFormat::SolverResultOnlyV1,
                b"unsat\n",
            )
            .unwrap(),
            size_bytes: b"unsat\n".len() as u64,
            canonical_bytes: Some(b"unsat\n".to_vec()),
        };
        assert_eq!(
            bitblast_checked_certificate_response_from_artifacts(
                &request,
                &policy,
                &problem,
                &semantic_proof,
                &raw_unsat,
            ),
            Err(SolverContractError::RequestMetadataMismatch {
                field: "certificate_format",
            })
        );
    }

    #[test]
    fn bitblast_lrat_end_to_end_rejects_wrong_variable_map_and_semantic_bridge_mismatch() {
        let (
            policy,
            request,
            lrat_policy,
            lrat_request,
            mut problem,
            mut semantic_proof,
            lrat_cnf,
            lrat_certificate,
        ) = bitblast_lrat_bridge_fixture();

        problem.cnf_artifact.variable_map_hash = hash(245);
        assert!(matches!(
            bitblast_lrat_checked_certificate_response_from_artifacts(
                BitblastLratSoundnessBridgeInput {
                    request: &request,
                    policy: &policy,
                    lrat_request: &lrat_request,
                    lrat_policy: &lrat_policy,
                    problem: &problem,
                    semantic_proof: &semantic_proof,
                    lrat_cnf: &lrat_cnf,
                    lrat_certificate: &lrat_certificate,
                },
            ),
            Err(SolverContractError::MismatchedHash {
                field: "bitblast_cnf_variable_map_hash",
                ..
            })
        ));

        let (
            policy,
            request,
            lrat_policy,
            lrat_request,
            problem,
            _semantic_proof,
            lrat_cnf,
            lrat_certificate,
        ) = bitblast_lrat_bridge_fixture();
        semantic_proof.final_goal_hash = hash(246);
        semantic_proof.steps = bitblast_reconstruction_steps_for_hashes(
            semantic_proof.root_reflected_expr_hash,
            semantic_proof.variable_map_hash,
            semantic_proof.circuit_hash,
            semantic_proof.semantic_plan_hash,
            semantic_proof.cnf_artifact_hash,
            semantic_proof.final_goal_hash,
        );
        assert!(matches!(
            bitblast_lrat_checked_certificate_response_from_artifacts(
                BitblastLratSoundnessBridgeInput {
                    request: &request,
                    policy: &policy,
                    lrat_request: &lrat_request,
                    lrat_policy: &lrat_policy,
                    problem: &problem,
                    semantic_proof: &semantic_proof,
                    lrat_cnf: &lrat_cnf,
                    lrat_certificate: &lrat_certificate,
                },
            ),
            Err(SolverContractError::MismatchedHash {
                field: "bitblast_semantic_proof_final_goal_hash",
                ..
            })
        ));
    }

    #[test]
    fn lrat_checker_minimal_unsat_proof_derives_empty_clause_and_hashes() {
        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let cnf = lrat_minimal_unsat_cnf();
        let certificate = lrat_minimal_unsat_certificate(&cnf);

        let artifact = lrat_check_certificate(&request, &policy, &cnf, &certificate)
            .expect("minimal LRAT proof should derive the empty clause");

        assert_eq!(artifact.empty_clause_line_id, 3);
        assert_eq!(artifact.original_clause_count, 2);
        assert_eq!(artifact.proof_line_count, 1);
        assert_eq!(artifact.rup_step_count, 1);
        assert_eq!(artifact.rat_step_count, 0);
        assert_eq!(artifact.deletion_step_count, 0);
        assert_eq!(artifact.cnf_hash, lrat_cnf_hash(&cnf).unwrap());
        assert_eq!(
            artifact.certificate_hash,
            lrat_certificate_hash(&certificate).unwrap()
        );
        assert_eq!(
            lrat_check_artifact_hash(&artifact).unwrap(),
            lrat_check_artifact_hash(&artifact).unwrap()
        );
        let payload = lrat_proof_payload_ref(&certificate).unwrap();
        validate_lrat_proof_payload_ref(&payload).unwrap();
        assert_eq!(payload.certificate_format, SolverCertificateFormat::LratV1);
    }

    #[test]
    fn lrat_checker_accepts_rat_and_deletion_heavy_proof() {
        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let cnf = lrat_rat_cnf();
        let certificate = lrat_rat_deletion_certificate(&cnf);

        let artifact = lrat_check_certificate(&request, &policy, &cnf, &certificate)
            .expect("RAT addition plus deletion should still derive the empty clause");

        assert_eq!(artifact.empty_clause_line_id, 5);
        assert_eq!(artifact.proof_line_count, 3);
        assert_eq!(artifact.rup_step_count, 1);
        assert_eq!(artifact.rat_step_count, 1);
        assert_eq!(artifact.deletion_step_count, 1);
    }

    #[test]
    fn lrat_checker_enforces_certificate_memory_step_and_hint_budgets() {
        let base_policy = lrat_policy();
        let cnf = lrat_minimal_unsat_cnf();
        let certificate = lrat_minimal_unsat_certificate(&cnf);

        let mut certificate_policy = base_policy.clone();
        certificate_policy.max_certificate_bytes = 4;
        let request = lrat_request_for_policy(&certificate_policy);
        assert!(matches!(
            lrat_check_certificate(&request, &certificate_policy, &cnf, &certificate),
            Err(SolverContractError::CertificateTooLarge {
                limit_bytes: 4,
                actual_bytes
            }) if actual_bytes > 4
        ));

        let mut memory_policy = base_policy.clone();
        memory_policy.max_memory_bytes = 1;
        let request = lrat_request_for_policy(&memory_policy);
        assert!(matches!(
            lrat_check_certificate(&request, &memory_policy, &cnf, &certificate),
            Err(SolverContractError::MemoryLimit {
                limit_bytes: 1,
                actual_bytes
            }) if actual_bytes > 1
        ));

        let mut proof_line_policy = base_policy.clone();
        proof_line_policy.max_proof_steps = 0;
        let request = lrat_request_for_policy(&proof_line_policy);
        assert_eq!(
            lrat_check_certificate(&request, &proof_line_policy, &cnf, &certificate),
            Err(SolverContractError::ProofSearchExhausted {
                field: SolverResourceField::ProofSteps,
                limit: 0,
                actual: 1,
            })
        );

        let mut hint_policy = base_policy;
        hint_policy.max_rule_count = 1;
        let request = lrat_request_for_policy(&hint_policy);
        assert_eq!(
            lrat_check_certificate(&request, &hint_policy, &cnf, &certificate),
            Err(SolverContractError::ProofSearchExhausted {
                field: SolverResourceField::RuleCount,
                limit: 1,
                actual: 2,
            })
        );
    }

    #[test]
    fn lrat_malformed_rejects_clause_normalization_duplicate_and_tautology() {
        let duplicate = LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 1,
            clauses: vec![lrat_clause(1, vec![lrat_lit(1, true), lrat_lit(1, true)])],
        };
        assert_eq!(
            validate_lrat_cnf(&duplicate),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::DuplicateLiteral {
                    line_id: 1,
                    literal: lrat_lit(1, true),
                },
            })
        );

        let tautology = LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 1,
            clauses: vec![lrat_clause(1, vec![lrat_lit(1, false), lrat_lit(1, true)])],
        };
        assert_eq!(
            validate_lrat_cnf(&tautology),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::TautologicalClause {
                    line_id: 1,
                    variable: 1,
                },
            })
        );

        let noncanonical_order = LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 2,
            clauses: vec![lrat_clause(1, vec![lrat_lit(2, true), lrat_lit(1, true)])],
        };
        assert_eq!(
            validate_lrat_cnf(&noncanonical_order),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::NonCanonicalLiteralOrder { line_id: 1 },
            })
        );
    }

    #[test]
    fn lrat_malformed_rejects_bad_hint_and_out_of_bounds_reference() {
        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let bad_hint_cnf = LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 2,
            clauses: vec![lrat_clause(1, vec![lrat_lit(1, true), lrat_lit(2, true)])],
        };
        let bad_hint_certificate = LratCertificate {
            version: SolverContractVersion::V1,
            cnf_hash: lrat_cnf_hash(&bad_hint_cnf).unwrap(),
            proof_lines: vec![LratProofLine {
                ordinal: 0,
                kind: LratProofLineKind::Add {
                    clause: lrat_clause(2, vec![]),
                    rule: LratProofRule::Rup { hints: vec![1] },
                },
            }],
        };
        assert_eq!(
            lrat_check_certificate(&request, &policy, &bad_hint_cnf, &bad_hint_certificate),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::BadRupHint {
                    line_id: 2,
                    hint_id: 1,
                },
            })
        );

        let cnf = lrat_minimal_unsat_cnf();
        let mut certificate = lrat_minimal_unsat_certificate(&cnf);
        let LratProofLineKind::Add {
            rule: LratProofRule::Rup { hints },
            ..
        } = &mut certificate.proof_lines[0].kind
        else {
            panic!("fixture should use a RUP line");
        };
        hints[1] = 99;
        assert_eq!(
            lrat_check_certificate(&request, &policy, &cnf, &certificate),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::HintOutOfBounds {
                    line_id: 3,
                    hint_id: 99,
                },
            })
        );
    }

    #[test]
    fn lrat_malformed_rejects_missing_pivot_invalid_deletion_and_no_empty_clause() {
        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let cnf = lrat_rat_cnf();

        let mut missing_pivot = lrat_rat_deletion_certificate(&cnf);
        let LratProofLineKind::Add {
            rule: LratProofRule::Rat { pivot, .. },
            ..
        } = &mut missing_pivot.proof_lines[0].kind
        else {
            panic!("fixture should use a RAT line");
        };
        *pivot = None;
        assert_eq!(
            lrat_check_certificate(&request, &policy, &cnf, &missing_pivot),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::MissingRatPivot { line_id: 4 },
            })
        );

        let invalid_delete = LratCertificate {
            version: SolverContractVersion::V1,
            cnf_hash: lrat_cnf_hash(&cnf).unwrap(),
            proof_lines: vec![LratProofLine {
                ordinal: 0,
                kind: LratProofLineKind::Delete {
                    clause_ids: vec![99],
                },
            }],
        };
        assert_eq!(
            lrat_check_certificate(&request, &policy, &cnf, &invalid_delete),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::InvalidDeletion {
                    ordinal: 0,
                    clause_id: 99,
                },
            })
        );

        let no_empty_cnf = LratCnf {
            version: SolverContractVersion::V1,
            variable_count: 1,
            clauses: vec![lrat_clause(1, vec![lrat_lit(1, true)])],
        };
        let no_empty_certificate = LratCertificate {
            version: SolverContractVersion::V1,
            cnf_hash: lrat_cnf_hash(&no_empty_cnf).unwrap(),
            proof_lines: vec![LratProofLine {
                ordinal: 0,
                kind: LratProofLineKind::Add {
                    clause: lrat_clause(2, vec![lrat_lit(1, true)]),
                    rule: LratProofRule::Rup { hints: vec![1] },
                },
            }],
        };
        assert_eq!(
            lrat_check_certificate(&request, &policy, &no_empty_cnf, &no_empty_certificate),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::NoEmptyClause,
            })
        );
    }

    #[test]
    fn lrat_malformed_rejects_raw_unsat_payload_cnf_hash_mismatch_and_bad_ordinal() {
        let raw_unsat = SolverProofPayloadRef {
            certificate_format: SolverCertificateFormat::SolverResultOnlyV1,
            payload_hash: solver_inline_payload_hash(
                SolverCertificateFormat::SolverResultOnlyV1,
                b"unsat\n",
            )
            .unwrap(),
            size_bytes: b"unsat\n".len() as u64,
            canonical_bytes: Some(b"unsat\n".to_vec()),
        };
        assert_eq!(
            validate_lrat_proof_payload_ref(&raw_unsat),
            Err(SolverContractError::RequestMetadataMismatch {
                field: "certificate_format",
            })
        );
        let mislabeled_raw_unsat = SolverProofPayloadRef {
            certificate_format: SolverCertificateFormat::LratV1,
            payload_hash: solver_inline_payload_hash(SolverCertificateFormat::LratV1, b"unsat\n")
                .unwrap(),
            size_bytes: b"unsat\n".len() as u64,
            canonical_bytes: Some(b"unsat\n".to_vec()),
        };
        assert_eq!(
            validate_lrat_proof_payload_ref(&mislabeled_raw_unsat),
            Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "lrat_payload_canonical_bytes",
            })
        );

        let policy = lrat_policy();
        let request = lrat_request_for_policy(&policy);
        let cnf = lrat_minimal_unsat_cnf();
        let mut certificate = lrat_minimal_unsat_certificate(&cnf);
        certificate.cnf_hash = hash(210);
        assert!(matches!(
            lrat_check_certificate(&request, &policy, &cnf, &certificate),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::CnfHashMismatch { .. }
            })
        ));

        let mut malformed_line = lrat_minimal_unsat_certificate(&cnf);
        malformed_line.proof_lines[0].ordinal = 1;
        assert_eq!(
            validate_lrat_certificate_shape(&malformed_line),
            Err(SolverContractError::LratCheckFailed {
                error: LratCheckError::NonCanonicalProofLine {
                    expected_ordinal: 0,
                    actual_ordinal: 1,
                },
            })
        );
    }

    fn omega_reconstruction_fixture(
    ) -> (SolverResourcePolicy, SolverRequest, OmegaNormalizedProblem) {
        let policy = omega_policy();
        let request = omega_request_for_policy(&policy);
        let options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let context = omega_context(&[("n", OmegaTermSort::Nat), ("i", OmegaTermSort::Int)]);
        let nat_goal = omega_app2(
            "Nat.le",
            omega_app2("Nat.add", Expr::bvar(1), omega_nat_lit(3)),
            omega_app2("Nat.add", Expr::bvar(1), omega_nat_lit(2)),
        );
        let int_goal = omega_app2(
            "Int.lt",
            omega_app2("Int.sub", Expr::bvar(0), omega_int_lit(1)),
            omega_int_lit(4),
        );
        let target = omega_appn("Bool.and", vec![nat_goal, int_goal]);
        let problem = omega_normalize_problem(&request, &context, &target, &options).unwrap();
        (policy, request, problem)
    }

    fn omega_first_atom(problem: &OmegaNormalizedProblem) -> &OmegaAtom {
        match &problem.formula {
            OmegaFormula::Atom(atom) => atom,
            OmegaFormula::Boolean { args, .. } => match &args[0] {
                OmegaFormula::Atom(atom) => atom,
                OmegaFormula::Boolean { .. } => panic!("nested first omega atom fixture changed"),
            },
        }
    }

    fn omega_step(
        step_id: &str,
        rule: OmegaReconstructionRule,
        input_step_ids: Vec<&str>,
        atom_indices: Vec<u64>,
        coefficients: Vec<i64>,
        constant: i64,
        side_condition_ordinals: Vec<u64>,
    ) -> OmegaReconstructionStep {
        let mut step = OmegaReconstructionStep {
            step_id: step_id.to_owned(),
            rule,
            input_step_ids: input_step_ids
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>(),
            atom_indices,
            coefficients,
            constant,
            side_condition_ordinals,
            result_hash: [0; 32],
        };
        step.result_hash = omega_reconstruction_step_result_hash(&step).unwrap();
        step
    }

    fn omega_valid_certificate(
        request: &SolverRequest,
        problem: &OmegaNormalizedProblem,
    ) -> OmegaCertificateArtifact {
        let variable_count = problem.variables.len();
        let zero_coefficients = vec![0; variable_count];
        let first_atom = omega_first_atom(problem);
        let first_normal_form = first_atom.normalized_lhs_minus_rhs.clone();
        let side_ordinals = problem
            .nat_to_int_side_conditions
            .iter()
            .map(|side_condition| side_condition.variable_ordinal)
            .collect::<Vec<_>>();
        let steps = vec![
            omega_step(
                "cmp-0",
                OmegaReconstructionRule::ComparisonNormalization,
                Vec::new(),
                vec![0],
                first_normal_form.coefficients.clone(),
                first_normal_form.constant,
                Vec::new(),
            ),
            omega_step(
                "bool-0",
                OmegaReconstructionRule::BooleanSplit,
                vec!["cmp-0"],
                Vec::new(),
                first_normal_form.coefficients.clone(),
                first_normal_form.constant,
                Vec::new(),
            ),
            omega_step(
                "nat-0",
                OmegaReconstructionRule::NatSideConditionDischarge,
                Vec::new(),
                Vec::new(),
                zero_coefficients.clone(),
                0,
                side_ordinals,
            ),
            omega_step(
                "lin-0",
                OmegaReconstructionRule::LinearCombination,
                vec!["bool-0", "nat-0"],
                vec![0],
                first_normal_form.coefficients.clone(),
                first_normal_form.constant,
                Vec::new(),
            ),
            omega_step(
                "contra",
                OmegaReconstructionRule::Contradiction,
                vec!["lin-0"],
                Vec::new(),
                first_normal_form.coefficients,
                first_normal_form.constant,
                Vec::new(),
            ),
        ];
        OmegaCertificateArtifact {
            version: SolverContractVersion::V1,
            request_hash: solver_request_hash(request).unwrap(),
            normalized_problem_hash: omega_normalized_problem_hash(problem).unwrap(),
            policy_hash: request.policy_hash,
            conclusion: OmegaCertificateConclusion::Contradiction,
            steps,
            final_step_id: "contra".to_owned(),
        }
    }

    fn certificate_metadata_for_request(request: &SolverRequest) -> SolverCertificateMetadata {
        let payload_ref = proof_payload_ref();
        SolverCertificateMetadata {
            family: request.family,
            fragment: request.fragment,
            profile: request.profile,
            certificate_format: SolverCertificateFormat::MvpSmtProofNodeTableV1,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            payload_hash: payload_ref.payload_hash,
            proof_payload_ref_hash: solver_proof_payload_ref_hash(&payload_ref).unwrap(),
            reconstruction_plan_hash: solver_reconstruction_plan_hash(&reconstruction_plan())
                .unwrap(),
        }
    }

    fn certificate_response_for_request(request: &SolverRequest) -> SolverResponse {
        let certificate = certificate_metadata_for_request(request);
        SolverResponse {
            version: SolverContractVersion::V1,
            status: SolverResponseStatus::Certificate,
            metadata: SolverResponseMetadata {
                request_hash: solver_request_hash(request).unwrap(),
                family: certificate.family,
                fragment: certificate.fragment,
                profile: certificate.profile,
                environment_hash: certificate.environment_hash,
                policy_hash: certificate.policy_hash,
                payload_hash: Some(certificate.payload_hash),
                proof_payload_ref_hash: Some(certificate.proof_payload_ref_hash),
                certificate_format: Some(certificate.certificate_format),
                certificate_metadata_hash: Some(
                    solver_certificate_metadata_hash(&certificate).unwrap(),
                ),
                reconstruction_plan_hash: Some(certificate.reconstruction_plan_hash),
            },
            payload: SolverResponsePayload::Certificate(
                SolverAcceptingPayload::CheckedCertificateReconstruction(certificate),
            ),
            advisory: SolverResponseAdvisory::default(),
        }
    }

    fn finite_decide_request() -> SolverRequest {
        let policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::FiniteDecideDefaultV1);
        SolverRequest {
            version: SolverContractVersion::V1,
            family: SolverFamily::FiniteDecide,
            fragment: SolverFragment::FiniteEnumerationV1,
            profile: SolverProfile::DirectProofTermV1,
            goal_identity: SolverGoalIdentity {
                goal_hash: hash(41),
                target_hash: hash(42),
            },
            local_context_hash: hash(43),
            environment_hash: hash(44),
            policy_hash: solver_resource_policy_hash(&policy).unwrap(),
        }
    }

    fn finite_decide_predicate(request: &SolverRequest) -> FiniteDecidePredicateRef {
        FiniteDecidePredicateRef {
            predicate_hash: hash(50),
            predicate_type_hash: hash(51),
            reflected_decidable_hash: hash(52),
            local_context_hash: request.local_context_hash,
            environment_hash: request.environment_hash,
            policy_hash: request.policy_hash,
            universe_params: vec!["u".to_owned()],
        }
    }

    fn bool_carrier() -> FiniteDecideCarrierRef {
        FiniteDecideCarrierRef {
            version: SolverContractVersion::V1,
            kind: FiniteDecideCarrierKind::Bool,
            small_kind: None,
            carrier_type_hash: hash(60),
            universe_params: Vec::new(),
            cardinality: 2,
            fin_bound: None,
            vector_bool_length: None,
            explicit_finite_evidence_hash: None,
            no_duplicate_evidence_hash: None,
            complete_evidence_hash: None,
        }
    }

    fn explicit_carrier(
        kind: FiniteDecideCarrierKind,
        small_kind: Option<FiniteDecideSmallCarrierKind>,
        cardinality: u64,
    ) -> FiniteDecideCarrierRef {
        FiniteDecideCarrierRef {
            version: SolverContractVersion::V1,
            kind,
            small_kind,
            carrier_type_hash: hash(61),
            universe_params: vec!["u".to_owned()],
            cardinality,
            fin_bound: None,
            vector_bool_length: None,
            explicit_finite_evidence_hash: Some(hash(62)),
            no_duplicate_evidence_hash: Some(hash(63)),
            complete_evidence_hash: Some(hash(64)),
        }
    }

    fn finite_carrier(bound: u64) -> FiniteDecideCarrierRef {
        FiniteDecideCarrierRef {
            version: SolverContractVersion::V1,
            kind: FiniteDecideCarrierKind::Fin,
            small_kind: None,
            carrier_type_hash: hash(65),
            universe_params: Vec::new(),
            cardinality: bound,
            fin_bound: Some(bound),
            vector_bool_length: None,
            explicit_finite_evidence_hash: None,
            no_duplicate_evidence_hash: None,
            complete_evidence_hash: None,
        }
    }

    fn vector_bool_carrier(length: u64) -> FiniteDecideCarrierRef {
        FiniteDecideCarrierRef {
            version: SolverContractVersion::V1,
            kind: FiniteDecideCarrierKind::VectorBool,
            small_kind: None,
            carrier_type_hash: hash(66),
            universe_params: Vec::new(),
            cardinality: 1u64 << (length as u32),
            fin_bound: None,
            vector_bool_length: Some(length),
            explicit_finite_evidence_hash: None,
            no_duplicate_evidence_hash: None,
            complete_evidence_hash: None,
        }
    }

    fn element(
        ordinal: u64,
        element_type_hash: Hash,
        origin: FiniteDecideElementOrigin,
    ) -> FiniteDecideElement {
        FiniteDecideElement {
            ordinal,
            element_hash: hash(100 + ordinal as u8),
            element_type_hash,
            origin,
        }
    }

    fn bool_enumeration() -> FiniteDecideEnumeration {
        let carrier = bool_carrier();
        FiniteDecideEnumeration {
            elements: vec![
                element(
                    0,
                    carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::BoolFalse,
                ),
                element(
                    1,
                    carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::BoolTrue,
                ),
            ],
            carrier,
        }
    }

    fn finite_decide_contract(
        enumeration: FiniteDecideEnumeration,
    ) -> FiniteDecideReflectionContract {
        let request = finite_decide_request();
        FiniteDecideReflectionContract {
            version: SolverContractVersion::V1,
            predicate: finite_decide_predicate(&request),
            request,
            enumeration,
        }
    }

    fn finite_decide_true_decisions(
        contract: &FiniteDecideReflectionContract,
    ) -> Vec<FiniteDecideElementDecision> {
        contract
            .enumeration
            .elements
            .iter()
            .map(|element| FiniteDecideElementDecision {
                element: element.clone(),
                value: FiniteDecideDecisionValue::PredicateTrue,
                predicate_evidence_hash: hash(120 + element.ordinal as u8),
                proof_term_hash: Some(hash(130 + element.ordinal as u8)),
            })
            .collect()
    }

    fn finite_decide_proof_artifact(
        contract: &FiniteDecideReflectionContract,
        goal_kind: FiniteDecideGoalKind,
        fold_result: bool,
        element_decisions: Vec<FiniteDecideElementDecision>,
    ) -> FiniteDecideProofArtifact {
        FiniteDecideProofArtifact {
            version: SolverContractVersion::V1,
            reflection_contract_hash: finite_decide_reflection_contract_hash(contract).unwrap(),
            enumeration_hash: finite_decide_enumeration_hash(&contract.enumeration).unwrap(),
            predicate_hash: contract.predicate.predicate_hash,
            goal_kind,
            fold_result,
            element_decisions,
            proof_identity: SolverCheckedProofTermIdentity {
                environment_hash: contract.request.environment_hash,
                proof_term_hash: hash(91),
                proof_type_hash: contract.request.goal_identity.target_hash,
            },
            generated_term_nodes: 11,
            proof_bytes: 37,
            proof_steps: 3,
        }
    }

    fn advanced_smt_candidate_fixture() -> (
        AdvancedMachineSmtCertificateCandidate,
        AdvancedMachineSmtEncodedProblem,
    ) {
        let problem = AdvancedMachineSmtEncodedProblem {
            encoder_version: AdvancedSmtEncoderVersion::MvpNormalizedQfV1,
            goal_fingerprint: hash(80),
            logic: AdvancedSmtLogic::MvpQfUf,
            command_profile: AdvancedSmtCommandProfile::MvpNormalizedQf,
            commands: Vec::new(),
        };
        let problem_bytes = advanced_ai_smt_problem_canonical_bytes(&problem).unwrap();
        let problem_hash = advanced_ai_smt_problem_hash(&problem).unwrap();
        let encoding_hash = advanced_ai_smt_encoding_hash(&problem, problem_hash);
        let candidate = AdvancedMachineSmtCertificateCandidate {
            goal: AdvancedAiGoal {
                universe_params: Vec::new(),
                local_context: Vec::new(),
                target: Expr::sort(Level::zero()),
            },
            solver: AdvancedSmtSolver::Cvc5,
            logic: AdvancedSmtLogic::MvpQfUf,
            encoded_problem: AdvancedMachineSmtProblemRef::Inline {
                problem_hash,
                encoding_hash,
                canonical_bytes: problem_bytes,
            },
            certificate_format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
            rule_registry_profile: AdvancedSmtRuleRegistryProfile::MvpEmptyRegistryV1,
            proof_payload: AdvancedMachineSmtProofPayloadRef::Inline {
                payload_hash: hash(81),
                canonical_bytes: b"proof".to_vec(),
            },
            reconstruction_plan: AdvancedMachineSmtReconstructionPlan {
                imported_theory_refs: Vec::new(),
                steps: Vec::new(),
                final_step: 0,
                final_proof: Expr::sort(Level::zero()),
            },
        };
        (candidate, problem)
    }

    #[test]
    fn finite_decide_supported_carrier_contracts_are_hash_stable() {
        let bool_enum = bool_enumeration();
        let fin_carrier = finite_carrier(3);
        let fin_enum = FiniteDecideEnumeration {
            elements: (0..3)
                .map(|ordinal| {
                    element(
                        ordinal,
                        fin_carrier.carrier_type_hash,
                        FiniteDecideElementOrigin::FinOrdinal(ordinal),
                    )
                })
                .collect(),
            carrier: fin_carrier,
        };
        let vector_carrier = vector_bool_carrier(2);
        let vector_enum = FiniteDecideEnumeration {
            elements: vec![
                element(
                    0,
                    vector_carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::VectorBoolBits(vec![false, false]),
                ),
                element(
                    1,
                    vector_carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::VectorBoolBits(vec![false, true]),
                ),
                element(
                    2,
                    vector_carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::VectorBoolBits(vec![true, false]),
                ),
                element(
                    3,
                    vector_carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::VectorBoolBits(vec![true, true]),
                ),
            ],
            carrier: vector_carrier,
        };
        let small_carrier = explicit_carrier(
            FiniteDecideCarrierKind::SmallExplicitFinite,
            Some(FiniteDecideSmallCarrierKind::Unit),
            1,
        );
        let small_enum = FiniteDecideEnumeration {
            elements: vec![element(
                0,
                small_carrier.carrier_type_hash,
                FiniteDecideElementOrigin::SmallExplicitOrdinal { ordinal: 0 },
            )],
            carrier: small_carrier,
        };
        let explicit_carrier = explicit_carrier(FiniteDecideCarrierKind::ExplicitFinite, None, 2);
        let explicit_enum = FiniteDecideEnumeration {
            elements: vec![
                element(
                    0,
                    explicit_carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::ExplicitIndex {
                        index_hash: hash(70),
                    },
                ),
                element(
                    1,
                    explicit_carrier.carrier_type_hash,
                    FiniteDecideElementOrigin::ExplicitIndex {
                        index_hash: hash(71),
                    },
                ),
            ],
            carrier: explicit_carrier,
        };

        let mut hashes = BTreeSet::new();
        for enumeration in [bool_enum, fin_enum, vector_enum, small_enum, explicit_enum] {
            validate_finite_decide_enumeration(&enumeration).unwrap();
            let contract = finite_decide_contract(enumeration);
            validate_finite_decide_reflection_contract(&contract).unwrap();
            let first = finite_decide_reflection_contract_hash(&contract).unwrap();
            let second = finite_decide_reflection_contract_hash(&contract).unwrap();
            assert_eq!(first, second);
            hashes.insert(first);
        }
        assert_eq!(hashes.len(), 5);
    }

    #[test]
    fn finite_decide_enumeration_rejects_duplicates_missing_and_bad_order() {
        let mut duplicate = bool_enumeration();
        duplicate.elements[1].element_hash = duplicate.elements[0].element_hash;
        assert!(matches!(
            validate_finite_decide_enumeration(&duplicate),
            Err(SolverContractError::DuplicateFiniteEnumerationElement { .. })
        ));

        let mut missing = bool_enumeration();
        missing.elements.pop();
        assert_eq!(
            validate_finite_decide_enumeration(&missing),
            Err(SolverContractError::MissingFiniteEnumerationElement {
                expected_cardinality: 2,
                actual_cardinality: 1,
            })
        );

        let mut wrong_order = bool_enumeration();
        wrong_order.elements[0].origin = FiniteDecideElementOrigin::BoolTrue;
        assert_eq!(
            validate_finite_decide_enumeration(&wrong_order),
            Err(SolverContractError::NonCanonicalFiniteEnumerationOrder {
                expected_ordinal: 0,
                actual_ordinal: 1,
            })
        );

        let mut non_explicit = explicit_carrier(FiniteDecideCarrierKind::ExplicitFinite, None, 1);
        non_explicit.explicit_finite_evidence_hash = None;
        assert_eq!(
            validate_finite_decide_carrier_ref(&non_explicit),
            Err(SolverContractError::MissingFiniteEvidence {
                field: "explicit_finite_evidence_hash",
            })
        );
    }

    #[test]
    fn finite_decide_reflection_binds_context_environment_and_policy_hashes() {
        let contract = finite_decide_contract(bool_enumeration());
        let base_hash = finite_decide_reflection_contract_hash(&contract).unwrap();
        assert_eq!(
            base_hash,
            finite_decide_reflection_contract_hash(&contract).unwrap()
        );

        let mut changed_predicate = contract.clone();
        changed_predicate.predicate.predicate_hash = hash(53);
        assert_ne!(
            base_hash,
            finite_decide_reflection_contract_hash(&changed_predicate).unwrap()
        );

        let mut wrong_context = contract.clone();
        wrong_context.predicate.local_context_hash = hash(54);
        assert_eq!(
            validate_finite_decide_reflection_contract(&wrong_context),
            Err(SolverContractError::MismatchedHash {
                field: "local_context_hash",
                expected: contract.request.local_context_hash,
                actual: hash(54),
            })
        );

        let mut wrong_environment = contract.clone();
        wrong_environment.predicate.environment_hash = hash(55);
        assert_eq!(
            validate_finite_decide_reflection_contract(&wrong_environment),
            Err(SolverContractError::MismatchedHash {
                field: "environment_hash",
                expected: contract.request.environment_hash,
                actual: hash(55),
            })
        );

        let mut wrong_policy = contract.clone();
        wrong_policy.predicate.policy_hash = hash(56);
        assert_eq!(
            validate_finite_decide_reflection_contract(&wrong_policy),
            Err(SolverContractError::MismatchedHash {
                field: "policy_hash",
                expected: contract.request.policy_hash,
                actual: hash(56),
            })
        );
    }

    #[test]
    fn finite_decide_counterexample_response_is_not_accepting_evidence() {
        let contract = finite_decide_contract(bool_enumeration());
        let counterexample =
            finite_decide_counterexample_for_reflection(&contract, 0, hash(72)).unwrap();
        validate_finite_decide_counterexample_for_reflection(&contract, &counterexample).unwrap();

        let response = finite_decide_counterexample_response(&contract, &counterexample).unwrap();
        validate_solver_response_for_request(&contract.request, &response).unwrap();
        assert_eq!(response.status, SolverResponseStatus::Counterexample);
        assert!(matches!(
            solver_response_accepting_payload(&response),
            Err(SolverContractError::NonAcceptingStatusCannotVerify {
                status: SolverResponseStatus::Counterexample,
            })
        ));
        assert_eq!(response.metadata.certificate_format, None);
        assert_eq!(response.metadata.proof_payload_ref_hash, None);
        assert_eq!(response.metadata.certificate_metadata_hash, None);

        let mut relabeled_contract = contract.clone();
        relabeled_contract.predicate.predicate_hash = hash(73);
        assert!(matches!(
            finite_decide_counterexample_response(&relabeled_contract, &counterexample),
            Err(SolverContractError::MismatchedHash {
                field: "reflection_contract_hash",
                ..
            })
        ));
    }

    #[test]
    fn finite_decide_source_free_checked_proof_response_binds_identity_and_policy() {
        let contract = finite_decide_contract(bool_enumeration());
        let policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::FiniteDecideDefaultV1);
        let artifact = finite_decide_proof_artifact(
            &contract,
            FiniteDecideGoalKind::Universal,
            true,
            finite_decide_true_decisions(&contract),
        );

        validate_finite_decide_proof_artifact_for_reflection(&contract, &artifact).unwrap();
        let response = finite_decide_checked_proof_response(&contract, &artifact, &policy).unwrap();
        validate_solver_response_for_request(&contract.request, &response).unwrap();
        assert_eq!(response.status, SolverResponseStatus::Certificate);
        assert_eq!(
            response.metadata.certificate_format,
            Some(SolverCertificateFormat::DirectNpaProofTermV1)
        );
        assert_eq!(response.metadata.proof_payload_ref_hash, None);
        assert!(matches!(
            solver_response_accepting_payload(&response),
            Ok(SolverAcceptingPayload::CheckedProofTerm(identity))
                if identity == &artifact.proof_identity
        ));

        let replay =
            solver_replay_metadata_for_response(&contract.request, &response, &policy).unwrap();
        validate_solver_replay_metadata(&contract.request, &response, &policy, &replay).unwrap();
    }

    #[test]
    fn finite_decide_source_free_rejects_false_folds_duplicates_and_budget_exhaustion() {
        let contract = finite_decide_contract(bool_enumeration());
        let policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::FiniteDecideDefaultV1);
        let mut false_universal_decisions = finite_decide_true_decisions(&contract);
        false_universal_decisions[1].value = FiniteDecideDecisionValue::PredicateFalse;
        false_universal_decisions[1].proof_term_hash = None;
        let false_universal = finite_decide_proof_artifact(
            &contract,
            FiniteDecideGoalKind::Universal,
            false,
            false_universal_decisions,
        );
        assert_eq!(
            finite_decide_checked_proof_response(&contract, &false_universal, &policy),
            Err(SolverContractError::FalseFiniteDecisionCannotProduceProof {
                goal_kind: FiniteDecideGoalKind::Universal,
                witness_ordinal: Some(1),
            })
        );

        let false_exists = finite_decide_proof_artifact(
            &contract,
            FiniteDecideGoalKind::Existential,
            false,
            contract
                .enumeration
                .elements
                .iter()
                .map(|element| FiniteDecideElementDecision {
                    element: element.clone(),
                    value: FiniteDecideDecisionValue::PredicateFalse,
                    predicate_evidence_hash: hash(140 + element.ordinal as u8),
                    proof_term_hash: None,
                })
                .collect(),
        );
        assert_eq!(
            finite_decide_checked_proof_response(&contract, &false_exists, &policy),
            Err(SolverContractError::FalseFiniteDecisionCannotProduceProof {
                goal_kind: FiniteDecideGoalKind::Existential,
                witness_ordinal: None,
            })
        );

        let mut duplicate = finite_decide_proof_artifact(
            &contract,
            FiniteDecideGoalKind::Universal,
            true,
            finite_decide_true_decisions(&contract),
        );
        duplicate.element_decisions[1].element = duplicate.element_decisions[0].element.clone();
        assert_eq!(
            finite_decide_checked_proof_response(&contract, &duplicate, &policy),
            Err(SolverContractError::CounterexampleWitnessNotInEnumeration { ordinal: 0 })
        );

        let mut tiny_policy = policy;
        tiny_policy.max_generated_term_nodes = 1;
        let over_budget = finite_decide_proof_artifact(
            &contract,
            FiniteDecideGoalKind::BooleanDecision,
            true,
            finite_decide_true_decisions(&contract),
        );
        assert_eq!(
            finite_decide_checked_proof_response(&contract, &over_budget, &tiny_policy),
            Err(SolverContractError::MismatchedHash {
                field: "policy_hash",
                expected: solver_resource_policy_hash(&tiny_policy).unwrap(),
                actual: contract.request.policy_hash,
            })
        );

        let mut budget_contract = contract.clone();
        budget_contract.request.policy_hash = solver_resource_policy_hash(&tiny_policy).unwrap();
        budget_contract.predicate.policy_hash = budget_contract.request.policy_hash;
        let over_budget = finite_decide_proof_artifact(
            &budget_contract,
            FiniteDecideGoalKind::BooleanDecision,
            true,
            finite_decide_true_decisions(&budget_contract),
        );
        assert_eq!(
            finite_decide_checked_proof_response(&budget_contract, &over_budget, &tiny_policy),
            Err(SolverContractError::ReconstructionTermTooLarge {
                limit_nodes: 1,
                actual_nodes: 11,
            })
        );
    }

    #[test]
    fn solver_request_identity_changes_for_goal_context_environment_policy_family_fragment_and_profile(
    ) {
        let base = request();
        let base_hash = solver_request_hash(&base).unwrap();

        let mut changed = base.clone();
        changed.goal_identity.goal_hash = hash(11);
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base.clone();
        changed.goal_identity.target_hash = hash(12);
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base.clone();
        changed.local_context_hash = hash(13);
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base.clone();
        changed.environment_hash = hash(14);
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base.clone();
        changed.policy_hash = hash(15);
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base.clone();
        changed.family = SolverFamily::FiniteDecide;
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base.clone();
        changed.fragment = SolverFragment::SmtQfLiaV1;
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());

        let mut changed = base;
        changed.profile = SolverProfile::DirectProofTermV1;
        assert_ne!(base_hash, solver_request_hash(&changed).unwrap());
    }

    #[test]
    fn solver_response_identity_excludes_display_stdout_wall_clock_score_and_diagnostic_prose() {
        let base = certificate_response();
        let base_hash = solver_response_identity_hash(&base).unwrap();

        let mut changed = base.clone();
        changed.advisory = SolverResponseAdvisory {
            display_text: Some("pretty proof".to_owned()),
            diagnostic_prose: Some("solver said unsat".to_owned()),
            raw_solver_stdout: Some("(success)".to_owned()),
            raw_solver_stderr: Some("warning".to_owned()),
            measured_wall_clock_ms: Some(1234),
            ranking_score: Some(99),
        };
        assert_eq!(base_hash, solver_response_identity_hash(&changed).unwrap());

        let mut changed = base;
        let SolverResponsePayload::Certificate(
            SolverAcceptingPayload::CheckedCertificateReconstruction(certificate),
        ) = &mut changed.payload
        else {
            unreachable!("test fixture is a certificate response")
        };
        certificate.reconstruction_plan_hash = hash(99);
        changed.metadata.reconstruction_plan_hash = Some(hash(99));
        changed.metadata.certificate_metadata_hash =
            Some(solver_certificate_metadata_hash(certificate).unwrap());
        assert_ne!(base_hash, solver_response_identity_hash(&changed).unwrap());
    }

    #[test]
    fn solver_response_certificate_status_is_the_only_accepting_status() {
        let request_hash = solver_request_hash(&request()).unwrap();
        let metadata = SolverResponseMetadata {
            request_hash,
            family: SolverFamily::FiniteDecide,
            fragment: SolverFragment::FiniteEnumerationV1,
            profile: SolverProfile::DirectProofTermV1,
            environment_hash: hash(4),
            policy_hash: hash(5),
            payload_hash: Some(hash(20)),
            proof_payload_ref_hash: None,
            certificate_format: Some(SolverCertificateFormat::DirectNpaProofTermV1),
            certificate_metadata_hash: None,
            reconstruction_plan_hash: None,
        };
        let certificate = SolverResponse {
            version: SolverContractVersion::V1,
            status: SolverResponseStatus::Certificate,
            metadata: metadata.clone(),
            payload: SolverResponsePayload::Certificate(SolverAcceptingPayload::CheckedProofTerm(
                SolverCheckedProofTermIdentity {
                    environment_hash: hash(4),
                    proof_term_hash: hash(20),
                    proof_type_hash: hash(21),
                },
            )),
            advisory: SolverResponseAdvisory::default(),
        };
        assert!(solver_response_accepting_payload(&certificate).is_ok());

        let proposed = SolverResponse {
            version: SolverContractVersion::V1,
            status: SolverResponseStatus::Proposed,
            metadata: SolverResponseMetadata {
                request_hash,
                family: SolverFamily::FiniteDecide,
                fragment: SolverFragment::FiniteEnumerationV1,
                profile: SolverProfile::DirectProofTermV1,
                environment_hash: hash(4),
                policy_hash: hash(5),
                payload_hash: Some(hash(30)),
                proof_payload_ref_hash: None,
                certificate_format: None,
                certificate_metadata_hash: None,
                reconstruction_plan_hash: None,
            },
            payload: SolverResponsePayload::Proposed {
                proposal_hash: Some(hash(30)),
                reconstruction_plan: None,
            },
            advisory: SolverResponseAdvisory::default(),
        };
        assert_eq!(
            solver_response_accepting_payload(&proposed),
            Err(SolverContractError::NonAcceptingStatusCannotVerify {
                status: SolverResponseStatus::Proposed
            })
        );

        let mismatched = SolverResponse {
            status: SolverResponseStatus::Unsupported,
            payload: SolverResponsePayload::Certificate(
                SolverAcceptingPayload::CheckedCertificateReconstruction(certificate_metadata()),
            ),
            ..certificate
        };
        assert!(matches!(
            validate_solver_response(&mismatched),
            Err(SolverContractError::ResponseStatusPayloadMismatch { .. })
        ));
    }

    #[test]
    fn solver_response_validation_rejects_metadata_relabeling() {
        let base = certificate_response();

        let mut changed = base.clone();
        changed.metadata.payload_hash = Some(hash(77));
        assert!(matches!(
            validate_solver_response(&changed),
            Err(SolverContractError::MismatchedHash {
                field: "payload_hash",
                ..
            })
        ));

        let mut changed = base.clone();
        changed.metadata.certificate_format = Some(SolverCertificateFormat::AletheOpaqueV1);
        assert_eq!(
            validate_solver_response(&changed),
            Err(SolverContractError::RequestMetadataMismatch {
                field: "certificate_format",
            })
        );

        let mut changed = base.clone();
        changed.metadata.certificate_metadata_hash = Some(hash(78));
        assert!(matches!(
            validate_solver_response(&changed),
            Err(SolverContractError::MismatchedHash {
                field: "certificate_metadata_hash",
                ..
            })
        ));

        let mut changed = base.clone();
        changed.metadata.family = SolverFamily::Omega;
        assert_eq!(
            validate_solver_response_for_request(&request(), &changed),
            Err(SolverContractError::RequestMetadataMismatch { field: "family" })
        );
    }

    #[test]
    fn solver_contract_validation_rejects_unknown_profiles_duplicates_mismatched_hashes_and_missing_hashes(
    ) {
        assert_eq!(
            SolverProfile::from_wire("future-profile"),
            Err(SolverContractError::UnknownProfileTag {
                field: "profile",
                tag: "future-profile".to_owned(),
            })
        );

        let mut bad_request = request();
        bad_request.environment_hash = [0; 32];
        assert_eq!(
            validate_solver_request(&bad_request),
            Err(SolverContractError::MissingEnvironmentHash)
        );

        let mut bad_request = request();
        bad_request.policy_hash = [0; 32];
        assert_eq!(
            validate_solver_request(&bad_request),
            Err(SolverContractError::MissingPolicyHash)
        );

        let mut bad_payload = proof_payload_ref();
        bad_payload.payload_hash = hash(77);
        assert!(matches!(
            solver_proof_payload_ref_hash(&bad_payload),
            Err(SolverContractError::MismatchedHash {
                field: "payload_hash",
                ..
            })
        ));

        assert_eq!(
            solver_inline_payload_hash(SolverCertificateFormat::SolverResultOnlyV1, b"sat\n"),
            Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "solver_result_only",
            })
        );

        let mut bad_plan = reconstruction_plan();
        bad_plan.step_ids = vec!["dup".to_owned(), "dup".to_owned()];
        assert_eq!(
            solver_reconstruction_plan_hash(&bad_plan),
            Err(SolverContractError::DuplicateIdentifier {
                field: "reconstruction_step_id",
                identifier: "dup".to_owned(),
            })
        );
    }

    #[test]
    fn solver_resource_policy_defaults_are_named_and_deterministic() {
        let profiles = [
            SolverResourcePolicyProfile::FiniteDecideDefaultV1,
            SolverResourcePolicyProfile::OmegaDefaultV1,
            SolverResourcePolicyProfile::RingNfDefaultV1,
            SolverResourcePolicyProfile::BitblastDefaultV1,
            SolverResourcePolicyProfile::LratDefaultV1,
            SolverResourcePolicyProfile::SmtReconstructionDefaultV1,
        ];
        let mut hashes = BTreeSet::new();
        for profile in profiles {
            let policy = solver_default_resource_policy(profile);
            validate_solver_resource_policy(&policy).unwrap();
            assert_eq!(policy.profile, profile);
            assert_eq!(profile.default_family(), Some(policy.family));
            assert!(solver_resource_policy_supports_fragment(
                &policy,
                request_for_resource_policy(&policy).fragment
            ));
            let first = solver_resource_policy_hash(&policy).unwrap();
            let second = solver_resource_policy_hash(&policy).unwrap();
            assert_eq!(first, second);
            assert!(hashes.insert(first));
            assert_eq!(
                solver_resource_policy_ref(&policy).unwrap().policy_hash,
                first
            );
        }
    }

    #[test]
    fn omega_fragment_normalizes_nat_int_linear_boolean_and_hashes_stably() {
        let policy = omega_policy();
        let request = omega_request_for_policy(&policy);
        let options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let context = omega_context(&[("n", OmegaTermSort::Nat), ("i", OmegaTermSort::Int)]);
        let nat_goal = omega_app2(
            "Nat.le",
            omega_app2("Nat.add", Expr::bvar(1), omega_nat_lit(2)),
            omega_app2("Nat.add", Expr::bvar(1), omega_nat_lit(3)),
        );
        let int_goal = omega_app2(
            "Int.lt",
            omega_app2("Int.sub", Expr::bvar(0), omega_int_lit(1)),
            omega_int_lit(4),
        );
        let target = omega_appn("Bool.and", vec![nat_goal, int_goal]);

        let problem = omega_normalize_problem(&request, &context, &target, &options).unwrap();
        validate_omega_normalized_problem(&problem).unwrap();

        assert_eq!(
            problem.fragment_profile,
            OmegaFragmentProfile::LinearArithmeticV1
        );
        assert_eq!(problem.variables.len(), 2);
        assert_eq!(problem.variables[0].ordinal, 0);
        assert_eq!(problem.variables[0].local_index, 0);
        assert_eq!(problem.variables[0].name, "n");
        assert_eq!(problem.variables[0].sort, OmegaTermSort::Nat);
        assert_eq!(problem.variables[1].ordinal, 1);
        assert_eq!(problem.variables[1].local_index, 1);
        assert_eq!(problem.variables[1].name, "i");
        assert_eq!(problem.variables[1].sort, OmegaTermSort::Int);
        assert_eq!(problem.nat_to_int_side_conditions.len(), 1);
        assert_eq!(
            problem.nat_to_int_side_conditions[0].variable_ordinal,
            problem.variables[0].ordinal
        );

        let OmegaFormula::Boolean { op, args } = &problem.formula else {
            panic!("omega Boolean input should normalize to a Boolean formula");
        };
        assert_eq!(*op, OmegaBooleanOp::And);
        assert_eq!(args.len(), 2);
        let OmegaFormula::Atom(nat_atom) = &args[0] else {
            panic!("first omega conjunct should be an atom");
        };
        assert_eq!(nat_atom.relation, OmegaComparisonOp::Le);
        assert_eq!(
            nat_atom.normalized_lhs_minus_rhs,
            OmegaLinearTerm {
                coefficients: vec![0, 0],
                constant: -1,
            }
        );
        let OmegaFormula::Atom(int_atom) = &args[1] else {
            panic!("second omega conjunct should be an atom");
        };
        assert_eq!(int_atom.relation, OmegaComparisonOp::Lt);
        assert_eq!(
            int_atom.normalized_lhs_minus_rhs,
            OmegaLinearTerm {
                coefficients: vec![0, 1],
                constant: -5,
            }
        );

        let first_hash = omega_normalized_problem_hash(&problem).unwrap();
        let second_hash = omega_normalized_problem_hash(&problem).unwrap();
        assert_eq!(first_hash, second_hash);
        assert_eq!(
            omega_normalized_problem_canonical_bytes(&problem).unwrap(),
            omega_normalized_problem_canonical_bytes(&problem).unwrap()
        );
        let usage = omega_resource_usage_from_normalized_problem(&problem).unwrap();
        assert_eq!(usage.input_nodes, problem.input_nodes);
        assert_eq!(usage.solver_steps, problem.normalized_nodes);
    }

    #[test]
    fn omega_fragment_bounded_quantifier_expansion_is_separately_budgeted() {
        let policy = omega_policy();
        let request = omega_request_for_policy(&policy);
        let mut options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let context = omega_context(&[("i", OmegaTermSort::Int)]);
        let case_zero = omega_app2("Int.le", omega_int_lit(0), Expr::bvar(0));
        let case_one = omega_app2("Int.lt", Expr::bvar(0), omega_int_lit(4));
        let target = omega_appn(
            "Omega.bforall",
            vec![omega_nat_lit(2), case_zero.clone(), case_one.clone()],
        );

        let problem = omega_normalize_problem(&request, &context, &target, &options).unwrap();
        assert_eq!(
            problem.fragment_profile,
            OmegaFragmentProfile::BoundedQuantifierExpansionV1
        );
        assert_eq!(problem.bounded_expansions.len(), 1);
        assert_eq!(
            problem.bounded_expansions[0].kind,
            OmegaBoundedQuantifierKind::Forall
        );
        assert_eq!(problem.bounded_expansions[0].bound, 2);
        assert_eq!(
            problem.bounded_expansions[0].expanded_case_hashes,
            vec![core_expr_hash(&case_zero), core_expr_hash(&case_one)]
        );
        let OmegaFormula::Boolean { op, args } = &problem.formula else {
            panic!("bounded forall should expand into a Boolean conjunction");
        };
        assert_eq!(*op, OmegaBooleanOp::And);
        assert_eq!(args.len(), 2);

        options.max_bounded_quantifier_cases = 1;
        assert_eq!(
            omega_normalize_problem(&request, &context, &target, &options),
            Err(SolverContractError::OmegaBoundedExpansionOverBudget {
                limit_cases: 1,
                actual_cases: 2,
            })
        );
    }

    #[test]
    fn omega_fragment_rejects_nonlinear_unsupported_missing_side_conditions_and_budget() {
        let policy = omega_policy();
        let request = omega_request_for_policy(&policy);
        let options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let int_context = omega_context(&[("i", OmegaTermSort::Int)]);
        let nonlinear = omega_app2(
            "Int.le",
            omega_app2("Int.mul", Expr::bvar(0), Expr::bvar(0)),
            omega_int_lit(4),
        );
        assert_eq!(
            omega_normalize_problem(&request, &int_context, &nonlinear, &options),
            Err(SolverContractError::NonlinearOmegaTerm {
                operator: "Int.mul".to_owned(),
            })
        );

        let unsupported = omega_app2(
            "Int.le",
            omega_app2("Int.div", Expr::bvar(0), omega_int_lit(2)),
            omega_int_lit(4),
        );
        assert_eq!(
            omega_normalize_problem(&request, &int_context, &unsupported, &options),
            Err(SolverContractError::UnsupportedOmegaOperator {
                operator: "Int.div".to_owned(),
            })
        );

        let unsupported_nat_sub = omega_app2(
            "Nat.le",
            omega_app2("Nat.sub", Expr::bvar(0), omega_nat_lit(1)),
            omega_nat_lit(4),
        );
        let nat_context = omega_context(&[("n", OmegaTermSort::Nat)]);
        assert_eq!(
            omega_normalize_problem(&request, &nat_context, &unsupported_nat_sub, &options),
            Err(SolverContractError::UnsupportedOmegaOperator {
                operator: "Nat.sub".to_owned(),
            })
        );

        let nat_goal = omega_app2("Nat.le", Expr::bvar(0), omega_nat_lit(4));
        let mut problem = omega_normalize_problem(&request, &nat_context, &nat_goal, &options)
            .expect("Nat variable should require an explicit side condition");
        problem.nat_to_int_side_conditions.clear();
        assert_eq!(
            validate_omega_normalized_problem(&problem),
            Err(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: 0,
            })
        );

        let mut problem = omega_normalize_problem(&request, &nat_context, &nat_goal, &options)
            .expect("Nat variable should normalize before side-condition mutation");
        problem.nat_to_int_side_conditions[0].discharge = OmegaNatToIntDischarge::Missing;
        assert_eq!(
            validate_omega_normalized_problem(&problem),
            Err(SolverContractError::MissingOmegaSideConditionDischarge {
                variable_ordinal: 0,
            })
        );

        let mut problem = omega_normalize_problem(&request, &nat_context, &nat_goal, &options)
            .expect("Nat variable should normalize before side-condition identity mutation");
        problem.nat_to_int_side_conditions[0].source_core_expr_hash = hash(99);
        assert!(matches!(
            validate_omega_normalized_problem(&problem),
            Err(SolverContractError::MismatchedHash {
                field: "omega_nat_to_int_source_core_expr_hash",
                ..
            })
        ));

        let mut problem = omega_normalize_problem(&request, &nat_context, &nat_goal, &options)
            .expect("Nat variable should normalize before side-condition duplication");
        problem
            .nat_to_int_side_conditions
            .push(problem.nat_to_int_side_conditions[0].clone());
        assert_eq!(
            validate_omega_normalized_problem(&problem),
            Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "omega_nat_to_int_side_condition_order",
            })
        );

        let mut tiny_options = options.clone();
        tiny_options.max_input_nodes = 1;
        assert_eq!(
            omega_normalize_problem(&request, &int_context, &unsupported, &tiny_options),
            Err(SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                limit: 1,
                actual: 2,
            })
        );
    }

    #[test]
    fn ring_nf_reflection_semiring_normalizes_and_hashes_stably() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::SemiringV1,
        )
        .unwrap();
        let context = ring_nf_context(&[("x", "Nat")]);
        let lhs = ring_nf_app2(
            "Nat.add",
            Expr::bvar(0),
            ring_nf_app2("Nat.mul", ring_nf_nat_lit(2), Expr::bvar(0)),
        );
        let rhs = ring_nf_app2("Nat.mul", ring_nf_nat_lit(3), Expr::bvar(0));
        let target = ring_nf_eq("Nat", lhs, rhs);

        let problem = ring_nf_normalize_problem(&request, &context, &target, &options).unwrap();
        validate_ring_nf_normalized_problem(&problem).unwrap();

        assert_eq!(problem.algebra_profile, RingNfAlgebraProfile::SemiringV1);
        assert_eq!(problem.coefficient_domain, RingNfCoefficientDomain::Nat);
        assert_eq!(problem.variables.len(), 1);
        assert_eq!(problem.variables[0].name, "x");
        assert_eq!(
            problem.equation.lhs_normal_form,
            RingNfPolynomial {
                monomials: vec![RingNfMonomial {
                    coefficient: 3,
                    exponents: vec![1],
                }],
            }
        );
        assert_eq!(
            problem.equation.lhs_normal_form,
            problem.equation.rhs_normal_form
        );
        assert!(problem.equation.normal_forms_equal);
        assert_eq!(problem.equation.difference_normal_form, None);
        assert_eq!(
            ring_nf_normalized_problem_hash(&problem).unwrap(),
            ring_nf_normalized_problem_hash(&problem).unwrap()
        );
        assert_eq!(
            ring_nf_normalized_problem_canonical_bytes(&problem).unwrap(),
            ring_nf_normalized_problem_canonical_bytes(&problem).unwrap()
        );
        let usage = ring_nf_resource_usage_from_normalized_problem(&problem).unwrap();
        assert_eq!(usage.input_nodes, problem.input_nodes);
        assert_eq!(usage.solver_steps, problem.normalized_nodes);
    }

    #[test]
    fn ring_nf_reflection_ring_profile_allows_negation_subtraction_and_difference() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::RingV1,
        )
        .unwrap();
        let context = ring_nf_context(&[("x", "Int")]);
        let lhs = ring_nf_app2(
            "Int.sub",
            ring_nf_app2("Int.add", Expr::bvar(0), ring_nf_int_lit(5)),
            ring_nf_int_lit(2),
        );
        let rhs = ring_nf_app2("Int.add", Expr::bvar(0), ring_nf_int_lit(3));
        let target = ring_nf_eq("Int", lhs, rhs);

        let problem = ring_nf_normalize_problem(&request, &context, &target, &options).unwrap();
        validate_ring_nf_normalized_problem(&problem).unwrap();

        assert_eq!(problem.algebra_profile, RingNfAlgebraProfile::RingV1);
        assert_eq!(problem.coefficient_domain, RingNfCoefficientDomain::Int);
        assert!(problem.equation.normal_forms_equal);
        assert_eq!(
            problem.equation.difference_normal_form,
            Some(RingNfPolynomial {
                monomials: Vec::new(),
            })
        );

        let neg_lhs = Expr::apps(Expr::konst("Int.neg", vec![]), [Expr::bvar(0)]);
        let neg_rhs = ring_nf_app2("Int.mul", ring_nf_int_lit(-1), Expr::bvar(0));
        let neg_problem = ring_nf_normalize_problem(
            &request,
            &context,
            &ring_nf_eq("Int", neg_lhs, neg_rhs),
            &options,
        )
        .unwrap();
        assert!(neg_problem.equation.normal_forms_equal);
    }

    #[test]
    fn ring_nf_reflection_commutative_profiles_reorder_monomials_and_support_powers() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeRingV1,
        )
        .unwrap();
        let context = ring_nf_context(&[("x", "Int"), ("y", "Int")]);
        let xy = ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(0));
        let yx = ring_nf_app2("Int.mul", Expr::bvar(0), Expr::bvar(1));
        let problem =
            ring_nf_normalize_problem(&request, &context, &ring_nf_eq("Int", xy, yx), &options)
                .unwrap();

        assert!(problem.equation.normal_forms_equal);
        assert_eq!(
            problem.equation.lhs_normal_form,
            RingNfPolynomial {
                monomials: vec![RingNfMonomial {
                    coefficient: 1,
                    exponents: vec![1, 1],
                }],
            }
        );

        let pow = ring_nf_app2("Int.pow", Expr::bvar(1), ring_nf_nat_lit(2));
        let square = ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(1));
        let pow_problem = ring_nf_normalize_problem(
            &request,
            &context,
            &ring_nf_eq("Int", pow, square),
            &options,
        )
        .unwrap();
        assert!(pow_problem.equation.normal_forms_equal);
    }

    #[test]
    fn ring_nf_reflection_rejects_profile_violations_and_noncommutative_multiplication() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let semiring_options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::SemiringV1,
        )
        .unwrap();
        let nat_context = ring_nf_context(&[("x", "Nat")]);
        let subtraction = ring_nf_app2("Nat.sub", Expr::bvar(0), ring_nf_nat_lit(1));
        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &nat_context,
                &ring_nf_eq("Nat", subtraction, Expr::bvar(0)),
                &semiring_options
            ),
            Err(SolverContractError::UnsupportedRingNfOperation {
                profile: RingNfAlgebraProfile::SemiringV1,
                operator: "Nat.sub".to_owned(),
            })
        );

        let ring_options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::RingV1,
        )
        .unwrap();
        let int_context = ring_nf_context(&[("x", "Int"), ("y", "Int")]);
        let product = ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(0));
        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &int_context,
                &ring_nf_eq("Int", product, Expr::bvar(1)),
                &ring_options
            ),
            Err(SolverContractError::NonCommutativeRingNfTerm {
                operator: "mul".to_owned(),
            })
        );

        let bad_profile = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::RingV1,
        )
        .unwrap();
        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &nat_context,
                &ring_nf_eq("Nat", Expr::bvar(0), Expr::bvar(0)),
                &bad_profile
            ),
            Err(SolverContractError::UnsupportedRingNfFragment {
                reason: "ring_nf ring profiles require an Int carrier in this contract",
            })
        );
    }

    #[test]
    fn ring_nf_reflection_rejects_coefficient_overflow_monomial_budget_and_stale_normal_forms() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let mut options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeSemiringV1,
        )
        .unwrap();
        options.max_coefficient_abs = 4;
        let context = ring_nf_context(&[("x", "Nat")]);
        let over_coeff = ring_nf_app2("Nat.mul", ring_nf_nat_lit(5), Expr::bvar(0));
        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &context,
                &ring_nf_eq("Nat", over_coeff, Expr::bvar(0)),
                &options
            ),
            Err(SolverContractError::RingNfCoefficientOverflow)
        );

        let mut budget_options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeSemiringV1,
        )
        .unwrap();
        budget_options.max_monomials = 1;
        let two_monomials = ring_nf_app2("Nat.add", Expr::bvar(0), ring_nf_nat_lit(1));
        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &context,
                &ring_nf_eq("Nat", two_monomials, Expr::bvar(0)),
                &budget_options
            ),
            Err(SolverContractError::RingNfMonomialOverBudget {
                limit: 1,
                actual: 2,
            })
        );

        let mut degree_options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeSemiringV1,
        )
        .unwrap();
        degree_options.max_total_degree = 1;
        let over_degree_constant_pow =
            ring_nf_app2("Nat.pow", ring_nf_nat_lit(2), ring_nf_nat_lit(2));
        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &context,
                &ring_nf_eq("Nat", over_degree_constant_pow, ring_nf_nat_lit(4)),
                &degree_options
            ),
            Err(SolverContractError::RingNfDegreeOverBudget {
                limit: 1,
                actual: 2,
            })
        );

        let ok_options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeSemiringV1,
        )
        .unwrap();
        let mut problem = ring_nf_normalize_problem(
            &request,
            &context,
            &ring_nf_eq("Nat", Expr::bvar(0), Expr::bvar(0)),
            &ok_options,
        )
        .unwrap();
        problem.equation.rhs_normal_form.monomials[0].coefficient = 2;
        assert_eq!(
            validate_ring_nf_normalized_problem(&problem),
            Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "ring_nf_rhs_normal_form",
            })
        );
    }

    #[test]
    fn ring_nf_reconstruction_checked_proof_response_binds_hashes_laws_policy_and_size() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let context = ring_nf_context(&[("x", "Int"), ("y", "Int")]);
        let xy = ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(0));
        let yx = ring_nf_app2("Int.mul", Expr::bvar(0), Expr::bvar(1));
        let target = ring_nf_eq("Int", xy, yx);
        let problem = ring_nf_reconstruction_problem(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeRingV1,
            &context,
            &target,
        );
        let artifact = ring_nf_proof_artifact(&request, &problem);

        validate_ring_nf_proof_artifact_for_problem(&request, &problem, &artifact).unwrap();
        assert_eq!(
            ring_nf_proof_artifact_hash(&artifact).unwrap(),
            ring_nf_proof_artifact_hash(&artifact).unwrap()
        );
        assert!(artifact
            .algebra_law_refs
            .iter()
            .any(|law_ref| law_ref.law == RingNfAlgebraLawKind::ReflectionSoundness));
        assert!(artifact
            .algebra_law_refs
            .iter()
            .any(|law_ref| law_ref.law == RingNfAlgebraLawKind::CommutativeReordering));

        let response = ring_nf_checked_proof_response(&request, &problem, &artifact, &policy)
            .expect(
                "matching normal forms with explicit laws should produce checked proof metadata",
            );
        validate_solver_response_for_request(&request, &response).unwrap();
        assert_eq!(response.status, SolverResponseStatus::Certificate);
        assert_eq!(
            response.metadata.certificate_format,
            Some(SolverCertificateFormat::DirectNpaProofTermV1)
        );
        assert!(matches!(
            solver_response_accepting_payload(&response),
            Ok(SolverAcceptingPayload::CheckedProofTerm(identity))
                if identity == &artifact.proof_identity
        ));
        let replay = solver_replay_metadata_for_response(&request, &response, &policy).unwrap();
        validate_solver_replay_metadata(&request, &response, &policy, &replay).unwrap();

        let usage = ring_nf_resource_usage_from_proof_artifact(&problem, &artifact).unwrap();
        assert_eq!(usage.generated_term_nodes, artifact.generated_term_nodes);
        assert_eq!(usage.proof_bytes, artifact.proof_bytes);
        assert_eq!(usage.proof_steps, artifact.proof_steps);
        assert_eq!(usage.rule_count, artifact.algebra_law_refs.len() as u64);
    }

    #[test]
    fn ring_nf_reconstruction_rejects_mismatched_normal_forms_stale_maps_wrong_profile_missing_law_and_budget(
    ) {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let context = ring_nf_context(&[("x", "Int"), ("y", "Int")]);
        let xy = ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(0));
        let yx = ring_nf_app2("Int.mul", Expr::bvar(0), Expr::bvar(1));
        let equal_problem = ring_nf_reconstruction_problem(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeRingV1,
            &context,
            &ring_nf_eq("Int", xy, yx),
        );
        let artifact = ring_nf_proof_artifact(&request, &equal_problem);

        let unequal_problem = ring_nf_reconstruction_problem(
            &policy,
            &request,
            RingNfAlgebraProfile::CommutativeRingV1,
            &context,
            &ring_nf_eq("Int", Expr::bvar(1), ring_nf_int_lit(0)),
        );
        let unequal_artifact = ring_nf_proof_artifact(&request, &unequal_problem);
        assert_eq!(
            validate_ring_nf_proof_artifact_for_problem(
                &request,
                &unequal_problem,
                &unequal_artifact
            ),
            Err(SolverContractError::RingNfNormalFormsMismatch)
        );

        let mut stale_environment = artifact.clone();
        stale_environment.variable_environment[0].source_core_expr_hash = hash(231);
        stale_environment.variable_environment_hash =
            ring_nf_variable_environment_hash(&stale_environment.variable_environment).unwrap();
        assert!(matches!(
            validate_ring_nf_proof_artifact_for_problem(
                &request,
                &equal_problem,
                &stale_environment
            ),
            Err(SolverContractError::MismatchedHash {
                field: "ring_nf_variable_source_hash",
                ..
            })
        ));

        let mut wrong_profile = artifact.clone();
        wrong_profile.algebra_law_refs[0].profile = RingNfAlgebraProfile::SemiringV1;
        assert!(matches!(
            validate_ring_nf_proof_artifact_for_problem(&request, &equal_problem, &wrong_profile),
            Err(SolverContractError::MismatchedRingNfAlgebraLawProfile { .. })
        ));

        let mut missing_law = artifact.clone();
        missing_law
            .algebra_law_refs
            .retain(|law_ref| law_ref.law != RingNfAlgebraLawKind::CommutativeReordering);
        assert_eq!(
            validate_ring_nf_proof_artifact_for_problem(&request, &equal_problem, &missing_law),
            Err(SolverContractError::MissingRingNfAlgebraLaw {
                law: RingNfAlgebraLawKind::CommutativeReordering,
            })
        );

        let mut tiny_policy = policy;
        tiny_policy.max_generated_term_nodes = 1;
        let tiny_request = ring_nf_request_for_policy(&tiny_policy);
        let tiny_problem = ring_nf_reconstruction_problem(
            &tiny_policy,
            &tiny_request,
            RingNfAlgebraProfile::CommutativeRingV1,
            &context,
            &ring_nf_eq(
                "Int",
                ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(0)),
                ring_nf_app2("Int.mul", Expr::bvar(0), Expr::bvar(1)),
            ),
        );
        let tiny_artifact = ring_nf_proof_artifact(&tiny_request, &tiny_problem);
        assert_eq!(
            ring_nf_checked_proof_response(
                &tiny_request,
                &tiny_problem,
                &tiny_artifact,
                &tiny_policy
            ),
            Err(SolverContractError::ReconstructionTermTooLarge {
                limit_nodes: 1,
                actual_nodes: tiny_artifact.generated_term_nodes,
            })
        );
    }

    #[test]
    fn ring_nf_reconstruction_rejects_unsupported_exponentiation_before_proof_acceptance() {
        let policy = ring_nf_policy();
        let request = ring_nf_request_for_policy(&policy);
        let context = ring_nf_context(&[("x", "Int")]);
        let options = ring_nf_normalization_options_from_policy(
            &policy,
            &request,
            RingNfAlgebraProfile::RingV1,
        )
        .unwrap();
        let pow = ring_nf_app2("Int.pow", Expr::bvar(0), ring_nf_nat_lit(2));

        assert_eq!(
            ring_nf_normalize_problem(
                &request,
                &context,
                &ring_nf_eq("Int", pow, Expr::bvar(0)),
                &options
            ),
            Err(SolverContractError::UnsupportedRingNfOperation {
                profile: RingNfAlgebraProfile::RingV1,
                operator: "Int.pow".to_owned(),
            })
        );
    }

    #[test]
    fn smt_nat_to_int_side_condition_hash_is_reused_by_omega_fragment() {
        let policy = omega_policy();
        let request = omega_request_for_policy(&policy);
        let options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let context = omega_context(&[("n", OmegaTermSort::Nat)]);
        let target = omega_app2("Nat.le", Expr::bvar(0), omega_nat_lit(1));

        let problem = omega_normalize_problem(&request, &context, &target, &options).unwrap();
        let side_condition = &problem.nat_to_int_side_conditions[0];
        let expected_smt_side_condition = advanced_ai_smt_nat_to_int_side_condition(
            Expr::bvar(0),
            side_condition.int_symbol.clone(),
        );

        assert_eq!(
            side_condition.smt_side_condition_hash,
            advanced_ai_smt_nat_to_int_side_condition_hash(&expected_smt_side_condition)
        );
        assert_eq!(
            side_condition.source_core_expr_hash,
            core_expr_hash(&Expr::bvar(0))
        );
        assert!(matches!(
            side_condition.discharge,
            OmegaNatToIntDischarge::ProofObligation { .. }
        ));
    }

    #[test]
    fn omega_reconstruction_accepts_rule_trace_and_replay_metadata_without_trusting_search() {
        let (policy, request, problem) = omega_reconstruction_fixture();
        let artifact = omega_valid_certificate(&request, &problem);

        validate_omega_certificate_artifact_for_problem(&request, &problem, &artifact).unwrap();
        let response =
            omega_checked_certificate_response(&request, &problem, &artifact, &policy).unwrap();
        validate_solver_response_for_request(&request, &response).unwrap();

        let SolverResponsePayload::Certificate(
            SolverAcceptingPayload::CheckedCertificateReconstruction(metadata),
        ) = &response.payload
        else {
            panic!("omega response should be a checked reconstruction certificate");
        };
        assert_eq!(metadata.family, SolverFamily::Omega);
        assert_eq!(
            metadata.certificate_format,
            SolverCertificateFormat::OmegaPresburgerTraceV1
        );
        assert_eq!(
            response.metadata.payload_hash,
            Some(
                solver_inline_payload_hash(
                    SolverCertificateFormat::OmegaPresburgerTraceV1,
                    &omega_certificate_artifact_canonical_bytes(&artifact).unwrap()
                )
                .unwrap()
            )
        );
        assert_eq!(
            artifact.normalized_problem_hash,
            omega_normalized_problem_hash(&problem).unwrap()
        );
        assert_eq!(artifact.policy_hash, request.policy_hash);

        let first_response_hash = solver_response_identity_hash(&response).unwrap();
        let second_response =
            omega_checked_certificate_response(&request, &problem, &artifact, &policy).unwrap();
        assert_eq!(
            first_response_hash,
            solver_response_identity_hash(&second_response).unwrap()
        );

        let replay = solver_replay_metadata_for_response(&request, &response, &policy).unwrap();
        validate_solver_replay_metadata(&request, &response, &policy, &replay).unwrap();
        assert_eq!(
            omega_reconstruction_plan_for_certificate(&artifact)
                .unwrap()
                .final_step_id
                .as_deref(),
            Some("contra")
        );
    }

    #[test]
    fn omega_reconstruction_rejects_malformed_wrong_coefficients_missing_side_conditions_and_unsupported_fragments(
    ) {
        let (policy, request, problem) = omega_reconstruction_fixture();
        let artifact = omega_valid_certificate(&request, &problem);

        let mut wrong_problem_hash = artifact.clone();
        wrong_problem_hash.normalized_problem_hash = hash(77);
        assert!(matches!(
            validate_omega_certificate_artifact_for_problem(
                &request,
                &problem,
                &wrong_problem_hash
            ),
            Err(SolverContractError::MismatchedHash {
                field: "omega_normalized_problem_hash",
                ..
            })
        ));

        let mut wrong_coefficients = artifact.clone();
        wrong_coefficients.steps[0].coefficients[0] = 9;
        assert!(matches!(
            validate_omega_certificate_artifact_for_problem(
                &request,
                &problem,
                &wrong_coefficients
            ),
            Err(SolverContractError::MismatchedHash {
                field: "omega_step_result_hash",
                ..
            })
        ));

        let mut multi_atom_comparison = artifact.clone();
        multi_atom_comparison.steps[0].atom_indices.push(1);
        multi_atom_comparison.steps[0].result_hash =
            omega_reconstruction_step_result_hash(&multi_atom_comparison.steps[0]).unwrap();
        assert_eq!(
            validate_omega_certificate_artifact_for_problem(
                &request,
                &problem,
                &multi_atom_comparison
            ),
            Err(SolverContractError::NonCanonicalPayloadBytes {
                field: "omega_comparison_atom_index",
            })
        );

        let mut missing_side_condition = problem.clone();
        missing_side_condition.nat_to_int_side_conditions.clear();
        assert_eq!(
            validate_omega_certificate_artifact_for_problem(
                &request,
                &missing_side_condition,
                &artifact
            ),
            Err(SolverContractError::MissingOmegaSideCondition {
                variable_ordinal: 0,
            })
        );

        let options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let bounded_target = omega_appn(
            "Omega.bforall",
            vec![
                omega_nat_lit(2),
                omega_app2("Int.le", omega_int_lit(0), Expr::bvar(0)),
                omega_app2("Int.lt", Expr::bvar(0), omega_int_lit(4)),
            ],
        );
        let bounded_problem = omega_normalize_problem(
            &request,
            &omega_context(&[("i", OmegaTermSort::Int)]),
            &bounded_target,
            &options,
        )
        .unwrap();
        assert_eq!(
            validate_omega_certificate_artifact_for_problem(&request, &bounded_problem, &artifact),
            Err(SolverContractError::UnsupportedOmegaFragment {
                reason: "omega reconstruction accepts only linear arithmetic normalized problems",
            })
        );

        let mut wrong_policy = artifact;
        wrong_policy.policy_hash = hash(88);
        assert!(matches!(
            validate_omega_certificate_artifact_for_problem(&request, &problem, &wrong_policy),
            Err(SolverContractError::MismatchedHash {
                field: "omega_policy_hash",
                ..
            })
        ));
    }

    #[test]
    fn omega_reconstruction_enforces_resource_policy_deterministically() {
        let mut policy = omega_policy();
        policy.max_certificate_bytes = 16;
        let request = omega_request_for_policy(&policy);
        let options = omega_normalization_options_from_policy(&policy, &request).unwrap();
        let context = omega_context(&[("n", OmegaTermSort::Nat), ("i", OmegaTermSort::Int)]);
        let target = omega_appn(
            "Bool.and",
            vec![
                omega_app2(
                    "Nat.le",
                    omega_app2("Nat.add", Expr::bvar(1), omega_nat_lit(3)),
                    omega_app2("Nat.add", Expr::bvar(1), omega_nat_lit(2)),
                ),
                omega_app2("Int.lt", Expr::bvar(0), omega_int_lit(4)),
            ],
        );
        let problem = omega_normalize_problem(&request, &context, &target, &options).unwrap();
        let artifact = omega_valid_certificate(&request, &problem);

        let first = omega_checked_certificate_response(&request, &problem, &artifact, &policy);
        let second = omega_checked_certificate_response(&request, &problem, &artifact, &policy);

        assert!(matches!(
            first,
            Err(SolverContractError::CertificateTooLarge {
                limit_bytes: 16,
                ..
            })
        ));
        assert_eq!(first, second);
    }

    #[test]
    fn solver_resource_policy_enforces_pre_execution_and_generated_artifact_limits() {
        let finite_policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::FiniteDecideDefaultV1);
        let finite_request = request_for_resource_policy(&finite_policy);
        assert_eq!(
            enforce_solver_pre_execution_resource_policy(
                &finite_policy,
                &finite_request,
                SolverResourceUsage {
                    input_nodes: finite_policy.max_input_nodes + 1,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::ResourceLimitExceeded {
                field: SolverResourceField::InputNodes,
                limit: finite_policy.max_input_nodes,
                actual: finite_policy.max_input_nodes + 1,
            })
        );

        let mut wrong_fragment = finite_request.clone();
        wrong_fragment.fragment = SolverFragment::SmtQfUfV1;
        assert_eq!(
            validate_solver_resource_policy_for_request(&finite_policy, &wrong_fragment),
            Err(SolverContractError::UnsupportedFragment {
                family: SolverFamily::FiniteDecide,
                fragment: SolverFragment::SmtQfUfV1,
            })
        );

        let mut smt_policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::SmtReconstructionDefaultV1);
        smt_policy.max_certificate_bytes = 4;
        smt_policy.max_generated_term_nodes = 2;
        smt_policy.max_proof_steps = 3;
        let smt_request = request_for_resource_policy(&smt_policy);
        let response = certificate_response_for_request(&smt_request);
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &smt_policy,
                &smt_request,
                &response,
                SolverResourceUsage {
                    certificate_bytes: 5,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::CertificateTooLarge {
                limit_bytes: 4,
                actual_bytes: 5,
            })
        );
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &smt_policy,
                &smt_request,
                &response,
                SolverResourceUsage {
                    generated_term_nodes: 3,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::ReconstructionTermTooLarge {
                limit_nodes: 2,
                actual_nodes: 3,
            })
        );
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &smt_policy,
                &smt_request,
                &response,
                SolverResourceUsage {
                    proof_steps: 4,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::ProofSearchExhausted {
                field: SolverResourceField::ProofSteps,
                limit: 3,
                actual: 4,
            })
        );
    }

    #[test]
    fn solver_resource_policy_timeout_memory_and_output_do_not_validate_accepting_response() {
        let mut policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::SmtReconstructionDefaultV1);
        policy.max_memory_bytes = 10;
        policy.max_wall_clock_millis = 20;
        policy.max_output_bytes = 30;
        let request = request_for_resource_policy(&policy);
        let response = certificate_response_for_request(&request);

        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &policy,
                &request,
                &response,
                SolverResourceUsage {
                    memory_bytes: 11,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::MemoryLimit {
                limit_bytes: 10,
                actual_bytes: 11,
            })
        );
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &policy,
                &request,
                &response,
                SolverResourceUsage {
                    wall_clock_millis: 21,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::Timeout {
                field: SolverResourceField::WallClockMillis,
                limit_millis: 20,
                actual_millis: 21,
            })
        );
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &policy,
                &request,
                &response,
                SolverResourceUsage {
                    output_bytes: 31,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::OutputLimit {
                limit_bytes: 30,
                actual_bytes: 31,
            })
        );
    }

    #[test]
    fn solver_resource_policy_replay_metadata_binds_policy_hash() {
        let policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::SmtReconstructionDefaultV1);
        let request = request_for_resource_policy(&policy);
        let response = certificate_response_for_request(&request);
        let metadata = solver_replay_metadata_for_response(&request, &response, &policy).unwrap();
        validate_solver_replay_metadata(&request, &response, &policy, &metadata).unwrap();

        let mut changed_policy = policy.clone();
        changed_policy.max_output_bytes += 1;
        assert_ne!(
            solver_resource_policy_hash(&policy).unwrap(),
            solver_resource_policy_hash(&changed_policy).unwrap()
        );
        assert_ne!(
            solver_request_hash(&request).unwrap(),
            solver_request_hash(&request_for_resource_policy(&changed_policy)).unwrap()
        );
        assert!(matches!(
            validate_solver_resource_policy_for_request(&changed_policy, &request),
            Err(SolverContractError::MismatchedHash {
                field: "policy_hash",
                ..
            })
        ));

        let mut relabeled = response.clone();
        relabeled.metadata.policy_hash = solver_resource_policy_hash(&changed_policy).unwrap();
        assert!(matches!(
            validate_solver_response_for_request(&request, &relabeled),
            Err(SolverContractError::MismatchedHash {
                field: "policy_hash",
                ..
            })
        ));

        let mut stale_metadata = metadata;
        stale_metadata.resource_policy_hash = solver_resource_policy_hash(&changed_policy).unwrap();
        assert!(matches!(
            validate_solver_replay_metadata(&request, &response, &policy, &stale_metadata),
            Err(SolverContractError::MismatchedHash {
                field: "resource_policy_hash",
                ..
            })
        ));
    }

    #[test]
    fn smt_resource_limits_bridge_counts_advanced_smt_sidecar_usage() {
        let (candidate, problem) = advanced_smt_candidate_fixture();
        let usage = solver_resource_usage_from_advanced_smt_candidate(&candidate, Some(&problem))
            .expect("advanced SMT sidecar usage should be measurable");
        assert!(usage.input_bytes > 0);
        assert_eq!(usage.certificate_bytes, 5);
        assert_eq!(usage.proof_bytes, 5);
        assert_eq!(usage.nested_solver_calls, 0);

        let mut policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::SmtReconstructionDefaultV1);
        policy.max_certificate_bytes = usage.certificate_bytes - 1;
        let request = request_for_resource_policy(&policy);
        let response = certificate_response_for_request(&request);
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(&policy, &request, &response, usage,),
            Err(SolverContractError::CertificateTooLarge {
                limit_bytes: 4,
                actual_bytes: 5,
            })
        );
    }

    struct SolverFixtureMatrixExpectation {
        id: &'static str,
        family: &'static str,
        positive_test: &'static str,
        negative_test: &'static str,
        modules: &'static [&'static str],
        ws08: &'static [&'static str],
        negative_acceptance: &'static [&'static str],
        metrics: &'static [&'static str],
    }

    fn assert_matrix_string(matrix: &str, field: &str, value: &str) {
        let token = format!(r#""{field}": "{value}""#);
        assert!(
            matrix.contains(&token),
            "missing fixture matrix token {token}"
        );
    }

    fn assert_matrix_list_item(matrix: &str, value: &str) {
        let token = format!(r#""{value}""#);
        assert!(
            matrix.contains(&token),
            "missing fixture matrix item {token}"
        );
    }

    fn fixture_matrix_row<'a>(matrix: &'a str, id: &str) -> &'a str {
        let id_token = format!(r#""id": "{id}""#);
        let id_pos = matrix
            .find(&id_token)
            .unwrap_or_else(|| panic!("missing fixture matrix row {id}"));
        let row_start = matrix[..id_pos]
            .rfind('{')
            .unwrap_or_else(|| panic!("missing fixture matrix row start for {id}"));
        let row_end = matrix[id_pos..]
            .find("\n    }")
            .map(|offset| id_pos + offset)
            .unwrap_or_else(|| panic!("missing fixture matrix row end for {id}"));
        &matrix[row_start..row_end]
    }

    fn metric_value(usage: SolverResourceUsage, metric: &str) -> u64 {
        match metric {
            "input_nodes" => usage.input_nodes,
            "proof_bytes" => usage.proof_bytes,
            "certificate_bytes" => usage.certificate_bytes,
            "generated_term_nodes" => usage.generated_term_nodes,
            "proof_steps" | "reconstruction_steps" => usage.proof_steps,
            "cnf_size" => usage.cnf_clauses,
            "lrat_size" => usage.certificate_bytes,
            "resource_policy_outcomes" => 1,
            other => panic!("unknown solver metric fixture field {other}"),
        }
    }

    fn assert_solver_metrics(label: &str, usage: SolverResourceUsage, metrics: &[&str]) {
        for metric in metrics {
            let value = metric_value(usage, metric);
            assert!(
                value > 0,
                "{label} fixture metric {metric} should be present and nonzero"
            );
        }
        assert_eq!(
            usage.wall_clock_millis, 0,
            "{label} fixture metrics must not use measured wall-clock as proof evidence"
        );
    }

    fn assert_solver_response_advisory_is_sidecar(
        label: &str,
        request: &SolverRequest,
        response: &SolverResponse,
        policy: &SolverResourcePolicy,
    ) {
        validate_solver_response_for_request(request, response).unwrap();
        let replay = solver_replay_metadata_for_response(request, response, policy).unwrap();
        validate_solver_replay_metadata(request, response, policy, &replay).unwrap();
        let response_identity = solver_response_identity_hash(response).unwrap();
        let replay_identity = solver_replay_metadata_hash(&replay).unwrap();

        let mut changed = response.clone();
        changed.advisory = SolverResponseAdvisory {
            display_text: Some(format!("{label} regression metrics")),
            diagnostic_prose: Some("metrics are advisory sidecars".to_owned()),
            raw_solver_stdout: Some("solver stdout is not proof evidence".to_owned()),
            raw_solver_stderr: Some("solver stderr is not proof evidence".to_owned()),
            measured_wall_clock_ms: Some(99),
            ranking_score: Some(42),
        };
        validate_solver_response_for_request(request, &changed).unwrap();
        assert_eq!(
            response_identity,
            solver_response_identity_hash(&changed).unwrap(),
            "{label} advisory metric fields must not change response identity"
        );
        let changed_replay =
            solver_replay_metadata_for_response(request, &changed, policy).unwrap();
        validate_solver_replay_metadata(request, &changed, policy, &changed_replay).unwrap();
        assert_eq!(
            replay_identity,
            solver_replay_metadata_hash(&changed_replay).unwrap(),
            "{label} advisory metric fields must not change replay identity"
        );
        assert!(solver_response_accepting_payload(&changed).is_ok());
    }

    #[test]
    fn solver_fixture_matrix_covers_source_free_replay_metrics_and_negative_acceptance() {
        let matrix = include_str!(
            "../../../testdata/proof-using-agents/fixtures/pua-m09-solver-fixture-matrix.json"
        );
        assert_matrix_string(
            matrix,
            "schema_version",
            "npa.pua-m09.solver-fixture-matrix.v1",
        );
        assert!(matrix.contains(r#""advisory_sidecar": true"#));
        assert_matrix_string(matrix, "proof_acceptance_effect", "none");
        for command in [
            "cargo test -p npa-api solver -- --skip proof_corpus --skip proof_package",
            "cargo test -p npa-tactic solver -- --skip proof_corpus --skip proof_package",
            "cargo test -p npa-frontend solver -- --skip proof_corpus --skip proof_package",
            "cargo run -p npa-proof-corpus -- --changed-only --verified-cache authoring",
            "./scripts/check-fast.sh",
            "./scripts/check-corpus-authoring.sh",
        ] {
            assert_matrix_list_item(matrix, command);
        }
        for module in [
            "crates/npa-api/src/solver.rs::tests",
            "crates/npa-api/src/advanced_ai.rs::tests",
            "crates/npa-tactic/src/lib.rs::tests",
            "crates/npa-frontend/src/human_parser.rs::tests",
            "tools/proof-corpus/src/main.rs",
        ] {
            assert_matrix_list_item(matrix, module);
        }

        let expectations = [
            SolverFixtureMatrixExpectation {
                id: "finite_decide.source_free_bool_universal",
                family: SolverFamily::FiniteDecide.as_str(),
                positive_test:
                    "finite_decide_source_free_checked_proof_response_binds_identity_and_policy",
                negative_test:
                    "finite_decide_source_free_rejects_false_folds_duplicates_and_budget_exhaustion",
                modules: &["crates/npa-api/src/solver.rs::tests"],
                ws08: &["WS08-T01"],
                negative_acceptance: &[
                    "false_fold",
                    "duplicate_enumeration",
                    "resource_exhaustion",
                    "stale_policy_hash",
                ],
                metrics: &[
                    "proof_bytes",
                    "generated_term_nodes",
                    "proof_steps",
                    "resource_policy_outcomes",
                ],
            },
            SolverFixtureMatrixExpectation {
                id: "omega.presburger_trace",
                family: SolverFamily::Omega.as_str(),
                positive_test:
                    "omega_reconstruction_accepts_rule_trace_and_replay_metadata_without_trusting_search",
                negative_test:
                    "omega_reconstruction_rejects_malformed_wrong_coefficients_missing_side_conditions_and_unsupported_fragments",
                modules: &["crates/npa-api/src/solver.rs::tests"],
                ws08: &["WS08-T02"],
                negative_acceptance: &[
                    "malformed_certificate",
                    "unsupported_fragment",
                    "hash_mismatch",
                    "stale_policy_hash",
                ],
                metrics: &[
                    "certificate_bytes",
                    "reconstruction_steps",
                    "generated_term_nodes",
                    "resource_policy_outcomes",
                ],
            },
            SolverFixtureMatrixExpectation {
                id: "ring_nf.checked_polynomial_equality",
                family: SolverFamily::Ring.as_str(),
                positive_test:
                    "ring_nf_reconstruction_checked_proof_response_binds_hashes_laws_policy_and_size",
                negative_test:
                    "ring_nf_reconstruction_rejects_mismatched_normal_forms_stale_maps_wrong_profile_missing_law_and_budget",
                modules: &["crates/npa-api/src/solver.rs::tests"],
                ws08: &["WS08-T03"],
                negative_acceptance: &[
                    "hash_mismatch",
                    "unsupported_fragment",
                    "resource_exhaustion",
                    "stale_policy_hash",
                ],
                metrics: &[
                    "proof_bytes",
                    "generated_term_nodes",
                    "reconstruction_steps",
                    "resource_policy_outcomes",
                ],
            },
            SolverFixtureMatrixExpectation {
                id: "bitblast.lrat_soundness_bridge",
                family: SolverFamily::Bitblast.as_str(),
                positive_test: "bitblast_lrat_end_to_end_accepts_checked_lrat_and_binds_bridge_metadata",
                negative_test:
                    "bitblast_lrat_end_to_end_rejects_malformed_lrat_wrong_cnf_and_raw_unsat",
                modules: &["crates/npa-api/src/solver.rs::tests"],
                ws08: &["WS08-T04"],
                negative_acceptance: &[
                    "malformed_lrat",
                    "hash_mismatch",
                    "opaque_solver_output",
                    "resource_exhaustion",
                ],
                metrics: &[
                    "cnf_size",
                    "lrat_size",
                    "certificate_bytes",
                    "generated_term_nodes",
                    "resource_policy_outcomes",
                ],
            },
            SolverFixtureMatrixExpectation {
                id: "lrat.minimal_unsat_bridge",
                family: SolverFamily::Lrat.as_str(),
                positive_test: "lrat_soundness_bridge_derives_cnf_unsat_theorem_from_checked_lrat",
                negative_test: "lrat_malformed_rejects_raw_unsat_payload_cnf_hash_mismatch_and_bad_ordinal",
                modules: &["crates/npa-api/src/solver.rs::tests"],
                ws08: &["WS08-T05"],
                negative_acceptance: &[
                    "malformed_lrat",
                    "opaque_solver_output",
                    "hash_mismatch",
                    "resource_exhaustion",
                ],
                metrics: &[
                    "certificate_bytes",
                    "cnf_size",
                    "lrat_size",
                    "reconstruction_steps",
                    "resource_policy_outcomes",
                ],
            },
            SolverFixtureMatrixExpectation {
                id: "smt.registry_reconstruction",
                family: SolverFamily::Smt.as_str(),
                positive_test: "smt_certificate_metadata_solver_contract_reuses_advanced_smt_fields",
                negative_test:
                    "smt_solver_handoff_rejects_resource_exhaustion_version_mismatch_and_unsupported_fragment",
                modules: &[
                    "crates/npa-api/src/solver.rs::tests",
                    "crates/npa-api/src/advanced_ai.rs::tests",
                ],
                ws08: &["WS08-T06", "WS08-T07"],
                negative_acceptance: &[
                    "unsupported_smt_fragment",
                    "opaque_solver_output",
                    "resource_exhaustion",
                    "hash_mismatch",
                ],
                metrics: &[
                    "certificate_bytes",
                    "proof_bytes",
                    "reconstruction_steps",
                    "resource_policy_outcomes",
                ],
            },
            SolverFixtureMatrixExpectation {
                id: "resource_policy.default_profiles",
                family: "resource_policy",
                positive_test: "solver_resource_policy_defaults_are_named_and_deterministic",
                negative_test:
                    "solver_resource_policy_timeout_memory_and_output_do_not_validate_accepting_response",
                modules: &["crates/npa-api/src/solver.rs::tests"],
                ws08: &["WS08-T08"],
                negative_acceptance: &[
                    "resource_exhaustion",
                    "stale_policy_hash",
                    "timeout",
                    "memory_limit",
                    "output_limit",
                ],
                metrics: &[
                    "input_nodes",
                    "proof_bytes",
                    "certificate_bytes",
                    "generated_term_nodes",
                    "resource_policy_outcomes",
                ],
            },
        ];

        let mut families = BTreeSet::new();
        let mut ws_tasks = BTreeSet::new();
        for expectation in expectations {
            let row = fixture_matrix_row(matrix, expectation.id);
            assert_matrix_string(row, "id", expectation.id);
            assert_matrix_string(row, "family", expectation.family);
            assert_matrix_string(row, "positive_test", expectation.positive_test);
            assert_matrix_string(row, "negative_test", expectation.negative_test);
            families.insert(expectation.family);
            for module in expectation.modules {
                assert_matrix_list_item(row, module);
            }
            for ws08 in expectation.ws08 {
                assert_matrix_list_item(row, ws08);
                ws_tasks.insert(*ws08);
            }
            for negative in expectation.negative_acceptance {
                assert_matrix_list_item(row, negative);
            }
            for metric in expectation.metrics {
                assert_matrix_list_item(row, metric);
            }
        }
        assert_eq!(families.len(), 7);
        for ws08 in [
            "WS08-T01", "WS08-T02", "WS08-T03", "WS08-T04", "WS08-T05", "WS08-T06", "WS08-T07",
            "WS08-T08",
        ] {
            assert!(ws_tasks.contains(ws08), "missing {ws08} fixture row");
        }
        for criterion in [
            "successful_solver_paths_end_in_checked_proof_or_checked_certificate",
            "raw_solver_output_is_untrusted",
            "deterministic_hashes_have_version_tags",
            "resource_policies_cover_size_time_memory_output_and_nested_limits",
            "unsupported_fragments_fail_closed",
            "positive_and_negative_solver_fixtures_exist",
            "optional_solver_support_stays_off_kernel_checker_and_normal_verify_hot_paths",
        ] {
            assert_matrix_list_item(matrix, criterion);
        }

        let finite_contract = finite_decide_contract(bool_enumeration());
        let finite_policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::FiniteDecideDefaultV1);
        let finite_artifact = finite_decide_proof_artifact(
            &finite_contract,
            FiniteDecideGoalKind::Universal,
            true,
            finite_decide_true_decisions(&finite_contract),
        );
        let finite_response = finite_decide_checked_proof_response(
            &finite_contract,
            &finite_artifact,
            &finite_policy,
        )
        .unwrap();
        assert_solver_response_advisory_is_sidecar(
            "finite_decide",
            &finite_contract.request,
            &finite_response,
            &finite_policy,
        );
        assert_solver_metrics(
            "finite_decide",
            finite_decide_resource_usage_from_proof_artifact(&finite_artifact).unwrap(),
            &["proof_bytes", "generated_term_nodes", "proof_steps"],
        );

        let (omega_policy, omega_request, omega_problem) = omega_reconstruction_fixture();
        let omega_artifact = omega_valid_certificate(&omega_request, &omega_problem);
        let omega_response = omega_checked_certificate_response(
            &omega_request,
            &omega_problem,
            &omega_artifact,
            &omega_policy,
        )
        .unwrap();
        assert_solver_response_advisory_is_sidecar(
            "omega",
            &omega_request,
            &omega_response,
            &omega_policy,
        );
        assert_solver_metrics(
            "omega",
            omega_resource_usage_from_certificate(&omega_problem, &omega_artifact).unwrap(),
            &[
                "certificate_bytes",
                "reconstruction_steps",
                "generated_term_nodes",
            ],
        );

        let ring_policy = ring_nf_policy();
        let ring_request = ring_nf_request_for_policy(&ring_policy);
        let ring_context = ring_nf_context(&[("x", "Int"), ("y", "Int")]);
        let ring_problem = ring_nf_reconstruction_problem(
            &ring_policy,
            &ring_request,
            RingNfAlgebraProfile::CommutativeRingV1,
            &ring_context,
            &ring_nf_eq(
                "Int",
                ring_nf_app2("Int.mul", Expr::bvar(1), Expr::bvar(0)),
                ring_nf_app2("Int.mul", Expr::bvar(0), Expr::bvar(1)),
            ),
        );
        let ring_artifact = ring_nf_proof_artifact(&ring_request, &ring_problem);
        let ring_response = ring_nf_checked_proof_response(
            &ring_request,
            &ring_problem,
            &ring_artifact,
            &ring_policy,
        )
        .unwrap();
        assert_solver_response_advisory_is_sidecar(
            "ring_nf",
            &ring_request,
            &ring_response,
            &ring_policy,
        );
        assert_solver_metrics(
            "ring_nf",
            ring_nf_resource_usage_from_proof_artifact(&ring_problem, &ring_artifact).unwrap(),
            &[
                "proof_bytes",
                "generated_term_nodes",
                "reconstruction_steps",
            ],
        );

        let (
            bitblast_policy,
            bitblast_request,
            lrat_policy,
            lrat_request,
            bitblast_problem,
            bitblast_semantic_proof,
            lrat_cnf,
            lrat_certificate,
        ) = bitblast_lrat_bridge_fixture();
        let bitblast_response = bitblast_lrat_checked_certificate_response_from_artifacts(
            BitblastLratSoundnessBridgeInput {
                request: &bitblast_request,
                policy: &bitblast_policy,
                lrat_request: &lrat_request,
                lrat_policy: &lrat_policy,
                problem: &bitblast_problem,
                semantic_proof: &bitblast_semantic_proof,
                lrat_cnf: &lrat_cnf,
                lrat_certificate: &lrat_certificate,
            },
        )
        .unwrap();
        assert_solver_response_advisory_is_sidecar(
            "bitblast",
            &bitblast_request,
            &bitblast_response,
            &bitblast_policy,
        );
        let lrat_payload = lrat_proof_payload_ref(&lrat_certificate).unwrap();
        assert_solver_metrics(
            "bitblast",
            bitblast_resource_usage_from_checked_certificate(
                &bitblast_problem,
                &bitblast_semantic_proof,
                &lrat_payload,
            )
            .unwrap(),
            &[
                "cnf_size",
                "lrat_size",
                "certificate_bytes",
                "generated_term_nodes",
            ],
        );

        let lrat_check =
            lrat_check_certificate(&lrat_request, &lrat_policy, &lrat_cnf, &lrat_certificate)
                .unwrap();
        let lrat_bridge = lrat_cnf_unsat_bridge_artifact(
            &lrat_request,
            &lrat_policy,
            &lrat_cnf,
            &lrat_certificate,
        )
        .unwrap();
        assert_eq!(
            lrat_check_artifact_hash(&lrat_check).unwrap(),
            lrat_bridge.lrat_check_artifact_hash
        );
        validate_lrat_cnf_unsat_bridge_artifact(
            &lrat_request,
            &lrat_policy,
            &lrat_cnf,
            &lrat_certificate,
            &lrat_bridge,
        )
        .unwrap();
        let lrat_bridge_hash = lrat_cnf_unsat_bridge_hash(&lrat_bridge).unwrap();
        let replayed_lrat_bridge = lrat_cnf_unsat_bridge_artifact(
            &lrat_request,
            &lrat_policy,
            &lrat_cnf,
            &lrat_certificate,
        )
        .unwrap();
        assert_eq!(
            lrat_bridge_hash,
            lrat_cnf_unsat_bridge_hash(&replayed_lrat_bridge).unwrap()
        );
        assert_solver_metrics(
            "lrat",
            lrat_resource_usage_from_certificate(&lrat_cnf, &lrat_certificate).unwrap(),
            &[
                "certificate_bytes",
                "cnf_size",
                "lrat_size",
                "reconstruction_steps",
            ],
        );

        let smt_policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::SmtReconstructionDefaultV1);
        let smt_request = request_for_resource_policy(&smt_policy);
        let smt_response = certificate_response_for_request(&smt_request);
        assert_solver_response_advisory_is_sidecar("smt", &smt_request, &smt_response, &smt_policy);
        let (smt_candidate, smt_problem) = advanced_smt_candidate_fixture();
        assert_solver_metrics(
            "smt",
            solver_resource_usage_from_advanced_smt_candidate(&smt_candidate, Some(&smt_problem))
                .unwrap(),
            &["certificate_bytes", "proof_bytes"],
        );

        let mut resource_policy =
            solver_default_resource_policy(SolverResourcePolicyProfile::SmtReconstructionDefaultV1);
        resource_policy.max_memory_bytes = 10;
        resource_policy.max_wall_clock_millis = 20;
        resource_policy.max_output_bytes = 30;
        let resource_request = request_for_resource_policy(&resource_policy);
        let resource_response = certificate_response_for_request(&resource_request);
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &resource_policy,
                &resource_request,
                &resource_response,
                SolverResourceUsage {
                    memory_bytes: 11,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::MemoryLimit {
                limit_bytes: 10,
                actual_bytes: 11,
            })
        );
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &resource_policy,
                &resource_request,
                &resource_response,
                SolverResourceUsage {
                    wall_clock_millis: 21,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::Timeout {
                field: SolverResourceField::WallClockMillis,
                limit_millis: 20,
                actual_millis: 21,
            })
        );
        assert_eq!(
            enforce_solver_generated_artifact_resource_policy(
                &resource_policy,
                &resource_request,
                &resource_response,
                SolverResourceUsage {
                    output_bytes: 31,
                    ..SolverResourceUsage::default()
                },
            ),
            Err(SolverContractError::OutputLimit {
                limit_bytes: 30,
                actual_bytes: 31,
            })
        );
    }

    #[test]
    fn smt_certificate_metadata_solver_contract_reuses_advanced_smt_fields() {
        let smt_metadata = AdvancedSmtCertificateMetadata {
            format: AdvancedSmtCertificateFormat::MvpProofNodeTableV1,
            solver: AdvancedSmtSolver::Cvc5,
            logic: AdvancedSmtLogic::MvpQfUf,
            encoded_goal_hash: hash(1),
            smt_problem_hash: hash(2),
            proof_hash: hash(3),
            reconstruction: AdvancedSmtReconstructionMetadata {
                rule_registry_profile: AdvancedSmtRuleRegistryProfile::MvpProofNodeTableQfV1,
                reconstruction_plan_hash: hash(4),
                imported_theory_count: 0,
                step_count: 1,
            },
        };
        let solver_metadata =
            SolverCertificateMetadata::from_advanced_smt_metadata(&smt_metadata, hash(5), hash(6))
                .unwrap();

        assert_eq!(solver_metadata.family, SolverFamily::Smt);
        assert_eq!(solver_metadata.fragment, SolverFragment::SmtQfUfV1);
        assert_eq!(
            solver_metadata.certificate_format,
            SolverCertificateFormat::MvpSmtProofNodeTableV1
        );
        assert_eq!(solver_metadata.payload_hash, smt_metadata.proof_hash);
        assert_eq!(
            solver_metadata.reconstruction_plan_hash,
            smt_metadata.reconstruction.reconstruction_plan_hash
        );
        assert_eq!(
            advanced_ai_smt_certificate_metadata_hash(&smt_metadata),
            advanced_ai_smt_certificate_metadata_hash(&smt_metadata)
        );
        assert_eq!(
            solver_certificate_metadata_hash(&solver_metadata),
            solver_certificate_metadata_hash(&solver_metadata)
        );
    }
}
