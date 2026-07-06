use std::collections::BTreeSet;

/// Machine-readable derive artifact names for inductive declarations.
///
/// The first four artifacts are the mandatory inductive baseline. The remaining
/// artifacts are heavy derived declarations and must enter only through an
/// explicit derive request or a reviewed foundational allowlist.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HumanDeriveArtifact {
    PrimitiveRecursor,
    DeterministicIotaRules,
    PositivityEvidence,
    MinimalMetadata,
    ConstructorInjectivity,
    ConstructorDisjointness,
    NoConfusion,
    CasesOn,
    RecOn,
    InductionOn,
    DecidableEq,
    ExplicitFinite,
    Codec,
    Size,
    Map,
    Fold,
    Traversal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanDeriveArtifactSource {
    Mandatory,
    FoundationalAllowlist,
    ExplicitRequest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanDeriveProofIdentityEffect {
    ExistingMandatoryCertificateArtifact,
    ExistingMandatoryMetadata,
    OrdinaryDerivedDeclaration,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HumanDeriveBudgetUsage {
    pub generated_declarations: u64,
    pub generated_core_nodes: u64,
    pub certificate_bytes: u64,
    pub source_free_verification_micros: u64,
}

impl HumanDeriveBudgetUsage {
    pub const fn zero() -> Self {
        Self {
            generated_declarations: 0,
            generated_core_nodes: 0,
            certificate_bytes: 0,
            source_free_verification_micros: 0,
        }
    }

    fn plus(self, other: Self) -> Self {
        Self {
            generated_declarations: self
                .generated_declarations
                .saturating_add(other.generated_declarations),
            generated_core_nodes: self
                .generated_core_nodes
                .saturating_add(other.generated_core_nodes),
            certificate_bytes: self
                .certificate_bytes
                .saturating_add(other.certificate_bytes),
            source_free_verification_micros: self
                .source_free_verification_micros
                .saturating_add(other.source_free_verification_micros),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HumanDeriveBudget {
    pub max_generated_declarations: u64,
    pub max_generated_core_nodes: u64,
    pub max_certificate_bytes: u64,
    pub max_source_free_verification_micros: u64,
}

impl HumanDeriveBudget {
    pub const fn new(
        max_generated_declarations: u64,
        max_generated_core_nodes: u64,
        max_certificate_bytes: u64,
        max_source_free_verification_micros: u64,
    ) -> Self {
        Self {
            max_generated_declarations,
            max_generated_core_nodes,
            max_certificate_bytes,
            max_source_free_verification_micros,
        }
    }

    pub const fn permissive() -> Self {
        Self::new(u64::MAX, u64::MAX, u64::MAX, u64::MAX)
    }

    fn exceeded_fields(self, usage: HumanDeriveBudgetUsage) -> Vec<HumanDeriveBudgetField> {
        let mut exceeded = Vec::new();
        if usage.generated_declarations > self.max_generated_declarations {
            exceeded.push(HumanDeriveBudgetField::GeneratedDeclarations);
        }
        if usage.generated_core_nodes > self.max_generated_core_nodes {
            exceeded.push(HumanDeriveBudgetField::GeneratedCoreNodes);
        }
        if usage.certificate_bytes > self.max_certificate_bytes {
            exceeded.push(HumanDeriveBudgetField::CertificateBytes);
        }
        if usage.source_free_verification_micros > self.max_source_free_verification_micros {
            exceeded.push(HumanDeriveBudgetField::SourceFreeVerificationMicros);
        }
        exceeded
    }
}

impl Default for HumanDeriveBudget {
    fn default() -> Self {
        Self::new(64, 65_536, 1_048_576, 1_000_000)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanDeriveBudgetField {
    GeneratedDeclarations,
    GeneratedCoreNodes,
    CertificateBytes,
    SourceFreeVerificationMicros,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDeriveBudgetError {
    pub budget: HumanDeriveBudget,
    pub requested_usage: HumanDeriveBudgetUsage,
    pub exceeded: Vec<HumanDeriveBudgetField>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDerivePlanError {
    BudgetExceeded(HumanDeriveBudgetError),
    MandatoryArtifactRequestedExplicitly(HumanDeriveArtifact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanPlannedDerivedArtifact {
    pub artifact: HumanDeriveArtifact,
    pub source: HumanDeriveArtifactSource,
    pub budget_usage: HumanDeriveBudgetUsage,
    pub proof_identity_effect: HumanDeriveProofIdentityEffect,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDerivePlan {
    pub type_name: npa_cert::Name,
    pub artifacts: Vec<HumanPlannedDerivedArtifact>,
    pub total_budget_usage: HumanDeriveBudgetUsage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanDerivedDeclarationKind {
    Definition,
    Theorem,
    Instance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDerivedDeclarationSpec {
    pub artifact: HumanDeriveArtifact,
    pub source: HumanDeriveArtifactSource,
    pub name: npa_cert::Name,
    pub kind: HumanDerivedDeclarationKind,
    pub declaration_index: u64,
    pub artifact_declaration_count: u64,
    pub budget_usage: HumanDeriveBudgetUsage,
    pub proof_identity_effect: HumanDeriveProofIdentityEffect,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanDerivedDeclarationPlan {
    pub type_name: npa_cert::Name,
    pub declarations: Vec<HumanDerivedDeclarationSpec>,
    pub total_budget_usage: HumanDeriveBudgetUsage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanUnsupportedDeriveArtifactName {
    pub requested: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanDerivedDeclarationPlanError {
    DerivePlan(HumanDerivePlanError),
    UnsupportedArtifactName(HumanUnsupportedDeriveArtifactName),
}

pub const HUMAN_MANDATORY_INDUCTIVE_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::PrimitiveRecursor,
    HumanDeriveArtifact::DeterministicIotaRules,
    HumanDeriveArtifact::PositivityEvidence,
    HumanDeriveArtifact::MinimalMetadata,
];

pub const HUMAN_HEAVY_DERIVE_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::InductionOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Codec,
    HumanDeriveArtifact::Size,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::Fold,
    HumanDeriveArtifact::Traversal,
];

const BOOL_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
];

const UNIT_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
];

const EMPTY_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
];

const OPTION_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::Fold,
    HumanDeriveArtifact::Traversal,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Codec,
];

const PROD_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Codec,
];

const SUM_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Codec,
];

const SIGMA_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
];

const SUBTYPE_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
];

const NAT_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::InductionOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::Size,
];

const LIST_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::InductionOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::Size,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::Fold,
    HumanDeriveArtifact::Traversal,
];

const FIN_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::InductionOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Size,
];

const VECTOR_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::InductionOn,
    HumanDeriveArtifact::Size,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::Fold,
    HumanDeriveArtifact::Traversal,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Codec,
];

const BITSTRING_FOUNDATIONAL_ARTIFACTS: &[HumanDeriveArtifact] = &[
    HumanDeriveArtifact::ConstructorInjectivity,
    HumanDeriveArtifact::ConstructorDisjointness,
    HumanDeriveArtifact::NoConfusion,
    HumanDeriveArtifact::CasesOn,
    HumanDeriveArtifact::RecOn,
    HumanDeriveArtifact::DecidableEq,
    HumanDeriveArtifact::ExplicitFinite,
    HumanDeriveArtifact::Codec,
    HumanDeriveArtifact::Size,
    HumanDeriveArtifact::Map,
    HumanDeriveArtifact::Fold,
    HumanDeriveArtifact::Traversal,
];

pub fn human_default_inductive_derivation_plan(
    type_name: npa_cert::Name,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivePlan, HumanDeriveBudgetError> {
    human_derive_plan(
        type_name,
        HUMAN_MANDATORY_INDUCTIVE_ARTIFACTS.iter().copied(),
        HumanDeriveArtifactSource::Mandatory,
        budget,
    )
}

pub fn human_foundational_derivation_plan(
    type_name: npa_cert::Name,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivePlan, HumanDeriveBudgetError> {
    let artifacts = human_foundational_allowlist_artifacts(&type_name);
    human_derive_plan(
        type_name,
        artifacts.iter().copied(),
        HumanDeriveArtifactSource::FoundationalAllowlist,
        budget,
    )
}

pub fn human_explicit_derivation_plan(
    type_name: npa_cert::Name,
    artifacts: impl IntoIterator<Item = HumanDeriveArtifact>,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivePlan, HumanDerivePlanError> {
    let artifacts = artifacts.into_iter().collect::<BTreeSet<_>>();
    if let Some(artifact) = artifacts
        .iter()
        .find(|artifact| !human_is_heavy_derive_artifact(**artifact))
    {
        return Err(HumanDerivePlanError::MandatoryArtifactRequestedExplicitly(
            *artifact,
        ));
    }
    human_derive_plan(
        type_name,
        artifacts,
        HumanDeriveArtifactSource::ExplicitRequest,
        budget,
    )
    .map_err(HumanDerivePlanError::BudgetExceeded)
}

pub fn human_default_derived_declaration_plan(
    type_name: npa_cert::Name,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivedDeclarationPlan, HumanDeriveBudgetError> {
    let plan = human_default_inductive_derivation_plan(type_name, budget)?;
    Ok(human_derived_declaration_plan_from_derivation_plan(&plan))
}

pub fn human_foundational_derived_declaration_plan(
    type_name: npa_cert::Name,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivedDeclarationPlan, HumanDeriveBudgetError> {
    let plan = human_foundational_derivation_plan(type_name, budget)?;
    Ok(human_derived_declaration_plan_from_derivation_plan(&plan))
}

pub fn human_explicit_derived_declaration_plan(
    type_name: npa_cert::Name,
    artifacts: impl IntoIterator<Item = HumanDeriveArtifact>,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivedDeclarationPlan, HumanDerivePlanError> {
    let plan = human_explicit_derivation_plan(type_name, artifacts, budget)?;
    Ok(human_derived_declaration_plan_from_derivation_plan(&plan))
}

pub fn human_explicit_derived_declaration_plan_from_names(
    type_name: npa_cert::Name,
    artifact_names: impl IntoIterator<Item = impl AsRef<str>>,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivedDeclarationPlan, HumanDerivedDeclarationPlanError> {
    let artifacts = artifact_names
        .into_iter()
        .map(|name| human_parse_derive_artifact(name.as_ref()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(HumanDerivedDeclarationPlanError::UnsupportedArtifactName)?;
    human_explicit_derived_declaration_plan(type_name, artifacts, budget)
        .map_err(HumanDerivedDeclarationPlanError::DerivePlan)
}

pub fn human_parse_derive_artifact(
    name: &str,
) -> Result<HumanDeriveArtifact, HumanUnsupportedDeriveArtifactName> {
    match name {
        "constructorInjectivity" | "ConstructorInjectivity" => {
            Ok(HumanDeriveArtifact::ConstructorInjectivity)
        }
        "constructorDisjointness" | "ConstructorDisjointness" => {
            Ok(HumanDeriveArtifact::ConstructorDisjointness)
        }
        "noConfusion" | "NoConfusion" => Ok(HumanDeriveArtifact::NoConfusion),
        "casesOn" | "CasesOn" => Ok(HumanDeriveArtifact::CasesOn),
        "recOn" | "RecOn" => Ok(HumanDeriveArtifact::RecOn),
        "inductionOn" | "InductionOn" => Ok(HumanDeriveArtifact::InductionOn),
        "decidableEq" | "DecidableEq" => Ok(HumanDeriveArtifact::DecidableEq),
        "explicitFinite" | "ExplicitFinite" => Ok(HumanDeriveArtifact::ExplicitFinite),
        "codec" | "Codec" => Ok(HumanDeriveArtifact::Codec),
        "size" | "Size" => Ok(HumanDeriveArtifact::Size),
        "map" | "Map" => Ok(HumanDeriveArtifact::Map),
        "fold" | "Fold" => Ok(HumanDeriveArtifact::Fold),
        "traversal" | "Traversal" => Ok(HumanDeriveArtifact::Traversal),
        _ => Err(HumanUnsupportedDeriveArtifactName {
            requested: name.to_owned(),
        }),
    }
}

pub fn human_derived_declaration_plan_from_derivation_plan(
    plan: &HumanDerivePlan,
) -> HumanDerivedDeclarationPlan {
    let declarations = plan
        .artifacts
        .iter()
        .filter(|artifact| {
            artifact.proof_identity_effect
                == HumanDeriveProofIdentityEffect::OrdinaryDerivedDeclaration
        })
        .flat_map(|artifact| human_derived_declaration_specs(&plan.type_name, artifact))
        .collect();

    HumanDerivedDeclarationPlan {
        type_name: plan.type_name.clone(),
        declarations,
        total_budget_usage: plan.total_budget_usage,
    }
}

pub fn human_foundational_allowlist_artifacts(
    type_name: &npa_cert::Name,
) -> &'static [HumanDeriveArtifact] {
    match type_name.as_dotted().as_str() {
        "Bool" => BOOL_FOUNDATIONAL_ARTIFACTS,
        "Unit" => UNIT_FOUNDATIONAL_ARTIFACTS,
        "Empty" => EMPTY_FOUNDATIONAL_ARTIFACTS,
        "Option" => OPTION_FOUNDATIONAL_ARTIFACTS,
        "Prod" => PROD_FOUNDATIONAL_ARTIFACTS,
        "Sum" => SUM_FOUNDATIONAL_ARTIFACTS,
        "Sigma" => SIGMA_FOUNDATIONAL_ARTIFACTS,
        "Subtype" => SUBTYPE_FOUNDATIONAL_ARTIFACTS,
        "Nat" => NAT_FOUNDATIONAL_ARTIFACTS,
        "List" => LIST_FOUNDATIONAL_ARTIFACTS,
        "Fin" => FIN_FOUNDATIONAL_ARTIFACTS,
        "Vector" => VECTOR_FOUNDATIONAL_ARTIFACTS,
        "BitString" => BITSTRING_FOUNDATIONAL_ARTIFACTS,
        _ => &[],
    }
}

pub fn human_is_heavy_derive_artifact(artifact: HumanDeriveArtifact) -> bool {
    HUMAN_HEAVY_DERIVE_ARTIFACTS.contains(&artifact)
}

fn human_derive_plan(
    type_name: npa_cert::Name,
    artifacts: impl IntoIterator<Item = HumanDeriveArtifact>,
    source: HumanDeriveArtifactSource,
    budget: HumanDeriveBudget,
) -> Result<HumanDerivePlan, HumanDeriveBudgetError> {
    let mut total_budget_usage = HumanDeriveBudgetUsage::zero();
    let artifacts = artifacts
        .into_iter()
        .map(|artifact| {
            let budget_usage = human_derive_artifact_budget_usage(artifact);
            total_budget_usage = total_budget_usage.plus(budget_usage);
            HumanPlannedDerivedArtifact {
                artifact,
                source,
                budget_usage,
                proof_identity_effect: human_derive_artifact_proof_identity_effect(artifact),
            }
        })
        .collect::<Vec<_>>();

    let exceeded = budget.exceeded_fields(total_budget_usage);
    if !exceeded.is_empty() {
        return Err(HumanDeriveBudgetError {
            budget,
            requested_usage: total_budget_usage,
            exceeded,
        });
    }

    Ok(HumanDerivePlan {
        type_name,
        artifacts,
        total_budget_usage,
    })
}

fn human_derived_declaration_specs(
    type_name: &npa_cert::Name,
    artifact: &HumanPlannedDerivedArtifact,
) -> Vec<HumanDerivedDeclarationSpec> {
    let declaration_count = artifact.budget_usage.generated_declarations;
    human_derive_declaration_templates(artifact.artifact)
        .iter()
        .enumerate()
        .map(|(index, template)| HumanDerivedDeclarationSpec {
            artifact: artifact.artifact,
            source: artifact.source,
            name: human_derived_declaration_name(type_name, template.suffix),
            kind: template.kind,
            declaration_index: index as u64,
            artifact_declaration_count: declaration_count,
            budget_usage: artifact.budget_usage,
            proof_identity_effect: artifact.proof_identity_effect,
        })
        .collect()
}

#[derive(Clone, Copy)]
struct HumanDerivedDeclarationTemplate {
    suffix: &'static str,
    kind: HumanDerivedDeclarationKind,
}

fn human_derive_declaration_templates(
    artifact: HumanDeriveArtifact,
) -> &'static [HumanDerivedDeclarationTemplate] {
    use HumanDerivedDeclarationKind::{Definition, Instance, Theorem};

    match artifact {
        HumanDeriveArtifact::ConstructorInjectivity => &[HumanDerivedDeclarationTemplate {
            suffix: "constructorInjectivity",
            kind: Theorem,
        }],
        HumanDeriveArtifact::ConstructorDisjointness => &[HumanDerivedDeclarationTemplate {
            suffix: "constructorDisjointness",
            kind: Theorem,
        }],
        HumanDeriveArtifact::NoConfusion => &[HumanDerivedDeclarationTemplate {
            suffix: "noConfusion",
            kind: Theorem,
        }],
        HumanDeriveArtifact::CasesOn => &[HumanDerivedDeclarationTemplate {
            suffix: "casesOn",
            kind: Definition,
        }],
        HumanDeriveArtifact::RecOn => &[HumanDerivedDeclarationTemplate {
            suffix: "recOn",
            kind: Definition,
        }],
        HumanDeriveArtifact::InductionOn => &[HumanDerivedDeclarationTemplate {
            suffix: "inductionOn",
            kind: Definition,
        }],
        HumanDeriveArtifact::DecidableEq => &[HumanDerivedDeclarationTemplate {
            suffix: "decidableEq",
            kind: Instance,
        }],
        HumanDeriveArtifact::ExplicitFinite => &[
            HumanDerivedDeclarationTemplate {
                suffix: "explicitFinite.enum",
                kind: Definition,
            },
            HumanDerivedDeclarationTemplate {
                suffix: "explicitFinite.complete",
                kind: Theorem,
            },
        ],
        HumanDeriveArtifact::Codec => &[
            HumanDerivedDeclarationTemplate {
                suffix: "codec.encode",
                kind: Definition,
            },
            HumanDerivedDeclarationTemplate {
                suffix: "codec.decode",
                kind: Definition,
            },
            HumanDerivedDeclarationTemplate {
                suffix: "codec.correct",
                kind: Theorem,
            },
        ],
        HumanDeriveArtifact::Size => &[HumanDerivedDeclarationTemplate {
            suffix: "size",
            kind: Definition,
        }],
        HumanDeriveArtifact::Map => &[HumanDerivedDeclarationTemplate {
            suffix: "map",
            kind: Definition,
        }],
        HumanDeriveArtifact::Fold => &[HumanDerivedDeclarationTemplate {
            suffix: "fold",
            kind: Definition,
        }],
        HumanDeriveArtifact::Traversal => &[
            HumanDerivedDeclarationTemplate {
                suffix: "traverse",
                kind: Definition,
            },
            HumanDerivedDeclarationTemplate {
                suffix: "traverse.correct",
                kind: Theorem,
            },
        ],
        HumanDeriveArtifact::PrimitiveRecursor
        | HumanDeriveArtifact::DeterministicIotaRules
        | HumanDeriveArtifact::PositivityEvidence
        | HumanDeriveArtifact::MinimalMetadata => &[],
    }
}

fn human_derived_declaration_name(type_name: &npa_cert::Name, suffix: &str) -> npa_cert::Name {
    npa_cert::Name::from_dotted(format!("{}.{}", type_name.as_dotted(), suffix))
}

fn human_derive_artifact_proof_identity_effect(
    artifact: HumanDeriveArtifact,
) -> HumanDeriveProofIdentityEffect {
    match artifact {
        HumanDeriveArtifact::PrimitiveRecursor
        | HumanDeriveArtifact::DeterministicIotaRules
        | HumanDeriveArtifact::PositivityEvidence => {
            HumanDeriveProofIdentityEffect::ExistingMandatoryCertificateArtifact
        }
        HumanDeriveArtifact::MinimalMetadata => {
            HumanDeriveProofIdentityEffect::ExistingMandatoryMetadata
        }
        _ => HumanDeriveProofIdentityEffect::OrdinaryDerivedDeclaration,
    }
}

fn human_derive_artifact_budget_usage(artifact: HumanDeriveArtifact) -> HumanDeriveBudgetUsage {
    match artifact {
        HumanDeriveArtifact::PrimitiveRecursor => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 48,
            certificate_bytes: 1024,
            source_free_verification_micros: 500,
        },
        HumanDeriveArtifact::DeterministicIotaRules => HumanDeriveBudgetUsage {
            generated_declarations: 0,
            generated_core_nodes: 8,
            certificate_bytes: 128,
            source_free_verification_micros: 50,
        },
        HumanDeriveArtifact::PositivityEvidence => HumanDeriveBudgetUsage {
            generated_declarations: 0,
            generated_core_nodes: 16,
            certificate_bytes: 128,
            source_free_verification_micros: 50,
        },
        HumanDeriveArtifact::MinimalMetadata => HumanDeriveBudgetUsage {
            generated_declarations: 0,
            generated_core_nodes: 0,
            certificate_bytes: 64,
            source_free_verification_micros: 0,
        },
        HumanDeriveArtifact::ConstructorInjectivity => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 96,
            certificate_bytes: 1536,
            source_free_verification_micros: 700,
        },
        HumanDeriveArtifact::ConstructorDisjointness => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 80,
            certificate_bytes: 1280,
            source_free_verification_micros: 650,
        },
        HumanDeriveArtifact::NoConfusion => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 128,
            certificate_bytes: 2048,
            source_free_verification_micros: 900,
        },
        HumanDeriveArtifact::CasesOn => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 64,
            certificate_bytes: 1024,
            source_free_verification_micros: 500,
        },
        HumanDeriveArtifact::RecOn => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 64,
            certificate_bytes: 1024,
            source_free_verification_micros: 500,
        },
        HumanDeriveArtifact::InductionOn => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 96,
            certificate_bytes: 1536,
            source_free_verification_micros: 700,
        },
        HumanDeriveArtifact::DecidableEq => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 160,
            certificate_bytes: 2560,
            source_free_verification_micros: 1100,
        },
        HumanDeriveArtifact::ExplicitFinite => HumanDeriveBudgetUsage {
            generated_declarations: 2,
            generated_core_nodes: 192,
            certificate_bytes: 3072,
            source_free_verification_micros: 1300,
        },
        HumanDeriveArtifact::Codec => HumanDeriveBudgetUsage {
            generated_declarations: 3,
            generated_core_nodes: 256,
            certificate_bytes: 4096,
            source_free_verification_micros: 1700,
        },
        HumanDeriveArtifact::Size => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 80,
            certificate_bytes: 1280,
            source_free_verification_micros: 650,
        },
        HumanDeriveArtifact::Map => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 96,
            certificate_bytes: 1536,
            source_free_verification_micros: 700,
        },
        HumanDeriveArtifact::Fold => HumanDeriveBudgetUsage {
            generated_declarations: 1,
            generated_core_nodes: 96,
            certificate_bytes: 1536,
            source_free_verification_micros: 700,
        },
        HumanDeriveArtifact::Traversal => HumanDeriveBudgetUsage {
            generated_declarations: 2,
            generated_core_nodes: 192,
            certificate_bytes: 3072,
            source_free_verification_micros: 1300,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compile_human_source_to_certificate_output_with_source_interfaces,
        HumanGeneratedDeclarationKind,
    };

    #[test]
    fn default_general_inductive_generates_only_mandatory_artifacts() {
        let output = compile_human_source_to_certificate_output_with_source_interfaces(
            crate::FileId(0),
            npa_cert::Name::from_dotted("Test"),
            "\
inductive Gate : Type where
| mk : Gate",
            &[],
            &[],
            &crate::HumanCompileOptions::default(),
        )
        .expect("general inductive should compile");

        let generated_kinds = output
            .source_interface
            .generated_declarations
            .iter()
            .map(|generated| generated.kind)
            .collect::<Vec<_>>();
        assert_eq!(
            generated_kinds,
            vec![
                HumanGeneratedDeclarationKind::Constructor,
                HumanGeneratedDeclarationKind::Recursor,
            ]
        );

        let plan = human_default_inductive_derivation_plan(
            npa_cert::Name::from_dotted("Gate"),
            HumanDeriveBudget::default(),
        )
        .expect("mandatory artifacts should fit the default budget");
        let artifacts = plan
            .artifacts
            .iter()
            .map(|artifact| artifact.artifact)
            .collect::<Vec<_>>();
        assert_eq!(artifacts, HUMAN_MANDATORY_INDUCTIVE_ARTIFACTS);
        assert!(artifacts
            .iter()
            .all(|artifact| !human_is_heavy_derive_artifact(*artifact)));
    }

    #[test]
    fn foundational_allowlist_is_exact_and_separate_from_default() {
        let bool_plan = human_foundational_derivation_plan(
            npa_cert::Name::from_dotted("Bool"),
            HumanDeriveBudget::default(),
        )
        .expect("Bool allowlist artifacts should fit the default budget");
        let bool_artifacts = bool_plan
            .artifacts
            .iter()
            .map(|artifact| artifact.artifact)
            .collect::<Vec<_>>();
        assert_eq!(bool_artifacts, BOOL_FOUNDATIONAL_ARTIFACTS);
        assert!(bool_plan.artifacts.iter().all(|artifact| {
            artifact.source == HumanDeriveArtifactSource::FoundationalAllowlist
                && artifact.proof_identity_effect
                    == HumanDeriveProofIdentityEffect::OrdinaryDerivedDeclaration
        }));

        let user_bool_plan = human_foundational_derivation_plan(
            npa_cert::Name::from_dotted("User.Bool"),
            HumanDeriveBudget::default(),
        )
        .expect("non-foundational type should have an empty allowlist plan");
        assert!(user_bool_plan.artifacts.is_empty());

        let default_bool = human_default_inductive_derivation_plan(
            npa_cert::Name::from_dotted("Bool"),
            HumanDeriveBudget::default(),
        )
        .expect("default Bool plan should still be mandatory-only");
        assert_eq!(
            default_bool
                .artifacts
                .iter()
                .map(|artifact| artifact.artifact)
                .collect::<Vec<_>>(),
            HUMAN_MANDATORY_INDUCTIVE_ARTIFACTS
        );
    }

    #[test]
    fn explicit_derive_plan_contains_only_requested_artifacts() {
        let plan = human_explicit_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            [
                HumanDeriveArtifact::Codec,
                HumanDeriveArtifact::NoConfusion,
                HumanDeriveArtifact::Codec,
            ],
            HumanDeriveBudget::default(),
        )
        .expect("explicit artifacts should fit the default budget");

        let artifacts = plan
            .artifacts
            .iter()
            .map(|artifact| artifact.artifact)
            .collect::<Vec<_>>();
        assert_eq!(
            artifacts,
            vec![HumanDeriveArtifact::NoConfusion, HumanDeriveArtifact::Codec]
        );
        assert!(plan.artifacts.iter().all(|artifact| {
            artifact.source == HumanDeriveArtifactSource::ExplicitRequest
                && artifact.proof_identity_effect
                    == HumanDeriveProofIdentityEffect::OrdinaryDerivedDeclaration
        }));
    }

    #[test]
    fn decidable_eq_is_foundational_or_explicit_but_not_default() {
        let default_literal = human_default_inductive_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            HumanDeriveBudget::default(),
        )
        .expect("default inductive plan should fit the default budget");
        assert!(!default_literal
            .artifacts
            .iter()
            .any(|artifact| artifact.artifact == HumanDeriveArtifact::DecidableEq));

        let explicit_literal = human_explicit_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::DecidableEq],
            HumanDeriveBudget::default(),
        )
        .expect("explicit DecidableEq should fit the default budget");
        assert_eq!(explicit_literal.artifacts.len(), 1);
        assert_eq!(
            explicit_literal.artifacts[0].source,
            HumanDeriveArtifactSource::ExplicitRequest
        );
        assert_eq!(
            explicit_literal.artifacts[0].artifact,
            HumanDeriveArtifact::DecidableEq
        );

        for type_name in ["Bool", "Fin", "BitString"] {
            let plan = human_foundational_derivation_plan(
                npa_cert::Name::from_dotted(type_name),
                HumanDeriveBudget::default(),
            )
            .unwrap_or_else(|err| panic!("{type_name} allowlist should fit budget: {err:?}"));
            assert!(
                plan.artifacts.iter().any(|artifact| artifact.artifact
                    == HumanDeriveArtifact::DecidableEq
                    && artifact.source == HumanDeriveArtifactSource::FoundationalAllowlist),
                "{type_name} should allow DecidableEq only through the foundational allowlist"
            );
        }
    }

    #[test]
    fn explicit_finite_is_foundational_or_explicit_but_not_default_and_budgeted() {
        let default_literal = human_default_inductive_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            HumanDeriveBudget::default(),
        )
        .expect("default inductive plan should fit the default budget");
        assert!(!default_literal
            .artifacts
            .iter()
            .any(|artifact| artifact.artifact == HumanDeriveArtifact::ExplicitFinite));

        let explicit_literal = human_explicit_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::ExplicitFinite],
            HumanDeriveBudget::default(),
        )
        .expect("explicit ExplicitFinite should fit the default budget");
        assert_eq!(explicit_literal.artifacts.len(), 1);
        assert_eq!(
            explicit_literal.artifacts[0].source,
            HumanDeriveArtifactSource::ExplicitRequest
        );
        assert_eq!(
            explicit_literal.artifacts[0].budget_usage,
            HumanDeriveBudgetUsage {
                generated_declarations: 2,
                generated_core_nodes: 192,
                certificate_bytes: 3072,
                source_free_verification_micros: 1300,
            }
        );

        for type_name in [
            "Bool",
            "Unit",
            "Empty",
            "Option",
            "Prod",
            "Sum",
            "Fin",
            "Vector",
            "BitString",
        ] {
            let plan = human_foundational_derivation_plan(
                npa_cert::Name::from_dotted(type_name),
                HumanDeriveBudget::default(),
            )
            .unwrap_or_else(|err| panic!("{type_name} allowlist should fit budget: {err:?}"));
            assert!(
                plan.artifacts.iter().any(|artifact| artifact.artifact
                    == HumanDeriveArtifact::ExplicitFinite
                    && artifact.source == HumanDeriveArtifactSource::FoundationalAllowlist),
                "{type_name} should allow ExplicitFinite only through the foundational allowlist"
            );
        }

        let user_option_plan = human_foundational_derivation_plan(
            npa_cert::Name::from_dotted("User.Option"),
            HumanDeriveBudget::default(),
        )
        .expect("non-foundational type should have an empty allowlist plan");
        assert!(!user_option_plan
            .artifacts
            .iter()
            .any(|artifact| artifact.artifact == HumanDeriveArtifact::ExplicitFinite));
    }

    #[test]
    fn codec_is_foundational_or_explicit_but_not_default_and_budgeted() {
        let default_literal = human_default_inductive_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            HumanDeriveBudget::default(),
        )
        .expect("default inductive plan should fit the default budget");
        assert!(!default_literal
            .artifacts
            .iter()
            .any(|artifact| artifact.artifact == HumanDeriveArtifact::Codec));

        let explicit_literal = human_explicit_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::Codec],
            HumanDeriveBudget::default(),
        )
        .expect("explicit Codec should fit the default budget");
        assert_eq!(explicit_literal.artifacts.len(), 1);
        assert_eq!(
            explicit_literal.artifacts[0].source,
            HumanDeriveArtifactSource::ExplicitRequest
        );
        assert_eq!(
            explicit_literal.artifacts[0].budget_usage,
            HumanDeriveBudgetUsage {
                generated_declarations: 3,
                generated_core_nodes: 256,
                certificate_bytes: 4096,
                source_free_verification_micros: 1700,
            }
        );

        for type_name in ["Option", "Prod", "Sum", "Vector", "BitString"] {
            let plan = human_foundational_derivation_plan(
                npa_cert::Name::from_dotted(type_name),
                HumanDeriveBudget::default(),
            )
            .unwrap_or_else(|err| panic!("{type_name} allowlist should fit budget: {err:?}"));
            assert!(
                plan.artifacts
                    .iter()
                    .any(|artifact| artifact.artifact == HumanDeriveArtifact::Codec
                        && artifact.source == HumanDeriveArtifactSource::FoundationalAllowlist),
                "{type_name} should allow Codec only through the foundational allowlist"
            );
        }

        let user_option_plan = human_foundational_derivation_plan(
            npa_cert::Name::from_dotted("User.Option"),
            HumanDeriveBudget::default(),
        )
        .expect("non-foundational type should have an empty allowlist plan");
        assert!(!user_option_plan
            .artifacts
            .iter()
            .any(|artifact| artifact.artifact == HumanDeriveArtifact::Codec));
    }

    #[test]
    fn explicit_derive_rejects_mandatory_artifacts() {
        let err = human_explicit_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::PrimitiveRecursor],
            HumanDeriveBudget::default(),
        )
        .expect_err("explicit derives are only for heavy artifacts");

        assert_eq!(
            err,
            HumanDerivePlanError::MandatoryArtifactRequestedExplicitly(
                HumanDeriveArtifact::PrimitiveRecursor
            )
        );
    }

    #[test]
    fn explicit_derive_budget_failure_returns_no_plan() {
        let err = human_explicit_derivation_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::NoConfusion],
            HumanDeriveBudget::new(0, 0, 0, 0),
        )
        .expect_err("budget failure should be deterministic and pre-generation");
        let HumanDerivePlanError::BudgetExceeded(err) = err else {
            panic!("expected budget error");
        };

        assert_eq!(
            err.exceeded,
            vec![
                HumanDeriveBudgetField::GeneratedDeclarations,
                HumanDeriveBudgetField::GeneratedCoreNodes,
                HumanDeriveBudgetField::CertificateBytes,
                HumanDeriveBudgetField::SourceFreeVerificationMicros,
            ]
        );
        assert_eq!(err.requested_usage.generated_declarations, 1);
        assert_eq!(err.requested_usage.generated_core_nodes, 128);
        assert_eq!(err.requested_usage.certificate_bytes, 2048);
        assert_eq!(err.requested_usage.source_free_verification_micros, 900);
    }

    #[test]
    fn default_general_inductive_has_empty_heavy_declaration_snapshot() {
        let plan = human_default_derived_declaration_plan(
            npa_cert::Name::from_dotted("Gate"),
            HumanDeriveBudget::default(),
        )
        .expect("mandatory default artifacts should fit the default budget");

        assert!(plan.declarations.is_empty());
        assert!(plan.total_budget_usage.generated_declarations > 0);
    }

    #[test]
    fn pua_m02_derive_policy_rejects_eager_heavy_declarations_by_default() {
        let plan = human_default_derived_declaration_plan(
            npa_cert::Name::from_dotted("UserInductive"),
            HumanDeriveBudget::default(),
        )
        .expect("mandatory default artifacts should fit the default budget");

        assert!(plan.declarations.is_empty());

        let derivation_plan = human_default_inductive_derivation_plan(
            npa_cert::Name::from_dotted("UserInductive"),
            HumanDeriveBudget::default(),
        )
        .expect("mandatory default artifacts should fit the default budget");
        assert!(derivation_plan.artifacts.iter().all(|artifact| {
            artifact.source == HumanDeriveArtifactSource::Mandatory
                && !human_is_heavy_derive_artifact(artifact.artifact)
                && artifact.proof_identity_effect
                    != HumanDeriveProofIdentityEffect::OrdinaryDerivedDeclaration
        }));
    }

    #[test]
    fn foundational_allowlist_declaration_snapshot_is_stable() {
        let plan = human_foundational_derived_declaration_plan(
            npa_cert::Name::from_dotted("Bool"),
            HumanDeriveBudget::default(),
        )
        .expect("Bool foundational derived declarations should fit the default budget");

        let names = plan
            .declarations
            .iter()
            .map(|decl| decl.name.as_dotted())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            vec![
                "Bool.constructorDisjointness",
                "Bool.noConfusion",
                "Bool.casesOn",
                "Bool.decidableEq",
                "Bool.explicitFinite.enum",
                "Bool.explicitFinite.complete",
            ]
        );

        let kinds = plan
            .declarations
            .iter()
            .map(|decl| decl.kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            vec![
                HumanDerivedDeclarationKind::Theorem,
                HumanDerivedDeclarationKind::Theorem,
                HumanDerivedDeclarationKind::Definition,
                HumanDerivedDeclarationKind::Instance,
                HumanDerivedDeclarationKind::Definition,
                HumanDerivedDeclarationKind::Theorem,
            ]
        );
        assert!(plan.declarations.iter().all(|decl| {
            decl.source == HumanDeriveArtifactSource::FoundationalAllowlist
                && decl.proof_identity_effect
                    == HumanDeriveProofIdentityEffect::OrdinaryDerivedDeclaration
        }));
    }

    #[test]
    fn explicit_derive_declaration_snapshot_is_deduplicated_and_ordered() {
        let plan = human_explicit_derived_declaration_plan_from_names(
            npa_cert::Name::from_dotted("Literal"),
            ["Codec", "noConfusion", "Codec"],
            HumanDeriveBudget::default(),
        )
        .expect("explicit derived declaration plan should fit the default budget");

        let names = plan
            .declarations
            .iter()
            .map(|decl| decl.name.as_dotted())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            vec![
                "Literal.noConfusion",
                "Literal.codec.encode",
                "Literal.codec.decode",
                "Literal.codec.correct",
            ]
        );
    }

    #[test]
    fn explicit_declaration_plan_does_not_over_generate() {
        let plan = human_explicit_derived_declaration_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::NoConfusion],
            HumanDeriveBudget::default(),
        )
        .expect("explicit NoConfusion should fit the default budget");

        assert_eq!(plan.declarations.len(), 1);
        assert_eq!(
            plan.declarations[0].artifact,
            HumanDeriveArtifact::NoConfusion
        );
        assert_eq!(plan.declarations[0].name.as_dotted(), "Literal.noConfusion");
    }

    #[test]
    fn explicit_declaration_plan_budget_failure_returns_no_plan() {
        let err = human_explicit_derived_declaration_plan(
            npa_cert::Name::from_dotted("Literal"),
            [HumanDeriveArtifact::NoConfusion],
            HumanDeriveBudget::new(0, 0, 0, 0),
        )
        .expect_err("budget failure should happen before declaration specs are emitted");

        let HumanDerivePlanError::BudgetExceeded(err) = err else {
            panic!("expected budget error");
        };
        assert_eq!(err.requested_usage.generated_declarations, 1);
        assert_eq!(
            err.exceeded,
            vec![
                HumanDeriveBudgetField::GeneratedDeclarations,
                HumanDeriveBudgetField::GeneratedCoreNodes,
                HumanDeriveBudgetField::CertificateBytes,
                HumanDeriveBudgetField::SourceFreeVerificationMicros,
            ]
        );
    }

    #[test]
    fn unsupported_derive_request_name_is_structured_error() {
        let err = human_explicit_derived_declaration_plan_from_names(
            npa_cert::Name::from_dotted("Literal"),
            ["deriveAll"],
            HumanDeriveBudget::default(),
        )
        .expect_err("unsupported derive names should be rejected deterministically");

        assert_eq!(
            err,
            HumanDerivedDeclarationPlanError::UnsupportedArtifactName(
                HumanUnsupportedDeriveArtifactName {
                    requested: "deriveAll".to_owned()
                }
            )
        );
    }
}
