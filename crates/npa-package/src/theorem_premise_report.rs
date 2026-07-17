//! Canonical source-free package theorem-premise report.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        axiom_reference_json, axiom_reference_sort_key, checker_summary_json, duplicate_key_error,
        expect_object, field_path, file_reference_json, global_ref_json, global_ref_sort_key,
        hash_json, json_array, json_object_in_order, json_string, json_u64,
        normalize_checker_summaries, parse_artifact_json, parse_axiom_reference,
        parse_checker_summary, parse_file_reference, parse_global_ref, reject_unknown_fields,
        required_array, required_hash, required_name, required_string, required_u64,
        required_value, validate_artifact_file_reference, validate_artifact_path,
        validate_axiom_reference, validate_checker_summaries, validate_declaration_name,
        validate_global_ref, validate_package_identity, PackageArtifactFileReference,
        PackageArtifactOrigin, PackageAxiomReference, PackageCheckerMode, PackageCheckerSummary,
        PackageGlobalRef,
    },
    error::{PackageArtifactError, PackageArtifactErrorReason, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, PackageHash},
    json::{JsonMember, JsonValue},
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
    theorem_index::PackageTheoremIndexArtifact,
};

/// Canonical theorem-premise report schema.
pub const PACKAGE_THEOREM_PREMISE_REPORT_SCHEMA: &str = "npa.package.theorem_premise_report.v0.1";
/// Fixed package-relative theorem-premise report path.
pub const PACKAGE_THEOREM_PREMISE_REPORT_PATH: &str = "generated/theorem-premise-report.json";
/// Certificate-structural theorem-premise analysis profile.
pub const PACKAGE_THEOREM_PREMISE_REPORT_PROFILE: &str =
    "npa.package.theorem_premise_report.v0.1.certificate_structural";
/// Fixed package-level representation of the version 1 analysis limits.
pub const PACKAGE_THEOREM_PREMISE_ANALYSIS_LIMITS_V1: PackageTheoremPremiseAnalysisLimits =
    PackageTheoremPremiseAnalysisLimits {
        telescope_binders_per_theorem: 16_384,
        kernel_whnf_fuel_per_theorem: 1_000_000,
        kernel_conversion_fuel_per_theorem: 1_000_000,
        expression_traversal_states_per_theorem: 1_000_000,
        resolved_global_dependencies_per_theorem: 262_144,
    };

/// Generated package theorem-premise report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremPremiseReport {
    /// Exact report schema.
    pub schema: String,
    /// Package id copied from the manifest.
    pub package: PackageId,
    /// Package version copied from the manifest.
    pub version: PackageVersion,
    /// Exact package-manifest file identity.
    pub manifest: PackageArtifactFileReference,
    /// Exact checked package-lock file identity.
    pub package_lock: PackageArtifactFileReference,
    /// Fixed analysis profile.
    pub analysis_profile: String,
    /// Fixed profile limits included in report identity.
    pub limits: PackageTheoremPremiseAnalysisLimits,
    /// Public local theorem entries.
    pub entries: Vec<PackageTheoremPremiseEntry>,
    /// Fast-kernel checker summaries.
    pub checker_summaries: Vec<PackageCheckerSummary>,
    /// Deterministic report counts.
    pub summary: PackageTheoremPremiseSummary,
    /// Self hash over canonical bytes excluding this member.
    pub report_hash: PackageHash,
}

impl PackageTheoremPremiseReport {
    /// Normalize arrays and compute the report self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_report(&mut self);
        self.report_hash = compute_package_theorem_premise_report_hash(&self)?;
        Ok(self)
    }

    /// Serialize deterministic canonical report JSON.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_package_theorem_premise_report(self)?;
        let mut normalized = self.clone();
        normalize_report(&mut normalized);
        Ok(report_json_unchecked(&normalized, true))
    }
}

/// Fixed analysis resource limits serialized into report identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackageTheoremPremiseAnalysisLimits {
    /// Maximum telescope binders per theorem.
    pub telescope_binders_per_theorem: u64,
    /// Shared weak-head fuel per theorem.
    pub kernel_whnf_fuel_per_theorem: u64,
    /// Shared conversion fuel per theorem.
    pub kernel_conversion_fuel_per_theorem: u64,
    /// Shared expression traversal states per theorem.
    pub expression_traversal_states_per_theorem: u64,
    /// Maximum resolved direct dependencies per theorem.
    pub resolved_global_dependencies_per_theorem: u64,
}

/// Structural premise report entry for one public local theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremPremiseEntry {
    /// Full theorem identity.
    pub global_ref: PackageGlobalRef,
    /// Exported theorem statement hash.
    pub statement_hash: PackageHash,
    /// Containing module axiom-report hash.
    pub module_axiom_report_hash: PackageHash,
    /// Local certificate artifact locator.
    pub artifact: PackageTheoremIndexArtifact,
    /// Structural theorem telescope profile.
    pub telescope: PackageTheoremTelescopeProfile,
    /// Checked-proof premise-use profile.
    pub proof: PackageTheoremProofProfile,
    /// Direct global and transitive axiom dependencies.
    pub dependency_basis: PackageTheoremDependencyProfile,
    /// Derived classifications and review priority.
    pub classification: PackageTheoremPremiseClassification,
}

/// Structural profile of an exposed theorem telescope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremTelescopeProfile {
    /// Number of telescope binders.
    pub binder_count: u64,
    /// Source-order sort-parameter binder indices.
    pub sort_parameter_indices: Vec<u64>,
    /// Source-order data-parameter binder indices.
    pub data_parameter_indices: Vec<u64>,
    /// Proposition-valued fact premises.
    pub fact_premises: Vec<PackageTheoremFactPremise>,
    /// Structural hash of the exposed conclusion.
    pub conclusion_hash: PackageHash,
    /// Telescope binders referenced by the conclusion.
    pub conclusion_depends_on_binder_indices: Vec<u64>,
}

/// Structural and use information for one fact premise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremFactPremise {
    /// Source-order telescope binder index.
    pub binder_index: u64,
    /// Structural hash of the reconstructed binder domain.
    pub type_hash: PackageHash,
    /// Earlier telescope binders referenced by the domain.
    pub depends_on_prior_binder_indices: Vec<u64>,
    /// Distinct checked-proof occurrence kinds.
    pub use_sites: Vec<PackageTheoremPremiseUseSite>,
}

/// Stable checked-proof occurrence kind for a fact premise.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremPremiseUseSite {
    /// The proof result is exactly the premise.
    DirectResult,
    /// The premise is the final application head.
    ApplicationHead,
    /// The premise occurs in an application argument.
    ApplicationArgument,
    /// The premise occurs at another term-body position.
    TermBody,
    /// The premise occurs in a nested dependent type.
    DependentType,
    /// The premise occurs in a let-bound value.
    LetValue,
}

impl PackageTheoremPremiseUseSite {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DirectResult => "direct_result",
            Self::ApplicationHead => "application_head",
            Self::ApplicationArgument => "application_argument",
            Self::TermBody => "term_body",
            Self::DependentType => "dependent_type",
            Self::LetValue => "let_value",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "direct_result" => Ok(Self::DirectResult),
            "application_head" => Ok(Self::ApplicationHead),
            "application_argument" => Ok(Self::ApplicationArgument),
            "term_body" => Ok(Self::TermBody),
            "dependent_type" => Ok(Self::DependentType),
            "let_value" => Ok(Self::LetValue),
            _ => Err(invalid_enum(path, "use_sites", value)),
        }
    }
}

/// Aggregate checked-proof premise-use indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremProofProfile {
    /// Fact premises with at least one checked-proof occurrence.
    pub used_fact_premise_indices: Vec<u64>,
    /// Fact premises directly or callback-head forwarded.
    pub forwarded_fact_premise_indices: Vec<u64>,
}

/// Declaration-wide dependency basis for one theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremDependencyProfile {
    /// Direct resolved global dependencies.
    pub global_dependencies: Vec<PackageTheoremGlobalDependency>,
    /// Verifier-recomputed transitive axiom dependencies.
    pub axiom_dependencies: Vec<PackageAxiomReference>,
}

/// Tagged stable identity for a direct theorem dependency.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackageTheoremGlobalDependencyIdentity {
    /// Trusted builtin identity without invented package ownership.
    Builtin {
        /// Canonical builtin name.
        name: Name,
        /// Expected builtin declaration-interface hash.
        decl_interface_hash: PackageHash,
    },
    /// Full package-global declaration identity.
    PackageGlobal(PackageGlobalRef),
}

/// Direct global dependency and its resolved kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremGlobalDependency {
    /// Tagged stable dependency identity.
    pub identity: PackageTheoremGlobalDependencyIdentity,
    /// Resolved dependency kind.
    pub kind: PackageTheoremGlobalDependencyKind,
}

/// Stable kind of a direct theorem declaration dependency.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremGlobalDependencyKind {
    /// Trusted builtin primitive.
    BuiltinPrimitive,
    /// Trusted builtin axiom.
    BuiltinAxiom,
    /// Ordinary definition.
    Definition,
    /// Checked theorem.
    Theorem,
    /// Declared axiom.
    Axiom,
    /// Inductive-family declaration.
    Inductive,
    /// Generated constructor.
    Constructor,
    /// Generated recursor.
    Recursor,
}

impl PackageTheoremGlobalDependencyKind {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BuiltinPrimitive => "builtin_primitive",
            Self::BuiltinAxiom => "builtin_axiom",
            Self::Definition => "definition",
            Self::Theorem => "theorem",
            Self::Axiom => "axiom",
            Self::Inductive => "inductive",
            Self::Constructor => "constructor",
            Self::Recursor => "recursor",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "builtin_primitive" => Ok(Self::BuiltinPrimitive),
            "builtin_axiom" => Ok(Self::BuiltinAxiom),
            "definition" => Ok(Self::Definition),
            "theorem" => Ok(Self::Theorem),
            "axiom" => Ok(Self::Axiom),
            "inductive" => Ok(Self::Inductive),
            "constructor" => Ok(Self::Constructor),
            "recursor" => Ok(Self::Recursor),
            _ => Err(invalid_enum(path, "kind", value)),
        }
    }
}

/// Derived theorem-premise classification axes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageTheoremPremiseClassification {
    /// Statement-shape classification.
    pub statement_class: PackageTheoremStatementClass,
    /// Checked-proof premise-use classification.
    pub premise_use_class: PackageTheoremPremiseUseClass,
    /// Declaration-wide global dependency classification.
    pub global_basis_class: PackageTheoremGlobalBasisClass,
    /// Informational review queue priority.
    pub review_priority: PackageTheoremReviewPriority,
    /// All applicable stable structural reasons.
    pub reason_codes: Vec<PackageTheoremPremiseReason>,
}

/// Whether the theorem statement declares fact premises.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremStatementClass {
    /// No fact premise is declared.
    Closed,
    /// At least one fact premise is declared.
    FactParameterized,
}

impl PackageTheoremStatementClass {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Closed => "closed",
            Self::FactParameterized => "fact_parameterized",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "closed" => Ok(Self::Closed),
            "fact_parameterized" => Ok(Self::FactParameterized),
            _ => Err(invalid_enum(path, "statement_class", value)),
        }
    }
}

/// How the checked proof uses declared fact premises.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremPremiseUseClass {
    /// The theorem declares no fact premises.
    NoneDeclared,
    /// Fact premises are declared but unused.
    DeclaredUnused,
    /// At least one fact premise is used but none is forwarded.
    Used,
    /// At least one fact premise is syntactically forwarded.
    Forwarded,
}

impl PackageTheoremPremiseUseClass {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NoneDeclared => "none_declared",
            Self::DeclaredUnused => "declared_unused",
            Self::Used => "used",
            Self::Forwarded => "forwarded",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "none_declared" => Ok(Self::NoneDeclared),
            "declared_unused" => Ok(Self::DeclaredUnused),
            "used" => Ok(Self::Used),
            "forwarded" => Ok(Self::Forwarded),
            _ => Err(invalid_enum(path, "premise_use_class", value)),
        }
    }
}

/// Declaration-wide global dependency basis.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremGlobalBasisClass {
    /// Only definitions, primitives, and inductive artifacts are referenced.
    DefinitionsAndPrimitivesOnly,
    /// At least one checked theorem is directly referenced and no axiom is transitive.
    VerifiedTheoremDependent,
    /// The theorem has at least one transitive axiom dependency.
    AxiomDependent,
}

impl PackageTheoremGlobalBasisClass {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DefinitionsAndPrimitivesOnly => "definitions_and_primitives_only",
            Self::VerifiedTheoremDependent => "verified_theorem_dependent",
            Self::AxiomDependent => "axiom_dependent",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "definitions_and_primitives_only" => Ok(Self::DefinitionsAndPrimitivesOnly),
            "verified_theorem_dependent" => Ok(Self::VerifiedTheoremDependent),
            "axiom_dependent" => Ok(Self::AxiomDependent),
            _ => Err(invalid_enum(path, "global_basis_class", value)),
        }
    }
}

/// Informational review priority derived from structural classifications.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremReviewPriority {
    /// Forwarding or axiom dependency deserves first review.
    High,
    /// Ordinary fact-premise use deserves review.
    Review,
    /// Declared but unused fact premises are informational.
    Informational,
    /// No premise-specific review priority.
    None,
}

impl PackageTheoremReviewPriority {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::High => "high",
            Self::Review => "review",
            Self::Informational => "informational",
            Self::None => "none",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "high" => Ok(Self::High),
            "review" => Ok(Self::Review),
            "informational" => Ok(Self::Informational),
            "none" => Ok(Self::None),
            _ => Err(invalid_enum(path, "review_priority", value)),
        }
    }
}

/// Stable structural reason attached to a theorem-premise classification.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageTheoremPremiseReason {
    /// The statement has no fact premises.
    ClosedWithoutFactPremises,
    /// The statement declares a fact premise.
    FactPremiseDeclared,
    /// Declared fact premises are unused.
    FactPremiseUnused,
    /// At least one fact premise is used.
    FactPremiseUsed,
    /// A fact premise is the direct proof result.
    FactPremiseDirectlyForwarded,
    /// A fact premise is the final callback application head.
    FactPremiseCallbackForwarded,
    /// A checked theorem is a direct global dependency.
    GlobalBasisUsesVerifiedTheorem,
    /// A transitive axiom dependency is present.
    GlobalBasisUsesTransitiveAxiom,
}

impl PackageTheoremPremiseReason {
    /// Return the canonical JSON string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ClosedWithoutFactPremises => "closed_without_fact_premises",
            Self::FactPremiseDeclared => "fact_premise_declared",
            Self::FactPremiseUnused => "fact_premise_unused",
            Self::FactPremiseUsed => "fact_premise_used",
            Self::FactPremiseDirectlyForwarded => "fact_premise_directly_forwarded",
            Self::FactPremiseCallbackForwarded => "fact_premise_callback_forwarded",
            Self::GlobalBasisUsesVerifiedTheorem => "global_basis_uses_verified_theorem",
            Self::GlobalBasisUsesTransitiveAxiom => "global_basis_uses_transitive_axiom",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "closed_without_fact_premises" => Ok(Self::ClosedWithoutFactPremises),
            "fact_premise_declared" => Ok(Self::FactPremiseDeclared),
            "fact_premise_unused" => Ok(Self::FactPremiseUnused),
            "fact_premise_used" => Ok(Self::FactPremiseUsed),
            "fact_premise_directly_forwarded" => Ok(Self::FactPremiseDirectlyForwarded),
            "fact_premise_callback_forwarded" => Ok(Self::FactPremiseCallbackForwarded),
            "global_basis_uses_verified_theorem" => Ok(Self::GlobalBasisUsesVerifiedTheorem),
            "global_basis_uses_transitive_axiom" => Ok(Self::GlobalBasisUsesTransitiveAxiom),
            _ => Err(invalid_enum(path, "reason_codes", value)),
        }
    }
}

/// Deterministic package-level theorem-premise counts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PackageTheoremPremiseSummary {
    /// Total theorem entry count.
    pub theorem_count: u64,
    /// Closed statement count.
    pub closed_count: u64,
    /// Fact-parameterized statement count.
    pub fact_parameterized_count: u64,
    /// No-fact-premise use class count.
    pub none_declared_count: u64,
    /// Declared-unused use class count.
    pub declared_unused_count: u64,
    /// Ordinary used class count.
    pub used_count: u64,
    /// Forwarded use class count.
    pub forwarded_count: u64,
    /// Definitions-and-primitives-only basis count.
    pub definitions_and_primitives_only_count: u64,
    /// Verified-theorem-dependent basis count.
    pub verified_theorem_dependent_count: u64,
    /// Axiom-dependent basis count.
    pub axiom_dependent_count: u64,
    /// High-priority entry count.
    pub high_priority_count: u64,
    /// Review-priority entry count.
    pub review_priority_count: u64,
    /// Informational-priority entry count.
    pub informational_priority_count: u64,
    /// No-priority entry count.
    pub none_priority_count: u64,
}

/// Derive aggregate used and forwarded fact-premise indices.
pub fn package_theorem_proof_profile(
    fact_premises: &[PackageTheoremFactPremise],
) -> PackageTheoremProofProfile {
    let used_fact_premise_indices = fact_premises
        .iter()
        .filter(|premise| !premise.use_sites.is_empty())
        .map(|premise| premise.binder_index)
        .collect();
    let forwarded_fact_premise_indices = fact_premises
        .iter()
        .filter(|premise| {
            premise.use_sites.iter().any(|site| {
                matches!(
                    site,
                    PackageTheoremPremiseUseSite::DirectResult
                        | PackageTheoremPremiseUseSite::ApplicationHead
                )
            })
        })
        .map(|premise| premise.binder_index)
        .collect();
    PackageTheoremProofProfile {
        used_fact_premise_indices,
        forwarded_fact_premise_indices,
    }
}

/// Derive all theorem-premise classifications from structural entry data.
pub fn package_theorem_premise_classification(
    telescope: &PackageTheoremTelescopeProfile,
    proof: &PackageTheoremProofProfile,
    dependency_basis: &PackageTheoremDependencyProfile,
) -> PackageTheoremPremiseClassification {
    let statement_class = if telescope.fact_premises.is_empty() {
        PackageTheoremStatementClass::Closed
    } else {
        PackageTheoremStatementClass::FactParameterized
    };
    let premise_use_class = if telescope.fact_premises.is_empty() {
        PackageTheoremPremiseUseClass::NoneDeclared
    } else if proof.used_fact_premise_indices.is_empty() {
        PackageTheoremPremiseUseClass::DeclaredUnused
    } else if proof.forwarded_fact_premise_indices.is_empty() {
        PackageTheoremPremiseUseClass::Used
    } else {
        PackageTheoremPremiseUseClass::Forwarded
    };
    let uses_theorem = dependency_basis
        .global_dependencies
        .iter()
        .any(|dependency| dependency.kind == PackageTheoremGlobalDependencyKind::Theorem);
    let global_basis_class = if !dependency_basis.axiom_dependencies.is_empty() {
        PackageTheoremGlobalBasisClass::AxiomDependent
    } else if uses_theorem {
        PackageTheoremGlobalBasisClass::VerifiedTheoremDependent
    } else {
        PackageTheoremGlobalBasisClass::DefinitionsAndPrimitivesOnly
    };
    let review_priority = if premise_use_class == PackageTheoremPremiseUseClass::Forwarded
        || global_basis_class == PackageTheoremGlobalBasisClass::AxiomDependent
    {
        PackageTheoremReviewPriority::High
    } else if premise_use_class == PackageTheoremPremiseUseClass::Used {
        PackageTheoremReviewPriority::Review
    } else if premise_use_class == PackageTheoremPremiseUseClass::DeclaredUnused {
        PackageTheoremReviewPriority::Informational
    } else {
        PackageTheoremReviewPriority::None
    };
    let mut reason_codes = Vec::new();
    reason_codes.push(match statement_class {
        PackageTheoremStatementClass::Closed => {
            PackageTheoremPremiseReason::ClosedWithoutFactPremises
        }
        PackageTheoremStatementClass::FactParameterized => {
            PackageTheoremPremiseReason::FactPremiseDeclared
        }
    });
    if premise_use_class == PackageTheoremPremiseUseClass::DeclaredUnused {
        reason_codes.push(PackageTheoremPremiseReason::FactPremiseUnused);
    }
    if matches!(
        premise_use_class,
        PackageTheoremPremiseUseClass::Used | PackageTheoremPremiseUseClass::Forwarded
    ) {
        reason_codes.push(PackageTheoremPremiseReason::FactPremiseUsed);
    }
    if telescope.fact_premises.iter().any(|premise| {
        premise
            .use_sites
            .contains(&PackageTheoremPremiseUseSite::DirectResult)
    }) {
        reason_codes.push(PackageTheoremPremiseReason::FactPremiseDirectlyForwarded);
    }
    if telescope.fact_premises.iter().any(|premise| {
        premise
            .use_sites
            .contains(&PackageTheoremPremiseUseSite::ApplicationHead)
    }) {
        reason_codes.push(PackageTheoremPremiseReason::FactPremiseCallbackForwarded);
    }
    if uses_theorem {
        reason_codes.push(PackageTheoremPremiseReason::GlobalBasisUsesVerifiedTheorem);
    }
    if !dependency_basis.axiom_dependencies.is_empty() {
        reason_codes.push(PackageTheoremPremiseReason::GlobalBasisUsesTransitiveAxiom);
    }
    reason_codes.sort();
    PackageTheoremPremiseClassification {
        statement_class,
        premise_use_class,
        global_basis_class,
        review_priority,
        reason_codes,
    }
}

/// Recompute deterministic package theorem-premise summary counts.
pub fn package_theorem_premise_summary(
    entries: &[PackageTheoremPremiseEntry],
) -> PackageTheoremPremiseSummary {
    let mut summary = PackageTheoremPremiseSummary {
        theorem_count: entries.len() as u64,
        ..PackageTheoremPremiseSummary::default()
    };
    for entry in entries {
        match entry.classification.statement_class {
            PackageTheoremStatementClass::Closed => summary.closed_count += 1,
            PackageTheoremStatementClass::FactParameterized => {
                summary.fact_parameterized_count += 1
            }
        }
        match entry.classification.premise_use_class {
            PackageTheoremPremiseUseClass::NoneDeclared => summary.none_declared_count += 1,
            PackageTheoremPremiseUseClass::DeclaredUnused => summary.declared_unused_count += 1,
            PackageTheoremPremiseUseClass::Used => summary.used_count += 1,
            PackageTheoremPremiseUseClass::Forwarded => summary.forwarded_count += 1,
        }
        match entry.classification.global_basis_class {
            PackageTheoremGlobalBasisClass::DefinitionsAndPrimitivesOnly => {
                summary.definitions_and_primitives_only_count += 1
            }
            PackageTheoremGlobalBasisClass::VerifiedTheoremDependent => {
                summary.verified_theorem_dependent_count += 1
            }
            PackageTheoremGlobalBasisClass::AxiomDependent => summary.axiom_dependent_count += 1,
        }
        match entry.classification.review_priority {
            PackageTheoremReviewPriority::High => summary.high_priority_count += 1,
            PackageTheoremReviewPriority::Review => summary.review_priority_count += 1,
            PackageTheoremReviewPriority::Informational => {
                summary.informational_priority_count += 1
            }
            PackageTheoremReviewPriority::None => summary.none_priority_count += 1,
        }
    }
    summary
}

/// Parse and validate canonical theorem-premise report JSON.
pub fn parse_package_theorem_premise_report_json(
    source: &str,
) -> PackageArtifactResult<PackageTheoremPremiseReport> {
    let root = parse_artifact_json(source)?;
    let report = parse_report_value(&root)?;
    validate_package_theorem_premise_report(&report)?;
    if source != report.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "package theorem-premise report JSON bytes",
        ));
    }
    Ok(report)
}

/// Validate a theorem-premise report model without filesystem access.
pub fn validate_package_theorem_premise_report(
    report: &PackageTheoremPremiseReport,
) -> PackageArtifactResult<()> {
    validate_report_shape_without_self_hash(report)?;
    let expected = compute_package_theorem_premise_report_hash(report)?;
    if expected != report.report_hash {
        return Err(PackageArtifactError::self_hash_mismatch(
            "report_hash",
            "report_hash",
            format_package_hash(&expected),
            format_package_hash(&report.report_hash),
        ));
    }
    Ok(())
}

/// Compute the report self hash over canonical bytes excluding `report_hash`.
pub fn compute_package_theorem_premise_report_hash(
    report: &PackageTheoremPremiseReport,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = report.clone();
    normalize_report(&mut normalized);
    validate_report_shape_without_self_hash(&normalized)?;
    Ok(package_file_hash(
        report_json_unchecked(&normalized, false).as_bytes(),
    ))
}

fn validate_report_shape_without_self_hash(
    report: &PackageTheoremPremiseReport,
) -> PackageArtifactResult<()> {
    if report.schema != PACKAGE_THEOREM_PREMISE_REPORT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_THEOREM_PREMISE_REPORT_SCHEMA,
            &report.schema,
        ));
    }
    validate_package_identity(&report.package, &report.version)?;
    validate_artifact_file_reference(&report.manifest, "manifest")?;
    validate_artifact_file_reference(&report.package_lock, "package_lock")?;
    if report.analysis_profile != PACKAGE_THEOREM_PREMISE_REPORT_PROFILE {
        return Err(PackageArtifactError::invalid_enum_value(
            "analysis_profile",
            "analysis_profile",
            PACKAGE_THEOREM_PREMISE_REPORT_PROFILE,
            &report.analysis_profile,
        ));
    }
    if report.limits != PACKAGE_THEOREM_PREMISE_ANALYSIS_LIMITS_V1 {
        return Err(PackageArtifactError::summary_mismatch(
            "limits",
            "limits",
            "fixed theorem-premise analysis limits v1",
            "different values",
        ));
    }
    validate_checker_summaries(&report.checker_summaries)?;
    if report
        .checker_summaries
        .iter()
        .any(|summary| summary.mode != PackageCheckerMode::Fast)
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "checker_summaries",
            "mode",
            "fast",
            "reference",
        ));
    }
    validate_entries(&report.entries)?;
    let expected = package_theorem_premise_summary(&report.entries);
    if expected != report.summary {
        return Err(PackageArtifactError::summary_mismatch(
            "summary",
            "summary",
            format!("{expected:?}"),
            format!("{:?}", report.summary),
        ));
    }
    Ok(())
}

fn validate_entries(entries: &[PackageTheoremPremiseEntry]) -> PackageArtifactResult<()> {
    let mut entry_keys = BTreeSet::new();
    for (entry_index, entry) in entries.iter().enumerate() {
        let path = format!("entries[{entry_index}]");
        validate_global_ref(&entry.global_ref, &field_path(&path, "global_ref"))?;
        let key = global_ref_sort_key(&entry.global_ref);
        if !entry_keys.insert(key.clone()) {
            return Err(duplicate_key_error(
                field_path(&path, "global_ref"),
                "global_ref",
                PackageArtifactErrorReason::DuplicateTheoremEntry,
                key,
            ));
        }
        if entry.artifact.origin != PackageArtifactOrigin::Local {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}.artifact.origin"),
                "origin",
                "local",
                entry.artifact.origin.as_str(),
            ));
        }
        validate_artifact_path(
            &entry.artifact.certificate,
            format!("{path}.artifact.certificate"),
        )?;
        validate_telescope(&entry.telescope, &format!("{path}.telescope"))?;
        validate_proof(&entry.proof, &entry.telescope, &format!("{path}.proof"))?;
        validate_dependency_basis(&entry.dependency_basis, &format!("{path}.dependency_basis"))?;
        let expected = package_theorem_premise_classification(
            &entry.telescope,
            &entry.proof,
            &entry.dependency_basis,
        );
        if entry.classification != expected {
            return Err(PackageArtifactError::summary_mismatch(
                format!("{path}.classification"),
                "classification",
                format!("{expected:?}"),
                format!("{:?}", entry.classification),
            ));
        }
    }
    Ok(())
}

fn validate_telescope(
    telescope: &PackageTheoremTelescopeProfile,
    path: &str,
) -> PackageArtifactResult<()> {
    let mut partition = BTreeSet::new();
    for (field, indices) in [
        ("sort_parameter_indices", &telescope.sort_parameter_indices),
        ("data_parameter_indices", &telescope.data_parameter_indices),
    ] {
        validate_index_set(indices, telescope.binder_count, &field_path(path, field))?;
        for index in indices {
            if !partition.insert(*index) {
                return Err(duplicate_index(&field_path(path, field), *index));
            }
        }
    }
    let mut fact_keys = BTreeSet::new();
    for (premise_index, premise) in telescope.fact_premises.iter().enumerate() {
        let premise_path = format!("{path}.fact_premises[{premise_index}]");
        if premise.binder_index >= telescope.binder_count {
            return Err(index_mismatch(&premise_path, premise.binder_index));
        }
        if !fact_keys.insert(premise.binder_index) || !partition.insert(premise.binder_index) {
            return Err(duplicate_index(&premise_path, premise.binder_index));
        }
        validate_index_set(
            &premise.depends_on_prior_binder_indices,
            premise.binder_index,
            &format!("{premise_path}.depends_on_prior_binder_indices"),
        )?;
        validate_unique_enum_values(
            premise.use_sites.iter().map(|value| value.as_str()),
            &format!("{premise_path}.use_sites"),
        )?;
    }
    if partition != (0..telescope.binder_count).collect::<BTreeSet<_>>() {
        return Err(PackageArtifactError::summary_mismatch(
            path,
            "binder partition",
            "exactly 0..binder_count",
            "incomplete or overlapping",
        ));
    }
    validate_index_set(
        &telescope.conclusion_depends_on_binder_indices,
        telescope.binder_count,
        &format!("{path}.conclusion_depends_on_binder_indices"),
    )
}

fn validate_proof(
    proof: &PackageTheoremProofProfile,
    telescope: &PackageTheoremTelescopeProfile,
    path: &str,
) -> PackageArtifactResult<()> {
    validate_index_set(
        &proof.used_fact_premise_indices,
        telescope.binder_count,
        &format!("{path}.used_fact_premise_indices"),
    )?;
    validate_index_set(
        &proof.forwarded_fact_premise_indices,
        telescope.binder_count,
        &format!("{path}.forwarded_fact_premise_indices"),
    )?;
    let expected = package_theorem_proof_profile(&telescope.fact_premises);
    if proof != &expected {
        return Err(PackageArtifactError::summary_mismatch(
            path,
            "proof",
            format!("{expected:?}"),
            format!("{proof:?}"),
        ));
    }
    Ok(())
}

fn validate_dependency_basis(
    basis: &PackageTheoremDependencyProfile,
    path: &str,
) -> PackageArtifactResult<()> {
    let mut identities = BTreeSet::new();
    let mut direct_axiom = false;
    for (index, dependency) in basis.global_dependencies.iter().enumerate() {
        let item_path = format!("{path}.global_dependencies[{index}]");
        match &dependency.identity {
            PackageTheoremGlobalDependencyIdentity::Builtin { name, .. } => {
                validate_declaration_name(name, format!("{item_path}.identity.name"))?;
                if !matches!(
                    dependency.kind,
                    PackageTheoremGlobalDependencyKind::BuiltinPrimitive
                        | PackageTheoremGlobalDependencyKind::BuiltinAxiom
                ) {
                    return Err(PackageArtifactError::invalid_enum_value(
                        format!("{item_path}.kind"),
                        "kind",
                        "builtin_primitive or builtin_axiom",
                        dependency.kind.as_str(),
                    ));
                }
            }
            PackageTheoremGlobalDependencyIdentity::PackageGlobal(global_ref) => {
                validate_global_ref(global_ref, &format!("{item_path}.identity"))?;
                if matches!(
                    dependency.kind,
                    PackageTheoremGlobalDependencyKind::BuiltinPrimitive
                        | PackageTheoremGlobalDependencyKind::BuiltinAxiom
                ) {
                    return Err(PackageArtifactError::invalid_enum_value(
                        format!("{item_path}.kind"),
                        "kind",
                        "non-builtin dependency kind",
                        dependency.kind.as_str(),
                    ));
                }
            }
        }
        direct_axiom |= matches!(
            dependency.kind,
            PackageTheoremGlobalDependencyKind::BuiltinAxiom
                | PackageTheoremGlobalDependencyKind::Axiom
        );
        let key = dependency_identity_sort_key(&dependency.identity);
        if !identities.insert(key.clone()) {
            return Err(duplicate_key_error(
                format!("{item_path}.identity"),
                "global_dependencies",
                PackageArtifactErrorReason::DuplicateConstant,
                key,
            ));
        }
    }
    let mut axioms = BTreeSet::new();
    for (index, axiom) in basis.axiom_dependencies.iter().enumerate() {
        let item_path = format!("{path}.axiom_dependencies[{index}]");
        validate_axiom_reference(axiom, &item_path)?;
        let key = axiom_reference_sort_key(axiom);
        if !axioms.insert(key.clone()) {
            return Err(duplicate_key_error(
                item_path,
                "axiom_dependencies",
                PackageArtifactErrorReason::DuplicateAxiom,
                key,
            ));
        }
    }
    if direct_axiom && basis.axiom_dependencies.is_empty() {
        return Err(PackageArtifactError::summary_mismatch(
            path,
            "axiom_dependencies",
            "direct axiom represented in transitive axiom set",
            "empty",
        ));
    }
    Ok(())
}

fn validate_index_set(indices: &[u64], bound: u64, path: &str) -> PackageArtifactResult<()> {
    let mut seen = BTreeSet::new();
    for index in indices {
        if *index >= bound {
            return Err(index_mismatch(path, *index));
        }
        if !seen.insert(*index) {
            return Err(duplicate_index(path, *index));
        }
    }
    Ok(())
}

fn validate_unique_enum_values<'a>(
    values: impl IntoIterator<Item = &'a str>,
    path: &str,
) -> PackageArtifactResult<()> {
    let mut seen = BTreeSet::new();
    for value in values {
        if !seen.insert(value) {
            return Err(duplicate_key_error(
                path,
                "enum array",
                PackageArtifactErrorReason::DuplicateConstant,
                value,
            ));
        }
    }
    Ok(())
}

fn index_mismatch(path: &str, index: u64) -> PackageArtifactError {
    PackageArtifactError::summary_mismatch(path, "binder_index", "in range", index.to_string())
}

fn duplicate_index(path: &str, index: u64) -> PackageArtifactError {
    duplicate_key_error(
        path,
        "binder_index",
        PackageArtifactErrorReason::DuplicateConstant,
        index.to_string(),
    )
}

fn normalize_report(report: &mut PackageTheoremPremiseReport) {
    report
        .entries
        .sort_by_key(|entry| global_ref_sort_key(&entry.global_ref));
    for entry in &mut report.entries {
        entry.telescope.sort_parameter_indices.sort();
        entry.telescope.data_parameter_indices.sort();
        entry
            .telescope
            .fact_premises
            .sort_by_key(|premise| premise.binder_index);
        entry.telescope.conclusion_depends_on_binder_indices.sort();
        for premise in &mut entry.telescope.fact_premises {
            premise.depends_on_prior_binder_indices.sort();
            premise.use_sites.sort();
        }
        entry.proof.used_fact_premise_indices.sort();
        entry.proof.forwarded_fact_premise_indices.sort();
        entry
            .dependency_basis
            .global_dependencies
            .sort_by(|left, right| {
                dependency_identity_sort_key(&left.identity)
                    .cmp(&dependency_identity_sort_key(&right.identity))
                    .then(left.kind.cmp(&right.kind))
            });
        entry
            .dependency_basis
            .axiom_dependencies
            .sort_by_key(axiom_reference_sort_key);
        entry.classification.reason_codes.sort();
    }
    normalize_checker_summaries(&mut report.checker_summaries);
}

fn dependency_identity_sort_key(identity: &PackageTheoremGlobalDependencyIdentity) -> String {
    match identity {
        PackageTheoremGlobalDependencyIdentity::Builtin {
            name,
            decl_interface_hash,
        } => format!(
            "0\u{1f}{}\u{1f}{}",
            name.as_dotted(),
            format_package_hash(decl_interface_hash)
        ),
        PackageTheoremGlobalDependencyIdentity::PackageGlobal(global_ref) => {
            format!("1\u{1f}{}", global_ref_sort_key(global_ref))
        }
    }
}

fn parse_report_value(value: &JsonValue) -> PackageArtifactResult<PackageTheoremPremiseReport> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, TOP_LEVEL_FIELDS)?;
    Ok(PackageTheoremPremiseReport {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        version: PackageVersion::new(required_string(members, "$", "version")?),
        manifest: parse_file_reference(required_value(members, "$", "manifest")?, "manifest")?,
        package_lock: parse_file_reference(
            required_value(members, "$", "package_lock")?,
            "package_lock",
        )?,
        analysis_profile: required_string(members, "$", "analysis_profile")?,
        limits: parse_limits(required_value(members, "$", "limits")?)?,
        entries: required_array(members, "$", "entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_entry(value, &format!("entries[{index}]")))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        checker_summaries: required_array(members, "$", "checker_summaries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_checker_summary(index, value))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        summary: parse_summary(required_value(members, "$", "summary")?)?,
        report_hash: required_hash(members, "$", "report_hash")?,
    })
}

fn parse_limits(value: &JsonValue) -> PackageArtifactResult<PackageTheoremPremiseAnalysisLimits> {
    let path = "limits";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, LIMIT_FIELDS)?;
    Ok(PackageTheoremPremiseAnalysisLimits {
        telescope_binders_per_theorem: required_u64(
            members,
            path,
            "telescope_binders_per_theorem",
        )?,
        kernel_whnf_fuel_per_theorem: required_u64(members, path, "kernel_whnf_fuel_per_theorem")?,
        kernel_conversion_fuel_per_theorem: required_u64(
            members,
            path,
            "kernel_conversion_fuel_per_theorem",
        )?,
        expression_traversal_states_per_theorem: required_u64(
            members,
            path,
            "expression_traversal_states_per_theorem",
        )?,
        resolved_global_dependencies_per_theorem: required_u64(
            members,
            path,
            "resolved_global_dependencies_per_theorem",
        )?,
    })
}

fn parse_entry(value: &JsonValue, path: &str) -> PackageArtifactResult<PackageTheoremPremiseEntry> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ENTRY_FIELDS)?;
    Ok(PackageTheoremPremiseEntry {
        global_ref: parse_global_ref(
            required_value(members, path, "global_ref")?,
            &field_path(path, "global_ref"),
        )?,
        statement_hash: required_hash(members, path, "statement_hash")?,
        module_axiom_report_hash: required_hash(members, path, "module_axiom_report_hash")?,
        artifact: parse_artifact(
            required_value(members, path, "artifact")?,
            &field_path(path, "artifact"),
        )?,
        telescope: parse_telescope(
            required_value(members, path, "telescope")?,
            &field_path(path, "telescope"),
        )?,
        proof: parse_proof(
            required_value(members, path, "proof")?,
            &field_path(path, "proof"),
        )?,
        dependency_basis: parse_dependency_basis(
            required_value(members, path, "dependency_basis")?,
            &field_path(path, "dependency_basis"),
        )?,
        classification: parse_classification(
            required_value(members, path, "classification")?,
            &field_path(path, "classification"),
        )?,
    })
}

fn parse_artifact(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremIndexArtifact> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, ARTIFACT_FIELDS)?;
    Ok(PackageTheoremIndexArtifact {
        origin: PackageArtifactOrigin::parse(
            &required_string(members, path, "origin")?,
            &field_path(path, "origin"),
        )?,
        certificate: PackagePath::new(required_string(members, path, "certificate")?),
    })
}

fn parse_telescope(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremTelescopeProfile> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TELESCOPE_FIELDS)?;
    Ok(PackageTheoremTelescopeProfile {
        binder_count: required_u64(members, path, "binder_count")?,
        sort_parameter_indices: parse_u64_array(members, path, "sort_parameter_indices")?,
        data_parameter_indices: parse_u64_array(members, path, "data_parameter_indices")?,
        fact_premises: required_array(members, path, "fact_premises")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_fact_premise(value, &format!("{path}.fact_premises[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        conclusion_hash: required_hash(members, path, "conclusion_hash")?,
        conclusion_depends_on_binder_indices: parse_u64_array(
            members,
            path,
            "conclusion_depends_on_binder_indices",
        )?,
    })
}

fn parse_fact_premise(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremFactPremise> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, FACT_PREMISE_FIELDS)?;
    Ok(PackageTheoremFactPremise {
        binder_index: required_u64(members, path, "binder_index")?,
        type_hash: required_hash(members, path, "type_hash")?,
        depends_on_prior_binder_indices: parse_u64_array(
            members,
            path,
            "depends_on_prior_binder_indices",
        )?,
        use_sites: parse_enum_array(
            required_array(members, path, "use_sites")?,
            &format!("{path}.use_sites"),
            PackageTheoremPremiseUseSite::parse,
        )?,
    })
}

fn parse_proof(value: &JsonValue, path: &str) -> PackageArtifactResult<PackageTheoremProofProfile> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, PROOF_FIELDS)?;
    Ok(PackageTheoremProofProfile {
        used_fact_premise_indices: parse_u64_array(members, path, "used_fact_premise_indices")?,
        forwarded_fact_premise_indices: parse_u64_array(
            members,
            path,
            "forwarded_fact_premise_indices",
        )?,
    })
}

fn parse_dependency_basis(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremDependencyProfile> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, DEPENDENCY_BASIS_FIELDS)?;
    Ok(PackageTheoremDependencyProfile {
        global_dependencies: required_array(members, path, "global_dependencies")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_global_dependency(value, &format!("{path}.global_dependencies[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        axiom_dependencies: required_array(members, path, "axiom_dependencies")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_axiom_reference(value, &format!("{path}.axiom_dependencies[{index}]"))
            })
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_global_dependency(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremGlobalDependency> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GLOBAL_DEPENDENCY_FIELDS)?;
    Ok(PackageTheoremGlobalDependency {
        identity: parse_dependency_identity(
            required_value(members, path, "identity")?,
            &field_path(path, "identity"),
        )?,
        kind: PackageTheoremGlobalDependencyKind::parse(
            &required_string(members, path, "kind")?,
            &field_path(path, "kind"),
        )?,
    })
}

fn parse_dependency_identity(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremGlobalDependencyIdentity> {
    let members = expect_object(value, path)?;
    let provider = required_string(members, path, "provider")?;
    match provider.as_str() {
        "builtin" => {
            reject_unknown_fields(path, members, BUILTIN_IDENTITY_FIELDS)?;
            Ok(PackageTheoremGlobalDependencyIdentity::Builtin {
                name: required_name(members, path, "name")?,
                decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
            })
        }
        "package_global" => {
            reject_unknown_fields(path, members, PACKAGE_GLOBAL_IDENTITY_FIELDS)?;
            Ok(PackageTheoremGlobalDependencyIdentity::PackageGlobal(
                PackageGlobalRef {
                    module: required_name(members, path, "module")?,
                    name: required_name(members, path, "name")?,
                    export_hash: required_hash(members, path, "export_hash")?,
                    certificate_hash: required_hash(members, path, "certificate_hash")?,
                    decl_interface_hash: required_hash(members, path, "decl_interface_hash")?,
                },
            ))
        }
        _ => Err(PackageArtifactError::invalid_enum_value(
            field_path(path, "provider"),
            "provider",
            "builtin or package_global",
            provider,
        )),
    }
}

fn parse_classification(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PackageTheoremPremiseClassification> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CLASSIFICATION_FIELDS)?;
    Ok(PackageTheoremPremiseClassification {
        statement_class: PackageTheoremStatementClass::parse(
            &required_string(members, path, "statement_class")?,
            &field_path(path, "statement_class"),
        )?,
        premise_use_class: PackageTheoremPremiseUseClass::parse(
            &required_string(members, path, "premise_use_class")?,
            &field_path(path, "premise_use_class"),
        )?,
        global_basis_class: PackageTheoremGlobalBasisClass::parse(
            &required_string(members, path, "global_basis_class")?,
            &field_path(path, "global_basis_class"),
        )?,
        review_priority: PackageTheoremReviewPriority::parse(
            &required_string(members, path, "review_priority")?,
            &field_path(path, "review_priority"),
        )?,
        reason_codes: parse_enum_array(
            required_array(members, path, "reason_codes")?,
            &format!("{path}.reason_codes"),
            PackageTheoremPremiseReason::parse,
        )?,
    })
}

fn parse_summary(value: &JsonValue) -> PackageArtifactResult<PackageTheoremPremiseSummary> {
    let path = "summary";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, SUMMARY_FIELDS)?;
    Ok(PackageTheoremPremiseSummary {
        theorem_count: required_u64(members, path, "theorem_count")?,
        closed_count: required_u64(members, path, "closed_count")?,
        fact_parameterized_count: required_u64(members, path, "fact_parameterized_count")?,
        none_declared_count: required_u64(members, path, "none_declared_count")?,
        declared_unused_count: required_u64(members, path, "declared_unused_count")?,
        used_count: required_u64(members, path, "used_count")?,
        forwarded_count: required_u64(members, path, "forwarded_count")?,
        definitions_and_primitives_only_count: required_u64(
            members,
            path,
            "definitions_and_primitives_only_count",
        )?,
        verified_theorem_dependent_count: required_u64(
            members,
            path,
            "verified_theorem_dependent_count",
        )?,
        axiom_dependent_count: required_u64(members, path, "axiom_dependent_count")?,
        high_priority_count: required_u64(members, path, "high_priority_count")?,
        review_priority_count: required_u64(members, path, "review_priority_count")?,
        informational_priority_count: required_u64(members, path, "informational_priority_count")?,
        none_priority_count: required_u64(members, path, "none_priority_count")?,
    })
}

fn parse_u64_array(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Vec<u64>> {
    required_array(members, path, field)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let number = value.number_value().ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    Some(field.to_owned()),
                    "unsigned integer",
                    value.kind().as_str(),
                )
            })?;
            if number.starts_with('-')
                || number.contains('.')
                || number.contains('e')
                || number.contains('E')
                || (number.len() > 1 && number.starts_with('0'))
            {
                return Err(PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    Some(field.to_owned()),
                    "unsigned integer",
                    number,
                ));
            }
            number.parse::<u64>().map_err(|_| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    Some(field.to_owned()),
                    "unsigned integer",
                    number,
                )
            })
        })
        .collect()
}

fn parse_enum_array<T>(
    values: &[JsonValue],
    path: &str,
    parse: impl Fn(&str, &str) -> PackageArtifactResult<T>,
) -> PackageArtifactResult<Vec<T>> {
    values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let item_path = format!("{path}[{index}]");
            let string = value.string_value().ok_or_else(|| {
                PackageArtifactError::wrong_type(&item_path, None, "string", value.kind().as_str())
            })?;
            parse(string, &item_path)
        })
        .collect()
}

fn report_json_unchecked(report: &PackageTheoremPremiseReport, include_hash: bool) -> String {
    let mut fields = vec![
        ("schema", json_string(&report.schema)),
        ("package", json_string(report.package.as_str())),
        ("version", json_string(report.version.as_str())),
        ("manifest", file_reference_json(&report.manifest)),
        ("package_lock", file_reference_json(&report.package_lock)),
        ("analysis_profile", json_string(&report.analysis_profile)),
        ("limits", limits_json(report.limits)),
        (
            "entries",
            json_array(report.entries.iter().map(entry_json).collect()),
        ),
        (
            "checker_summaries",
            json_array(
                report
                    .checker_summaries
                    .iter()
                    .map(checker_summary_json)
                    .collect(),
            ),
        ),
        ("summary", summary_json(&report.summary)),
    ];
    if include_hash {
        fields.push(("report_hash", hash_json(report.report_hash)));
    }
    json_object_in_order(fields)
}

fn limits_json(limits: PackageTheoremPremiseAnalysisLimits) -> String {
    json_object_in_order(vec![
        (
            "telescope_binders_per_theorem",
            json_u64(limits.telescope_binders_per_theorem),
        ),
        (
            "kernel_whnf_fuel_per_theorem",
            json_u64(limits.kernel_whnf_fuel_per_theorem),
        ),
        (
            "kernel_conversion_fuel_per_theorem",
            json_u64(limits.kernel_conversion_fuel_per_theorem),
        ),
        (
            "expression_traversal_states_per_theorem",
            json_u64(limits.expression_traversal_states_per_theorem),
        ),
        (
            "resolved_global_dependencies_per_theorem",
            json_u64(limits.resolved_global_dependencies_per_theorem),
        ),
    ])
}

fn entry_json(entry: &PackageTheoremPremiseEntry) -> String {
    json_object_in_order(vec![
        ("global_ref", global_ref_json(&entry.global_ref)),
        ("statement_hash", hash_json(entry.statement_hash)),
        (
            "module_axiom_report_hash",
            hash_json(entry.module_axiom_report_hash),
        ),
        ("artifact", artifact_json(&entry.artifact)),
        ("telescope", telescope_json(&entry.telescope)),
        ("proof", proof_json(&entry.proof)),
        (
            "dependency_basis",
            dependency_basis_json(&entry.dependency_basis),
        ),
        ("classification", classification_json(&entry.classification)),
    ])
}

fn artifact_json(artifact: &PackageTheoremIndexArtifact) -> String {
    json_object_in_order(vec![
        ("origin", json_string(artifact.origin.as_str())),
        ("certificate", json_string(artifact.certificate.as_str())),
    ])
}

fn telescope_json(telescope: &PackageTheoremTelescopeProfile) -> String {
    json_object_in_order(vec![
        ("binder_count", json_u64(telescope.binder_count)),
        (
            "sort_parameter_indices",
            json_array(
                telescope
                    .sort_parameter_indices
                    .iter()
                    .map(|value| json_u64(*value))
                    .collect(),
            ),
        ),
        (
            "data_parameter_indices",
            json_array(
                telescope
                    .data_parameter_indices
                    .iter()
                    .map(|value| json_u64(*value))
                    .collect(),
            ),
        ),
        (
            "fact_premises",
            json_array(
                telescope
                    .fact_premises
                    .iter()
                    .map(fact_premise_json)
                    .collect(),
            ),
        ),
        ("conclusion_hash", hash_json(telescope.conclusion_hash)),
        (
            "conclusion_depends_on_binder_indices",
            json_array(
                telescope
                    .conclusion_depends_on_binder_indices
                    .iter()
                    .map(|value| json_u64(*value))
                    .collect(),
            ),
        ),
    ])
}

fn fact_premise_json(premise: &PackageTheoremFactPremise) -> String {
    json_object_in_order(vec![
        ("binder_index", json_u64(premise.binder_index)),
        ("type_hash", hash_json(premise.type_hash)),
        (
            "depends_on_prior_binder_indices",
            json_array(
                premise
                    .depends_on_prior_binder_indices
                    .iter()
                    .map(|value| json_u64(*value))
                    .collect(),
            ),
        ),
        (
            "use_sites",
            json_array(
                premise
                    .use_sites
                    .iter()
                    .map(|value| json_string(value.as_str()))
                    .collect(),
            ),
        ),
    ])
}

fn proof_json(proof: &PackageTheoremProofProfile) -> String {
    json_object_in_order(vec![
        (
            "used_fact_premise_indices",
            json_array(
                proof
                    .used_fact_premise_indices
                    .iter()
                    .map(|value| json_u64(*value))
                    .collect(),
            ),
        ),
        (
            "forwarded_fact_premise_indices",
            json_array(
                proof
                    .forwarded_fact_premise_indices
                    .iter()
                    .map(|value| json_u64(*value))
                    .collect(),
            ),
        ),
    ])
}

fn dependency_basis_json(basis: &PackageTheoremDependencyProfile) -> String {
    json_object_in_order(vec![
        (
            "global_dependencies",
            json_array(
                basis
                    .global_dependencies
                    .iter()
                    .map(global_dependency_json)
                    .collect(),
            ),
        ),
        (
            "axiom_dependencies",
            json_array(
                basis
                    .axiom_dependencies
                    .iter()
                    .map(axiom_reference_json)
                    .collect(),
            ),
        ),
    ])
}

fn global_dependency_json(dependency: &PackageTheoremGlobalDependency) -> String {
    json_object_in_order(vec![
        ("identity", dependency_identity_json(&dependency.identity)),
        ("kind", json_string(dependency.kind.as_str())),
    ])
}

fn dependency_identity_json(identity: &PackageTheoremGlobalDependencyIdentity) -> String {
    match identity {
        PackageTheoremGlobalDependencyIdentity::Builtin {
            name,
            decl_interface_hash,
        } => json_object_in_order(vec![
            ("provider", json_string("builtin")),
            ("name", json_string(&name.as_dotted())),
            ("decl_interface_hash", hash_json(*decl_interface_hash)),
        ]),
        PackageTheoremGlobalDependencyIdentity::PackageGlobal(global_ref) => {
            json_object_in_order(vec![
                ("provider", json_string("package_global")),
                ("module", json_string(&global_ref.module.as_dotted())),
                ("name", json_string(&global_ref.name.as_dotted())),
                ("export_hash", hash_json(global_ref.export_hash)),
                ("certificate_hash", hash_json(global_ref.certificate_hash)),
                (
                    "decl_interface_hash",
                    hash_json(global_ref.decl_interface_hash),
                ),
            ])
        }
    }
}

fn classification_json(classification: &PackageTheoremPremiseClassification) -> String {
    json_object_in_order(vec![
        (
            "statement_class",
            json_string(classification.statement_class.as_str()),
        ),
        (
            "premise_use_class",
            json_string(classification.premise_use_class.as_str()),
        ),
        (
            "global_basis_class",
            json_string(classification.global_basis_class.as_str()),
        ),
        (
            "review_priority",
            json_string(classification.review_priority.as_str()),
        ),
        (
            "reason_codes",
            json_array(
                classification
                    .reason_codes
                    .iter()
                    .map(|value| json_string(value.as_str()))
                    .collect(),
            ),
        ),
    ])
}

fn summary_json(summary: &PackageTheoremPremiseSummary) -> String {
    json_object_in_order(vec![
        ("theorem_count", json_u64(summary.theorem_count)),
        ("closed_count", json_u64(summary.closed_count)),
        (
            "fact_parameterized_count",
            json_u64(summary.fact_parameterized_count),
        ),
        ("none_declared_count", json_u64(summary.none_declared_count)),
        (
            "declared_unused_count",
            json_u64(summary.declared_unused_count),
        ),
        ("used_count", json_u64(summary.used_count)),
        ("forwarded_count", json_u64(summary.forwarded_count)),
        (
            "definitions_and_primitives_only_count",
            json_u64(summary.definitions_and_primitives_only_count),
        ),
        (
            "verified_theorem_dependent_count",
            json_u64(summary.verified_theorem_dependent_count),
        ),
        (
            "axiom_dependent_count",
            json_u64(summary.axiom_dependent_count),
        ),
        ("high_priority_count", json_u64(summary.high_priority_count)),
        (
            "review_priority_count",
            json_u64(summary.review_priority_count),
        ),
        (
            "informational_priority_count",
            json_u64(summary.informational_priority_count),
        ),
        ("none_priority_count", json_u64(summary.none_priority_count)),
    ])
}

fn invalid_enum(path: &str, field: &str, value: &str) -> PackageArtifactError {
    PackageArtifactError::invalid_enum_value(path, field, "canonical theorem-premise value", value)
}

const TOP_LEVEL_FIELDS: &[&str] = &[
    "schema",
    "package",
    "version",
    "manifest",
    "package_lock",
    "analysis_profile",
    "limits",
    "entries",
    "checker_summaries",
    "summary",
    "report_hash",
];
const LIMIT_FIELDS: &[&str] = &[
    "telescope_binders_per_theorem",
    "kernel_whnf_fuel_per_theorem",
    "kernel_conversion_fuel_per_theorem",
    "expression_traversal_states_per_theorem",
    "resolved_global_dependencies_per_theorem",
];
const ENTRY_FIELDS: &[&str] = &[
    "global_ref",
    "statement_hash",
    "module_axiom_report_hash",
    "artifact",
    "telescope",
    "proof",
    "dependency_basis",
    "classification",
];
const ARTIFACT_FIELDS: &[&str] = &["origin", "certificate"];
const TELESCOPE_FIELDS: &[&str] = &[
    "binder_count",
    "sort_parameter_indices",
    "data_parameter_indices",
    "fact_premises",
    "conclusion_hash",
    "conclusion_depends_on_binder_indices",
];
const FACT_PREMISE_FIELDS: &[&str] = &[
    "binder_index",
    "type_hash",
    "depends_on_prior_binder_indices",
    "use_sites",
];
const PROOF_FIELDS: &[&str] = &[
    "used_fact_premise_indices",
    "forwarded_fact_premise_indices",
];
const DEPENDENCY_BASIS_FIELDS: &[&str] = &["global_dependencies", "axiom_dependencies"];
const GLOBAL_DEPENDENCY_FIELDS: &[&str] = &["identity", "kind"];
const BUILTIN_IDENTITY_FIELDS: &[&str] = &["provider", "name", "decl_interface_hash"];
const PACKAGE_GLOBAL_IDENTITY_FIELDS: &[&str] = &[
    "provider",
    "module",
    "name",
    "export_hash",
    "certificate_hash",
    "decl_interface_hash",
];
const CLASSIFICATION_FIELDS: &[&str] = &[
    "statement_class",
    "premise_use_class",
    "global_basis_class",
    "review_priority",
    "reason_codes",
];
const SUMMARY_FIELDS: &[&str] = &[
    "theorem_count",
    "closed_count",
    "fact_parameterized_count",
    "none_declared_count",
    "declared_unused_count",
    "used_count",
    "forwarded_count",
    "definitions_and_primitives_only_count",
    "verified_theorem_dependent_count",
    "axiom_dependent_count",
    "high_priority_count",
    "review_priority_count",
    "informational_priority_count",
    "none_priority_count",
];

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(seed: u8) -> PackageHash {
        PackageHash::new([seed; 32])
    }

    fn entry() -> PackageTheoremPremiseEntry {
        let telescope = PackageTheoremTelescopeProfile {
            binder_count: 2,
            sort_parameter_indices: vec![0],
            data_parameter_indices: vec![],
            fact_premises: vec![PackageTheoremFactPremise {
                binder_index: 1,
                type_hash: hash(7),
                depends_on_prior_binder_indices: vec![0],
                use_sites: vec![PackageTheoremPremiseUseSite::DirectResult],
            }],
            conclusion_hash: hash(8),
            conclusion_depends_on_binder_indices: vec![0],
        };
        let proof = package_theorem_proof_profile(&telescope.fact_premises);
        let dependency_basis = PackageTheoremDependencyProfile {
            global_dependencies: vec![],
            axiom_dependencies: vec![],
        };
        let classification =
            package_theorem_premise_classification(&telescope, &proof, &dependency_basis);
        PackageTheoremPremiseEntry {
            global_ref: PackageGlobalRef {
                module: Name::from_dotted("Premise.Test"),
                name: Name::from_dotted("identity"),
                export_hash: hash(1),
                certificate_hash: hash(2),
                decl_interface_hash: hash(3),
            },
            statement_hash: hash(4),
            module_axiom_report_hash: hash(5),
            artifact: PackageTheoremIndexArtifact {
                origin: PackageArtifactOrigin::Local,
                certificate: PackagePath::new("Premise/Test/cert.npcert"),
            },
            telescope,
            proof,
            dependency_basis,
            classification,
        }
    }

    fn report() -> PackageTheoremPremiseReport {
        let entries = vec![entry()];
        PackageTheoremPremiseReport {
            schema: PACKAGE_THEOREM_PREMISE_REPORT_SCHEMA.to_owned(),
            package: PackageId::new("premise-test"),
            version: PackageVersion::new("0.1.0"),
            manifest: PackageArtifactFileReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash(9),
            },
            package_lock: PackageArtifactFileReference {
                path: PackagePath::new("generated/package-lock.json"),
                file_hash: hash(10),
            },
            analysis_profile: PACKAGE_THEOREM_PREMISE_REPORT_PROFILE.to_owned(),
            limits: PACKAGE_THEOREM_PREMISE_ANALYSIS_LIMITS_V1,
            summary: package_theorem_premise_summary(&entries),
            entries,
            checker_summaries: vec![],
            report_hash: hash(0),
        }
    }

    #[test]
    fn theorem_premise_report_round_trips_canonically() {
        let report = report().with_computed_hash().unwrap();
        let json = report.canonical_json().unwrap();
        assert_eq!(
            parse_package_theorem_premise_report_json(&json).unwrap(),
            report
        );
        assert!(json.find("\"analysis_profile\"").unwrap() < json.find("\"limits\"").unwrap());
        assert!(json.find("\"proof\"").unwrap() < json.find("\"dependency_basis\"").unwrap());
    }

    #[test]
    fn theorem_premise_report_rejects_limit_drift() {
        let mut report = report();
        report.limits.kernel_whnf_fuel_per_theorem -= 1;
        assert_eq!(
            report.with_computed_hash().unwrap_err().kind,
            crate::PackageArtifactErrorKind::Summary
        );
    }

    #[test]
    fn theorem_premise_classification_keeps_theorem_reason_under_axioms() {
        let mut entry = entry();
        entry.dependency_basis.global_dependencies = vec![PackageTheoremGlobalDependency {
            identity: PackageTheoremGlobalDependencyIdentity::PackageGlobal(
                entry.global_ref.clone(),
            ),
            kind: PackageTheoremGlobalDependencyKind::Theorem,
        }];
        entry.dependency_basis.axiom_dependencies = vec![PackageAxiomReference {
            module: Name::from_dotted("Premise.Axioms"),
            name: Name::from_dotted("choice"),
            export_hash: hash(20),
            decl_interface_hash: hash(21),
        }];
        let classification = package_theorem_premise_classification(
            &entry.telescope,
            &entry.proof,
            &entry.dependency_basis,
        );
        assert_eq!(
            classification.global_basis_class,
            PackageTheoremGlobalBasisClass::AxiomDependent
        );
        assert!(classification
            .reason_codes
            .contains(&PackageTheoremPremiseReason::GlobalBasisUsesVerifiedTheorem));
        assert!(classification
            .reason_codes
            .contains(&PackageTheoremPremiseReason::GlobalBasisUsesTransitiveAxiom));
    }
}
