//! Canonical verified declaration materialization attestation.
//!
//! This artifact binds deterministic verification results but remains
//! source-owned governance metadata rather than proof evidence.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        parse_artifact_json, reject_unknown_fields, required_array, required_bool, required_hash,
        required_name, required_path, required_string, required_u64, required_value,
        validate_declaration_name, validate_package_identity,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::{validate_package_path, PackagePath},
    promotion_plan::PromotionPackageSnapshot,
    promotion_plan_v2::{
        declaration_json, identity_json, mapping_json, parse_declaration, parse_identity,
        parse_mapping, parse_source, parse_target, source_json, target_json,
        validate_declaration_promotion_resource_count,
        validate_declaration_promotion_resource_limits, validate_promotion_plan_v2_declaration,
        validate_promotion_plan_v2_generated_export_ownership, validate_promotion_plan_v2_identity,
        validate_promotion_plan_v2_mapping, validate_promotion_target_snapshot_v2,
        PromotionPlanV2Declaration, PromotionPlanV2DependencyMapping, PromotionPlanV2Identity,
        PromotionTargetSnapshotV2, DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
        DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
        DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS,
    },
    schema::{
        MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA, MATHLIB_PROMOTION_PLAN_V2_SCHEMA,
        MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA,
    },
};

const ATTESTATION_DOMAIN: &[u8] = b"NPA-MATHLIB-VERIFIED-MATERIALIZATION-v1\0";
const FIELDS: &[&str] = &[
    "schema",
    "promotion_id",
    "request",
    "plan",
    "source",
    "target_baseline",
    "target",
    "source_declaration_closure_hash",
    "normalized_closure_hash",
    "materialized_declarations",
    "generated_exports",
    "externalized_dependencies",
    "replay_omissions",
    "checker_verdicts",
    "gate_results",
    "status",
    "attestation_hash",
    "proof_evidence",
];
const REF_FIELDS: &[&str] = &["path", "schema", "file_hash", "identity_hash"];
const TARGET_FIELDS: &[&str] = &[
    "package",
    "version",
    "manifest_file_hash",
    "lock_file_hash",
    "axiom_report_file_hash",
    "theorem_index_file_hash",
    "verified_export_summary_file_hash",
    "publish_plan_file_hash",
    "source_path",
    "source_file_hash",
    "meta_path",
    "meta_file_hash",
    "replay_path",
    "replay_file_hash",
    "certificate_path",
    "certificate_file_hash",
    "certificate_hash",
    "export_hash",
    "axiom_report_hash",
];
const OMISSION_FIELDS: &[&str] = &[
    "source_replay_file_hash",
    "declaration",
    "row_index",
    "reason",
];
const CHECKER_FIELDS: &[&str] = &[
    "side",
    "checker",
    "profile",
    "cache",
    "certificate_hash",
    "export_hash",
    "status",
];
const GATE_FIELDS: &[&str] = &["side", "gate", "status", "identity_hash"];
const REQUIRED_GATE_PAIRS: &[(&str, &str)] = &[
    ("source", "axiom-report-check"),
    ("source", "build-certs-check"),
    ("source", "check-hashes"),
    ("source", "package-check"),
    ("source", "reference-verification"),
    ("source", "theorem-index-check"),
    ("target", "axiom-report-check"),
    ("target", "build-certs-check"),
    ("target", "check-hashes"),
    ("target", "deterministic-rebuild"),
    ("target", "diff-allowlist"),
    ("target", "export-import-inventory"),
    ("target", "export-summary-check"),
    ("target", "normalized-closure-equality"),
    ("target", "package-check"),
    ("target", "publish-plan-check"),
    ("target", "reference-verification"),
    ("target", "theorem-index-check"),
];
const MAX_CHECKER_VERDICTS: usize = 2;
const MAX_GATE_RESULTS: usize = REQUIRED_GATE_PAIRS.len();
// Reuse the dependency-edge ceiling for bounded per-step omission metadata.
const MAX_REPLAY_OMISSIONS: usize = DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES;

/// Stable reason for omitting a replay row whose semantic references cannot be rewritten safely.
pub const PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON: &str =
    "semantic_replay_rewrite_unsupported";

/// Exact request or plan artifact reference.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionAttestationArtifactRef {
    /// Source-root-relative path.
    pub path: PackagePath,
    /// Exact artifact schema.
    pub schema: String,
    /// Exact file bytes hash.
    pub file_hash: PackageHash,
    /// Request file hash or plan self-hash.
    pub identity_hash: PackageHash,
}

/// Complete generated target and selected sidecar identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionMaterializedTarget {
    /// Target package ID.
    pub package: PackageId,
    /// Planned target version.
    pub version: PackageVersion,
    /// Target manifest bytes hash.
    pub manifest_file_hash: PackageHash,
    /// Target lock bytes hash.
    pub lock_file_hash: PackageHash,
    /// Target axiom-report bytes hash.
    pub axiom_report_file_hash: PackageHash,
    /// Target theorem-index bytes hash.
    pub theorem_index_file_hash: PackageHash,
    /// Target export-summary bytes hash.
    pub verified_export_summary_file_hash: PackageHash,
    /// Target publish-plan bytes hash.
    pub publish_plan_file_hash: PackageHash,
    /// Materialized source path.
    pub source_path: PackagePath,
    /// Materialized source bytes hash.
    pub source_file_hash: PackageHash,
    /// Filtered metadata path.
    pub meta_path: PackagePath,
    /// Filtered metadata bytes hash.
    pub meta_file_hash: PackageHash,
    /// Filtered replay path.
    pub replay_path: PackagePath,
    /// Filtered replay bytes hash.
    pub replay_file_hash: PackageHash,
    /// Target certificate path.
    pub certificate_path: PackagePath,
    /// Target certificate bytes hash.
    pub certificate_file_hash: PackageHash,
    /// Canonical target certificate hash.
    pub certificate_hash: PackageHash,
    /// Canonical target export hash.
    pub export_hash: PackageHash,
    /// Canonical target axiom-report hash.
    pub axiom_report_hash: PackageHash,
}

/// One source replay row intentionally omitted from the filtered target replay.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionReplayOmission {
    /// Exact source replay bytes hash.
    pub source_replay_file_hash: PackageHash,
    /// Declaration owning the omitted row.
    pub declaration: Name,
    /// Zero-based source replay row index.
    pub row_index: u64,
    /// Stable omission reason.
    pub reason: String,
}

/// Cache-off source-free checker verdict.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionCheckerVerdict {
    /// `source` or `target`.
    pub side: String,
    /// Checker identity.
    pub checker: String,
    /// Checker profile.
    pub profile: String,
    /// Exactly `off`.
    pub cache: String,
    /// Verified certificate hash.
    pub certificate_hash: PackageHash,
    /// Verified export hash.
    pub export_hash: PackageHash,
    /// Exactly `passed`.
    pub status: String,
}

/// One deterministic package gate result.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PromotionGateResult {
    /// `source` or `target`.
    pub side: String,
    /// Stable gate name.
    pub gate: String,
    /// Exactly `passed`.
    pub status: String,
    /// Hash of deterministic gate inputs/results.
    pub identity_hash: PackageHash,
}

/// Canonical verified materialization attestation v1.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedMaterializationAttestation {
    /// Exact schema.
    pub schema: String,
    /// Stable declaration route ID.
    pub promotion_id: PackageHash,
    /// Exact selection request reference.
    pub request: PromotionAttestationArtifactRef,
    /// Exact plan reference and plan self-hash.
    pub plan: PromotionAttestationArtifactRef,
    /// Exact source package snapshot.
    pub source: PromotionPackageSnapshot,
    /// Exact clean target baseline snapshot.
    pub target_baseline: PromotionTargetSnapshotV2,
    /// Complete temporary target identity.
    pub target: PromotionMaterializedTarget,
    /// Source closure hash from the plan.
    pub source_declaration_closure_hash: PackageHash,
    /// Equal normalized source/target projection hash.
    pub normalized_closure_hash: PackageHash,
    /// Exact materialized declaration rows.
    pub materialized_declarations: Vec<PromotionPlanV2Declaration>,
    /// Exact generated export rows.
    pub generated_exports: Vec<PromotionPlanV2Identity>,
    /// Exact externalized dependency rows.
    pub externalized_dependencies: Vec<PromotionPlanV2DependencyMapping>,
    /// Ordered replay omissions.
    pub replay_omissions: Vec<PromotionReplayOmission>,
    /// Source and target checker verdicts.
    pub checker_verdicts: Vec<PromotionCheckerVerdict>,
    /// Ordered deterministic gate results.
    pub gate_results: Vec<PromotionGateResult>,
    /// Exactly `verified_materialization_accepted`.
    pub status: String,
    /// Domain-separated self-hash.
    pub attestation_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl VerifiedMaterializationAttestation {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_verified_materialization_attestation(self)?;
        Ok(format!("{}\n", attestation_json(self)))
    }

    /// Recompute and store the attestation self-hash.
    pub fn finalize(&mut self) -> PackageArtifactResult<()> {
        self.attestation_hash = verified_materialization_attestation_hash(self)?;
        Ok(())
    }
}

/// Parse and validate strict canonical attestation JSON.
pub fn parse_verified_materialization_attestation_json(
    source: &str,
) -> PackageArtifactResult<VerifiedMaterializationAttestation> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, FIELDS)?;
    let attestation = VerifiedMaterializationAttestation {
        schema: required_string(members, "$", "schema")?,
        promotion_id: required_hash(members, "$", "promotion_id")?,
        request: parse_ref(required_value(members, "$", "request")?, "request")?,
        plan: parse_ref(required_value(members, "$", "plan")?, "plan")?,
        source: parse_source(required_value(members, "$", "source")?, "source")?,
        target_baseline: parse_target(
            required_value(members, "$", "target_baseline")?,
            "target_baseline",
        )?,
        target: parse_materialized_target(required_value(members, "$", "target")?, "target")?,
        source_declaration_closure_hash: required_hash(
            members,
            "$",
            "source_declaration_closure_hash",
        )?,
        normalized_closure_hash: required_hash(members, "$", "normalized_closure_hash")?,
        materialized_declarations: parse_array_bounded(
            members,
            "$",
            "materialized_declarations",
            DECLARATION_PROMOTION_V1_MAX_MATERIALIZED_DECLARATIONS,
            parse_declaration,
        )?,
        generated_exports: parse_array_bounded(
            members,
            "$",
            "generated_exports",
            DECLARATION_PROMOTION_V1_MAX_GENERATED_EXPORTS,
            parse_identity,
        )?,
        externalized_dependencies: parse_array_bounded(
            members,
            "$",
            "externalized_dependencies",
            DECLARATION_PROMOTION_V1_MAX_DEPENDENCY_EDGES,
            parse_mapping,
        )?,
        replay_omissions: parse_array_bounded(
            members,
            "$",
            "replay_omissions",
            MAX_REPLAY_OMISSIONS,
            parse_omission,
        )?,
        checker_verdicts: parse_array_bounded(
            members,
            "$",
            "checker_verdicts",
            MAX_CHECKER_VERDICTS,
            parse_checker,
        )?,
        gate_results: parse_array_bounded(
            members,
            "$",
            "gate_results",
            MAX_GATE_RESULTS,
            parse_gate,
        )?,
        status: required_string(members, "$", "status")?,
        attestation_hash: required_hash(members, "$", "attestation_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_verified_materialization_attestation(&attestation)?;
    if source != attestation.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "verified materialization attestation JSON bytes",
        ));
    }
    Ok(attestation)
}

/// Compute the attestation self-hash with its hash field zeroed.
pub fn verified_materialization_attestation_hash(
    attestation: &VerifiedMaterializationAttestation,
) -> PackageArtifactResult<PackageHash> {
    validate_shape(attestation, false)?;
    let mut copy = attestation.clone();
    copy.attestation_hash = PackageHash::new([0; 32]);
    Ok(domain_hash(
        ATTESTATION_DOMAIN,
        attestation_json(&copy).as_bytes(),
    ))
}

/// Validate all strict attestation identities and the self-hash.
pub fn validate_verified_materialization_attestation(
    attestation: &VerifiedMaterializationAttestation,
) -> PackageArtifactResult<()> {
    validate_shape(attestation, true)
}

fn validate_shape(
    attestation: &VerifiedMaterializationAttestation,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    if attestation.schema != MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA
        || attestation.request.schema != MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA
        || attestation.plan.schema != MATHLIB_PROMOTION_PLAN_V2_SCHEMA
        || attestation.status != "verified_materialization_accepted"
        || attestation.proof_evidence
        || attestation.materialized_declarations.is_empty()
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "fixed_values",
            "verified materialization attestation v1",
            "mismatch",
        ));
    }
    validate_declaration_promotion_resource_limits(
        None,
        None,
        None,
        &attestation.materialized_declarations,
        Some(&attestation.generated_exports),
        &attestation.externalized_dependencies,
        "$",
    )?;
    for reference in [&attestation.request, &attestation.plan] {
        validate_package_path(&reference.path, "artifact_ref.path").map_err(|_| {
            PackageArtifactError::invalid_path("artifact_ref.path", reference.path.as_str())
        })?;
    }
    validate_package_identity(&attestation.source.package, &attestation.source.version)?;
    validate_promotion_target_snapshot_v2(&attestation.target_baseline, "target_baseline")?;
    validate_package_identity(&attestation.target.package, &attestation.target.version)?;
    if attestation.request.file_hash != attestation.request.identity_hash
        || attestation.target.package != attestation.target_baseline.package
        || attestation.target.version != attestation.target_baseline.planned_version
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "target",
            "identity",
            "planned target identity",
            "mismatch",
        ));
    }
    validate_declaration_promotion_resource_count(
        "$",
        "replay_omissions",
        attestation.replay_omissions.len(),
        MAX_REPLAY_OMISSIONS,
    )?;
    validate_declaration_promotion_resource_count(
        "$",
        "checker_verdicts",
        attestation.checker_verdicts.len(),
        MAX_CHECKER_VERDICTS,
    )?;
    validate_declaration_promotion_resource_count(
        "$",
        "gate_results",
        attestation.gate_results.len(),
        MAX_GATE_RESULTS,
    )?;
    for path in [
        &attestation.target.source_path,
        &attestation.target.meta_path,
        &attestation.target.replay_path,
        &attestation.target.certificate_path,
    ] {
        validate_package_path(path, "target.path")
            .map_err(|_| PackageArtifactError::invalid_path("target.path", path.as_str()))?;
    }
    ensure_strict(
        &attestation.materialized_declarations,
        "materialized_declarations",
    )?;
    ensure_strict(&attestation.generated_exports, "generated_exports")?;
    ensure_strict(
        &attestation.externalized_dependencies,
        "externalized_dependencies",
    )?;
    ensure_strict(&attestation.replay_omissions, "replay_omissions")?;
    ensure_strict(&attestation.checker_verdicts, "checker_verdicts")?;
    ensure_strict(&attestation.gate_results, "gate_results")?;
    let mut declaration_names = BTreeSet::new();
    for declaration in &attestation.materialized_declarations {
        validate_promotion_plan_v2_declaration(declaration, "materialized_declarations")?;
        if !declaration_names.insert(declaration.source_name.clone()) {
            return Err(PackageArtifactError::non_canonical(
                "materialized_declarations",
                "unique declaration names",
            ));
        }
    }
    validate_promotion_plan_v2_generated_export_ownership(
        &attestation.materialized_declarations,
        "materialized_declarations",
    )?;
    for identity in &attestation.generated_exports {
        validate_promotion_plan_v2_identity(identity, "generated_exports")?;
    }
    let generated = attestation
        .materialized_declarations
        .iter()
        .flat_map(|row| row.generated_exports.iter().cloned())
        .collect::<BTreeSet<_>>();
    if generated != attestation.generated_exports.iter().cloned().collect() {
        return Err(PackageArtifactError::non_canonical(
            "generated_exports",
            "complete generated export union",
        ));
    }
    for mapping in &attestation.externalized_dependencies {
        validate_promotion_plan_v2_mapping(mapping, "externalized_dependencies")?;
    }
    let mut omission_rows = BTreeSet::new();
    let mut omission_source_hash = None;
    for omission in &attestation.replay_omissions {
        validate_declaration_name(&omission.declaration, "replay_omissions.declaration")?;
        if !declaration_names.contains(&omission.declaration) {
            return Err(PackageArtifactError::invalid_enum_value(
                "replay_omissions.declaration",
                "declaration",
                "one materialized declaration",
                omission.declaration.as_dotted(),
            ));
        }
        if omission.reason != PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON {
            return Err(PackageArtifactError::invalid_enum_value(
                "replay_omissions.reason",
                "reason",
                PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON,
                &omission.reason,
            ));
        }
        if !omission_rows.insert(omission.row_index) {
            return Err(PackageArtifactError::invalid_enum_value(
                "replay_omissions.row_index",
                "row_index",
                "unique source replay row index",
                omission.row_index.to_string(),
            ));
        }
        if omission_source_hash
            .replace(omission.source_replay_file_hash)
            .is_some_and(|expected| expected != omission.source_replay_file_hash)
        {
            return Err(PackageArtifactError::invalid_enum_value(
                "replay_omissions.source_replay_file_hash",
                "source_replay_file_hash",
                "one source replay file hash",
                crate::format_package_hash(&omission.source_replay_file_hash),
            ));
        }
    }
    let sides = attestation
        .checker_verdicts
        .iter()
        .map(|verdict| verdict.side.as_str())
        .collect::<BTreeSet<_>>();
    let gate_pairs = attestation
        .gate_results
        .iter()
        .map(|gate| (gate.side.as_str(), gate.gate.as_str()))
        .collect::<BTreeSet<_>>();
    let required_gate_pairs = REQUIRED_GATE_PAIRS.iter().copied().collect::<BTreeSet<_>>();
    if attestation.checker_verdicts.len() != MAX_CHECKER_VERDICTS
        || sides != BTreeSet::from(["source", "target"])
        || attestation.checker_verdicts.iter().any(|verdict| {
            verdict.checker != "npa-checker-ref"
                || verdict.cache != "off"
                || verdict.status != "passed"
                || verdict.profile != "reference"
        })
        || attestation.gate_results.len() != MAX_GATE_RESULTS
        || gate_pairs != required_gate_pairs
        || attestation.gate_results.iter().any(|gate| {
            gate.status != "passed" || !matches!(gate.side.as_str(), "source" | "target")
        })
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "verification",
            "verdict",
            "source and target cache-off reference verdicts and passed gates",
            "mismatch",
        ));
    }
    let source_checker = attestation
        .checker_verdicts
        .iter()
        .find(|verdict| verdict.side == "source")
        .expect("validated source checker verdict");
    let target_checker = attestation
        .checker_verdicts
        .iter()
        .find(|verdict| verdict.side == "target")
        .expect("validated target checker verdict");
    if target_checker.certificate_hash != attestation.target.certificate_hash
        || target_checker.export_hash != attestation.target.export_hash
        || attestation.gate_results.iter().any(|gate| {
            expected_gate_identity(attestation, source_checker, target_checker, gate)
                .is_none_or(|expected| gate.identity_hash != expected)
        })
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "verification",
            "identity_hash",
            "checker and gate identities bound to attested snapshots",
            "mismatch",
        ));
    }
    if check_hash
        && attestation.attestation_hash != verified_materialization_attestation_hash(attestation)?
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "attestation_hash",
            "attestation_hash",
            "recomputed attestation hash",
            crate::format_package_hash(&attestation.attestation_hash),
        ));
    }
    Ok(())
}

fn expected_gate_identity(
    attestation: &VerifiedMaterializationAttestation,
    source_checker: &PromotionCheckerVerdict,
    target_checker: &PromotionCheckerVerdict,
    gate: &PromotionGateResult,
) -> Option<PackageHash> {
    match (gate.side.as_str(), gate.gate.as_str()) {
        ("source", "package-check") => Some(attestation.source.manifest_file_hash),
        ("source", "check-hashes") => Some(attestation.source.lock_file_hash),
        ("source", "build-certs-check" | "reference-verification") => {
            Some(source_checker.certificate_hash)
        }
        ("source", "axiom-report-check") => Some(attestation.source.axiom_report_file_hash),
        ("source", "theorem-index-check") => Some(attestation.source.theorem_index_file_hash),
        ("target", "package-check") => Some(attestation.target.manifest_file_hash),
        ("target", "check-hashes") => Some(attestation.target.lock_file_hash),
        ("target", "build-certs-check" | "reference-verification") => {
            Some(target_checker.certificate_hash)
        }
        ("target", "axiom-report-check") => Some(attestation.target.axiom_report_file_hash),
        ("target", "theorem-index-check") => Some(attestation.target.theorem_index_file_hash),
        ("target", "export-summary-check") => {
            Some(attestation.target.verified_export_summary_file_hash)
        }
        ("target", "publish-plan-check") => Some(attestation.target.publish_plan_file_hash),
        ("target", "deterministic-rebuild") => Some(attestation.target.source_file_hash),
        ("target", "diff-allowlist") => Some(package_file_hash(
            attestation.target.package.as_str().as_bytes(),
        )),
        ("target", "export-import-inventory") => Some(target_checker.export_hash),
        ("target", "normalized-closure-equality") => Some(attestation.normalized_closure_hash),
        _ => None,
    }
}

fn ensure_strict<T: Ord>(values: &[T], path: &str) -> PackageArtifactResult<()> {
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        Err(PackageArtifactError::non_canonical(path, "strict order"))
    } else {
        Ok(())
    }
}

fn parse_array_bounded<T>(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
    maximum: usize,
    parser: fn(&JsonValue, &str) -> PackageArtifactResult<T>,
) -> PackageArtifactResult<Vec<T>> {
    let values = required_array(members, path, field)?;
    validate_declaration_promotion_resource_count(path, field, values.len(), maximum)?;
    values
        .iter()
        .enumerate()
        .map(|(index, value)| parser(value, &format!("{field}[{index}]")))
        .collect()
}

fn parse_ref(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionAttestationArtifactRef> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, REF_FIELDS)?;
    Ok(PromotionAttestationArtifactRef {
        path: required_path(members, path, "path")?,
        schema: required_string(members, path, "schema")?,
        file_hash: required_hash(members, path, "file_hash")?,
        identity_hash: required_hash(members, path, "identity_hash")?,
    })
}

fn parse_materialized_target(
    value: &JsonValue,
    path: &str,
) -> PackageArtifactResult<PromotionMaterializedTarget> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, TARGET_FIELDS)?;
    Ok(PromotionMaterializedTarget {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        manifest_file_hash: required_hash(members, path, "manifest_file_hash")?,
        lock_file_hash: required_hash(members, path, "lock_file_hash")?,
        axiom_report_file_hash: required_hash(members, path, "axiom_report_file_hash")?,
        theorem_index_file_hash: required_hash(members, path, "theorem_index_file_hash")?,
        verified_export_summary_file_hash: required_hash(
            members,
            path,
            "verified_export_summary_file_hash",
        )?,
        publish_plan_file_hash: required_hash(members, path, "publish_plan_file_hash")?,
        source_path: required_path(members, path, "source_path")?,
        source_file_hash: required_hash(members, path, "source_file_hash")?,
        meta_path: required_path(members, path, "meta_path")?,
        meta_file_hash: required_hash(members, path, "meta_file_hash")?,
        replay_path: required_path(members, path, "replay_path")?,
        replay_file_hash: required_hash(members, path, "replay_file_hash")?,
        certificate_path: required_path(members, path, "certificate_path")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
    })
}

fn parse_omission(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionReplayOmission> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, OMISSION_FIELDS)?;
    Ok(PromotionReplayOmission {
        source_replay_file_hash: required_hash(members, path, "source_replay_file_hash")?,
        declaration: required_name(members, path, "declaration")?,
        row_index: required_u64(members, path, "row_index")?,
        reason: required_string(members, path, "reason")?,
    })
}

fn parse_checker(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionCheckerVerdict> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, CHECKER_FIELDS)?;
    Ok(PromotionCheckerVerdict {
        side: required_string(members, path, "side")?,
        checker: required_string(members, path, "checker")?,
        profile: required_string(members, path, "profile")?,
        cache: required_string(members, path, "cache")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        status: required_string(members, path, "status")?,
    })
}

fn parse_gate(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionGateResult> {
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, GATE_FIELDS)?;
    Ok(PromotionGateResult {
        side: required_string(members, path, "side")?,
        gate: required_string(members, path, "gate")?,
        status: required_string(members, path, "status")?,
        identity_hash: required_hash(members, path, "identity_hash")?,
    })
}

fn attestation_json(value: &VerifiedMaterializationAttestation) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&value.schema)),
        ("promotion_id", hash_json(value.promotion_id)),
        ("request", ref_json(&value.request)),
        ("plan", ref_json(&value.plan)),
        ("source", source_json(&value.source)),
        ("target_baseline", target_json(&value.target_baseline)),
        ("target", materialized_target_json(&value.target)),
        (
            "source_declaration_closure_hash",
            hash_json(value.source_declaration_closure_hash),
        ),
        (
            "normalized_closure_hash",
            hash_json(value.normalized_closure_hash),
        ),
        (
            "materialized_declarations",
            json_array(
                value
                    .materialized_declarations
                    .iter()
                    .map(declaration_json)
                    .collect(),
            ),
        ),
        (
            "generated_exports",
            json_array(value.generated_exports.iter().map(identity_json).collect()),
        ),
        (
            "externalized_dependencies",
            json_array(
                value
                    .externalized_dependencies
                    .iter()
                    .map(mapping_json)
                    .collect(),
            ),
        ),
        (
            "replay_omissions",
            json_array(value.replay_omissions.iter().map(omission_json).collect()),
        ),
        (
            "checker_verdicts",
            json_array(value.checker_verdicts.iter().map(checker_json).collect()),
        ),
        (
            "gate_results",
            json_array(value.gate_results.iter().map(gate_json).collect()),
        ),
        ("status", json_string(&value.status)),
        ("attestation_hash", hash_json(value.attestation_hash)),
        ("proof_evidence", json_bool(value.proof_evidence)),
    ])
}

fn ref_json(value: &PromotionAttestationArtifactRef) -> String {
    json_object_in_order(vec![
        ("path", json_string(value.path.as_str())),
        ("schema", json_string(&value.schema)),
        ("file_hash", hash_json(value.file_hash)),
        ("identity_hash", hash_json(value.identity_hash)),
    ])
}

fn materialized_target_json(value: &PromotionMaterializedTarget) -> String {
    json_object_in_order(vec![
        ("package", json_string(value.package.as_str())),
        ("version", json_string(value.version.as_str())),
        ("manifest_file_hash", hash_json(value.manifest_file_hash)),
        ("lock_file_hash", hash_json(value.lock_file_hash)),
        (
            "axiom_report_file_hash",
            hash_json(value.axiom_report_file_hash),
        ),
        (
            "theorem_index_file_hash",
            hash_json(value.theorem_index_file_hash),
        ),
        (
            "verified_export_summary_file_hash",
            hash_json(value.verified_export_summary_file_hash),
        ),
        (
            "publish_plan_file_hash",
            hash_json(value.publish_plan_file_hash),
        ),
        ("source_path", json_string(value.source_path.as_str())),
        ("source_file_hash", hash_json(value.source_file_hash)),
        ("meta_path", json_string(value.meta_path.as_str())),
        ("meta_file_hash", hash_json(value.meta_file_hash)),
        ("replay_path", json_string(value.replay_path.as_str())),
        ("replay_file_hash", hash_json(value.replay_file_hash)),
        (
            "certificate_path",
            json_string(value.certificate_path.as_str()),
        ),
        (
            "certificate_file_hash",
            hash_json(value.certificate_file_hash),
        ),
        ("certificate_hash", hash_json(value.certificate_hash)),
        ("export_hash", hash_json(value.export_hash)),
        ("axiom_report_hash", hash_json(value.axiom_report_hash)),
    ])
}

fn omission_json(value: &PromotionReplayOmission) -> String {
    json_object_in_order(vec![
        (
            "source_replay_file_hash",
            hash_json(value.source_replay_file_hash),
        ),
        ("declaration", json_string(&value.declaration.as_dotted())),
        ("row_index", value.row_index.to_string()),
        ("reason", json_string(&value.reason)),
    ])
}

fn checker_json(value: &PromotionCheckerVerdict) -> String {
    json_object_in_order(vec![
        ("side", json_string(&value.side)),
        ("checker", json_string(&value.checker)),
        ("profile", json_string(&value.profile)),
        ("cache", json_string(&value.cache)),
        ("certificate_hash", hash_json(value.certificate_hash)),
        ("export_hash", hash_json(value.export_hash)),
        ("status", json_string(&value.status)),
    ])
}

fn gate_json(value: &PromotionGateResult) -> String {
    json_object_in_order(vec![
        ("side", json_string(&value.side)),
        ("gate", json_string(&value.gate)),
        ("status", json_string(&value.status)),
        ("identity_hash", hash_json(value.identity_hash)),
    ])
}

fn domain_hash(domain: &[u8], bytes: &[u8]) -> PackageHash {
    let mut input = Vec::with_capacity(domain.len() + bytes.len());
    input.extend_from_slice(domain);
    input.extend_from_slice(bytes);
    package_file_hash(&input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PackageId, PackageVersion, PromotionSourceSpan};

    fn hash(byte: u8) -> PackageHash {
        PackageHash::new([byte; 32])
    }

    fn attestation() -> VerifiedMaterializationAttestation {
        let declaration = PromotionPlanV2Declaration {
            role: "root".to_owned(),
            source_name: Name::from_dotted("selected"),
            target_name: Name::from_dotted("selected"),
            certificate_kind: "theorem".to_owned(),
            human_kind: "theorem".to_owned(),
            source_decl_index: 1,
            decl_interface_hash: hash(1),
            decl_certificate_hash: hash(2),
            type_hash: hash(3),
            body_hash: None,
            item_span: PromotionSourceSpan { start: 1, end: 8 },
            family_owner: Name::from_dotted("selected"),
            family_members: vec![Name::from_dotted("selected")],
            generated_exports: Vec::new(),
            direct_dependencies: Vec::new(),
        };
        let source = PromotionPackageSnapshot {
            package: PackageId::new("npa-project-fixture"),
            version: PackageVersion::new("0.1.0"),
            manifest_file_hash: hash(4),
            lock_file_hash: hash(5),
            axiom_report_file_hash: hash(6),
            theorem_index_file_hash: hash(7),
        };
        let baseline = PromotionTargetSnapshotV2 {
            package: PackageId::new("npa-mathlib"),
            version: PackageVersion::new("0.2.0"),
            planned_version: PackageVersion::new("0.2.1"),
            manifest_file_hash: hash(8),
            lock_file_hash: hash(9),
            axiom_report_file_hash: hash(10),
            theorem_index_file_hash: hash(11),
            verified_export_summary_file_hash: hash(12),
            publish_plan_file_hash: hash(13),
            registry_file_hash: hash(14),
        };
        let mut value = VerifiedMaterializationAttestation {
            schema: MATHLIB_VERIFIED_MATERIALIZATION_ATTESTATION_SCHEMA.to_owned(),
            promotion_id: hash(15),
            request: PromotionAttestationArtifactRef {
                path: PackagePath::new("promotion/selection.json"),
                schema: MATHLIB_DECLARATION_PROMOTION_REQUEST_SCHEMA.to_owned(),
                file_hash: hash(16),
                identity_hash: hash(16),
            },
            plan: PromotionAttestationArtifactRef {
                path: PackagePath::new("promotion/plan.json"),
                schema: MATHLIB_PROMOTION_PLAN_V2_SCHEMA.to_owned(),
                file_hash: hash(17),
                identity_hash: hash(18),
            },
            source,
            target_baseline: baseline,
            target: PromotionMaterializedTarget {
                package: PackageId::new("npa-mathlib"),
                version: PackageVersion::new("0.2.1"),
                manifest_file_hash: hash(19),
                lock_file_hash: hash(20),
                axiom_report_file_hash: hash(21),
                theorem_index_file_hash: hash(22),
                verified_export_summary_file_hash: hash(23),
                publish_plan_file_hash: hash(24),
                source_path: PackagePath::new("Mathlib/Selected/source.npa"),
                source_file_hash: hash(25),
                meta_path: PackagePath::new("Mathlib/Selected/meta.json"),
                meta_file_hash: hash(26),
                replay_path: PackagePath::new("Mathlib/Selected/replay.json"),
                replay_file_hash: hash(27),
                certificate_path: PackagePath::new("Mathlib/Selected/certificate.npcert"),
                certificate_file_hash: hash(28),
                certificate_hash: hash(29),
                export_hash: hash(30),
                axiom_report_hash: hash(31),
            },
            source_declaration_closure_hash: hash(32),
            normalized_closure_hash: hash(33),
            materialized_declarations: vec![declaration],
            generated_exports: Vec::new(),
            externalized_dependencies: Vec::new(),
            replay_omissions: Vec::new(),
            checker_verdicts: vec![
                PromotionCheckerVerdict {
                    side: "source".to_owned(),
                    checker: "npa-checker-ref".to_owned(),
                    profile: "reference".to_owned(),
                    cache: "off".to_owned(),
                    certificate_hash: hash(34),
                    export_hash: hash(35),
                    status: "passed".to_owned(),
                },
                PromotionCheckerVerdict {
                    side: "target".to_owned(),
                    checker: "npa-checker-ref".to_owned(),
                    profile: "reference".to_owned(),
                    cache: "off".to_owned(),
                    certificate_hash: hash(29),
                    export_hash: hash(30),
                    status: "passed".to_owned(),
                },
            ],
            gate_results: REQUIRED_GATE_PAIRS
                .iter()
                .enumerate()
                .map(|(index, (side, gate))| PromotionGateResult {
                    side: (*side).to_owned(),
                    gate: (*gate).to_owned(),
                    status: "passed".to_owned(),
                    identity_hash: hash(38 + index as u8),
                })
                .collect(),
            status: "verified_materialization_accepted".to_owned(),
            attestation_hash: hash(0),
            proof_evidence: false,
        };
        let identity_source = value.clone();
        let source_checker = &identity_source.checker_verdicts[0];
        let target_checker = &identity_source.checker_verdicts[1];
        for gate in &mut value.gate_results {
            gate.identity_hash =
                expected_gate_identity(&identity_source, source_checker, target_checker, gate)
                    .expect("every required gate has an attested identity");
        }
        value.gate_results.sort();
        value.finalize().unwrap();
        value
    }

    #[test]
    fn attestation_round_trips_and_detects_self_hash_tampering() {
        let expected = attestation();
        let json = expected.canonical_json().unwrap();
        assert_eq!(
            parse_verified_materialization_attestation_json(&json).unwrap(),
            expected
        );
        let mut tampered = expected;
        tampered.normalized_closure_hash = hash(99);
        assert!(tampered.canonical_json().is_err());
        assert!(parse_verified_materialization_attestation_json(&format!(" {json}")).is_err());
    }

    #[test]
    fn attestation_bounds_auxiliary_arrays_before_typed_conversion() {
        let mut expected = attestation();
        expected.replay_omissions.push(PromotionReplayOmission {
            source_replay_file_hash: hash(90),
            declaration: Name::from_dotted("selected"),
            row_index: 0,
            reason: PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON.to_owned(),
        });
        expected.finalize().unwrap();
        let value = parse_artifact_json(&expected.canonical_json().unwrap()).unwrap();
        let members = expect_object(&value, "$").unwrap();

        let omission_error =
            parse_array_bounded(members, "$", "replay_omissions", 0, parse_omission).unwrap_err();
        assert_eq!(omission_error.field.as_deref(), Some("replay_omissions"));
        let checker_error =
            parse_array_bounded(members, "$", "checker_verdicts", 1, parse_checker).unwrap_err();
        assert_eq!(checker_error.field.as_deref(), Some("checker_verdicts"));
        let gate_error = parse_array_bounded(
            members,
            "$",
            "gate_results",
            MAX_GATE_RESULTS - 1,
            parse_gate,
        )
        .unwrap_err();
        assert_eq!(gate_error.field.as_deref(), Some("gate_results"));
    }

    #[test]
    fn replay_omissions_are_closure_owned_unique_and_stable() {
        let omission = PromotionReplayOmission {
            source_replay_file_hash: hash(90),
            declaration: Name::from_dotted("selected"),
            row_index: 0,
            reason: PROMOTION_REPLAY_OMISSION_UNSUPPORTED_REWRITE_REASON.to_owned(),
        };
        let mut valid = attestation();
        valid.replay_omissions.push(omission.clone());
        valid.finalize().unwrap();

        let mut outside_closure = attestation();
        outside_closure
            .replay_omissions
            .push(PromotionReplayOmission {
                declaration: Name::from_dotted("unselected"),
                ..omission.clone()
            });
        let error = outside_closure.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("declaration"));

        let mut unstable_reason = attestation();
        unstable_reason
            .replay_omissions
            .push(PromotionReplayOmission {
                reason: "invented_reason".to_owned(),
                ..omission.clone()
            });
        let error = unstable_reason.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("reason"));

        let mut duplicate_row = attestation();
        duplicate_row.replay_omissions = vec![
            omission.clone(),
            PromotionReplayOmission {
                source_replay_file_hash: hash(91),
                ..omission.clone()
            },
        ];
        duplicate_row.replay_omissions.sort();
        let error = duplicate_row.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("row_index"));

        let mut mixed_source = attestation();
        mixed_source.replay_omissions = vec![
            omission.clone(),
            PromotionReplayOmission {
                source_replay_file_hash: hash(91),
                row_index: 1,
                ..omission
            },
        ];
        mixed_source.replay_omissions.sort();
        let error = mixed_source.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("source_replay_file_hash"));
    }

    #[test]
    fn attestation_resource_limits_precede_verification_array_walks() {
        let mut checker = attestation();
        checker
            .checker_verdicts
            .push(checker.checker_verdicts[0].clone());
        let error = checker.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("checker_verdicts"));

        let mut gate = attestation();
        gate.gate_results.push(gate.gate_results[0].clone());
        let error = gate.finalize().unwrap_err();
        assert_eq!(error.field.as_deref(), Some("gate_results"));
    }

    #[test]
    fn attestation_rejects_invalid_embedded_declaration_rows() {
        let mut value = attestation();
        value.materialized_declarations[0].human_kind = "lemma".to_owned();
        assert!(value.finalize().is_err());
    }

    #[test]
    fn attestation_rejects_ambiguous_generated_export_ownership() {
        let mut value = attestation();
        let generated = PromotionPlanV2Identity {
            module: Name::from_dotted("Proofs.Source"),
            name: Name::from_dotted("generated"),
            kind: "constructor".to_owned(),
            decl_interface_hash: hash(99),
        };
        let family_members = vec![
            generated.name.clone(),
            Name::from_dotted("selected"),
            Name::from_dotted("support"),
        ];
        value.materialized_declarations[0]
            .family_members
            .clone_from(&family_members);
        value.materialized_declarations[0].generated_exports = vec![generated.clone()];
        let mut second_owner = value.materialized_declarations[0].clone();
        second_owner.source_name = Name::from_dotted("support");
        second_owner.target_name = second_owner.source_name.clone();
        second_owner.source_decl_index = 2;
        value.materialized_declarations.push(second_owner);
        value.materialized_declarations.sort();
        value.generated_exports = vec![generated];

        let error = value.finalize().unwrap_err();
        assert_eq!(
            error.actual_value.as_deref(),
            Some("one declaration owner per generated export")
        );
    }

    #[test]
    fn attestation_rejects_unbound_snapshot_and_verification_identities() {
        let mut target_version = attestation();
        target_version.target_baseline.planned_version = PackageVersion::new("0.1.9");
        target_version.target.version = PackageVersion::new("0.1.9");
        assert!(target_version.finalize().is_err());

        let mut request_identity = attestation();
        request_identity.request.identity_hash = hash(99);
        assert!(request_identity.finalize().is_err());

        let mut checker = attestation();
        checker.checker_verdicts[1].certificate_hash = hash(99);
        checker.checker_verdicts.sort();
        assert!(checker.finalize().is_err());

        let mut gate = attestation();
        gate.gate_results
            .iter_mut()
            .find(|row| row.gate == "package-check" && row.side == "target")
            .unwrap()
            .identity_hash = hash(99);
        gate.gate_results.sort();
        assert!(gate.finalize().is_err());
    }
}
