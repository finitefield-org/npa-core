//! Canonical theorem review inputs and independent sub-agent reports.
//!
//! These artifacts are promotion-policy evidence only. They are never proof
//! evidence and do not replace certificate verification.

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, field_path, hash_json, json_array, json_bool, json_object_in_order,
        json_string, json_u64, parse_artifact_json, reject_unknown_fields, required_array,
        required_bool, required_hash, required_name, required_path, required_string, required_u64,
        validate_artifact_path, validate_declaration_name, validate_module_name,
        validate_package_identity, validate_plain_string, PackageArtifactOrigin,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
    schema::{L2_REVIEW_INPUT_SCHEMA, L2_REVIEW_REPORT_SCHEMA},
};

const INPUT_FIELDS: &[&str] = &["schema", "policy", "source", "input_hash", "proof_evidence"];
const INPUT_POLICY_FIELDS: &[&str] = &[
    "policy_id",
    "policy_version",
    "policy_file_hash",
    "review_protocol",
    "accepted_level",
    "required_roles",
    "required_checks",
];
const INPUT_SOURCE_FIELDS: &[&str] = &[
    "package",
    "version",
    "module",
    "theorem",
    "source_path",
    "source_file_hash",
    "statement_hash",
    "certificate_hash",
    "certificate_file_hash",
    "export_hash",
    "axiom_report_hash",
    "direct_imports",
];
const INPUT_IMPORT_FIELDS: &[&str] = &[
    "module",
    "origin",
    "package",
    "version",
    "export_hash",
    "certificate_hash",
];
const REPORT_FIELDS: &[&str] = &[
    "schema",
    "policy_id",
    "policy_version",
    "policy_file_hash",
    "review_protocol",
    "input_path",
    "input_file_hash",
    "input_hash",
    "authority",
    "authority_version",
    "decision_id",
    "reviewer_role",
    "agent_task",
    "check_results",
    "verdict",
    "rationale",
    "proof_evidence",
];
const CHECK_RESULT_FIELDS: &[&str] = &["check", "decision", "rationale"];

/// Policy identity embedded in one review input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2ReviewInputPolicy {
    /// Stable acceptance policy identity.
    pub policy_id: String,
    /// Exact acceptance policy version.
    pub policy_version: u64,
    /// Exact acceptance policy file hash.
    pub policy_file_hash: PackageHash,
    /// Exact independent review protocol.
    pub review_protocol: String,
    /// Exact accepted theorem level.
    pub accepted_level: String,
    /// Required reviewer roles in policy order.
    pub required_roles: Vec<String>,
    /// Required checks in policy order.
    pub required_checks: Vec<String>,
}

/// One exact direct import identity bound by a review input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2ReviewInputImport {
    /// Imported module.
    pub module: Name,
    /// Local or external package origin.
    pub origin: PackageArtifactOrigin,
    /// Providing package identity.
    pub package: PackageId,
    /// Providing package version.
    pub version: PackageVersion,
    /// Canonical module export hash.
    pub export_hash: PackageHash,
    /// Canonical module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Exact theorem and source-package identity bound by a review input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2ReviewInputSource {
    /// Source package identity.
    pub package: PackageId,
    /// Source package version.
    pub version: PackageVersion,
    /// Source module.
    pub module: Name,
    /// Source theorem declaration.
    pub theorem: Name,
    /// Package-relative source path.
    pub source_path: PackagePath,
    /// Exact source file hash.
    pub source_file_hash: PackageHash,
    /// Certificate-derived statement hash.
    pub statement_hash: PackageHash,
    /// Canonical module certificate hash.
    pub certificate_hash: PackageHash,
    /// Exact certificate file hash.
    pub certificate_file_hash: PackageHash,
    /// Canonical module export hash.
    pub export_hash: PackageHash,
    /// Canonical module axiom report hash.
    pub axiom_report_hash: PackageHash,
    /// Exact direct import identities.
    pub direct_imports: Vec<L2ReviewInputImport>,
}

/// Canonical immutable theorem-specific L2 review input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2ReviewInput {
    /// Schema identifier.
    pub schema: String,
    /// Bound acceptance policy.
    pub policy: L2ReviewInputPolicy,
    /// Bound theorem and package identity.
    pub source: L2ReviewInputSource,
    /// Self hash over canonical bytes without this field.
    pub input_hash: PackageHash,
    /// Always false; this artifact is policy evidence only.
    pub proof_evidence: bool,
}

impl L2ReviewInput {
    /// Normalize direct imports and compute the self hash.
    pub fn with_computed_hash(mut self) -> PackageArtifactResult<Self> {
        normalize_input(&mut self);
        self.input_hash = compute_l2_review_input_v2_hash(&self)?;
        validate_l2_review_input(&self)?;
        Ok(self)
    }

    /// Serialize canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_l2_review_input(self)?;
        let mut normalized = self.clone();
        normalize_input(&mut normalized);
        Ok(format!("{}\n", input_json(&normalized, true)))
    }
}

/// One per-check decision in an independent review report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum L2ReviewCheckDecision {
    /// Check passed.
    Pass,
    /// Check definitively failed.
    Fail,
    /// Check could not be decided.
    Defer,
}

impl L2ReviewCheckDecision {
    /// Stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pass => "pass",
            Self::Fail => "fail",
            Self::Defer => "defer",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "pass" => Ok(Self::Pass),
            "fail" => Ok(Self::Fail),
            "defer" => Ok(Self::Defer),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "decision",
                "pass, fail, or defer",
                value,
            )),
        }
    }
}

/// One required-check result in a review report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2ReviewCheckResult {
    /// Policy check identifier.
    pub check: String,
    /// Reviewer's decision for this check.
    pub decision: L2ReviewCheckDecision,
    /// Concise theorem-specific rationale.
    pub rationale: String,
}

/// Canonical structured output from one independent L2 reviewer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2ReviewReport {
    /// Schema identifier.
    pub schema: String,
    /// Bound policy identity.
    pub policy_id: String,
    /// Bound policy version.
    pub policy_version: u64,
    /// Bound policy file hash.
    pub policy_file_hash: PackageHash,
    /// Exact review protocol.
    pub review_protocol: String,
    /// Package-relative input artifact path.
    pub input_path: PackagePath,
    /// Exact input file hash.
    pub input_file_hash: PackageHash,
    /// Exact review subject hash.
    pub input_hash: PackageHash,
    /// Versioned authority identity.
    pub authority: String,
    /// Authority version.
    pub authority_version: u64,
    /// Immutable authority-scoped decision identifier.
    pub decision_id: String,
    /// Reviewer role.
    pub reviewer_role: String,
    /// Canonical direct sub-agent task name.
    pub agent_task: String,
    /// Required check results in policy order.
    pub check_results: Vec<L2ReviewCheckResult>,
    /// `accepted`, `reject`, or `defer`.
    pub verdict: String,
    /// Concise theorem-specific final rationale.
    pub rationale: String,
    /// Always false; this artifact is policy evidence only.
    pub proof_evidence: bool,
}

impl L2ReviewReport {
    /// Serialize canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_l2_review_report(self)?;
        Ok(format!("{}\n", report_json(self)))
    }
}

/// Parse and validate canonical review-input JSON.
pub fn parse_l2_review_input_json(source: &str) -> PackageArtifactResult<L2ReviewInput> {
    let value = parse_artifact_json(source)?;
    let input = parse_input(&value)?;
    validate_l2_review_input(&input)?;
    if source != input.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "L2 review input JSON bytes",
        ));
    }
    Ok(input)
}

/// Parse and validate canonical review-report JSON.
pub fn parse_l2_review_report_json(source: &str) -> PackageArtifactResult<L2ReviewReport> {
    let value = parse_artifact_json(source)?;
    let report = parse_report(&value)?;
    validate_l2_review_report(&report)?;
    if source != report.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "L2 review report JSON bytes",
        ));
    }
    Ok(report)
}

/// Compute the v2 review-input self hash.
pub fn compute_l2_review_input_v2_hash(
    input: &L2ReviewInput,
) -> PackageArtifactResult<PackageHash> {
    let mut normalized = input.clone();
    normalize_input(&mut normalized);
    validate_input_shape(&normalized)?;
    Ok(package_file_hash(
        format!("{}\n", input_json(&normalized, false)).as_bytes(),
    ))
}

/// Validate a review-input model without filesystem access.
pub fn validate_l2_review_input(input: &L2ReviewInput) -> PackageArtifactResult<()> {
    validate_input_shape(input)?;
    let expected = compute_l2_review_input_v2_hash(input)?;
    if input.input_hash != expected {
        return Err(PackageArtifactError::self_hash_mismatch(
            "input_hash",
            "input_hash",
            crate::format_package_hash(&expected),
            crate::format_package_hash(&input.input_hash),
        ));
    }
    Ok(())
}

/// Validate a review-report model without filesystem access.
pub fn validate_l2_review_report(report: &L2ReviewReport) -> PackageArtifactResult<()> {
    if report.schema != L2_REVIEW_REPORT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_REVIEW_REPORT_SCHEMA,
            &report.schema,
        ));
    }
    for (value, field) in [
        (&report.policy_id, "policy_id"),
        (&report.review_protocol, "review_protocol"),
        (&report.authority, "authority"),
        (&report.decision_id, "decision_id"),
        (&report.reviewer_role, "reviewer_role"),
        (&report.agent_task, "agent_task"),
    ] {
        validate_plain_string(value, field)?;
    }
    if report.policy_version == 0 || report.authority_version == 0 {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "version",
            "positive integer",
            "0",
        ));
    }
    validate_artifact_path(&report.input_path, "input_path")?;
    if report.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    if report.check_results.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            "check_results",
            "check_results",
            "non-empty",
            "empty",
        ));
    }
    let mut seen = std::collections::BTreeSet::new();
    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut defer = 0usize;
    for (index, result) in report.check_results.iter().enumerate() {
        validate_plain_string(&result.check, format!("check_results[{index}].check"))?;
        validate_rationale(
            &result.rationale,
            1024,
            &format!("check_results[{index}].rationale"),
        )?;
        if !seen.insert(result.check.clone()) {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("check_results[{index}].check"),
                "check",
                "unique check",
                &result.check,
            ));
        }
        match result.decision {
            L2ReviewCheckDecision::Pass => pass += 1,
            L2ReviewCheckDecision::Fail => fail += 1,
            L2ReviewCheckDecision::Defer => defer += 1,
        }
    }
    validate_rationale(&report.rationale, 4096, "rationale")?;
    let valid_verdict = match report.verdict.as_str() {
        "accepted" => pass == report.check_results.len(),
        "reject" => fail > 0,
        "defer" => defer > 0 && fail == 0,
        _ => false,
    };
    if !valid_verdict {
        return Err(PackageArtifactError::invalid_enum_value(
            "verdict",
            "verdict",
            "accepted/all-pass, reject/has-fail, or defer/has-defer-no-fail",
            &report.verdict,
        ));
    }
    Ok(())
}

fn validate_input_shape(input: &L2ReviewInput) -> PackageArtifactResult<()> {
    if input.schema != L2_REVIEW_INPUT_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_REVIEW_INPUT_SCHEMA,
            &input.schema,
        ));
    }
    validate_plain_string(&input.policy.policy_id, "policy.policy_id")?;
    validate_plain_string(&input.policy.review_protocol, "policy.review_protocol")?;
    validate_plain_string(&input.policy.accepted_level, "policy.accepted_level")?;
    if input.policy.policy_version == 0 {
        return Err(PackageArtifactError::invalid_enum_value(
            "policy.policy_version",
            "policy_version",
            "positive integer",
            "0",
        ));
    }
    validate_unique_strings(&input.policy.required_roles, "policy.required_roles")?;
    validate_unique_strings(&input.policy.required_checks, "policy.required_checks")?;
    validate_package_identity(&input.source.package, &input.source.version)?;
    validate_module_name(&input.source.module, "source.module")?;
    validate_declaration_name(&input.source.theorem, "source.theorem")?;
    validate_artifact_path(&input.source.source_path, "source.source_path")?;
    for (index, import) in input.source.direct_imports.iter().enumerate() {
        validate_module_name(
            &import.module,
            format!("source.direct_imports[{index}].module"),
        )?;
        validate_package_identity(&import.package, &import.version)?;
    }
    if input.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    Ok(())
}

fn validate_unique_strings(values: &[String], path: &str) -> PackageArtifactResult<()> {
    if values.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            path,
            "non-empty unique list",
            "empty",
        ));
    }
    let mut seen = std::collections::BTreeSet::new();
    for (index, value) in values.iter().enumerate() {
        validate_plain_string(value, format!("{path}[{index}]"))?;
        if !seen.insert(value) {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("{path}[{index}]"),
                path,
                "unique values",
                value,
            ));
        }
    }
    Ok(())
}

fn validate_rationale(value: &str, max: usize, path: &str) -> PackageArtifactResult<()> {
    if value.is_empty() || value.len() > max || value.chars().any(|ch| ch.is_control()) {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "rationale",
            format!("1 through {max} UTF-8 bytes without control characters"),
            value.len().to_string(),
        ));
    }
    Ok(())
}

fn normalize_input(input: &mut L2ReviewInput) {
    input.source.direct_imports.sort_by_key(|import| {
        (
            import.origin.as_str(),
            import.package.as_str().to_owned(),
            import.module.as_dotted(),
            import.version.as_str().to_owned(),
            import.export_hash,
            import.certificate_hash,
        )
    });
}

fn parse_input(value: &JsonValue) -> PackageArtifactResult<L2ReviewInput> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, INPUT_FIELDS)?;
    Ok(L2ReviewInput {
        schema: required_string(members, "$", "schema")?,
        policy: parse_input_policy(required_value(members, "$", "policy")?)?,
        source: parse_input_source(required_value(members, "$", "source")?)?,
        input_hash: required_hash(members, "$", "input_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    })
}

fn parse_input_policy(value: &JsonValue) -> PackageArtifactResult<L2ReviewInputPolicy> {
    let path = "policy";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, INPUT_POLICY_FIELDS)?;
    Ok(L2ReviewInputPolicy {
        policy_id: required_string(members, path, "policy_id")?,
        policy_version: required_u64(members, path, "policy_version")?,
        policy_file_hash: required_hash(members, path, "policy_file_hash")?,
        review_protocol: required_string(members, path, "review_protocol")?,
        accepted_level: required_string(members, path, "accepted_level")?,
        required_roles: string_array(members, path, "required_roles")?,
        required_checks: string_array(members, path, "required_checks")?,
    })
}

fn parse_input_source(value: &JsonValue) -> PackageArtifactResult<L2ReviewInputSource> {
    let path = "source";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, INPUT_SOURCE_FIELDS)?;
    let imports = required_array(members, path, "direct_imports")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_input_import(value, index))
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    Ok(L2ReviewInputSource {
        package: PackageId::new(required_string(members, path, "package")?),
        version: PackageVersion::new(required_string(members, path, "version")?),
        module: required_name(members, path, "module")?,
        theorem: required_name(members, path, "theorem")?,
        source_path: required_path(members, path, "source_path")?,
        source_file_hash: required_hash(members, path, "source_file_hash")?,
        statement_hash: required_hash(members, path, "statement_hash")?,
        certificate_hash: required_hash(members, path, "certificate_hash")?,
        certificate_file_hash: required_hash(members, path, "certificate_file_hash")?,
        export_hash: required_hash(members, path, "export_hash")?,
        axiom_report_hash: required_hash(members, path, "axiom_report_hash")?,
        direct_imports: imports,
    })
}

fn parse_input_import(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<L2ReviewInputImport> {
    let path = format!("source.direct_imports[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, INPUT_IMPORT_FIELDS)?;
    Ok(L2ReviewInputImport {
        module: required_name(members, &path, "module")?,
        origin: parse_origin(&required_string(members, &path, "origin")?, &path)?,
        package: PackageId::new(required_string(members, &path, "package")?),
        version: PackageVersion::new(required_string(members, &path, "version")?),
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
    })
}

fn parse_report(value: &JsonValue) -> PackageArtifactResult<L2ReviewReport> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, REPORT_FIELDS)?;
    let check_results = required_array(members, "$", "check_results")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_check_result(value, index))
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    Ok(L2ReviewReport {
        schema: required_string(members, "$", "schema")?,
        policy_id: required_string(members, "$", "policy_id")?,
        policy_version: required_u64(members, "$", "policy_version")?,
        policy_file_hash: required_hash(members, "$", "policy_file_hash")?,
        review_protocol: required_string(members, "$", "review_protocol")?,
        input_path: required_path(members, "$", "input_path")?,
        input_file_hash: required_hash(members, "$", "input_file_hash")?,
        input_hash: required_hash(members, "$", "input_hash")?,
        authority: required_string(members, "$", "authority")?,
        authority_version: required_u64(members, "$", "authority_version")?,
        decision_id: required_string(members, "$", "decision_id")?,
        reviewer_role: required_string(members, "$", "reviewer_role")?,
        agent_task: required_string(members, "$", "agent_task")?,
        check_results,
        verdict: required_string(members, "$", "verdict")?,
        rationale: required_string(members, "$", "rationale")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    })
}

fn parse_check_result(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<L2ReviewCheckResult> {
    let path = format!("check_results[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, CHECK_RESULT_FIELDS)?;
    let decision = required_string(members, &path, "decision")?;
    Ok(L2ReviewCheckResult {
        check: required_string(members, &path, "check")?,
        decision: L2ReviewCheckDecision::parse(&decision, &field_path(&path, "decision"))?,
        rationale: required_string(members, &path, "rationale")?,
    })
}

fn parse_origin(value: &str, path: &str) -> PackageArtifactResult<PackageArtifactOrigin> {
    match value {
        "local" => Ok(PackageArtifactOrigin::Local),
        "external" => Ok(PackageArtifactOrigin::External),
        _ => Err(PackageArtifactError::invalid_enum_value(
            field_path(path, "origin"),
            "origin",
            "local or external",
            value,
        )),
    }
}

fn string_array(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Vec<String>> {
    required_array(members, path, field)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                PackageArtifactError::invalid_enum_value(
                    format!("{}.{}[{index}]", path, field),
                    field,
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect()
}

fn required_value<'a>(
    members: &'a [crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<&'a JsonValue> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(|member| member.value())
        .ok_or_else(|| PackageArtifactError::missing_field(field_path(path, field), field))
}

fn input_json(input: &L2ReviewInput, include_hash: bool) -> String {
    let mut fields = vec![
        ("schema", json_string(&input.schema)),
        ("policy", input_policy_json(&input.policy)),
        ("source", input_source_json(&input.source)),
    ];
    if include_hash {
        fields.push(("input_hash", hash_json(input.input_hash)));
    }
    fields.push(("proof_evidence", json_bool(input.proof_evidence)));
    json_object_in_order(fields)
}

fn input_policy_json(policy: &L2ReviewInputPolicy) -> String {
    json_object_in_order(vec![
        ("policy_id", json_string(&policy.policy_id)),
        ("policy_version", json_u64(policy.policy_version)),
        ("policy_file_hash", hash_json(policy.policy_file_hash)),
        ("review_protocol", json_string(&policy.review_protocol)),
        ("accepted_level", json_string(&policy.accepted_level)),
        (
            "required_roles",
            json_array(
                policy
                    .required_roles
                    .iter()
                    .map(|v| json_string(v))
                    .collect(),
            ),
        ),
        (
            "required_checks",
            json_array(
                policy
                    .required_checks
                    .iter()
                    .map(|v| json_string(v))
                    .collect(),
            ),
        ),
    ])
}

fn input_source_json(source: &L2ReviewInputSource) -> String {
    json_object_in_order(vec![
        ("package", json_string(source.package.as_str())),
        ("version", json_string(source.version.as_str())),
        ("module", json_string(&source.module.as_dotted())),
        ("theorem", json_string(&source.theorem.as_dotted())),
        ("source_path", json_string(source.source_path.as_str())),
        ("source_file_hash", hash_json(source.source_file_hash)),
        ("statement_hash", hash_json(source.statement_hash)),
        ("certificate_hash", hash_json(source.certificate_hash)),
        (
            "certificate_file_hash",
            hash_json(source.certificate_file_hash),
        ),
        ("export_hash", hash_json(source.export_hash)),
        ("axiom_report_hash", hash_json(source.axiom_report_hash)),
        (
            "direct_imports",
            json_array(
                source
                    .direct_imports
                    .iter()
                    .map(input_import_json)
                    .collect(),
            ),
        ),
    ])
}

fn input_import_json(import: &L2ReviewInputImport) -> String {
    json_object_in_order(vec![
        ("module", json_string(&import.module.as_dotted())),
        ("origin", json_string(import.origin.as_str())),
        ("package", json_string(import.package.as_str())),
        ("version", json_string(import.version.as_str())),
        ("export_hash", hash_json(import.export_hash)),
        ("certificate_hash", hash_json(import.certificate_hash)),
    ])
}

fn report_json(report: &L2ReviewReport) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&report.schema)),
        ("policy_id", json_string(&report.policy_id)),
        ("policy_version", json_u64(report.policy_version)),
        ("policy_file_hash", hash_json(report.policy_file_hash)),
        ("review_protocol", json_string(&report.review_protocol)),
        ("input_path", json_string(report.input_path.as_str())),
        ("input_file_hash", hash_json(report.input_file_hash)),
        ("input_hash", hash_json(report.input_hash)),
        ("authority", json_string(&report.authority)),
        ("authority_version", json_u64(report.authority_version)),
        ("decision_id", json_string(&report.decision_id)),
        ("reviewer_role", json_string(&report.reviewer_role)),
        ("agent_task", json_string(&report.agent_task)),
        (
            "check_results",
            json_array(report.check_results.iter().map(check_result_json).collect()),
        ),
        ("verdict", json_string(&report.verdict)),
        ("rationale", json_string(&report.rationale)),
        ("proof_evidence", json_bool(report.proof_evidence)),
    ])
}

fn check_result_json(result: &L2ReviewCheckResult) -> String {
    json_object_in_order(vec![
        ("check", json_string(&result.check)),
        ("decision", json_string(result.decision.as_str())),
        ("rationale", json_string(&result.rationale)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(byte: u8) -> PackageHash {
        PackageHash([byte; 32])
    }

    fn input() -> L2ReviewInput {
        L2ReviewInput {
            schema: L2_REVIEW_INPUT_SCHEMA.to_owned(),
            policy: L2ReviewInputPolicy {
                policy_id: "policy".to_owned(),
                policy_version: 2,
                policy_file_hash: hash(1),
                review_protocol: "protocol".to_owned(),
                accepted_level: "L2 Derived certificate".to_owned(),
                required_roles: vec!["a".to_owned(), "b".to_owned()],
                required_checks: vec!["check".to_owned()],
            },
            source: L2ReviewInputSource {
                package: PackageId::new("pkg"),
                version: PackageVersion::new("0.1.0"),
                module: Name::from_dotted("Proofs.Ai.Test"),
                theorem: Name::from_dotted("theorem"),
                source_path: PackagePath::new("Proofs/Ai/Test/source.npa"),
                source_file_hash: hash(2),
                statement_hash: hash(3),
                certificate_hash: hash(4),
                certificate_file_hash: hash(5),
                export_hash: hash(6),
                axiom_report_hash: hash(7),
                direct_imports: Vec::new(),
            },
            input_hash: hash(0),
            proof_evidence: false,
        }
        .with_computed_hash()
        .unwrap()
    }

    #[test]
    fn review_input_round_trips_and_binds_source() {
        let input = input();
        let json = input.canonical_json().unwrap();
        assert_eq!(parse_l2_review_input_json(&json).unwrap(), input);
        let mut changed = input.clone();
        changed.source.source_file_hash = hash(9);
        assert_ne!(
            compute_l2_review_input_v2_hash(&changed).unwrap(),
            input.input_hash
        );
    }

    #[test]
    fn report_verdict_matrix_is_strict() {
        let input = input();
        let mut report = L2ReviewReport {
            schema: L2_REVIEW_REPORT_SCHEMA.to_owned(),
            policy_id: input.policy.policy_id.clone(),
            policy_version: 2,
            policy_file_hash: hash(1),
            review_protocol: "protocol".to_owned(),
            input_path: PackagePath::new("l2-reviews/test.input.json"),
            input_file_hash: hash(8),
            input_hash: input.input_hash,
            authority: "authority".to_owned(),
            authority_version: 2,
            decision_id: "decision".to_owned(),
            reviewer_role: "role".to_owned(),
            agent_task: "/root/l2_test".to_owned(),
            check_results: vec![L2ReviewCheckResult {
                check: "check".to_owned(),
                decision: L2ReviewCheckDecision::Pass,
                rationale: "ok".to_owned(),
            }],
            verdict: "accepted".to_owned(),
            rationale: "ok".to_owned(),
            proof_evidence: false,
        };
        let json = report.canonical_json().unwrap();
        assert_eq!(parse_l2_review_report_json(&json).unwrap(), report);
        report.verdict = "defer".to_owned();
        assert!(validate_l2_review_report(&report).is_err());
    }
}
