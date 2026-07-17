//! Repository-governed, hash-bound L2 acceptance metadata.
//!
//! L2 acceptance records authorize a theorem for promotion policy. They are
//! not proof evidence and do not replace canonical certificate verification.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, field_path, hash_json, json_array, json_bool, json_object_in_order,
        json_string, json_u64, parse_artifact_json, reject_unknown_fields, required_array,
        required_bool, required_hash, required_name, required_string, required_u64,
        validate_declaration_name, validate_module_name, validate_package_identity,
        validate_plain_string,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{format_package_hash, package_file_hash, PackageHash},
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    schema::{L2_ACCEPTANCE_POLICY_SCHEMA, L2_ACCEPTANCE_SCHEMA},
};

/// Only theorem level accepted by the mathlib promotion policy.
pub const L2_ACCEPTANCE_LEVEL: &str = "L2 Derived certificate";

/// Validator contract implemented by `npa package validate-l2-acceptance`.
pub const L2_ACCEPTANCE_VALIDATOR_PROFILE: &str = "npa.l2_acceptance.validator.v1";

/// Review protocol implemented by independent L2 approval sub-agents.
pub const L2_ACCEPTANCE_REVIEW_PROTOCOL: &str = "npa.l2.subagent-review.v1";

/// Current report-backed validator contract.
pub const L2_ACCEPTANCE_VALIDATOR_PROFILE_V2: &str = "npa.l2_acceptance.validator.v2";
/// Current structured sub-agent review protocol.
pub const L2_ACCEPTANCE_REVIEW_PROTOCOL_V2: &str = "npa.l2.subagent-review.v2";

const POLICY_FIELDS: &[&str] = &[
    "schema",
    "policy_id",
    "policy_version",
    "governance_mode",
    "validator_profile",
    "review_protocol",
    "accepted_level",
    "required_roles",
    "required_checks",
    "authorities",
    "proof_evidence",
];
const AUTHORITY_FIELDS: &[&str] = &[
    "authority",
    "authority_version",
    "status",
    "reviewer_role",
    "agent_task_prefix",
    "decision_id_prefix",
];
const ACCEPTANCE_FIELDS: &[&str] = &[
    "schema",
    "policy_id",
    "policy_version",
    "policy_file_hash",
    "source_package",
    "source_version",
    "aggregator_agent_task",
    "entries",
    "proof_evidence",
];
const ENTRY_FIELDS: &[&str] = &[
    "module",
    "theorem",
    "statement_hash",
    "certificate_hash",
    "accepted_level",
    "approvals",
];
const APPROVAL_FIELDS: &[&str] = &[
    "authority",
    "authority_version",
    "decision_id",
    "reviewer_role",
    "agent_task",
    "review_protocol",
    "input_hash",
    "checks",
    "verdict",
    "rationale",
];

/// Authority policy consumed by the L2 acceptance validator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptancePolicy {
    /// Schema identifier.
    pub schema: String,
    /// Stable policy identity.
    pub policy_id: String,
    /// Monotonic policy version.
    pub policy_version: u64,
    /// Governance mechanism; version 1 requires independent sub-agent quorum.
    pub governance_mode: String,
    /// Validator contract identifier.
    pub validator_profile: String,
    /// Exact independent sub-agent review protocol.
    pub review_protocol: String,
    /// Exact accepted theorem level.
    pub accepted_level: String,
    /// Distinct sub-agent reviewer roles required for every theorem.
    pub required_roles: Vec<String>,
    /// Review checks every approval must explicitly complete.
    pub required_checks: Vec<String>,
    /// Versioned decision authorities.
    pub authorities: Vec<L2AcceptanceAuthority>,
    /// Must remain false: policy metadata is not proof evidence.
    pub proof_evidence: bool,
}

impl L2AcceptancePolicy {
    /// Serialize this policy as schema-defined canonical JSON with a final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_l2_acceptance_policy(self)?;
        Ok(format!("{}\n", policy_json(self)))
    }
}

/// One versioned authority allowed to issue L2 acceptance decisions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceAuthority {
    /// Stable authority identifier.
    pub authority: String,
    /// Authority rule/version identifier.
    pub authority_version: u64,
    /// Whether this authority version may issue current decisions.
    pub status: L2AcceptanceAuthorityStatus,
    /// Independent review role issued by this authority.
    pub reviewer_role: String,
    /// Required canonical collaboration task-name prefix.
    pub agent_task_prefix: String,
    /// Required prefix for decision identifiers.
    pub decision_id_prefix: String,
}

/// Authority lifecycle state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum L2AcceptanceAuthorityStatus {
    /// Authority version may issue decisions.
    Active,
    /// Authority version is retained for history but cannot issue current decisions.
    Retired,
}

impl L2AcceptanceAuthorityStatus {
    /// Stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Active => "active",
            Self::Retired => "retired",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "active" => Ok(Self::Active),
            "retired" => Ok(Self::Retired),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "status",
                "active or retired",
                value,
            )),
        }
    }
}

/// Hash-bound L2 acceptance document for one source package identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2Acceptance {
    /// Schema identifier.
    pub schema: String,
    /// Policy identity used for the decisions.
    pub policy_id: String,
    /// Exact policy version used for the decisions.
    pub policy_version: u64,
    /// Exact SHA-256 hash of the canonical policy file bytes.
    pub policy_file_hash: PackageHash,
    /// Source package identity.
    pub source_package: PackageId,
    /// Source package version.
    pub source_version: PackageVersion,
    /// Canonical task name of the non-voting promotion aggregator.
    pub aggregator_agent_task: String,
    /// Theorem-level decisions.
    pub entries: Vec<L2AcceptanceEntry>,
    /// Must remain false: acceptance metadata is not proof evidence.
    pub proof_evidence: bool,
}

impl L2Acceptance {
    /// Serialize this acceptance record as canonical JSON with a final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_l2_acceptance(self)?;
        Ok(format!("{}\n", acceptance_json(self)))
    }
}

/// One theorem-level L2 acceptance decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceEntry {
    /// Exact source module.
    pub module: Name,
    /// Exact source theorem declaration.
    pub theorem: Name,
    /// Exact certificate-derived statement core hash.
    pub statement_hash: PackageHash,
    /// Exact canonical module certificate hash.
    pub certificate_hash: PackageHash,
    /// Accepted theorem level; must be [`L2_ACCEPTANCE_LEVEL`].
    pub accepted_level: String,
    /// Independent sub-agent approvals satisfying the policy quorum.
    pub approvals: Vec<L2AcceptanceApproval>,
}

/// One independent sub-agent approval attached to a theorem decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceApproval {
    /// Sub-agent approval authority identifier.
    pub authority: String,
    /// Exact authority version.
    pub authority_version: u64,
    /// Immutable authority-scoped decision identifier.
    pub decision_id: String,
    /// Independent reviewer role.
    pub reviewer_role: String,
    /// Canonical collaboration task name of the issuing sub-agent.
    pub agent_task: String,
    /// Exact review protocol followed by the sub-agent.
    pub review_protocol: String,
    /// Exact hash of the immutable theorem review input packet.
    pub input_hash: PackageHash,
    /// Completed protocol check identifiers.
    pub checks: Vec<String>,
    /// Review verdict; accepted records require `accepted`.
    pub verdict: String,
    /// Non-empty theorem-specific review rationale.
    pub rationale: String,
}

/// Parse and validate a canonical L2 authority policy JSON file.
pub fn parse_l2_acceptance_policy_json(source: &str) -> PackageArtifactResult<L2AcceptancePolicy> {
    let root = parse_artifact_json(source)?;
    let policy = parse_policy(&root)?;
    validate_l2_acceptance_policy(&policy)?;
    if source != policy.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "L2 acceptance policy JSON bytes",
        ));
    }
    Ok(policy)
}

/// Parse and validate a canonical L2 acceptance JSON file.
pub fn parse_l2_acceptance_json(source: &str) -> PackageArtifactResult<L2Acceptance> {
    let root = parse_artifact_json(source)?;
    let acceptance = parse_acceptance(&root)?;
    validate_l2_acceptance(&acceptance)?;
    if source != acceptance.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "L2 acceptance JSON bytes",
        ));
    }
    Ok(acceptance)
}

/// Validate the policy model without reading files.
pub fn validate_l2_acceptance_policy(policy: &L2AcceptancePolicy) -> PackageArtifactResult<()> {
    if policy.schema != L2_ACCEPTANCE_POLICY_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_ACCEPTANCE_POLICY_SCHEMA,
            &policy.schema,
        ));
    }
    validate_plain_string(&policy.policy_id, "policy_id")?;
    if policy.policy_version == 0 || policy.policy_version > 2 {
        return Err(PackageArtifactError::invalid_enum_value(
            "policy_version",
            "policy_version",
            "1 or 2",
            policy.policy_version.to_string(),
        ));
    }
    require_exact(
        &policy.governance_mode,
        "independent-subagent-quorum",
        "governance_mode",
    )?;
    let (validator_profile, review_protocol) = if policy.policy_version == 1 {
        (
            L2_ACCEPTANCE_VALIDATOR_PROFILE,
            L2_ACCEPTANCE_REVIEW_PROTOCOL,
        )
    } else {
        (
            L2_ACCEPTANCE_VALIDATOR_PROFILE_V2,
            L2_ACCEPTANCE_REVIEW_PROTOCOL_V2,
        )
    };
    require_exact(
        &policy.validator_profile,
        validator_profile,
        "validator_profile",
    )?;
    require_exact(&policy.review_protocol, review_protocol, "review_protocol")?;
    require_exact(
        &policy.accepted_level,
        L2_ACCEPTANCE_LEVEL,
        "accepted_level",
    )?;
    if policy.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    if policy.authorities.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            "authorities",
            "authorities",
            "non-empty authority list",
            "empty",
        ));
    }
    if policy.required_roles.len() < 2 {
        return Err(PackageArtifactError::invalid_enum_value(
            "required_roles",
            "required_roles",
            "at least two distinct independent sub-agent roles",
            policy.required_roles.len().to_string(),
        ));
    }
    let mut required_roles = BTreeSet::new();
    for (index, role) in policy.required_roles.iter().enumerate() {
        validate_plain_string(role, format!("required_roles[{index}]"))?;
        if !required_roles.insert(role.clone()) {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("required_roles[{index}]"),
                "required_roles",
                "unique reviewer roles",
                role,
            ));
        }
    }
    if policy.required_checks.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            "required_checks",
            "required_checks",
            "non-empty review check list",
            "empty",
        ));
    }
    let mut required_checks = BTreeSet::new();
    for (index, check) in policy.required_checks.iter().enumerate() {
        validate_plain_string(check, format!("required_checks[{index}]"))?;
        if !required_checks.insert(check.clone()) {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("required_checks[{index}]"),
                "required_checks",
                "unique review checks",
                check,
            ));
        }
    }
    let mut keys = BTreeSet::new();
    let mut active_roles = BTreeSet::new();
    for (index, authority) in policy.authorities.iter().enumerate() {
        let path = format!("authorities[{index}]");
        validate_plain_string(&authority.authority, field_path(&path, "authority"))?;
        validate_plain_string(
            &authority.decision_id_prefix,
            field_path(&path, "decision_id_prefix"),
        )?;
        validate_plain_string(&authority.reviewer_role, field_path(&path, "reviewer_role"))?;
        validate_plain_string(
            &authority.agent_task_prefix,
            field_path(&path, "agent_task_prefix"),
        )?;
        if !authority.agent_task_prefix.starts_with("/root/l2_") {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "agent_task_prefix"),
                "agent_task_prefix",
                "canonical direct sub-agent task prefix beginning /root/l2_",
                &authority.agent_task_prefix,
            ));
        }
        if authority.authority_version == 0 {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "authority_version"),
                "authority_version",
                "positive integer",
                "0",
            ));
        }
        if !keys.insert((authority.authority.clone(), authority.authority_version)) {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "authorities",
                "unique authority/version pair",
                format!("{}@{}", authority.authority, authority.authority_version),
            ));
        }
        if authority.status == L2AcceptanceAuthorityStatus::Active {
            active_roles.insert(authority.reviewer_role.clone());
        }
    }
    for role in required_roles {
        if !active_roles.contains(&role) {
            return Err(PackageArtifactError::invalid_enum_value(
                "authorities",
                "reviewer_role",
                "an active sub-agent authority for every required role",
                role,
            ));
        }
    }
    Ok(())
}

/// Validate the acceptance model without reading policy or package files.
pub fn validate_l2_acceptance(acceptance: &L2Acceptance) -> PackageArtifactResult<()> {
    if acceptance.schema != L2_ACCEPTANCE_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_ACCEPTANCE_SCHEMA,
            &acceptance.schema,
        ));
    }
    validate_plain_string(&acceptance.policy_id, "policy_id")?;
    if acceptance.policy_version == 0 {
        return Err(PackageArtifactError::invalid_enum_value(
            "policy_version",
            "policy_version",
            "positive integer",
            "0",
        ));
    }
    validate_package_identity(&acceptance.source_package, &acceptance.source_version)?;
    validate_plain_string(&acceptance.aggregator_agent_task, "aggregator_agent_task")?;
    if acceptance.aggregator_agent_task != "/root" {
        return Err(PackageArtifactError::invalid_enum_value(
            "aggregator_agent_task",
            "aggregator_agent_task",
            "canonical non-voting promotion aggregator /root",
            &acceptance.aggregator_agent_task,
        ));
    }
    if acceptance.proof_evidence {
        return Err(PackageArtifactError::invalid_enum_value(
            "proof_evidence",
            "proof_evidence",
            "false",
            "true",
        ));
    }
    let mut declarations = BTreeSet::new();
    let mut decisions = BTreeSet::new();
    for (index, entry) in acceptance.entries.iter().enumerate() {
        let path = format!("entries[{index}]");
        validate_module_name(&entry.module, field_path(&path, "module"))?;
        validate_declaration_name(&entry.theorem, field_path(&path, "theorem"))?;
        require_exact(
            &entry.accepted_level,
            L2_ACCEPTANCE_LEVEL,
            &field_path(&path, "accepted_level"),
        )?;
        if entry.approvals.len() < 2 {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "approvals"),
                "approvals",
                "at least two independent sub-agent approvals",
                entry.approvals.len().to_string(),
            ));
        }
        let expected_input_hash = compute_l2_review_input_hash(acceptance, entry);
        let mut roles = BTreeSet::new();
        let mut agent_tasks = BTreeSet::new();
        for (approval_index, approval) in entry.approvals.iter().enumerate() {
            let approval_path = format!("{path}.approvals[{approval_index}]");
            validate_plain_string(&approval.authority, field_path(&approval_path, "authority"))?;
            validate_plain_string(
                &approval.decision_id,
                field_path(&approval_path, "decision_id"),
            )?;
            validate_plain_string(
                &approval.reviewer_role,
                field_path(&approval_path, "reviewer_role"),
            )?;
            validate_plain_string(
                &approval.agent_task,
                field_path(&approval_path, "agent_task"),
            )?;
            validate_plain_string(&approval.rationale, field_path(&approval_path, "rationale"))?;
            if approval.agent_task == acceptance.aggregator_agent_task {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(&approval_path, "agent_task"),
                    "agent_task",
                    "reviewer task distinct from promotion aggregator",
                    &approval.agent_task,
                ));
            }
            if approval.authority_version == 0 {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(&approval_path, "authority_version"),
                    "authority_version",
                    "positive integer",
                    "0",
                ));
            }
            require_exact(
                &approval.review_protocol,
                L2_ACCEPTANCE_REVIEW_PROTOCOL,
                &field_path(&approval_path, "review_protocol"),
            )?;
            require_exact(
                &approval.verdict,
                "accepted",
                &field_path(&approval_path, "verdict"),
            )?;
            if approval.input_hash != expected_input_hash {
                return Err(PackageArtifactError::self_hash_mismatch(
                    field_path(&approval_path, "input_hash"),
                    "input_hash",
                    format_package_hash(&expected_input_hash),
                    format_package_hash(&approval.input_hash),
                ));
            }
            if approval.checks.is_empty() {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(&approval_path, "checks"),
                    "checks",
                    "non-empty completed review checks",
                    "empty",
                ));
            }
            let mut approval_checks = BTreeSet::new();
            for (check_index, check) in approval.checks.iter().enumerate() {
                validate_plain_string(check, format!("{approval_path}.checks[{check_index}]"))?;
                if !approval_checks.insert(check.clone()) {
                    return Err(PackageArtifactError::invalid_enum_value(
                        format!("{approval_path}.checks[{check_index}]"),
                        "checks",
                        "unique completed review checks",
                        check,
                    ));
                }
            }
            if !roles.insert(approval.reviewer_role.clone()) {
                return Err(PackageArtifactError::invalid_enum_value(
                    &approval_path,
                    "reviewer_role",
                    "one approval per independent reviewer role",
                    &approval.reviewer_role,
                ));
            }
            if !agent_tasks.insert(approval.agent_task.clone()) {
                return Err(PackageArtifactError::invalid_enum_value(
                    &approval_path,
                    "agent_task",
                    "distinct sub-agent tasks",
                    &approval.agent_task,
                ));
            }
            if !decisions.insert((approval.authority.clone(), approval.decision_id.clone())) {
                return Err(PackageArtifactError::invalid_enum_value(
                    &approval_path,
                    "decision_id",
                    "unique decision id within authority",
                    &approval.decision_id,
                ));
            }
        }
        if !declarations.insert((entry.module.as_dotted(), entry.theorem.as_dotted())) {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "entries",
                "one decision per module/theorem",
                format!("{}.{}", entry.module.as_dotted(), entry.theorem.as_dotted()),
            ));
        }
    }
    Ok(())
}

/// Compute the immutable review-input hash shared by every approval for an entry.
///
/// The input binds the source package identity, exact theorem identity and
/// hashes, accepted level, and review protocol. It deliberately excludes
/// reviewer output so independent sub-agents receive the same packet.
pub fn compute_l2_review_input_hash(
    acceptance: &L2Acceptance,
    entry: &L2AcceptanceEntry,
) -> PackageHash {
    let mut input = String::new();
    input.push_str("schema:npa.l2.review-input.v1\n");
    input.push_str("source_package:");
    input.push_str(acceptance.source_package.as_str());
    input.push('\n');
    input.push_str("source_version:");
    input.push_str(acceptance.source_version.as_str());
    input.push('\n');
    input.push_str("module:");
    input.push_str(&entry.module.as_dotted());
    input.push('\n');
    input.push_str("theorem:");
    input.push_str(&entry.theorem.as_dotted());
    input.push('\n');
    input.push_str("statement_hash:");
    input.push_str(&format_package_hash(&entry.statement_hash));
    input.push('\n');
    input.push_str("certificate_hash:");
    input.push_str(&format_package_hash(&entry.certificate_hash));
    input.push('\n');
    input.push_str("accepted_level:");
    input.push_str(&entry.accepted_level);
    input.push('\n');
    input.push_str("review_protocol:");
    input.push_str(L2_ACCEPTANCE_REVIEW_PROTOCOL);
    input.push('\n');
    package_file_hash(input.as_bytes())
}

fn require_exact(value: &str, expected: &str, path: &str) -> PackageArtifactResult<()> {
    if value == expected {
        Ok(())
    } else {
        Err(PackageArtifactError::invalid_enum_value(
            path, path, expected, value,
        ))
    }
}

fn parse_policy(value: &JsonValue) -> PackageArtifactResult<L2AcceptancePolicy> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, POLICY_FIELDS)?;
    Ok(L2AcceptancePolicy {
        schema: required_string(members, "$", "schema")?,
        policy_id: required_string(members, "$", "policy_id")?,
        policy_version: required_u64(members, "$", "policy_version")?,
        governance_mode: required_string(members, "$", "governance_mode")?,
        validator_profile: required_string(members, "$", "validator_profile")?,
        review_protocol: required_string(members, "$", "review_protocol")?,
        accepted_level: required_string(members, "$", "accepted_level")?,
        required_roles: parse_string_array(members, "$", "required_roles")?,
        required_checks: parse_string_array(members, "$", "required_checks")?,
        authorities: required_array(members, "$", "authorities")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_authority(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    })
}

fn parse_authority(
    value: &JsonValue,
    index: usize,
) -> PackageArtifactResult<L2AcceptanceAuthority> {
    let path = format!("authorities[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, AUTHORITY_FIELDS)?;
    let status_path = field_path(&path, "status");
    Ok(L2AcceptanceAuthority {
        authority: required_string(members, &path, "authority")?,
        authority_version: required_u64(members, &path, "authority_version")?,
        status: L2AcceptanceAuthorityStatus::parse(
            &required_string(members, &path, "status")?,
            &status_path,
        )?,
        reviewer_role: required_string(members, &path, "reviewer_role")?,
        agent_task_prefix: required_string(members, &path, "agent_task_prefix")?,
        decision_id_prefix: required_string(members, &path, "decision_id_prefix")?,
    })
}

fn parse_acceptance(value: &JsonValue) -> PackageArtifactResult<L2Acceptance> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, ACCEPTANCE_FIELDS)?;
    Ok(L2Acceptance {
        schema: required_string(members, "$", "schema")?,
        policy_id: required_string(members, "$", "policy_id")?,
        policy_version: required_u64(members, "$", "policy_version")?,
        policy_file_hash: required_hash(members, "$", "policy_file_hash")?,
        source_package: PackageId::new(required_string(members, "$", "source_package")?),
        source_version: PackageVersion::new(required_string(members, "$", "source_version")?),
        aggregator_agent_task: required_string(members, "$", "aggregator_agent_task")?,
        entries: required_array(members, "$", "entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_entry(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    })
}

fn parse_entry(value: &JsonValue, index: usize) -> PackageArtifactResult<L2AcceptanceEntry> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ENTRY_FIELDS)?;
    Ok(L2AcceptanceEntry {
        module: required_name(members, &path, "module")?,
        theorem: required_name(members, &path, "theorem")?,
        statement_hash: required_hash(members, &path, "statement_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        accepted_level: required_string(members, &path, "accepted_level")?,
        approvals: required_array(members, &path, "approvals")?
            .iter()
            .enumerate()
            .map(|(approval_index, value)| parse_approval(value, index, approval_index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_approval(
    value: &JsonValue,
    entry_index: usize,
    approval_index: usize,
) -> PackageArtifactResult<L2AcceptanceApproval> {
    let path = format!("entries[{entry_index}].approvals[{approval_index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, APPROVAL_FIELDS)?;
    Ok(L2AcceptanceApproval {
        authority: required_string(members, &path, "authority")?,
        authority_version: required_u64(members, &path, "authority_version")?,
        decision_id: required_string(members, &path, "decision_id")?,
        reviewer_role: required_string(members, &path, "reviewer_role")?,
        agent_task: required_string(members, &path, "agent_task")?,
        review_protocol: required_string(members, &path, "review_protocol")?,
        input_hash: required_hash(members, &path, "input_hash")?,
        checks: parse_string_array(members, &path, "checks")?,
        verdict: required_string(members, &path, "verdict")?,
        rationale: required_string(members, &path, "rationale")?,
    })
}

fn parse_string_array(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Vec<String>> {
    required_array(members, path, field)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}[{index}]"),
                    Some(field.to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .collect()
}

fn policy_json(policy: &L2AcceptancePolicy) -> String {
    let mut authorities = policy.authorities.clone();
    authorities.sort_by_key(|authority| (authority.authority.clone(), authority.authority_version));
    json_object_in_order(vec![
        ("schema", json_string(&policy.schema)),
        ("policy_id", json_string(&policy.policy_id)),
        ("policy_version", json_u64(policy.policy_version)),
        ("governance_mode", json_string(&policy.governance_mode)),
        ("validator_profile", json_string(&policy.validator_profile)),
        ("review_protocol", json_string(&policy.review_protocol)),
        ("accepted_level", json_string(&policy.accepted_level)),
        (
            "required_roles",
            json_array(sorted_strings(&policy.required_roles)),
        ),
        (
            "required_checks",
            json_array(sorted_strings(&policy.required_checks)),
        ),
        (
            "authorities",
            json_array(authorities.iter().map(authority_json).collect()),
        ),
        ("proof_evidence", json_bool(policy.proof_evidence)),
    ])
}

fn authority_json(authority: &L2AcceptanceAuthority) -> String {
    json_object_in_order(vec![
        ("authority", json_string(&authority.authority)),
        ("authority_version", json_u64(authority.authority_version)),
        ("status", json_string(authority.status.as_str())),
        ("reviewer_role", json_string(&authority.reviewer_role)),
        (
            "agent_task_prefix",
            json_string(&authority.agent_task_prefix),
        ),
        (
            "decision_id_prefix",
            json_string(&authority.decision_id_prefix),
        ),
    ])
}

fn acceptance_json(acceptance: &L2Acceptance) -> String {
    let mut entries = acceptance.entries.clone();
    entries.sort_by_key(|entry| (entry.module.as_dotted(), entry.theorem.as_dotted()));
    json_object_in_order(vec![
        ("schema", json_string(&acceptance.schema)),
        ("policy_id", json_string(&acceptance.policy_id)),
        ("policy_version", json_u64(acceptance.policy_version)),
        ("policy_file_hash", hash_json(acceptance.policy_file_hash)),
        (
            "source_package",
            json_string(acceptance.source_package.as_str()),
        ),
        (
            "source_version",
            json_string(acceptance.source_version.as_str()),
        ),
        (
            "aggregator_agent_task",
            json_string(&acceptance.aggregator_agent_task),
        ),
        (
            "entries",
            json_array(entries.iter().map(entry_json).collect()),
        ),
        ("proof_evidence", json_bool(acceptance.proof_evidence)),
    ])
}

fn entry_json(entry: &L2AcceptanceEntry) -> String {
    let mut approvals = entry.approvals.clone();
    approvals.sort_by_key(|approval| {
        (
            approval.reviewer_role.clone(),
            approval.agent_task.clone(),
            approval.decision_id.clone(),
        )
    });
    json_object_in_order(vec![
        ("module", json_string(&entry.module.as_dotted())),
        ("theorem", json_string(&entry.theorem.as_dotted())),
        ("statement_hash", hash_json(entry.statement_hash)),
        ("certificate_hash", hash_json(entry.certificate_hash)),
        ("accepted_level", json_string(&entry.accepted_level)),
        (
            "approvals",
            json_array(approvals.iter().map(approval_json).collect()),
        ),
    ])
}

fn approval_json(approval: &L2AcceptanceApproval) -> String {
    json_object_in_order(vec![
        ("authority", json_string(&approval.authority)),
        ("authority_version", json_u64(approval.authority_version)),
        ("decision_id", json_string(&approval.decision_id)),
        ("reviewer_role", json_string(&approval.reviewer_role)),
        ("agent_task", json_string(&approval.agent_task)),
        ("review_protocol", json_string(&approval.review_protocol)),
        ("input_hash", hash_json(approval.input_hash)),
        ("checks", json_array(sorted_strings(&approval.checks))),
        ("verdict", json_string(&approval.verdict)),
        ("rationale", json_string(&approval.rationale)),
    ])
}

fn sorted_strings(values: &[String]) -> Vec<String> {
    let mut values = values.to_vec();
    values.sort();
    values.iter().map(|value| json_string(value)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_canonical_policy_and_acceptance() {
        let policy = policy();
        let policy_json = policy.canonical_json().unwrap();
        let parsed_policy = parse_l2_acceptance_policy_json(&policy_json).unwrap();
        assert_eq!(parsed_policy.authorities.len(), 2);

        let acceptance = acceptance();
        let acceptance_json = acceptance.canonical_json().unwrap();
        let parsed = parse_l2_acceptance_json(&acceptance_json).unwrap();
        assert_eq!(parsed.entries[0].approvals.len(), 2);
    }

    #[test]
    fn rejects_noncanonical_and_proof_evidence_claims() {
        let noncanonical = r#"{ "schema":"npa.l2_acceptance_policy.v1" }"#;
        assert!(parse_l2_acceptance_policy_json(noncanonical).is_err());

        let mut policy = policy();
        policy.proof_evidence = true;
        assert!(validate_l2_acceptance_policy(&policy).is_err());
    }

    #[test]
    fn rejects_single_reviewer_and_aggregator_self_approval() {
        let mut single = acceptance();
        single.entries[0].approvals.pop();
        assert!(validate_l2_acceptance(&single).is_err());

        let mut self_approval = acceptance();
        self_approval.entries[0].approvals[0].agent_task = "/root".to_owned();
        assert!(validate_l2_acceptance(&self_approval).is_err());

        let mut duplicated = acceptance();
        duplicated.entries[0].approvals[1].agent_task =
            duplicated.entries[0].approvals[0].agent_task.clone();
        assert!(validate_l2_acceptance(&duplicated).is_err());

        let mut tampered = acceptance();
        tampered.entries[0].approvals[0].input_hash = package_file_hash(b"tampered input");
        assert!(validate_l2_acceptance(&tampered).is_err());

        let mut weak_policy = policy();
        weak_policy.required_roles.pop();
        assert!(validate_l2_acceptance_policy(&weak_policy).is_err());
    }

    fn policy() -> L2AcceptancePolicy {
        L2AcceptancePolicy {
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
        }
    }

    fn acceptance() -> L2Acceptance {
        let mut acceptance = L2Acceptance {
            schema: L2_ACCEPTANCE_SCHEMA.to_owned(),
            policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
            policy_version: 1,
            policy_file_hash: package_file_hash(b"policy"),
            source_package: PackageId::new("npa-corpus"),
            source_version: PackageVersion::new("0.1.0"),
            aggregator_agent_task: "/root".to_owned(),
            entries: vec![L2AcceptanceEntry {
                module: Name::from_dotted("Proofs.Logic.Basic"),
                theorem: Name::from_dotted("identity"),
                statement_hash: package_file_hash(b"statement"),
                certificate_hash: package_file_hash(b"certificate"),
                accepted_level: L2_ACCEPTANCE_LEVEL.to_owned(),
                approvals: vec![
                    approval("adversarial-review", "/root/l2_adversarial_basic"),
                    approval("semantic-review", "/root/l2_semantic_basic"),
                ],
            }],
            proof_evidence: false,
        };
        let input_hash = compute_l2_review_input_hash(&acceptance, &acceptance.entries[0]);
        for approval in &mut acceptance.entries[0].approvals {
            approval.input_hash = input_hash;
        }
        acceptance
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
            rationale: format!("independent {role} accepted the exact theorem input"),
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
}
