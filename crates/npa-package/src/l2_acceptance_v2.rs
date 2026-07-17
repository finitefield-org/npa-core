//! Current report-backed L2 acceptance ledger.

use std::collections::BTreeSet;

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, field_path, hash_json, json_array, json_bool, json_object_in_order,
        json_string, json_u64, parse_artifact_json, reject_unknown_fields, required_array,
        required_bool, required_hash, required_name, required_path, required_string, required_u64,
        validate_artifact_path, validate_declaration_name, validate_module_name,
        validate_package_identity, validate_plain_string,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::PackageHash,
    json::JsonValue,
    manifest::PackageVersion,
    name::PackageId,
    path::PackagePath,
    schema::L2_ACCEPTANCE_V2_SCHEMA,
};

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
    "review_report",
    "verdict",
];
const REPORT_REF_FIELDS: &[&str] = &["path", "file_hash"];

/// Exact immutable review-report reference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceReviewReportRef {
    /// Package-relative report path.
    pub path: PackagePath,
    /// Exact report file hash.
    pub file_hash: PackageHash,
}

/// One projected accepted review decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceApprovalV2 {
    /// Versioned process authority.
    pub authority: String,
    /// Authority version.
    pub authority_version: u64,
    /// Immutable authority-scoped decision identifier.
    pub decision_id: String,
    /// Required reviewer role.
    pub reviewer_role: String,
    /// Canonical reviewer task name.
    pub agent_task: String,
    /// Exact review protocol.
    pub review_protocol: String,
    /// Exact review subject hash.
    pub input_hash: PackageHash,
    /// Exact immutable report reference.
    pub review_report: L2AcceptanceReviewReportRef,
    /// Always `accepted` in an acceptance ledger.
    pub verdict: String,
}

/// One theorem-level current L2 acceptance entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceEntryV2 {
    /// Source module.
    pub module: Name,
    /// Source theorem declaration.
    pub theorem: Name,
    /// Certificate-derived statement hash.
    pub statement_hash: PackageHash,
    /// Canonical module certificate hash.
    pub certificate_hash: PackageHash,
    /// Exact accepted level.
    pub accepted_level: String,
    /// Independent accepted approvals.
    pub approvals: Vec<L2AcceptanceApprovalV2>,
}

/// Current report-backed L2 acceptance ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L2AcceptanceV2 {
    /// Schema identifier.
    pub schema: String,
    /// Acceptance policy identity.
    pub policy_id: String,
    /// Acceptance policy version.
    pub policy_version: u64,
    /// Exact policy file hash.
    pub policy_file_hash: PackageHash,
    /// Source package identity.
    pub source_package: PackageId,
    /// Source package version.
    pub source_version: PackageVersion,
    /// Non-voting aggregator task.
    pub aggregator_agent_task: String,
    /// Theorem entries.
    pub entries: Vec<L2AcceptanceEntryV2>,
    /// Always false; this is policy evidence only.
    pub proof_evidence: bool,
}

impl L2AcceptanceV2 {
    /// Normalize entries and approvals for deterministic serialization.
    pub fn normalized(mut self) -> Self {
        normalize_acceptance(&mut self);
        self
    }

    /// Serialize canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_l2_acceptance_v2(self)?;
        let mut normalized = self.clone();
        normalize_acceptance(&mut normalized);
        Ok(format!("{}\n", acceptance_json(&normalized)))
    }
}

/// Parse and validate a canonical v2 L2 acceptance ledger.
pub fn parse_l2_acceptance_v2_json(source: &str) -> PackageArtifactResult<L2AcceptanceV2> {
    let root = parse_artifact_json(source)?;
    let acceptance = parse_acceptance(&root)?;
    validate_l2_acceptance_v2(&acceptance)?;
    if source != acceptance.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "L2 acceptance v2 JSON bytes",
        ));
    }
    Ok(acceptance)
}

/// Validate a v2 acceptance model without filesystem or policy access.
pub fn validate_l2_acceptance_v2(acceptance: &L2AcceptanceV2) -> PackageArtifactResult<()> {
    if acceptance.schema != L2_ACCEPTANCE_V2_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            L2_ACCEPTANCE_V2_SCHEMA,
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
    if acceptance.aggregator_agent_task != "/root" {
        return Err(PackageArtifactError::invalid_enum_value(
            "aggregator_agent_task",
            "aggregator_agent_task",
            "/root",
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
    let mut theorem_keys = BTreeSet::new();
    let mut decisions = BTreeSet::new();
    for (entry_index, entry) in acceptance.entries.iter().enumerate() {
        let path = format!("entries[{entry_index}]");
        validate_module_name(&entry.module, field_path(&path, "module"))?;
        validate_declaration_name(&entry.theorem, field_path(&path, "theorem"))?;
        validate_plain_string(&entry.accepted_level, field_path(&path, "accepted_level"))?;
        if entry.approvals.len() < 2 {
            return Err(PackageArtifactError::invalid_enum_value(
                field_path(&path, "approvals"),
                "approvals",
                "at least two",
                entry.approvals.len().to_string(),
            ));
        }
        if !theorem_keys.insert((entry.module.as_dotted(), entry.theorem.as_dotted())) {
            return Err(PackageArtifactError::invalid_enum_value(
                &path,
                "entries",
                "unique module/theorem",
                entry.theorem.as_dotted(),
            ));
        }
        let mut roles = BTreeSet::new();
        let mut tasks = BTreeSet::new();
        for (approval_index, approval) in entry.approvals.iter().enumerate() {
            let approval_path = format!("{path}.approvals[{approval_index}]");
            for (value, field) in [
                (&approval.authority, "authority"),
                (&approval.decision_id, "decision_id"),
                (&approval.reviewer_role, "reviewer_role"),
                (&approval.agent_task, "agent_task"),
                (&approval.review_protocol, "review_protocol"),
            ] {
                validate_plain_string(value, field_path(&approval_path, field))?;
            }
            if approval.authority_version == 0 || approval.verdict != "accepted" {
                return Err(PackageArtifactError::invalid_enum_value(
                    &approval_path,
                    "approval",
                    "positive authority version and accepted verdict",
                    &approval.verdict,
                ));
            }
            if approval.agent_task == acceptance.aggregator_agent_task {
                return Err(PackageArtifactError::invalid_enum_value(
                    field_path(&approval_path, "agent_task"),
                    "agent_task",
                    "reviewer distinct from aggregator",
                    &approval.agent_task,
                ));
            }
            validate_artifact_path(
                &approval.review_report.path,
                field_path(&approval_path, "review_report.path"),
            )?;
            if !roles.insert(approval.reviewer_role.clone())
                || !tasks.insert(approval.agent_task.clone())
                || !decisions.insert((approval.authority.clone(), approval.decision_id.clone()))
            {
                return Err(PackageArtifactError::invalid_enum_value(
                    &approval_path,
                    "approval",
                    "unique role, task, and authority decision",
                    &approval.decision_id,
                ));
            }
        }
    }
    Ok(())
}

/// Merge new entries into an existing ledger with explicit replacement keys.
pub fn merge_l2_acceptance_v2_entries(
    mut base: L2AcceptanceV2,
    entries: Vec<L2AcceptanceEntryV2>,
    replacements: &BTreeSet<(Name, Name)>,
) -> PackageArtifactResult<L2AcceptanceV2> {
    for entry in entries {
        let key = (entry.module.clone(), entry.theorem.clone());
        if let Some(index) = base
            .entries
            .iter()
            .position(|old| old.module == entry.module && old.theorem == entry.theorem)
        {
            if !replacements.contains(&key) {
                return Err(PackageArtifactError::invalid_enum_value(
                    "entries",
                    "replacement",
                    "explicit replacement selector",
                    format!("{}::{}", key.0.as_dotted(), key.1.as_dotted()),
                ));
            }
            base.entries[index] = entry;
        } else {
            if replacements.contains(&key) {
                return Err(PackageArtifactError::invalid_enum_value(
                    "entries",
                    "replacement",
                    "selector matching existing theorem",
                    format!("{}::{}", key.0.as_dotted(), key.1.as_dotted()),
                ));
            }
            base.entries.push(entry);
        }
    }
    normalize_acceptance(&mut base);
    validate_l2_acceptance_v2(&base)?;
    Ok(base)
}

fn normalize_acceptance(acceptance: &mut L2AcceptanceV2) {
    acceptance
        .entries
        .sort_by_key(|entry| (entry.module.as_dotted(), entry.theorem.as_dotted()));
    for entry in &mut acceptance.entries {
        entry.approvals.sort_by_key(|approval| {
            (
                approval.reviewer_role.clone(),
                approval.agent_task.clone(),
                approval.authority.clone(),
                approval.decision_id.clone(),
            )
        });
    }
}

fn parse_acceptance(value: &JsonValue) -> PackageArtifactResult<L2AcceptanceV2> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, ACCEPTANCE_FIELDS)?;
    Ok(L2AcceptanceV2 {
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

fn parse_entry(value: &JsonValue, index: usize) -> PackageArtifactResult<L2AcceptanceEntryV2> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ENTRY_FIELDS)?;
    Ok(L2AcceptanceEntryV2 {
        module: required_name(members, &path, "module")?,
        theorem: required_name(members, &path, "theorem")?,
        statement_hash: required_hash(members, &path, "statement_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        accepted_level: required_string(members, &path, "accepted_level")?,
        approvals: required_array(members, &path, "approvals")?
            .iter()
            .enumerate()
            .map(|(approval_index, value)| parse_approval(value, &path, approval_index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
    })
}

fn parse_approval(
    value: &JsonValue,
    entry_path: &str,
    index: usize,
) -> PackageArtifactResult<L2AcceptanceApprovalV2> {
    let path = format!("{entry_path}.approvals[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, APPROVAL_FIELDS)?;
    Ok(L2AcceptanceApprovalV2 {
        authority: required_string(members, &path, "authority")?,
        authority_version: required_u64(members, &path, "authority_version")?,
        decision_id: required_string(members, &path, "decision_id")?,
        reviewer_role: required_string(members, &path, "reviewer_role")?,
        agent_task: required_string(members, &path, "agent_task")?,
        review_protocol: required_string(members, &path, "review_protocol")?,
        input_hash: required_hash(members, &path, "input_hash")?,
        review_report: parse_report_ref(required_value(members, &path, "review_report")?, &path)?,
        verdict: required_string(members, &path, "verdict")?,
    })
}

fn parse_report_ref(
    value: &JsonValue,
    approval_path: &str,
) -> PackageArtifactResult<L2AcceptanceReviewReportRef> {
    let path = format!("{approval_path}.review_report");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, REPORT_REF_FIELDS)?;
    Ok(L2AcceptanceReviewReportRef {
        path: required_path(members, &path, "path")?,
        file_hash: required_hash(members, &path, "file_hash")?,
    })
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

fn acceptance_json(acceptance: &L2AcceptanceV2) -> String {
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
            json_array(acceptance.entries.iter().map(entry_json).collect()),
        ),
        ("proof_evidence", json_bool(acceptance.proof_evidence)),
    ])
}

fn entry_json(entry: &L2AcceptanceEntryV2) -> String {
    json_object_in_order(vec![
        ("module", json_string(&entry.module.as_dotted())),
        ("theorem", json_string(&entry.theorem.as_dotted())),
        ("statement_hash", hash_json(entry.statement_hash)),
        ("certificate_hash", hash_json(entry.certificate_hash)),
        ("accepted_level", json_string(&entry.accepted_level)),
        (
            "approvals",
            json_array(entry.approvals.iter().map(approval_json).collect()),
        ),
    ])
}

fn approval_json(approval: &L2AcceptanceApprovalV2) -> String {
    json_object_in_order(vec![
        ("authority", json_string(&approval.authority)),
        ("authority_version", json_u64(approval.authority_version)),
        ("decision_id", json_string(&approval.decision_id)),
        ("reviewer_role", json_string(&approval.reviewer_role)),
        ("agent_task", json_string(&approval.agent_task)),
        ("review_protocol", json_string(&approval.review_protocol)),
        ("input_hash", hash_json(approval.input_hash)),
        (
            "review_report",
            json_object_in_order(vec![
                ("path", json_string(approval.review_report.path.as_str())),
                ("file_hash", hash_json(approval.review_report.file_hash)),
            ]),
        ),
        ("verdict", json_string(&approval.verdict)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(seed: u8) -> PackageHash {
        PackageHash::from([seed; 32])
    }

    fn approval(role: &str, seed: u8) -> L2AcceptanceApprovalV2 {
        L2AcceptanceApprovalV2 {
            authority: format!("authority-{role}"),
            authority_version: 2,
            decision_id: format!("decision-{role}"),
            reviewer_role: role.to_owned(),
            agent_task: format!("/root/l2_{role}"),
            review_protocol: "npa.l2.subagent-review.v2".to_owned(),
            input_hash: hash(8),
            review_report: L2AcceptanceReviewReportRef {
                path: PackagePath::new(format!("l2-reviews/{role}.json")),
                file_hash: hash(seed),
            },
            verdict: "accepted".to_owned(),
        }
    }

    fn entry(statement_seed: u8) -> L2AcceptanceEntryV2 {
        L2AcceptanceEntryV2 {
            module: Name::from_dotted("Proofs.Ai.Finite"),
            theorem: Name::from_dotted("finite_intro"),
            statement_hash: hash(statement_seed),
            certificate_hash: hash(2),
            accepted_level: "L2 Derived certificate".to_owned(),
            approvals: vec![
                approval("semantic-review", 4),
                approval("adversarial-review", 3),
            ],
        }
    }

    #[test]
    fn v2_ledger_round_trips_and_requires_explicit_replacement() {
        let ledger = L2AcceptanceV2 {
            schema: L2_ACCEPTANCE_V2_SCHEMA.to_owned(),
            policy_id: "finitefield-org.npa-mathlib.l2".to_owned(),
            policy_version: 2,
            policy_file_hash: hash(1),
            source_package: PackageId::new("npa-proof-corpus"),
            source_version: PackageVersion::new("0.1.0"),
            aggregator_agent_task: "/root".to_owned(),
            entries: vec![entry(1)],
            proof_evidence: false,
        };
        let json = ledger.canonical_json().unwrap();
        let parsed = parse_l2_acceptance_v2_json(&json).unwrap();
        assert_eq!(parsed.canonical_json().unwrap(), json);
        assert!(
            merge_l2_acceptance_v2_entries(parsed.clone(), vec![entry(9)], &BTreeSet::new(),)
                .is_err()
        );
        let key = (
            Name::from_dotted("Proofs.Ai.Finite"),
            Name::from_dotted("finite_intro"),
        );
        let replaced =
            merge_l2_acceptance_v2_entries(parsed, vec![entry(9)], &[key].into_iter().collect())
                .unwrap();
        assert_eq!(replaced.entries[0].statement_hash, hash(9));
    }
}
