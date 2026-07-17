//! Closed parsing and deterministic serialization for untrusted proof replay sidecars.
//!
//! Replay metadata is never proof evidence. This module exists so package tools
//! can preserve its exact public identities without rewriting raw JSON text.

use npa_cert::Name;

use crate::{
    artifacts::{
        expect_object, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_name, required_path, required_string,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    json::JsonValue,
    PackagePath,
};

/// Exact untrusted proof replay schema.
pub const PACKAGE_PROOF_REPLAY_SCHEMA: &str = "npa-ai-proof-replay-v0.1";
/// Exact replay producer profile supported by package promotion.
pub const PACKAGE_PROOF_REPLAY_PROFILE: &str = "explicit_term_source_certificate_handoff";

const PACKAGE_PROOF_REPLAY_PRODUCER: &str = "human-surface-explicit-term";
const ROOT_FIELDS: &[&str] = &[
    "schema",
    "module",
    "trusted",
    "profile",
    "producer",
    "steps",
    "acceptance",
];
const STEP_FIELDS: &[&str] = &["declaration", "source_kind", "term", "note"];
const ACCEPTANCE_FIELDS: &[&str] = &["required", "accepted_artifact"];
const REQUIRED_CHECKS: &[&str] = &["decode_module_cert", "verify_module_cert"];
const SOURCE_KINDS: &[&str] = &[
    "explicit_def_source",
    "explicit_def_value",
    "explicit_proof_term",
    "explicit_term",
    "explicit_term_source",
    "explicit_theorem_term",
    "inductive_decl",
    "theorem",
];

/// One untrusted declaration replay row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageProofReplayStep {
    /// Declaration name recorded by the replay producer.
    pub declaration: String,
    /// Closed source-kind spelling.
    pub source_kind: String,
    /// Optional untrusted source term or declaration text.
    pub term: Option<String>,
    /// Optional untrusted explanatory note used by audit-oriented producers.
    pub note: Option<String>,
}

/// One parsed untrusted proof replay document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageProofReplay {
    /// Module identity recorded by the replay.
    pub module: Name,
    /// Explicit-term replay profile, absent for producer-only sidecars.
    pub profile: Option<String>,
    /// Producer identity, present only for producer-only sidecars.
    pub producer: Option<String>,
    /// Ordered declaration replay rows.
    pub steps: Vec<PackageProofReplayStep>,
    /// Package-relative canonical certificate path accepted by the replay.
    pub accepted_artifact: Option<PackagePath>,
}

impl PackageProofReplay {
    /// Serialize the closed replay schema deterministically with one final newline.
    pub fn canonical_json(&self) -> String {
        let steps = self
            .steps
            .iter()
            .map(|step| {
                let mut fields = vec![
                    format!("      \"declaration\": {}", json_string(&step.declaration)),
                    format!("      \"source_kind\": {}", json_string(&step.source_kind)),
                ];
                if let Some(term) = &step.term {
                    fields.push(format!("      \"term\": {}", json_string(term)));
                }
                if let Some(note) = &step.note {
                    fields.push(format!("      \"note\": {}", json_string(note)));
                }
                format!("    {{\n{}\n    }}", fields.join(",\n"))
            })
            .collect::<Vec<_>>()
            .join(",\n");
        let identity = if let Some(profile) = &self.profile {
            format!("  \"profile\": {},", json_string(profile))
        } else {
            format!(
                "  \"producer\": {},",
                json_string(self.producer.as_deref().unwrap_or_default())
            )
        };
        let acceptance = self.accepted_artifact.as_ref().map_or_else(String::new, |path| {
            format!(
                ",\n  \"acceptance\": {{\n    \"required\": [\"decode_module_cert\", \"verify_module_cert\"],\n    \"accepted_artifact\": {}\n  }}",
                json_string(path.as_str())
            )
        });
        format!(
            "{{\n  \"schema\": \"{PACKAGE_PROOF_REPLAY_SCHEMA}\",\n  \"module\": {},\n  \"trusted\": false,\n{identity}\n  \"steps\": [\n{steps}\n  ]{acceptance}\n}}\n",
            json_string(&self.module.as_dotted())
        )
    }
}

/// Parse and validate one closed untrusted proof replay document.
pub fn parse_package_proof_replay(source: &str) -> PackageArtifactResult<PackageProofReplay> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, ROOT_FIELDS)?;
    let schema = required_string(members, "$", "schema")?;
    if schema != PACKAGE_PROOF_REPLAY_SCHEMA {
        return Err(PackageArtifactError::invalid_enum_value(
            "$.schema",
            "schema",
            PACKAGE_PROOF_REPLAY_SCHEMA,
            schema,
        ));
    }
    let trusted = required_bool(members, "$", "trusted")?;
    if trusted {
        return Err(PackageArtifactError::invalid_enum_value(
            "$.trusted",
            "trusted",
            "false",
            "true",
        ));
    }
    let profile = optional_string(members, "$", "profile")?;
    let producer = optional_string(members, "$", "producer")?;
    if !matches!((&profile, &producer), (Some(_), None) | (None, Some(_))) {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "producer identity",
            "exactly one of profile or producer",
            "mismatch",
        ));
    }
    if profile
        .as_deref()
        .is_some_and(|value| value != PACKAGE_PROOF_REPLAY_PROFILE)
        || producer
            .as_deref()
            .is_some_and(|value| value != PACKAGE_PROOF_REPLAY_PRODUCER)
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "producer identity",
            "supported replay profile or producer",
            "mismatch",
        ));
    }
    let steps = required_array(members, "$", "steps")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_step(value, index))
        .collect::<PackageArtifactResult<Vec<_>>>()?;
    let accepted_artifact = optional_value(members, "acceptance")
        .map(parse_acceptance)
        .transpose()?;
    if producer.is_some() && (accepted_artifact.is_some() || !steps.is_empty()) {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "producer replay",
            "empty steps and no acceptance",
            "mismatch",
        ));
    }
    Ok(PackageProofReplay {
        module: required_name(members, "$", "module")?,
        profile,
        producer,
        steps,
        accepted_artifact,
    })
}

fn parse_step(value: &JsonValue, index: usize) -> PackageArtifactResult<PackageProofReplayStep> {
    let path = format!("$.steps[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, STEP_FIELDS)?;
    let declaration = required_string(members, &path, "declaration")?;
    let source_kind = required_string(members, &path, "source_kind")?;
    let term = optional_string(members, &path, "term")?;
    let note = optional_string(members, &path, "note")?;
    if declaration.is_empty()
        || term.as_ref().is_some_and(String::is_empty)
        || note.as_ref().is_some_and(String::is_empty)
        || (term.is_some() && note.is_some())
        || !SOURCE_KINDS.contains(&source_kind.as_str())
    {
        return Err(PackageArtifactError::invalid_enum_value(
            path,
            "step",
            "non-empty declaration, optional term or note, and supported source_kind",
            "mismatch",
        ));
    }
    Ok(PackageProofReplayStep {
        declaration,
        source_kind,
        term,
        note,
    })
}

fn parse_acceptance(value: &JsonValue) -> PackageArtifactResult<PackagePath> {
    let acceptance_members = expect_object(value, "$.acceptance")?;
    reject_unknown_fields("$.acceptance", acceptance_members, ACCEPTANCE_FIELDS)?;
    let required = required_array(acceptance_members, "$.acceptance", "required")?;
    if required.len() != REQUIRED_CHECKS.len()
        || required
            .iter()
            .zip(REQUIRED_CHECKS)
            .any(|(value, expected)| {
                value
                    .string_value()
                    .is_none_or(|actual| actual != *expected)
            })
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "$.acceptance.required",
            "required",
            "decode_module_cert then verify_module_cert",
            "mismatch",
        ));
    }
    required_path(acceptance_members, "$.acceptance", "accepted_artifact")
}

fn optional_value<'a>(
    members: &'a [crate::json::JsonMember],
    field: &str,
) -> Option<&'a JsonValue> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(crate::json::JsonMember::value)
}

fn optional_string(
    members: &[crate::json::JsonMember],
    path: &str,
    field: &str,
) -> PackageArtifactResult<Option<String>> {
    optional_value(members, field)
        .map(|value| {
            value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
                PackageArtifactError::wrong_type(
                    format!("{path}.{field}"),
                    Some(field.to_owned()),
                    "string",
                    value.kind().as_str(),
                )
            })
        })
        .transpose()
}

fn json_string(value: &str) -> String {
    crate::artifacts::json_string(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn replay() -> PackageProofReplay {
        PackageProofReplay {
            module: Name::from_dotted("Proofs.Ai.Basic"),
            profile: Some(PACKAGE_PROOF_REPLAY_PROFILE.to_owned()),
            producer: None,
            steps: vec![PackageProofReplayStep {
                declaration: "id".to_owned(),
                source_kind: "explicit_term".to_owned(),
                term: Some("fun A => fun x => x".to_owned()),
                note: None,
            }],
            accepted_artifact: Some(PackagePath::new("Proofs/Ai/Basic/certificate.npcert")),
        }
    }

    #[test]
    fn proof_replay_round_trips_canonical_bytes() {
        let expected = replay();
        let source = expected.canonical_json();
        assert_eq!(parse_package_proof_replay(&source).unwrap(), expected);
    }

    #[test]
    fn proof_replay_rejects_shadow_and_duplicate_identity_fields() {
        let source = replay().canonical_json();
        let shadow = source.replacen(
            "{\n  \"schema\"",
            "{\n  \"shadow\": {\"module\": \"Proofs.Ai.Basic\"},\n  \"schema\"",
            1,
        );
        assert!(parse_package_proof_replay(&shadow).is_err());
        let duplicate = source.replacen(
            "  \"module\": \"Proofs.Ai.Basic\",",
            "  \"module\": \"Proofs.Ai.Basic\",\n  \"module\": \"Other.Module\",",
            1,
        );
        assert!(parse_package_proof_replay(&duplicate).is_err());
    }

    #[test]
    fn proof_replay_accepts_every_current_producer_source_kind() {
        for source_kind in SOURCE_KINDS {
            let mut expected = replay();
            expected.steps[0].source_kind = (*source_kind).to_owned();
            assert_eq!(
                parse_package_proof_replay(&expected.canonical_json()).unwrap(),
                expected
            );
        }
    }

    #[test]
    fn proof_replay_round_trips_current_optional_step_variants() {
        let mut without_term = replay();
        without_term.steps[0].term = None;
        assert_eq!(
            parse_package_proof_replay(&without_term.canonical_json()).unwrap(),
            without_term
        );

        let mut with_note = replay();
        with_note.steps[0].term = None;
        with_note.steps[0].note = Some("Audit-oriented explanation.".to_owned());
        assert_eq!(
            parse_package_proof_replay(&with_note.canonical_json()).unwrap(),
            with_note
        );
    }

    #[test]
    fn proof_replay_round_trips_profile_without_acceptance_and_producer_only_variants() {
        let mut without_acceptance = replay();
        without_acceptance.accepted_artifact = None;
        assert_eq!(
            parse_package_proof_replay(&without_acceptance.canonical_json()).unwrap(),
            without_acceptance
        );

        let producer = PackageProofReplay {
            module: Name::from_dotted("Proofs.Ai.Empty"),
            profile: None,
            producer: Some(PACKAGE_PROOF_REPLAY_PRODUCER.to_owned()),
            steps: Vec::new(),
            accepted_artifact: None,
        };
        assert_eq!(
            parse_package_proof_replay(&producer.canonical_json()).unwrap(),
            producer
        );
    }
}
