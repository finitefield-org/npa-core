//! Pure, owned-byte SNAP/VMSP controller and sealed-artifact validator.
//!
//! The process supervisor and retained-directory implementation live in the
//! caller.  This module deliberately accepts only owned byte slices and typed
//! fixture rows, so the same transformation and validation code is used before
//! publication and by the independent sealed-directory consumer.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use npa_api::{
    JsonDocument, JsonParseLimits, JsonValue, JsonValueKind, PerformanceFixtureArtifactMode,
    PerformanceFixtureImplementation, PerformanceFixtureSelectionV02, PerformanceMeasurementLabel,
};
use sha2::{Digest as _, Sha256};

pub const SNAP_MATRIX_SCHEMA: &str = "npa.package_artifact_snapshot.matrix.v3";
pub const VMSP_MATRIX_SCHEMA: &str = "npa.shared-payload.matrix.v0.3";
pub const SNAP_LANE_ID: &str = "package-artifact-snapshot";
pub const VMSP_LANE_ID: &str = "verified-module-shared-payload";
pub const MAX_SEMANTIC_STRUCTURE_BYTES: u64 = 64 * 1024 * 1024;
pub const MAX_CANONICAL_JSON_BYTES: u64 = 8 * 1024 * 1024;
const MAX_CANONICAL_JSON_VALUES: usize = 65_536;
const MAX_CANONICAL_JSON_CONTAINER_ITEMS: usize = 65_536;
const MAX_CANONICAL_JSON_DECODED_STRING_BYTES: usize = 8 * 1024 * 1024;
const MAX_CANONICAL_JSON_NUMBER_BYTES: usize = 128;

/// Return the closed working-set reservation required before parsing one
/// canonical document. The underlying parser separately caps source bytes,
/// values, container items, decoded string bytes, number bytes, and depth
/// before each proportional allocation.
pub fn json_structure_reservation(source_bytes: u64) -> Result<u64, String> {
    if source_bytes > MAX_CANONICAL_JSON_BYTES {
        return Err("canonical JSON source exceeds its closed byte bound".to_owned());
    }
    Ok(MAX_SEMANTIC_STRUCTURE_BYTES)
}

/// A completed record changes one existing natural and appends one bounded
/// ordinal field. Reserve this closed maximum before constructing it.
pub fn completed_record_byte_reservation(raw_bytes: u64) -> Result<u64, String> {
    raw_bytes
        .checked_add(256)
        .ok_or("completed record byte reservation overflowed".to_owned())
}

const SNAP_SAMPLE_SCHEMA: &str = "npa.package_artifact_snapshot.benchmark_sample.v2";
const SNAP_RUN_SCHEMA: &str = "npa.package_artifact_snapshot.benchmark_run.v2";
const VMSP_SAMPLE_SCHEMA: &str = "npa.shared-payload.sample.v0.3";
const VMSP_RUN_SCHEMA: &str = "npa.shared-payload.run.v0.3";
const MEASUREMENT_SCHEMA: &str = "npa.performance.measurements.v0.9";
const BASELINE_SCHEMA: &str = "npa.performance.baselines.v0.1";
const BASELINE_UPDATE_POLICY: &str = "Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request. Raw elapsed time and peak RSS are advisory evidence and must never be copied into this generic deterministic baseline.";
const ORACLE_HEADER: &str = "generator_schema\tprofile\tdescriptor_sha256\tlogical_identity_sha256\tartifact_tree_sha256\tmodule_count\timport_edge_count\tdeclaration_count\tname_table_entry_count\tlevel_table_node_count\tterm_table_node_count\ttree_file_count\tcertificate_bytes";
const ORACLE_PROFILES: &[&str] = &[
    "representative-1000-certificates",
    "synthetic-1kib",
    "synthetic-1mib",
    "synthetic-near-limit",
    "payload-1mib",
    "payload-16mib",
    "payload-near-limit",
    "payload-heavy-multi-module",
    "session-index",
    "small-certificate",
];

#[derive(Clone, Debug, Eq, PartialEq)]
struct OracleRow {
    generator_schema: String,
    profile: String,
    descriptor_sha256: String,
    logical_identity_sha256: String,
    artifact_tree_sha256: String,
    module_count: u64,
    import_edge_count: u64,
    declaration_count: u64,
    name_table_entry_count: u64,
    level_table_node_count: u64,
    term_table_node_count: u64,
    tree_file_count: u64,
    certificate_bytes: u64,
}

fn parse_oracle_rows(oracle: &[u8]) -> Result<BTreeMap<String, OracleRow>, String> {
    let oracle = std::str::from_utf8(oracle)
        .map_err(|error| format!("fixture oracle is not UTF-8: {error}"))?;
    if !oracle.ends_with('\n') || oracle.contains('\r') {
        return Err("fixture oracle must use one terminal LF and no CR".to_owned());
    }
    let lines = oracle.lines().collect::<Vec<_>>();
    if lines.len() != ORACLE_PROFILES.len() + 1 || lines.first() != Some(&ORACLE_HEADER) {
        return Err("fixture oracle header or exact row population mismatch".to_owned());
    }
    let mut rows = BTreeMap::new();
    for (line, expected_profile) in lines[1..].iter().zip(ORACLE_PROFILES) {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 13
            || fields[0] != "npa.performance.fixture-generator.v1"
            || fields[1] != *expected_profile
            || fields[2..5].iter().any(|hash| !valid_hash(hash, false))
        {
            return Err(format!("fixture oracle row {expected_profile} is invalid"));
        }
        let natural = |index: usize, label: &str| {
            let value = fields[index];
            if value.is_empty()
                || !value.bytes().all(|byte| byte.is_ascii_digit())
                || (value.len() > 1 && value.starts_with('0'))
            {
                return Err(format!("fixture oracle {label} is not canonical"));
            }
            value
                .parse::<u64>()
                .map_err(|_| format!("fixture oracle {label} exceeds u64"))
        };
        let row = OracleRow {
            generator_schema: fields[0].to_owned(),
            profile: fields[1].to_owned(),
            descriptor_sha256: fields[2].to_owned(),
            logical_identity_sha256: fields[3].to_owned(),
            artifact_tree_sha256: fields[4].to_owned(),
            module_count: natural(5, "module_count")?,
            import_edge_count: natural(6, "import_edge_count")?,
            declaration_count: natural(7, "declaration_count")?,
            name_table_entry_count: natural(8, "name_table_entry_count")?,
            level_table_node_count: natural(9, "level_table_node_count")?,
            term_table_node_count: natural(10, "term_table_node_count")?,
            tree_file_count: natural(11, "tree_file_count")?,
            certificate_bytes: natural(12, "certificate_bytes")?,
        };
        if rows.insert(row.profile.clone(), row).is_some() {
            return Err(format!("fixture oracle duplicates {expected_profile}"));
        }
    }
    Ok(rows)
}

fn selected_oracle_row(oracle: &[u8], profile: &str) -> Result<OracleRow, String> {
    parse_oracle_rows(oracle)?
        .remove(profile)
        .ok_or_else(|| format!("fixture oracle omits selected profile {profile}"))
}
const TARGETED_BUILD_CERT_IDS: &[&str] = &[
    "targeted-build-certs-small-off",
    "targeted-build-certs-small-read-through-cold",
    "targeted-build-certs-small-read-through-warm",
    "targeted-build-certs-large-off",
    "targeted-build-certs-large-read-through-cold",
    "targeted-build-certs-large-read-through-warm",
];
const TARGETED_BUILD_CERT_COUNTERS: &[&str] = &[
    "avoided_source_interface_resolutions",
    "cache_summary_emitted",
    "support_checks_avoided",
    "support_context_cache_hits",
    "support_context_entries_written",
    "support_live_checked",
    "target_result_cache_hits",
    "target_result_cache_misses",
    "target_result_cache_schema_misses",
    "target_result_cache_stale",
    "target_result_entries_written",
    "targets_live_built",
];
const TARGETED_BUILD_CERT_ROLLOUT_IDS: &[&str] = &[
    "targeted-build-certs-small-local-hit-cold",
    "targeted-build-certs-small-local-hit-warm",
    "targeted-build-certs-large-local-hit-cold",
    "targeted-build-certs-large-local-hit-partially-warm",
    "targeted-build-certs-large-local-hit-fully-warm",
];
const TARGETED_BUILD_CERT_ROLLOUT_COUNTERS: &[&str] = &[
    "support_selected",
    "targets_selected",
    "external_selected",
    "forced_live_support",
    "targets_forced_live",
    "visited_support",
    "visited_targets",
    "visited_external",
    "context_hits",
    "context_bypassed_hits",
    "context_misses",
    "context_stale",
    "context_schema_misses",
    "context_invalid",
    "context_ineligible",
    "live_prerequisite_checks",
    "avoided_kernel_checks",
    "avoided_source_interface_resolutions",
    "target_attempts",
    "target_fresh_builds",
    "entries_written",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LaneKind {
    Snapshot,
    SharedPayload,
}

impl LaneKind {
    pub const fn lane_id(self) -> &'static str {
        match self {
            Self::Snapshot => SNAP_LANE_ID,
            Self::SharedPayload => VMSP_LANE_ID,
        }
    }

    pub const fn matrix_schema(self) -> &'static str {
        match self {
            Self::Snapshot => SNAP_MATRIX_SCHEMA,
            Self::SharedPayload => VMSP_MATRIX_SCHEMA,
        }
    }

    pub const fn execution_count(self) -> usize {
        match self {
            Self::Snapshot => 200,
            Self::SharedPayload => 275,
        }
    }

    pub const fn payload_count(self) -> usize {
        // Three files per execution, two report/catalog files, three input
        // snapshots, and one benchmark plus one manager audit executable.
        self.execution_count() * 3 + 2 + 3 + 2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Execution {
    pub ordinal: usize,
    pub scenario: String,
    pub sample_index: Option<u64>,
    pub suffix: String,
}

impl Execution {
    pub fn raw_name(&self) -> PathBuf {
        PathBuf::from(format!(
            "{}.{}.{}.raw.json",
            self.ordinal, self.scenario, self.suffix
        ))
    }

    pub fn completed_name(&self) -> PathBuf {
        PathBuf::from(format!(
            "{}.{}.{}.json",
            self.ordinal, self.scenario, self.suffix
        ))
    }

    pub fn stderr_name(&self) -> PathBuf {
        PathBuf::from(format!(
            "{}.{}.{}.stderr",
            self.ordinal, self.scenario, self.suffix
        ))
    }
}

#[derive(Clone, Debug)]
pub struct AuditBinding<'a> {
    pub source_identity: &'a str,
    pub manifest_sha256: &'a str,
    pub baseline_sha256: &'a str,
    pub oracle_sha256: &'a str,
    pub benchmark_sha256: &'a str,
    pub manager_sha256: &'a str,
    pub manager_source_set_sha256: &'a str,
    pub manager_source_sha256: &'a str,
    pub manager_cargo_lock_sha256: &'a str,
    pub manager_cargo_profile: &'a str,
    pub manager_target: &'a str,
    pub manager_features: &'a str,
    pub manager_rustc_vv: &'a str,
    pub manager_rustflags: &'a str,
    pub benchmark_cargo_lock_sha256: &'a str,
    pub benchmark_cargo_profile: &'a str,
    pub benchmark_target: &'a str,
    pub benchmark_features: &'a str,
    pub benchmark_rustc_vv: &'a str,
    pub benchmark_rustflags: &'a str,
    pub benchmark_harness_source_sha256: &'a str,
    pub benchmark_source_set_sha256: &'a str,
    pub benchmark_fixture_parser_source_sha256: Option<&'a str>,
    pub benchmark_measure_process_source_sha256: &'a str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OwnedJson {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<OwnedJson>),
    Object(Vec<(String, OwnedJson)>),
}

impl OwnedJson {
    pub fn parse_canonical_line(bytes: &[u8], label: &str) -> Result<Self, String> {
        Self::parse_bounded(bytes, label, true)
    }

    pub fn parse_bounded_document(bytes: &[u8], label: &str) -> Result<Self, String> {
        Self::parse_bounded(bytes, label, false)
    }

    fn parse_bounded(bytes: &[u8], label: &str, require_canonical: bool) -> Result<Self, String> {
        if u64::try_from(bytes.len()).map_err(|error| error.to_string())? > MAX_CANONICAL_JSON_BYTES
        {
            return Err(format!("{label} exceeds its canonical byte bound"));
        }
        let reservation = json_structure_reservation(
            u64::try_from(bytes.len()).map_err(|error| error.to_string())?,
        )?;
        if reservation > MAX_SEMANTIC_STRUCTURE_BYTES {
            return Err(format!(
                "{label} exceeds its pre-parse structural-memory bound"
            ));
        }
        let source =
            std::str::from_utf8(bytes).map_err(|error| format!("{label} is not UTF-8: {error}"))?;
        if !source.ends_with('\n') || source[..source.len() - 1].ends_with('\n') {
            return Err(format!("{label} must have one terminal LF"));
        }
        let document = JsonDocument::parse_with_limits(
            source,
            JsonParseLimits::bounded(
                64,
                MAX_CANONICAL_JSON_VALUES,
                MAX_CANONICAL_JSON_CONTAINER_ITEMS,
                MAX_CANONICAL_JSON_DECODED_STRING_BYTES,
                MAX_CANONICAL_JSON_NUMBER_BYTES,
            ),
        )
        .map_err(|error| format!("{label} JSON error at byte {}", error.offset))?;
        let value = Self::from_value(document.root(), label)?;
        if value.retained_bytes()? > reservation {
            return Err(format!(
                "{label} exceeded its conservative structural reservation"
            ));
        }
        if require_canonical && value.canonical_line().as_bytes() != bytes {
            return Err(format!("{label} is not exact canonical JSON"));
        }
        Ok(value)
    }

    fn from_value(value: &JsonValue<'_>, label: &str) -> Result<Self, String> {
        match value.kind() {
            JsonValueKind::Null => Ok(Self::Null),
            JsonValueKind::Bool => {
                Ok(Self::Bool(value.bool_value().ok_or_else(|| {
                    format!("{label} parser lost a boolean value")
                })?))
            }
            JsonValueKind::Number => Ok(Self::Number(
                value
                    .number_raw()
                    .ok_or_else(|| format!("{label} parser lost a number spelling"))?
                    .to_owned(),
            )),
            JsonValueKind::String => Ok(Self::String(
                value
                    .string_value()
                    .ok_or_else(|| format!("{label} parser lost a string value"))?
                    .to_owned(),
            )),
            JsonValueKind::Array => Ok(Self::Array(
                value
                    .array_elements()
                    .ok_or_else(|| format!("{label} parser lost array elements"))?
                    .iter()
                    .map(|value| Self::from_value(value, label))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            JsonValueKind::Object => {
                let mut seen = BTreeSet::new();
                let members = value
                    .object_members()
                    .ok_or_else(|| format!("{label} parser lost object members"))?
                    .iter()
                    .map(|member| {
                        if !seen.insert(member.key()) {
                            return Err(format!("{label} duplicates key {}", member.key()));
                        }
                        Ok((
                            member.key().to_owned(),
                            Self::from_value(member.value(), label)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(Self::Object(members))
            }
        }
    }

    /// Conservative checked accounting for owned JSON storage retained by the
    /// controller. This charges string bytes plus the complete in-memory node
    /// and vector-slot footprint, so canonical input bytes are not the only
    /// resource bound.
    pub fn retained_bytes(&self) -> Result<u64, String> {
        fn add(total: &mut u64, value: u64) -> Result<(), String> {
            *total = total
                .checked_add(value)
                .ok_or("owned JSON retained-byte accounting overflowed")?;
            Ok(())
        }

        fn visit(value: &OwnedJson, total: &mut u64) -> Result<(), String> {
            add(
                total,
                u64::try_from(std::mem::size_of::<OwnedJson>())
                    .map_err(|error| error.to_string())?,
            )?;
            match value {
                OwnedJson::Null | OwnedJson::Bool(_) => Ok(()),
                OwnedJson::Number(value) | OwnedJson::String(value) => add(
                    total,
                    u64::try_from(value.len()).map_err(|error| error.to_string())?,
                ),
                OwnedJson::Array(values) => {
                    add(
                        total,
                        u64::try_from(values.capacity())
                            .map_err(|error| error.to_string())?
                            .checked_mul(
                                u64::try_from(std::mem::size_of::<OwnedJson>())
                                    .map_err(|error| error.to_string())?,
                            )
                            .ok_or("owned JSON array accounting overflowed")?,
                    )?;
                    for value in values {
                        visit(value, total)?;
                    }
                    Ok(())
                }
                OwnedJson::Object(members) => {
                    add(
                        total,
                        u64::try_from(members.capacity())
                            .map_err(|error| error.to_string())?
                            .checked_mul(
                                u64::try_from(std::mem::size_of::<(String, OwnedJson)>())
                                    .map_err(|error| error.to_string())?,
                            )
                            .ok_or("owned JSON object accounting overflowed")?,
                    )?;
                    for (key, value) in members {
                        add(
                            total,
                            u64::try_from(key.len()).map_err(|error| error.to_string())?,
                        )?;
                        visit(value, total)?;
                    }
                    Ok(())
                }
            }
        }

        let mut total = 0;
        visit(self, &mut total)?;
        Ok(total)
    }

    pub fn canonical_line(&self) -> String {
        let mut output = String::new();
        self.write_canonical(&mut output);
        output.push('\n');
        output
    }

    /// Return one exact-sized canonical allocation.
    ///
    /// `String::into_bytes` preserves the serializer's geometric spare
    /// capacity.  Completed records and matrices are retained under a strict
    /// byte budget, so their ownership boundary must discard that capacity
    /// instead of charging an allocator-growth artifact as evidence bytes.
    pub fn canonical_boxed_line(&self) -> Box<[u8]> {
        self.canonical_line().into_boxed_str().into_boxed_bytes()
    }

    fn write_canonical(&self, output: &mut String) {
        match self {
            Self::Null => output.push_str("null"),
            Self::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
            Self::Number(value) => output.push_str(value),
            Self::String(value) => push_json_string(output, value),
            Self::Array(values) => {
                output.push('[');
                for (index, value) in values.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    value.write_canonical(output);
                }
                output.push(']');
            }
            Self::Object(members) => {
                output.push('{');
                for (index, (key, value)) in members.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    push_json_string(output, key);
                    output.push(':');
                    value.write_canonical(output);
                }
                output.push('}');
            }
        }
    }

    pub fn exact_object(&self, keys: &[&str], label: &str) -> Result<(), String> {
        let actual = self
            .object_members()
            .ok_or_else(|| format!("{label} must be an object"))?
            .iter()
            .map(|(key, _)| key.as_str())
            .collect::<Vec<_>>();
        if actual != keys {
            return Err(format!(
                "{label} has missing, unknown, duplicate, or reordered keys: expected {keys:?}, actual {actual:?}"
            ));
        }
        Ok(())
    }

    pub fn object_members(&self) -> Option<&[(String, OwnedJson)]> {
        match self {
            Self::Object(value) => Some(value),
            _ => None,
        }
    }

    pub fn object_members_mut(&mut self) -> Option<&mut Vec<(String, OwnedJson)>> {
        match self {
            Self::Object(value) => Some(value),
            _ => None,
        }
    }

    pub fn array(&self, label: &str) -> Result<&[OwnedJson], String> {
        match self {
            Self::Array(values) => Ok(values),
            _ => Err(format!("{label} must be an array")),
        }
    }

    pub fn field(&self, name: &str, label: &str) -> Result<&OwnedJson, String> {
        self.object_members()
            .ok_or_else(|| format!("{label} must be an object"))?
            .iter()
            .find(|(key, _)| key == name)
            .map(|(_, value)| value)
            .ok_or_else(|| format!("{label}.{name} is missing"))
    }

    pub fn text(&self, label: &str) -> Result<&str, String> {
        match self {
            Self::String(value) => Ok(value),
            _ => Err(format!("{label} must be a string")),
        }
    }

    pub fn natural(&self, label: &str) -> Result<u64, String> {
        let Self::Number(value) = self else {
            return Err(format!("{label} must be a natural number"));
        };
        if value.is_empty()
            || !value.bytes().all(|byte| byte.is_ascii_digit())
            || (value.len() > 1 && value.starts_with('0'))
        {
            return Err(format!("{label} must be a canonical natural number"));
        }
        value
            .parse::<u64>()
            .map_err(|_| format!("{label} exceeds u64"))
    }

    pub fn boolean(&self, label: &str) -> Result<bool, String> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err(format!("{label} must be a boolean")),
        }
    }

    pub fn set_existing(&mut self, key: &str, value: OwnedJson) -> Result<(), String> {
        let members = self
            .object_members_mut()
            .ok_or("JSON mutation target is not an object")?;
        let selected = members
            .iter_mut()
            .find(|(candidate, _)| candidate == key)
            .ok_or_else(|| format!("JSON mutation target omits {key}"))?;
        selected.1 = value;
        Ok(())
    }

    pub fn push_field(&mut self, key: &str, value: OwnedJson) -> Result<(), String> {
        let members = self
            .object_members_mut()
            .ok_or("JSON mutation target is not an object")?;
        if members.iter().any(|(candidate, _)| candidate == key) {
            return Err(format!("JSON mutation would duplicate {key}"));
        }
        members.push((key.to_owned(), value));
        Ok(())
    }

    pub fn remove_fields(&mut self, fields: &[&str]) -> Result<(), String> {
        let members = self
            .object_members_mut()
            .ok_or("JSON mutation target is not an object")?;
        for field in fields {
            let before = members.len();
            members.retain(|(key, _)| key != field);
            if members.len() + 1 != before {
                return Err(format!("JSON mutation target omits {field}"));
            }
        }
        Ok(())
    }

    fn reject_absolute_strings(&self, label: &str) -> Result<(), String> {
        match self {
            Self::String(value) if value.starts_with('/') => {
                Err(format!("{label} contains an absolute path"))
            }
            Self::Array(values) => {
                for value in values {
                    value.reject_absolute_strings(label)?;
                }
                Ok(())
            }
            Self::Object(members) => {
                for (_, value) in members {
                    value.reject_absolute_strings(label)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

fn number(value: u64) -> OwnedJson {
    OwnedJson::Number(value.to_string())
}

fn string(value: impl Into<String>) -> OwnedJson {
    OwnedJson::String(value.into())
}

fn object(entries: impl IntoIterator<Item = (&'static str, OwnedJson)>) -> OwnedJson {
    OwnedJson::Object(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect(),
    )
}

pub fn sha256(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}

pub fn raw_sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

pub fn execution_catalog(
    kind: LaneKind,
    rows: &[PerformanceFixtureSelectionV02],
) -> Result<Vec<Execution>, String> {
    match kind {
        LaneKind::Snapshot => snapshot_execution_catalog(rows),
        LaneKind::SharedPayload => shared_payload_execution_catalog(rows),
    }
}

fn snapshot_execution_catalog(
    rows: &[PerformanceFixtureSelectionV02],
) -> Result<Vec<Execution>, String> {
    let snapshot_rows = rows
        .iter()
        .filter_map(|row| match row {
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(row) => Some(row),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut executions = Vec::new();
    for sample in 0..5_u64 {
        for raw in snapshot_rows
            .iter()
            .copied()
            .filter(|row| row.artifact_mode == PerformanceFixtureArtifactMode::Raw)
        {
            let companion = snapshot_rows
                .iter()
                .copied()
                .filter(|candidate| {
                    candidate.common.interleave_group == raw.common.interleave_group
                        && candidate.artifact_mode == PerformanceFixtureArtifactMode::Snapshot
                })
                .collect::<Vec<_>>();
            let [snapshot] = companion.as_slice() else {
                return Err("SNAP manifest has no unique raw/snapshot companion".to_owned());
            };
            let ordered = if sample % 2 == 0 {
                [raw, *snapshot]
            } else {
                [*snapshot, raw]
            };
            for row in ordered {
                executions.push(Execution {
                    ordinal: executions.len(),
                    scenario: row.common.id.clone(),
                    sample_index: Some(sample),
                    suffix: format!("sample-{sample}"),
                });
            }
        }
    }
    if executions.len() != LaneKind::Snapshot.execution_count() {
        return Err("SNAP manifest must select exactly 200 executions".to_owned());
    }
    Ok(executions)
}

fn shared_payload_execution_catalog(
    rows: &[PerformanceFixtureSelectionV02],
) -> Result<Vec<Execution>, String> {
    let paired = rows
        .iter()
        .filter_map(|row| match row {
            PerformanceFixtureSelectionV02::SharedPayloadClone(row)
            | PerformanceFixtureSelectionV02::SharedPayloadSmall(row) => Some((
                row.common.id.as_str(),
                row.common.interleave_group.as_str(),
                row.implementation,
            )),
            PerformanceFixtureSelectionV02::SharedPayloadSession(row) => Some((
                row.common.id.as_str(),
                row.common.interleave_group.as_str(),
                row.implementation,
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut executions = Vec::new();
    for sample in 0..7_u64 {
        for (legacy, group, _) in paired.iter().copied().filter(|(_, _, implementation)| {
            *implementation == PerformanceFixtureImplementation::LegacyModel
        }) {
            let companion = paired
                .iter()
                .copied()
                .filter(|(_, candidate_group, implementation)| {
                    *candidate_group == group
                        && *implementation == PerformanceFixtureImplementation::SharedHandle
                })
                .collect::<Vec<_>>();
            let [(shared, _, _)] = companion.as_slice() else {
                return Err("VMSP manifest has no unique legacy/shared companion".to_owned());
            };
            let ordered = if sample % 2 == 0 {
                [legacy, *shared]
            } else {
                [*shared, legacy]
            };
            for scenario in ordered {
                executions.push(Execution {
                    ordinal: executions.len(),
                    scenario: scenario.to_owned(),
                    sample_index: Some(sample),
                    suffix: format!("sample-{sample}"),
                });
            }
        }
    }
    for row in rows {
        let scenario = match row {
            PerformanceFixtureSelectionV02::SharedPayloadCache(row) => Some(&row.common.id),
            PerformanceFixtureSelectionV02::SharedPayloadMemo(row) => Some(&row.common.id),
            PerformanceFixtureSelectionV02::SharedPayloadShard(row) => Some(&row.common.id),
            _ => None,
        };
        if let Some(scenario) = scenario {
            executions.push(Execution {
                ordinal: executions.len(),
                scenario: scenario.clone(),
                sample_index: None,
                suffix: "run".to_owned(),
            });
        }
    }
    if executions.len() != LaneKind::SharedPayload.execution_count() {
        return Err("VMSP manifest must select exactly 275 executions".to_owned());
    }
    Ok(executions)
}

pub fn manifest_order_json(kind: LaneKind, rows: &[PerformanceFixtureSelectionV02]) -> Vec<u8> {
    let values = rows
        .iter()
        .filter(|row| match kind {
            LaneKind::Snapshot => {
                matches!(
                    row,
                    PerformanceFixtureSelectionV02::PackageArtifactSnapshot(_)
                )
            }
            LaneKind::SharedPayload => matches!(
                row,
                PerformanceFixtureSelectionV02::SharedPayloadClone(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadCache(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadMemo(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadShard(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
            ),
        })
        .map(|row| string(row.id()))
        .collect::<Vec<_>>();
    OwnedJson::Array(values).canonical_line().into_bytes()
}

pub fn expected_payload_catalog(
    kind: LaneKind,
    rows: &[PerformanceFixtureSelectionV02],
) -> Result<BTreeSet<PathBuf>, String> {
    let executions = execution_catalog(kind, rows)?;
    let mut files = BTreeSet::from([
        PathBuf::from(".manifest-order.json"),
        PathBuf::from("matrix.json"),
        PathBuf::from(".fixture-manifest.json"),
        PathBuf::from(".measurement-baseline.json"),
        PathBuf::from(".fixture-oracle.tsv"),
        PathBuf::from(".benchmark-executable"),
        PathBuf::from(".measure-process-executable"),
    ]);
    for execution in executions {
        files.insert(execution.raw_name());
        files.insert(execution.completed_name());
        files.insert(execution.stderr_name());
    }
    if files.len() != kind.payload_count() {
        return Err("SNAP/VMSP payload catalog count is not closed".to_owned());
    }
    Ok(files)
}

/// Validate every row of the build-pinned baseline and every oracle row once
/// before any measured child is started. Selected-row lookups later are then
/// projections from a closed, whole-file semantic input.
pub fn validate_whole_inputs(
    kind: LaneKind,
    rows: &[PerformanceFixtureSelectionV02],
    baseline: &[u8],
    oracle: &[u8],
) -> Result<(), String> {
    let parsed = OwnedJson::parse_bounded_document(baseline, "performance baseline")?;
    parsed.exact_object(
        &[
            "schema",
            "measurement_schema",
            "scenarios",
            "targeted_build_certs",
            "targeted_build_certs_rollout",
            "update_policy",
        ],
        "performance baseline",
    )?;
    exact_text(
        parsed.field("schema", "baseline")?,
        BASELINE_SCHEMA,
        "baseline schema",
    )?;
    exact_text(
        parsed.field("measurement_schema", "baseline")?,
        MEASUREMENT_SCHEMA,
        "baseline measurement schema",
    )?;
    exact_text(
        parsed.field("update_policy", "baseline")?,
        BASELINE_UPDATE_POLICY,
        "baseline update policy",
    )?;
    let scenarios = parsed
        .field("scenarios", "baseline")?
        .array("baseline scenarios")?;
    let mut ids = BTreeSet::new();
    for row in scenarios {
        let (id, _, _, _, _) = validate_baseline_scenario(row)?;
        if !ids.insert(id.to_owned()) {
            return Err(format!("performance baseline duplicates scenario {id}"));
        }
    }
    validate_targeted_build_collection(
        parsed.field("targeted_build_certs", "baseline")?,
        TARGETED_BUILD_CERT_IDS,
        TARGETED_BUILD_CERT_COUNTERS,
        "targeted_build_certs",
    )?;
    validate_targeted_build_collection(
        parsed.field("targeted_build_certs_rollout", "baseline")?,
        TARGETED_BUILD_CERT_ROLLOUT_IDS,
        TARGETED_BUILD_CERT_ROLLOUT_COUNTERS,
        "targeted_build_certs_rollout",
    )?;
    for row in rows.iter().filter(|row| match kind {
        LaneKind::Snapshot => matches!(
            row,
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(_)
        ),
        LaneKind::SharedPayload => matches!(
            row,
            PerformanceFixtureSelectionV02::SharedPayloadClone(_)
                | PerformanceFixtureSelectionV02::SharedPayloadCache(_)
                | PerformanceFixtureSelectionV02::SharedPayloadMemo(_)
                | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
                | PerformanceFixtureSelectionV02::SharedPayloadShard(_)
                | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
        ),
    }) {
        if !ids.contains(row.id()) {
            return Err(format!(
                "performance baseline omits lane scenario {}",
                row.id()
            ));
        }
    }

    let _ = parse_oracle_rows(oracle)?;
    Ok(())
}

fn validate_targeted_build_collection(
    value: &OwnedJson,
    expected_ids: &[&str],
    expected_counter_keys: &[&str],
    label: &str,
) -> Result<(), String> {
    let rows = value.array(label)?;
    if rows.len() != expected_ids.len() {
        return Err(format!("{label} exact row population mismatch"));
    }
    for (row, expected_id) in rows.iter().zip(expected_ids) {
        row.exact_object(
            &[
                "id",
                "status",
                "support_module_count",
                "target_module_count",
                "deterministic_counters",
            ],
            label,
        )?;
        exact_text(row.field("id", label)?, expected_id, &format!("{label} id"))?;
        exact_text(
            row.field("status", label)?,
            "passed",
            &format!("{label} status"),
        )?;
        let support = row
            .field("support_module_count", label)?
            .natural(&format!("{label} support_module_count"))?;
        if support != 2 && support != 24 {
            return Err(format!(
                "{label} support_module_count is outside the closed set"
            ));
        }
        exact_natural(
            row.field("target_module_count", label)?,
            1,
            &format!("{label} target_module_count"),
        )?;
        let counters = row.field("deterministic_counters", label)?;
        counters.exact_object(expected_counter_keys, &format!("{label} counters"))?;
        for key in expected_counter_keys {
            counters
                .field(key, label)?
                .natural(&format!("{label} counter {key}"))?;
        }
    }
    Ok(())
}

#[allow(clippy::type_complexity)]
fn validate_baseline_scenario(
    row: &OwnedJson,
) -> Result<(&str, u64, BTreeMap<String, u64>, u64, bool), String> {
    row.exact_object(
        &[
            "id",
            "status",
            "module_count",
            "deterministic_counters",
            "coverage",
        ],
        "baseline row",
    )?;
    let id = row.field("id", "baseline row")?.text("baseline row.id")?;
    if id.is_empty() {
        return Err("baseline scenario id must not be empty".to_owned());
    }
    exact_text(
        row.field("status", "baseline row")?,
        "passed",
        "baseline status",
    )?;
    let mut counters = BTreeMap::new();
    let members = row
        .field("deterministic_counters", "baseline row")?
        .object_members()
        .ok_or("baseline deterministic_counters must be an object")?;
    if members.is_empty() {
        return Err("baseline deterministic_counters must not be empty".to_owned());
    }
    let mut previous = None;
    for (key, value) in members {
        if previous.is_some_and(|previous: &str| previous >= key.as_str()) {
            return Err("baseline counters are not strictly ordered".to_owned());
        }
        if PerformanceMeasurementLabel::from_schema_identifier(MEASUREMENT_SCHEMA, key).is_none() {
            return Err(format!(
                "baseline counter {key} is unknown for {MEASUREMENT_SCHEMA}"
            ));
        }
        previous = Some(key);
        counters.insert(key.clone(), value.natural("baseline counter")?);
    }
    let coverage = row.field("coverage", "baseline row")?;
    coverage.exact_object(
        &["live_results_min", "proof_evidence_reduction_allowed"],
        "baseline coverage",
    )?;
    Ok((
        id,
        row.field("module_count", "baseline row")?
            .natural("baseline module_count")?,
        counters,
        coverage
            .field("live_results_min", "baseline coverage")?
            .natural("baseline live_results_min")?,
        coverage
            .field("proof_evidence_reduction_allowed", "baseline coverage")?
            .boolean("baseline proof_evidence_reduction_allowed")?,
    ))
}

fn baseline_counters(
    baseline: &[u8],
    scenario: &str,
) -> Result<(u64, BTreeMap<String, u64>, u64, bool), String> {
    let root = OwnedJson::parse_bounded_document(baseline, "baseline")?;
    root.exact_object(
        &[
            "schema",
            "measurement_schema",
            "scenarios",
            "targeted_build_certs",
            "targeted_build_certs_rollout",
            "update_policy",
        ],
        "baseline",
    )?;
    let scenarios = root
        .field("scenarios", "baseline")?
        .array("baseline.scenarios")?;
    let mut selected = None;
    for row in scenarios {
        if row.field("id", "baseline row")?.text("baseline row.id")? == scenario
            && selected.replace(row).is_some()
        {
            return Err(format!("baseline duplicates scenario {scenario}"));
        }
    }
    let row = selected.ok_or_else(|| format!("baseline omits scenario {scenario}"))?;
    let (_, module_count, counters, live_results_min, proof_evidence_reduction_allowed) =
        validate_baseline_scenario(row)?;
    Ok((
        module_count,
        counters,
        live_results_min,
        proof_evidence_reduction_allowed,
    ))
}

fn exact_text(value: &OwnedJson, expected: &str, label: &str) -> Result<(), String> {
    if value.text(label)? == expected {
        Ok(())
    } else {
        Err(format!("{label} mismatch"))
    }
}

fn exact_natural(value: &OwnedJson, expected: u64, label: &str) -> Result<(), String> {
    if value.natural(label)? == expected {
        Ok(())
    } else {
        Err(format!("{label} mismatch"))
    }
}

fn valid_source_identity(value: &str) -> bool {
    let oid = value.strip_suffix("-dirty").unwrap_or(value);
    oid.len() == 40
        && oid
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn valid_hash(value: &str, prefixed: bool) -> bool {
    let value = if prefixed {
        value.strip_prefix("sha256:")
    } else {
        Some(value)
    };
    value.is_some_and(|value| {
        value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    })
}

fn tagged_benchmark_hash_raw(value: &str) -> Result<&str, String> {
    let raw = value
        .strip_prefix("sha256:")
        .ok_or("benchmark executable audit hash must use the sha256:<hex> representation")?;
    if !valid_hash(value, true) {
        return Err("benchmark executable audit hash is not canonical SHA-256".to_owned());
    }
    Ok(raw)
}

fn tagged_benchmark_hash(value: &str) -> Result<&str, String> {
    tagged_benchmark_hash_raw(value)?;
    Ok(value)
}

#[allow(clippy::too_many_arguments)]
pub fn complete_captured_record(
    kind: LaneKind,
    execution: &Execution,
    raw_bytes: &[u8],
    peak_rss_kib: u64,
    rows: &[PerformanceFixtureSelectionV02],
    baseline: &[u8],
    oracle: &[u8],
    binding: &AuditBinding<'_>,
) -> Result<Box<[u8]>, String> {
    let mut raw = OwnedJson::parse_canonical_line(raw_bytes, "captured benchmark record").map_err(
        |error| {
            format!(
                "captured benchmark record {} ordinal {} ({} bytes): {error}",
                execution.scenario,
                execution.ordinal,
                raw_bytes.len()
            )
        },
    )?;
    validate_raw_record(
        kind, execution, &raw, rows, baseline, oracle, binding, false,
    )?;
    let peak_field = match kind {
        LaneKind::Snapshot => "process_peak_rss_kib",
        LaneKind::SharedPayload => "peak_rss_kib",
    };
    raw.set_existing(peak_field, number(peak_rss_kib))?;
    raw.push_field("execution_ordinal", number(execution.ordinal as u64))?;
    validate_raw_record(kind, execution, &raw, rows, baseline, oracle, binding, true)?;
    Ok(raw.canonical_boxed_line())
}

#[allow(clippy::too_many_arguments)]
pub fn validate_completed_against_raw(
    kind: LaneKind,
    execution: &Execution,
    raw_bytes: &[u8],
    completed_bytes: &[u8],
    rows: &[PerformanceFixtureSelectionV02],
    baseline: &[u8],
    oracle: &[u8],
    binding: &AuditBinding<'_>,
) -> Result<OwnedJson, String> {
    let raw = OwnedJson::parse_canonical_line(raw_bytes, "sealed raw record")?;
    validate_raw_record(
        kind, execution, &raw, rows, baseline, oracle, binding, false,
    )?;
    let completed = OwnedJson::parse_canonical_line(completed_bytes, "sealed completed record")?;
    validate_raw_record(
        kind, execution, &completed, rows, baseline, oracle, binding, true,
    )?;
    let peak_field = match kind {
        LaneKind::Snapshot => "process_peak_rss_kib",
        LaneKind::SharedPayload => "peak_rss_kib",
    };
    let peak = completed
        .field(peak_field, "completed record")?
        .natural("completed peak RSS")?;
    let expected = complete_captured_record(
        kind, execution, raw_bytes, peak, rows, baseline, oracle, binding,
    )?;
    if expected.as_ref() != completed_bytes {
        return Err("completed record is not the exact canonical raw projection".to_owned());
    }
    Ok(completed)
}

/// Test/support entry point for validating a captured record without running
/// a child process. Production uses the same implementation before retaining
/// any completed bytes.
#[allow(clippy::too_many_arguments)]
fn validate_raw_record(
    kind: LaneKind,
    execution: &Execution,
    record: &OwnedJson,
    rows: &[PerformanceFixtureSelectionV02],
    baseline: &[u8],
    oracle: &[u8],
    binding: &AuditBinding<'_>,
    completed: bool,
) -> Result<(), String> {
    match kind {
        LaneKind::Snapshot => validate_snapshot_record(
            execution, record, rows, baseline, oracle, binding, completed,
        ),
        LaneKind::SharedPayload => validate_vmsp_record(
            execution, record, rows, baseline, oracle, binding, completed,
        ),
    }
}

fn validate_snapshot_record(
    execution: &Execution,
    record: &OwnedJson,
    rows: &[PerformanceFixtureSelectionV02],
    baseline: &[u8],
    oracle: &[u8],
    binding: &AuditBinding<'_>,
    completed: bool,
) -> Result<(), String> {
    const RAW_KEYS: &[&str] = &[
        "schema",
        "scenario_id",
        "source_identity",
        "build_identity_sha256",
        "cargo_lock_sha256",
        "rustc_vv",
        "cargo_profile",
        "features",
        "target",
        "rustflags",
        "harness_source_sha256",
        "production_source_set_sha256",
        "measure_process_source_sha256",
        "measurement_mode",
        "execution_lane",
        "artifact_mode",
        "fixture_profile",
        "artifact_bytes",
        "fixture_descriptor_sha256",
        "fixture_logical_identity_sha256",
        "fixture_tree_sha256",
        "warmup",
        "manifest_samples",
        "sample_index",
        "interleave_group",
        "process_peak_rss_scope",
        "elapsed_ns",
        "acquisition_ns",
        "checker_ns",
        "allocation_events",
        "allocated_bytes",
        "process_peak_rss_kib",
        "deterministic_counters",
    ];
    let mut keys = RAW_KEYS.to_vec();
    if completed {
        keys.push("execution_ordinal");
    }
    record.exact_object(&keys, "SNAP record")?;
    record.reject_absolute_strings("SNAP record")?;
    let row = rows
        .iter()
        .find_map(|row| match row {
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(row)
                if row.common.id == execution.scenario =>
            {
                Some(row)
            }
            _ => None,
        })
        .ok_or("SNAP execution scenario is absent from the manifest")?;
    exact_text(
        record.field("schema", "SNAP")?,
        SNAP_SAMPLE_SCHEMA,
        "SNAP schema",
    )?;
    exact_text(
        record.field("scenario_id", "SNAP")?,
        &execution.scenario,
        "SNAP scenario",
    )?;
    let source = record
        .field("source_identity", "SNAP")?
        .text("SNAP source identity")?;
    if source != binding.source_identity || !valid_source_identity(source) {
        return Err("SNAP source identity mismatch".to_owned());
    }
    exact_text(
        record.field("build_identity_sha256", "SNAP")?,
        tagged_benchmark_hash_raw(binding.benchmark_sha256)?,
        "SNAP benchmark executable hash",
    )?;
    exact_text(
        record.field("cargo_lock_sha256", "SNAP")?,
        binding.benchmark_cargo_lock_sha256,
        "SNAP Cargo.lock hash",
    )?;
    exact_text(
        record.field("cargo_profile", "SNAP")?,
        binding.benchmark_cargo_profile,
        "SNAP profile",
    )?;
    exact_text(
        record.field("target", "SNAP")?,
        binding.benchmark_target,
        "SNAP target",
    )?;
    exact_text(
        record.field("rustc_vv", "SNAP")?,
        binding.benchmark_rustc_vv,
        "SNAP rustc identity",
    )?;
    exact_text(
        record.field("rustflags", "SNAP")?,
        binding.benchmark_rustflags,
        "SNAP rustflags",
    )?;
    exact_features(
        record.field("features", "SNAP")?,
        binding.benchmark_features,
        "SNAP features",
    )?;
    exact_text(
        record.field("harness_source_sha256", "SNAP")?,
        binding.benchmark_harness_source_sha256,
        "SNAP harness source hash",
    )?;
    exact_text(
        record.field("production_source_set_sha256", "SNAP")?,
        binding.benchmark_source_set_sha256,
        "SNAP benchmark source-set hash",
    )?;
    exact_text(
        record.field("measure_process_source_sha256", "SNAP")?,
        binding.benchmark_measure_process_source_sha256,
        "SNAP measurement source hash",
    )?;
    exact_text(
        record.field("measurement_mode", "SNAP")?,
        "detailed",
        "SNAP measurement mode",
    )?;
    exact_text(
        record.field("execution_lane", "SNAP")?,
        row.execution_lane.as_str(),
        "SNAP execution lane",
    )?;
    exact_text(
        record.field("artifact_mode", "SNAP")?,
        row.artifact_mode.as_str(),
        "SNAP artifact mode",
    )?;
    exact_text(
        record.field("fixture_profile", "SNAP")?,
        row.fixture_profile.as_str(),
        "SNAP fixture profile",
    )?;
    exact_natural(
        record.field("artifact_bytes", "SNAP")?,
        row.artifact_bytes,
        "SNAP artifact bytes",
    )?;
    let oracle = selected_oracle_row(oracle, row.fixture_profile.as_str())?;
    exact_text(
        record.field("fixture_descriptor_sha256", "SNAP")?,
        &oracle.descriptor_sha256,
        "SNAP fixture descriptor hash",
    )?;
    exact_text(
        record.field("fixture_logical_identity_sha256", "SNAP")?,
        &oracle.logical_identity_sha256,
        "SNAP fixture logical identity hash",
    )?;
    exact_text(
        record.field("fixture_tree_sha256", "SNAP")?,
        &oracle.artifact_tree_sha256,
        "SNAP fixture tree hash",
    )?;
    if oracle.certificate_bytes != row.artifact_bytes {
        return Err("SNAP manifest artifact bytes differ from the fixture oracle".to_owned());
    }
    exact_natural(
        record.field("warmup", "SNAP")?,
        row.common.warmup,
        "SNAP warmup",
    )?;
    exact_natural(
        record.field("manifest_samples", "SNAP")?,
        row.common.samples,
        "SNAP samples",
    )?;
    exact_natural(
        record.field("sample_index", "SNAP")?,
        execution.sample_index.ok_or("SNAP sample index missing")?,
        "SNAP sample index",
    )?;
    exact_text(
        record.field("interleave_group", "SNAP")?,
        &row.common.interleave_group,
        "SNAP interleave group",
    )?;
    exact_text(
        record.field("process_peak_rss_scope", "SNAP")?,
        "row-sample-child",
        "SNAP RSS scope",
    )?;
    for field in [
        "elapsed_ns",
        "acquisition_ns",
        "checker_ns",
        "allocation_events",
        "allocated_bytes",
    ] {
        record
            .field(field, "SNAP")?
            .natural(&format!("SNAP {field}"))?;
    }
    if completed {
        record
            .field("process_peak_rss_kib", "SNAP")?
            .natural("SNAP peak RSS")?;
        exact_natural(
            record.field("execution_ordinal", "SNAP")?,
            execution.ordinal as u64,
            "SNAP execution ordinal",
        )?;
    } else if record.field("process_peak_rss_kib", "SNAP")? != &OwnedJson::Null {
        return Err("raw SNAP peak RSS must be null".to_owned());
    }
    for field in [
        "build_identity_sha256",
        "cargo_lock_sha256",
        "harness_source_sha256",
        "production_source_set_sha256",
        "measure_process_source_sha256",
        "fixture_descriptor_sha256",
        "fixture_logical_identity_sha256",
        "fixture_tree_sha256",
    ] {
        if !valid_hash(record.field(field, "SNAP")?.text(field)?, false) {
            return Err(format!("SNAP {field} is not a raw SHA-256"));
        }
    }
    let (_, expected, _, _) = baseline_counters(baseline, &execution.scenario)?;
    validate_counter_object(record.field("deterministic_counters", "SNAP")?, &expected)?;
    Ok(())
}

fn validate_features(value: &OwnedJson) -> Result<(), String> {
    let values = value.array("features")?;
    let mut previous = None;
    for value in values {
        let feature = value.text("feature")?;
        if feature.is_empty() || previous.is_some_and(|previous: &str| previous >= feature) {
            return Err("features are empty, duplicate, or unordered".to_owned());
        }
        previous = Some(feature);
    }
    Ok(())
}

fn exact_features(value: &OwnedJson, expected: &str, label: &str) -> Result<(), String> {
    validate_features(value)?;
    let observed = value
        .array(label)?
        .iter()
        .map(|feature| feature.text(label))
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    if observed != expected {
        return Err(format!("{label} differ from the bound benchmark build"));
    }
    Ok(())
}

fn validate_counter_object(
    value: &OwnedJson,
    expected: &BTreeMap<String, u64>,
) -> Result<(), String> {
    let members = value
        .object_members()
        .ok_or("deterministic counters must be an object")?;
    if members.len() != expected.len() {
        return Err("deterministic counter set differs from baseline".to_owned());
    }
    for ((name, value), (expected_name, expected_value)) in members.iter().zip(expected) {
        if name != expected_name || value.natural("deterministic counter")? != *expected_value {
            return Err("deterministic counter set/value differs from baseline".to_owned());
        }
    }
    Ok(())
}

fn validate_vmsp_record(
    execution: &Execution,
    record: &OwnedJson,
    rows: &[PerformanceFixtureSelectionV02],
    baseline: &[u8],
    oracle: &[u8],
    binding: &AuditBinding<'_>,
    completed: bool,
) -> Result<(), String> {
    const RAW_KEYS: &[&str] = &[
        "schema",
        "trusted",
        "proof_evidence",
        "scenario",
        "fixture_manifest_hash",
        "baseline_hash",
        "source_identity",
        "build_identity_hash",
        "cargo_lock_hash",
        "rustc_vv",
        "cargo_profile",
        "features",
        "target",
        "rustflags",
        "harness_source_hash",
        "production_source_set_hash",
        "fixture_parser_source_hash",
        "measure_process_source_hash",
        "fixture_profile",
        "fixture_oracle",
        "measurement_mode",
        "warmup",
        "manifest_samples",
        "sample_count",
        "sample_index",
        "interleave_group",
        "interleave_order",
        "execution_order",
        "peak_rss_scope",
        "policies",
        "memo_limits",
        "counter_model",
        "samples",
        "elapsed_summary_ns",
        "peak_rss_kib",
        "elapsed_profile",
        "elapsed_gate",
        "status",
        "measurements",
    ];
    let mut keys = RAW_KEYS.to_vec();
    if completed {
        keys.push("execution_ordinal");
    }
    record.exact_object(&keys, "VMSP record")?;
    record.reject_absolute_strings("VMSP record")?;
    let row = rows
        .iter()
        .find(|row| row.id() == execution.scenario)
        .ok_or("VMSP scenario is absent from the manifest")?;
    let paired = matches!(
        row,
        PerformanceFixtureSelectionV02::SharedPayloadClone(_)
            | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
            | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
    );
    exact_text(
        record.field("schema", "VMSP")?,
        if paired {
            VMSP_SAMPLE_SCHEMA
        } else {
            VMSP_RUN_SCHEMA
        },
        "VMSP schema",
    )?;
    if record.field("trusted", "VMSP")?.boolean("trusted")?
        || record
            .field("proof_evidence", "VMSP")?
            .boolean("proof_evidence")?
    {
        return Err("VMSP diagnostic report claimed trust or proof evidence".to_owned());
    }
    exact_text(
        record.field("scenario", "VMSP")?,
        &execution.scenario,
        "VMSP scenario",
    )?;
    exact_text(
        record.field("fixture_manifest_hash", "VMSP")?,
        binding.manifest_sha256,
        "VMSP manifest hash",
    )?;
    exact_text(
        record.field("baseline_hash", "VMSP")?,
        binding.baseline_sha256,
        "VMSP baseline hash",
    )?;
    exact_text(
        record.field("source_identity", "VMSP")?,
        binding.source_identity,
        "VMSP source identity",
    )?;
    exact_text(
        record.field("build_identity_hash", "VMSP")?,
        tagged_benchmark_hash(binding.benchmark_sha256)?,
        "VMSP benchmark hash",
    )?;
    exact_text(
        record.field("cargo_lock_hash", "VMSP")?,
        &format!("sha256:{}", binding.benchmark_cargo_lock_sha256),
        "VMSP Cargo.lock hash",
    )?;
    exact_text(
        record.field("cargo_profile", "VMSP")?,
        binding.benchmark_cargo_profile,
        "VMSP profile",
    )?;
    exact_text(
        record.field("target", "VMSP")?,
        binding.benchmark_target,
        "VMSP target",
    )?;
    exact_text(
        record.field("rustc_vv", "VMSP")?,
        binding.benchmark_rustc_vv,
        "VMSP rustc identity",
    )?;
    exact_text(
        record.field("rustflags", "VMSP")?,
        binding.benchmark_rustflags,
        "VMSP rustflags",
    )?;
    exact_features(
        record.field("features", "VMSP")?,
        binding.benchmark_features,
        "VMSP features",
    )?;
    exact_text(
        record.field("harness_source_hash", "VMSP")?,
        binding.benchmark_harness_source_sha256,
        "VMSP harness source hash",
    )?;
    exact_text(
        record.field("production_source_set_hash", "VMSP")?,
        binding.benchmark_source_set_sha256,
        "VMSP benchmark source-set hash",
    )?;
    exact_text(
        record.field("fixture_parser_source_hash", "VMSP")?,
        binding
            .benchmark_fixture_parser_source_sha256
            .ok_or("VMSP benchmark fixture-parser binding is absent")?,
        "VMSP fixture-parser source hash",
    )?;
    exact_text(
        record.field("measure_process_source_hash", "VMSP")?,
        binding.benchmark_measure_process_source_sha256,
        "VMSP measurement source hash",
    )?;
    exact_text(
        record.field("measurement_mode", "VMSP")?,
        "detailed",
        "VMSP mode",
    )?;
    exact_natural(record.field("warmup", "VMSP")?, 1, "VMSP warmup")?;
    exact_natural(record.field("manifest_samples", "VMSP")?, 7, "VMSP samples")?;
    let common = vmsp_common(row)?;
    exact_text(
        record.field("fixture_profile", "VMSP")?,
        vmsp_profile(row)?,
        "VMSP fixture profile",
    )?;
    let oracle = selected_oracle_row(oracle, vmsp_profile(row)?)?;
    validate_vmsp_oracle_object(record.field("fixture_oracle", "VMSP")?, &oracle)?;
    exact_text(
        record.field("interleave_group", "VMSP")?,
        &common.interleave_group,
        "VMSP interleave group",
    )?;
    exact_text(
        record.field("counter_model", "VMSP")?,
        "operation-boundary-clone-spy-v1",
        "VMSP counter model",
    )?;
    if record.field("elapsed_profile", "VMSP")? != &OwnedJson::Null {
        return Err("VMSP elapsed profile must be null".to_owned());
    }
    exact_text(
        record.field("elapsed_gate", "VMSP")?,
        "advisory",
        "VMSP elapsed gate",
    )?;
    exact_text(record.field("status", "VMSP")?, "passed", "VMSP status")?;
    record.field("memo_limits", "VMSP")?.exact_object(
        &["max_entries", "max_weighted_certificate_bytes"],
        "VMSP memo limits",
    )?;
    exact_natural(
        record
            .field("memo_limits", "VMSP")?
            .field("max_entries", "memo limits")?,
        1024,
        "memo entry limit",
    )?;
    exact_natural(
        record
            .field("memo_limits", "VMSP")?
            .field("max_weighted_certificate_bytes", "memo limits")?,
        536_870_912,
        "memo byte limit",
    )?;
    validate_vmsp_policies(record.field("policies", "VMSP")?, row)?;
    let samples = record.field("samples", "VMSP")?.array("VMSP samples")?;
    let expected_count = if paired { 1 } else { 7 };
    if samples.len() != expected_count {
        return Err("VMSP sample population mismatch".to_owned());
    }
    for (position, sample) in samples.iter().enumerate() {
        validate_vmsp_sample(
            sample,
            if paired {
                execution
                    .sample_index
                    .ok_or("paired VMSP execution omits sample index")?
            } else {
                position as u64
            },
        )?;
    }
    validate_vmsp_elapsed_summary(record.field("elapsed_summary_ns", "VMSP")?, samples)?;
    if paired {
        exact_natural(
            record.field("sample_count", "VMSP")?,
            1,
            "VMSP sample_count",
        )?;
        exact_natural(
            record.field("sample_index", "VMSP")?,
            execution
                .sample_index
                .ok_or("paired VMSP execution omits sample index")?,
            "VMSP sample_index",
        )?;
        exact_text(
            record.field("interleave_order", "VMSP")?,
            "controller-sample-major-paired-parity",
            "VMSP interleave order",
        )?;
        exact_text(
            record.field("peak_rss_scope", "VMSP")?,
            "row-sample-child",
            "VMSP RSS scope",
        )?;
    } else {
        exact_natural(
            record.field("sample_count", "VMSP")?,
            7,
            "VMSP sample_count",
        )?;
        if record.field("sample_index", "VMSP")? != &OwnedJson::Null {
            return Err("single VMSP sample_index must be null".to_owned());
        }
        exact_text(
            record.field("interleave_order", "VMSP")?,
            "single-variant-sample-order",
            "VMSP interleave order",
        )?;
        exact_text(
            record.field("peak_rss_scope", "VMSP")?,
            "scenario-child",
            "VMSP RSS scope",
        )?;
    }
    if completed {
        record
            .field("peak_rss_kib", "VMSP")?
            .natural("VMSP peak RSS")?;
        exact_natural(
            record.field("execution_ordinal", "VMSP")?,
            execution.ordinal as u64,
            "VMSP ordinal",
        )?;
    } else if record.field("peak_rss_kib", "VMSP")? != &OwnedJson::Null {
        return Err("raw VMSP peak RSS must be null".to_owned());
    }
    validate_vmsp_measurements(
        record.field("measurements", "VMSP")?,
        baseline,
        &execution.scenario,
        &format!("sha256:{}", oracle.artifact_tree_sha256),
    )?;
    for field in [
        "fixture_manifest_hash",
        "baseline_hash",
        "build_identity_hash",
        "cargo_lock_hash",
        "harness_source_hash",
        "production_source_set_hash",
        "fixture_parser_source_hash",
        "measure_process_source_hash",
    ] {
        if !valid_hash(record.field(field, "VMSP")?.text(field)?, true) {
            return Err(format!("VMSP {field} is not a prefixed SHA-256"));
        }
    }
    Ok(())
}

fn vmsp_common(
    row: &PerformanceFixtureSelectionV02,
) -> Result<&npa_api::PerformanceFixtureCommonV02, String> {
    match row {
        PerformanceFixtureSelectionV02::SharedPayloadClone(row)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(row) => Ok(&row.common),
        PerformanceFixtureSelectionV02::SharedPayloadCache(row) => Ok(&row.common),
        PerformanceFixtureSelectionV02::SharedPayloadMemo(row) => Ok(&row.common),
        PerformanceFixtureSelectionV02::SharedPayloadSession(row) => Ok(&row.common),
        PerformanceFixtureSelectionV02::SharedPayloadShard(row) => Ok(&row.common),
        _ => Err("fixture is not VMSP".to_owned()),
    }
}

fn vmsp_profile(row: &PerformanceFixtureSelectionV02) -> Result<&'static str, String> {
    match row {
        PerformanceFixtureSelectionV02::SharedPayloadClone(row)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(row) => {
            Ok(row.fixture_profile.as_str())
        }
        PerformanceFixtureSelectionV02::SharedPayloadCache(row) => Ok(row.fixture_profile.as_str()),
        PerformanceFixtureSelectionV02::SharedPayloadMemo(row) => Ok(row.fixture_profile.as_str()),
        PerformanceFixtureSelectionV02::SharedPayloadSession(row) => {
            Ok(row.fixture_profile.as_str())
        }
        PerformanceFixtureSelectionV02::SharedPayloadShard(row) => Ok(row.fixture_profile.as_str()),
        _ => Err("fixture is not VMSP".to_owned()),
    }
}

fn validate_vmsp_oracle_object(value: &OwnedJson, expected: &OracleRow) -> Result<(), String> {
    value.exact_object(
        &[
            "generator_schema",
            "descriptor_sha256",
            "logical_identity_sha256",
            "artifact_tree_sha256",
            "module_count",
            "import_edge_count",
            "declaration_count",
            "name_table_entry_count",
            "level_table_node_count",
            "term_table_node_count",
            "tree_file_count",
            "certificate_bytes",
        ],
        "VMSP fixture oracle",
    )?;
    for (field, expected_value) in [
        ("generator_schema", expected.generator_schema.as_str()),
        ("descriptor_sha256", expected.descriptor_sha256.as_str()),
        (
            "logical_identity_sha256",
            expected.logical_identity_sha256.as_str(),
        ),
        (
            "artifact_tree_sha256",
            expected.artifact_tree_sha256.as_str(),
        ),
    ] {
        exact_text(
            value.field(field, "VMSP fixture oracle")?,
            expected_value,
            &format!("VMSP fixture oracle {field}"),
        )?;
    }
    for (field, expected_value) in [
        ("module_count", expected.module_count),
        ("import_edge_count", expected.import_edge_count),
        ("declaration_count", expected.declaration_count),
        ("name_table_entry_count", expected.name_table_entry_count),
        ("level_table_node_count", expected.level_table_node_count),
        ("term_table_node_count", expected.term_table_node_count),
        ("tree_file_count", expected.tree_file_count),
        ("certificate_bytes", expected.certificate_bytes),
    ] {
        exact_natural(
            value.field(field, "VMSP fixture oracle")?,
            expected_value,
            &format!("VMSP fixture oracle {field}"),
        )?;
    }
    Ok(())
}

fn validate_vmsp_policies(
    value: &OwnedJson,
    row: &PerformanceFixtureSelectionV02,
) -> Result<(), String> {
    let expected = match row {
        PerformanceFixtureSelectionV02::SharedPayloadClone(row)
        | PerformanceFixtureSelectionV02::SharedPayloadSmall(row) => object([
            ("implementation", string(row.implementation.as_str())),
            ("decode_cache_policy", string("disabled")),
            ("process_memo_policy", string("disabled")),
            ("jobs", number(1)),
        ]),
        PerformanceFixtureSelectionV02::SharedPayloadCache(row) => object([
            ("implementation", string("shared-handle")),
            ("phase", string(row.phase.as_str())),
            (
                "decode_cache_policy",
                string(row.decode_cache_policy.as_str()),
            ),
            ("process_memo_policy", string("disabled")),
            ("jobs", number(1)),
        ]),
        PerformanceFixtureSelectionV02::SharedPayloadMemo(row) => object([
            ("implementation", string("shared-handle")),
            ("phase", string(row.phase.as_str())),
            (
                "decode_cache_policy",
                string(row.decode_cache_policy.as_str()),
            ),
            (
                "process_memo_policy",
                string(row.process_memo_policy.as_str()),
            ),
            ("jobs", number(row.jobs)),
        ]),
        PerformanceFixtureSelectionV02::SharedPayloadSession(row) => object([
            ("implementation", string(row.implementation.as_str())),
            ("phase", string(row.phase.as_str())),
            ("decode_cache_policy", string("disabled")),
            ("process_memo_policy", string("disabled")),
            ("jobs", number(1)),
        ]),
        PerformanceFixtureSelectionV02::SharedPayloadShard(row) => object([
            ("implementation", string("shared-handle")),
            (
                "decode_cache_policy",
                string(row.decode_cache_policy.as_str()),
            ),
            (
                "process_memo_policy",
                string(row.process_memo_policy.as_str()),
            ),
            ("jobs", number(row.jobs)),
        ]),
        _ => return Err("fixture is not VMSP".to_owned()),
    };
    if value != &expected {
        return Err("VMSP policies differ from the selected fixture".to_owned());
    }
    Ok(())
}

fn validate_vmsp_sample(sample: &OwnedJson, index: u64) -> Result<(), String> {
    sample.exact_object(&["index", "elapsed_ns", "blocking_counters"], "VMSP sample")?;
    exact_natural(sample.field("index", "sample")?, index, "VMSP sample index")?;
    sample
        .field("elapsed_ns", "sample")?
        .natural("VMSP elapsed_ns")?;
    let counters = sample.field("blocking_counters", "sample")?;
    counters.exact_object(
        &[
            "payload_allocations",
            "payload_copied_bytes",
            "payload_handle_clones",
            "avoided_payload_clone_bytes",
            "physical_decodes",
            "decode_cache_retained_bytes",
            "decode_cache_capacity_stops",
            "process_memo_payload_handle_clones",
            "session_snapshot_clones",
            "session_index_cow_copies",
            "session_index_cow_entries",
            "worker_count",
        ],
        "VMSP blocking counters",
    )?;
    for (_, value) in counters
        .object_members()
        .ok_or("VMSP blocking counters must be an object")?
    {
        value.natural("VMSP blocking counter")?;
    }
    Ok(())
}

fn validate_vmsp_elapsed_summary(summary: &OwnedJson, samples: &[OwnedJson]) -> Result<(), String> {
    summary.exact_object(
        &["median", "median_absolute_deviation", "minimum", "maximum"],
        "VMSP elapsed summary",
    )?;
    let values = samples
        .iter()
        .map(|sample| sample.field("elapsed_ns", "sample")?.natural("elapsed_ns"))
        .collect::<Result<Vec<_>, String>>()?;
    let expected = vmsp_summary(&values)?;
    if summary != &expected {
        return Err("VMSP elapsed summary is not derived from samples".to_owned());
    }
    Ok(())
}

fn validate_vmsp_measurements(
    value: &OwnedJson,
    baseline: &[u8],
    scenario: &str,
    expected_input_identity: &str,
) -> Result<(), String> {
    value.exact_object(
        &[
            "schema",
            "trusted",
            "proof_evidence",
            "mode",
            "input_identity",
            "counters",
            "modules",
            "module_details",
            "declarations",
            "declaration_details",
            "candidates",
            "candidate_details",
            "workers",
            "worker_details",
            "package_sharding",
            "package_layers",
            "package_layer_details",
            "package_shards",
            "package_shard_details",
            "detail_truncated",
            "overflowed",
            "clock",
        ],
        "VMSP measurements",
    )?;
    exact_text(
        value.field("schema", "measurements")?,
        MEASUREMENT_SCHEMA,
        "measurement schema",
    )?;
    exact_text(
        value.field("mode", "measurements")?,
        "detailed",
        "measurement mode",
    )?;
    if value
        .field("trusted", "measurements")?
        .boolean("measurement trusted")?
        || value
            .field("proof_evidence", "measurements")?
            .boolean("measurement proof_evidence")?
        || value
            .field("overflowed", "measurements")?
            .boolean("measurement overflowed")?
    {
        return Err("VMSP measurement trust/overflow contract failed".to_owned());
    }
    exact_text(
        value.field("input_identity", "measurements")?,
        expected_input_identity,
        "VMSP measurement input identity",
    )?;
    let (module_count, expected, live_min, reduction_allowed) =
        baseline_counters(baseline, scenario)?;
    validate_vmsp_measurement_counters(
        value.field("counters", "measurements")?,
        &expected,
        module_count,
        live_min,
        reduction_allowed,
    )?;
    validate_measurement_detail_shapes(value)
}

fn validate_vmsp_measurement_counters(
    counters: &OwnedJson,
    expected: &BTreeMap<String, u64>,
    module_count: u64,
    live_min: u64,
    reduction_allowed: bool,
) -> Result<(), String> {
    let counters = counters.array("measurement counters")?;
    let mut promoted = BTreeMap::new();
    let mut coverage = BTreeMap::new();
    let mut previous = None;
    for counter in counters {
        counter.exact_object(&["label", "unit", "value"], "measurement counter")?;
        let label = counter.field("label", "counter")?.text("counter label")?;
        if previous.is_some_and(|previous: &str| previous >= label) {
            return Err("measurement counters are duplicate or unordered".to_owned());
        }
        previous = Some(label);
        let unit = counter.field("unit", "counter")?.text("counter unit")?;
        let stable_label =
            PerformanceMeasurementLabel::from_schema_identifier(MEASUREMENT_SCHEMA, label)
                .ok_or_else(|| {
                    format!("measurement counter {label} is not stable for {MEASUREMENT_SCHEMA}")
                })?;
        if unit != stable_label.unit().as_str() {
            return Err("measurement counter unit is invalid".to_owned());
        }
        let amount = counter
            .field("value", "counter")?
            .natural("counter value")?;
        if matches!(
            label,
            "package.live_results" | "package.cache_results" | "package.memo_results"
        ) {
            coverage.insert(label.to_owned(), amount);
        } else if expected.contains_key(label) {
            promoted.insert(label.to_owned(), amount);
        }
    }
    if &promoted != expected || (!coverage.is_empty() && coverage.len() != 3) {
        return Err("VMSP measurement counters differ from the exact baseline".to_owned());
    }
    if !coverage.is_empty() {
        let live = coverage["package.live_results"];
        let cache = coverage["package.cache_results"];
        let memo = coverage["package.memo_results"];
        let covered = live
            .checked_add(cache)
            .and_then(|total| total.checked_add(memo))
            .ok_or("VMSP measurement coverage counter sum overflowed")?;
        if covered != module_count
            || live < live_min
            || (!reduction_allowed && (live != module_count || cache != 0 || memo != 0))
        {
            return Err("VMSP measurement coverage violates the baseline".to_owned());
        }
    } else if module_count != 0 {
        return Err("VMSP measurement omitted nonzero coverage counters".to_owned());
    }
    Ok(())
}

fn validate_measurement_detail_shapes(value: &OwnedJson) -> Result<(), String> {
    for field in [
        "modules",
        "declarations",
        "candidates",
        "workers",
        "package_layers",
        "package_shards",
    ] {
        value.field(field, "measurements")?.array(field)?;
    }
    for field in [
        "module_details",
        "declaration_details",
        "candidate_details",
        "worker_details",
        "package_layer_details",
        "package_shard_details",
    ] {
        let detail = value.field(field, "measurements")?;
        detail.exact_object(&["attempted", "retained", "omitted"], field)?;
        let attempted = detail
            .field("attempted", field)?
            .natural("detail attempted")?;
        let retained = detail
            .field("retained", field)?
            .natural("detail retained")?;
        let omitted = detail.field("omitted", field)?.natural("detail omitted")?;
        if retained.checked_add(omitted) != Some(attempted) {
            return Err("measurement detail counts are inconsistent".to_owned());
        }
    }
    value
        .field("detail_truncated", "measurements")?
        .boolean("detail_truncated")?;
    let clock = value.field("clock", "measurements")?;
    clock.exact_object(
        &["source", "resolution_ns", "coarse_stage_reads"],
        "measurement clock",
    )?;
    if clock
        .field("source", "clock")?
        .text("clock source")?
        .is_empty()
    {
        return Err("measurement clock source is empty".to_owned());
    }
    clock
        .field("resolution_ns", "clock")?
        .natural("clock resolution")?;
    clock
        .field("coarse_stage_reads", "clock")?
        .natural("clock reads")?;
    Ok(())
}

pub fn build_matrix(
    kind: LaneKind,
    executions: &[Execution],
    completed: &[OwnedJson],
    rows: &[PerformanceFixtureSelectionV02],
    binding: &AuditBinding<'_>,
) -> Result<Box<[u8]>, String> {
    tagged_benchmark_hash(binding.benchmark_sha256)?;
    if executions.len() != kind.execution_count() || completed.len() != executions.len() {
        return Err("SNAP/VMSP completed execution population mismatch".to_owned());
    }
    let matrix_rows = match kind {
        LaneKind::Snapshot => build_snapshot_rows(executions, completed, rows)?,
        LaneKind::SharedPayload => build_vmsp_rows(executions, completed, rows)?,
    };
    let execution_order = executions
        .iter()
        .zip(completed)
        .map(|(execution, record)| match kind {
            LaneKind::Snapshot => Ok(object([
                ("ordinal", number(execution.ordinal as u64)),
                ("scenario_id", string(&execution.scenario)),
                (
                    "sample_index",
                    number(
                        execution
                            .sample_index
                            .ok_or("SNAP execution omits sample index")?,
                    ),
                ),
                (
                    "artifact_mode",
                    record.field("artifact_mode", "record")?.clone(),
                ),
                (
                    "interleave_group",
                    record.field("interleave_group", "record")?.clone(),
                ),
            ])),
            LaneKind::SharedPayload => Ok(object([
                ("ordinal", number(execution.ordinal as u64)),
                ("scenario", string(&execution.scenario)),
                (
                    "sample_index",
                    execution.sample_index.map_or(OwnedJson::Null, number),
                ),
                ("implementation", vmsp_implementation(record)?),
                (
                    "interleave_group",
                    record.field("interleave_group", "record")?.clone(),
                ),
            ])),
        })
        .collect::<Result<Vec<_>, String>>()?;
    let matrix = object([
        ("schema", string(kind.matrix_schema())),
        ("inputs", object([
            ("fixture_manifest_sha256", string(binding.manifest_sha256)),
            ("baseline_sha256", string(binding.baseline_sha256)),
            ("oracle_sha256", string(binding.oracle_sha256)),
        ])),
        ("executables", object([
            ("benchmark_sha256", string(binding.benchmark_sha256)),
            ("manager_sha256", string(binding.manager_sha256)),
        ])),
        ("build", object([
            ("source_identity", string(binding.source_identity)),
            ("manager", object([
                ("cargo_lock_sha256", string(format!("sha256:{}", binding.manager_cargo_lock_sha256))),
                ("source_set_sha256", string(binding.manager_source_set_sha256)),
                ("source_sha256", string(binding.manager_source_sha256)),
                ("cargo_profile", string(binding.manager_cargo_profile)),
                ("features", string(binding.manager_features)),
                ("target", string(binding.manager_target)),
                ("rustc_vv", string(binding.manager_rustc_vv)),
                ("rustflags", string(binding.manager_rustflags)),
            ])),
            ("benchmark", object([
                ("cargo_lock_sha256", string(format!("sha256:{}", binding.benchmark_cargo_lock_sha256))),
                ("source_set_sha256", string(binding.benchmark_source_set_sha256)),
                ("harness_source_sha256", string(binding.benchmark_harness_source_sha256)),
                ("fixture_parser_source_sha256", binding.benchmark_fixture_parser_source_sha256.map_or(OwnedJson::Null, string)),
                ("measure_process_source_sha256", string(binding.benchmark_measure_process_source_sha256)),
                ("cargo_profile", string(binding.benchmark_cargo_profile)),
                ("features", string(binding.benchmark_features)),
                ("target", string(binding.benchmark_target)),
                ("rustc_vv", string(binding.benchmark_rustc_vv)),
                ("rustflags", string(binding.benchmark_rustflags)),
            ])),
        ])),
        ("interleave", string(match kind {
            LaneKind::Snapshot => "row-sample-child/controller-sample-major-group-major-raw-snapshot-alternating-parity",
            LaneKind::SharedPayload => "paired-row-sample-child/controller-sample-major-group-major-legacy-shared-alternating-parity;single-row-scenario-child",
        })),
        ("execution_order", OwnedJson::Array(execution_order)),
        ("rows", OwnedJson::Array(matrix_rows)),
    ]);
    Ok(matrix.canonical_boxed_line())
}

fn build_snapshot_rows(
    executions: &[Execution],
    completed: &[OwnedJson],
    rows: &[PerformanceFixtureSelectionV02],
) -> Result<Vec<OwnedJson>, String> {
    let mut grouped = BTreeMap::<String, Vec<(&Execution, &OwnedJson)>>::new();
    for (execution, record) in executions.iter().zip(completed) {
        grouped
            .entry(execution.scenario.clone())
            .or_default()
            .push((execution, record));
    }
    rows.iter()
        .filter_map(|fixture| match fixture {
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(row) => Some(&row.common.id),
            _ => None,
        })
        .map(|scenario| {
            let samples = grouped.get(scenario).ok_or("SNAP matrix row missing")?;
            if samples.len() != 5 {
                return Err("SNAP matrix row must contain five samples".to_owned());
            }
            let mut row = samples[0].1.clone();
            row.remove_fields(&[
                "schema",
                "sample_index",
                "manifest_samples",
                "execution_ordinal",
                "elapsed_ns",
                "acquisition_ns",
                "checker_ns",
                "allocation_events",
                "allocated_bytes",
                "process_peak_rss_kib",
            ])?;
            row.push_field("schema", string(SNAP_RUN_SCHEMA))?;
            row.push_field("samples", number(5))?;
            row.push_field(
                "interleave_order",
                string("controller-sample-major-group-major-raw-snapshot-alternating-parity"),
            )?;
            row.push_field(
                "execution_order",
                OwnedJson::Array(
                    samples
                        .iter()
                        .map(|(execution, record)| {
                            Ok(object([
                                ("ordinal", number(execution.ordinal as u64)),
                                (
                                    "sample_index",
                                    number(
                                        execution
                                            .sample_index
                                            .ok_or("SNAP sample index missing")?,
                                    ),
                                ),
                                (
                                    "artifact_mode",
                                    record.field("artifact_mode", "SNAP record")?.clone(),
                                ),
                            ]))
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                ),
            )?;
            for field in [
                "elapsed_ns",
                "acquisition_ns",
                "checker_ns",
                "allocation_events",
                "allocated_bytes",
            ] {
                row.push_field(
                    field,
                    OwnedJson::Array(
                        samples
                            .iter()
                            .map(|(_, record)| record.field(field, "SNAP record").cloned())
                            .collect::<Result<Vec<_>, String>>()?,
                    ),
                )?;
            }
            let peak = samples
                .iter()
                .map(|(_, record)| {
                    record
                        .field("process_peak_rss_kib", "SNAP record")?
                        .natural("peak")
                })
                .collect::<Result<Vec<_>, String>>()?;
            row.push_field(
                "sample_process_peak_rss_kib",
                OwnedJson::Array(peak.iter().copied().map(number).collect()),
            )?;
            row.push_field(
                "process_peak_rss_kib",
                number(*peak.iter().max().ok_or("SNAP peak population is empty")?),
            )?;
            for (source, target) in [
                ("elapsed_ns", "elapsed_summary"),
                ("acquisition_ns", "acquisition_summary"),
                ("checker_ns", "checker_summary"),
                ("allocation_events", "allocation_event_summary"),
                ("allocated_bytes", "allocated_byte_summary"),
            ] {
                let values = samples
                    .iter()
                    .map(|(_, record)| record.field(source, "SNAP record")?.natural(source))
                    .collect::<Result<Vec<_>, String>>()?;
                row.push_field(target, snapshot_summary(&values)?)?;
            }
            Ok(row)
        })
        .collect()
}

fn build_vmsp_rows(
    executions: &[Execution],
    completed: &[OwnedJson],
    rows: &[PerformanceFixtureSelectionV02],
) -> Result<Vec<OwnedJson>, String> {
    let mut grouped = BTreeMap::<String, Vec<(&Execution, &OwnedJson)>>::new();
    for (execution, record) in executions.iter().zip(completed) {
        grouped
            .entry(execution.scenario.clone())
            .or_default()
            .push((execution, record));
    }
    rows.iter()
        .filter(|fixture| {
            matches!(
                fixture,
                PerformanceFixtureSelectionV02::SharedPayloadClone(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadCache(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadMemo(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadShard(_)
                    | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
            )
        })
        .map(|fixture| {
            let samples = grouped.get(fixture.id()).ok_or("VMSP matrix row missing")?;
            if samples.len() == 1 && samples[0].0.sample_index.is_none() {
                return Ok(samples[0].1.clone());
            }
            if samples.len() != 7 {
                return Err("paired VMSP row must contain seven samples".to_owned());
            }
            let mut row = samples[0].1.clone();
            row.remove_fields(&[
                "schema",
                "sample_index",
                "sample_count",
                "execution_ordinal",
                "samples",
                "elapsed_summary_ns",
                "interleave_order",
                "execution_order",
                "peak_rss_scope",
                "peak_rss_kib",
            ])?;
            row.push_field("schema", string(VMSP_RUN_SCHEMA))?;
            row.push_field("sample_count", number(7))?;
            row.push_field(
                "interleave_order",
                string("controller-sample-major-group-major-legacy-shared-alternating-parity"),
            )?;
            row.push_field(
                "execution_order",
                OwnedJson::Array(
                    samples
                        .iter()
                        .map(|(execution, record)| {
                            Ok(object([
                                ("ordinal", number(execution.ordinal as u64)),
                                (
                                    "sample_index",
                                    number(
                                        execution
                                            .sample_index
                                            .ok_or("VMSP sample index missing")?,
                                    ),
                                ),
                                ("implementation", vmsp_implementation(record)?),
                            ]))
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                ),
            )?;
            row.push_field("peak_rss_scope", string("row-sample-child"))?;
            let peaks = samples
                .iter()
                .map(|(_, record)| record.field("peak_rss_kib", "VMSP record")?.natural("peak"))
                .collect::<Result<Vec<_>, String>>()?;
            row.push_field(
                "sample_peak_rss_kib",
                OwnedJson::Array(peaks.iter().copied().map(number).collect()),
            )?;
            row.push_field(
                "peak_rss_kib",
                number(*peaks.iter().max().ok_or("VMSP peak population is empty")?),
            )?;
            let sample_values = samples
                .iter()
                .map(|(_, record)| {
                    record
                        .field("samples", "VMSP record")?
                        .array("samples")?
                        .first()
                        .cloned()
                        .ok_or_else(|| "VMSP sample population is empty".to_owned())
                })
                .collect::<Result<Vec<_>, String>>()?;
            row.push_field("samples", OwnedJson::Array(sample_values.clone()))?;
            let elapsed = sample_values
                .iter()
                .map(|sample| sample.field("elapsed_ns", "sample")?.natural("elapsed"))
                .collect::<Result<Vec<_>, String>>()?;
            row.push_field("elapsed_summary_ns", vmsp_summary(&elapsed)?)?;
            Ok(row)
        })
        .collect()
}

fn vmsp_implementation(record: &OwnedJson) -> Result<OwnedJson, String> {
    record
        .field("policies", "VMSP record")
        .and_then(|policies| policies.field("implementation", "policies"))
        .cloned()
}

fn snapshot_summary(values: &[u64]) -> Result<OwnedJson, String> {
    if values.is_empty() {
        return Err("SNAP summary population is empty".to_owned());
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let median = sorted[sorted.len() / 2];
    let mut deviations = values
        .iter()
        .map(|value| value.abs_diff(median))
        .collect::<Vec<_>>();
    deviations.sort_unstable();
    Ok(object([
        ("median", number(median)),
        ("mad", number(deviations[deviations.len() / 2])),
        ("min", number(sorted[0])),
        (
            "max",
            number(*sorted.last().ok_or("SNAP summary population is empty")?),
        ),
    ]))
}

fn vmsp_summary(values: &[u64]) -> Result<OwnedJson, String> {
    if values.is_empty() {
        return Err("VMSP summary population is empty".to_owned());
    }
    let median_value = median(values)?;
    let deviations = values
        .iter()
        .map(|value| value.abs_diff(median_value))
        .collect::<Vec<_>>();
    Ok(object([
        ("median", number(median_value)),
        ("median_absolute_deviation", number(median(&deviations)?)),
        (
            "minimum",
            number(
                *values
                    .iter()
                    .min()
                    .ok_or("VMSP summary population is empty")?,
            ),
        ),
        (
            "maximum",
            number(
                *values
                    .iter()
                    .max()
                    .ok_or("VMSP summary population is empty")?,
            ),
        ),
    ]))
}

fn median(values: &[u64]) -> Result<u64, String> {
    if values.is_empty() {
        return Err("median population is empty".to_owned());
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let middle = sorted.len() / 2;
    if sorted.len() % 2 == 1 {
        Ok(sorted[middle])
    } else {
        Ok(sorted[middle - 1] / 2
            + sorted[middle] / 2
            + (sorted[middle - 1] % 2 + sorted[middle] % 2) / 2)
    }
}

pub fn validate_matrix(
    kind: LaneKind,
    matrix_bytes: &[u8],
    executions: &[Execution],
    completed: &[OwnedJson],
    rows: &[PerformanceFixtureSelectionV02],
    binding: &AuditBinding<'_>,
) -> Result<(), String> {
    let parsed = OwnedJson::parse_canonical_line(matrix_bytes, "sealed matrix")?;
    if parsed.retained_bytes()? > MAX_SEMANTIC_STRUCTURE_BYTES {
        return Err("sealed matrix exceeds its structural-memory bound".to_owned());
    }
    parsed.exact_object(
        &[
            "schema",
            "inputs",
            "executables",
            "build",
            "interleave",
            "execution_order",
            "rows",
        ],
        "sealed matrix",
    )?;
    let expected = build_matrix(kind, executions, completed, rows, binding)?;
    if expected.as_ref() != matrix_bytes {
        return Err("sealed matrix is not the exact strict semantic reconstruction".to_owned());
    }
    Ok(())
}

fn push_json_string(output: &mut String, value: &str) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                if write!(output, "\\u{:04x}", character as u32).is_err() {
                    // `String`'s formatter is infallible. Preserve the
                    // panic-free external-data contract even if that invariant
                    // changes in the standard library.
                    return;
                }
            }
            character => output.push(character),
        }
    }
    output.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    const RAW_TEST_HASH: &str = "0000000000000000000000000000000000000000000000000000000000000000";
    const TAGGED_TEST_HASH: &str =
        "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    fn test_binding(benchmark_sha256: &str) -> AuditBinding<'_> {
        AuditBinding {
            source_identity: "0000000000000000000000000000000000000000-dirty",
            manifest_sha256: TAGGED_TEST_HASH,
            baseline_sha256: TAGGED_TEST_HASH,
            oracle_sha256: TAGGED_TEST_HASH,
            benchmark_sha256,
            manager_sha256: TAGGED_TEST_HASH,
            manager_source_set_sha256: TAGGED_TEST_HASH,
            manager_source_sha256: RAW_TEST_HASH,
            manager_cargo_lock_sha256: RAW_TEST_HASH,
            manager_cargo_profile: "release",
            manager_target: "aarch64-apple-darwin",
            manager_features: "",
            manager_rustc_vv: "rustc test",
            manager_rustflags: "",
            benchmark_cargo_lock_sha256: RAW_TEST_HASH,
            benchmark_cargo_profile: "release",
            benchmark_target: "aarch64-apple-darwin",
            benchmark_features: "",
            benchmark_rustc_vv: "rustc test",
            benchmark_rustflags: "",
            benchmark_harness_source_sha256: RAW_TEST_HASH,
            benchmark_source_set_sha256: TAGGED_TEST_HASH,
            benchmark_fixture_parser_source_sha256: None,
            benchmark_measure_process_source_sha256: RAW_TEST_HASH,
        }
    }

    fn representative_snapshot_raw_shape() -> OwnedJson {
        let hash = "a".repeat(64);
        let counters = object([
            ("package.artifact_file_hashes", number(1)),
            ("package.artifact_files_read", number(0)),
            ("package.artifact_full_decodes", number(2)),
            ("package.artifact_prepared_reuses", number(0)),
            ("package.prepared_artifact_admissions", number(0)),
            ("package.prepared_artifact_admitted_bytes", number(0)),
            ("package.prepared_artifact_byte_limit_fallbacks", number(0)),
            ("package.prepared_artifact_current_bytes", number(0)),
            ("package.prepared_artifact_current_entries", number(0)),
            (
                "package.prepared_artifact_derivation_current_bytes",
                number(0),
            ),
            ("package.prepared_artifact_derivation_peak_bytes", number(0)),
            ("package.prepared_artifact_entry_limit_fallbacks", number(0)),
            ("package.prepared_artifact_key_current_bytes", number(0)),
            ("package.prepared_artifact_key_peak_bytes", number(0)),
            ("package.prepared_artifact_peak_bytes", number(0)),
            ("package.prepared_artifact_peak_entries", number(0)),
            ("package.prepared_artifact_released_bytes", number(0)),
            ("package.prepared_artifact_releases", number(0)),
            (
                "package.prepared_artifact_saturated_charge_fallbacks",
                number(0),
            ),
        ]);
        object([
            ("schema", string(SNAP_SAMPLE_SCHEMA)),
            (
                "scenario_id",
                string("package-artifact-snapshot-1k-api-pm0-dc0-fast-raw-j1"),
            ),
            (
                "source_identity",
                string("d6e67f0ee1b1e43d6c2b5e6ca2b245aee216e58e-dirty"),
            ),
            ("build_identity_sha256", string(hash.clone())),
            ("cargo_lock_sha256", string(hash.clone())),
            (
                "rustc_vv",
                string(
                    "rustc 1.97.1 (8bab26f4f 2026-07-14)\nbinary: rustc\ncommit-hash: 8bab26f4f68e0e26f0bb7960be334d5b520ea452\ncommit-date: 2026-07-14\nhost: aarch64-apple-darwin\nrelease: 1.97.1\nLLVM version: 22.1.6\n",
                ),
            ),
            ("cargo_profile", string("release")),
            ("features", OwnedJson::Array(Vec::new())),
            ("target", string("aarch64-apple-darwin")),
            ("rustflags", string("")),
            ("harness_source_sha256", string(hash.clone())),
            (
                "production_source_set_sha256",
                string(format!("sha256:{hash}")),
            ),
            ("measure_process_source_sha256", string(hash.clone())),
            ("measurement_mode", string("detailed")),
            ("warmup", number(1)),
            ("manifest_samples", number(5)),
            ("sample_index", number(0)),
            ("process_peak_rss_kib", number(0)),
            ("process_peak_rss_scope", string("child-wait4-maxrss")),
            ("fixture_profile", string("snapshot-1k")),
            ("fixture_descriptor_sha256", string(hash.clone())),
            ("fixture_logical_identity_sha256", string(hash.clone())),
            ("fixture_tree_sha256", string(hash)),
            ("artifact_mode", string("raw")),
            ("execution_lane", string("api")),
            ("interleave_group", string("pm0-dc0-fast-j1")),
            ("elapsed_ns", number(1)),
            ("acquisition_ns", number(1)),
            ("checker_ns", number(1)),
            ("artifact_bytes", number(1)),
            ("allocated_bytes", number(1)),
            ("allocation_events", number(1)),
            ("deterministic_counters", counters),
        ])
    }

    #[test]
    fn owned_json_requires_exact_canonical_line() {
        let value = OwnedJson::parse_canonical_line(b"{\"a\":1,\"b\":\"x\"}\n", "test").unwrap();
        assert_eq!(value.canonical_line(), "{\"a\":1,\"b\":\"x\"}\n");
        assert_eq!(
            value.canonical_boxed_line().as_ref(),
            b"{\"a\":1,\"b\":\"x\"}\n"
        );
        assert!(OwnedJson::parse_canonical_line(b"{ \"a\":1}\n", "test").is_err());
        assert!(OwnedJson::parse_canonical_line(b"{\"a\":1,\"a\":1}\n", "test").is_err());
    }

    #[test]
    fn benchmark_binding_is_tagged_with_explicit_raw_snapshot_projection() {
        assert_eq!(
            tagged_benchmark_hash_raw(TAGGED_TEST_HASH),
            Ok(RAW_TEST_HASH)
        );
        assert_eq!(
            tagged_benchmark_hash(TAGGED_TEST_HASH),
            Ok(TAGGED_TEST_HASH)
        );
        assert!(tagged_benchmark_hash_raw(RAW_TEST_HASH).is_err());
        assert!(tagged_benchmark_hash(RAW_TEST_HASH).is_err());
        assert!(tagged_benchmark_hash_raw(&format!("sha256:{TAGGED_TEST_HASH}")).is_err());

        let raw_binding = test_binding(RAW_TEST_HASH);
        let error = build_matrix(LaneKind::Snapshot, &[], &[], &[], &raw_binding).unwrap_err();
        assert!(error.contains("sha256:<hex>"));

        let tagged_binding = test_binding(TAGGED_TEST_HASH);
        assert_eq!(
            build_matrix(LaneKind::SharedPayload, &[], &[], &[], &tagged_binding),
            Err("SNAP/VMSP completed execution population mismatch".to_owned())
        );
    }

    #[test]
    fn snapshot_completed_and_matrix_shapes_use_exact_boxed_allocations() {
        let raw = representative_snapshot_raw_shape();
        let raw_bytes = raw.canonical_boxed_line();
        assert!((2_000..4_000).contains(&raw_bytes.len()));
        let mut completed = raw;
        completed
            .push_field("execution_ordinal", number(0))
            .unwrap();
        let completed_bytes: Box<[u8]> = completed.canonical_boxed_line();
        let completed_limit = completed_record_byte_reservation(raw_bytes.len() as u64).unwrap();
        assert!(completed_bytes.len() as u64 <= completed_limit);

        let execution = object([
            ("ordinal", number(0)),
            (
                "scenario_id",
                string("package-artifact-snapshot-1k-api-pm0-dc0-fast-raw-j1"),
            ),
            ("sample_index", number(0)),
            ("artifact_mode", string("raw")),
            ("interleave_group", string("pm0-dc0-fast-j1")),
        ]);
        let row = object([
            (
                "scenario_id",
                string("package-artifact-snapshot-1k-api-pm0-dc0-fast-raw-j1"),
            ),
            ("samples", OwnedJson::Array(vec![completed; 5])),
        ]);
        let matrix_shape = object([
            ("schema", string(SNAP_MATRIX_SCHEMA)),
            (
                "execution_order",
                OwnedJson::Array(vec![execution; LaneKind::Snapshot.execution_count()]),
            ),
            ("rows", OwnedJson::Array(vec![row; 40])),
        ]);
        let matrix_bytes: Box<[u8]> = matrix_shape.canonical_boxed_line();
        assert!(matrix_bytes.len() as u64 <= MAX_CANONICAL_JSON_BYTES);
        assert!(matrix_bytes.len() > completed_bytes.len());
    }

    #[test]
    fn paired_vmsp_samples_replace_sample_metadata_when_building_the_run_row() {
        let manifest = npa_api::validate_checked_performance_fixture_selection_v02(include_str!(
            "../../../../testdata/performance/fixtures/manifest.v0.2.json"
        ))
        .unwrap();
        let fixture = manifest
            .scenarios
            .iter()
            .find(|fixture| fixture.id() == "shared-payload-clone-1m-c1-legacy")
            .unwrap();
        let executions = (0..7)
            .map(|index| Execution {
                ordinal: index,
                scenario: fixture.id().to_owned(),
                sample_index: Some(index as u64),
                suffix: format!("sample-{index}"),
            })
            .collect::<Vec<_>>();
        let records = (0..7)
            .map(|index| {
                object([
                    ("schema", string(VMSP_SAMPLE_SCHEMA)),
                    ("sample_index", number(index)),
                    ("sample_count", number(1)),
                    ("execution_ordinal", number(index)),
                    (
                        "samples",
                        OwnedJson::Array(vec![object([("elapsed_ns", number(index + 1))])]),
                    ),
                    (
                        "elapsed_summary_ns",
                        object([
                            ("median", number(index + 1)),
                            ("median_absolute_deviation", number(0)),
                            ("minimum", number(index + 1)),
                            ("maximum", number(index + 1)),
                        ]),
                    ),
                    (
                        "interleave_order",
                        string("controller-sample-major-paired-parity"),
                    ),
                    (
                        "execution_order",
                        OwnedJson::Array(vec![string(format!("{index}:{}", fixture.id()))]),
                    ),
                    ("peak_rss_scope", string("row-sample-child")),
                    ("peak_rss_kib", number(100 + index)),
                    (
                        "policies",
                        object([("implementation", string("legacy-model"))]),
                    ),
                ])
            })
            .collect::<Vec<_>>();

        let rows = build_vmsp_rows(&executions, &records, std::slice::from_ref(fixture)).unwrap();
        assert_eq!(rows.len(), 1);
        let row = &rows[0];
        exact_text(
            row.field("schema", "row").unwrap(),
            VMSP_RUN_SCHEMA,
            "schema",
        )
        .unwrap();
        assert_eq!(
            row.field("sample_count", "row")
                .unwrap()
                .natural("sample_count")
                .unwrap(),
            7
        );
        assert_eq!(
            row.field("execution_order", "row")
                .unwrap()
                .array("execution_order")
                .unwrap()
                .len(),
            7
        );
        assert_eq!(
            row.field("samples", "row")
                .unwrap()
                .array("samples")
                .unwrap()
                .len(),
            7
        );
        assert_eq!(
            row.field("peak_rss_kib", "row")
                .unwrap()
                .natural("peak")
                .unwrap(),
            106
        );
        assert_eq!(
            row.field("elapsed_summary_ns", "row").unwrap(),
            &vmsp_summary(&[1, 2, 3, 4, 5, 6, 7]).unwrap()
        );
    }

    #[test]
    fn owned_json_structural_accounting_is_checked_and_nontrivial() {
        let value = OwnedJson::parse_canonical_line(
            b"{\"array\":[\"payload\",1,true,null],\"object\":{\"nested\":\"value\"}}\n",
            "accounting test",
        )
        .unwrap();
        let retained = value.retained_bytes().unwrap();
        assert!(retained > value.canonical_line().len() as u64);
        assert!(retained < MAX_SEMANTIC_STRUCTURE_BYTES);
    }

    #[test]
    fn catalog_counts_are_closed() {
        assert_eq!(LaneKind::Snapshot.payload_count(), 607);
        assert_eq!(LaneKind::Snapshot.payload_count() + 1, 608);
        assert_eq!(LaneKind::SharedPayload.payload_count(), 832);
        assert_eq!(LaneKind::SharedPayload.payload_count() + 1, 833);
    }

    #[test]
    fn whole_input_validator_rejects_unused_baseline_and_oracle_drift() {
        let manifest_source =
            include_str!("../../../../testdata/performance/fixtures/manifest.v0.2.json");
        let manifest =
            npa_api::validate_checked_performance_fixture_selection_v02(manifest_source).unwrap();
        let baseline =
            include_bytes!("../../../../testdata/performance/baselines/measurements.v0.1.json");
        let oracle = include_bytes!("../../../../testdata/performance/fixture-generator.v1.tsv");
        validate_whole_inputs(LaneKind::Snapshot, &manifest.scenarios, baseline, oracle).unwrap();
        validate_whole_inputs(
            LaneKind::SharedPayload,
            &manifest.scenarios,
            baseline,
            oracle,
        )
        .unwrap();

        let baseline_text = std::str::from_utf8(baseline).unwrap();
        let malformed_unused = baseline_text.replacen(
            "\"id\": \"compact-package-fast\"",
            "\"id\": \"compact-package-fast\", \"unknown\": 0",
            1,
        );
        assert!(validate_whole_inputs(
            LaneKind::Snapshot,
            &manifest.scenarios,
            malformed_unused.as_bytes(),
            oracle,
        )
        .is_err());

        let parsed_baseline = OwnedJson::parse_bounded_document(baseline, "test baseline").unwrap();
        let first_row = parsed_baseline
            .field("scenarios", "test baseline")
            .unwrap()
            .array("test scenarios")
            .unwrap()[0]
            .clone();
        let mut empty_id = first_row.clone();
        empty_id.set_existing("id", string("")).unwrap();
        assert!(validate_baseline_scenario(&empty_id).is_err());
        let mut empty_counters = first_row.clone();
        empty_counters
            .set_existing("deterministic_counters", object([]))
            .unwrap();
        assert!(validate_baseline_scenario(&empty_counters).is_err());
        let mut unknown_counter = first_row;
        unknown_counter
            .set_existing(
                "deterministic_counters",
                object([("zz.unknown_counter", number(1))]),
            )
            .unwrap();
        assert!(validate_baseline_scenario(&unknown_counter).is_err());

        let mut oracle_lines = std::str::from_utf8(oracle)
            .unwrap()
            .lines()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        oracle_lines.swap(1, 2);
        let reordered = format!("{}\n", oracle_lines.join("\n"));
        assert!(validate_whole_inputs(
            LaneKind::SharedPayload,
            &manifest.scenarios,
            baseline,
            reordered.as_bytes(),
        )
        .is_err());
        oracle_lines.remove(1);
        let missing = format!("{}\n", oracle_lines.join("\n"));
        assert!(validate_whole_inputs(
            LaneKind::SharedPayload,
            &manifest.scenarios,
            baseline,
            missing.as_bytes(),
        )
        .is_err());
    }

    #[test]
    fn vmsp_measurement_projection_accepts_only_stable_unpromoted_counters() {
        fn counters(entries: &BTreeMap<&str, (&str, u64)>) -> OwnedJson {
            OwnedJson::Array(
                entries
                    .iter()
                    .map(|(label, (unit, value))| {
                        object([
                            ("label", string(*label)),
                            ("unit", string(*unit)),
                            ("value", number(*value)),
                        ])
                    })
                    .collect(),
            )
        }

        let expected = BTreeMap::from([
            ("package.avoided_module_payload_clone_bytes".to_owned(), 0),
            ("package.module_payload_handle_clones".to_owned(), 0),
            ("package.module_payload_unique_bytes".to_owned(), 0),
            ("package.module_payloads_frozen".to_owned(), 0),
        ]);
        let entries = BTreeMap::from([
            ("package.avoided_module_payload_clone_bytes", ("bytes", 0)),
            ("package.cache_results", ("count", 0)),
            ("package.decode_cache_retained_bytes", ("bytes", 0)),
            ("package.live_results", ("count", 0)),
            ("package.memo_results", ("count", 0)),
            ("package.module_payload_handle_clones", ("count", 0)),
            ("package.module_payload_unique_bytes", ("bytes", 0)),
            ("package.module_payloads_frozen", ("count", 0)),
        ]);
        validate_vmsp_measurement_counters(&counters(&entries), &expected, 0, 0, false).unwrap();

        let mut missing = entries.clone();
        missing.remove("package.module_payloads_frozen");
        assert!(
            validate_vmsp_measurement_counters(&counters(&missing), &expected, 0, 0, false,)
                .is_err()
        );

        let mut changed = entries.clone();
        changed.insert("package.module_payload_handle_clones", ("count", 1));
        assert!(
            validate_vmsp_measurement_counters(&counters(&changed), &expected, 0, 0, false,)
                .is_err()
        );

        let mut unknown = entries.clone();
        unknown.insert("zz.unknown", ("count", 0));
        assert!(
            validate_vmsp_measurement_counters(&counters(&unknown), &expected, 0, 0, false,)
                .is_err()
        );

        let mut wrong_unit = entries;
        wrong_unit.insert("package.decode_cache_retained_bytes", ("count", 0));
        assert!(
            validate_vmsp_measurement_counters(&counters(&wrong_unit), &expected, 0, 0, false,)
                .is_err()
        );
    }

    #[test]
    fn vmsp_oracle_and_measurement_identity_reject_nested_tampering() {
        let oracle = include_bytes!("../../../../testdata/performance/fixture-generator.v1.tsv");
        let expected = selected_oracle_row(oracle, "small-certificate").unwrap();
        let oracle_object = object([
            (
                "generator_schema",
                string(expected.generator_schema.clone()),
            ),
            (
                "descriptor_sha256",
                string(expected.descriptor_sha256.clone()),
            ),
            (
                "logical_identity_sha256",
                string(expected.logical_identity_sha256.clone()),
            ),
            (
                "artifact_tree_sha256",
                string(expected.artifact_tree_sha256.clone()),
            ),
            ("module_count", number(expected.module_count)),
            ("import_edge_count", number(expected.import_edge_count)),
            ("declaration_count", number(expected.declaration_count)),
            (
                "name_table_entry_count",
                number(expected.name_table_entry_count),
            ),
            (
                "level_table_node_count",
                number(expected.level_table_node_count),
            ),
            (
                "term_table_node_count",
                number(expected.term_table_node_count),
            ),
            ("tree_file_count", number(expected.tree_file_count)),
            ("certificate_bytes", number(expected.certificate_bytes)),
        ]);
        validate_vmsp_oracle_object(&oracle_object, &expected).unwrap();

        let mut tampered = oracle_object;
        tampered
            .set_existing("artifact_tree_sha256", string("0".repeat(64)))
            .unwrap();
        assert!(validate_vmsp_oracle_object(&tampered, &expected).is_err());

        let expected_identity = format!("sha256:{}", expected.artifact_tree_sha256);
        assert_eq!(
            exact_text(
                &string(expected_identity.clone()),
                &expected_identity,
                "VMSP input identity",
            ),
            Ok(())
        );
        assert!(exact_text(
            &string(format!("sha256:{}", "f".repeat(64))),
            &expected_identity,
            "VMSP input identity",
        )
        .is_err());
    }
}
