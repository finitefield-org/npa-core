//! Versioned SNAP/VMSP performance-fixture union.
//!
//! The historical v0.1 parser remains unchanged in `performance_gate`.  This
//! module owns the first additive manifest version that can describe snapshot
//! and shared-payload workloads without weakening any v0.1 variant.

use std::{collections::BTreeMap, fmt};

use crate::json::{JsonDocument, JsonValue};
use sha2::{Digest, Sha256};

/// Closed SNAP/VMSP fixture-union schema.
pub const PERFORMANCE_FIXTURES_SCHEMA_V0_2: &str = "npa.performance.fixtures.v0.2";
const CHECKED_PERFORMANCE_FIXTURE_MANIFEST_V0_2: &str =
    include_str!("../../../testdata/performance/fixtures/manifest.v0.2.json");
const CHECKED_PERFORMANCE_FIXTURE_MANIFEST_V0_2_SHA256: &str =
    "7f75e44fbfe7b8b9365c272ee10ed91081e406222569162ad013bdd54bd7fe28";
const PERFORMANCE_FIXTURE_NOTES_V0_2: &str =
    "Blocking deterministic counters; elapsed and RSS advisory.";

macro_rules! selector {
    ($name:ident { $($variant:ident => $text:literal),+ $(,)? }) => {
        #[non_exhaustive]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum $name { $($variant),+ }

        impl $name {
            fn parse(value: &str, path: &str) -> Result<Self, PerformanceFixtureV02Error> {
                match value {
                    $($text => Ok(Self::$variant),)+
                    _ => Err(PerformanceFixtureV02Error::new(format!(
                        "{path} has unsupported value '{value}'"
                    ))),
                }
            }

            /// Stable JSON spelling.
            pub const fn as_str(self) -> &'static str {
                match self { $(Self::$variant => $text),+ }
            }
        }
    };
}

selector!(PerformanceFixtureVerifier { Fast => "fast", Reference => "reference" });
selector!(PerformanceFixtureExecutionLane { CliLocal => "cli-local", Api => "api" });
selector!(PerformanceFixtureArtifactMode { Raw => "raw", Snapshot => "snapshot" });
selector!(PerformanceFixtureImplementation { LegacyModel => "legacy-model", SharedHandle => "shared-handle" });
selector!(PerformanceFixtureAuditCachePolicy { Off => "off", ReadThrough => "read-through", LocalHit => "local-hit" });
selector!(PerformanceFixtureDiskMemoPolicy { Off => "off", ReadThrough => "read-through", Disk => "disk" });
selector!(PerformanceFixtureProcessMemoPolicy { Disabled => "disabled", ProcessLocal => "process-local" });
selector!(PerformanceFixtureDecodeCachePolicy { Disabled => "disabled", ProcessLocal => "process-local", ProcessLocalAndPersistent => "process-local-and-persistent" });
selector!(PerformanceFixtureCachePhase { Cold => "cold", MissInsert => "miss-insert", Hit => "hit" });
selector!(PerformanceFixtureMemoPhase { Miss => "miss", Hit => "hit" });
selector!(PerformanceFixtureSessionPhase { Snapshot => "snapshot", FirstCow => "first-cow" });
selector!(PerformanceFixtureMeasurementMode { Detailed => "detailed" });
selector!(PerformanceFixtureProfile {
    Representative1000Certificates => "representative-1000-certificates",
    Synthetic1Kib => "synthetic-1kib",
    Synthetic1Mib => "synthetic-1mib",
    SyntheticNearLimit => "synthetic-near-limit",
    Payload1Mib => "payload-1mib",
    Payload16Mib => "payload-16mib",
    PayloadNearLimit => "payload-near-limit",
    PayloadHeavyMultiModule => "payload-heavy-multi-module",
    SessionIndex => "session-index",
    SmallCertificate => "small-certificate",
});

/// One strict v0.2 scenario.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PerformanceFixtureSelectionV02 {
    /// Historical warmed checked-artifact verifier scenario.
    WarmedCheckedArtifactVerifier(HistoricalPerformanceFixtureCommonV01),
    /// Historical targeted build-certs scenario.
    TargetedBuildCerts(TargetedBuildCertsFixtureV01),
    /// Historical package-verifier process-memo scenario.
    PackageVerifierProcessMemoScope(HistoricalPerformanceFixtureCommonV01),
    /// Historical changed-selection Git batching scenario.
    PackageChangedSelectionGitBatching(HistoricalPerformanceFixtureCommonV01),
    /// Operation-owned package artifact comparison.
    PackageArtifactSnapshot(PackageArtifactSnapshotFixture),
    /// Immutable payload handle versus deep-copy model.
    SharedPayloadClone(SharedPayloadCloneFixture),
    /// Decode/import cache ownership lifecycle.
    SharedPayloadCache(SharedPayloadCacheFixture),
    /// Package process-memo ownership lifecycle.
    SharedPayloadMemo(SharedPayloadMemoFixture),
    /// Verifier-session snapshot/COW lifecycle.
    SharedPayloadSession(SharedPayloadSessionFixture),
    /// Package shard ownership comparison.
    SharedPayloadShard(SharedPayloadShardFixture),
    /// Small-certificate clone crossover comparison.
    SharedPayloadSmall(SharedPayloadCloneFixture),
}

impl PerformanceFixtureSelectionV02 {
    /// Stable unique scenario identifier.
    pub fn id(&self) -> &str {
        match self {
            Self::WarmedCheckedArtifactVerifier(value)
            | Self::PackageVerifierProcessMemoScope(value)
            | Self::PackageChangedSelectionGitBatching(value) => &value.id,
            Self::TargetedBuildCerts(value) => &value.common.id,
            Self::PackageArtifactSnapshot(value) => &value.common.id,
            Self::SharedPayloadClone(value) | Self::SharedPayloadSmall(value) => &value.common.id,
            Self::SharedPayloadCache(value) => &value.common.id,
            Self::SharedPayloadMemo(value) => &value.common.id,
            Self::SharedPayloadSession(value) => &value.common.id,
            Self::SharedPayloadShard(value) => &value.common.id,
        }
    }

    #[cfg(test)]
    fn is_inherited(&self) -> bool {
        matches!(
            self,
            Self::WarmedCheckedArtifactVerifier(_)
                | Self::TargetedBuildCerts(_)
                | Self::PackageVerifierProcessMemoScope(_)
                | Self::PackageChangedSelectionGitBatching(_)
        )
    }
}

/// Exact eight-field shape shared by the three simple historical v0.1 tags.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HistoricalPerformanceFixtureCommonV01 {
    /// Stable scenario identifier.
    pub id: String,
    /// Normalized repository-relative package root.
    pub package_root: String,
    /// Historical verifier spelling.
    pub verifier: String,
    /// Historical cache-policy spelling.
    pub cache_policy: String,
    /// Unmeasured warmup count.
    pub warmup: u64,
    /// Measured sample count.
    pub samples: u64,
    /// Stable human-readable policy note.
    pub notes: String,
}

/// Exact historical targeted-build-certs shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedBuildCertsFixtureV01 {
    /// Fields common to every historical fixture tag.
    pub common: HistoricalPerformanceFixtureCommonV01,
    /// Number of generated support modules.
    pub support_module_count: u64,
    /// Number of generated target modules.
    pub target_module_count: u64,
    /// Closed historical target-edit spelling.
    pub target_edit: String,
    /// Modules prepopulated in the cache.
    pub population_modules: Vec<String>,
    /// Support modules removed before the measured run.
    pub removed_support_modules: Vec<String>,
}

/// Fields common to every new v0.2 tag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceFixtureCommonV02 {
    /// Stable scenario identifier.
    pub id: String,
    /// Required measurement population.
    pub measurement_mode: PerformanceFixtureMeasurementMode,
    /// Unmeasured warmup count.
    pub warmup: u64,
    /// Measured sample count.
    pub samples: u64,
    /// Stable human-readable policy note.
    pub notes: String,
    /// Group whose paired variants are interleaved.
    pub interleave_group: String,
}

/// Snapshot fixture row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageArtifactSnapshotFixture {
    /// Common v0.2 fields.
    pub common: PerformanceFixtureCommonV02,
    /// Generated package root token.
    pub package_root: String,
    /// API or in-process CLI execution lane.
    pub execution_lane: PerformanceFixtureExecutionLane,
    /// Deterministic generator profile.
    pub fixture_profile: PerformanceFixtureProfile,
    /// Raw or operation-owned snapshot representation.
    pub artifact_mode: PerformanceFixtureArtifactMode,
    /// Exact aggregate certificate bytes.
    pub artifact_bytes: u64,
    /// Fast or independent reference verifier.
    pub verifier: PerformanceFixtureVerifier,
    /// CLI local-audit policy.
    pub audit_cache_policy: PerformanceFixtureAuditCachePolicy,
    /// CLI disk-memo policy.
    pub disk_memo_policy: PerformanceFixtureDiskMemoPolicy,
    /// Process-memo policy.
    pub process_memo_policy: PerformanceFixtureProcessMemoPolicy,
    /// Decode-cache policy.
    pub decode_cache_policy: PerformanceFixtureDecodeCachePolicy,
    /// Requested verifier jobs.
    pub jobs: u64,
}

/// Clone-oriented shared-payload fixture row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedPayloadCloneFixture {
    /// Common v0.2 fields.
    pub common: PerformanceFixtureCommonV02,
    /// Legacy deep-copy model or shared production handle.
    pub implementation: PerformanceFixtureImplementation,
    /// Deterministic generator profile.
    pub fixture_profile: PerformanceFixtureProfile,
    /// Exact canonical payload bytes.
    pub payload_bytes: u64,
    /// Clone operations in one sample.
    pub clone_count: u64,
}

/// Cache-oriented shared-payload fixture row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedPayloadCacheFixture {
    /// Common v0.2 fields.
    pub common: PerformanceFixtureCommonV02,
    /// Deterministic generator profile.
    pub fixture_profile: PerformanceFixtureProfile,
    /// Exact canonical payload bytes.
    pub payload_bytes: u64,
    /// Cold, insertion, or hit phase.
    pub phase: PerformanceFixtureCachePhase,
    /// Decode-cache policy.
    pub decode_cache_policy: PerformanceFixtureDecodeCachePolicy,
}

/// Memo-oriented shared-payload fixture row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedPayloadMemoFixture {
    /// Common v0.2 fields.
    pub common: PerformanceFixtureCommonV02,
    /// Deterministic generator profile.
    pub fixture_profile: PerformanceFixtureProfile,
    /// Memo miss or hit phase.
    pub phase: PerformanceFixtureMemoPhase,
    /// Decode-cache policy fixed independently of memo state.
    pub decode_cache_policy: PerformanceFixtureDecodeCachePolicy,
    /// Process-memo policy.
    pub process_memo_policy: PerformanceFixtureProcessMemoPolicy,
    /// Requested verifier jobs.
    pub jobs: u64,
}

/// Session-oriented shared-payload fixture row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedPayloadSessionFixture {
    /// Common v0.2 fields.
    pub common: PerformanceFixtureCommonV02,
    /// Legacy deep-copy model or shared production handle.
    pub implementation: PerformanceFixtureImplementation,
    /// Deterministic generator profile.
    pub fixture_profile: PerformanceFixtureProfile,
    /// Session entries populated before sampling.
    pub session_entries: u64,
    /// Snapshot or first-copy-on-write phase.
    pub phase: PerformanceFixtureSessionPhase,
}

/// Shard-oriented shared-payload fixture row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedPayloadShardFixture {
    /// Common v0.2 fields.
    pub common: PerformanceFixtureCommonV02,
    /// Deterministic generator profile.
    pub fixture_profile: PerformanceFixtureProfile,
    /// Decode-cache policy.
    pub decode_cache_policy: PerformanceFixtureDecodeCachePolicy,
    /// Process-memo policy.
    pub process_memo_policy: PerformanceFixtureProcessMemoPolicy,
    /// Requested verifier jobs.
    pub jobs: u64,
}

/// Strict parsed v0.2 manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceFixtureManifestV02 {
    /// Strictly validated scenario rows in manifest order.
    pub scenarios: Vec<PerformanceFixtureSelectionV02>,
}

/// Versioned manifest dispatch result.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VersionedPerformanceFixtureSelection {
    /// Historical v0.1 closed manifest, validated without changing its public
    /// scenario-selection entry point.
    V01 {
        /// Number of validated historical scenarios.
        scenario_count: usize,
    },
    /// Selected SNAP/VMSP union manifest.
    V02(PerformanceFixtureManifestV02),
}

/// Strict fixture-union parse error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceFixtureV02Error {
    message: String,
}

impl PerformanceFixtureV02Error {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for PerformanceFixtureV02Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for PerformanceFixtureV02Error {}

/// Parse and validate the exact v0.2 SNAP/VMSP fixture union.
pub fn validate_performance_fixture_selection_v02(
    source: &str,
) -> Result<PerformanceFixtureManifestV02, PerformanceFixtureV02Error> {
    let document = JsonDocument::parse(source).map_err(|error| {
        PerformanceFixtureV02Error::new(format!("invalid JSON at byte {}", error.offset))
    })?;
    let root = exact_object(document.root(), "$", &["schema", "scenarios"])?;
    require_text(
        &root,
        "schema",
        PERFORMANCE_FIXTURES_SCHEMA_V0_2,
        "$.schema",
    )?;
    let rows = field(&root, "scenarios", "$")?
        .array_elements()
        .ok_or_else(|| PerformanceFixtureV02Error::new("$.scenarios must be an array"))?;
    let mut ids = BTreeMap::new();
    let mut scenarios = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().enumerate() {
        let path = format!("$.scenarios[{index}]");
        let open = object(row, &path)?;
        let kind = get_text(&open, "kind", &path)?;
        let scenario = match kind.as_str() {
            "package-artifact-snapshot" => parse_snapshot(row, &path)?,
            "shared-payload-clone" => parse_clone(row, &path, false)?,
            "shared-payload-cache" => parse_cache(row, &path)?,
            "shared-payload-memo" => parse_memo(row, &path)?,
            "shared-payload-session" => parse_session(row, &path)?,
            "shared-payload-shard" => parse_shard(row, &path)?,
            "shared-payload-small" => parse_clone(row, &path, true)?,
            _ => parse_inherited(row, &path, &kind)?,
        };
        if scenario.id().is_empty() || ids.insert(scenario.id().to_owned(), index).is_some() {
            return Err(PerformanceFixtureV02Error::new(format!(
                "{path}.id must be nonempty and unique"
            )));
        }
        scenarios.push(scenario);
    }
    validate_interleave_groups(&scenarios)?;
    Ok(PerformanceFixtureManifestV02 { scenarios })
}

/// Validate the repository's immutable 138-row v0.2 catalog byte for byte.
///
/// The general v0.2 parser remains available for focused malformed-fixture
/// tests and private generators. Production performance controllers must use
/// this entry so reordered, renamed, missing, altered, or extra rows fail
/// before any workload is executed.
pub fn validate_checked_performance_fixture_selection_v02(
    source: &str,
) -> Result<PerformanceFixtureManifestV02, PerformanceFixtureV02Error> {
    if source != CHECKED_PERFORMANCE_FIXTURE_MANIFEST_V0_2
        || format!("{:x}", Sha256::digest(source.as_bytes()))
            != CHECKED_PERFORMANCE_FIXTURE_MANIFEST_V0_2_SHA256
    {
        return Err(PerformanceFixtureV02Error::new(
            "v0.2 manifest differs from the checked 138-row catalog bytes",
        ));
    }
    let manifest = validate_performance_fixture_selection_v02(source)?;
    if manifest.scenarios.len() != 138 {
        return Err(PerformanceFixtureV02Error::new(
            "checked v0.2 manifest must contain exactly 138 rows",
        ));
    }
    Ok(manifest)
}

fn validate_interleave_groups(
    scenarios: &[PerformanceFixtureSelectionV02],
) -> Result<(), PerformanceFixtureV02Error> {
    let mut groups = BTreeMap::<&str, Vec<&PerformanceFixtureSelectionV02>>::new();
    for scenario in scenarios {
        let group = match scenario {
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(value) => {
                &value.common.interleave_group
            }
            PerformanceFixtureSelectionV02::SharedPayloadClone(value)
            | PerformanceFixtureSelectionV02::SharedPayloadSmall(value) => {
                &value.common.interleave_group
            }
            PerformanceFixtureSelectionV02::SharedPayloadCache(value) => {
                &value.common.interleave_group
            }
            PerformanceFixtureSelectionV02::SharedPayloadMemo(value) => {
                &value.common.interleave_group
            }
            PerformanceFixtureSelectionV02::SharedPayloadSession(value) => {
                &value.common.interleave_group
            }
            PerformanceFixtureSelectionV02::SharedPayloadShard(value) => {
                &value.common.interleave_group
            }
            PerformanceFixtureSelectionV02::WarmedCheckedArtifactVerifier(_)
            | PerformanceFixtureSelectionV02::TargetedBuildCerts(_)
            | PerformanceFixtureSelectionV02::PackageVerifierProcessMemoScope(_)
            | PerformanceFixtureSelectionV02::PackageChangedSelectionGitBatching(_) => continue,
        };
        groups.entry(group).or_default().push(scenario);
    }

    for (group, rows) in groups {
        match rows.first().copied() {
            Some(PerformanceFixtureSelectionV02::PackageArtifactSnapshot(_)) => {
                validate_snapshot_pair(group, &rows)?;
            }
            Some(PerformanceFixtureSelectionV02::SharedPayloadClone(_)) => {
                validate_clone_pair(group, &rows, false)?;
            }
            Some(PerformanceFixtureSelectionV02::SharedPayloadSession(_)) => {
                validate_session_pair(group, &rows)?;
            }
            Some(PerformanceFixtureSelectionV02::SharedPayloadSmall(_)) => {
                validate_clone_pair(group, &rows, true)?;
            }
            Some(PerformanceFixtureSelectionV02::SharedPayloadCache(_)) => {
                validate_cache_group(group, &rows)?;
            }
            Some(PerformanceFixtureSelectionV02::SharedPayloadMemo(_)) => {
                validate_memo_group(group, &rows)?;
            }
            Some(PerformanceFixtureSelectionV02::SharedPayloadShard(_)) => {
                validate_shard_group(group, &rows)?;
            }
            Some(_) => unreachable!("all non-inherited fixture kinds are handled above"),
            None => unreachable!("group was populated above"),
        }
    }
    Ok(())
}

fn require_group_id(
    id: &str,
    group: &str,
    variant: &str,
) -> Result<(), PerformanceFixtureV02Error> {
    let expected = format!("{group}-{variant}");
    if id == expected {
        Ok(())
    } else {
        Err(PerformanceFixtureV02Error::new(format!(
            "scenario id '{id}' must equal interleave_group plus '-{variant}'"
        )))
    }
}

fn validate_snapshot_pair(
    group: &str,
    rows: &[&PerformanceFixtureSelectionV02],
) -> Result<(), PerformanceFixtureV02Error> {
    let values = rows
        .iter()
        .map(|row| match row {
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(value) => Ok(value),
            _ => Err(PerformanceFixtureV02Error::new(format!(
                "interleave_group '{group}' mixes fixture kinds"
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != 2
        || values[0].artifact_mode == values[1].artifact_mode
        || !values
            .iter()
            .any(|value| value.artifact_mode == PerformanceFixtureArtifactMode::Raw)
        || !values
            .iter()
            .any(|value| value.artifact_mode == PerformanceFixtureArtifactMode::Snapshot)
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "snapshot interleave_group '{group}' must contain exactly one raw and one snapshot row"
        )));
    }
    let first = values[0];
    let second = values[1];
    for value in &values {
        let marker = match value.artifact_mode {
            PerformanceFixtureArtifactMode::Raw => "raw",
            PerformanceFixtureArtifactMode::Snapshot => "snapshot",
        };
        let suffix = format!("-{marker}-j{}", value.jobs);
        let expected = value
            .common
            .id
            .strip_suffix(&suffix)
            .map(|prefix| format!("{prefix}-j{}", value.jobs));
        if expected.as_deref() != Some(group) {
            return Err(PerformanceFixtureV02Error::new(format!(
                "snapshot id '{}' does not derive interleave_group '{group}'",
                value.common.id
            )));
        }
    }
    if !group.starts_with("package-artifact-snapshot-") {
        return Err(PerformanceFixtureV02Error::new(format!(
            "snapshot interleave_group '{group}' is outside the closed catalog grammar"
        )));
    }
    if first.common.measurement_mode != second.common.measurement_mode
        || first.common.warmup != second.common.warmup
        || first.common.samples != second.common.samples
        || first.common.notes != second.common.notes
        || first.package_root != second.package_root
        || first.execution_lane != second.execution_lane
        || first.fixture_profile != second.fixture_profile
        || first.artifact_bytes != second.artifact_bytes
        || first.verifier != second.verifier
        || first.audit_cache_policy != second.audit_cache_policy
        || first.disk_memo_policy != second.disk_memo_policy
        || first.process_memo_policy != second.process_memo_policy
        || first.decode_cache_policy != second.decode_cache_policy
        || first.jobs != second.jobs
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "snapshot interleave_group '{group}' companions differ outside artifact_mode/id"
        )));
    }
    Ok(())
}

fn validate_clone_pair(
    group: &str,
    rows: &[&PerformanceFixtureSelectionV02],
    small: bool,
) -> Result<(), PerformanceFixtureV02Error> {
    let values = rows
        .iter()
        .map(|row| match (small, row) {
            (false, PerformanceFixtureSelectionV02::SharedPayloadClone(value))
            | (true, PerformanceFixtureSelectionV02::SharedPayloadSmall(value)) => Ok(value),
            _ => Err(PerformanceFixtureV02Error::new(format!(
                "interleave_group '{group}' mixes fixture kinds"
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != 2
        || values[0].implementation == values[1].implementation
        || !values
            .iter()
            .any(|value| value.implementation == PerformanceFixtureImplementation::LegacyModel)
        || !values
            .iter()
            .any(|value| value.implementation == PerformanceFixtureImplementation::SharedHandle)
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload interleave_group '{group}' must contain exactly one legacy-model and one shared-handle row"
        )));
    }
    let first = values[0];
    let second = values[1];
    let expected_group = if small {
        format!("shared-payload-small-1k-c{}", first.clone_count)
    } else {
        let profile = match first.fixture_profile {
            PerformanceFixtureProfile::Payload1Mib => "1m",
            PerformanceFixtureProfile::Payload16Mib => "16m",
            PerformanceFixtureProfile::PayloadNearLimit => "near",
            _ => unreachable!("clone profile was validated before grouping"),
        };
        format!("shared-payload-clone-{profile}-c{}", first.clone_count)
    };
    if group != expected_group {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload clone interleave_group '{group}' does not match its closed catalog axes"
        )));
    }
    for value in &values {
        let variant = match value.implementation {
            PerformanceFixtureImplementation::LegacyModel => "legacy",
            PerformanceFixtureImplementation::SharedHandle => "shared",
        };
        require_group_id(&value.common.id, group, variant)?;
    }
    if first.common.measurement_mode != second.common.measurement_mode
        || first.common.warmup != second.common.warmup
        || first.common.samples != second.common.samples
        || first.common.notes != second.common.notes
        || first.fixture_profile != second.fixture_profile
        || first.payload_bytes != second.payload_bytes
        || first.clone_count != second.clone_count
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload interleave_group '{group}' companions differ outside implementation/id"
        )));
    }
    Ok(())
}

fn validate_session_pair(
    group: &str,
    rows: &[&PerformanceFixtureSelectionV02],
) -> Result<(), PerformanceFixtureV02Error> {
    let values = rows
        .iter()
        .map(|row| match row {
            PerformanceFixtureSelectionV02::SharedPayloadSession(value) => Ok(value),
            _ => Err(PerformanceFixtureV02Error::new(format!(
                "interleave_group '{group}' mixes fixture kinds"
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != 2
        || values[0].implementation == values[1].implementation
        || !values
            .iter()
            .any(|value| value.implementation == PerformanceFixtureImplementation::LegacyModel)
        || !values
            .iter()
            .any(|value| value.implementation == PerformanceFixtureImplementation::SharedHandle)
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload session interleave_group '{group}' must contain exactly one legacy-model and one shared-handle row"
        )));
    }
    let first = values[0];
    let second = values[1];
    let phase = match first.phase {
        PerformanceFixtureSessionPhase::Snapshot => "snapshot",
        PerformanceFixtureSessionPhase::FirstCow => "first-cow",
    };
    let expected_group = format!("shared-payload-session-s{}-{phase}", first.session_entries);
    if group != expected_group {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload session interleave_group '{group}' does not match its closed catalog axes"
        )));
    }
    for value in &values {
        let variant = match value.implementation {
            PerformanceFixtureImplementation::LegacyModel => "legacy",
            PerformanceFixtureImplementation::SharedHandle => "shared",
        };
        require_group_id(&value.common.id, group, variant)?;
    }
    if first.common.measurement_mode != second.common.measurement_mode
        || first.common.warmup != second.common.warmup
        || first.common.samples != second.common.samples
        || first.common.notes != second.common.notes
        || first.fixture_profile != second.fixture_profile
        || first.session_entries != second.session_entries
        || first.phase != second.phase
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload session interleave_group '{group}' companions differ outside implementation/id"
        )));
    }
    Ok(())
}

fn validate_cache_group(
    group: &str,
    rows: &[&PerformanceFixtureSelectionV02],
) -> Result<(), PerformanceFixtureV02Error> {
    let values = rows
        .iter()
        .map(|row| match row {
            PerformanceFixtureSelectionV02::SharedPayloadCache(value) => Ok(value),
            _ => Err(PerformanceFixtureV02Error::new(format!(
                "interleave_group '{group}' mixes fixture kinds"
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != 5 {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload cache interleave_group '{group}' must contain exactly five catalog rows"
        )));
    }
    if group != "shared-payload-cache-1m" {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload cache interleave_group '{group}' is outside the closed catalog"
        )));
    }
    let expected = [
        (
            PerformanceFixtureCachePhase::Cold,
            PerformanceFixtureDecodeCachePolicy::Disabled,
            "cold-disabled",
        ),
        (
            PerformanceFixtureCachePhase::MissInsert,
            PerformanceFixtureDecodeCachePolicy::ProcessLocal,
            "miss-process-local",
        ),
        (
            PerformanceFixtureCachePhase::Hit,
            PerformanceFixtureDecodeCachePolicy::ProcessLocal,
            "hit-process-local",
        ),
        (
            PerformanceFixtureCachePhase::MissInsert,
            PerformanceFixtureDecodeCachePolicy::ProcessLocalAndPersistent,
            "miss-persistent",
        ),
        (
            PerformanceFixtureCachePhase::Hit,
            PerformanceFixtureDecodeCachePolicy::ProcessLocalAndPersistent,
            "hit-persistent",
        ),
    ];
    for (phase, policy, suffix) in expected {
        let matches = values
            .iter()
            .filter(|value| value.phase == phase && value.decode_cache_policy == policy)
            .copied()
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(PerformanceFixtureV02Error::new(format!(
                "shared-payload cache interleave_group '{group}' has a missing or duplicate phase/policy row"
            )));
        }
        require_group_id(&matches[0].common.id, group, suffix)?;
    }
    let first = values[0];
    for value in values {
        if value.common.measurement_mode != first.common.measurement_mode
            || value.common.warmup != first.common.warmup
            || value.common.samples != first.common.samples
            || value.common.notes != first.common.notes
            || value.fixture_profile != first.fixture_profile
            || value.payload_bytes != first.payload_bytes
        {
            return Err(PerformanceFixtureV02Error::new(format!(
                "shared-payload cache interleave_group '{group}' has a mismatched fixed axis or id"
            )));
        }
    }
    Ok(())
}

fn validate_memo_group(
    group: &str,
    rows: &[&PerformanceFixtureSelectionV02],
) -> Result<(), PerformanceFixtureV02Error> {
    let values = rows
        .iter()
        .map(|row| match row {
            PerformanceFixtureSelectionV02::SharedPayloadMemo(value) => Ok(value),
            _ => Err(PerformanceFixtureV02Error::new(format!(
                "interleave_group '{group}' mixes fixture kinds"
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != 2
        || values
            .iter()
            .filter(|value| value.phase == PerformanceFixtureMemoPhase::Miss)
            .count()
            != 1
        || values
            .iter()
            .filter(|value| value.phase == PerformanceFixtureMemoPhase::Hit)
            .count()
            != 1
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload memo interleave_group '{group}' must contain exactly one miss and one hit row"
        )));
    }
    if group != "shared-payload-memo-multi" {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload memo interleave_group '{group}' is outside the closed catalog"
        )));
    }
    let first = values[0];
    for value in values {
        let variant = match value.phase {
            PerformanceFixtureMemoPhase::Miss => "miss",
            PerformanceFixtureMemoPhase::Hit => "hit",
        };
        require_group_id(&value.common.id, group, variant)?;
        if value.common.measurement_mode != first.common.measurement_mode
            || value.common.warmup != first.common.warmup
            || value.common.samples != first.common.samples
            || value.common.notes != first.common.notes
            || value.fixture_profile != first.fixture_profile
            || value.decode_cache_policy != first.decode_cache_policy
            || value.process_memo_policy != first.process_memo_policy
            || value.jobs != first.jobs
        {
            return Err(PerformanceFixtureV02Error::new(format!(
                "shared-payload memo interleave_group '{group}' has a mismatched fixed axis"
            )));
        }
    }
    Ok(())
}

fn validate_shard_group(
    group: &str,
    rows: &[&PerformanceFixtureSelectionV02],
) -> Result<(), PerformanceFixtureV02Error> {
    let values = rows
        .iter()
        .map(|row| match row {
            PerformanceFixtureSelectionV02::SharedPayloadShard(value) => Ok(value),
            _ => Err(PerformanceFixtureV02Error::new(format!(
                "interleave_group '{group}' mixes fixture kinds"
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != 2
        || values.iter().filter(|value| value.jobs == 1).count() != 1
        || values.iter().filter(|value| value.jobs == 8).count() != 1
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload shard interleave_group '{group}' must contain exactly jobs=1 and jobs=8 rows"
        )));
    }
    if group != "shared-payload-shard-multi" {
        return Err(PerformanceFixtureV02Error::new(format!(
            "shared-payload shard interleave_group '{group}' is outside the closed catalog"
        )));
    }
    let first = values[0];
    for value in values {
        require_group_id(&value.common.id, group, &format!("j{}", value.jobs))?;
        if value.common.measurement_mode != first.common.measurement_mode
            || value.common.warmup != first.common.warmup
            || value.common.samples != first.common.samples
            || value.common.notes != first.common.notes
            || value.fixture_profile != first.fixture_profile
            || value.decode_cache_policy != first.decode_cache_policy
            || value.process_memo_policy != first.process_memo_policy
        {
            return Err(PerformanceFixtureV02Error::new(format!(
                "shared-payload shard interleave_group '{group}' has a mismatched fixed axis"
            )));
        }
    }
    Ok(())
}

/// Dispatch a versioned fixture manifest.  Historical v0.1 remains owned by
/// `validate_performance_fixture_selection`; this entry intentionally accepts
/// only versions for which it can return a complete typed manifest.
pub fn validate_versioned_performance_fixture_selection(
    source: &str,
) -> Result<VersionedPerformanceFixtureSelection, PerformanceFixtureV02Error> {
    let document = JsonDocument::parse(source).map_err(|error| {
        PerformanceFixtureV02Error::new(format!("invalid JSON at byte {}", error.offset))
    })?;
    let root = object(document.root(), "$")?;
    match get_text(&root, "schema", "$")?.as_str() {
        crate::PERFORMANCE_FIXTURES_SCHEMA => {
            let scenario_count = validate_performance_fixture_selection_v01_manifest(source)?;
            Ok(VersionedPerformanceFixtureSelection::V01 { scenario_count })
        }
        PERFORMANCE_FIXTURES_SCHEMA_V0_2 => Ok(VersionedPerformanceFixtureSelection::V02(
            validate_performance_fixture_selection_v02(source)?,
        )),
        schema => Err(PerformanceFixtureV02Error::new(format!(
            "unsupported typed fixture schema '{schema}'"
        ))),
    }
}

fn validate_performance_fixture_selection_v01_manifest(
    source: &str,
) -> Result<usize, PerformanceFixtureV02Error> {
    let document = JsonDocument::parse(source).map_err(|error| {
        PerformanceFixtureV02Error::new(format!("invalid JSON at byte {}", error.offset))
    })?;
    let root = exact_object(document.root(), "$", &["schema", "scenarios"])?;
    require_text(
        &root,
        "schema",
        crate::PERFORMANCE_FIXTURES_SCHEMA,
        "$.schema",
    )?;
    let rows = field(&root, "scenarios", "$")?
        .array_elements()
        .ok_or_else(|| PerformanceFixtureV02Error::new("$.scenarios must be an array"))?;
    for (index, row) in rows.iter().enumerate() {
        let path = format!("$.scenarios[{index}]");
        let open = object(row, &path)?;
        let id = get_text(&open, "id", &path)?;
        let kind = get_text(&open, "kind", &path)?;
        let package_root = get_text(&open, "package_root", &path)?;
        let verifier = get_text(&open, "verifier", &path)?;
        let cache_policy = get_text(&open, "cache_policy", &path)?;
        let warmup = natural(&open, "warmup", &path)?;
        let samples = positive(&open, "samples", &path)?;
        crate::validate_performance_fixture_selection(
            source,
            crate::PerformanceFixtureSelection {
                scenario: &id,
                kind: &kind,
                package_root: &package_root,
                verifier: &verifier,
                cache_policy: &cache_policy,
                warmup,
                samples,
            },
        )
        .map_err(|error| PerformanceFixtureV02Error::new(error.to_string()))?;
    }
    if rows.is_empty() {
        return Err(PerformanceFixtureV02Error::new(
            "historical v0.1 manifest has no selectable scenario",
        ));
    }
    Ok(rows.len())
}

fn parse_inherited(
    value: &JsonValue<'_>,
    path: &str,
    kind: &str,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let fields: &[&str] = if kind == "targeted-build-certs" {
        &[
            "id",
            "kind",
            "package_root",
            "verifier",
            "cache_policy",
            "warmup",
            "samples",
            "support_module_count",
            "target_module_count",
            "target_edit",
            "population_modules",
            "removed_support_modules",
            "notes",
        ]
    } else if matches!(
        kind,
        "warmed-checked-artifact-verifier"
            | "package-verifier-process-memo-scope"
            | "package-changed-selection-git-batching"
    ) {
        &[
            "id",
            "kind",
            "package_root",
            "verifier",
            "cache_policy",
            "warmup",
            "samples",
            "notes",
        ]
    } else {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.kind has unsupported inherited value '{kind}'"
        )));
    };
    let object = exact_object(value, path, fields)?;
    let id = get_text(&object, "id", path)?;
    let package_root = get_text(&object, "package_root", path)?;
    let verifier = get_text(&object, "verifier", path)?;
    let cache_policy = get_text(&object, "cache_policy", path)?;
    let warmup = natural(&object, "warmup", path)?;
    let samples = positive(&object, "samples", path)?;
    let notes = get_text(&object, "notes", path)?;
    require_nonempty(&notes, &format!("{path}.notes"))?;
    let targeted = if kind == "targeted-build-certs" {
        Some((
            positive(&object, "support_module_count", path)?,
            positive(&object, "target_module_count", path)?,
            get_text(&object, "target_edit", path)?,
            string_array(&object, "population_modules", path)?,
            string_array(&object, "removed_support_modules", path)?,
        ))
    } else {
        None
    };

    // A successor manifest must preserve not only the published field table,
    // but also every semantic constraint of the historical parser.  Validate
    // the exact inherited row through that parser instead of maintaining a
    // weaker second copy here.
    let historical_source = format!(
        r#"{{"schema":"{}","scenarios":[{}]}}"#,
        crate::PERFORMANCE_FIXTURES_SCHEMA,
        value.raw_slice()
    );
    crate::validate_performance_fixture_selection(
        &historical_source,
        crate::PerformanceFixtureSelection {
            scenario: &id,
            kind,
            package_root: &package_root,
            verifier: &verifier,
            cache_policy: &cache_policy,
            warmup,
            samples,
        },
    )
    .map_err(|error| {
        PerformanceFixtureV02Error::new(format!(
            "{path} violates its historical v0.1 contract: {error}"
        ))
    })?;
    let common = HistoricalPerformanceFixtureCommonV01 {
        id,
        package_root,
        verifier,
        cache_policy,
        warmup,
        samples,
        notes,
    };
    match kind {
        "warmed-checked-artifact-verifier" => {
            Ok(PerformanceFixtureSelectionV02::WarmedCheckedArtifactVerifier(common))
        }
        "package-verifier-process-memo-scope" => {
            Ok(PerformanceFixtureSelectionV02::PackageVerifierProcessMemoScope(common))
        }
        "package-changed-selection-git-batching" => {
            Ok(PerformanceFixtureSelectionV02::PackageChangedSelectionGitBatching(common))
        }
        "targeted-build-certs" => {
            let (
                support_module_count,
                target_module_count,
                target_edit,
                population_modules,
                removed_support_modules,
            ) = targeted.ok_or_else(|| {
                PerformanceFixtureV02Error::new(format!(
                    "{path} is missing its targeted-build-certs fields"
                ))
            })?;
            Ok(PerformanceFixtureSelectionV02::TargetedBuildCerts(
                TargetedBuildCertsFixtureV01 {
                    common,
                    support_module_count,
                    target_module_count,
                    target_edit,
                    population_modules,
                    removed_support_modules,
                },
            ))
        }
        _ => Err(PerformanceFixtureV02Error::new(format!(
            "{path}.kind has unsupported inherited value '{kind}'"
        ))),
    }
}

fn parse_snapshot(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let object = exact_object(
        value,
        path,
        &[
            "id",
            "kind",
            "measurement_mode",
            "warmup",
            "samples",
            "notes",
            "interleave_group",
            "package_root",
            "execution_lane",
            "fixture_profile",
            "artifact_mode",
            "artifact_bytes",
            "verifier",
            "audit_cache_policy",
            "disk_memo_policy",
            "process_memo_policy",
            "decode_cache_policy",
            "jobs",
        ],
    )?;
    let common = common(&object, path)?;
    require_sampling(&common, 5, path)?;
    let package_root = get_text(&object, "package_root", path)?;
    validate_relative_path(&package_root, &format!("{path}.package_root"))?;
    let execution_lane = PerformanceFixtureExecutionLane::parse(
        &get_text(&object, "execution_lane", path)?,
        &format!("{path}.execution_lane"),
    )?;
    let fixture_profile = PerformanceFixtureProfile::parse(
        &get_text(&object, "fixture_profile", path)?,
        &format!("{path}.fixture_profile"),
    )?;
    if !matches!(
        fixture_profile,
        PerformanceFixtureProfile::Representative1000Certificates
            | PerformanceFixtureProfile::Synthetic1Kib
            | PerformanceFixtureProfile::Synthetic1Mib
            | PerformanceFixtureProfile::SyntheticNearLimit
    ) {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.fixture_profile is not a snapshot profile"
        )));
    }
    let artifact_mode = PerformanceFixtureArtifactMode::parse(
        &get_text(&object, "artifact_mode", path)?,
        &format!("{path}.artifact_mode"),
    )?;
    let artifact_bytes = positive(&object, "artifact_bytes", path)?;
    let expected_artifact_bytes = match fixture_profile {
        PerformanceFixtureProfile::Representative1000Certificates => 49_283_072,
        PerformanceFixtureProfile::Synthetic1Kib => 1_024,
        PerformanceFixtureProfile::Synthetic1Mib => 1_048_576,
        PerformanceFixtureProfile::SyntheticNearLimit => 67_108_000,
        _ => unreachable!("snapshot profiles were checked above"),
    };
    if artifact_bytes != expected_artifact_bytes {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.artifact_bytes does not match fixture_profile"
        )));
    }
    let verifier = PerformanceFixtureVerifier::parse(
        &get_text(&object, "verifier", path)?,
        &format!("{path}.verifier"),
    )?;
    let audit_cache_policy = PerformanceFixtureAuditCachePolicy::parse(
        &get_text(&object, "audit_cache_policy", path)?,
        &format!("{path}.audit_cache_policy"),
    )?;
    let disk_memo_policy = PerformanceFixtureDiskMemoPolicy::parse(
        &get_text(&object, "disk_memo_policy", path)?,
        &format!("{path}.disk_memo_policy"),
    )?;
    let process_memo_policy = PerformanceFixtureProcessMemoPolicy::parse(
        &get_text(&object, "process_memo_policy", path)?,
        &format!("{path}.process_memo_policy"),
    )?;
    let decode_cache_policy = PerformanceFixtureDecodeCachePolicy::parse(
        &get_text(&object, "decode_cache_policy", path)?,
        &format!("{path}.decode_cache_policy"),
    )?;
    let jobs = positive(&object, "jobs", path)?;
    match execution_lane {
        PerformanceFixtureExecutionLane::CliLocal => {
            if process_memo_policy != PerformanceFixtureProcessMemoPolicy::Disabled
                || decode_cache_policy != PerformanceFixtureDecodeCachePolicy::Disabled
                || (audit_cache_policy != PerformanceFixtureAuditCachePolicy::Off
                    && disk_memo_policy != PerformanceFixtureDiskMemoPolicy::Off)
            {
                return Err(PerformanceFixtureV02Error::new(format!(
                    "{path} has an incompatible cli-local policy matrix"
                )));
            }
            if (audit_cache_policy != PerformanceFixtureAuditCachePolicy::Off
                || disk_memo_policy != PerformanceFixtureDiskMemoPolicy::Off)
                && jobs != 1
            {
                return Err(PerformanceFixtureV02Error::new(format!(
                    "{path} cache-backed cli-local rows require jobs=1"
                )));
            }
        }
        PerformanceFixtureExecutionLane::Api => {
            if audit_cache_policy != PerformanceFixtureAuditCachePolicy::Off
                || disk_memo_policy != PerformanceFixtureDiskMemoPolicy::Off
            {
                return Err(PerformanceFixtureV02Error::new(format!(
                    "{path} has an incompatible api policy matrix"
                )));
            }
        }
    }
    Ok(PerformanceFixtureSelectionV02::PackageArtifactSnapshot(
        PackageArtifactSnapshotFixture {
            common,
            package_root,
            execution_lane,
            fixture_profile,
            artifact_mode,
            artifact_bytes,
            verifier,
            audit_cache_policy,
            disk_memo_policy,
            process_memo_policy,
            decode_cache_policy,
            jobs,
        },
    ))
}

fn parse_clone(
    value: &JsonValue<'_>,
    path: &str,
    small: bool,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let object = exact_object(
        value,
        path,
        &[
            "id",
            "kind",
            "measurement_mode",
            "warmup",
            "samples",
            "notes",
            "interleave_group",
            "implementation",
            "fixture_profile",
            "payload_bytes",
            "clone_count",
        ],
    )?;
    let fixture = SharedPayloadCloneFixture {
        common: common(&object, path)?,
        implementation: PerformanceFixtureImplementation::parse(
            &get_text(&object, "implementation", path)?,
            &format!("{path}.implementation"),
        )?,
        fixture_profile: PerformanceFixtureProfile::parse(
            &get_text(&object, "fixture_profile", path)?,
            &format!("{path}.fixture_profile"),
        )?,
        payload_bytes: positive(&object, "payload_bytes", path)?,
        clone_count: positive(&object, "clone_count", path)?,
    };
    require_sampling(&fixture.common, 7, path)?;
    let valid = if small {
        fixture.fixture_profile == PerformanceFixtureProfile::SmallCertificate
    } else {
        matches!(
            fixture.fixture_profile,
            PerformanceFixtureProfile::Payload1Mib
                | PerformanceFixtureProfile::Payload16Mib
                | PerformanceFixtureProfile::PayloadNearLimit
        )
    };
    if !valid {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.fixture_profile is incompatible with its tag"
        )));
    }
    let expected_payload_bytes = match fixture.fixture_profile {
        PerformanceFixtureProfile::Payload1Mib => 1_048_576,
        PerformanceFixtureProfile::Payload16Mib => 16_777_216,
        PerformanceFixtureProfile::PayloadNearLimit => 67_108_000,
        PerformanceFixtureProfile::SmallCertificate => 1_024,
        _ => unreachable!("clone profiles were checked above"),
    };
    if fixture.payload_bytes != expected_payload_bytes
        || (!small && !matches!(fixture.clone_count, 1 | 8 | 32 | 256))
        || (small && fixture.clone_count != 256)
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path} has bytes or clone count outside the closed catalog"
        )));
    }
    Ok(if small {
        PerformanceFixtureSelectionV02::SharedPayloadSmall(fixture)
    } else {
        PerformanceFixtureSelectionV02::SharedPayloadClone(fixture)
    })
}

fn parse_cache(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let object = exact_object(
        value,
        path,
        &[
            "id",
            "kind",
            "measurement_mode",
            "warmup",
            "samples",
            "notes",
            "interleave_group",
            "fixture_profile",
            "payload_bytes",
            "phase",
            "decode_cache_policy",
        ],
    )?;
    let fixture = SharedPayloadCacheFixture {
        common: common(&object, path)?,
        fixture_profile: PerformanceFixtureProfile::parse(
            &get_text(&object, "fixture_profile", path)?,
            &format!("{path}.fixture_profile"),
        )?,
        payload_bytes: positive(&object, "payload_bytes", path)?,
        phase: PerformanceFixtureCachePhase::parse(
            &get_text(&object, "phase", path)?,
            &format!("{path}.phase"),
        )?,
        decode_cache_policy: PerformanceFixtureDecodeCachePolicy::parse(
            &get_text(&object, "decode_cache_policy", path)?,
            &format!("{path}.decode_cache_policy"),
        )?,
    };
    require_sampling(&fixture.common, 7, path)?;
    if fixture.fixture_profile != PerformanceFixtureProfile::Payload1Mib {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.fixture_profile must be payload-1mib"
        )));
    }
    if fixture.payload_bytes != 1_048_576 {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.payload_bytes must equal 1048576"
        )));
    }
    let phase_policy_matches = matches!(
        (fixture.phase, fixture.decode_cache_policy),
        (
            PerformanceFixtureCachePhase::Cold,
            PerformanceFixtureDecodeCachePolicy::Disabled
        ) | (
            PerformanceFixtureCachePhase::MissInsert | PerformanceFixtureCachePhase::Hit,
            PerformanceFixtureDecodeCachePolicy::ProcessLocal
                | PerformanceFixtureDecodeCachePolicy::ProcessLocalAndPersistent
        )
    );
    if !phase_policy_matches {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path} cache phase and decode-cache policy are incompatible"
        )));
    }
    Ok(PerformanceFixtureSelectionV02::SharedPayloadCache(fixture))
}

fn parse_memo(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let object = exact_object(
        value,
        path,
        &[
            "id",
            "kind",
            "measurement_mode",
            "warmup",
            "samples",
            "notes",
            "interleave_group",
            "fixture_profile",
            "phase",
            "decode_cache_policy",
            "process_memo_policy",
            "jobs",
        ],
    )?;
    let fixture = SharedPayloadMemoFixture {
        common: common(&object, path)?,
        fixture_profile: PerformanceFixtureProfile::parse(
            &get_text(&object, "fixture_profile", path)?,
            &format!("{path}.fixture_profile"),
        )?,
        phase: PerformanceFixtureMemoPhase::parse(
            &get_text(&object, "phase", path)?,
            &format!("{path}.phase"),
        )?,
        decode_cache_policy: PerformanceFixtureDecodeCachePolicy::parse(
            &get_text(&object, "decode_cache_policy", path)?,
            &format!("{path}.decode_cache_policy"),
        )?,
        process_memo_policy: PerformanceFixtureProcessMemoPolicy::parse(
            &get_text(&object, "process_memo_policy", path)?,
            &format!("{path}.process_memo_policy"),
        )?,
        jobs: positive(&object, "jobs", path)?,
    };
    require_sampling(&fixture.common, 7, path)?;
    if fixture.fixture_profile != PerformanceFixtureProfile::PayloadHeavyMultiModule {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.fixture_profile must be payload-heavy-multi-module"
        )));
    }
    if fixture.decode_cache_policy != PerformanceFixtureDecodeCachePolicy::Disabled
        || fixture.process_memo_policy != PerformanceFixtureProcessMemoPolicy::ProcessLocal
        || fixture.jobs != 1
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path} has an incompatible process-memo policy matrix"
        )));
    }
    Ok(PerformanceFixtureSelectionV02::SharedPayloadMemo(fixture))
}

fn parse_session(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let object = exact_object(
        value,
        path,
        &[
            "id",
            "kind",
            "measurement_mode",
            "warmup",
            "samples",
            "notes",
            "interleave_group",
            "implementation",
            "fixture_profile",
            "session_entries",
            "phase",
        ],
    )?;
    let fixture = SharedPayloadSessionFixture {
        common: common(&object, path)?,
        implementation: PerformanceFixtureImplementation::parse(
            &get_text(&object, "implementation", path)?,
            &format!("{path}.implementation"),
        )?,
        fixture_profile: PerformanceFixtureProfile::parse(
            &get_text(&object, "fixture_profile", path)?,
            &format!("{path}.fixture_profile"),
        )?,
        session_entries: positive(&object, "session_entries", path)?,
        phase: PerformanceFixtureSessionPhase::parse(
            &get_text(&object, "phase", path)?,
            &format!("{path}.phase"),
        )?,
    };
    require_sampling(&fixture.common, 7, path)?;
    if fixture.fixture_profile != PerformanceFixtureProfile::SessionIndex {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.fixture_profile must be session-index"
        )));
    }
    if !matches!(fixture.session_entries, 1 | 64 | 1_024) {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.session_entries is outside the closed catalog"
        )));
    }
    Ok(PerformanceFixtureSelectionV02::SharedPayloadSession(
        fixture,
    ))
}

fn parse_shard(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<PerformanceFixtureSelectionV02, PerformanceFixtureV02Error> {
    let object = exact_object(
        value,
        path,
        &[
            "id",
            "kind",
            "measurement_mode",
            "warmup",
            "samples",
            "notes",
            "interleave_group",
            "fixture_profile",
            "decode_cache_policy",
            "process_memo_policy",
            "jobs",
        ],
    )?;
    let fixture = SharedPayloadShardFixture {
        common: common(&object, path)?,
        fixture_profile: PerformanceFixtureProfile::parse(
            &get_text(&object, "fixture_profile", path)?,
            &format!("{path}.fixture_profile"),
        )?,
        decode_cache_policy: PerformanceFixtureDecodeCachePolicy::parse(
            &get_text(&object, "decode_cache_policy", path)?,
            &format!("{path}.decode_cache_policy"),
        )?,
        process_memo_policy: PerformanceFixtureProcessMemoPolicy::parse(
            &get_text(&object, "process_memo_policy", path)?,
            &format!("{path}.process_memo_policy"),
        )?,
        jobs: positive(&object, "jobs", path)?,
    };
    require_sampling(&fixture.common, 7, path)?;
    if fixture.fixture_profile != PerformanceFixtureProfile::PayloadHeavyMultiModule {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.fixture_profile must be payload-heavy-multi-module"
        )));
    }
    if fixture.decode_cache_policy != PerformanceFixtureDecodeCachePolicy::Disabled
        || fixture.process_memo_policy != PerformanceFixtureProcessMemoPolicy::Disabled
        || !matches!(fixture.jobs, 1 | 8)
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path} has an incompatible shard policy matrix"
        )));
    }
    Ok(PerformanceFixtureSelectionV02::SharedPayloadShard(fixture))
}

fn common(
    object: &BTreeMap<String, &JsonValue<'_>>,
    path: &str,
) -> Result<PerformanceFixtureCommonV02, PerformanceFixtureV02Error> {
    let id = get_text(object, "id", path)?;
    require_nonempty(&id, &format!("{path}.id"))?;
    let notes = get_text(object, "notes", path)?;
    if notes != PERFORMANCE_FIXTURE_NOTES_V0_2 {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.notes must equal the closed v0.2 advisory note"
        )));
    }
    let interleave_group = get_text(object, "interleave_group", path)?;
    require_nonempty(&interleave_group, &format!("{path}.interleave_group"))?;
    Ok(PerformanceFixtureCommonV02 {
        id,
        measurement_mode: PerformanceFixtureMeasurementMode::parse(
            &get_text(object, "measurement_mode", path)?,
            &format!("{path}.measurement_mode"),
        )?,
        warmup: natural(object, "warmup", path)?,
        samples: positive(object, "samples", path)?,
        notes,
        interleave_group,
    })
}

fn require_sampling(
    common: &PerformanceFixtureCommonV02,
    samples: u64,
    path: &str,
) -> Result<(), PerformanceFixtureV02Error> {
    if common.warmup == 1 && common.samples == samples {
        Ok(())
    } else {
        Err(PerformanceFixtureV02Error::new(format!(
            "{path} must use warmup=1 and samples={samples}"
        )))
    }
}

fn object<'a>(
    value: &'a JsonValue<'a>,
    path: &str,
) -> Result<BTreeMap<String, &'a JsonValue<'a>>, PerformanceFixtureV02Error> {
    let members = value
        .object_members()
        .ok_or_else(|| PerformanceFixtureV02Error::new(format!("{path} must be an object")))?;
    let mut result = BTreeMap::new();
    for member in members {
        if result
            .insert(member.key().to_owned(), member.value())
            .is_some()
        {
            return Err(PerformanceFixtureV02Error::new(format!(
                "{path}.{} is duplicated",
                member.key()
            )));
        }
    }
    Ok(result)
}

fn exact_object<'a>(
    value: &'a JsonValue<'a>,
    path: &str,
    fields: &[&str],
) -> Result<BTreeMap<String, &'a JsonValue<'a>>, PerformanceFixtureV02Error> {
    let object = object(value, path)?;
    if object.len() != fields.len()
        || fields.iter().any(|field| !object.contains_key(*field))
        || object.keys().any(|field| !fields.contains(&field.as_str()))
    {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path} has missing or unknown fields"
        )));
    }
    Ok(object)
}

fn field<'a>(
    object: &'a BTreeMap<String, &'a JsonValue<'a>>,
    name: &str,
    path: &str,
) -> Result<&'a JsonValue<'a>, PerformanceFixtureV02Error> {
    object
        .get(name)
        .copied()
        .ok_or_else(|| PerformanceFixtureV02Error::new(format!("{path}.{name} is missing")))
}

fn get_text(
    object: &BTreeMap<String, &JsonValue<'_>>,
    name: &str,
    path: &str,
) -> Result<String, PerformanceFixtureV02Error> {
    field(object, name, path)?
        .string_value()
        .map(ToOwned::to_owned)
        .ok_or_else(|| PerformanceFixtureV02Error::new(format!("{path}.{name} must be a string")))
}

fn require_text(
    object: &BTreeMap<String, &JsonValue<'_>>,
    name: &str,
    expected: &str,
    path: &str,
) -> Result<(), PerformanceFixtureV02Error> {
    let actual = get_text(object, name, path)?;
    if actual == expected {
        Ok(())
    } else {
        Err(PerformanceFixtureV02Error::new(format!(
            "{path} must equal '{expected}'"
        )))
    }
}

fn natural(
    object: &BTreeMap<String, &JsonValue<'_>>,
    name: &str,
    path: &str,
) -> Result<u64, PerformanceFixtureV02Error> {
    let raw = field(object, name, path)?.number_raw().ok_or_else(|| {
        PerformanceFixtureV02Error::new(format!("{path}.{name} must be a natural number"))
    })?;
    if raw.starts_with('-') || raw.contains(['.', 'e', 'E']) {
        return Err(PerformanceFixtureV02Error::new(format!(
            "{path}.{name} must be a natural number"
        )));
    }
    raw.parse::<u64>().map_err(|_| {
        PerformanceFixtureV02Error::new(format!("{path}.{name} must be a natural number"))
    })
}

fn positive(
    object: &BTreeMap<String, &JsonValue<'_>>,
    name: &str,
    path: &str,
) -> Result<u64, PerformanceFixtureV02Error> {
    let value = natural(object, name, path)?;
    if value == 0 {
        Err(PerformanceFixtureV02Error::new(format!(
            "{path}.{name} must be positive"
        )))
    } else {
        Ok(value)
    }
}

fn require_nonempty(value: &str, path: &str) -> Result<(), PerformanceFixtureV02Error> {
    if value.is_empty() {
        Err(PerformanceFixtureV02Error::new(format!(
            "{path} must be nonempty"
        )))
    } else {
        Ok(())
    }
}

fn string_array(
    object: &BTreeMap<String, &JsonValue<'_>>,
    name: &str,
    path: &str,
) -> Result<Vec<String>, PerformanceFixtureV02Error> {
    let values = field(object, name, path)?.array_elements().ok_or_else(|| {
        PerformanceFixtureV02Error::new(format!("{path}.{name} must be an array"))
    })?;
    let mut parsed = Vec::with_capacity(values.len());
    for value in values {
        parsed.push(value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
            PerformanceFixtureV02Error::new(format!("{path}.{name} must contain strings"))
        })?);
    }
    Ok(parsed)
}

fn validate_relative_path(value: &str, path: &str) -> Result<(), PerformanceFixtureV02Error> {
    if value.is_empty()
        || value.starts_with('/')
        || value
            .split('/')
            .any(|component| matches!(component, "" | "." | ".."))
    {
        Err(PerformanceFixtureV02Error::new(format!(
            "{path} must be a normalized relative path"
        )))
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SNAPSHOT_RAW: &str = r#"{"id":"package-artifact-snapshot-1k-api-pm0-dc0-fast-raw-j1","kind":"package-artifact-snapshot","measurement_mode":"detailed","warmup":1,"samples":5,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"package-artifact-snapshot-1k-api-pm0-dc0-fast-j1","package_root":"generated/synthetic-1kib","execution_lane":"api","fixture_profile":"synthetic-1kib","artifact_mode":"raw","artifact_bytes":1024,"verifier":"fast","audit_cache_policy":"off","disk_memo_policy":"off","process_memo_policy":"disabled","decode_cache_policy":"disabled","jobs":1}"#;
    const SNAPSHOT_OWNED: &str = r#"{"id":"package-artifact-snapshot-1k-api-pm0-dc0-fast-snapshot-j1","kind":"package-artifact-snapshot","measurement_mode":"detailed","warmup":1,"samples":5,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"package-artifact-snapshot-1k-api-pm0-dc0-fast-j1","package_root":"generated/synthetic-1kib","execution_lane":"api","fixture_profile":"synthetic-1kib","artifact_mode":"snapshot","artifact_bytes":1024,"verifier":"fast","audit_cache_policy":"off","disk_memo_policy":"off","process_memo_policy":"disabled","decode_cache_policy":"disabled","jobs":1}"#;
    const CLONE: &str = r#"{"id":"shared-payload-clone-1m-c1-legacy","kind":"shared-payload-clone","measurement_mode":"detailed","warmup":1,"samples":7,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"shared-payload-clone-1m-c1","implementation":"legacy-model","fixture_profile":"payload-1mib","payload_bytes":1048576,"clone_count":1}"#;
    const CACHE: &str = r#"{"id":"shared-payload-cache-1m-cold-disabled","kind":"shared-payload-cache","measurement_mode":"detailed","warmup":1,"samples":7,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"shared-payload-cache-1m","fixture_profile":"payload-1mib","payload_bytes":1048576,"phase":"cold","decode_cache_policy":"disabled"}"#;
    const MEMO: &str = r#"{"id":"shared-payload-memo-multi-miss","kind":"shared-payload-memo","measurement_mode":"detailed","warmup":1,"samples":7,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"shared-payload-memo-multi","fixture_profile":"payload-heavy-multi-module","phase":"miss","decode_cache_policy":"disabled","process_memo_policy":"process-local","jobs":1}"#;
    const SESSION: &str = r#"{"id":"shared-payload-session-s1-snapshot-legacy","kind":"shared-payload-session","measurement_mode":"detailed","warmup":1,"samples":7,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"shared-payload-session-s1-snapshot","implementation":"legacy-model","fixture_profile":"session-index","session_entries":1,"phase":"snapshot"}"#;
    const SHARD: &str = r#"{"id":"shared-payload-shard-multi-j1","kind":"shared-payload-shard","measurement_mode":"detailed","warmup":1,"samples":7,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"shared-payload-shard-multi","fixture_profile":"payload-heavy-multi-module","decode_cache_policy":"disabled","process_memo_policy":"disabled","jobs":1}"#;
    const SMALL: &str = r#"{"id":"shared-payload-small-1k-c256-legacy","kind":"shared-payload-small","measurement_mode":"detailed","warmup":1,"samples":7,"notes":"Blocking deterministic counters; elapsed and RSS advisory.","interleave_group":"shared-payload-small-1k-c256","implementation":"legacy-model","fixture_profile":"small-certificate","payload_bytes":1024,"clone_count":256}"#;
    const INHERITED_WARMED: &str = r#"{"id":"compact-package-fast","kind":"warmed-checked-artifact-verifier","package_root":"testdata/package/npa-std","verifier":"fast","cache_policy":"disabled","warmup":1,"samples":3,"notes":"Historical warmed row."}"#;

    fn manifest(rows: &[&str]) -> String {
        format!(
            r#"{{"schema":"{PERFORMANCE_FIXTURES_SCHEMA_V0_2}","scenarios":[{}]}}"#,
            rows.join(",")
        )
    }

    #[test]
    fn performance_fixture_selected_union() {
        let snapshot = manifest(&[SNAPSHOT_RAW, SNAPSHOT_OWNED]);
        let clone_shared = CLONE
            .replacen("-legacy\"", "-shared\"", 1)
            .replace("\"legacy-model\"", "\"shared-handle\"");
        let session_shared = SESSION
            .replacen("-legacy\"", "-shared\"", 1)
            .replace("\"legacy-model\"", "\"shared-handle\"");
        let small_shared = SMALL
            .replacen("-legacy\"", "-shared\"", 1)
            .replace("\"legacy-model\"", "\"shared-handle\"");
        let cache_miss = CACHE
            .replace("-cold-disabled\"", "-miss-process-local\"")
            .replace("\"phase\":\"cold\"", "\"phase\":\"miss-insert\"")
            .replace(
                "\"decode_cache_policy\":\"disabled\"",
                "\"decode_cache_policy\":\"process-local\"",
            );
        let cache_hit = cache_miss
            .replace("-miss-process-local\"", "-hit-process-local\"")
            .replace("\"phase\":\"miss-insert\"", "\"phase\":\"hit\"");
        let cache_miss_persistent = cache_miss
            .replace("-miss-process-local\"", "-miss-persistent\"")
            .replace("\"process-local\"", "\"process-local-and-persistent\"");
        let cache_hit_persistent = cache_miss_persistent
            .replace("-miss-persistent\"", "-hit-persistent\"")
            .replace("\"phase\":\"miss-insert\"", "\"phase\":\"hit\"");
        let memo_hit = MEMO
            .replace("-miss\"", "-hit\"")
            .replace("\"phase\":\"miss\"", "\"phase\":\"hit\"");
        let shard_eight = SHARD
            .replace("-j1\"", "-j8\"")
            .replace("\"jobs\":1", "\"jobs\":8");
        let parsed = validate_performance_fixture_selection_v02(&snapshot).unwrap();
        assert_eq!(parsed.scenarios.len(), 2);
        assert!(matches!(
            parsed.scenarios[0],
            PerformanceFixtureSelectionV02::PackageArtifactSnapshot(_)
        ));
        assert!(validate_performance_fixture_selection_v02(
            &snapshot.replace("\"jobs\":1", "\"jobs\":0")
        )
        .is_err());
        assert!(validate_performance_fixture_selection_v02(
            &snapshot.replace("\"artifact_mode\":\"raw\"", "\"artifact_mode\":\"unknown\"")
        )
        .is_err());
        assert!(validate_performance_fixture_selection_v02(
            &snapshot.replace("\"notes\":", "\"extra\":0,\"notes\":")
        )
        .is_err());

        let rows = [
            SNAPSHOT_RAW,
            SNAPSHOT_OWNED,
            CLONE,
            &clone_shared,
            CACHE,
            &cache_miss,
            &cache_hit,
            &cache_miss_persistent,
            &cache_hit_persistent,
            MEMO,
            &memo_hit,
            SESSION,
            &session_shared,
            SHARD,
            &shard_eight,
            SMALL,
            &small_shared,
        ];
        let parsed = validate_performance_fixture_selection_v02(&manifest(&rows)).unwrap();
        assert_eq!(parsed.scenarios.len(), 17);
        assert_eq!(
            parsed
                .scenarios
                .iter()
                .filter(|row| matches!(row, PerformanceFixtureSelectionV02::SharedPayloadCache(_)))
                .count(),
            5
        );

        assert!(validate_performance_fixture_selection_v02(&manifest(&[CLONE, CLONE])).is_err());
        assert!(
            validate_performance_fixture_selection_v02(&manifest(&[CLONE]).replace(
                PERFORMANCE_FIXTURES_SCHEMA_V0_2,
                "npa.performance.fixtures.v0.3"
            ))
            .is_err()
        );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[CLONE
            .replace(
                "\"notes\":\"Blocking deterministic counters; elapsed and RSS advisory.\",",
                ""
            )
            .as_str()]))
        .is_err());
        assert!(validate_performance_fixture_selection_v02(&manifest(&[CACHE
            .replace(
                "\"decode_cache_policy\":\"disabled\"",
                "\"decode_cache_policy\":\"process-local\""
            )
            .as_str()]))
        .is_err());
        assert!(validate_performance_fixture_selection_v02(&manifest(&[MEMO
            .replace(
                "\"process_memo_policy\":\"process-local\"",
                "\"process_memo_policy\":\"disabled\""
            )
            .as_str()]))
        .is_err());
        assert!(validate_performance_fixture_selection_v02(&manifest(&[SHARD
            .replace("\"jobs\":1", "\"jobs\":4")
            .as_str()]))
        .is_err());
        assert!(validate_performance_fixture_selection_v02(&manifest(&[INHERITED_WARMED])).is_ok());
        assert!(
            validate_performance_fixture_selection_v02(&manifest(&[INHERITED_WARMED
                .replace("\"verifier\":\"fast\"", "\"verifier\":\"unknown\"")
                .as_str()]))
            .is_err()
        );
    }

    #[test]
    fn performance_fixture_interleave_groups_fail_closed() {
        assert!(validate_performance_fixture_selection_v02(&manifest(&[SNAPSHOT_RAW])).is_err());

        let duplicate_snapshot_mode = SNAPSHOT_OWNED
            .replace("-snapshot-j1\"", "-snapshot-copy-j1\"")
            .replace(
                "\"artifact_mode\":\"snapshot\"",
                "\"artifact_mode\":\"raw\"",
            );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            SNAPSHOT_RAW,
            &duplicate_snapshot_mode,
        ]))
        .is_err());

        let wrong_snapshot_companion = SNAPSHOT_OWNED.replace(
            "\"decode_cache_policy\":\"disabled\"",
            "\"decode_cache_policy\":\"process-local\"",
        );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            SNAPSHOT_RAW,
            &wrong_snapshot_companion,
        ]))
        .is_err());

        let clone_shared = CLONE
            .replacen("-legacy\"", "-shared\"", 1)
            .replace("\"legacy-model\"", "\"shared-handle\"");
        assert!(validate_performance_fixture_selection_v02(&manifest(&[CLONE])).is_err());
        let duplicate_clone_mode = clone_shared.replace("\"shared-handle\"", "\"legacy-model\"");
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            CLONE,
            &duplicate_clone_mode,
        ]))
        .is_err());
        let wrong_clone_companion = clone_shared.replace("\"clone_count\":1", "\"clone_count\":8");
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            CLONE,
            &wrong_clone_companion,
        ]))
        .is_err());

        let false_group_raw = SNAPSHOT_RAW.replace(
            "package-artifact-snapshot-1k-api-pm0-dc0-fast-j1\"",
            "arbitrary-snapshot-group\"",
        );
        let false_group_owned = SNAPSHOT_OWNED.replace(
            "package-artifact-snapshot-1k-api-pm0-dc0-fast-j1\"",
            "arbitrary-snapshot-group\"",
        );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            &false_group_raw,
            &false_group_owned,
        ]))
        .is_err());

        let fake_clone_group = clone_shared
            .replace("shared-payload-clone-1m-c1\"", "renamed-clone-group\"")
            .replace(
                "shared-payload-clone-1m-c1-shared",
                "renamed-clone-group-shared",
            );
        let fake_clone_legacy = CLONE
            .replace("shared-payload-clone-1m-c1\"", "renamed-clone-group\"")
            .replace(
                "shared-payload-clone-1m-c1-legacy",
                "renamed-clone-group-legacy",
            );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            &fake_clone_legacy,
            &fake_clone_group,
        ]))
        .is_err());

        let cache_miss = CACHE
            .replace("-cold-disabled\"", "-miss-process-local\"")
            .replace("\"phase\":\"cold\"", "\"phase\":\"miss-insert\"")
            .replace(
                "\"decode_cache_policy\":\"disabled\"",
                "\"decode_cache_policy\":\"process-local\"",
            );
        let cache_hit = cache_miss
            .replace("-miss-process-local\"", "-hit-process-local\"")
            .replace("\"phase\":\"miss-insert\"", "\"phase\":\"hit\"");
        let cache_miss_persistent = cache_miss
            .replace("-miss-process-local\"", "-miss-persistent\"")
            .replace("\"process-local\"", "\"process-local-and-persistent\"");
        let cache_hit_persistent = cache_miss_persistent
            .replace("-miss-persistent\"", "-hit-persistent\"")
            .replace("\"phase\":\"miss-insert\"", "\"phase\":\"hit\"");
        let cache_group = [
            CACHE,
            &cache_miss,
            &cache_hit,
            &cache_miss_persistent,
            &cache_hit_persistent,
        ];
        assert!(validate_performance_fixture_selection_v02(&manifest(&cache_group)).is_ok());
        assert!(validate_performance_fixture_selection_v02(&manifest(&cache_group[..4])).is_err());
        let wrong_cache_profile =
            cache_hit_persistent.replace("\"payload-1mib\"", "\"payload-16mib\"");
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            CACHE,
            &cache_miss,
            &cache_hit,
            &cache_miss_persistent,
            &wrong_cache_profile,
        ]))
        .is_err());

        let memo_hit = MEMO
            .replace("-miss\"", "-hit\"")
            .replace("\"phase\":\"miss\"", "\"phase\":\"hit\"");
        assert!(validate_performance_fixture_selection_v02(&manifest(&[MEMO, &memo_hit])).is_ok());
        assert!(validate_performance_fixture_selection_v02(&manifest(&[MEMO])).is_err());

        let shard_eight = SHARD
            .replace("-j1\"", "-j8\"")
            .replace("\"jobs\":1", "\"jobs\":8");
        assert!(
            validate_performance_fixture_selection_v02(&manifest(&[SHARD, &shard_eight])).is_ok()
        );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[SHARD])).is_err());

        let wrong_note = SNAPSHOT_OWNED.replace(
            PERFORMANCE_FIXTURE_NOTES_V0_2,
            "Blocking counters, advisory elapsed.",
        );
        assert!(validate_performance_fixture_selection_v02(&manifest(&[
            SNAPSHOT_RAW,
            &wrong_note,
        ]))
        .is_err());
    }

    #[test]
    fn performance_fixture_selected_manifest_seed() {
        let historical_source =
            include_str!("../../../testdata/performance/fixtures/manifest.v0.1.json");
        let source = include_str!("../../../testdata/performance/fixtures/manifest.v0.2.json");
        let parsed = validate_performance_fixture_selection_v02(source).unwrap();
        let historical = JsonDocument::parse(historical_source).unwrap();
        let selected = JsonDocument::parse(source).unwrap();
        let historical_root = object(historical.root(), "historical").unwrap();
        let selected_root = object(selected.root(), "selected").unwrap();
        let historical_rows = field(&historical_root, "scenarios", "historical")
            .unwrap()
            .array_elements()
            .unwrap();
        let selected_rows = field(&selected_root, "scenarios", "selected")
            .unwrap()
            .array_elements()
            .unwrap();
        assert!(selected_rows.len() >= historical_rows.len());
        for (index, (historical_row, selected_row)) in
            historical_rows.iter().zip(selected_rows.iter()).enumerate()
        {
            assert_eq!(
                selected_row.raw_slice(),
                historical_row.raw_slice(),
                "inherited fixture row {index} changed in the successor manifest"
            );
        }
        assert_eq!(
            parsed
                .scenarios
                .iter()
                .take(historical_rows.len())
                .filter(|row| row.is_inherited())
                .count(),
            historical_rows.len()
        );
        type SelectionPredicate = fn(&PerformanceFixtureSelectionV02) -> bool;
        let inherited_variant_counts: [(usize, SelectionPredicate); 4] = [
            (4, |row: &PerformanceFixtureSelectionV02| {
                matches!(
                    row,
                    PerformanceFixtureSelectionV02::WarmedCheckedArtifactVerifier(_)
                )
            }),
            (11, |row: &PerformanceFixtureSelectionV02| {
                matches!(row, PerformanceFixtureSelectionV02::TargetedBuildCerts(_))
            }),
            (11, |row: &PerformanceFixtureSelectionV02| {
                matches!(
                    row,
                    PerformanceFixtureSelectionV02::PackageVerifierProcessMemoScope(_)
                )
            }),
            (25, |row: &PerformanceFixtureSelectionV02| {
                matches!(
                    row,
                    PerformanceFixtureSelectionV02::PackageChangedSelectionGitBatching(_)
                )
            }),
        ];
        for (expected, predicate) in inherited_variant_counts {
            assert_eq!(
                parsed.scenarios.iter().filter(|row| predicate(row)).count(),
                expected
            );
        }
        assert_eq!(
            parsed
                .scenarios
                .iter()
                .filter(|row| matches!(
                    row,
                    PerformanceFixtureSelectionV02::PackageArtifactSnapshot(_)
                ))
                .count(),
            40
        );
        assert_eq!(
            parsed
                .scenarios
                .iter()
                .filter(|row| matches!(
                    row,
                    PerformanceFixtureSelectionV02::SharedPayloadClone(_)
                        | PerformanceFixtureSelectionV02::SharedPayloadCache(_)
                        | PerformanceFixtureSelectionV02::SharedPayloadMemo(_)
                        | PerformanceFixtureSelectionV02::SharedPayloadSession(_)
                        | PerformanceFixtureSelectionV02::SharedPayloadShard(_)
                        | PerformanceFixtureSelectionV02::SharedPayloadSmall(_)
                ))
                .count(),
            47
        );
        let mut ids = parsed
            .scenarios
            .iter()
            .map(PerformanceFixtureSelectionV02::id)
            .collect::<Vec<_>>();
        let length = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), length);
    }

    #[test]
    fn performance_fixture_checked_catalog_rejects_any_order_or_row_change() {
        let checked = CHECKED_PERFORMANCE_FIXTURE_MANIFEST_V0_2;
        let parsed = validate_checked_performance_fixture_selection_v02(checked).unwrap();
        assert_eq!(parsed.scenarios.len(), 138);
        let ids = parsed
            .scenarios
            .iter()
            .map(PerformanceFixtureSelectionV02::id)
            .collect::<Vec<_>>();
        assert_eq!(ids[0], "compact-package-fast");
        assert_eq!(
            ids[51],
            "package-artifact-snapshot-rep-api-pm0-dc0-fast-raw-j1"
        );
        assert_eq!(
            ids[90],
            "package-artifact-snapshot-rep-api-pm0-dc0-fast-snapshot-j8"
        );
        assert_eq!(ids[91], "shared-payload-clone-1m-c1-legacy");
        assert_eq!(ids[137], "shared-payload-small-1k-c256-shared");

        let renamed = checked.replacen(
            "package-artifact-snapshot-rep-api-pm0-dc0-fast-j1",
            "package-artifact-snapshot-renamed-api-pm0-dc0-fast-j1",
            2,
        );
        assert!(validate_checked_performance_fixture_selection_v02(&renamed).is_err());

        let marker = "    {\"id\":\"package-artifact-snapshot-rep-api-pm0-dc0-fast-raw-j1\"";
        let first = checked.find(marker).unwrap();
        let next = checked[first + marker.len()..]
            .find("    {\"id\":")
            .unwrap()
            + first
            + marker.len();
        let end = checked[next..].find("\n").unwrap() + next + 1;
        let first_end = checked[first..].find("\n").unwrap() + first + 1;
        let swapped = format!(
            "{}{}{}{}{}",
            &checked[..first],
            &checked[next..end],
            &checked[first_end..next],
            &checked[first..first_end],
            &checked[end..]
        );
        assert!(validate_checked_performance_fixture_selection_v02(&swapped).is_err());

        let missing = format!("{}{}", &checked[..first], &checked[first_end..]);
        assert!(validate_checked_performance_fixture_selection_v02(&missing).is_err());
        let duplicated = format!(
            "{}{}{}",
            &checked[..first_end],
            &checked[first..first_end],
            &checked[first_end..]
        );
        assert!(validate_checked_performance_fixture_selection_v02(&duplicated).is_err());
    }

    #[test]
    fn performance_fixture_snapshot_selected_schema() {
        performance_fixture_selected_union();
        performance_fixture_selected_manifest_seed();
    }

    #[test]
    fn snapshot_manifest_selected_schema() {
        performance_fixture_selected_manifest_seed();
        performance_fixture_legacy_dispatch_preserves_historical_acceptance();
    }

    #[test]
    fn performance_fixture_legacy_api() {
        let source = include_str!("../../../testdata/performance/fixtures/manifest.v0.1.json");
        assert_eq!(
            validate_versioned_performance_fixture_selection(source).unwrap(),
            VersionedPerformanceFixtureSelection::V01 { scenario_count: 51 }
        );
        let changed = source.replace(
            "npa.performance.fixtures.v0.1",
            "npa.performance.fixtures.v0.0",
        );
        assert!(validate_versioned_performance_fixture_selection(&changed).is_err());
    }

    #[test]
    fn performance_fixture_legacy_dispatch_preserves_historical_acceptance() {
        let source = r#"{"schema":"npa.performance.fixtures.v0.1","scenarios":[{"id":"legacy-targeted","kind":"targeted-build-certs","package_root":"testdata/legacy-targeted","verifier":"build-certs-check","cache_policy":"off","warmup":0,"samples":1,"support_module_count":1,"target_module_count":1,"target_edit":"append-comment-without-support-identity-change","notes":"Historical row without the later population contract."}]}"#;
        assert_eq!(
            validate_versioned_performance_fixture_selection(source).unwrap(),
            VersionedPerformanceFixtureSelection::V01 { scenario_count: 1 }
        );

        let unsupported_verifier = source.replace("build-certs-check", "fast");
        assert!(validate_versioned_performance_fixture_selection(&unsupported_verifier).is_err());
    }
}
