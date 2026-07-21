//! Strict local performance-fixture and deterministic-baseline validation.

use std::{collections::BTreeMap, fmt};

use crate::json::{JsonDocument, JsonValue};
use crate::{
    PerformanceMeasurementLabel, PerformanceMeasurementReport, PERFORMANCE_MEASUREMENTS_SCHEMA,
};

/// Schema for the checked-in performance fixture manifest.
pub const PERFORMANCE_FIXTURES_SCHEMA: &str = "npa.performance.fixtures.v0.1";
/// Schema for deterministic performance baselines.
pub const PERFORMANCE_BASELINES_SCHEMA: &str = "npa.performance.baselines.v0.1";

/// Explicit scenario selection supplied to the local performance harness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PerformanceFixtureSelection<'a> {
    pub scenario: &'a str,
    pub kind: &'a str,
    pub package_root: &'a str,
    pub verifier: &'a str,
    pub cache_policy: &'a str,
    pub warmup: u64,
    pub samples: u64,
}

/// Malformed fixture metadata or a deterministic baseline mismatch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerformanceGateValidationError {
    message: String,
}

impl PerformanceGateValidationError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for PerformanceGateValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for PerformanceGateValidationError {}

/// Strictly validate a fixture manifest and bind the selected scenario to the
/// explicit harness arguments.
pub fn validate_performance_fixture_selection(
    source: &str,
    selection: PerformanceFixtureSelection<'_>,
) -> Result<(), PerformanceGateValidationError> {
    let document = JsonDocument::parse(source).map_err(|error| {
        PerformanceGateValidationError::new(format!(
            "performance fixture manifest is invalid JSON at byte {}",
            error.offset
        ))
    })?;
    let root = closed_object(document.root(), "$", &["schema", "scenarios"])?;
    require_exact_text(&root, "schema", PERFORMANCE_FIXTURES_SCHEMA, "$.schema")?;
    let scenarios = array(field(&root, "scenarios", "$")?, "$.scenarios")?;
    let mut selected = 0usize;
    let mut ids = BTreeMap::new();
    for (index, scenario) in scenarios.iter().enumerate() {
        let path = format!("$.scenarios[{index}]");
        let object = closed_object(
            scenario,
            &path,
            &[
                "id",
                "kind",
                "package_root",
                "verifier",
                "cache_policy",
                "warmup",
                "samples",
                "notes",
            ],
        )?;
        let id = text(field(&object, "id", &path)?, &format!("{path}.id"))?;
        if id.is_empty() || ids.insert(id, index).is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.id must be nonempty and unique"
            )));
        }
        let kind = text(field(&object, "kind", &path)?, &format!("{path}.kind"))?;
        let package_root = text(
            field(&object, "package_root", &path)?,
            &format!("{path}.package_root"),
        )?;
        validate_relative_path(package_root, &format!("{path}.package_root"))?;
        let verifier = text(
            field(&object, "verifier", &path)?,
            &format!("{path}.verifier"),
        )?;
        if !matches!(verifier, "fast" | "reference") {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.verifier is unsupported"
            )));
        }
        let cache_policy = text(
            field(&object, "cache_policy", &path)?,
            &format!("{path}.cache_policy"),
        )?;
        if cache_policy != "disabled" {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.cache_policy is unsupported"
            )));
        }
        let warmup = natural(field(&object, "warmup", &path)?, &format!("{path}.warmup"))?;
        let samples = natural(
            field(&object, "samples", &path)?,
            &format!("{path}.samples"),
        )?;
        if samples == 0 {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.samples must be positive"
            )));
        }
        let notes = text(field(&object, "notes", &path)?, &format!("{path}.notes"))?;
        if notes.is_empty() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.notes must be nonempty"
            )));
        }
        if id == selection.scenario {
            selected += 1;
            for (field_name, expected, actual) in [
                ("kind", selection.kind, kind),
                ("package_root", selection.package_root, package_root),
                ("verifier", selection.verifier, verifier),
                ("cache_policy", selection.cache_policy, cache_policy),
            ] {
                if actual != expected {
                    return Err(PerformanceGateValidationError::new(format!(
                        "{path}.{field_name} disagrees with the harness argument"
                    )));
                }
            }
            if warmup != selection.warmup || samples != selection.samples {
                return Err(PerformanceGateValidationError::new(format!(
                    "{path} warmup/sample counts disagree with the harness arguments"
                )));
            }
        }
    }
    if selected != 1 {
        return Err(PerformanceGateValidationError::new(format!(
            "fixture scenario '{}' was not selected exactly once",
            selection.scenario
        )));
    }
    Ok(())
}

/// Strictly validate all deterministic expectations for one scenario against
/// the completed common measurement report.
pub fn validate_performance_measurement_baseline(
    source: &str,
    scenario_id: &str,
    report: &PerformanceMeasurementReport,
) -> Result<(), PerformanceGateValidationError> {
    if report.schema != PERFORMANCE_MEASUREMENTS_SCHEMA
        || report.trusted
        || report.proof_evidence
        || report.overflowed
    {
        return Err(PerformanceGateValidationError::new(
            "performance report has an incompatible schema, trust boundary, or overflow",
        ));
    }
    let mut previous_counter = None;
    for counter in &report.counters {
        let label = counter.label.as_str();
        if previous_counter.is_some_and(|previous| previous >= label)
            || counter.unit != counter.label.unit()
        {
            return Err(PerformanceGateValidationError::new(
                "performance report counters are not canonical",
            ));
        }
        previous_counter = Some(label);
    }
    let document = JsonDocument::parse(source).map_err(|error| {
        PerformanceGateValidationError::new(format!(
            "performance baseline is invalid JSON at byte {}",
            error.offset
        ))
    })?;
    let root = closed_object(
        document.root(),
        "$",
        &["schema", "measurement_schema", "scenarios", "update_policy"],
    )?;
    require_exact_text(&root, "schema", PERFORMANCE_BASELINES_SCHEMA, "$.schema")?;
    require_exact_text(
        &root,
        "measurement_schema",
        PERFORMANCE_MEASUREMENTS_SCHEMA,
        "$.measurement_schema",
    )?;
    if text(field(&root, "update_policy", "$")?, "$.update_policy")?.is_empty() {
        return Err(PerformanceGateValidationError::new(
            "$.update_policy must be nonempty",
        ));
    }

    let scenarios = array(field(&root, "scenarios", "$")?, "$.scenarios")?;
    let mut selected = 0usize;
    let mut ids = BTreeMap::new();
    for (index, scenario) in scenarios.iter().enumerate() {
        let path = format!("$.scenarios[{index}]");
        let object = closed_object(
            scenario,
            &path,
            &[
                "id",
                "status",
                "module_count",
                "deterministic_counters",
                "coverage",
            ],
        )?;
        let id = text(field(&object, "id", &path)?, &format!("{path}.id"))?;
        if id.is_empty() || ids.insert(id, index).is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.id must be nonempty and unique"
            )));
        }
        require_exact_text(&object, "status", "passed", &format!("{path}.status"))?;
        let module_count = natural(
            field(&object, "module_count", &path)?,
            &format!("{path}.module_count"),
        )?;
        let counters_path = format!("{path}.deterministic_counters");
        let raw_counters = field(&object, "deterministic_counters", &path)?;
        open_object(raw_counters, &counters_path)?;
        let counter_members = raw_counters
            .object_members()
            .expect("object shape was checked above");
        if counter_members.is_empty() {
            return Err(PerformanceGateValidationError::new(format!(
                "{counters_path} must not be empty"
            )));
        }
        let mut previous = None;
        for member in counter_members {
            let label = member.key();
            if previous.is_some_and(|previous| previous >= label) {
                return Err(PerformanceGateValidationError::new(format!(
                    "{counters_path} labels are not in canonical order"
                )));
            }
            previous = Some(label);
            let Some(label_value) = PerformanceMeasurementLabel::ALL
                .iter()
                .copied()
                .find(|candidate| candidate.as_str() == label)
            else {
                return Err(PerformanceGateValidationError::new(format!(
                    "{counters_path}.{label} is not a stable measurement label"
                )));
            };
            let expected = natural(member.value(), &format!("{counters_path}.{label}"))?;
            if id == scenario_id && counter_value(report, label_value) != Some(expected) {
                return Err(PerformanceGateValidationError::new(format!(
                    "deterministic baseline mismatch for {label}"
                )));
            }
        }
        let coverage_path = format!("{path}.coverage");
        let coverage = closed_object(
            field(&object, "coverage", &path)?,
            &coverage_path,
            &["live_results_min", "proof_evidence_reduction_allowed"],
        )?;
        let live_min = natural(
            field(&coverage, "live_results_min", &coverage_path)?,
            &format!("{coverage_path}.live_results_min"),
        )?;
        let reduction_allowed = boolean(
            field(
                &coverage,
                "proof_evidence_reduction_allowed",
                &coverage_path,
            )?,
            &format!("{coverage_path}.proof_evidence_reduction_allowed"),
        )?;

        if id == scenario_id {
            selected += 1;
            let live =
                counter_value(report, PerformanceMeasurementLabel::PackageLiveResults).unwrap_or(0);
            let cache = counter_value(report, PerformanceMeasurementLabel::PackageCacheResults)
                .unwrap_or(0);
            let memo =
                counter_value(report, PerformanceMeasurementLabel::PackageMemoResults).unwrap_or(0);
            if live.saturating_add(cache).saturating_add(memo) != module_count {
                return Err(PerformanceGateValidationError::new(
                    "measured module coverage disagrees with baseline module_count",
                ));
            }
            if live < live_min
                || (!reduction_allowed && (live < module_count || cache != 0 || memo != 0))
            {
                return Err(PerformanceGateValidationError::new(
                    "measured live verification coverage is below the baseline policy",
                ));
            }
        }
    }
    if selected != 1 {
        return Err(PerformanceGateValidationError::new(format!(
            "baseline scenario '{scenario_id}' was not selected exactly once"
        )));
    }
    Ok(())
}

fn counter_value(
    report: &PerformanceMeasurementReport,
    label: PerformanceMeasurementLabel,
) -> Option<u64> {
    report
        .counters
        .iter()
        .find(|counter| counter.label == label)
        .map(|counter| counter.value)
}

fn validate_relative_path(path: &str, where_: &str) -> Result<(), PerformanceGateValidationError> {
    if path.is_empty()
        || path.starts_with('/')
        || path.contains('\\')
        || path
            .split('/')
            .any(|component| matches!(component, "" | "." | ".."))
    {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} must be a canonical relative path"
        )));
    }
    Ok(())
}

fn closed_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    where_: &str,
    fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'source>>, PerformanceGateValidationError> {
    let object = open_object(value, where_)?;
    if object.len() != fields.len() || object.keys().any(|field| !fields.contains(field)) {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} has missing or unknown fields"
        )));
    }
    Ok(object)
}

fn open_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    where_: &str,
) -> Result<BTreeMap<&'value str, &'value JsonValue<'source>>, PerformanceGateValidationError> {
    let Some(members) = value.object_members() else {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} must be an object"
        )));
    };
    let mut object = BTreeMap::new();
    for member in members {
        if object.insert(member.key(), member.value()).is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{where_}.{} is duplicated",
                member.key()
            )));
        }
    }
    Ok(object)
}

fn field<'value, 'source>(
    object: &BTreeMap<&str, &'value JsonValue<'source>>,
    field: &str,
    where_: &str,
) -> Result<&'value JsonValue<'source>, PerformanceGateValidationError> {
    object
        .get(field)
        .copied()
        .ok_or_else(|| PerformanceGateValidationError::new(format!("{where_}.{field} is required")))
}

fn array<'value, 'source>(
    value: &'value JsonValue<'source>,
    where_: &str,
) -> Result<&'value [JsonValue<'source>], PerformanceGateValidationError> {
    value
        .array_elements()
        .ok_or_else(|| PerformanceGateValidationError::new(format!("{where_} must be an array")))
}

fn text<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<&'value str, PerformanceGateValidationError> {
    value
        .string_value()
        .ok_or_else(|| PerformanceGateValidationError::new(format!("{where_} must be a string")))
}

fn require_exact_text(
    object: &BTreeMap<&str, &JsonValue<'_>>,
    field_name: &str,
    expected: &str,
    where_: &str,
) -> Result<(), PerformanceGateValidationError> {
    if text(field(object, field_name, where_)?, where_)? != expected {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} is unsupported"
        )));
    }
    Ok(())
}

fn natural(value: &JsonValue<'_>, where_: &str) -> Result<u64, PerformanceGateValidationError> {
    let Some(raw) = value.number_raw() else {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} must be a u64"
        )));
    };
    if raw.is_empty()
        || !raw.bytes().all(|byte| byte.is_ascii_digit())
        || (raw.len() > 1 && raw.starts_with('0'))
    {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} must be a canonical u64"
        )));
    }
    raw.parse()
        .map_err(|_| PerformanceGateValidationError::new(format!("{where_} exceeds the u64 limit")))
}

fn boolean(value: &JsonValue<'_>, where_: &str) -> Result<bool, PerformanceGateValidationError> {
    value
        .bool_value()
        .ok_or_else(|| PerformanceGateValidationError::new(format!("{where_} must be a boolean")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        PerformanceMeasurementMode, PerformanceMeasurementRecorder, PerformanceModuleMeasurement,
    };

    const FIXTURE: &str = r#"{"schema":"npa.performance.fixtures.v0.1","scenarios":[{"id":"compact","kind":"warmed-checked-artifact-verifier","package_root":"testdata/package/npa-std","verifier":"fast","cache_policy":"disabled","warmup":1,"samples":3,"notes":"fixture"}]}"#;
    const BASELINE: &str = r#"{"schema":"npa.performance.baselines.v0.1","measurement_schema":"npa.performance.measurements.v0.2","scenarios":[{"id":"compact","status":"passed","module_count":1,"deterministic_counters":{"package.live_results":1,"package.modules_checked":1},"coverage":{"live_results_min":1,"proof_evidence_reduction_allowed":false}}],"update_policy":"manual"}"#;

    #[test]
    fn fixture_selection_is_bound_to_explicit_arguments() {
        validate_performance_fixture_selection(
            FIXTURE,
            PerformanceFixtureSelection {
                scenario: "compact",
                kind: "warmed-checked-artifact-verifier",
                package_root: "testdata/package/npa-std",
                verifier: "fast",
                cache_policy: "disabled",
                warmup: 1,
                samples: 3,
            },
        )
        .unwrap();
    }

    #[test]
    fn baseline_checks_every_declared_counter_and_live_coverage() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        recorder.add_counter(PerformanceMeasurementLabel::PackageLiveResults, 1);
        recorder.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 1);
        recorder.record_module(PerformanceModuleMeasurement {
            module: "Fixture".to_owned(),
            certificate_bytes: 1,
            declaration_count: 1,
            import_count: 0,
            checker_elapsed_ns: 0,
            package_sharding: None,
        });
        let report = recorder.report().unwrap();
        validate_performance_measurement_baseline(BASELINE, "compact", &report).unwrap();

        let mismatched =
            BASELINE.replace("package.modules_checked\":1", "package.modules_checked\":2");
        assert!(
            validate_performance_measurement_baseline(&mismatched, "compact", &report).is_err()
        );
    }
}
