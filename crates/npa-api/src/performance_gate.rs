//! Strict local performance-fixture and deterministic-baseline validation.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::json::{JsonDocument, JsonValue};
use crate::{
    PerformanceMeasurementLabel, PerformanceMeasurementMode, PerformanceMeasurementRecorder,
    PerformanceMeasurementReport, PerformancePackageSelectionObservation,
    PERFORMANCE_MEASUREMENTS_SCHEMA,
};

/// Schema for the checked-in performance fixture manifest.
pub const PERFORMANCE_FIXTURES_SCHEMA: &str = "npa.performance.fixtures.v0.1";
/// Schema for deterministic performance baselines.
pub const PERFORMANCE_BASELINES_SCHEMA: &str = "npa.performance.baselines.v0.1";
const PERFORMANCE_BASELINES_UPDATE_POLICY: &str =
    "Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request. Raw elapsed time and peak RSS are advisory evidence and must never be copied into this generic deterministic baseline.";
/// Dedicated deterministic baseline schema for package-verifier process-memo scope.
pub const PACKAGE_VERIFIER_PROCESS_MEMO_SCOPE_BASELINES_SCHEMA: &str =
    "npa.package_verifier.process_memo_scope.baselines.v0.1";
const PACKAGE_VERIFIER_PROCESS_MEMO_SCOPE_UPDATE_POLICY: &str =
    "Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request.";

/// Store projection consumed by the package-verifier process-memo benchmark.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackageVerifierProcessMemoScopeStoreObservation {
    pub retained_entries: u64,
    pub retained_weighted_certificate_bytes: u64,
    pub cumulative_hits: u64,
    pub cumulative_misses: u64,
    pub cumulative_inserted: u64,
    pub cumulative_evicted: u64,
    pub cumulative_rejected_oversize: u64,
}

/// Closed deterministic observation for one process-memo benchmark profile.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackageVerifierProcessMemoScopeBaselineObservation<'a> {
    pub status: &'a str,
    pub selection_kind: &'a str,
    pub selected_module: Option<&'a str>,
    pub closure_module_count: u64,
    pub closure_certificate_bytes: u64,
    pub jobs: u64,
    pub measurement_mode: &'a str,
    pub memo_mode: &'a str,
    pub max_entries: Option<u64>,
    pub max_weighted_certificate_bytes: Option<u64>,
    pub hits: u64,
    pub misses: u64,
    pub inserted: u64,
    pub keys_built: u64,
    pub certificate_bytes_hashed: u64,
    pub evicted: u64,
    pub rejected_oversize: u64,
    pub bypassed_store_unavailable: u64,
    pub post_warmup_store: Option<PackageVerifierProcessMemoScopeStoreObservation>,
}

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
        let open = open_object(scenario, &path)?;
        let kind = text(field(&open, "kind", &path)?, &format!("{path}.kind"))?;
        let object = if kind == "targeted-build-certs" {
            let has_population_contract = open.contains_key("population_modules")
                || open.contains_key("removed_support_modules");
            let targeted_fields = if has_population_contract {
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
                ][..]
            } else {
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
                    "notes",
                ][..]
            };
            closed_object(scenario, &path, targeted_fields)?
        } else {
            closed_object(
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
            )?
        };
        let id = text(field(&object, "id", &path)?, &format!("{path}.id"))?;
        if id.is_empty() || ids.insert(id, index).is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.id must be nonempty and unique"
            )));
        }
        let package_root = text(
            field(&object, "package_root", &path)?,
            &format!("{path}.package_root"),
        )?;
        validate_relative_path(package_root, &format!("{path}.package_root"))?;
        let verifier = text(
            field(&object, "verifier", &path)?,
            &format!("{path}.verifier"),
        )?;
        let supported_verifier = if kind == "targeted-build-certs" {
            verifier == "build-certs-check"
        } else {
            matches!(verifier, "fast" | "reference")
        };
        if !supported_verifier {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.verifier is unsupported"
            )));
        }
        let cache_policy = text(
            field(&object, "cache_policy", &path)?,
            &format!("{path}.cache_policy"),
        )?;
        let supported_cache_policy = if kind == "targeted-build-certs" {
            matches!(
                cache_policy,
                "off"
                    | "read-through-cold"
                    | "read-through-warm"
                    | "local-hit-cold"
                    | "local-hit-warm"
                    | "local-hit-partially-warm"
                    | "local-hit-fully-warm"
            )
        } else {
            cache_policy == "disabled"
        };
        if !supported_cache_policy {
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
        if kind == "targeted-build-certs" {
            let support_count = natural(
                field(&object, "support_module_count", &path)?,
                &format!("{path}.support_module_count"),
            )?;
            let target_count = natural(
                field(&object, "target_module_count", &path)?,
                &format!("{path}.target_module_count"),
            )?;
            if support_count == 0 || target_count != 1 {
                return Err(PerformanceGateValidationError::new(format!(
                    "{path} targeted-build fixture must have positive support and exactly one target"
                )));
            }
            require_exact_text(
                &object,
                "target_edit",
                "append-comment-without-support-identity-change",
                &format!("{path}.target_edit"),
            )?;
            if let Some(population) = object.get("population_modules") {
                validate_module_array(population, &format!("{path}.population_modules"))?;
                validate_module_array(
                    field(&object, "removed_support_modules", &path)?,
                    &format!("{path}.removed_support_modules"),
                )?;
            }
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
    let root = open_object(document.root(), "$")?;
    let allowed_root_fields = [
        "schema",
        "measurement_schema",
        "scenarios",
        "targeted_build_certs",
        "targeted_build_certs_rollout",
        "update_policy",
    ];
    if !matches!(root.len(), 4..=6)
        || root
            .keys()
            .any(|field| !allowed_root_fields.contains(field))
    {
        return Err(PerformanceGateValidationError::new(
            "$ has missing or unknown fields",
        ));
    }
    let expected_root_fields: &[&str] = match (
        root.contains_key("targeted_build_certs"),
        root.contains_key("targeted_build_certs_rollout"),
    ) {
        (false, false) => &["schema", "measurement_schema", "scenarios", "update_policy"],
        (true, false) => &[
            "schema",
            "measurement_schema",
            "scenarios",
            "targeted_build_certs",
            "update_policy",
        ],
        (false, true) => &[
            "schema",
            "measurement_schema",
            "scenarios",
            "targeted_build_certs_rollout",
            "update_policy",
        ],
        (true, true) => &[
            "schema",
            "measurement_schema",
            "scenarios",
            "targeted_build_certs",
            "targeted_build_certs_rollout",
            "update_policy",
        ],
    };
    closed_ordered_object(document.root(), "$", expected_root_fields)?;
    require_exact_text(&root, "schema", PERFORMANCE_BASELINES_SCHEMA, "$.schema")?;
    require_exact_text(
        &root,
        "measurement_schema",
        PERFORMANCE_MEASUREMENTS_SCHEMA,
        "$.measurement_schema",
    )?;
    require_exact_text(
        &root,
        "update_policy",
        PERFORMANCE_BASELINES_UPDATE_POLICY,
        "$.update_policy",
    )?;
    if let Some(targeted) = root.get("targeted_build_certs") {
        validate_targeted_build_certs_baselines(
            targeted,
            "targeted_build_certs",
            TARGETED_BUILD_CERTS_COUNTERS,
        )?;
    }
    if let Some(targeted) = root.get("targeted_build_certs_rollout") {
        validate_targeted_build_certs_baselines(
            targeted,
            "targeted_build_certs_rollout",
            TARGETED_BUILD_CERTS_ROLLOUT_COUNTERS,
        )?;
    }

    let scenarios = array(field(&root, "scenarios", "$")?, "$.scenarios")?;
    let mut selected = 0usize;
    let mut selected_counter_labels = None;
    let mut ids = BTreeMap::new();
    for (index, scenario) in scenarios.iter().enumerate() {
        let path = format!("$.scenarios[{index}]");
        let object = closed_ordered_object(
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
        let mut declared_labels = BTreeSet::new();
        for member in counter_members {
            let label = member.key();
            if previous.is_some_and(|previous| previous >= label) {
                return Err(PerformanceGateValidationError::new(format!(
                    "{counters_path} labels are not in canonical order"
                )));
            }
            previous = Some(label);
            let Some(label_value) = PerformanceMeasurementLabel::from_schema_identifier(
                PERFORMANCE_MEASUREMENTS_SCHEMA,
                label,
            ) else {
                return Err(PerformanceGateValidationError::new(format!(
                    "{counters_path}.{label} is not a stable measurement label"
                )));
            };
            declared_labels.insert(label_value);
            let expected = natural(member.value(), &format!("{counters_path}.{label}"))?;
            if id == scenario_id && counter_value(report, label_value) != Some(expected) {
                return Err(PerformanceGateValidationError::new(format!(
                    "deterministic baseline mismatch for {label}"
                )));
            }
        }
        let coverage_path = format!("{path}.coverage");
        let coverage = closed_ordered_object(
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
            selected_counter_labels = Some(declared_labels);
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
    let expected = selected_counter_labels.ok_or_else(|| {
        PerformanceGateValidationError::new("selected baseline counter catalog is unavailable")
    })?;
    let actual = report
        .counters
        .iter()
        .map(|counter| counter.label)
        .collect::<BTreeSet<_>>();
    let mut expected_with_coverage = expected.clone();
    expected_with_coverage.extend([
        PerformanceMeasurementLabel::PackageLiveResults,
        PerformanceMeasurementLabel::PackageCacheResults,
        PerformanceMeasurementLabel::PackageMemoResults,
    ]);
    if actual != expected && actual != expected_with_coverage {
        return Err(PerformanceGateValidationError::new(
            "performance report counter set differs from the selected baseline profile",
        ));
    }
    Ok(())
}

/// Validate one changed-selection observation against its checked common
/// deterministic baseline row. Host elapsed values are intentionally absent
/// from both the observation and this gate.
pub fn validate_package_changed_selection_baseline(
    source: &str,
    scenario_id: &str,
    observation: PerformancePackageSelectionObservation,
) -> Result<(), PerformanceGateValidationError> {
    let mut recorder = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary);
    recorder.observe_package_selection(&observation);
    let report = recorder.report().ok_or_else(|| {
        PerformanceGateValidationError::new(
            "changed-selection baseline validation requires measurement state",
        )
    })?;
    validate_performance_measurement_baseline(source, scenario_id, &report)
}

/// Strictly validate one dedicated package-verifier process-memo baseline row.
#[doc(hidden)]
pub fn validate_package_verifier_process_memo_scope_baseline(
    source: &str,
    scenario_id: &str,
    observation: PackageVerifierProcessMemoScopeBaselineObservation<'_>,
) -> Result<(), PerformanceGateValidationError> {
    let document = JsonDocument::parse(source).map_err(|error| {
        PerformanceGateValidationError::new(format!(
            "process-memo scope baseline is invalid JSON at byte {}",
            error.offset
        ))
    })?;
    let root = closed_ordered_object(
        document.root(),
        "$",
        &["schema", "scenarios", "update_policy"],
    )?;
    require_exact_text(
        &root,
        "schema",
        PACKAGE_VERIFIER_PROCESS_MEMO_SCOPE_BASELINES_SCHEMA,
        "$.schema",
    )?;
    require_exact_text(
        &root,
        "update_policy",
        PACKAGE_VERIFIER_PROCESS_MEMO_SCOPE_UPDATE_POLICY,
        "$.update_policy",
    )?;
    let scenarios = array(field(&root, "scenarios", "$")?, "$.scenarios")?;
    let mut ids = BTreeMap::new();
    let mut selected = 0usize;
    for (index, scenario) in scenarios.iter().enumerate() {
        let path = format!("$.scenarios[{index}]");
        let row = closed_ordered_object(
            scenario,
            &path,
            &[
                "id",
                "status",
                "selection",
                "jobs",
                "measurement_mode",
                "memo",
                "measured_run_memo_counters",
                "post_warmup_store",
            ],
        )?;
        let id = text(field(&row, "id", &path)?, &format!("{path}.id"))?;
        if id.is_empty() || ids.insert(id, index).is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.id must be nonempty and unique"
            )));
        }
        require_exact_text(&row, "status", "passed", &format!("{path}.status"))?;

        let selection_path = format!("{path}.selection");
        let selection = closed_ordered_object(
            field(&row, "selection", &path)?,
            &selection_path,
            &[
                "kind",
                "module",
                "closure_module_count",
                "closure_certificate_bytes",
            ],
        )?;
        let selection_kind = text(
            field(&selection, "kind", &selection_path)?,
            &format!("{selection_path}.kind"),
        )?;
        if !matches!(selection_kind, "empty" | "leaf" | "full") {
            return Err(PerformanceGateValidationError::new(format!(
                "{selection_path}.kind is unsupported"
            )));
        }
        let selected_module = optional_text(
            field(&selection, "module", &selection_path)?,
            &format!("{selection_path}.module"),
        )?;
        if (selection_kind == "leaf") != selected_module.is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{selection_path}.module is inconsistent with selection kind"
            )));
        }
        if selected_module.is_some_and(|module| !npa_cert::Name::from_dotted(module).is_canonical())
        {
            return Err(PerformanceGateValidationError::new(format!(
                "{selection_path}.module must be a canonical dotted module name"
            )));
        }
        let closure_module_count = natural(
            field(&selection, "closure_module_count", &selection_path)?,
            &format!("{selection_path}.closure_module_count"),
        )?;
        let closure_certificate_bytes = natural(
            field(&selection, "closure_certificate_bytes", &selection_path)?,
            &format!("{selection_path}.closure_certificate_bytes"),
        )?;
        let jobs = natural(field(&row, "jobs", &path)?, &format!("{path}.jobs"))?;
        if jobs == 0 {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.jobs must be positive"
            )));
        }
        let measurement_mode = text(
            field(&row, "measurement_mode", &path)?,
            &format!("{path}.measurement_mode"),
        )?;
        if !matches!(measurement_mode, "off" | "summary") {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.measurement_mode is unsupported"
            )));
        }

        let memo_path = format!("{path}.memo");
        let memo = closed_ordered_object(
            field(&row, "memo", &path)?,
            &memo_path,
            &["mode", "max_entries", "max_weighted_certificate_bytes"],
        )?;
        let memo_mode = text(
            field(&memo, "mode", &memo_path)?,
            &format!("{memo_path}.mode"),
        )?;
        if !matches!(memo_mode, "disabled" | "warm") {
            return Err(PerformanceGateValidationError::new(format!(
                "{memo_path}.mode is unsupported"
            )));
        }
        let max_entries = optional_natural(
            field(&memo, "max_entries", &memo_path)?,
            &format!("{memo_path}.max_entries"),
        )?;
        let max_weighted_certificate_bytes = optional_natural(
            field(&memo, "max_weighted_certificate_bytes", &memo_path)?,
            &format!("{memo_path}.max_weighted_certificate_bytes"),
        )?;
        if memo_mode == "warm" {
            if max_entries == Some(0)
                || max_entries.is_none()
                || max_weighted_certificate_bytes == Some(0)
                || max_weighted_certificate_bytes.is_none()
            {
                return Err(PerformanceGateValidationError::new(format!(
                    "{memo_path} warm limits must be nonzero"
                )));
            }
        } else if max_entries.is_some() || max_weighted_certificate_bytes.is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{memo_path} disabled limits must be null"
            )));
        }

        let counters_path = format!("{path}.measured_run_memo_counters");
        let counters = closed_ordered_object(
            field(&row, "measured_run_memo_counters", &path)?,
            &counters_path,
            &[
                "hits",
                "misses",
                "inserted",
                "keys_built",
                "certificate_bytes_hashed",
                "evicted",
                "rejected_oversize",
                "bypassed_store_unavailable",
            ],
        )?;
        let counter_values = [
            ("hits", observation.hits),
            ("misses", observation.misses),
            ("inserted", observation.inserted),
            ("keys_built", observation.keys_built),
            (
                "certificate_bytes_hashed",
                observation.certificate_bytes_hashed,
            ),
            ("evicted", observation.evicted),
            ("rejected_oversize", observation.rejected_oversize),
            (
                "bypassed_store_unavailable",
                observation.bypassed_store_unavailable,
            ),
        ];
        let parsed_counters = counter_values
            .iter()
            .map(|(name, _)| {
                natural(
                    field(&counters, name, &counters_path)?,
                    &format!("{counters_path}.{name}"),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let parsed_store = parse_process_memo_store(
            field(&row, "post_warmup_store", &path)?,
            &format!("{path}.post_warmup_store"),
        )?;
        if (memo_mode == "warm") != parsed_store.is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.post_warmup_store is inconsistent with memo mode"
            )));
        }

        if id == scenario_id {
            selected = selected.saturating_add(1);
            let expected_counters = counter_values
                .iter()
                .map(|(_, value)| *value)
                .collect::<Vec<_>>();
            if observation.status != "passed"
                || selection_kind != observation.selection_kind
                || selected_module != observation.selected_module
                || closure_module_count != observation.closure_module_count
                || closure_certificate_bytes != observation.closure_certificate_bytes
                || jobs != observation.jobs
                || measurement_mode != observation.measurement_mode
                || memo_mode != observation.memo_mode
                || max_entries != observation.max_entries
                || max_weighted_certificate_bytes != observation.max_weighted_certificate_bytes
                || parsed_counters != expected_counters
                || parsed_store != observation.post_warmup_store
            {
                return Err(PerformanceGateValidationError::new(format!(
                    "process-memo scope baseline mismatch for {scenario_id}"
                )));
            }
        }
    }
    if selected != 1 {
        return Err(PerformanceGateValidationError::new(format!(
            "process-memo scope baseline scenario '{scenario_id}' was not selected exactly once"
        )));
    }
    Ok(())
}

fn parse_process_memo_store(
    value: &JsonValue<'_>,
    where_: &str,
) -> Result<Option<PackageVerifierProcessMemoScopeStoreObservation>, PerformanceGateValidationError>
{
    if value.kind() == crate::json::JsonValueKind::Null {
        return Ok(None);
    }
    let store = closed_ordered_object(
        value,
        where_,
        &[
            "retained_entries",
            "retained_weighted_certificate_bytes",
            "cumulative_hits",
            "cumulative_misses",
            "cumulative_inserted",
            "cumulative_evicted",
            "cumulative_rejected_oversize",
        ],
    )?;
    Ok(Some(PackageVerifierProcessMemoScopeStoreObservation {
        retained_entries: natural(
            field(&store, "retained_entries", where_)?,
            &format!("{where_}.retained_entries"),
        )?,
        retained_weighted_certificate_bytes: natural(
            field(&store, "retained_weighted_certificate_bytes", where_)?,
            &format!("{where_}.retained_weighted_certificate_bytes"),
        )?,
        cumulative_hits: natural(
            field(&store, "cumulative_hits", where_)?,
            &format!("{where_}.cumulative_hits"),
        )?,
        cumulative_misses: natural(
            field(&store, "cumulative_misses", where_)?,
            &format!("{where_}.cumulative_misses"),
        )?,
        cumulative_inserted: natural(
            field(&store, "cumulative_inserted", where_)?,
            &format!("{where_}.cumulative_inserted"),
        )?,
        cumulative_evicted: natural(
            field(&store, "cumulative_evicted", where_)?,
            &format!("{where_}.cumulative_evicted"),
        )?,
        cumulative_rejected_oversize: natural(
            field(&store, "cumulative_rejected_oversize", where_)?,
            &format!("{where_}.cumulative_rejected_oversize"),
        )?,
    }))
}

const TARGETED_BUILD_CERTS_COUNTERS: &[&str] = &[
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

const TARGETED_BUILD_CERTS_ROLLOUT_COUNTERS: &[&str] = &[
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

fn validate_targeted_build_certs_baselines(
    value: &JsonValue<'_>,
    field_name: &str,
    expected_counters: &[&str],
) -> Result<(), PerformanceGateValidationError> {
    let array_path = format!("$.{field_name}");
    let scenarios = array(value, &array_path)?;
    let mut ids = BTreeMap::new();
    for (index, scenario) in scenarios.iter().enumerate() {
        let path = format!("{array_path}[{index}]");
        let object = closed_object(
            scenario,
            &path,
            &[
                "id",
                "status",
                "support_module_count",
                "target_module_count",
                "deterministic_counters",
            ],
        )?;
        let id = text(field(&object, "id", &path)?, &format!("{path}.id"))?;
        if id.is_empty() || ids.insert(id, index).is_some() {
            return Err(PerformanceGateValidationError::new(format!(
                "{path}.id must be nonempty and unique"
            )));
        }
        require_exact_text(&object, "status", "passed", &format!("{path}.status"))?;
        let support_count = natural(
            field(&object, "support_module_count", &path)?,
            &format!("{path}.support_module_count"),
        )?;
        let target_count = natural(
            field(&object, "target_module_count", &path)?,
            &format!("{path}.target_module_count"),
        )?;
        if support_count == 0 || target_count != 1 {
            return Err(PerformanceGateValidationError::new(format!(
                "{path} must declare positive support and exactly one target"
            )));
        }
        let counters_path = format!("{path}.deterministic_counters");
        let counters = closed_object(
            field(&object, "deterministic_counters", &path)?,
            &counters_path,
            expected_counters,
        )?;
        for counter in expected_counters {
            natural(
                field(&counters, counter, &counters_path)?,
                &format!("{counters_path}.{counter}"),
            )?;
        }
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

fn validate_module_array(
    value: &JsonValue<'_>,
    where_: &str,
) -> Result<(), PerformanceGateValidationError> {
    let modules = array(value, where_)?;
    let mut observed = BTreeMap::new();
    for (index, module) in modules.iter().enumerate() {
        let path = format!("{where_}[{index}]");
        let module = text(module, &path)?;
        if !npa_cert::Name::from_dotted(module).is_canonical()
            || observed.insert(module, index).is_some()
        {
            return Err(PerformanceGateValidationError::new(format!(
                "{path} must be a unique dotted module name"
            )));
        }
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

fn closed_ordered_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    where_: &str,
    fields: &[&str],
) -> Result<BTreeMap<&'value str, &'value JsonValue<'source>>, PerformanceGateValidationError> {
    let members = value.object_members().ok_or_else(|| {
        PerformanceGateValidationError::new(format!("{where_} must be an object"))
    })?;
    if members.len() != fields.len()
        || members
            .iter()
            .zip(fields)
            .any(|(member, expected)| member.key() != *expected)
    {
        return Err(PerformanceGateValidationError::new(format!(
            "{where_} has noncanonical, missing, or unknown fields"
        )));
    }
    open_object(value, where_)
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

fn optional_text<'value>(
    value: &'value JsonValue<'_>,
    where_: &str,
) -> Result<Option<&'value str>, PerformanceGateValidationError> {
    if value.kind() == crate::json::JsonValueKind::Null {
        Ok(None)
    } else {
        text(value, where_).map(Some)
    }
}

fn optional_natural(
    value: &JsonValue<'_>,
    where_: &str,
) -> Result<Option<u64>, PerformanceGateValidationError> {
    if value.kind() == crate::json::JsonValueKind::Null {
        Ok(None)
    } else {
        natural(value, where_).map(Some)
    }
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
    const BASELINE: &str = r#"{"schema":"npa.performance.baselines.v0.1","measurement_schema":"npa.performance.measurements.v0.9","scenarios":[{"id":"compact","status":"passed","module_count":1,"deterministic_counters":{"package.live_results":1,"package.modules_checked":1},"coverage":{"live_results_min":1,"proof_evidence_reduction_allowed":false}}],"targeted_build_certs":[],"update_policy":"Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request. Raw elapsed time and peak RSS are advisory evidence and must never be copied into this generic deterministic baseline."}"#;

    const TARGETED_FIXTURE: &str = r#"{"schema":"npa.performance.fixtures.v0.1","scenarios":[{"id":"targeted-small-off","kind":"targeted-build-certs","package_root":"generated/targeted-build-certs-small","verifier":"build-certs-check","cache_policy":"off","warmup":1,"samples":5,"support_module_count":2,"target_module_count":1,"target_edit":"append-comment-without-support-identity-change","notes":"fixture"}]}"#;
    const PROCESS_MEMO_BASELINE: &str = r#"{"schema":"npa.package_verifier.process_memo_scope.baselines.v0.1","scenarios":[{"id":"package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off","status":"passed","selection":{"kind":"empty","module":null,"closure_module_count":0,"closure_certificate_bytes":0},"jobs":1,"measurement_mode":"off","memo":{"mode":"disabled","max_entries":null,"max_weighted_certificate_bytes":null},"measured_run_memo_counters":{"hits":0,"misses":0,"inserted":0,"keys_built":0,"certificate_bytes_hashed":0,"evicted":0,"rejected_oversize":0,"bypassed_store_unavailable":0},"post_warmup_store":null}],"update_policy":"Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request."}"#;

    #[test]
    fn linear_dag_iut_common_baselines_are_strict() {
        let baseline =
            include_str!("../../../testdata/performance/baselines/measurements.v0.1.json");
        assert!(!baseline.contains("package.verifier.linear_dag_planning.v1.iut992.empty.j4.off"));
        for mode in [
            PerformanceMeasurementMode::Summary,
            PerformanceMeasurementMode::Detailed,
        ] {
            let mut recorder = PerformanceMeasurementRecorder::new(mode);
            for label in [
                PerformanceMeasurementLabel::PackageCacheResults,
                PerformanceMeasurementLabel::PackageCertificateBytes,
                PerformanceMeasurementLabel::PackageEffectiveJobs,
                PerformanceMeasurementLabel::PackageLiveResults,
                PerformanceMeasurementLabel::PackageMemoResults,
                PerformanceMeasurementLabel::PackageModulesChecked,
            ] {
                recorder.add_counter(label, 0);
            }
            recorder.add_counter(PerformanceMeasurementLabel::PackageRequestedJobs, 4);
            let report = recorder.report().unwrap();
            let id = format!(
                "package.verifier.linear_dag_planning.v1.iut992.empty.j4.{}",
                mode.as_str()
            );
            validate_performance_measurement_baseline(baseline, &id, &report).unwrap();
            let drift = baseline.replace(
                "\"package.requested_jobs\": 4",
                "\"package.requested_jobs\": 3",
            );
            assert!(validate_performance_measurement_baseline(&drift, &id, &report).is_err());
        }
    }

    #[test]
    fn linear_dag_iut_fixture_catalog_is_strict() {
        const SOURCE: &str =
            include_str!("../../../testdata/performance/fixtures/manifest.v0.1.json");
        let expected = ["off", "summary", "detailed"]
            .map(|mode| format!("package.verifier.linear_dag_planning.v1.iut992.empty.j4.{mode}"))
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        let document = JsonDocument::parse(SOURCE).unwrap();
        let root = open_object(document.root(), "$").unwrap();
        let scenarios = array(field(&root, "scenarios", "$").unwrap(), "$.scenarios").unwrap();
        let actual = scenarios
            .iter()
            .filter_map(|scenario| {
                let object = open_object(scenario, "$.scenarios[]").unwrap();
                let id = text(
                    field(&object, "id", "$.scenarios[]").unwrap(),
                    "$.scenarios[].id",
                )
                .unwrap();
                id.starts_with("package.verifier.linear_dag_planning.v1.iut992.empty.j4.")
                    .then_some(id.to_owned())
            })
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(actual, expected);

        for id in &expected {
            validate_performance_fixture_selection(
                SOURCE,
                PerformanceFixtureSelection {
                    scenario: id,
                    kind: "warmed-checked-artifact-verifier",
                    package_root: "external/npa-project-iut/proofs",
                    verifier: "fast",
                    cache_policy: "disabled",
                    warmup: 1,
                    samples: 7,
                },
            )
            .unwrap();
        }
        let wrong_token = SOURCE.replace(
            "\"package_root\": \"external/npa-project-iut/proofs\"",
            "\"package_root\": \"external/wrong/proofs\"",
        );
        assert!(validate_performance_fixture_selection(
            &wrong_token,
            PerformanceFixtureSelection {
                scenario: "package.verifier.linear_dag_planning.v1.iut992.empty.j4.off",
                kind: "warmed-checked-artifact-verifier",
                package_root: "external/npa-project-iut/proofs",
                verifier: "fast",
                cache_policy: "disabled",
                warmup: 1,
                samples: 7,
            },
        )
        .is_err());
    }

    #[test]
    fn performance_process_memo_scope_baseline_shape_is_closed() {
        let observation = PackageVerifierProcessMemoScopeBaselineObservation {
            status: "passed",
            selection_kind: "empty",
            selected_module: None,
            closure_module_count: 0,
            closure_certificate_bytes: 0,
            jobs: 1,
            measurement_mode: "off",
            memo_mode: "disabled",
            max_entries: None,
            max_weighted_certificate_bytes: None,
            hits: 0,
            misses: 0,
            inserted: 0,
            keys_built: 0,
            certificate_bytes_hashed: 0,
            evicted: 0,
            rejected_oversize: 0,
            bypassed_store_unavailable: 0,
            post_warmup_store: None,
        };
        validate_package_verifier_process_memo_scope_baseline(
            PROCESS_MEMO_BASELINE,
            "package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off",
            observation,
        )
        .unwrap();
        assert!(validate_package_verifier_process_memo_scope_baseline(
            &PROCESS_MEMO_BASELINE.replace("\"hits\":0", "\"hits\":1"),
            "package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off",
            observation,
        )
        .is_err());
        assert!(validate_package_verifier_process_memo_scope_baseline(
            &PROCESS_MEMO_BASELINE.replace(
                "\"status\":\"passed\"",
                "\"unknown\":0,\"status\":\"passed\""
            ),
            "package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off",
            observation,
        )
        .is_err());
        assert!(validate_package_verifier_process_memo_scope_baseline(
            &PROCESS_MEMO_BASELINE
                .replace(PACKAGE_VERIFIER_PROCESS_MEMO_SCOPE_UPDATE_POLICY, "manual"),
            "package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off",
            observation,
        )
        .is_err());
    }

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

        validate_performance_fixture_selection(
            TARGETED_FIXTURE,
            PerformanceFixtureSelection {
                scenario: "targeted-small-off",
                kind: "targeted-build-certs",
                package_root: "generated/targeted-build-certs-small",
                verifier: "build-certs-check",
                cache_policy: "off",
                warmup: 1,
                samples: 5,
            },
        )
        .unwrap();

        for cache_policy in [
            "local-hit-cold",
            "local-hit-warm",
            "local-hit-partially-warm",
            "local-hit-fully-warm",
        ] {
            let fixture = TARGETED_FIXTURE.replace(
                "\"cache_policy\":\"off\"",
                &format!("\"cache_policy\":\"{cache_policy}\""),
            );
            validate_performance_fixture_selection(
                &fixture,
                PerformanceFixtureSelection {
                    scenario: "targeted-small-off",
                    kind: "targeted-build-certs",
                    package_root: "generated/targeted-build-certs-small",
                    verifier: "build-certs-check",
                    cache_policy,
                    warmup: 1,
                    samples: 5,
                },
            )
            .unwrap();
        }

        let population_fixture = TARGETED_FIXTURE.replace(
            "\"notes\":\"fixture\"",
            "\"population_modules\":[\"Fixture.Target'\"],\"removed_support_modules\":[],\"notes\":\"fixture\"",
        );
        validate_performance_fixture_selection(
            &population_fixture,
            PerformanceFixtureSelection {
                scenario: "targeted-small-off",
                kind: "targeted-build-certs",
                package_root: "generated/targeted-build-certs-small",
                verifier: "build-certs-check",
                cache_policy: "off",
                warmup: 1,
                samples: 5,
            },
        )
        .unwrap();
        let noncanonical_population =
            population_fixture.replace("Fixture.Target'", "Fixture.2Target");
        assert!(validate_performance_fixture_selection(
            &noncanonical_population,
            PerformanceFixtureSelection {
                scenario: "targeted-small-off",
                kind: "targeted-build-certs",
                package_root: "generated/targeted-build-certs-small",
                verifier: "build-certs-check",
                cache_policy: "off",
                warmup: 1,
                samples: 5,
            },
        )
        .is_err());
    }

    #[test]
    fn performance_changed_selection_fixture_catalog_is_strict() {
        const SOURCE: &str =
            include_str!("../../../testdata/performance/fixtures/manifest.v0.1.json");
        let rows = [
            ("empty0.clean", "generated/empty-package"),
            ("tiny1.clean", "generated/short-package"),
            ("tiny1.tracked1", "generated/short-package"),
            ("tiny1.untracked1", "generated/short-package"),
            ("former127.clean", "generated/short-package"),
            ("former128.clean", "generated/short-package"),
            ("former129.clean", "generated/short-package"),
            ("count1023.clean", "generated/count-package"),
            ("count1024.clean", "generated/count-package"),
            ("count1025.clean", "generated/count-package"),
            ("byte65535.clean", "generated/byte-boundary-package"),
            ("byte65536.clean", "generated/byte-boundary-package"),
            ("byte65537.clean", "generated/byte-boundary-package"),
            ("long32.mixed", "generated/long-path-package"),
            ("long128.mixed", "generated/long-path-package"),
            ("long1024.mixed", "generated/long-path-package"),
            ("fallback1.clean", "generated/fallback-package"),
            ("fallback129.clean", "generated/fallback-package"),
            ("fallback1024.clean", "generated/fallback-package"),
            (
                "inflated129.clean",
                "generated/inflated-environment-package",
            ),
            (
                "inflated992.clean",
                "generated/inflated-environment-package",
            ),
            ("iut1401.clean", "npa-project-iut/proofs"),
            ("iut1401.tracked1", "npa-project-iut/proofs"),
            ("iut1401.untracked1", "npa-project-iut/proofs"),
            ("large4096.mixed", "generated/large-package"),
        ];
        let expected_ids = rows
            .iter()
            .map(|(suffix, _)| format!("package.changed_selection.git_batching.v1.{suffix}"))
            .collect::<std::collections::BTreeSet<_>>();
        let document = JsonDocument::parse(SOURCE).unwrap();
        let root = open_object(document.root(), "$").unwrap();
        let scenarios = array(field(&root, "scenarios", "$").unwrap(), "$.scenarios").unwrap();
        let actual_ids = scenarios
            .iter()
            .filter_map(|scenario| {
                let object = open_object(scenario, "$.scenarios[]").unwrap();
                (text(
                    field(&object, "kind", "$.scenarios[]").unwrap(),
                    "$.scenarios[].kind",
                )
                .unwrap()
                    == "package-changed-selection-git-batching")
                    .then(|| {
                        text(
                            field(&object, "id", "$.scenarios[]").unwrap(),
                            "$.scenarios[].id",
                        )
                        .unwrap()
                        .to_owned()
                    })
            })
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(actual_ids, expected_ids);

        for (suffix, package_root) in rows {
            let scenario = format!("package.changed_selection.git_batching.v1.{suffix}");
            validate_performance_fixture_selection(
                SOURCE,
                PerformanceFixtureSelection {
                    scenario: &scenario,
                    kind: "package-changed-selection-git-batching",
                    package_root,
                    verifier: "fast",
                    cache_policy: "disabled",
                    warmup: 1,
                    samples: 7,
                },
            )
            .unwrap_or_else(|error| panic!("{scenario}: {error}"));
        }
    }

    #[test]
    fn performance_changed_selection_checked_baseline_is_strict() {
        const SOURCE: &str =
            include_str!("../../../testdata/performance/baselines/measurements.v0.1.json");
        let suffixes = [
            "empty0.clean",
            "tiny1.clean",
            "tiny1.tracked1",
            "tiny1.untracked1",
            "former127.clean",
            "former128.clean",
            "former129.clean",
            "count1023.clean",
            "count1024.clean",
            "count1025.clean",
            "byte65535.clean",
            "byte65536.clean",
            "byte65537.clean",
            "long32.mixed",
            "long128.mixed",
            "long1024.mixed",
            "fallback1.clean",
            "fallback129.clean",
            "fallback1024.clean",
            "inflated129.clean",
            "inflated992.clean",
            "iut1401.clean",
            "iut1401.tracked1",
            "iut1401.untracked1",
            "large4096.mixed",
        ];
        let expected_ids = suffixes
            .iter()
            .map(|suffix| format!("package.changed_selection.git_batching.v1.{suffix}"))
            .collect::<std::collections::BTreeSet<_>>();

        let baseline_ids = |source: &str| -> Result<std::collections::BTreeSet<String>, String> {
            let document = JsonDocument::parse(source)
                .map_err(|error| format!("invalid JSON at byte {}", error.offset))?;
            let root = open_object(document.root(), "$").map_err(|error| error.to_string())?;
            let scenarios = array(
                field(&root, "scenarios", "$").map_err(|error| error.to_string())?,
                "$.scenarios",
            )
            .map_err(|error| error.to_string())?;
            scenarios
                .iter()
                .filter_map(|scenario| {
                    let object = open_object(scenario, "$.scenarios[]").ok()?;
                    let id = text(
                        field(&object, "id", "$.scenarios[]").ok()?,
                        "$.scenarios[].id",
                    )
                    .ok()?;
                    id.starts_with("package.changed_selection.git_batching.v1.")
                        .then_some(Ok(id.to_owned()))
                })
                .collect()
        };
        assert_eq!(baseline_ids(SOURCE).unwrap(), expected_ids);

        let tiny = PerformancePackageSelectionObservation {
            batch_policy: crate::PerformancePackageSelectionBatchPolicy::ExecBudget,
            candidate_paths: 1,
            pathspec_payload_bytes: 230,
            effective_argv_charge_bytes: 65_536,
            max_batch_payload_bytes: 230,
            max_batch_argv_charge_bytes: 246,
            pathspec_batches: 1,
            worktree_root_queries: 1,
            head_queries: 1,
            tracked_queries: 1,
            untracked_queries: 1,
            tracked_output_paths: 0,
            untracked_output_paths: 0,
            selected_paths: 0,
            overflowed: false,
            ..PerformancePackageSelectionObservation::default()
        };
        let tiny_id = "package.changed_selection.git_batching.v1.tiny1.clean";
        validate_package_changed_selection_baseline(SOURCE, tiny_id, tiny).unwrap();
        assert!(validate_package_changed_selection_baseline(
            SOURCE,
            tiny_id,
            PerformancePackageSelectionObservation {
                selected_paths: 1,
                ..tiny
            },
        )
        .is_err());

        let drifted_id = SOURCE.replacen(
            tiny_id,
            "package.changed_selection.git_batching.v1.unexpected.clean",
            1,
        );
        assert_ne!(baseline_ids(&drifted_id).unwrap(), expected_ids);
        assert!(validate_package_changed_selection_baseline(&drifted_id, tiny_id, tiny).is_err());

        let mismatched_counter = SOURCE.replacen(
            "\"package.selection_candidate_paths\": 1,",
            "\"package.selection_candidate_paths\": 2,",
            1,
        );
        assert_ne!(mismatched_counter, SOURCE);
        assert!(
            validate_package_changed_selection_baseline(&mismatched_counter, tiny_id, tiny,)
                .is_err()
        );
    }

    #[test]
    fn performance_changed_selection_optimized_baseline_is_strict() {
        performance_changed_selection_checked_baseline_is_strict();
    }

    #[test]
    fn shared_payload_common_schema_baseline_migration() {
        linear_dag_iut_common_baselines_are_strict();
        performance_process_memo_scope_baseline_shape_is_closed();
        performance_changed_selection_checked_baseline_is_strict();
    }

    #[test]
    fn snapshot_common_schema_baseline_migration() {
        const SOURCE: &str =
            include_str!("../../../testdata/performance/baselines/measurements.v0.1.json");
        let document = JsonDocument::parse(SOURCE).unwrap();
        let root = open_object(document.root(), "$").unwrap();
        assert_eq!(
            text(
                field(&root, "measurement_schema", "$").unwrap(),
                "$.measurement_schema"
            )
            .unwrap(),
            PERFORMANCE_MEASUREMENTS_SCHEMA
        );
        assert_eq!(
            text(
                field(&root, "update_policy", "$").unwrap(),
                "$.update_policy"
            )
            .unwrap(),
            "Manual review only. Record the reason for every deterministic baseline change in the reviewing commit or pull request. Raw elapsed time and peak RSS are advisory evidence and must never be copied into this generic deterministic baseline.",
        );
        let rows = array(field(&root, "scenarios", "$").unwrap(), "$.scenarios").unwrap();
        let snapshot_rows = rows
            .iter()
            .filter(|row| {
                let object = open_object(row, "$.scenarios[]").unwrap();
                text(
                    field(&object, "id", "$.scenarios[]").unwrap(),
                    "$.scenarios[].id",
                )
                .unwrap()
                .starts_with("package-artifact-snapshot-")
            })
            .collect::<Vec<_>>();
        assert_eq!(snapshot_rows.len(), 40);
        for row in snapshot_rows {
            let object = open_object(row, "$.scenarios[]").unwrap();
            let counters = open_object(
                field(&object, "deterministic_counters", "$.scenarios[]").unwrap(),
                "$.scenarios[].deterministic_counters",
            )
            .unwrap();
            assert_eq!(counters.len(), 19);
            assert!(counters.keys().all(|label| {
                PerformanceMeasurementLabel::from_schema_identifier(
                    PERFORMANCE_MEASUREMENTS_SCHEMA,
                    label,
                )
                .is_some()
            }));
        }
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

        let baseline_without_targeted = BASELINE.replace("\"targeted_build_certs\":[],", "");
        validate_performance_measurement_baseline(&baseline_without_targeted, "compact", &report)
            .unwrap();

        let mismatched =
            BASELINE.replace("package.modules_checked\":1", "package.modules_checked\":2");
        assert!(
            validate_performance_measurement_baseline(&mismatched, "compact", &report).is_err()
        );

        let historical = BASELINE.replace(
            "npa.performance.measurements.v0.9",
            "npa.performance.measurements.v0.3",
        );
        assert!(
            validate_performance_measurement_baseline(&historical, "compact", &report).is_err()
        );

        let manual_policy = BASELINE.replace(PERFORMANCE_BASELINES_UPDATE_POLICY, "manual");
        assert!(
            validate_performance_measurement_baseline(&manual_policy, "compact", &report).is_err()
        );

        let reordered_root = BASELINE.replacen(
            "{\"schema\":\"npa.performance.baselines.v0.1\",\"measurement_schema\":\"npa.performance.measurements.v0.9\"",
            "{\"measurement_schema\":\"npa.performance.measurements.v0.9\",\"schema\":\"npa.performance.baselines.v0.1\"",
            1,
        );
        assert!(
            validate_performance_measurement_baseline(&reordered_root, "compact", &report).is_err()
        );

        let mut with_unknown_valid_label =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        with_unknown_valid_label.add_counter(PerformanceMeasurementLabel::PackageLiveResults, 1);
        with_unknown_valid_label.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 1);
        with_unknown_valid_label.add_counter(PerformanceMeasurementLabel::PackageImports, 0);
        assert!(validate_performance_measurement_baseline(
            BASELINE,
            "compact",
            &with_unknown_valid_label.report().unwrap(),
        )
        .is_err());

        let mut with_partial_coverage =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        with_partial_coverage.add_counter(PerformanceMeasurementLabel::PackageLiveResults, 1);
        with_partial_coverage.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 1);
        with_partial_coverage.add_counter(PerformanceMeasurementLabel::PackageCacheResults, 0);
        assert!(validate_performance_measurement_baseline(
            BASELINE,
            "compact",
            &with_partial_coverage.report().unwrap(),
        )
        .is_err());

        let mut with_complete_coverage =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        with_complete_coverage.add_counter(PerformanceMeasurementLabel::PackageLiveResults, 1);
        with_complete_coverage.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 1);
        with_complete_coverage.add_counter(PerformanceMeasurementLabel::PackageCacheResults, 0);
        with_complete_coverage.add_counter(PerformanceMeasurementLabel::PackageMemoResults, 0);
        validate_performance_measurement_baseline(
            BASELINE,
            "compact",
            &with_complete_coverage.report().unwrap(),
        )
        .unwrap();

        let mut missing_declared =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        missing_declared.add_counter(PerformanceMeasurementLabel::PackageLiveResults, 1);
        assert!(validate_performance_measurement_baseline(
            BASELINE,
            "compact",
            &missing_declared.report().unwrap(),
        )
        .is_err());
    }
}
