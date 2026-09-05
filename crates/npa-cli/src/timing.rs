//! Internal timing collection for package audit commands.

use std::collections::BTreeMap;
use std::time::Instant;

use crate::args::PackageTimingMode;
use crate::diagnostic::{CommandResult, CommandTimingMetric, CommandTimings};
use crate::diagnostic::{PACKAGE_TIMINGS_SCHEMA_V0_1, PACKAGE_TIMINGS_SCHEMA_V0_2};
use npa_api::{
    PackageCertificateArtifactObservation, PackagePayloadOwnershipObservation,
    PerformanceMeasurementMode, PerformanceMeasurementRecorder, PerformanceMeasurementReport,
    PerformancePackageSelectionObservation,
};
use npa_cert::CertificatePayloadObservation;
use npa_package::PreparedArtifactRetentionObservation;

pub(crate) const TIMING_LOAD_ROOT_MS: &str = "load_root_ms";
pub(crate) const TIMING_LOAD_LOCK_MS: &str = "load_lock_ms";
pub(crate) const TIMING_DECODE_CERTIFICATES_MS: &str = "decode_certificates_ms";
pub(crate) const TIMING_BUILD_GRAPH_MS: &str = "build_graph_ms";
pub(crate) const TIMING_SELECTION_MS: &str = "selection_ms";
pub(crate) const TIMING_SOURCE_PREFLIGHT_MS: &str = "source_preflight_ms";
pub(crate) const TIMING_PRIORITY_BUILD_MS: &str = "priority_build_ms";
pub(crate) const TIMING_COMPLETION_BUILD_MS: &str = "completion_build_ms";
pub(crate) const TIMING_CACHE_LOOKUP_MS: &str = "cache_lookup_ms";
pub(crate) const TIMING_CHECKER_MS: &str = "checker_ms";
pub(crate) const TIMING_PROJECTION_MS: &str = "projection_ms";
pub(crate) const TIMING_JSON_WRITE_MS: &str = "json_write_ms";
pub(crate) const TIMING_ARTIFACT_COMPARE_MS: &str = "artifact_compare_ms";
pub(crate) const TIMING_TOTAL_MS: &str = "total_ms";

const TIMING_FIELD_ORDER: &[&str] = &[
    TIMING_LOAD_ROOT_MS,
    TIMING_LOAD_LOCK_MS,
    TIMING_DECODE_CERTIFICATES_MS,
    TIMING_BUILD_GRAPH_MS,
    TIMING_SELECTION_MS,
    TIMING_SOURCE_PREFLIGHT_MS,
    TIMING_PRIORITY_BUILD_MS,
    TIMING_COMPLETION_BUILD_MS,
    TIMING_CACHE_LOOKUP_MS,
    TIMING_CHECKER_MS,
    TIMING_PROJECTION_MS,
    TIMING_JSON_WRITE_MS,
    TIMING_ARTIFACT_COMPARE_MS,
    TIMING_TOTAL_MS,
];

pub(crate) struct PackageTimingCollector {
    mode: PackageTimingMode,
    started: Option<Instant>,
    metrics: BTreeMap<&'static str, u128>,
    measurements: Option<PerformanceMeasurementRecorder>,
}

impl PackageTimingCollector {
    pub(crate) fn new(mode: PackageTimingMode) -> Self {
        Self {
            mode,
            started: mode.is_enabled().then(Instant::now),
            metrics: BTreeMap::new(),
            measurements: mode.is_enabled().then(|| {
                PerformanceMeasurementRecorder::new(match mode {
                    PackageTimingMode::Off => PerformanceMeasurementMode::Off,
                    PackageTimingMode::Summary => PerformanceMeasurementMode::Summary,
                    PackageTimingMode::Detailed => PerformanceMeasurementMode::Detailed,
                })
            }),
        }
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.mode.is_enabled()
    }

    pub(crate) fn is_detailed(&self) -> bool {
        self.mode == PackageTimingMode::Detailed
    }

    pub(crate) fn measurement_mode(&self) -> PerformanceMeasurementMode {
        match self.mode {
            PackageTimingMode::Off => PerformanceMeasurementMode::Off,
            PackageTimingMode::Summary => PerformanceMeasurementMode::Summary,
            PackageTimingMode::Detailed => PerformanceMeasurementMode::Detailed,
        }
    }

    pub(crate) fn observe_measurements(
        &mut self,
        measurements: Option<PerformanceMeasurementReport>,
    ) {
        if let (Some(recorder), Some(measurements)) =
            (self.measurements.as_mut(), measurements.as_ref())
        {
            recorder.merge_child_report_preserving_identity(measurements);
        }
    }

    pub(crate) fn observe_package_selection(
        &mut self,
        observation: &PerformancePackageSelectionObservation,
    ) {
        if let Some(recorder) = self.measurements.as_mut() {
            recorder.observe_package_selection(observation);
        }
    }

    pub(crate) fn observe_package_certificate_artifacts(
        &mut self,
        artifacts: &PackageCertificateArtifactObservation,
        retention: Option<&PreparedArtifactRetentionObservation>,
    ) {
        if let Some(recorder) = self.measurements.as_mut() {
            recorder.observe_package_certificate_artifacts(artifacts, retention);
        }
    }

    pub(crate) fn observe_certificate_payload_ownership(
        &mut self,
        certificate: &CertificatePayloadObservation,
    ) {
        if let Some(recorder) = self.measurements.as_mut() {
            recorder.observe_certificate_payload_ownership(
                certificate,
                &PackagePayloadOwnershipObservation::default(),
            );
        }
    }

    pub(crate) fn time_phase<T>(&mut self, field: &'static str, run: impl FnOnce() -> T) -> T {
        if !self.is_enabled() {
            return run();
        }
        let started = Instant::now();
        let value = run();
        self.add_elapsed(field, started.elapsed().as_millis());
        value
    }

    pub(crate) fn observe_elapsed_ms(&mut self, field: &'static str, milliseconds: u64) {
        if self.is_enabled() {
            self.add_elapsed(field, u128::from(milliseconds));
        }
    }

    pub(crate) fn finish_result(mut self, result: CommandResult) -> CommandResult {
        let Some(timings) = self.finish() else {
            return result;
        };
        result.with_timings(timings)
    }

    fn add_elapsed(&mut self, field: &'static str, milliseconds: u128) {
        let total = self.metrics.entry(field).or_insert(0);
        *total = total.saturating_add(milliseconds);
    }

    fn finish(&mut self) -> Option<CommandTimings> {
        if !self.mode.is_enabled() {
            return None;
        }
        let started = self
            .started
            .expect("enabled timing collector has a start instant");
        self.metrics
            .insert(TIMING_TOTAL_MS, started.elapsed().as_millis());
        let metrics = TIMING_FIELD_ORDER
            .iter()
            .filter_map(|field| {
                self.metrics
                    .get(field)
                    .map(|milliseconds| CommandTimingMetric {
                        field: (*field).to_owned(),
                        milliseconds: *milliseconds,
                    })
            })
            .collect();
        let measurements = self
            .measurements
            .as_ref()
            .and_then(PerformanceMeasurementRecorder::report);
        Some(CommandTimings {
            schema: if measurements.is_some() {
                PACKAGE_TIMINGS_SCHEMA_V0_2
            } else {
                PACKAGE_TIMINGS_SCHEMA_V0_1
            },
            mode: self.mode.as_str().to_owned(),
            metrics,
            measurements,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_api::{PerformanceMeasurementLabel, PerformancePackageSelectionBatchPolicy};

    #[test]
    fn off_mode_has_no_start_clock_or_measurement_state() {
        let mut collector = PackageTimingCollector::new(PackageTimingMode::Off);
        assert!(collector.started.is_none());
        assert_eq!(
            collector.measurement_mode(),
            PerformanceMeasurementMode::Off
        );
        assert_eq!(collector.time_phase(TIMING_CHECKER_MS, || 7), 7);
        assert!(collector.metrics.is_empty());
        assert!(collector.finish().is_none());
    }

    #[test]
    fn cache_lookup_intervals_accumulate_when_interleaved() {
        let mut collector = PackageTimingCollector::new(PackageTimingMode::Summary);
        collector.add_elapsed(TIMING_CACHE_LOOKUP_MS, 2);
        collector.add_elapsed(TIMING_CHECKER_MS, 3);
        collector.add_elapsed(TIMING_CACHE_LOOKUP_MS, 5);

        let timings = collector.finish().unwrap();
        let cache_lookup = timings
            .metrics
            .iter()
            .find(|metric| metric.field == TIMING_CACHE_LOOKUP_MS)
            .unwrap();
        assert_eq!(cache_lookup.milliseconds, 7);
        assert!(!timings
            .metrics
            .iter()
            .any(|metric| metric.field == "cache.lookup_elapsed"));
    }

    #[test]
    fn selection_then_checker_finalizes_one_identity_preserving_report() {
        let mut collector = PackageTimingCollector::new(PackageTimingMode::Summary);
        collector.observe_package_selection(&PerformancePackageSelectionObservation {
            batch_policy: PerformancePackageSelectionBatchPolicy::ExecBudget,
            candidate_paths: 129,
            pathspec_batches: 1,
            tracked_queries: 1,
            untracked_queries: 1,
            ..PerformancePackageSelectionObservation::default()
        });
        let mut child = PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Summary)
            .with_input_identity("sha256:checker-input");
        child.add_counter(PerformanceMeasurementLabel::PackageModulesChecked, 1);
        collector.observe_measurements(child.report());

        let timings = collector.finish().unwrap();
        let report = timings.measurements.unwrap();
        assert_eq!(
            report.input_identity.as_deref(),
            Some("sha256:checker-input")
        );
        assert!(report.counters.iter().any(|counter| {
            counter.label == PerformanceMeasurementLabel::PackageSelectionCandidatePaths
                && counter.value == 129
        }));
        assert!(report.counters.iter().any(|counter| {
            counter.label == PerformanceMeasurementLabel::PackageModulesChecked
                && counter.value == 1
        }));

        let mut off = PackageTimingCollector::new(PackageTimingMode::Off);
        off.observe_package_selection(&PerformancePackageSelectionObservation {
            candidate_paths: 129,
            ..PerformancePackageSelectionObservation::default()
        });
        off.observe_measurements(child.report());
        assert!(off.finish().is_none());
    }

    #[test]
    fn selection_observation_projects_only_when_enabled() {
        selection_then_checker_finalizes_one_identity_preserving_report();
    }

    #[test]
    fn checker_measurement_merge_preserves_selection_and_identity() {
        selection_then_checker_finalizes_one_identity_preserving_report();
    }
}
