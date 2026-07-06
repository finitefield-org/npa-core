//! Internal timing collection for package audit commands.

use std::collections::BTreeMap;
use std::time::Instant;

use crate::args::PackageTimingMode;
use crate::diagnostic::{CommandResult, CommandTimingMetric, CommandTimings};

pub(crate) const TIMING_LOAD_ROOT_MS: &str = "load_root_ms";
pub(crate) const TIMING_LOAD_LOCK_MS: &str = "load_lock_ms";
pub(crate) const TIMING_DECODE_CERTIFICATES_MS: &str = "decode_certificates_ms";
pub(crate) const TIMING_BUILD_GRAPH_MS: &str = "build_graph_ms";
pub(crate) const TIMING_SELECTION_MS: &str = "selection_ms";
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
    TIMING_CACHE_LOOKUP_MS,
    TIMING_CHECKER_MS,
    TIMING_PROJECTION_MS,
    TIMING_JSON_WRITE_MS,
    TIMING_ARTIFACT_COMPARE_MS,
    TIMING_TOTAL_MS,
];

pub(crate) struct PackageTimingCollector {
    mode: PackageTimingMode,
    started: Instant,
    metrics: BTreeMap<&'static str, u128>,
}

impl PackageTimingCollector {
    pub(crate) fn new(mode: PackageTimingMode) -> Self {
        Self {
            mode,
            started: Instant::now(),
            metrics: BTreeMap::new(),
        }
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.mode.is_enabled()
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

    pub(crate) fn finish_result(mut self, result: CommandResult) -> CommandResult {
        let Some(timings) = self.finish() else {
            return result;
        };
        result.with_timings(timings)
    }

    fn add_elapsed(&mut self, field: &'static str, milliseconds: u128) {
        *self.metrics.entry(field).or_insert(0) += milliseconds;
    }

    fn finish(&mut self) -> Option<CommandTimings> {
        if !self.mode.is_enabled() {
            return None;
        }
        self.metrics
            .insert(TIMING_TOTAL_MS, self.started.elapsed().as_millis());
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
        Some(CommandTimings {
            mode: self.mode.as_str().to_owned(),
            metrics,
        })
    }
}
