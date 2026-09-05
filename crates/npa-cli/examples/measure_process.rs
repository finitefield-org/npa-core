#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "../../npa-api/examples/support/runtime_source_set.rs"]
mod runtime_source_set;
#[path = "../../npa-api/examples/support/sealed_performance_run.rs"]
mod sealed_performance_run;
#[path = "../../npa-api/examples/support/snap_vmsp_controller.rs"]
mod snap_vmsp_controller;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::io;
use std::mem::MaybeUninit;
use std::os::fd::{AsRawFd as _, RawFd};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{
    atomic::{AtomicBool, AtomicU64, Ordering},
    mpsc, Arc,
};
use std::time::{Duration, Instant};

use closed_private_tree::{
    consume_inherited_detached_executable, create_new_absolute_file, detached_executable_snapshot,
    prepare_new_absolute_private_directory, read_invocation_regular_file, AttachedOutputFile,
    ClosedPrivateDirectory, DetachedExecutable, PreparedPrivateDirectoryDestination,
    SealedRegularFile,
};
use npa_api::{validate_checked_performance_fixture_selection_v02, PerformanceFixtureSelectionV02};
use runtime_source_set::{validate_runtime_source_identity, validate_runtime_source_set};
use snap_vmsp_controller::{AuditBinding, LaneKind, OwnedJson};

const MAX_MANIFEST_BYTES: u64 = 4 * 1024 * 1024;
const MAX_BASELINE_BYTES: u64 = snap_vmsp_controller::MAX_CANONICAL_JSON_BYTES;
const MAX_ORACLE_BYTES: u64 = 4 * 1024 * 1024;
const MAX_BENCHMARK_EXECUTABLE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_MANAGER_EXECUTABLE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_SEALED_MATRIX_MEMBER_BYTES: u64 = 64 * 1024 * 1024;
const MAX_SEALED_MATRIX_TOTAL_BYTES: u64 = 128 * 1024 * 1024;
const MAX_JSON_OPERATION_WORKING_BYTES: u64 = snap_vmsp_controller::MAX_SEMANTIC_STRUCTURE_BYTES;
// A completed projection can simultaneously retain the outer raw and
// completed trees while reconstructing the raw projection and parsing the
// selected baseline.  The population validator additionally retains at most
// one operation's worth of already-validated records while it admits the next
// four-tree projection.  These are separate from the exact retained payload
// byte budget above.
const MAX_COMPLETED_VALIDATION_WORKING_BYTES: u64 = 4 * MAX_JSON_OPERATION_WORKING_BYTES;
const MAX_CONTROLLER_WORKING_BYTES: u64 = 5 * MAX_JSON_OPERATION_WORKING_BYTES;
const CAPTURE_CHUNK_BYTES: usize = 16 * 1024;
const MEASURED_CHILD_TIMEOUT: Duration = Duration::from_secs(15 * 60);
const CAPTURE_DRAIN_TIMEOUT: Duration = Duration::from_secs(2);
const SEALED_MATRIX_NAME: &str = sealed_performance_run::SEAL_NAME;

#[cfg(target_os = "macos")]
const CONTROLLER_TMPDIR: &str = "/private/tmp";
#[cfg(target_os = "linux")]
const CONTROLLER_TMPDIR: &str = "/tmp";
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
const CONTROLLER_TMPDIR: &str = "";

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn write_controller_matrix_digest(
    output: &mut impl io::Write,
    matrix: &[u8],
) -> Result<(), String> {
    // This line is an operational shell ABI, not a persisted provenance
    // value.  Reports, audit bindings, and the seal use tagged
    // `sha256:<hex>` values; both production shell wrappers intentionally
    // accept one raw lowercase-hex digest line from the controller.
    let line = format!("{}\n", snap_vmsp_controller::raw_sha256(matrix));
    output.write_all(line.as_bytes()).map_err(display_error)?;
    output.flush().map_err(display_error)
}

fn write_controller_matrix_digest_then<T>(
    output: &mut impl io::Write,
    matrix: &[u8],
    continuation: impl FnOnce() -> Result<T, String>,
) -> Result<T, String> {
    write_controller_matrix_digest(output, matrix)?;
    continuation()
}

fn validated_controller_tmpdir() -> Result<&'static str, String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        if CONTROLLER_TMPDIR.is_empty() {
            return Err("SNAP/VMSP controller has no fixed temp root on this platform".to_owned());
        }
        let path = Path::new(CONTROLLER_TMPDIR);
        let metadata = path.symlink_metadata().map_err(display_error)?;
        if !metadata.is_dir()
            || metadata.file_type().is_symlink()
            || metadata.uid() != 0
            || metadata.mode() & 0o7777 != 0o1777
            || path.canonicalize().map_err(display_error)? != path
        {
            return Err(format!(
                "SNAP/VMSP controller temp root {CONTROLLER_TMPDIR} is not the canonical root-owned 01777 directory"
            ));
        }
        Ok(CONTROLLER_TMPDIR)
    }
    #[cfg(not(unix))]
    {
        Err("SNAP/VMSP controller requires Unix temp-root semantics".to_owned())
    }
}

struct LaneSnapshots {
    manifest: Vec<u8>,
    baseline: Vec<u8>,
    oracle: Vec<u8>,
    manager: Vec<u8>,
    manager_sha256: String,
    benchmark: Arc<DetachedExecutable>,
    benchmark_build: BenchmarkBuildDescriptor,
    scratch: Arc<ClosedPrivateDirectory>,
}

fn strip_sha256_prefix(value: &str) -> &str {
    value.strip_prefix("sha256:").unwrap_or(value)
}

struct BenchmarkBuildDescriptor {
    source_identity: String,
    cargo_lock_sha256: String,
    cargo_profile: String,
    target: String,
    features: String,
    rustc_vv: String,
    rustflags: String,
    harness_source_sha256: String,
    source_set_sha256: String,
    fixture_parser_source_sha256: Option<String>,
    measure_process_source_sha256: String,
}

struct ExpectedBenchmarkBuildMetadata<'a> {
    target: &'a str,
    features: &'a str,
    rustc_vv: &'a str,
    rustflags: &'a str,
}

fn validate_benchmark_build_metadata(
    observed: &BenchmarkBuildDescriptor,
    expected: &ExpectedBenchmarkBuildMetadata<'_>,
) -> Result<(), String> {
    for (label, observed, expected) in [
        ("target", observed.target.as_str(), expected.target),
        ("features", observed.features.as_str(), expected.features),
        ("rustc -Vv", observed.rustc_vv.as_str(), expected.rustc_vv),
        ("rustflags", observed.rustflags.as_str(), expected.rustflags),
    ] {
        if observed != expected {
            return Err(format!(
                "lane benchmark {label} differs from the independently embedded build descriptor"
            ));
        }
    }
    Ok(())
}

struct ControllerBudget {
    used: AtomicU64,
    maximum: u64,
}

impl ControllerBudget {
    fn new(maximum: u64) -> Self {
        Self {
            used: AtomicU64::new(0),
            maximum,
        }
    }

    fn charge(&self, bytes: u64, label: &str) -> Result<(), String> {
        self.used
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |used| {
                used.checked_add(bytes).filter(|next| *next <= self.maximum)
            })
            .map(|_| ())
            .map_err(|_| format!("SNAP/VMSP owned-byte budget exceeded while retaining {label}"))
    }

    fn reserve(self: &Arc<Self>, bytes: u64, label: &str) -> Result<ControllerReservation, String> {
        self.charge(bytes, label)?;
        Ok(ControllerReservation {
            budget: Arc::clone(self),
            bytes,
        })
    }

    fn release(&self, bytes: u64) {
        if bytes != 0 {
            self.used.fetch_sub(bytes, Ordering::SeqCst);
        }
    }
}

struct ControllerReservation {
    budget: Arc<ControllerBudget>,
    bytes: u64,
}

impl ControllerReservation {
    fn retain(mut self, actual_bytes: u64, label: &str) -> Result<(), String> {
        if actual_bytes > self.bytes {
            return Err(format!(
                "{label} exceeded its pre-allocation SNAP/VMSP reservation"
            ));
        }
        self.budget
            .used
            .fetch_sub(self.bytes - actual_bytes, Ordering::SeqCst);
        self.bytes = 0;
        Ok(())
    }
}

impl Drop for ControllerReservation {
    fn drop(&mut self) {
        if self.bytes != 0 {
            self.budget.used.fetch_sub(self.bytes, Ordering::SeqCst);
        }
    }
}

struct CapturedExecution {
    raw: BudgetedBytes,
    stderr: BudgetedBytes,
    completed: BudgetedBytes,
}

struct BudgetedBytes {
    bytes: Box<[u8]>,
    budget: Arc<ControllerBudget>,
    charged: u64,
}

impl BudgetedBytes {
    fn retain_exact(
        bytes: Box<[u8]>,
        maximum_bytes: u64,
        budget: Arc<ControllerBudget>,
        label: &str,
    ) -> Result<Self, String> {
        let charged = u64::try_from(bytes.len()).map_err(display_error)?;
        if charged > maximum_bytes {
            return Err(format!("{label} exceeded its exact byte envelope"));
        }
        budget.charge(charged, label)?;
        Ok(Self {
            bytes,
            budget,
            charged,
        })
    }

    fn as_slice(&self) -> &[u8] {
        &self.bytes
    }

    fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }
}

impl Drop for BudgetedBytes {
    fn drop(&mut self) {
        self.budget.release(self.charged);
    }
}

struct BudgetedCaptureChunks {
    chunks: Vec<Vec<u8>>,
    retained_budget: Arc<ControllerBudget>,
    working_budget: Arc<ControllerBudget>,
    charged_content_capacity: u64,
    charged_metadata: u64,
    content_bytes: u64,
}

impl BudgetedCaptureChunks {
    fn new(
        member_maximum: u64,
        retained_budget: Arc<ControllerBudget>,
        working_budget: Arc<ControllerBudget>,
        label: &str,
    ) -> Result<Self, String> {
        let chunk_bytes = u64::try_from(CAPTURE_CHUNK_BYTES).map_err(display_error)?;
        let maximum_chunks = member_maximum
            .checked_add(chunk_bytes - 1)
            .ok_or_else(|| format!("measured {label} chunk-count overflowed"))?
            / chunk_bytes;
        let maximum_chunks = usize::try_from(maximum_chunks).map_err(display_error)?;
        let metadata_bytes = maximum_chunks
            .checked_mul(std::mem::size_of::<Vec<u8>>())
            .and_then(|bytes| u64::try_from(bytes).ok())
            .ok_or_else(|| format!("measured {label} chunk metadata overflowed"))?;
        working_budget.charge(metadata_bytes, &format!("measured {label} chunk metadata"))?;
        let mut chunks = Vec::new();
        if let Err(error) = chunks.try_reserve_exact(maximum_chunks) {
            working_budget.release(metadata_bytes);
            return Err(format!("reserve measured {label} chunks: {error}"));
        }
        if chunks.capacity() > maximum_chunks {
            working_budget.release(metadata_bytes);
            return Err(format!(
                "measured {label} chunk allocator exceeded its precharged capacity"
            ));
        }
        Ok(Self {
            chunks,
            retained_budget,
            working_budget,
            charged_content_capacity: 0,
            charged_metadata: metadata_bytes,
            content_bytes: 0,
        })
    }

    fn push(&mut self, bytes: &[u8], member_maximum: u64, label: &str) -> Result<(), String> {
        let bytes_len = u64::try_from(bytes.len()).map_err(display_error)?;
        let next = self
            .content_bytes
            .checked_add(bytes_len)
            .ok_or_else(|| format!("measured {label} size overflowed"))?;
        if next > member_maximum {
            return Err(format!("measured {label} exceeds its byte limit"));
        }
        let mut remaining = bytes;
        while !remaining.is_empty() {
            let needs_chunk = self
                .chunks
                .last()
                .is_none_or(|chunk| chunk.len() == CAPTURE_CHUNK_BYTES);
            if needs_chunk {
                // Charge each complete fixed-capacity allocation before
                // allocating it. Small pipe reads are coalesced into the last
                // chunk, so the preallocated chunk-vector bound is exact.
                let chunk_capacity = u64::try_from(CAPTURE_CHUNK_BYTES).map_err(display_error)?;
                let next_charge = self
                    .charged_content_capacity
                    .checked_add(chunk_capacity)
                    .ok_or_else(|| format!("measured {label} charge overflowed"))?;
                self.working_budget.charge(
                    chunk_capacity,
                    &format!("measured {label} chunk allocation"),
                )?;
                let mut chunk = Vec::new();
                if let Err(error) = chunk.try_reserve_exact(CAPTURE_CHUNK_BYTES) {
                    self.working_budget.release(chunk_capacity);
                    return Err(format!("reserve measured {label} chunk: {error}"));
                }
                if chunk.capacity() > CAPTURE_CHUNK_BYTES {
                    self.working_budget.release(chunk_capacity);
                    return Err(format!(
                        "measured {label} chunk allocator exceeded its precharged capacity"
                    ));
                }
                self.chunks.push(chunk);
                self.charged_content_capacity = next_charge;
            }
            let chunk = self
                .chunks
                .last_mut()
                .ok_or_else(|| format!("measured {label} chunk allocation disappeared"))?;
            let available = CAPTURE_CHUNK_BYTES - chunk.len();
            let take = available.min(remaining.len());
            chunk.extend_from_slice(&remaining[..take]);
            remaining = &remaining[take..];
        }
        self.content_bytes = next;
        Ok(())
    }

    fn into_budgeted_bytes(mut self, label: &str) -> Result<BudgetedBytes, String> {
        let flatten = self.working_budget.reserve(
            self.content_bytes,
            &format!("measured {label} flattening buffer"),
        )?;
        let length = usize::try_from(self.content_bytes).map_err(display_error)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(length)
            .map_err(|error| format!("reserve measured {label} output: {error}"))?;
        if bytes.capacity() > length {
            return Err(format!(
                "measured {label} output allocator exceeded its precharged capacity"
            ));
        }
        for chunk in &self.chunks {
            bytes.extend_from_slice(chunk);
        }
        if bytes.len() != length {
            return Err(format!("measured {label} flattening length mismatch"));
        }
        let content_bytes = self.content_bytes;
        // Keep the exact flatten reservation until every chunk allocation and
        // its metadata have been released, then transfer one exact retained
        // charge to the returned boxed slice.
        self.chunks.clear();
        self.working_budget.release(self.charged_content_capacity);
        self.charged_content_capacity = 0;
        self.retained_budget
            .charge(content_bytes, &format!("measured {label} flattened bytes"))?;
        drop(flatten);
        Ok(BudgetedBytes {
            bytes: bytes.into_boxed_slice(),
            budget: Arc::clone(&self.retained_budget),
            charged: content_bytes,
        })
    }
}

impl Drop for BudgetedCaptureChunks {
    fn drop(&mut self) {
        self.working_budget
            .release(self.charged_content_capacity + self.charged_metadata);
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("measure-process: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let raw_arguments = env::args().skip(1).collect::<Vec<_>>();
    if raw_arguments.first().map(String::as_str) == Some("--run-snap-vmsp-controller") {
        if env::var_os("NPA_MANAGER_EXECUTABLE_AUDIT_FD").is_none() {
            return bootstrap_snap_vmsp_manager(&raw_arguments);
        }
        return run_snap_vmsp_controller(&raw_arguments[1..], consume_manager_executable()?);
    }
    if raw_arguments.first().map(String::as_str) == Some("--validate-snap-vmsp-sealed-run") {
        if env::var_os("NPA_MANAGER_EXECUTABLE_AUDIT_FD").is_none() {
            return bootstrap_snap_vmsp_manager(&raw_arguments);
        }
        return validate_snap_vmsp_sealed_run(&raw_arguments[1..], consume_manager_executable()?);
    }
    let mut arguments = raw_arguments.into_iter();
    let output_flag = arguments.next();
    let output_path = arguments.next();
    let stderr_flag = arguments.next();
    let stderr_path = arguments.next();
    let separator = arguments.next();
    let executable = arguments.next();
    let command_arguments = arguments.collect::<Vec<_>>();
    if output_flag.as_deref() != Some("--output")
        || stderr_flag.as_deref() != Some("--stderr")
        || separator.as_deref() != Some("--")
        || executable.is_none()
    {
        return Err(
            "usage: measure_process --output PATH --stderr PATH -- COMMAND [ARG ...]".to_owned(),
        );
    }

    let output_path = output_path.ok_or("measurement output path disappeared after validation")?;
    let stderr_path = stderr_path.ok_or("measurement stderr path disappeared after validation")?;
    let executable = executable.ok_or("measurement executable disappeared after validation")?;
    let stdout = create_new_absolute_file(Path::new(&output_path), "measurement output")?;
    let stderr = create_new_absolute_file(Path::new(&stderr_path), "measurement stderr")?;
    run_measured_child(stdout, stderr, executable, command_arguments)
}

fn bootstrap_snap_vmsp_manager(arguments: &[String]) -> Result<(), String> {
    use std::os::unix::process::CommandExt as _;

    let controller_tmpdir = validated_controller_tmpdir()?;
    let current = env::current_exe().map_err(display_error)?;
    let executable = detached_executable_snapshot(
        &current,
        MAX_MANAGER_EXECUTABLE_BYTES,
        "SNAP/VMSP manager bootstrap executable",
    )?;
    let file = executable.try_clone_file()?;
    let descriptor = file.as_raw_fd();
    let executable_path = executable.execution_path(descriptor)?;
    let mut command = Command::new(executable_path);
    command
        .args(arguments)
        .env_clear()
        .env("TMPDIR", controller_tmpdir)
        .env("NPA_MANAGER_EXECUTABLE_AUDIT_FD", descriptor.to_string())
        // This inherited bootstrap ABI carries the untagged lowercase
        // 64-hex digest returned by `DetachedExecutable::sha256`. Tagged
        // `sha256:<hex>` values are report data and are not accepted here.
        .env("NPA_MANAGER_EXECUTABLE_SHA256", executable.sha256())
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    append_test_controller_environment(&mut command);
    unsafe {
        command.pre_exec(move || {
            let flags = libc::fcntl(descriptor, libc::F_GETFD);
            if flags < 0 || libc::fcntl(descriptor, libc::F_SETFD, flags & !libc::FD_CLOEXEC) != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let status = command
        .status()
        .map_err(|error| format!("bootstrap SNAP/VMSP manager: {error}"))?;
    if !status.success() {
        return Err(format!(
            "descriptor-bound SNAP/VMSP manager exited {}",
            status.code().unwrap_or(2)
        ));
    }
    Ok(())
}

fn append_test_controller_environment(_command: &mut Command) {
    #[cfg(test)]
    for (name, value) in env::vars_os() {
        if name.to_string_lossy().starts_with("NPA_TEST_") {
            _command.env(name, value);
        }
    }
}

fn consume_manager_executable() -> Result<Vec<u8>, String> {
    let descriptor = env::var("NPA_MANAGER_EXECUTABLE_AUDIT_FD")
        .map_err(|_| "manager executable audit descriptor is absent".to_owned())?
        .parse::<i32>()
        .map_err(|_| "manager executable audit descriptor is invalid".to_owned())?;
    let expected = env::var("NPA_MANAGER_EXECUTABLE_SHA256")
        .map_err(|_| "manager executable audit hash is absent".to_owned())?;
    if expected.len() != 64
        || !expected
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("manager executable audit hash is not raw lowercase SHA-256".to_owned());
    }
    let bytes = consume_inherited_detached_executable(
        descriptor,
        MAX_MANAGER_EXECUTABLE_BYTES,
        "SNAP/VMSP manager executable",
    )?;
    if snap_vmsp_controller::raw_sha256(&bytes) != expected {
        return Err("manager executable audit hash mismatch".to_owned());
    }
    Ok(bytes)
}

fn parse_controller_arguments(arguments: &[String]) -> Result<BTreeMap<&str, &str>, String> {
    if arguments.is_empty() || !arguments.len().is_multiple_of(2) {
        return Err("SNAP/VMSP controller arguments must be flag/value pairs".to_owned());
    }
    let mut values = BTreeMap::new();
    for pair in arguments.as_chunks::<2>().0 {
        let flag = pair[0].as_str();
        if !matches!(
            flag,
            "--kind"
                | "--manifest"
                | "--baseline"
                | "--oracle"
                | "--benchmark"
                | "--source-identity"
                | "--output"
        ) {
            return Err(format!("unknown SNAP/VMSP controller option {flag}"));
        }
        if values.insert(flag, pair[1].as_str()).is_some() {
            return Err(format!("duplicate SNAP/VMSP controller option {flag}"));
        }
    }
    Ok(values)
}

fn required_controller_value<'a>(
    values: &BTreeMap<&str, &'a str>,
    key: &str,
) -> Result<&'a str, String> {
    values
        .get(key)
        .copied()
        .ok_or_else(|| format!("missing SNAP/VMSP controller option {key}"))
}

fn lane_from_controller_value(value: &str) -> Result<LaneKind, String> {
    match value {
        "snapshot" => Ok(LaneKind::Snapshot),
        "shared-payload" => Ok(LaneKind::SharedPayload),
        _ => Err("SNAP/VMSP controller kind must be snapshot or shared-payload".to_owned()),
    }
}

fn run_snap_vmsp_controller(arguments: &[String], manager: Vec<u8>) -> Result<(), String> {
    let values = parse_controller_arguments(arguments)?;
    let kind = lane_from_controller_value(required_controller_value(&values, "--kind")?)?;
    let manifest_path = Path::new(required_controller_value(&values, "--manifest")?);
    let baseline_path = Path::new(required_controller_value(&values, "--baseline")?);
    let oracle_path = Path::new(required_controller_value(&values, "--oracle")?);
    let benchmark_path = Path::new(required_controller_value(&values, "--benchmark")?);
    let source_identity = required_controller_value(&values, "--source-identity")?;
    let output = Path::new(required_controller_value(&values, "--output")?);
    if !output.is_absolute() {
        return Err("SNAP/VMSP final output must be absolute".to_owned());
    }
    if !valid_source_identity(source_identity)
        || env!("NPA_CLI_BUILD_SOURCE_REVISION") == "unbound"
        || env!("NPA_CLI_BUILD_SOURCE_REVISION") != source_identity
    {
        return Err("SNAP/VMSP source identity differs from the bound manager build".to_owned());
    }
    // Existing artifacts are validated without executing children. For a new
    // run, retain the complete destination parent/name chain and its absence
    // before any child starts; final creation later consumes this capability.
    if output.exists() || output.symlink_metadata().is_ok() {
        return validate_existing_snap_vmsp_sealed_run(
            kind,
            manager,
            manifest_path,
            baseline_path,
            oracle_path,
            benchmark_path,
            source_identity,
            output,
        );
    }
    let destination = prepare_new_absolute_private_directory(output, "snap-vmsp-final")?;

    let budget = Arc::new(ControllerBudget::new(MAX_SEALED_MATRIX_TOTAL_BYTES));
    budget.charge(
        u64::try_from(manager.capacity()).map_err(display_error)?,
        "manager audit executable allocation",
    )?;
    let working_budget = Arc::new(ControllerBudget::new(MAX_CONTROLLER_WORKING_BYTES));
    let snapshots = snapshot_lane_inputs(
        kind,
        manager,
        manifest_path,
        baseline_path,
        oracle_path,
        benchmark_path,
        Arc::clone(&budget),
    )?;
    let manifest_source = std::str::from_utf8(&snapshots.manifest).map_err(display_error)?;
    let manifest = validate_checked_performance_fixture_selection_v02(manifest_source)
        .map_err(display_error)?;
    let whole_input_reservation = working_budget.reserve(
        MAX_JSON_OPERATION_WORKING_BYTES,
        "whole baseline and oracle validation working set",
    )?;
    snap_vmsp_controller::validate_whole_inputs(
        kind,
        &manifest.scenarios,
        &snapshots.baseline,
        &snapshots.oracle,
    )?;
    drop(whole_input_reservation);
    let executions = snap_vmsp_controller::execution_catalog(kind, &manifest.scenarios)?;
    let binding_storage = manager_audit_binding(kind, source_identity, &snapshots)?;
    let binding = binding_storage.as_binding();
    let mut captured = Vec::with_capacity(executions.len());
    for execution in &executions {
        snapshots.benchmark.verify()?;
        verify_lane_input_scratch(&snapshots)?;
        let command_arguments =
            controller_child_arguments(kind, execution, &snapshots, source_identity)?;
        let (measurement, raw, stderr) = run_measured_child_captured_budgeted(
            &snapshots.benchmark,
            command_arguments,
            MAX_SEALED_MATRIX_MEMBER_BYTES,
            MAX_SEALED_MATRIX_MEMBER_BYTES,
            Arc::clone(&budget),
            Arc::clone(&working_budget),
        )?;
        let (peak_rss_kib, exit_code) = parse_measurement_line(&measurement)?;
        if exit_code != 0 {
            return Err(format!(
                "{} child {} exited {exit_code}; final directory was not created; stderr={}",
                kind.lane_id(),
                execution.ordinal,
                String::from_utf8_lossy(stderr.as_slice())
            ));
        }
        if !stderr.is_empty() {
            return Err(format!(
                "{} child {} emitted stderr; successful persisted stderr must be exactly empty",
                kind.lane_id(),
                execution.ordinal
            ));
        }
        let completed_capacity = snap_vmsp_controller::completed_record_byte_reservation(
            u64::try_from(raw.as_slice().len()).map_err(display_error)?,
        )?;
        let completed_bytes_reservation = working_budget.reserve(
            completed_capacity,
            "completed record construction byte envelope",
        )?;
        let completed_working_reservation = working_budget.reserve(
            MAX_COMPLETED_VALIDATION_WORKING_BYTES,
            "completed record parser working set",
        )?;
        let completed = snap_vmsp_controller::complete_captured_record(
            kind,
            execution,
            raw.as_slice(),
            peak_rss_kib,
            &manifest.scenarios,
            &snapshots.baseline,
            &snapshots.oracle,
            &binding,
        )?;
        let parsed = snap_vmsp_controller::validate_completed_against_raw(
            kind,
            execution,
            raw.as_slice(),
            completed.as_ref(),
            &manifest.scenarios,
            &snapshots.baseline,
            &snapshots.oracle,
            &binding,
        )?;
        drop(completed_working_reservation);
        let completed = BudgetedBytes::retain_exact(
            completed,
            completed_capacity,
            Arc::clone(&budget),
            "completed record exact allocation",
        )?;
        drop(completed_bytes_reservation);
        captured.push(CapturedExecution {
            raw,
            stderr,
            completed,
        });
        // Parsing proves the completed projection before retention. Reparse
        // once for matrix construction below instead of retaining and then
        // cloning an entire second execution population.
        drop(parsed);
    }
    snapshots.benchmark.verify()?;
    verify_lane_input_scratch(&snapshots)?;
    let matrix_capacity = snap_vmsp_controller::MAX_CANONICAL_JSON_BYTES;
    let matrix_bytes_reservation =
        working_budget.reserve(matrix_capacity, "matrix report byte envelope")?;
    let mut parsed = Vec::with_capacity(executions.len());
    for (execution, capture) in executions.iter().zip(&captured) {
        let parse_reservation = working_budget.reserve(
            MAX_COMPLETED_VALIDATION_WORKING_BYTES,
            "matrix completed-record parser working set",
        )?;
        let record = snap_vmsp_controller::validate_completed_against_raw(
            kind,
            execution,
            capture.raw.as_slice(),
            capture.completed.as_slice(),
            &manifest.scenarios,
            &snapshots.baseline,
            &snapshots.oracle,
            &binding,
        )?;
        parse_reservation.retain(record.retained_bytes()?, "matrix completed record")?;
        parsed.push(record);
    }
    let matrix_build_reservation = working_budget.reserve(
        2 * MAX_JSON_OPERATION_WORKING_BYTES,
        "matrix construction working set",
    )?;
    let matrix = snap_vmsp_controller::build_matrix(
        kind,
        &executions,
        &parsed,
        &manifest.scenarios,
        &binding,
    )?;
    let matrix = BudgetedBytes::retain_exact(
        matrix,
        matrix_capacity,
        Arc::clone(&budget),
        "matrix report exact allocation",
    )?;
    drop(matrix_bytes_reservation);
    drop(matrix_build_reservation);
    let matrix_validation_reservation = working_budget.reserve(
        2 * MAX_JSON_OPERATION_WORKING_BYTES,
        "matrix validation working set",
    )?;
    snap_vmsp_controller::validate_matrix(
        kind,
        matrix.as_slice(),
        &executions,
        &parsed,
        &manifest.scenarios,
        &binding,
    )?;
    drop(matrix_validation_reservation);
    // Publication repeats the independent semantic-consumer path from exact
    // owned bytes.  Do not keep the producer's parsed population live across
    // that second validation pass.
    drop(parsed);
    publish_owned_snap_vmsp_run(
        kind,
        destination,
        &snapshots,
        &manifest.scenarios,
        &executions,
        &captured,
        matrix.as_slice(),
        &binding,
        &mut io::stdout().lock(),
    )
}

fn validate_snap_vmsp_sealed_run(arguments: &[String], manager: Vec<u8>) -> Result<(), String> {
    let values = parse_controller_arguments(arguments)?;
    let kind = lane_from_controller_value(required_controller_value(&values, "--kind")?)?;
    validate_existing_snap_vmsp_sealed_run(
        kind,
        manager,
        Path::new(required_controller_value(&values, "--manifest")?),
        Path::new(required_controller_value(&values, "--baseline")?),
        Path::new(required_controller_value(&values, "--oracle")?),
        Path::new(required_controller_value(&values, "--benchmark")?),
        required_controller_value(&values, "--source-identity")?,
        Path::new(required_controller_value(&values, "--output")?),
    )
}

fn valid_source_identity(value: &str) -> bool {
    let oid = value.strip_suffix("-dirty").unwrap_or(value);
    oid.len() == 40
        && oid
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn parse_measurement_line(value: &str) -> Result<(u64, i32), String> {
    let fields = value.split('\t').collect::<Vec<_>>();
    if fields.len() != 3 || fields[0].parse::<f64>().is_err() {
        return Err("measured child returned a malformed measurement line".to_owned());
    }
    let peak = fields[1]
        .parse::<u64>()
        .map_err(|_| "measured child peak RSS is invalid".to_owned())?;
    let exit = fields[2]
        .parse::<i32>()
        .map_err(|_| "measured child exit status is invalid".to_owned())?;
    Ok((peak, exit))
}

struct BindingStorage {
    source_identity: String,
    manifest_sha256: String,
    baseline_sha256: String,
    oracle_sha256: String,
    benchmark_sha256: String,
    manager_sha256: String,
    manager_source_set_sha256: String,
    manager_source_sha256: String,
    manager_cargo_lock_sha256: String,
    manager_cargo_profile: String,
    manager_target: String,
    manager_features: String,
    manager_rustc_vv: String,
    manager_rustflags: String,
    benchmark_cargo_lock_sha256: String,
    benchmark_cargo_profile: String,
    benchmark_target: String,
    benchmark_features: String,
    benchmark_rustc_vv: String,
    benchmark_rustflags: String,
    benchmark_harness_source_sha256: String,
    benchmark_source_set_sha256: String,
    benchmark_fixture_parser_source_sha256: Option<String>,
    benchmark_measure_process_source_sha256: String,
}

impl BindingStorage {
    fn as_binding(&self) -> AuditBinding<'_> {
        AuditBinding {
            source_identity: &self.source_identity,
            manifest_sha256: &self.manifest_sha256,
            baseline_sha256: &self.baseline_sha256,
            oracle_sha256: &self.oracle_sha256,
            benchmark_sha256: &self.benchmark_sha256,
            manager_sha256: &self.manager_sha256,
            manager_source_set_sha256: &self.manager_source_set_sha256,
            manager_source_sha256: &self.manager_source_sha256,
            manager_cargo_lock_sha256: &self.manager_cargo_lock_sha256,
            manager_cargo_profile: &self.manager_cargo_profile,
            manager_target: &self.manager_target,
            manager_features: &self.manager_features,
            manager_rustc_vv: &self.manager_rustc_vv,
            manager_rustflags: &self.manager_rustflags,
            benchmark_cargo_lock_sha256: &self.benchmark_cargo_lock_sha256,
            benchmark_cargo_profile: &self.benchmark_cargo_profile,
            benchmark_target: &self.benchmark_target,
            benchmark_features: &self.benchmark_features,
            benchmark_rustc_vv: &self.benchmark_rustc_vv,
            benchmark_rustflags: &self.benchmark_rustflags,
            benchmark_harness_source_sha256: &self.benchmark_harness_source_sha256,
            benchmark_source_set_sha256: &self.benchmark_source_set_sha256,
            benchmark_fixture_parser_source_sha256: self
                .benchmark_fixture_parser_source_sha256
                .as_deref(),
            benchmark_measure_process_source_sha256: &self.benchmark_measure_process_source_sha256,
        }
    }
}

fn decode_build_hex(value: &str, label: &str) -> Result<String, String> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    {
        return Err(format!("embedded {label} is not lowercase hexadecimal"));
    }
    let mut bytes = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().as_chunks::<2>().0 {
        let digit = |byte: u8| match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => Err(format!("embedded {label} has an invalid nibble")),
        };
        bytes.push((digit(pair[0])? << 4) | digit(pair[1])?);
    }
    String::from_utf8(bytes).map_err(|error| format!("embedded {label} is not UTF-8: {error}"))
}

fn manager_audit_binding(
    kind: LaneKind,
    source_identity: &str,
    snapshots: &LaneSnapshots,
) -> Result<BindingStorage, String> {
    let workspace = workspace_root()?;
    validate_runtime_source_identity(&workspace, source_identity)?;
    let source_set = validate_runtime_source_set(
        &workspace,
        env!("NPA_CLI_BUILD_SNAP_VMSP_MANAGER_SOURCE_SET_PATHS"),
        b"npa-snap-vmsp-manager-source-set-v1\0",
        env!("NPA_CLI_BUILD_SNAP_VMSP_MANAGER_SOURCE_SET_SHA256"),
        "SNAP/VMSP manager",
    )?;
    let manager_source = read_invocation_regular_file(
        &workspace.join("crates/npa-cli/examples/measure_process.rs"),
        MAX_SEALED_MATRIX_MEMBER_BYTES,
        "measure-process source",
    )?;
    let manager_source_sha256 = snap_vmsp_controller::raw_sha256(&manager_source);
    if manager_source_sha256 != env!("NPA_CLI_BUILD_MEASURE_PROCESS_SOURCE_SHA256") {
        return Err("runtime measure-process source differs from the manager build".to_owned());
    }
    let cargo_lock = read_invocation_regular_file(
        &workspace.join("Cargo.lock"),
        MAX_SEALED_MATRIX_MEMBER_BYTES,
        "manager Cargo.lock",
    )?;
    let cargo_lock_sha256 = snap_vmsp_controller::raw_sha256(&cargo_lock);
    if cargo_lock_sha256 != env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256") {
        return Err("runtime Cargo.lock differs from the manager build".to_owned());
    }
    let manifest_sha256 = snap_vmsp_controller::sha256(&snapshots.manifest);
    let baseline_sha256 = snap_vmsp_controller::sha256(&snapshots.baseline);
    let oracle_sha256 = snap_vmsp_controller::sha256(&snapshots.oracle);
    for (label, actual, expected) in [
        (
            "manifest",
            manifest_sha256.as_str(),
            concat!(
                "sha256:",
                env!("NPA_CLI_BUILD_PERFORMANCE_MANIFEST_V02_SHA256")
            ),
        ),
        (
            "baseline",
            baseline_sha256.as_str(),
            concat!("sha256:", env!("NPA_CLI_BUILD_PERFORMANCE_BASELINE_SHA256")),
        ),
        (
            "oracle",
            oracle_sha256.as_str(),
            concat!("sha256:", env!("NPA_CLI_BUILD_FIXTURE_ORACLE_SHA256")),
        ),
    ] {
        if actual != expected {
            return Err(format!("SNAP/VMSP {label} differs from the manager build"));
        }
    }
    if env!("NPA_CLI_BUILD_CARGO_PROFILE") != "release" {
        return Err("SNAP/VMSP manager must be a release build".to_owned());
    }
    let manager_source_set_sha256 = source_set;
    let manager_sha256 = snapshots.manager_sha256.clone();
    // The inherited descriptor ABI is intentionally raw lowercase SHA-256,
    // but persisted report/matrix/semantic-audit hashes use the repository's
    // tagged `sha256:<hex>` representation. Keep that boundary explicit.
    let benchmark_sha256 = snap_vmsp_controller::sha256(snapshots.benchmark.audit_bytes());
    if benchmark_sha256 != format!("sha256:{}", snapshots.benchmark.sha256()) {
        return Err("benchmark executable raw and tagged audit hashes disagree".to_owned());
    }
    let expected_source_set = match kind {
        LaneKind::Snapshot => env!("NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_SHA256"),
        LaneKind::SharedPayload => env!("NPA_CLI_BUILD_VMSP_BENCHMARK_SOURCE_SET_SHA256"),
    };
    let expected_harness = match kind {
        LaneKind::Snapshot => env!("NPA_CLI_BUILD_SNAPSHOT_HARNESS_SOURCE_SHA256"),
        LaneKind::SharedPayload => env!("NPA_CLI_BUILD_VMSP_HARNESS_SOURCE_SHA256"),
    };
    let expected_fixture_parser = match kind {
        LaneKind::Snapshot => None,
        LaneKind::SharedPayload => Some(env!("NPA_CLI_BUILD_VMSP_FIXTURE_PARSER_SOURCE_SHA256")),
    };
    for (label, observed, expected) in [
        (
            "source set",
            snapshots.benchmark_build.source_set_sha256.as_str(),
            expected_source_set,
        ),
        (
            "harness source",
            snapshots.benchmark_build.harness_source_sha256.as_str(),
            expected_harness,
        ),
        (
            "measurement source",
            snapshots
                .benchmark_build
                .measure_process_source_sha256
                .as_str(),
            env!("NPA_CLI_BUILD_MEASURE_PROCESS_SOURCE_SHA256"),
        ),
    ] {
        if strip_sha256_prefix(observed) != strip_sha256_prefix(expected) {
            return Err(format!(
                "runtime lane benchmark {label} differs from the manager build closure"
            ));
        }
    }
    if snapshots
        .benchmark_build
        .fixture_parser_source_sha256
        .as_deref()
        .map(strip_sha256_prefix)
        != expected_fixture_parser.map(strip_sha256_prefix)
    {
        return Err("runtime VMSP fixture parser differs from manager build closure".to_owned());
    }
    if snapshots.benchmark_build.source_identity != source_identity {
        return Err("benchmark build descriptor source identity mismatch".to_owned());
    }
    if snapshots.benchmark_build.cargo_profile != "release" {
        return Err("SNAP/VMSP benchmark must be a release build".to_owned());
    }
    if strip_sha256_prefix(&snapshots.benchmark_build.cargo_lock_sha256)
        != env!("NPA_CLI_BUILD_CARGO_LOCK_SHA256")
    {
        return Err("lane benchmark Cargo.lock differs from the manager build".to_owned());
    }
    let expected_benchmark_rustc_vv = match kind {
        LaneKind::Snapshot => decode_build_hex(
            env!("NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_RUSTC_VV_HEX"),
            "SNAP benchmark rustc -Vv",
        )?,
        LaneKind::SharedPayload => decode_build_hex(
            npa_api::npa_api_build_descriptor().rustc_vv_hex,
            "VMSP benchmark rustc -Vv",
        )?,
    };
    let expected_benchmark_rustflags = match kind {
        LaneKind::Snapshot => decode_build_hex(
            env!("NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_RUSTFLAGS_HEX"),
            "SNAP benchmark rustflags",
        )?,
        LaneKind::SharedPayload => decode_build_hex(
            npa_api::npa_api_build_descriptor().rustflags_hex,
            "VMSP benchmark rustflags",
        )?,
    };
    validate_benchmark_build_metadata(
        &snapshots.benchmark_build,
        &ExpectedBenchmarkBuildMetadata {
            target: match kind {
                LaneKind::Snapshot => env!("NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_TARGET"),
                LaneKind::SharedPayload => npa_api::npa_api_build_descriptor().target,
            },
            features: match kind {
                LaneKind::Snapshot => env!("NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_FEATURES"),
                LaneKind::SharedPayload => npa_api::npa_api_build_descriptor().features,
            },
            rustc_vv: &expected_benchmark_rustc_vv,
            rustflags: &expected_benchmark_rustflags,
        },
    )?;
    let manager_rustc_vv = decode_build_hex(env!("NPA_CLI_BUILD_RUSTC_VV_HEX"), "rustc -Vv")?;
    let manager_rustflags = decode_build_hex(env!("NPA_CLI_BUILD_RUSTFLAGS_HEX"), "rustflags")?;
    Ok(BindingStorage {
        source_identity: source_identity.to_owned(),
        manifest_sha256,
        baseline_sha256,
        oracle_sha256,
        benchmark_sha256,
        manager_sha256,
        manager_source_set_sha256,
        manager_source_sha256,
        manager_cargo_lock_sha256: cargo_lock_sha256.clone(),
        manager_cargo_profile: env!("NPA_CLI_BUILD_CARGO_PROFILE").to_owned(),
        manager_target: env!("NPA_CLI_BUILD_TARGET").to_owned(),
        manager_features: env!("NPA_CLI_BUILD_CARGO_FEATURES").to_owned(),
        manager_rustc_vv: manager_rustc_vv.clone(),
        manager_rustflags: manager_rustflags.clone(),
        benchmark_cargo_lock_sha256: strip_sha256_prefix(
            &snapshots.benchmark_build.cargo_lock_sha256,
        )
        .to_owned(),
        benchmark_cargo_profile: snapshots.benchmark_build.cargo_profile.clone(),
        benchmark_target: snapshots.benchmark_build.target.clone(),
        benchmark_features: snapshots.benchmark_build.features.clone(),
        benchmark_rustc_vv: snapshots.benchmark_build.rustc_vv.clone(),
        benchmark_rustflags: snapshots.benchmark_build.rustflags.clone(),
        benchmark_harness_source_sha256: snapshots.benchmark_build.harness_source_sha256.clone(),
        benchmark_source_set_sha256: snapshots.benchmark_build.source_set_sha256.clone(),
        benchmark_fixture_parser_source_sha256: snapshots
            .benchmark_build
            .fixture_parser_source_sha256
            .clone(),
        benchmark_measure_process_source_sha256: snapshots
            .benchmark_build
            .measure_process_source_sha256
            .clone(),
    })
}

fn workspace_root() -> Result<PathBuf, String> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    if !manifest.is_absolute() {
        return Err("embedded npa-cli manifest directory is not absolute".to_owned());
    }
    let root = manifest
        .parent()
        .and_then(Path::parent)
        .ok_or("npa-cli is not nested below its workspace")?;
    let canonical = root.canonicalize().map_err(display_error)?;
    if canonical != root {
        return Err("embedded npa-cli workspace is not canonical".to_owned());
    }
    Ok(root.to_owned())
}

fn snapshot_lane_inputs(
    kind: LaneKind,
    manager: Vec<u8>,
    manifest_path: &Path,
    baseline_path: &Path,
    oracle_path: &Path,
    benchmark_path: &Path,
    budget: Arc<ControllerBudget>,
) -> Result<LaneSnapshots, String> {
    let manifest_reservation =
        budget.reserve(MAX_MANIFEST_BYTES, "manifest snapshot allocation envelope")?;
    let manifest =
        read_invocation_regular_file(manifest_path, MAX_MANIFEST_BYTES, "SNAP/VMSP manifest")?;
    manifest_reservation.retain(
        u64::try_from(manifest.capacity()).map_err(display_error)?,
        "manifest snapshot allocation",
    )?;
    let baseline_reservation =
        budget.reserve(MAX_BASELINE_BYTES, "baseline snapshot allocation envelope")?;
    let baseline =
        read_invocation_regular_file(baseline_path, MAX_BASELINE_BYTES, "SNAP/VMSP baseline")?;
    baseline_reservation.retain(
        u64::try_from(baseline.capacity()).map_err(display_error)?,
        "baseline snapshot allocation",
    )?;
    let oracle_reservation =
        budget.reserve(MAX_ORACLE_BYTES, "oracle snapshot allocation envelope")?;
    let oracle = read_invocation_regular_file(oracle_path, MAX_ORACLE_BYTES, "SNAP/VMSP oracle")?;
    oracle_reservation.retain(
        u64::try_from(oracle.capacity()).map_err(display_error)?,
        "oracle snapshot allocation",
    )?;
    let benchmark = snapshot_budgeted_benchmark(benchmark_path, Arc::clone(&budget))?;
    let benchmark_build = query_benchmark_build_descriptor(kind, &benchmark)?;
    let manager_sha256 = snap_vmsp_controller::sha256(&manager);
    let scratch = Arc::new(ClosedPrivateDirectory::new("npa-snap-vmsp-inputs")?);
    scratch.create_new_file(Path::new("fixture-manifest.json"), &manifest)?;
    scratch.create_new_file(Path::new("measurement-baseline.json"), &baseline)?;
    scratch.create_new_file(Path::new("fixture-oracle.tsv"), &oracle)?;
    scratch.sync_root_and_parent()?;
    Ok(LaneSnapshots {
        manifest,
        baseline,
        oracle,
        manager,
        manager_sha256,
        benchmark,
        benchmark_build,
        scratch,
    })
}

fn snapshot_budgeted_benchmark(
    benchmark_path: &Path,
    budget: Arc<ControllerBudget>,
) -> Result<Arc<DetachedExecutable>, String> {
    let reservation = budget.reserve(
        MAX_BENCHMARK_EXECUTABLE_BYTES,
        "benchmark audit executable allocation envelope",
    )?;
    let benchmark = Arc::new(detached_executable_snapshot(
        benchmark_path,
        MAX_BENCHMARK_EXECUTABLE_BYTES,
        "SNAP/VMSP benchmark executable",
    )?);
    reservation.retain(
        u64::try_from(benchmark.audit_allocation_bytes()).map_err(display_error)?,
        "benchmark audit executable allocation",
    )?;
    Ok(benchmark)
}

fn verify_lane_input_scratch(snapshots: &LaneSnapshots) -> Result<(), String> {
    for (name, expected, maximum) in [
        (
            "fixture-manifest.json",
            snapshots.manifest.as_slice(),
            MAX_MANIFEST_BYTES,
        ),
        (
            "measurement-baseline.json",
            snapshots.baseline.as_slice(),
            MAX_BASELINE_BYTES,
        ),
        (
            "fixture-oracle.tsv",
            snapshots.oracle.as_slice(),
            MAX_ORACLE_BYTES,
        ),
    ] {
        if snapshots
            .scratch
            .read_regular_file(Path::new(name), maximum)?
            != expected
        {
            return Err(format!("SNAP/VMSP private input snapshot {name} changed"));
        }
    }
    Ok(())
}

fn controller_child_arguments(
    kind: LaneKind,
    execution: &snap_vmsp_controller::Execution,
    snapshots: &LaneSnapshots,
    source_identity: &str,
) -> Result<Vec<String>, String> {
    let manifest = snapshots.scratch.path().join("fixture-manifest.json");
    let baseline = snapshots.scratch.path().join("measurement-baseline.json");
    let oracle = snapshots.scratch.path().join("fixture-oracle.tsv");
    let as_string = |path: &Path| {
        path.to_str()
            .map(str::to_owned)
            .ok_or("SNAP/VMSP private input path is not UTF-8")
    };
    let mut arguments = match kind {
        LaneKind::Snapshot => vec![
            "--scenario".to_owned(),
            execution.scenario.clone(),
            "--manifest".to_owned(),
            as_string(&manifest)?,
            "--baseline".to_owned(),
            as_string(&baseline)?,
            "--oracle".to_owned(),
            as_string(&oracle)?,
            "--source-identity".to_owned(),
            source_identity.to_owned(),
            "--sample-index".to_owned(),
            execution
                .sample_index
                .ok_or("SNAP execution omits sample index")?
                .to_string(),
        ],
        LaneKind::SharedPayload => vec![
            "--fixture-manifest".to_owned(),
            as_string(&manifest)?,
            "--baseline".to_owned(),
            as_string(&baseline)?,
            "--oracle".to_owned(),
            as_string(&oracle)?,
            "--source-identity".to_owned(),
            source_identity.to_owned(),
            "--scenario".to_owned(),
            execution.scenario.clone(),
            "--measurements".to_owned(),
            "detailed".to_owned(),
            "--warmup".to_owned(),
            "1".to_owned(),
            "--samples".to_owned(),
            "7".to_owned(),
        ],
    };
    if kind == LaneKind::SharedPayload {
        if let Some(sample) = execution.sample_index {
            arguments.push("--sample-index".to_owned());
            arguments.push(sample.to_string());
        }
    }
    Ok(arguments)
}

#[allow(clippy::too_many_arguments)]
fn publish_owned_snap_vmsp_run(
    kind: LaneKind,
    destination: PreparedPrivateDirectoryDestination,
    snapshots: &LaneSnapshots,
    rows: &[PerformanceFixtureSelectionV02],
    executions: &[snap_vmsp_controller::Execution],
    captured: &[CapturedExecution],
    matrix: &[u8],
    binding: &AuditBinding<'_>,
    operational_output: &mut impl io::Write,
) -> Result<(), String> {
    if executions.len() != captured.len() || executions.len() != kind.execution_count() {
        return Err("cannot publish an incomplete SNAP/VMSP execution population".to_owned());
    }
    snapshots.benchmark.verify()?;
    verify_lane_input_scratch(snapshots)?;
    let manifest_order = snap_vmsp_controller::manifest_order_json(kind, rows);
    let mut payload = BTreeMap::<PathBuf, &[u8]>::from([
        (
            PathBuf::from(".fixture-manifest.json"),
            snapshots.manifest.as_slice(),
        ),
        (
            PathBuf::from(".measurement-baseline.json"),
            snapshots.baseline.as_slice(),
        ),
        (
            PathBuf::from(".fixture-oracle.tsv"),
            snapshots.oracle.as_slice(),
        ),
        (
            PathBuf::from(".benchmark-executable"),
            snapshots.benchmark.audit_bytes(),
        ),
        (
            PathBuf::from(".measure-process-executable"),
            snapshots.manager.as_slice(),
        ),
        (
            PathBuf::from(".manifest-order.json"),
            manifest_order.as_slice(),
        ),
        (PathBuf::from("matrix.json"), matrix),
    ]);
    for (execution, capture) in executions.iter().zip(captured) {
        payload.insert(execution.raw_name(), capture.raw.as_slice());
        payload.insert(execution.stderr_name(), capture.stderr.as_slice());
        payload.insert(execution.completed_name(), capture.completed.as_slice());
    }
    let expected = snap_vmsp_controller::expected_payload_catalog(kind, rows)?;
    if payload.keys().cloned().collect::<BTreeSet<_>>() != expected {
        return Err("owned SNAP/VMSP payload differs from its exact catalog".to_owned());
    }
    validate_semantic_byte_refs(kind, &payload, rows, binding)?;
    // The raw operational digest is the final fallible side effect before the
    // commit begins. The shell observes it only if this process later exits
    // successfully. A broken stdout therefore cannot leave a newly created
    // sealed destination that the wrapper reports as failed.
    let directory =
        write_controller_matrix_digest_then(operational_output, matrix, || destination.create())?;
    let result =
        seal_owned_semantically_validated_directory(kind, &directory, &payload, rows, binding);
    // The direct final directory and every partial member are preserved on
    // failure. Online inspect-then-delete cleanup is intentionally forbidden.
    directory.leave_in_place();
    result
}

fn seal_owned_semantically_validated_directory(
    kind: LaneKind,
    directory: &ClosedPrivateDirectory,
    payload: &BTreeMap<PathBuf, &[u8]>,
    rows: &[PerformanceFixtureSelectionV02],
    binding: &AuditBinding<'_>,
) -> Result<(), String> {
    validate_semantic_byte_refs(kind, payload, rows, binding)?;
    write_and_seal_owned_directory(
        directory,
        payload,
        kind.lane_id(),
        kind.matrix_schema(),
        MAX_SEALED_MATRIX_MEMBER_BYTES,
        MAX_SEALED_MATRIX_TOTAL_BYTES,
    )
}

/// Write a complete already-validated payload through one retained final-root
/// capability, create the canonical commit marker last, and perform the same
/// exact readback used by production before syncing the directory and parent.
/// Semantic lane validation deliberately remains the caller's prerequisite.
fn write_and_seal_owned_directory(
    directory: &ClosedPrivateDirectory,
    payload: &BTreeMap<PathBuf, &[u8]>,
    lane_id: &str,
    report_schema: &str,
    maximum_member_bytes: u64,
    maximum_payload_bytes: u64,
) -> Result<(), String> {
    for (path, bytes) in payload {
        directory.create_new_file(path, bytes)?;
    }
    directory.verify_exact_flat_regular_file_bytes(
        payload,
        maximum_member_bytes,
        maximum_payload_bytes,
    )?;
    let seal_inputs = payload
        .iter()
        .map(|(path, bytes)| {
            (
                path.clone(),
                sealed_performance_run::SealedInputFile {
                    bytes,
                    mode: 0o600,
                    link_count: 1,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let seal = sealed_performance_run::canonical_seal_bytes(
        lane_id,
        "matrix.json",
        report_schema,
        &seal_inputs,
    )?;
    directory.create_new_file(Path::new(SEALED_MATRIX_NAME), &seal)?;
    let mut sealed_bytes = payload.clone();
    sealed_bytes.insert(PathBuf::from(SEALED_MATRIX_NAME), &seal);
    directory.verify_exact_flat_regular_file_bytes(
        &sealed_bytes,
        maximum_member_bytes,
        maximum_payload_bytes
            .checked_add(sealed_performance_run::MAX_SEAL_BYTES)
            .ok_or("sealed matrix total bound overflowed")?,
    )?;
    sealed_performance_run::validate_canonical_seal_bytes(
        &seal,
        lane_id,
        "matrix.json",
        report_schema,
        &seal_inputs,
    )?;
    directory.sync_root_and_parent()?;
    Ok(())
}

#[cfg(test)]
fn validate_owned_sealed_directory(
    directory: &ClosedPrivateDirectory,
    expected_payload: &BTreeSet<PathBuf>,
    lane_id: &str,
    report_schema: &str,
    maximum_member_bytes: u64,
    maximum_payload_bytes: u64,
) -> Result<(), String> {
    let mut expected = expected_payload.clone();
    expected.insert(PathBuf::from(SEALED_MATRIX_NAME));
    let files = directory.read_exact_flat_regular_files(
        &expected,
        maximum_member_bytes,
        maximum_payload_bytes
            .checked_add(sealed_performance_run::MAX_SEAL_BYTES)
            .ok_or("sealed matrix total bound overflowed")?,
    )?;
    let seal_inputs = files
        .iter()
        .filter(|(path, _)| path.as_path() != Path::new(SEALED_MATRIX_NAME))
        .map(|(path, file)| {
            (
                path.clone(),
                sealed_performance_run::SealedInputFile {
                    bytes: &file.bytes,
                    mode: file.mode,
                    link_count: file.link_count,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    sealed_performance_run::validate_canonical_seal_bytes(
        &files
            .get(Path::new(SEALED_MATRIX_NAME))
            .ok_or("sealed directory omits its marker")?
            .bytes,
        lane_id,
        "matrix.json",
        report_schema,
        &seal_inputs,
    )?;
    directory.sync_root_and_parent()
}

fn validate_semantically_sealed_directory(
    kind: LaneKind,
    directory: &ClosedPrivateDirectory,
    expected: &BTreeSet<PathBuf>,
    rows: &[PerformanceFixtureSelectionV02],
    binding: &AuditBinding<'_>,
) -> Result<(), String> {
    let mut sealed = expected.clone();
    sealed.insert(PathBuf::from(SEALED_MATRIX_NAME));
    let files = directory.read_exact_flat_regular_files(
        &sealed,
        MAX_SEALED_MATRIX_MEMBER_BYTES,
        MAX_SEALED_MATRIX_TOTAL_BYTES
            .checked_add(sealed_performance_run::MAX_SEAL_BYTES)
            .ok_or("sealed matrix total bound overflowed")?,
    )?;
    let payload = files
        .iter()
        .filter(|(path, _)| path.as_path() != Path::new(SEALED_MATRIX_NAME))
        .map(|(path, file)| (path.clone(), file))
        .collect::<BTreeMap<_, _>>();
    validate_semantic_file_refs(kind, &payload, rows, binding)?;
    let seal_inputs = payload
        .iter()
        .map(|(path, file)| {
            (
                path.clone(),
                sealed_performance_run::SealedInputFile {
                    bytes: &file.bytes,
                    mode: file.mode,
                    link_count: file.link_count,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    sealed_performance_run::validate_canonical_seal_bytes(
        &files
            .get(Path::new(SEALED_MATRIX_NAME))
            .ok_or("sealed directory omits its marker")?
            .bytes,
        kind.lane_id(),
        "matrix.json",
        kind.matrix_schema(),
        &seal_inputs,
    )?;
    directory.sync_root_and_parent()
}

fn validate_semantic_file_refs(
    kind: LaneKind,
    files: &BTreeMap<PathBuf, &SealedRegularFile>,
    rows: &[PerformanceFixtureSelectionV02],
    binding: &AuditBinding<'_>,
) -> Result<(), String> {
    let references = files
        .iter()
        .map(|(path, file)| (path.clone(), file.bytes.as_slice()))
        .collect::<BTreeMap<_, _>>();
    validate_semantic_byte_refs(kind, &references, rows, binding)
}

fn validate_semantic_byte_refs(
    kind: LaneKind,
    files: &BTreeMap<PathBuf, &[u8]>,
    rows: &[PerformanceFixtureSelectionV02],
    binding: &AuditBinding<'_>,
) -> Result<(), String> {
    let expected = snap_vmsp_controller::expected_payload_catalog(kind, rows)?;
    if files.keys().cloned().collect::<BTreeSet<_>>() != expected {
        return Err("SNAP/VMSP semantic validator received the wrong exact catalog".to_owned());
    }
    validate_semantic_audit_member_hashes(
        files,
        [
            (Path::new(".fixture-manifest.json"), binding.manifest_sha256),
            (
                Path::new(".measurement-baseline.json"),
                binding.baseline_sha256,
            ),
            (Path::new(".fixture-oracle.tsv"), binding.oracle_sha256),
            (Path::new(".benchmark-executable"), binding.benchmark_sha256),
            (
                Path::new(".measure-process-executable"),
                binding.manager_sha256,
            ),
        ],
    )?;
    let manifest_bytes = files[Path::new(".fixture-manifest.json")];
    let manifest_source = std::str::from_utf8(manifest_bytes).map_err(display_error)?;
    let manifest = validate_checked_performance_fixture_selection_v02(manifest_source)
        .map_err(display_error)?;
    if manifest.scenarios != rows {
        return Err("sealed fixture manifest differs from the selected manifest".to_owned());
    }
    let executions = snap_vmsp_controller::execution_catalog(kind, rows)?;
    let working_budget = Arc::new(ControllerBudget::new(MAX_CONTROLLER_WORKING_BYTES));
    let mut completed = Vec::with_capacity(executions.len());
    for execution in &executions {
        if !files[&execution.stderr_name()].is_empty() {
            return Err(format!(
                "sealed successful execution {} has nonempty stderr",
                execution.ordinal
            ));
        }
        let parse_reservation = working_budget.reserve(
            MAX_COMPLETED_VALIDATION_WORKING_BYTES,
            "sealed completed-record parser working set",
        )?;
        let record = snap_vmsp_controller::validate_completed_against_raw(
            kind,
            execution,
            files[&execution.raw_name()],
            files[&execution.completed_name()],
            rows,
            files[Path::new(".measurement-baseline.json")],
            files[Path::new(".fixture-oracle.tsv")],
            binding,
        )?;
        parse_reservation.retain(record.retained_bytes()?, "sealed completed record")?;
        completed.push(record);
    }
    let matrix_reservation = working_budget.reserve(
        2 * MAX_JSON_OPERATION_WORKING_BYTES,
        "sealed matrix validation working set",
    )?;
    snap_vmsp_controller::validate_matrix(
        kind,
        files[Path::new("matrix.json")],
        &executions,
        &completed,
        rows,
        binding,
    )?;
    drop(matrix_reservation);
    if files[Path::new(".manifest-order.json")]
        != snap_vmsp_controller::manifest_order_json(kind, rows)
    {
        return Err("sealed manifest-order member is not derived from the manifest".to_owned());
    }
    Ok(())
}

fn validate_semantic_audit_member_hashes<const N: usize>(
    files: &BTreeMap<PathBuf, &[u8]>,
    expected: [(&Path, &str); N],
) -> Result<(), String> {
    for (path, expected_bytes) in expected {
        let observed = snap_vmsp_controller::sha256(
            files
                .get(path)
                .copied()
                .ok_or_else(|| format!("semantic catalog omits {}", path.display()))?,
        );
        if observed != expected_bytes {
            return Err(format!(
                "semantic audit member {} hash mismatch",
                path.display()
            ));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_existing_snap_vmsp_sealed_run(
    kind: LaneKind,
    manager: Vec<u8>,
    manifest_path: &Path,
    baseline_path: &Path,
    oracle_path: &Path,
    benchmark_path: &Path,
    source_identity: &str,
    output: &Path,
) -> Result<(), String> {
    if !output.is_absolute() || !valid_source_identity(source_identity) {
        return Err("sealed SNAP/VMSP validation arguments are invalid".to_owned());
    }
    let budget = Arc::new(ControllerBudget::new(MAX_SEALED_MATRIX_TOTAL_BYTES));
    budget.charge(
        u64::try_from(manager.capacity()).map_err(display_error)?,
        "manager audit executable allocation",
    )?;
    let working_budget = Arc::new(ControllerBudget::new(MAX_CONTROLLER_WORKING_BYTES));
    let snapshots = snapshot_lane_inputs(
        kind,
        manager,
        manifest_path,
        baseline_path,
        oracle_path,
        benchmark_path,
        budget,
    )?;
    let manifest = validate_checked_performance_fixture_selection_v02(
        std::str::from_utf8(&snapshots.manifest).map_err(display_error)?,
    )
    .map_err(display_error)?;
    let whole_input_reservation = working_budget.reserve(
        MAX_JSON_OPERATION_WORKING_BYTES,
        "whole sealed-input validation working set",
    )?;
    snap_vmsp_controller::validate_whole_inputs(
        kind,
        &manifest.scenarios,
        &snapshots.baseline,
        &snapshots.oracle,
    )?;
    drop(whole_input_reservation);
    let binding_storage = manager_audit_binding(kind, source_identity, &snapshots)?;
    let expected = snap_vmsp_controller::expected_payload_catalog(kind, &manifest.scenarios)?;
    // Independent consumption needs only the closed build/input digests and
    // the owned manifest rows. Release the manager, benchmark, and three input
    // snapshots before allocating the bounded sealed-file map so the two
    // complete audit populations never coexist.
    drop(snapshots);
    let binding = binding_storage.as_binding();
    let directory = ClosedPrivateDirectory::open_existing(output, "snap-vmsp-final")?;
    let result = validate_semantically_sealed_directory(
        kind,
        &directory,
        &expected,
        &manifest.scenarios,
        &binding,
    );
    directory.leave_in_place();
    result
}

fn run_measured_child(
    stdout: AttachedOutputFile,
    stderr: AttachedOutputFile,
    executable: String,
    command_arguments: Vec<String>,
) -> Result<(), String> {
    let started = Instant::now();
    let mut child = Command::new(executable)
        .args(command_arguments)
        .stdout(Stdio::from(
            stdout.try_clone_file().map_err(|error| error.to_string())?,
        ))
        .stderr(Stdio::from(
            stderr.try_clone_file().map_err(|error| error.to_string())?,
        ))
        .spawn()
        .map_err(|error| format!("spawn measured command: {error}"))?;
    let child_pid = i32::try_from(child.id()).map_err(|_| "child PID exceeds pid_t".to_owned())?;
    let (wait_status, usage) =
        wait_for_child(child_pid).map_err(|error| format!("wait for measured command: {error}"))?;
    let elapsed = started.elapsed().as_secs_f64();
    let _ = child.try_wait();
    stdout.sync_all().map_err(|error| error.to_string())?;
    stderr.sync_all().map_err(|error| error.to_string())?;

    let exit_code = decoded_exit_code(wait_status);
    let peak_rss_kib = peak_rss_kib(&usage)?;
    println!("{elapsed:.9}\t{peak_rss_kib}\t{exit_code}");
    Ok(())
}

/// Test-only wrapper for the production budgeted capture supervisor. Production
/// lanes accept only operator-selected, build-closure-bound benchmark bytes;
/// process supervision is a robustness boundary, not an OS sandbox.
#[cfg(test)]
fn run_measured_child_captured_with_timeout(
    executable: &DetachedExecutable,
    command_arguments: Vec<String>,
    maximum_stdout_bytes: u64,
    maximum_stderr_bytes: u64,
    child_timeout: Duration,
) -> Result<(String, Vec<u8>, Vec<u8>), String> {
    use std::os::unix::process::CommandExt as _;

    let started = Instant::now();
    let controller_tmpdir = validated_controller_tmpdir()?;
    let executable_fd = executable.try_clone_file()?;
    let executable_raw_fd = std::os::fd::AsRawFd::as_raw_fd(&executable_fd);
    let executable_path = executable.execution_path(executable_raw_fd)?;
    let mut command = Command::new(executable_path);
    command
        .args(command_arguments)
        .env_clear()
        .env("TMPDIR", controller_tmpdir)
        .env(
            "NPA_BENCH_EXECUTABLE_AUDIT_FD",
            executable_raw_fd.to_string(),
        )
        .env("NPA_BENCH_EXECUTABLE_SHA256", executable.sha256())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    // SAFETY: fcntl and setpgid are async-signal-safe. The fd is a private
    // duplicate retained solely so the child can exec the already-verified
    // inode (anonymous on Linux and privately named on macOS).
    unsafe {
        command.pre_exec(move || {
            let flags = libc::fcntl(executable_raw_fd, libc::F_GETFD);
            if flags < 0
                || libc::fcntl(executable_raw_fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) != 0
            {
                return Err(io::Error::last_os_error());
            }
            if libc::setpgid(0, 0) == 0 {
                Ok(())
            } else {
                Err(io::Error::last_os_error())
            }
        });
    }
    let mut child = command
        .spawn()
        .map_err(|error| format!("spawn measured command: {error}"))?;
    let child_pid = i32::try_from(child.id()).map_err(|_| "child PID exceeds pid_t".to_owned())?;
    let stdout_pipe = child
        .stdout
        .take()
        .ok_or("measured child has no stdout pipe")?;
    let stderr_pipe = child
        .stderr
        .take()
        .ok_or("measured child has no stderr pipe")?;
    let stdout_limit = maximum_stdout_bytes
        .checked_add(1)
        .ok_or("measured stdout limit cannot be u64::MAX")?;
    let stderr_limit = maximum_stderr_bytes
        .checked_add(1)
        .ok_or("measured stderr limit cannot be u64::MAX")?;
    set_nonblocking(stdout_pipe.as_raw_fd(), "measured stdout")?;
    set_nonblocking(stderr_pipe.as_raw_fd(), "measured stderr")?;
    let direct_child_done = Arc::new(AtomicBool::new(false));
    let (capture_error_sender, capture_error_receiver) = mpsc::channel();
    let stdout_reader = spawn_bounded_capture_reader(
        stdout_pipe,
        stdout_limit,
        Arc::clone(&direct_child_done),
        capture_error_sender.clone(),
        "stdout",
    );
    let stderr_reader = spawn_bounded_capture_reader(
        stderr_pipe,
        stderr_limit,
        Arc::clone(&direct_child_done),
        capture_error_sender,
        "stderr",
    );
    let child_deadline = Instant::now()
        .checked_add(child_timeout)
        .ok_or("measured child deadline overflowed")?;
    let child_result =
        wait_for_child_with_deadline(child_pid, child_deadline, &capture_error_receiver);
    direct_child_done.store(true, Ordering::SeqCst);
    let stdout_result = stdout_reader
        .join()
        .map_err(|_| "measured stdout reader panicked".to_owned())?;
    let stderr_result = stderr_reader
        .join()
        .map_err(|_| "measured stderr reader panicked".to_owned())?;
    if let Err(error) = stdout_result.as_ref() {
        return Err(format!("read measured stdout: {error}"));
    }
    if let Err(error) = stderr_result.as_ref() {
        return Err(format!("read measured stderr: {error}"));
    }
    let stdout = stdout_result?;
    let stderr = stderr_result?;
    let (exit_code, usage) = child_result?;
    if u64::try_from(stdout.len()).map_err(|error| error.to_string())? > maximum_stdout_bytes
        || u64::try_from(stderr.len()).map_err(|error| error.to_string())? > maximum_stderr_bytes
    {
        return Err("measured child output exceeds its byte limit".to_owned());
    }
    let elapsed = started.elapsed().as_secs_f64();
    let peak_rss_kib = peak_rss_kib(&usage)?;
    executable.verify()?;
    Ok((
        format!("{elapsed:.9}\t{peak_rss_kib}\t{exit_code}"),
        stdout,
        stderr,
    ))
}

fn query_benchmark_build_descriptor(
    kind: LaneKind,
    executable: &DetachedExecutable,
) -> Result<BenchmarkBuildDescriptor, String> {
    let budget = Arc::new(ControllerBudget::new(2 * 1024 * 1024));
    let working_budget = Arc::new(ControllerBudget::new(2 * 1024 * 1024));
    let (measurement, stdout, stderr) = run_measured_child_captured_budgeted_with_timeout(
        executable,
        vec!["--npa-build-descriptor".to_owned()],
        1024 * 1024,
        64 * 1024,
        budget,
        working_budget,
        Duration::from_secs(30),
    )?;
    let (_, exit) = parse_measurement_line(&measurement)?;
    if exit != 0 || !stderr.is_empty() {
        return Err(format!(
            "benchmark build-descriptor query failed its closed protocol (exit {exit}, stdout {:?}, stderr {:?})",
            String::from_utf8_lossy(stdout.as_slice()),
            String::from_utf8_lossy(stderr.as_slice())
        ));
    }
    let value = OwnedJson::parse_canonical_line(stdout.as_slice(), "benchmark build descriptor")?;
    value.exact_object(
        &[
            "schema",
            "lane_id",
            "source_identity",
            "cargo_lock_sha256",
            "cargo_profile",
            "target",
            "features",
            "rustc_vv",
            "rustflags",
            "harness_source_sha256",
            "source_set_sha256",
            "fixture_parser_source_sha256",
            "measure_process_source_sha256",
        ],
        "benchmark build descriptor",
    )?;
    let text = |name| {
        value
            .field(name, "benchmark build descriptor")?
            .text(name)
            .map(str::to_owned)
    };
    if text("schema")? != "npa.performance.benchmark-build.v1" || text("lane_id")? != kind.lane_id()
    {
        return Err("benchmark build descriptor schema or lane mismatch".to_owned());
    }
    let features = value
        .field("features", "benchmark build descriptor")?
        .array("benchmark build features")?
        .iter()
        .map(|feature| feature.text("benchmark feature").map(str::to_owned))
        .collect::<Result<Vec<_>, _>>()?;
    if features.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err("benchmark build features are duplicate or unordered".to_owned());
    }
    let fixture_parser_source_sha256 =
        match value.field("fixture_parser_source_sha256", "benchmark build descriptor")? {
            OwnedJson::Null => None,
            field => Some(field.text("fixture parser source hash")?.to_owned()),
        };
    Ok(BenchmarkBuildDescriptor {
        source_identity: text("source_identity")?,
        cargo_lock_sha256: text("cargo_lock_sha256")?,
        cargo_profile: text("cargo_profile")?,
        target: text("target")?,
        features: features.join(","),
        rustc_vv: text("rustc_vv")?,
        rustflags: text("rustflags")?,
        harness_source_sha256: text("harness_source_sha256")?,
        source_set_sha256: text("source_set_sha256")?,
        fixture_parser_source_sha256,
        measure_process_source_sha256: text("measure_process_source_sha256")?,
    })
}

#[cfg(test)]
fn query_real_benchmark_build_descriptor_for_test(
    kind: LaneKind,
    path: &Path,
) -> Result<BenchmarkBuildDescriptor, String> {
    let executable = detached_executable_snapshot(
        path,
        MAX_BENCHMARK_EXECUTABLE_BYTES,
        "real descriptor-exec benchmark test",
    )?;
    query_benchmark_build_descriptor(kind, &executable)
}

fn set_nonblocking(descriptor: RawFd, label: &str) -> Result<(), String> {
    let flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
    if flags < 0 || unsafe { libc::fcntl(descriptor, libc::F_SETFL, flags | libc::O_NONBLOCK) } != 0
    {
        return Err(format!(
            "set {label} nonblocking: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(test)]
fn spawn_bounded_capture_reader<R>(
    mut reader: R,
    read_limit: u64,
    direct_child_done: Arc<AtomicBool>,
    capture_error_sender: mpsc::Sender<String>,
    label: &'static str,
) -> std::thread::JoinHandle<Result<Vec<u8>, String>>
where
    R: io::Read + Send + 'static,
{
    std::thread::spawn(move || {
        let result = (|| {
            let maximum = read_limit
                .checked_sub(1)
                .ok_or_else(|| format!("measured {label} limit must be positive"))?;
            let mut bytes = Vec::new();
            let mut buffer = [0_u8; 16 * 1024];
            let mut drain_deadline = None;
            loop {
                match reader.read(&mut buffer) {
                    Ok(0) => return Ok(bytes),
                    Ok(read) => {
                        let next = u64::try_from(bytes.len())
                            .map_err(|error| error.to_string())?
                            .checked_add(u64::try_from(read).map_err(|error| error.to_string())?)
                            .ok_or_else(|| format!("measured {label} size overflowed"))?;
                        if next > maximum {
                            return Err(format!("measured {label} exceeds its byte limit"));
                        }
                        bytes.extend_from_slice(&buffer[..read]);
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        if direct_child_done.load(Ordering::SeqCst) {
                            let deadline = *drain_deadline
                                .get_or_insert_with(|| Instant::now() + CAPTURE_DRAIN_TIMEOUT);
                            if Instant::now() >= deadline {
                                return Err(format!(
                                "measured {label} pipe did not reach EOF after the direct child exited"
                            ));
                            }
                        }
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => return Err(format!("read measured {label}: {error}")),
                }
            }
        })();
        if let Err(error) = &result {
            let _ = capture_error_sender.send(error.clone());
        }
        result
    })
}

fn spawn_budgeted_capture_reader<R>(
    mut reader: R,
    member_maximum: u64,
    budget: Arc<ControllerBudget>,
    working_budget: Arc<ControllerBudget>,
    direct_child_done: Arc<AtomicBool>,
    capture_error_sender: mpsc::Sender<String>,
    label: &'static str,
) -> std::thread::JoinHandle<Result<BudgetedBytes, String>>
where
    R: io::Read + Send + 'static,
{
    std::thread::spawn(move || {
        let result = (|| {
            let mut chunks =
                BudgetedCaptureChunks::new(member_maximum, budget, working_budget, label)?;
            let mut buffer = [0_u8; CAPTURE_CHUNK_BYTES];
            let mut drain_deadline = None;
            loop {
                match reader.read(&mut buffer) {
                    Ok(0) => return chunks.into_budgeted_bytes(label),
                    Ok(read) => {
                        chunks.push(&buffer[..read], member_maximum, label)?;
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        if direct_child_done.load(Ordering::SeqCst) {
                            let deadline = *drain_deadline.get_or_insert_with(|| {
                                Instant::now()
                                    .checked_add(CAPTURE_DRAIN_TIMEOUT)
                                    .unwrap_or_else(Instant::now)
                            });
                            if Instant::now() >= deadline {
                                return Err(format!(
                                    "measured {label} pipe did not reach EOF after the direct child exited"
                                ));
                            }
                        }
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => return Err(format!("read measured {label}: {error}")),
                }
            }
        })();
        if let Err(error) = &result {
            let _ = capture_error_sender.send(error.clone());
        }
        result
    })
}

fn run_measured_child_captured_budgeted(
    executable: &DetachedExecutable,
    command_arguments: Vec<String>,
    maximum_stdout_bytes: u64,
    maximum_stderr_bytes: u64,
    budget: Arc<ControllerBudget>,
    working_budget: Arc<ControllerBudget>,
) -> Result<(String, BudgetedBytes, BudgetedBytes), String> {
    run_measured_child_captured_budgeted_with_timeout(
        executable,
        command_arguments,
        maximum_stdout_bytes,
        maximum_stderr_bytes,
        budget,
        working_budget,
        MEASURED_CHILD_TIMEOUT,
    )
}

fn run_measured_child_captured_budgeted_with_timeout(
    executable: &DetachedExecutable,
    command_arguments: Vec<String>,
    maximum_stdout_bytes: u64,
    maximum_stderr_bytes: u64,
    budget: Arc<ControllerBudget>,
    working_budget: Arc<ControllerBudget>,
    child_timeout: Duration,
) -> Result<(String, BudgetedBytes, BudgetedBytes), String> {
    use std::os::unix::process::CommandExt as _;

    let started = Instant::now();
    let controller_tmpdir = validated_controller_tmpdir()?;
    let executable_fd = executable.try_clone_file()?;
    let executable_raw_fd = executable_fd.as_raw_fd();
    let executable_path = executable.execution_path(executable_raw_fd)?;
    let mut command = Command::new(executable_path);
    command
        .args(command_arguments)
        .env_clear()
        .env("TMPDIR", controller_tmpdir)
        .env(
            "NPA_BENCH_EXECUTABLE_AUDIT_FD",
            executable_raw_fd.to_string(),
        )
        .env("NPA_BENCH_EXECUTABLE_SHA256", executable.sha256())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    unsafe {
        command.pre_exec(move || {
            let flags = libc::fcntl(executable_raw_fd, libc::F_GETFD);
            if flags < 0
                || libc::fcntl(executable_raw_fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) != 0
            {
                return Err(io::Error::last_os_error());
            }
            if libc::setpgid(0, 0) == 0 {
                Ok(())
            } else {
                Err(io::Error::last_os_error())
            }
        });
    }
    let mut child = command
        .spawn()
        .map_err(|error| format!("spawn measured command: {error}"))?;
    let child_pid = i32::try_from(child.id()).map_err(|_| "child PID exceeds pid_t".to_owned())?;
    let stdout_pipe = child.stdout.take().ok_or("measured child has no stdout")?;
    let stderr_pipe = child.stderr.take().ok_or("measured child has no stderr")?;
    set_nonblocking(stdout_pipe.as_raw_fd(), "measured stdout")?;
    set_nonblocking(stderr_pipe.as_raw_fd(), "measured stderr")?;
    let direct_child_done = Arc::new(AtomicBool::new(false));
    let (capture_error_sender, capture_error_receiver) = mpsc::channel();
    let stdout_reader = spawn_budgeted_capture_reader(
        stdout_pipe,
        maximum_stdout_bytes,
        Arc::clone(&budget),
        Arc::clone(&working_budget),
        Arc::clone(&direct_child_done),
        capture_error_sender.clone(),
        "stdout",
    );
    let stderr_reader = spawn_budgeted_capture_reader(
        stderr_pipe,
        maximum_stderr_bytes,
        budget,
        working_budget,
        Arc::clone(&direct_child_done),
        capture_error_sender,
        "stderr",
    );
    let deadline = Instant::now()
        .checked_add(child_timeout)
        .ok_or("measured child deadline overflowed")?;
    let child_result = wait_for_child_with_deadline(child_pid, deadline, &capture_error_receiver);
    direct_child_done.store(true, Ordering::SeqCst);
    let stdout_result = stdout_reader
        .join()
        .map_err(|_| "measured stdout reader panicked".to_owned())?;
    let stderr_result = stderr_reader
        .join()
        .map_err(|_| "measured stderr reader panicked".to_owned())?;
    let stdout = stdout_result?;
    let stderr = stderr_result?;
    let (exit_code, usage) = child_result?;
    executable.verify()?;
    Ok((
        format!(
            "{:.9}\t{}\t{}",
            started.elapsed().as_secs_f64(),
            peak_rss_kib(&usage)?,
            exit_code
        ),
        stdout,
        stderr,
    ))
}

fn wait_for_child(pid: libc::pid_t) -> io::Result<(libc::c_int, libc::rusage)> {
    let mut wait_status = 0;
    let mut usage = MaybeUninit::<libc::rusage>::zeroed();
    loop {
        // SAFETY: `wait_status` and `usage` are valid writable objects, `pid`
        // is the child just spawned above, and no other code waits for it.
        let waited = unsafe { libc::wait4(pid, &mut wait_status, 0, usage.as_mut_ptr()) };
        if waited == pid {
            // SAFETY: a successful wait4 call initializes the complete rusage.
            return Ok((wait_status, unsafe { usage.assume_init() }));
        }
        if waited == -1 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
    }
}

fn wait_for_child_with_deadline(
    pid: libc::pid_t,
    deadline: Instant,
    capture_errors: &mpsc::Receiver<String>,
) -> Result<(libc::c_int, libc::rusage), String> {
    loop {
        if let Ok(error) = capture_errors.try_recv() {
            terminate_and_reap(pid)?;
            return Err(format!("measured child capture failed: {error}"));
        }
        let mut info = MaybeUninit::<libc::siginfo_t>::zeroed();
        // WNOWAIT observes the terminal state but keeps the direct child as a
        // zombie. Its PID/PGID therefore cannot be reused before the retained
        // group is signaled and the final wait4 reaps it.
        let waited = unsafe {
            libc::waitid(
                libc::P_PID,
                u32::try_from(pid).map_err(display_error)?,
                info.as_mut_ptr(),
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if waited == 0 {
            let info = unsafe { info.assume_init() };
            if unsafe { info.si_pid() } == pid {
                let observed_exit_code = decoded_siginfo_exit_code(&info)?;
                signal_retained_process_group(pid)?;
                let (_, usage) = wait_for_child(pid)
                    .map_err(|error| format!("reap measured command: {error}"))?;
                return Ok((observed_exit_code, usage));
            }
        } else {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(format!("wait for measured command: {error}"));
        }
        if Instant::now() >= deadline {
            terminate_and_reap(pid)?;
            return Err("measured child exceeded the closed execution deadline".to_owned());
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn signal_retained_process_group(pid: libc::pid_t) -> Result<(), String> {
    let killed = unsafe { libc::kill(-pid, libc::SIGKILL) };
    if killed != 0 {
        let error = io::Error::last_os_error();
        // Darwin reports EPERM when the retained group contains only its
        // already-terminal zombie leader. WNOWAIT still anchors that numeric
        // PID/PGID until the following wait4, and successful pipe EOF remains
        // mandatory, so this case has no live group member left to signal.
        #[cfg(target_os = "macos")]
        let terminal_group_absent = error.raw_os_error() == Some(libc::EPERM);
        #[cfg(not(target_os = "macos"))]
        let terminal_group_absent = false;
        if error.raw_os_error() != Some(libc::ESRCH) && !terminal_group_absent {
            return Err(format!("terminate measured process group: {error}"));
        }
    }
    Ok(())
}

fn decoded_siginfo_exit_code(info: &libc::siginfo_t) -> Result<i32, String> {
    let status = unsafe { info.si_status() };
    match info.si_code {
        libc::CLD_EXITED => Ok(status),
        libc::CLD_KILLED | libc::CLD_DUMPED => Ok(128 + status),
        _ => Err("measured child reported a nonterminal wait status".to_owned()),
    }
}

fn terminate_and_reap(pid: libc::pid_t) -> Result<(), String> {
    // Kill both the process group and the direct PID. The second operation is
    // required even if the child changed its process-group membership.
    for target in [-pid, pid] {
        let result = unsafe { libc::kill(target, libc::SIGKILL) };
        if result != 0 {
            let error = io::Error::last_os_error();
            if error.raw_os_error() != Some(libc::ESRCH) {
                return Err(format!("terminate measured child {target}: {error}"));
            }
        }
    }
    let mut wait_status = 0;
    loop {
        let waited = unsafe { libc::waitpid(pid, &mut wait_status, 0) };
        if waited == pid {
            return Ok(());
        }
        if waited == -1 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            if error.raw_os_error() == Some(libc::ECHILD) {
                return Ok(());
            }
            return Err(format!("reap measured child: {error}"));
        }
    }
}

fn decoded_exit_code(wait_status: libc::c_int) -> i32 {
    if libc::WIFEXITED(wait_status) {
        libc::WEXITSTATUS(wait_status)
    } else if libc::WIFSIGNALED(wait_status) {
        128 + libc::WTERMSIG(wait_status)
    } else {
        255
    }
}

fn peak_rss_kib(usage: &libc::rusage) -> Result<u64, String> {
    let peak = u64::try_from(usage.ru_maxrss).map_err(|_| "negative peak RSS".to_owned())?;
    #[cfg(target_os = "macos")]
    {
        Ok(peak.saturating_add(1023) / 1024)
    }
    #[cfg(not(target_os = "macos"))]
    {
        Ok(peak)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::fd::FromRawFd as _;

    fn private_test_root(label: &str) -> PathBuf {
        let parent = env::temp_dir().canonicalize().unwrap();
        let root = parent.join(format!(
            "npa-measure-process-{label}-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir(&root).unwrap();
        root
    }

    #[test]
    fn measure_process_outputs_are_create_new() {
        let root = private_test_root("create-new");
        let path = root.join("result");
        drop(create_new_absolute_file(&path, "output").unwrap());
        fs::write(&path, b"sentinel").unwrap();
        assert!(create_new_absolute_file(&path, "output").is_err());
        assert_eq!(fs::read(&path).unwrap(), b"sentinel");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn measure_process_outputs_reject_relative_and_parent_components() {
        let root = private_test_root("normalized");
        assert!(create_new_absolute_file(Path::new("relative-output"), "output").is_err());
        let noncanonical = root.join("child").join("..").join("result");
        fs::create_dir(root.join("child")).unwrap();
        assert!(create_new_absolute_file(&noncanonical, "output").is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn measure_process_outputs_reject_symlink_parent_and_dangling_leaf() {
        use std::os::unix::fs::symlink;

        let root = private_test_root("symlink");
        let real_parent = root.join("real");
        let link_parent = root.join("link");
        fs::create_dir(&real_parent).unwrap();
        symlink(&real_parent, &link_parent).unwrap();
        assert!(create_new_absolute_file(&link_parent.join("result"), "output").is_err());

        let dangling = root.join("dangling");
        symlink(root.join("absent"), &dangling).unwrap();
        assert!(create_new_absolute_file(&dangling, "output").is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn measure_process_attached_output_rejects_path_replacement() {
        let root = private_test_root("parent-capability");
        let parent_path = root.join("parent");
        let relocated = root.join("relocated-parent");
        fs::create_dir(&parent_path).unwrap();
        let output = parent_path.join("result");
        let mut attached = create_new_absolute_file(&output, "output").unwrap();
        use std::io::Write as _;
        attached.write_all(b"original").unwrap();

        fs::rename(&parent_path, &relocated).unwrap();
        fs::create_dir(&parent_path).unwrap();
        fs::write(&output, b"replacement").unwrap();

        assert!(attached.sync_all().is_err());
        assert_eq!(fs::read(relocated.join("result")).unwrap(), b"original");
        assert_eq!(fs::read(&output).unwrap(), b"replacement");
        drop(attached);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn controller_budget_is_atomic_exact_and_overflow_closed() {
        let budget = Arc::new(ControllerBudget::new(9));
        let first = Arc::clone(&budget);
        let second = Arc::clone(&budget);
        let left = std::thread::spawn(move || first.charge(5, "left"));
        let right = std::thread::spawn(move || second.charge(5, "right"));
        let successes =
            usize::from(left.join().unwrap().is_ok()) + usize::from(right.join().unwrap().is_ok());
        assert_eq!(successes, 1);
        assert!(budget.charge(u64::MAX, "overflow").is_err());

        let exact = ControllerBudget::new(10);
        exact.charge(4, "prefix").unwrap();
        exact.charge(6, "suffix").unwrap();
        assert!(exact.charge(1, "one over").is_err());
    }

    #[test]
    fn exact_boxed_payload_retention_accepts_limit_and_rejects_one_over() {
        let budget = Arc::new(ControllerBudget::new(3));
        let exact = BudgetedBytes::retain_exact(
            vec![1, 2, 3].into_boxed_slice(),
            3,
            Arc::clone(&budget),
            "exact boxed test payload",
        )
        .unwrap();
        assert_eq!(exact.as_slice(), &[1, 2, 3]);
        assert_eq!(budget.used.load(Ordering::SeqCst), 3);
        drop(exact);
        assert_eq!(budget.used.load(Ordering::SeqCst), 0);

        assert!(BudgetedBytes::retain_exact(
            vec![1, 2, 3, 4].into_boxed_slice(),
            3,
            Arc::clone(&budget),
            "one-over boxed test payload",
        )
        .is_err());
        assert_eq!(budget.used.load(Ordering::SeqCst), 0);
    }

    #[cfg(unix)]
    #[test]
    fn snapshot_real_shaped_audit_hashes_are_tagged_before_destination_create() {
        let outer = private_test_root("snapshot-tagged-audit-precreate");
        let output = outer.join("final");
        let destination =
            prepare_new_absolute_private_directory(&output, "snap-vmsp-final").unwrap();
        let manifest = include_bytes!("../../../testdata/performance/fixtures/manifest.v0.2.json");
        let baseline =
            include_bytes!("../../../testdata/performance/baselines/measurements.v0.1.json");
        let oracle = include_bytes!("../../../testdata/performance/fixture-generator.v1.tsv");
        let benchmark = b"representative SNAP benchmark executable audit bytes".as_slice();
        let manager = b"representative SNAP manager executable audit bytes".as_slice();
        let files = BTreeMap::from([
            (PathBuf::from(".fixture-manifest.json"), manifest.as_slice()),
            (
                PathBuf::from(".measurement-baseline.json"),
                baseline.as_slice(),
            ),
            (PathBuf::from(".fixture-oracle.tsv"), oracle.as_slice()),
            (PathBuf::from(".benchmark-executable"), benchmark),
            (PathBuf::from(".measure-process-executable"), manager),
        ]);
        let manifest_hash = snap_vmsp_controller::sha256(manifest);
        let baseline_hash = snap_vmsp_controller::sha256(baseline);
        let oracle_hash = snap_vmsp_controller::sha256(oracle);
        let benchmark_hash = snap_vmsp_controller::sha256(benchmark);
        let benchmark_raw = snap_vmsp_controller::raw_sha256(benchmark);
        let manager_hash = snap_vmsp_controller::sha256(manager);
        let mut expected = [
            (Path::new(".fixture-manifest.json"), manifest_hash.as_str()),
            (
                Path::new(".measurement-baseline.json"),
                baseline_hash.as_str(),
            ),
            (Path::new(".fixture-oracle.tsv"), oracle_hash.as_str()),
            (Path::new(".benchmark-executable"), benchmark_hash.as_str()),
            (
                Path::new(".measure-process-executable"),
                manager_hash.as_str(),
            ),
        ];

        validate_semantic_audit_member_hashes(&files, expected).unwrap();
        assert_eq!(
            benchmark_hash.strip_prefix("sha256:"),
            Some(benchmark_raw.as_str())
        );
        expected[3].1 = benchmark_raw.as_str();
        let raw_error = validate_semantic_audit_member_hashes(&files, expected).unwrap_err();
        assert!(raw_error.contains(".benchmark-executable"));
        let double_tagged = format!("sha256:{benchmark_hash}");
        expected[3].1 = double_tagged.as_str();
        let tagged_error = validate_semantic_audit_member_hashes(&files, expected).unwrap_err();
        assert!(tagged_error.contains(".benchmark-executable"));
        assert!(!output.exists());
        destination.verify_absent().unwrap();
        drop(destination);
        fs::remove_dir(outer).unwrap();
    }

    #[test]
    fn retained_and_transient_controller_budgets_accept_exact_closed_peaks() {
        let retained = Arc::new(ControllerBudget::new(MAX_SEALED_MATRIX_TOTAL_BYTES));
        retained
            .charge(MAX_SEALED_MATRIX_TOTAL_BYTES, "exact retained payload")
            .unwrap();
        assert!(retained.charge(1, "retained one over").is_err());

        let transient = Arc::new(ControllerBudget::new(MAX_CONTROLLER_WORKING_BYTES));
        let population = transient
            .reserve(
                MAX_COMPLETED_VALIDATION_WORKING_BYTES,
                "exact parse working set",
            )
            .unwrap();
        population
            .retain(
                snap_vmsp_controller::MAX_SEMANTIC_STRUCTURE_BYTES,
                "retained parsed population",
            )
            .unwrap();
        let remaining = transient
            .reserve(
                MAX_COMPLETED_VALIDATION_WORKING_BYTES,
                "exact remaining working set",
            )
            .unwrap();
        assert!(transient.reserve(1, "transient one over").is_err());
        drop(remaining);
        transient.reserve(1, "released transient byte").unwrap();

        assert_eq!(
            snap_vmsp_controller::completed_record_byte_reservation(u64::MAX),
            Err("completed record byte reservation overflowed".to_owned())
        );
        assert!(snap_vmsp_controller::json_structure_reservation(
            snap_vmsp_controller::MAX_CANONICAL_JSON_BYTES
        )
        .is_ok());
        assert!(snap_vmsp_controller::json_structure_reservation(
            snap_vmsp_controller::MAX_CANONICAL_JSON_BYTES + 1
        )
        .is_err());
    }

    #[cfg(unix)]
    #[test]
    fn benchmark_snapshot_obeys_precharged_budget_under_low_address_space() {
        const CHILD_MODE: &str = "NPA_TEST_CONTROLLER_SNAPSHOT_LOW_ADDRESS_SPACE";
        const FILE_BYTES: usize = 12 * 1024 * 1024;

        if let Some(path) = env::var_os(CHILD_MODE) {
            let mut current = libc::rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut current) }, 0);
            // Leave enough headroom for the test executable and Rust runtime,
            // but not for repeated near-limit benchmark-sized copies.
            let requested = 256 * 1024 * 1024;
            let low_limit_active = requested <= current.rlim_max
                && unsafe {
                    libc::setrlimit(
                        libc::RLIMIT_AS,
                        &libc::rlimit {
                            rlim_cur: requested,
                            rlim_max: current.rlim_max,
                        },
                    )
                } == 0;
            #[cfg(target_os = "linux")]
            assert!(
                low_limit_active,
                "Linux must enforce the controller AS gate"
            );
            #[cfg(not(target_os = "linux"))]
            let _ = low_limit_active;

            let budget = Arc::new(ControllerBudget::new(68 * 1024 * 1024));
            budget
                .charge(4 * 1024 * 1024, "preexisting manager allocation")
                .unwrap();
            let snapshot =
                snapshot_budgeted_benchmark(Path::new(&path), Arc::clone(&budget)).unwrap();
            assert_eq!(snapshot.audit_bytes().len(), FILE_BYTES);
            snapshot.verify().unwrap();
            budget
                .charge(52 * 1024 * 1024, "exact remaining retained capacity")
                .unwrap();
            assert!(budget
                .charge(1, "one byte beyond the closed budget")
                .is_err());
            return;
        }

        let root = private_test_root("snapshot-low-address-space");
        let executable = root.join("benchmark");
        let file = fs::File::create(&executable).unwrap();
        file.set_len(u64::try_from(FILE_BYTES).unwrap()).unwrap();
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
        let test_name = std::thread::current().name().unwrap().to_owned();
        let status = Command::new(env::current_exe().unwrap())
            .args(["--exact", &test_name, "--nocapture"])
            .env(CHILD_MODE, &executable)
            .status()
            .unwrap();
        assert!(status.success());
        fs::remove_file(executable).unwrap();
        fs::remove_dir(root).unwrap();
    }

    #[test]
    fn benchmark_build_metadata_is_independently_closed() {
        let descriptor = BenchmarkBuildDescriptor {
            source_identity: "0".repeat(40),
            cargo_lock_sha256: "1".repeat(64),
            cargo_profile: "release".to_owned(),
            target: "aarch64-apple-darwin".to_owned(),
            features: "default".to_owned(),
            rustc_vv: "rustc 1.2.3\n".to_owned(),
            rustflags: "-Ctarget-cpu=apple-m1".to_owned(),
            harness_source_sha256: "2".repeat(64),
            source_set_sha256: "3".repeat(64),
            fixture_parser_source_sha256: None,
            measure_process_source_sha256: "4".repeat(64),
        };
        let expected = ExpectedBenchmarkBuildMetadata {
            target: "aarch64-apple-darwin",
            features: "default",
            rustc_vv: "rustc 1.2.3\n",
            rustflags: "-Ctarget-cpu=apple-m1",
        };
        validate_benchmark_build_metadata(&descriptor, &expected).unwrap();
        for changed in [
            ExpectedBenchmarkBuildMetadata {
                target: "x86_64-unknown-linux-gnu",
                ..expected
            },
            ExpectedBenchmarkBuildMetadata {
                features: "default,planning-benchmark",
                ..expected
            },
            ExpectedBenchmarkBuildMetadata {
                rustc_vv: "rustc 9.9.9\n",
                ..expected
            },
            ExpectedBenchmarkBuildMetadata {
                rustflags: "-Copt-level=1",
                ..expected
            },
        ] {
            assert!(validate_benchmark_build_metadata(&descriptor, &changed).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn manager_executable_bootstrap_hash_contract_is_raw_lowercase_sha256() {
        use std::os::unix::process::CommandExt as _;

        const CHILD_MODE: &str = "NPA_TEST_MANAGER_EXECUTABLE_HASH_CONTRACT";
        if let Some(mode) = env::var_os(CHILD_MODE) {
            match mode.to_str().unwrap() {
                "raw" => {
                    let expected = env::var("NPA_MANAGER_EXECUTABLE_SHA256").unwrap();
                    let bytes = consume_manager_executable().unwrap();
                    assert_eq!(snap_vmsp_controller::raw_sha256(&bytes), expected);
                }
                "prefixed" => {
                    let error = consume_manager_executable().unwrap_err();
                    assert!(error.contains("not raw lowercase SHA-256"));
                }
                _ => panic!("unknown manager executable hash contract mode"),
            }
            return;
        }

        let executable = detached_executable_snapshot(
            &env::current_exe().unwrap(),
            MAX_MANAGER_EXECUTABLE_BYTES,
            "manager hash-contract test executable",
        )
        .unwrap();
        let test_name = std::thread::current().name().unwrap().to_owned();
        for (mode, expected) in [
            ("raw", executable.sha256().to_owned()),
            ("prefixed", format!("sha256:{}", executable.sha256())),
        ] {
            let file = executable.try_clone_file().unwrap();
            let descriptor = file.as_raw_fd();
            let execution_path = executable.execution_path(descriptor).unwrap();
            let mut command = Command::new(execution_path);
            command
                .args(["--exact", &test_name, "--nocapture"])
                .env_clear()
                .env("TMPDIR", validated_controller_tmpdir().unwrap())
                .env(CHILD_MODE, mode)
                .env("NPA_MANAGER_EXECUTABLE_AUDIT_FD", descriptor.to_string())
                .env("NPA_MANAGER_EXECUTABLE_SHA256", expected);
            unsafe {
                command.pre_exec(move || {
                    let flags = libc::fcntl(descriptor, libc::F_GETFD);
                    if flags < 0
                        || libc::fcntl(descriptor, libc::F_SETFD, flags & !libc::FD_CLOEXEC) != 0
                    {
                        return Err(io::Error::last_os_error());
                    }
                    Ok(())
                });
            }
            assert!(command.status().unwrap().success());
        }
        executable.verify().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn real_snap_and_vmsp_benchmarks_support_detached_descriptor_exec() {
        let workspace = workspace_root().unwrap();
        let mut source_identity = None;
        for (kind, relative) in [
            (
                LaneKind::Snapshot,
                "target/debug/examples/bench_package_artifact_snapshot",
            ),
            (
                LaneKind::SharedPayload,
                "target/debug/examples/bench_shared_payload",
            ),
        ] {
            let path = workspace.join(relative);
            if !path.is_file() {
                continue;
            }
            let descriptor = query_real_benchmark_build_descriptor_for_test(kind, &path).unwrap();
            assert!(valid_source_identity(&descriptor.source_identity));
            assert_ne!(descriptor.source_identity, "unbound");
            if let Some(expected) = &source_identity {
                assert_eq!(&descriptor.source_identity, expected);
            } else {
                source_identity = Some(descriptor.source_identity.clone());
            }
            assert_eq!(descriptor.cargo_profile, "dev");
            assert_eq!(descriptor.target, env!("NPA_CLI_BUILD_TARGET"));
        }
    }

    #[cfg(unix)]
    #[test]
    fn measured_child_deadline_kills_and_reaps_direct_hang() {
        let executable =
            detached_executable_snapshot(Path::new("/bin/sh"), 16 * 1024 * 1024, "timeout runner")
                .unwrap();
        let started = Instant::now();
        let error = run_measured_child_captured_with_timeout(
            &executable,
            vec!["-c".to_owned(), "while :; do :; done".to_owned()],
            1024,
            1024,
            Duration::from_millis(100),
        )
        .unwrap_err();
        assert!(
            error.contains("deadline") || error.contains("spawn measured command"),
            "unexpected timeout result: {error}"
        );
        assert!(started.elapsed() < Duration::from_secs(3));
        executable.verify().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn measured_child_output_limit_interrupts_without_global_deadline() {
        let executable =
            detached_executable_snapshot(Path::new("/bin/sh"), 16 * 1024 * 1024, "flood runner")
                .unwrap();
        let started = Instant::now();
        let result = run_measured_child_captured_with_timeout(
            &executable,
            vec![
                "-c".to_owned(),
                "while :; do printf xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; done".to_owned(),
            ],
            128,
            128,
            Duration::from_secs(10),
        );
        match result {
            Err(error) => assert!(
                error.contains("byte limit")
                    || error.contains("capture failed")
                    || error.contains("spawn measured command"),
                "unexpected flood result: {error}"
            ),
            Ok((measurement, stdout, stderr)) => {
                let (_, exit_code) = parse_measurement_line(&measurement).unwrap();
                assert_ne!(exit_code, 0, "an over-limit child must not succeed");
                assert!(stdout.len() <= 128);
                assert!(stderr.len() <= 128);
            }
        }
        assert!(started.elapsed() < Duration::from_secs(3));
    }

    #[cfg(unix)]
    #[test]
    fn tiny_controller_round_trip_creates_final_only_after_quiescence_and_seals() {
        use std::os::unix::fs::PermissionsExt as _;

        struct WriteFailure;
        impl io::Write for WriteFailure {
            fn write(&mut self, _buffer: &[u8]) -> io::Result<usize> {
                Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "injected write failure",
                ))
            }

            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }

        struct FlushFailure;
        impl io::Write for FlushFailure {
            fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
                Ok(buffer.len())
            }

            fn flush(&mut self) -> io::Result<()> {
                Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "injected flush failure",
                ))
            }
        }

        let outer = private_test_root("tiny-sealed-round-trip");
        let output = outer.join("final");
        let destination =
            prepare_new_absolute_private_directory(&output, "snap-vmsp-final").unwrap();

        // Preparing the retained destination must not expose the future final
        // root to the measured phase. This dedicated executable stands in for
        // one quiescent trusted benchmark invocation while using the same
        // descriptor-exec and capture protocol as production.
        let runner_path = outer.join("tiny-runner.sh");
        fs::write(
            &runner_path,
            b"#!/bin/sh\nif test -e \"$1\"; then exit 91; fi\nprintf '{\"ok\":true}\\n'\n",
        )
        .unwrap();
        fs::set_permissions(&runner_path, fs::Permissions::from_mode(0o700)).unwrap();
        let benchmark = detached_executable_snapshot(&runner_path, 4096, "tiny runner").unwrap();
        let (measurement, stdout, stderr) = run_measured_child_captured_with_timeout(
            &benchmark,
            vec![output.to_string_lossy().into_owned()],
            1024,
            1024,
            Duration::from_secs(2),
        )
        .unwrap();
        assert_eq!(parse_measurement_line(&measurement).unwrap().1, 0);
        assert_eq!(stdout, b"{\"ok\":true}\n");
        assert!(stderr.is_empty());
        assert!(!output.exists());
        benchmark.verify().unwrap();

        let payload = BTreeMap::from([
            (PathBuf::from("audit.json"), stdout.as_slice()),
            (PathBuf::from("matrix.json"), b"{\"rows\":[]}\n".as_slice()),
        ]);

        for (suffix, mut failed_output) in [
            (
                "write-failure",
                Box::new(WriteFailure) as Box<dyn io::Write>,
            ),
            (
                "flush-failure",
                Box::new(FlushFailure) as Box<dyn io::Write>,
            ),
        ] {
            let rejected_output = outer.join(suffix);
            let rejected_destination = prepare_new_absolute_private_directory(
                &rejected_output,
                "snap-vmsp-final-rejected-output",
            )
            .unwrap();
            let result = write_controller_matrix_digest_then(
                &mut failed_output,
                payload[Path::new("matrix.json")],
                || rejected_destination.create(),
            );
            assert!(result.is_err());
            assert!(!rejected_output.exists());
        }

        let mut operational_stdout = Vec::new();
        let directory = write_controller_matrix_digest_then(
            &mut operational_stdout,
            payload[Path::new("matrix.json")],
            || destination.create(),
        )
        .unwrap();
        write_and_seal_owned_directory(
            &directory,
            &payload,
            "snapshot-test",
            "matrix.test.v1",
            1024,
            2048,
        )
        .unwrap();
        let expected = payload.keys().cloned().collect::<BTreeSet<_>>();
        validate_owned_sealed_directory(
            &directory,
            &expected,
            "snapshot-test",
            "matrix.test.v1",
            1024,
            2048,
        )
        .unwrap();
        assert!(output.join(SEALED_MATRIX_NAME).is_file());

        // Exercise the exact operational stdout bytes consumed by both
        // production shell wrappers. They were written and flushed before
        // destination creation, and no stdout operation follows the sealed
        // commit. A tagged digest would still make the wrapper report failure
        // after the final root exists.
        let operational_stdout = std::str::from_utf8(&operational_stdout).unwrap();
        assert_eq!(operational_stdout.len(), 65);
        assert!(operational_stdout.ends_with('\n'));
        assert!(operational_stdout[..64]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f')));
        assert_eq!(
            operational_stdout.trim_end(),
            snap_vmsp_controller::raw_sha256(payload[Path::new("matrix.json")])
        );
        assert_ne!(
            operational_stdout.trim_end(),
            snap_vmsp_controller::sha256(payload[Path::new("matrix.json")])
        );
        directory.leave_in_place();

        // Cleanup is deliberately only test-side after the controller has
        // released every retained capability; production preserves residues.
        fs::remove_file(output.join("audit.json")).unwrap();
        fs::remove_file(output.join("matrix.json")).unwrap();
        fs::remove_file(output.join(SEALED_MATRIX_NAME)).unwrap();
        fs::remove_dir(&output).unwrap();
        fs::remove_file(runner_path).unwrap();
        fs::remove_dir(outer).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn escaped_setsid_pipe_holder_fails_closed_before_final_creation() {
        let outer = private_test_root("setsid-pipe-holder");
        let output = outer.join("final");
        let destination =
            prepare_new_absolute_private_directory(&output, "snap-vmsp-final").unwrap();

        let mut stdout_descriptors = [0_i32; 2];
        let mut stderr_descriptors = [0_i32; 2];
        let mut survivor_pid_descriptors = [0_i32; 2];
        assert_eq!(unsafe { libc::pipe(stdout_descriptors.as_mut_ptr()) }, 0);
        assert_eq!(unsafe { libc::pipe(stderr_descriptors.as_mut_ptr()) }, 0);
        assert_eq!(
            unsafe { libc::pipe(survivor_pid_descriptors.as_mut_ptr()) },
            0
        );
        let direct = unsafe { libc::fork() };
        assert!(direct >= 0);
        if direct == 0 {
            unsafe {
                libc::close(stdout_descriptors[0]);
                libc::close(stderr_descriptors[0]);
                libc::close(survivor_pid_descriptors[0]);
                let _ = libc::setpgid(0, 0);
            }
            let survivor = unsafe { libc::fork() };
            if survivor == 0 {
                unsafe {
                    libc::close(survivor_pid_descriptors[1]);
                    let _ = libc::setsid();
                    libc::close(stderr_descriptors[1]);
                    // Retain stdout beyond the direct child lifetime.  The
                    // production drain deadline must reject this condition.
                    loop {
                        libc::pause();
                    }
                }
            }
            if survivor > 0 {
                let bytes = survivor.to_ne_bytes();
                let mut written = 0_usize;
                while written < bytes.len() {
                    let result = unsafe {
                        libc::write(
                            survivor_pid_descriptors[1],
                            bytes[written..].as_ptr().cast(),
                            bytes.len() - written,
                        )
                    };
                    if result <= 0 {
                        break;
                    }
                    written += usize::try_from(result).unwrap_or(0);
                }
            }
            unsafe {
                libc::close(survivor_pid_descriptors[1]);
                libc::close(stdout_descriptors[1]);
                libc::close(stderr_descriptors[1]);
                libc::_exit(if survivor < 0 { 1 } else { 0 });
            }
        }

        unsafe {
            libc::close(stdout_descriptors[1]);
            libc::close(stderr_descriptors[1]);
            libc::close(survivor_pid_descriptors[1]);
        }
        let mut survivor_pid_file = unsafe { fs::File::from_raw_fd(survivor_pid_descriptors[0]) };
        let mut survivor_pid_bytes = [0_u8; std::mem::size_of::<i32>()];
        use std::io::Read as _;
        survivor_pid_file
            .read_exact(&mut survivor_pid_bytes)
            .unwrap();
        let survivor_pid = i32::from_ne_bytes(survivor_pid_bytes);
        let stdout = unsafe { fs::File::from_raw_fd(stdout_descriptors[0]) };
        let stderr = unsafe { fs::File::from_raw_fd(stderr_descriptors[0]) };
        set_nonblocking(stdout.as_raw_fd(), "setsid stdout").unwrap();
        set_nonblocking(stderr.as_raw_fd(), "setsid stderr").unwrap();
        let direct_done = Arc::new(AtomicBool::new(false));
        let (errors, received_errors) = mpsc::channel();
        let stdout_reader = spawn_bounded_capture_reader(
            stdout,
            1024,
            Arc::clone(&direct_done),
            errors.clone(),
            "stdout",
        );
        let stderr_reader =
            spawn_bounded_capture_reader(stderr, 1024, Arc::clone(&direct_done), errors, "stderr");
        let deadline = Instant::now().checked_add(Duration::from_secs(1)).unwrap();
        let direct_result = wait_for_child_with_deadline(direct, deadline, &received_errors);
        direct_done.store(true, Ordering::SeqCst);
        let started = Instant::now();
        let stdout_result = stdout_reader.join().unwrap();
        let stderr_result = stderr_reader.join().unwrap();

        assert!(direct_result.is_ok());
        assert!(stdout_result
            .unwrap_err()
            .contains("pipe did not reach EOF"));
        assert!(stderr_result.unwrap().is_empty());
        assert!(started.elapsed() < Duration::from_secs(3));
        assert!(!output.exists());
        destination.verify_absent().unwrap();

        // The escaped helper is intentionally outside process-group
        // containment under the documented trusted-child boundary. Wait for
        // its exact PID to disappear instead of relying on a timing margin.
        // The helper is intentionally an orphan after setsid; kill its exact
        // PID once the production timeout contract has been observed so this
        // regression does not depend on a wall-clock sleep margin.
        let killed = unsafe { libc::kill(survivor_pid, libc::SIGKILL) };
        if killed != 0 {
            assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
        }
        assert!(!output.exists());
        fs::remove_dir(outer).unwrap();
    }
}
