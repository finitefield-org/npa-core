#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/runtime_source_set.rs"]
mod runtime_source_set;
#[path = "support/term_dag_performance.rs"]
mod term_dag_performance;

use std::{
    collections::BTreeSet,
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

use closed_private_tree::{
    create_new_absolute_file, read_absolute_regular_file, read_invocation_regular_file,
    AttachedExecutable, AttachedOutputFile, ClosedPrivateDirectory,
};
use npa_api::{JsonDocument, JsonMember, JsonValue};
use term_dag_performance::{CaseSpec, BASELINE_PATH, MANIFEST_PATH};

const MAX_DESCRIPTOR_BYTES: u64 = 4 * 1024 * 1024;
const MAX_REPORT_BYTES: u64 = 64 * 1024 * 1024;
const MAX_EXECUTABLE_BYTES: u64 = 512 * 1024 * 1024;
const MAX_CARGO_LOCK_BYTES: u64 = 32 * 1024 * 1024;

fn main() {
    if let Err(error) = run() {
        eprintln!("certificate term-DAG benchmark: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    if arguments == ["--help"] {
        println!("{}", usage());
        return Ok(());
    }
    if arguments == ["--print-canonical-manifest"] {
        print!("{}", term_dag_performance::render_manifest()?);
        return Ok(());
    }
    if arguments == ["--print-canonical-baseline"] {
        print!("{}", term_dag_performance::render_baseline()?);
        return Ok(());
    }
    let parsed = Arguments::parse(&arguments)?;
    match parsed.mode {
        Mode::ValidateManifest => {
            let source = read_utf8(&parsed.manifest)?;
            term_dag_performance::validate_manifest(&source)?;
            validate_optional_scenario(parsed.scenario.as_deref())
        }
        Mode::ValidateBaseline => {
            let source = read_utf8(&parsed.baseline)?;
            term_dag_performance::validate_baseline(&source)
        }
        Mode::ValidateAll | Mode::CheckDeterministic => {
            validate_pair(&parsed)?;
            if let Some(id) = parsed.scenario.as_deref() {
                validate_optional_scenario(Some(id))?;
                for case in term_dag_performance::cases()
                    .into_iter()
                    .filter(|case| case.scenario_id == id)
                {
                    execute_deterministic_case(&case)?;
                }
            }
            Ok(())
        }
        Mode::Child => run_child(&parsed),
        Mode::Controller => run_controller(&parsed),
        Mode::ValidateReport => run_report_validator(&parsed),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    ValidateManifest,
    ValidateBaseline,
    ValidateAll,
    CheckDeterministic,
    Child,
    Controller,
    ValidateReport,
}

#[derive(Clone, Debug)]
struct Arguments {
    mode: Mode,
    manifest: PathBuf,
    baseline: PathBuf,
    scenario: Option<String>,
    case_id: Option<String>,
    requested_jobs: Option<u64>,
    sample_index: Option<u64>,
    measure_process: Option<PathBuf>,
    output: Option<PathBuf>,
}

impl Arguments {
    fn parse(arguments: &[String]) -> Result<Self, String> {
        let mut mode = None;
        let mut manifest = None;
        let mut baseline = None;
        let mut scenario = None;
        let mut case_id = None;
        let mut requested_jobs = None;
        let mut sample_index = None;
        let mut measure_process = None;
        let mut output = None;
        let mut index = 0;
        while index < arguments.len() {
            let flag = arguments[index].as_str();
            if matches!(
                flag,
                "--validate-all"
                    | "--check-deterministic"
                    | "--child"
                    | "--controller"
                    | "--validate-report"
            ) {
                if mode.is_some() {
                    return Err("exactly one execution mode is required".to_owned());
                }
                mode = Some(match flag {
                    "--validate-all" => Mode::ValidateAll,
                    "--check-deterministic" => Mode::CheckDeterministic,
                    "--child" => Mode::Child,
                    "--controller" => Mode::Controller,
                    "--validate-report" => Mode::ValidateReport,
                    _ => return Err(format!("unknown execution mode {flag}")),
                });
                index += 1;
                continue;
            }
            let value = arguments.get(index + 1).ok_or_else(usage)?;
            match flag {
                "--validate-manifest-only" if mode.is_none() => {
                    mode = Some(Mode::ValidateManifest);
                    manifest = Some(PathBuf::from(value));
                }
                "--validate-baseline-only" if mode.is_none() => {
                    mode = Some(Mode::ValidateBaseline);
                    baseline = Some(PathBuf::from(value));
                }
                "--manifest" if manifest.is_none() => manifest = Some(PathBuf::from(value)),
                "--baseline" if baseline.is_none() => baseline = Some(PathBuf::from(value)),
                "--scenario" if scenario.is_none() => scenario = Some(value.clone()),
                "--case" if case_id.is_none() => case_id = Some(value.clone()),
                "--requested-jobs" if requested_jobs.is_none() => {
                    requested_jobs = Some(value.parse().map_err(|_| "invalid --requested-jobs")?)
                }
                "--sample-index" if sample_index.is_none() => {
                    sample_index = Some(value.parse().map_err(|_| "invalid --sample-index")?)
                }
                "--measure-process" if measure_process.is_none() => {
                    measure_process = Some(PathBuf::from(value))
                }
                "--output" if output.is_none() => output = Some(PathBuf::from(value)),
                option => {
                    return Err(format!(
                        "unknown or duplicate option: {option}\n{}",
                        usage()
                    ))
                }
            }
            index += 2;
        }
        let mode = mode.ok_or_else(usage)?;
        let manifest = manifest.unwrap_or_else(|| PathBuf::from(MANIFEST_PATH));
        let baseline = baseline.unwrap_or_else(|| PathBuf::from(BASELINE_PATH));
        match mode {
            Mode::ValidateManifest => {}
            Mode::ValidateBaseline => {}
            Mode::ValidateAll => {}
            Mode::CheckDeterministic => {
                if scenario.is_none() {
                    return Err("--check-deterministic requires --scenario".to_owned());
                }
            }
            Mode::Child => {
                if scenario.is_none()
                    || case_id.is_none()
                    || requested_jobs.is_none()
                    || sample_index.is_none()
                {
                    return Err(
                        "child mode requires scenario, case, requested-jobs, and sample-index"
                            .to_owned(),
                    );
                }
                if sample_index.unwrap_or(3) >= 3 {
                    return Err("child sample index must be 0, 1, or 2".to_owned());
                }
            }
            Mode::Controller => {
                if measure_process.is_none() || output.is_none() {
                    return Err(
                        "controller mode requires --measure-process and --output".to_owned()
                    );
                }
                validate_absolute_paths(
                    &manifest,
                    &baseline,
                    measure_process.as_deref(),
                    output.as_deref(),
                )?;
            }
            Mode::ValidateReport => {
                if measure_process.is_none() || output.is_none() {
                    return Err(
                        "validate-report mode requires --measure-process and --output".to_owned(),
                    );
                }
                validate_absolute_paths(
                    &manifest,
                    &baseline,
                    measure_process.as_deref(),
                    output.as_deref(),
                )?;
            }
        }
        Ok(Self {
            mode,
            manifest,
            baseline,
            scenario,
            case_id,
            requested_jobs,
            sample_index,
            measure_process,
            output,
        })
    }
}

fn validate_absolute_paths(
    manifest: &Path,
    baseline: &Path,
    measure_process: Option<&Path>,
    output: Option<&Path>,
) -> Result<(), String> {
    if !manifest.is_absolute()
        || !baseline.is_absolute()
        || measure_process.is_none_or(|path| !path.is_absolute())
        || output.is_none_or(|path| !path.is_absolute())
    {
        return Err("controller/validator paths must all be absolute".to_owned());
    }
    Ok(())
}

fn usage() -> String {
    "usage: bench_certificate_term_dag_materialization --validate-manifest-only PATH [--scenario ID]\n       bench_certificate_term_dag_materialization --validate-baseline-only PATH\n       bench_certificate_term_dag_materialization --validate-all --manifest PATH --baseline PATH\n       bench_certificate_term_dag_materialization --check-deterministic --manifest PATH --baseline PATH --scenario ID\n       bench_certificate_term_dag_materialization --child --manifest PATH --baseline PATH --scenario ID --case ID --requested-jobs N --sample-index N\n       bench_certificate_term_dag_materialization --controller --manifest PATH --baseline PATH --measure-process PATH --output PATH\n       bench_certificate_term_dag_materialization --validate-report --manifest PATH --baseline PATH --measure-process PATH --output PATH".to_owned()
}

fn validate_pair(arguments: &Arguments) -> Result<(), String> {
    term_dag_performance::validate_manifest(&read_utf8(&arguments.manifest)?)?;
    term_dag_performance::validate_baseline(&read_utf8(&arguments.baseline)?)?;
    let workspace = workspace_root().canonicalize().map_err(display_error)?;
    term_dag_performance::validate_artifacts(&workspace)
}

fn validate_optional_scenario(id: Option<&str>) -> Result<(), String> {
    if let Some(id) = id {
        term_dag_performance::scenario(id).ok_or_else(|| format!("unknown scenario: {id}"))?;
    }
    Ok(())
}

fn selected_case(arguments: &Arguments) -> Result<CaseSpec, String> {
    let scenario = arguments.scenario.as_deref().ok_or("missing scenario")?;
    let case_id = arguments.case_id.as_deref().ok_or("missing case")?;
    let requested_jobs = arguments.requested_jobs.ok_or("missing requested jobs")?;
    term_dag_performance::cases()
        .into_iter()
        .find(|case| {
            case.scenario_id == scenario
                && case.case_id == case_id
                && case.requested_jobs == requested_jobs
        })
        .ok_or_else(|| "scenario/case/requested-jobs lane mismatch".to_owned())
}

fn run_child(arguments: &Arguments) -> Result<(), String> {
    validate_pair(arguments)?;
    let case = selected_case(arguments)?;
    let prepared = term_dag_performance::prepare_production_case(&case)?;
    let warmup = prepared.execute()?;
    term_dag_performance::validate_production_result(&case, &warmup)?;
    let (measured, elapsed) = prepared.execute_measured()?;
    term_dag_performance::validate_production_result(&case, &measured)?;
    let manifest = read_bounded(&arguments.manifest, MAX_DESCRIPTOR_BYTES, "manifest")?;
    let baseline = read_bounded(&arguments.baseline, MAX_DESCRIPTOR_BYTES, "baseline")?;
    let manifest_text = std::str::from_utf8(&manifest)
        .map_err(|_| "controller manifest snapshot is not UTF-8".to_owned())?;
    let baseline_text = std::str::from_utf8(&baseline)
        .map_err(|_| "controller baseline snapshot is not UTF-8".to_owned())?;
    term_dag_performance::validate_manifest(manifest_text)?;
    term_dag_performance::validate_baseline(baseline_text)?;
    let scenario = term_dag_performance::scenario(case.scenario_id).ok_or_else(|| {
        format!(
            "closed case references unknown scenario {}",
            case.scenario_id
        )
    })?;
    let sample_index = arguments.sample_index.ok_or("missing child sample index")?;
    let json = child_json(
        &case,
        sample_index,
        &term_dag_performance::fixture_tree_hash_for_descriptor(scenario),
        &term_dag_performance::sha256(&manifest),
        &term_dag_performance::sha256(&baseline),
        elapsed,
        &term_dag_performance::production_observation_json(&case, &measured),
    );
    npa_api::JsonDocument::parse(&json)
        .map_err(|error| format!("child JSON invalid at {}", error.offset))?;
    println!("{json}");
    Ok(())
}

fn execute_deterministic_case(case: &CaseSpec) -> Result<(), String> {
    let prepared = term_dag_performance::prepare_production_case(case)?;
    let actual = prepared.execute()?;
    term_dag_performance::validate_production_result(case, &actual)
}

#[derive(Debug)]
struct ControllerRow {
    child: String,
    scenario_id: String,
    case_id: String,
    requested_jobs: u64,
    inner_elapsed_ns: u64,
    process_elapsed_seconds: String,
    peak_rss_kib: u64,
    exit_code: i32,
}

fn run_controller(arguments: &Arguments) -> Result<(), String> {
    validate_pair(arguments)?;
    if cfg!(debug_assertions) {
        return Err("controller mode requires a release build".to_owned());
    }
    if env!("NPA_BUILD_CARGO_PROFILE") != "release" {
        return Err(format!(
            "controller mode requires Cargo release profile, got {}",
            env!("NPA_BUILD_CARGO_PROFILE")
        ));
    }
    validate_runtime_build_inputs(false)?;
    let output = canonical_new_output_path(
        arguments
            .output
            .as_ref()
            .ok_or("controller output was not provided")?,
        "controller output",
    )?;
    let runner = std::env::current_exe().map_err(display_error)?;
    let runner = canonical_regular_file(&runner, "runner")?;
    let measure_process = canonical_regular_file(
        arguments
            .measure_process
            .as_ref()
            .ok_or("measure-process executable was not provided")?,
        "measure-process",
    )?;
    let manifest = read_bounded(&arguments.manifest, MAX_DESCRIPTOR_BYTES, "manifest")?;
    let baseline = read_bounded(&arguments.baseline, MAX_DESCRIPTOR_BYTES, "baseline")?;
    let manifest_sha256 = term_dag_performance::sha256(&manifest);
    let baseline_sha256 = term_dag_performance::sha256(&baseline);
    let temporary_directory = make_controller_temp_dir()?;
    let runner_snapshot = temporary_directory.create_executable_snapshot(
        Path::new("runner"),
        &runner,
        MAX_EXECUTABLE_BYTES,
        "TDAG runner",
    )?;
    let measure_snapshot = temporary_directory.create_executable_snapshot(
        Path::new("measure-process"),
        &measure_process,
        MAX_EXECUTABLE_BYTES,
        "TDAG measure-process",
    )?;
    let manifest_snapshot =
        temporary_directory.create_input_snapshot(Path::new("manifest.json"), &manifest)?;
    let baseline_snapshot =
        temporary_directory.create_input_snapshot(Path::new("baseline.json"), &baseline)?;
    let mut snapshot_arguments = arguments.clone();
    snapshot_arguments.manifest = temporary_directory.path()?.join("manifest.json");
    snapshot_arguments.baseline = temporary_directory.path()?.join("baseline.json");
    snapshot_arguments.measure_process = Some(measure_snapshot.path().to_owned());
    let collection = (|| -> Result<Vec<ControllerRow>, String> {
        let mut rows = Vec::with_capacity(54);
        for sample in 0_u64..3 {
            for case in term_dag_performance::cases() {
                let stem = format!(
                    "tdag-{}-{}-{sample}-{}",
                    case.scenario_id,
                    case.case_id,
                    std::process::id()
                );
                let stdout_name = PathBuf::from(format!("{stem}.stdout"));
                let stderr_name = PathBuf::from(format!("{stem}.stderr"));
                let stdout_path = temporary_directory.path()?.join(&stdout_name);
                let stderr_path = temporary_directory.path()?.join(&stderr_name);
                verify_tdag_controller_inputs(
                    &runner_snapshot,
                    &measure_snapshot,
                    &manifest_snapshot,
                    &manifest,
                    &baseline_snapshot,
                    &baseline,
                )?;
                let measured = Command::new(measure_snapshot.path())
                    .args([
                        "--output",
                        stdout_path.to_str().ok_or("stdout path is not UTF-8")?,
                        "--stderr",
                        stderr_path.to_str().ok_or("stderr path is not UTF-8")?,
                        "--",
                        runner_snapshot
                            .path()
                            .to_str()
                            .ok_or("runner path is not UTF-8")?,
                        "--child",
                        "--manifest",
                        snapshot_arguments
                            .manifest
                            .to_str()
                            .ok_or("manifest path is not UTF-8")?,
                        "--baseline",
                        snapshot_arguments
                            .baseline
                            .to_str()
                            .ok_or("baseline path is not UTF-8")?,
                        "--scenario",
                        case.scenario_id,
                        "--case",
                        &case.case_id,
                        "--requested-jobs",
                        &case.requested_jobs.to_string(),
                        "--sample-index",
                        &sample.to_string(),
                    ])
                    .output()
                    .map_err(display_error)?;
                verify_tdag_controller_inputs(
                    &runner_snapshot,
                    &measure_snapshot,
                    &manifest_snapshot,
                    &manifest,
                    &baseline_snapshot,
                    &baseline,
                )?;
                if !measured.status.success() {
                    return Err(format!(
                        "measure-process failed for {stem}: {}",
                        String::from_utf8_lossy(&measured.stderr)
                    ));
                }
                let wrapper = String::from_utf8(measured.stdout).map_err(display_error)?;
                let (process_elapsed_seconds, peak_rss_kib, exit_code) = parse_wrapper(&wrapper)?;
                let child = String::from_utf8(
                    temporary_directory.read_regular_file(&stdout_name, 1024 * 1024)?,
                )
                .map_err(display_error)?;
                let child = child
                    .strip_suffix('\n')
                    .ok_or("child output must contain exactly one newline")?
                    .to_owned();
                let scenario =
                    term_dag_performance::scenario(case.scenario_id).ok_or_else(|| {
                        format!(
                            "closed case references unknown scenario {}",
                            case.scenario_id
                        )
                    })?;
                let inner_elapsed_ns = validate_child_output(
                    &child,
                    &case,
                    sample,
                    &term_dag_performance::fixture_tree_hash_for_descriptor(scenario),
                    &manifest_sha256,
                    &baseline_sha256,
                )?;
                if exit_code != 0 {
                    return Err(format!("child returned nonzero exit code {exit_code}"));
                }
                let stderr = String::from_utf8(
                    temporary_directory.read_regular_file(&stderr_name, 1024 * 1024)?,
                )
                .map_err(display_error)?;
                if !stderr.is_empty() {
                    return Err(format!("child wrote stderr for {stem}"));
                }
                rows.push(ControllerRow {
                    child,
                    scenario_id: case.scenario_id.to_owned(),
                    case_id: case.case_id,
                    requested_jobs: case.requested_jobs,
                    inner_elapsed_ns,
                    process_elapsed_seconds,
                    peak_rss_kib,
                    exit_code,
                });
            }
        }
        Ok(rows)
    })();
    let rows = collection?;
    validate_controller_rows(&rows)?;
    let report = controller_report_with_hashes(
        &snapshot_arguments,
        runner_snapshot.sha256(),
        measure_snapshot.sha256(),
        &rows,
    )?;
    validate_controller_report_with_hashes(
        &report,
        &snapshot_arguments,
        runner_snapshot.sha256(),
        measure_snapshot.sha256(),
    )?;
    verify_tdag_controller_inputs(
        &runner_snapshot,
        &measure_snapshot,
        &manifest_snapshot,
        &manifest,
        &baseline_snapshot,
        &baseline,
    )?;
    drop(runner_snapshot);
    drop(measure_snapshot);
    drop(manifest_snapshot);
    drop(baseline_snapshot);
    temporary_directory.cleanup_exact(controller_temp_catalog())?;
    write_new_file(&output, report.as_bytes())
}

fn verify_tdag_controller_inputs(
    runner: &AttachedExecutable,
    measure_process: &AttachedExecutable,
    manifest: &AttachedOutputFile,
    expected_manifest: &[u8],
    baseline: &AttachedOutputFile,
    expected_baseline: &[u8],
) -> Result<(), String> {
    runner.verify()?;
    measure_process.verify()?;
    if manifest.read_all_bounded(MAX_DESCRIPTOR_BYTES)? != expected_manifest {
        return Err("private TDAG manifest snapshot bytes changed".to_owned());
    }
    if baseline.read_all_bounded(MAX_DESCRIPTOR_BYTES)? != expected_baseline {
        return Err("private TDAG baseline snapshot bytes changed".to_owned());
    }
    Ok(())
}

fn run_report_validator(arguments: &Arguments) -> Result<(), String> {
    validate_pair(arguments)?;
    validate_runtime_build_inputs(cfg!(test))?;
    let output = arguments
        .output
        .as_ref()
        .ok_or("validate-report output was not provided")?;
    let measure_process = arguments
        .measure_process
        .as_ref()
        .ok_or("validate-report measure-process was not provided")?;
    let measure_process = canonical_regular_file(measure_process, "measure-process")?;
    let runner = std::env::current_exe().map_err(display_error)?;
    let runner = canonical_regular_file(&runner, "runner")?;
    canonical_regular_file(output, "run report")?;
    let report = String::from_utf8(read_absolute_regular_file(
        output,
        MAX_REPORT_BYTES,
        "run report",
    )?)
    .map_err(display_error)?;
    validate_controller_report(&report, arguments, &runner, &measure_process)
}

fn canonical_regular_file(path: &Path, label: &str) -> Result<PathBuf, String> {
    if !path.is_absolute() {
        return Err(format!("{label} path must be absolute"));
    }
    let mut cursor = PathBuf::new();
    for component in path.components() {
        cursor.push(component.as_os_str());
        let metadata = fs::symlink_metadata(&cursor).map_err(display_error)?;
        if metadata.file_type().is_symlink() {
            return Err(format!("{label} path must not contain symbolic links"));
        }
    }
    let metadata = fs::symlink_metadata(path).map_err(display_error)?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!("{label} must be a regular non-symlink file"));
    }
    let canonical = fs::canonicalize(path).map_err(display_error)?;
    if canonical != path {
        return Err(format!("{label} path must already be canonical"));
    }
    Ok(canonical)
}

fn valid_output_basename(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|byte| byte.is_ascii_alphanumeric())
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
}

fn canonical_new_output_path(path: &Path, label: &str) -> Result<PathBuf, String> {
    if !path.is_absolute() {
        return Err(format!("{label} path must be absolute"));
    }
    match fs::symlink_metadata(path) {
        Ok(_) => return Err(format!("{label} already exists")),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(display_error(error)),
    }
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .ok_or_else(|| format!("{label} has no parent"))?;
    let mut cursor = PathBuf::new();
    for component in parent.components() {
        cursor.push(component.as_os_str());
        let metadata = fs::symlink_metadata(&cursor).map_err(display_error)?;
        if metadata.file_type().is_symlink() {
            return Err(format!("{label} parent must not contain symbolic links"));
        }
    }
    let metadata = fs::symlink_metadata(parent).map_err(display_error)?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!("{label} parent must be a non-symlink directory"));
    }
    let canonical_parent = fs::canonicalize(parent).map_err(display_error)?;
    if canonical_parent != parent {
        return Err(format!("{label} parent must already be canonical"));
    }
    let basename = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("{label} basename must be UTF-8"))?;
    if !valid_output_basename(basename) {
        return Err(format!("{label} has an invalid basename"));
    }
    let canonical = canonical_parent.join(basename);
    if canonical != path {
        return Err(format!(
            "{label} must already be a normalized canonical path"
        ));
    }
    Ok(canonical)
}

fn parse_wrapper(source: &str) -> Result<(String, u64, i32), String> {
    let line = source
        .strip_suffix('\n')
        .ok_or("measure-process output must end in exactly one newline")?;
    if line.contains(['\n', '\r']) {
        return Err("measure-process output must be exactly one line".to_owned());
    }
    let fields = line.split('\t').collect::<Vec<_>>();
    let seconds = fields.first().and_then(|value| value.split_once('.'));
    if fields.len() != 3
        || !matches!(seconds, Some((whole, fraction))
            if !whole.is_empty()
                && whole.bytes().all(|byte| byte.is_ascii_digit())
                && fraction.len() == 9
                && fraction.bytes().all(|byte| byte.is_ascii_digit()))
    {
        return Err("measure-process output shape mismatch".to_owned());
    }
    Ok((
        fields[0].to_owned(),
        fields[1].parse().map_err(display_error)?,
        fields[2].parse().map_err(display_error)?,
    ))
}

fn validate_controller_rows(rows: &[ControllerRow]) -> Result<(), String> {
    let cases = term_dag_performance::cases();
    if rows.len() != cases.len() * 3 {
        return Err("controller requires exactly 54 rows".to_owned());
    }
    for sample in 0..3 {
        for (case_index, case) in cases.iter().enumerate() {
            let row = &rows[sample * cases.len() + case_index];
            if row.scenario_id != case.scenario_id
                || row.case_id != case.case_id
                || row.requested_jobs != case.requested_jobs
                || row.exit_code != 0
            {
                return Err("controller row selection/order mismatch".to_owned());
            }
        }
    }
    Ok(())
}

fn child_json(
    case: &CaseSpec,
    sample_index: u64,
    fixture_tree_sha256: &str,
    manifest_sha256: &str,
    baseline_sha256: &str,
    inner_elapsed_ns: u64,
    deterministic_observation: &str,
) -> String {
    format!(
        "{{\"schema\":\"{}\",\"scenario_id\":\"{}\",\"case_id\":\"{}\",\"requested_jobs\":{},\"sample_index\":{},\"fixture_tree_sha256\":\"{}\",\"manifest_sha256\":\"{}\",\"baseline_sha256\":\"{}\",\"inner_elapsed_ns\":{},\"deterministic_observation\":{}}}",
        term_dag_performance::CHILD_SCHEMA,
        case.scenario_id,
        case.case_id,
        case.requested_jobs,
        sample_index,
        fixture_tree_sha256,
        manifest_sha256,
        baseline_sha256,
        inner_elapsed_ns,
        deterministic_observation,
    )
}

fn validate_child_output(
    source: &str,
    case: &CaseSpec,
    sample_index: u64,
    fixture_tree_sha256: &str,
    manifest_sha256: &str,
    baseline_sha256: &str,
) -> Result<u64, String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("child JSON invalid at {}", error.offset))?;
    let fields = exact_object(
        document.root(),
        &[
            "schema",
            "scenario_id",
            "case_id",
            "requested_jobs",
            "sample_index",
            "fixture_tree_sha256",
            "manifest_sha256",
            "baseline_sha256",
            "inner_elapsed_ns",
            "deterministic_observation",
        ],
        "term_dag_child",
    )?;
    let elapsed = fields[8]
        .value()
        .number_raw()
        .ok_or("term_dag_child.inner_elapsed_ns must be an unsigned integer")?
        .parse::<u64>()
        .map_err(|_| "term_dag_child.inner_elapsed_ns must be an unsigned integer".to_owned())?;
    let expected_observation = term_dag_performance::expected_production_observation_json(case)?;
    let expected = child_json(
        case,
        sample_index,
        fixture_tree_sha256,
        manifest_sha256,
        baseline_sha256,
        elapsed,
        &expected_observation,
    );
    if source != expected {
        return Err("term-DAG child row does not match its exact selected lane".to_owned());
    }
    Ok(elapsed)
}

fn exact_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    expected_keys: &[&str],
    path: &str,
) -> Result<&'value [JsonMember<'source>], String> {
    let fields = value
        .object_members()
        .ok_or_else(|| format!("{path} must be an object"))?;
    let actual_keys = fields.iter().map(JsonMember::key).collect::<Vec<_>>();
    if actual_keys != expected_keys {
        return Err(format!("{path} keys/order mismatch: {actual_keys:?}"));
    }
    Ok(fields)
}

struct ControllerTempDir(Option<ClosedPrivateDirectory>);

impl ControllerTempDir {
    fn path(&self) -> Result<&Path, String> {
        self.0
            .as_ref()
            .map(ClosedPrivateDirectory::path)
            .ok_or("controller temporary directory was already cleaned".to_owned())
    }

    fn read_regular_file(&self, relative: &Path, maximum_bytes: u64) -> Result<Vec<u8>, String> {
        self.0
            .as_ref()
            .ok_or("controller temporary directory was already cleaned")?
            .read_regular_file(relative, maximum_bytes)
    }

    fn directory(&self) -> Result<&ClosedPrivateDirectory, String> {
        self.0
            .as_ref()
            .ok_or("controller temporary directory was already cleaned".to_owned())
    }

    fn create_executable_snapshot(
        &self,
        relative: &Path,
        source: &Path,
        maximum_bytes: u64,
        label: &str,
    ) -> Result<AttachedExecutable, String> {
        self.directory()?
            .create_executable_snapshot(relative, source, maximum_bytes, label)
    }

    fn create_input_snapshot(
        &self,
        relative: &Path,
        bytes: &[u8],
    ) -> Result<AttachedOutputFile, String> {
        let mut output = self.directory()?.create_new_file_handle(relative)?;
        output.write_all(bytes).map_err(display_error)?;
        output.sync_all().map_err(display_error)?;
        Ok(output)
    }

    fn cleanup_exact(mut self, files: BTreeSet<PathBuf>) -> Result<(), String> {
        self.0
            .take()
            .ok_or("controller temporary directory was already cleaned")?
            .remove_exact_root(&files)
    }
}

impl Drop for ControllerTempDir {
    fn drop(&mut self) {
        if let Some(directory) = self.0.take() {
            let _ = directory.remove_allowed_root(&controller_temp_catalog());
        }
    }
}

fn make_controller_temp_dir() -> Result<ControllerTempDir, String> {
    ClosedPrivateDirectory::new("npa-certificate-term-dag-controller")
        .map(|directory| ControllerTempDir(Some(directory)))
}

fn controller_temp_catalog() -> BTreeSet<PathBuf> {
    let mut files = BTreeSet::new();
    for fixed in [
        "runner",
        "measure-process",
        "manifest.json",
        "baseline.json",
    ] {
        files.insert(PathBuf::from(fixed));
    }
    for sample in 0_u64..3 {
        for case in term_dag_performance::cases() {
            let stem = format!(
                "tdag-{}-{}-{sample}-{}",
                case.scenario_id,
                case.case_id,
                std::process::id()
            );
            files.insert(PathBuf::from(format!("{stem}.stdout")));
            files.insert(PathBuf::from(format!("{stem}.stderr")));
        }
    }
    files
}

fn write_new_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = create_new_absolute_file(path, "controller output")?;
    file.write_all(bytes)
        .map_err(|error| format!("write controller output {}: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("sync controller output {}: {error}", path.display()))
}

#[cfg(test)]
fn controller_report(
    arguments: &Arguments,
    runner: &Path,
    measure_process: &Path,
    rows: &[ControllerRow],
) -> Result<String, String> {
    let runner_sha256 = term_dag_performance::sha256(&read_absolute_regular_file(
        runner,
        MAX_EXECUTABLE_BYTES,
        "runner",
    )?);
    let measure_process_sha256 = term_dag_performance::sha256(&read_absolute_regular_file(
        measure_process,
        MAX_EXECUTABLE_BYTES,
        "measure-process",
    )?);
    controller_report_with_hashes(arguments, &runner_sha256, &measure_process_sha256, rows)
}

fn controller_report_with_hashes(
    arguments: &Arguments,
    runner_sha256: &str,
    measure_process_sha256: &str,
    rows: &[ControllerRow],
) -> Result<String, String> {
    if rows.len() != 54 {
        return Err("controller requires exactly 54 rows".to_owned());
    }
    let row_json = rows
        .iter()
        .map(|row| {
            let prefix = row
                .child
                .strip_suffix('}')
                .ok_or("validated child object lost its closing delimiter")?;
            Ok(format!("{prefix},\"process_elapsed_seconds\":\"{}\",\"peak_rss_kib\":{},\"exit_code\":{}}}", row.process_elapsed_seconds, row.peak_rss_kib, row.exit_code))
        })
        .collect::<Result<Vec<_>, String>>()?
        .join(",");
    let summaries = term_dag_performance::cases().into_iter().map(|case| {
        let selected = rows.iter().filter(|row| row.scenario_id == case.scenario_id && row.case_id == case.case_id && row.requested_jobs == case.requested_jobs).collect::<Vec<_>>();
        let inner = selected.iter().map(|row| row.inner_elapsed_ns).collect::<Vec<_>>();
        let rss = selected.iter().map(|row| row.peak_rss_kib).collect::<Vec<_>>();
        Ok(format!("{{\"scenario_id\":\"{}\",\"case_id\":\"{}\",\"requested_jobs\":{},\"inner_elapsed_ns\":{},\"process_peak_rss_kib\":{}}}", case.scenario_id, case.case_id, case.requested_jobs, statistics_json(&inner)?, statistics_json(&rss)?))
    }).collect::<Result<Vec<_>, String>>()?.join(",");
    controller_report_from_parts(
        arguments,
        runner_sha256,
        measure_process_sha256,
        &row_json,
        &summaries,
    )
}

fn controller_report_from_parts(
    arguments: &Arguments,
    runner_sha256: &str,
    measure_process_sha256: &str,
    row_json: &str,
    summaries: &str,
) -> Result<String, String> {
    let manifest = read_bounded(&arguments.manifest, MAX_DESCRIPTOR_BYTES, "manifest")?;
    let baseline = read_bounded(&arguments.baseline, MAX_DESCRIPTOR_BYTES, "baseline")?;
    validate_runtime_build_inputs(cfg!(test))?;
    let source_identity = runtime_source_identity(cfg!(test))?;
    let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?;
    let target = env!("NPA_BUILD_TARGET");
    let features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(quoted)
        .collect::<Vec<_>>()
        .join(",");
    let rustflags = decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?;
    let json = format!(
        "{{\"schema\":\"{}\",\"manifest_sha256\":\"{}\",\"baseline_sha256\":\"{}\",\"interleave\":\"sample-major-scenario-job-order\",\"warmup_per_child\":1,\"samples_per_lane\":3,\"build_identity\":{{\"source_identity\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv_sha256\":\"{}\",\"target\":\"{}\",\"profile\":{},\"features\":[{}],\"rustflags\":{},\"tdag_source_set_sha256\":\"{}\",\"runner_source_sha256\":\"{}\",\"support_source_sha256\":\"{}\",\"runner_sha256\":\"{}\",\"measure_process_sha256\":\"{}\"}},\"rows\":[{}],\"summaries\":[{}]}}\n",
        term_dag_performance::RUN_SCHEMA,
        term_dag_performance::sha256(&manifest),
        term_dag_performance::sha256(&baseline),
        source_identity,
        env!("NPA_BUILD_CARGO_LOCK_SHA256"),
        term_dag_performance::sha256(rustc_vv.as_bytes()),
        target,
        quoted(env!("NPA_BUILD_CARGO_PROFILE")),
        features,
        quoted(&rustflags),
        env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256"),
        env!("NPA_BUILD_TDAG_RUNNER_SOURCE_SHA256"),
        env!("NPA_BUILD_TDAG_SUPPORT_SOURCE_SHA256"),
        runner_sha256,
        measure_process_sha256,
        row_json,
        summaries,
    );
    npa_api::JsonDocument::parse(&json)
        .map_err(|error| format!("run JSON invalid at {}", error.offset))?;
    Ok(json)
}

fn validate_controller_report(
    source: &str,
    arguments: &Arguments,
    runner: &Path,
    measure_process: &Path,
) -> Result<(), String> {
    let runner_sha256 = term_dag_performance::sha256(&read_absolute_regular_file(
        runner,
        MAX_EXECUTABLE_BYTES,
        "runner",
    )?);
    let measure_process_sha256 = term_dag_performance::sha256(&read_absolute_regular_file(
        measure_process,
        MAX_EXECUTABLE_BYTES,
        "measure-process",
    )?);
    validate_controller_report_with_hashes(
        source,
        arguments,
        &runner_sha256,
        &measure_process_sha256,
    )
}

fn validate_controller_report_with_hashes(
    source: &str,
    arguments: &Arguments,
    runner_sha256: &str,
    measure_process_sha256: &str,
) -> Result<(), String> {
    if !source.ends_with('\n') || source[..source.len() - 1].contains('\n') {
        return Err("run report must be one newline-terminated JSON object".to_owned());
    }
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("run JSON invalid at {}", error.offset))?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "manifest_sha256",
            "baseline_sha256",
            "interleave",
            "warmup_per_child",
            "samples_per_lane",
            "build_identity",
            "rows",
            "summaries",
        ],
        "term_dag_run",
    )?;
    expect_string(
        root[0].value(),
        term_dag_performance::RUN_SCHEMA,
        "term_dag_run.schema",
    )?;
    let manifest = read_bounded(&arguments.manifest, MAX_DESCRIPTOR_BYTES, "manifest")?;
    let baseline = read_bounded(&arguments.baseline, MAX_DESCRIPTOR_BYTES, "baseline")?;
    expect_string(
        root[1].value(),
        &term_dag_performance::sha256(&manifest),
        "term_dag_run.manifest_sha256",
    )?;
    expect_string(
        root[2].value(),
        &term_dag_performance::sha256(&baseline),
        "term_dag_run.baseline_sha256",
    )?;
    expect_string(
        root[3].value(),
        "sample-major-scenario-job-order",
        "term_dag_run.interleave",
    )?;
    expect_u64(root[4].value(), 1, "term_dag_run.warmup_per_child")?;
    expect_u64(root[5].value(), 3, "term_dag_run.samples_per_lane")?;
    let build = exact_object(
        root[6].value(),
        &[
            "source_identity",
            "cargo_lock_sha256",
            "rustc_vv_sha256",
            "target",
            "profile",
            "features",
            "rustflags",
            "tdag_source_set_sha256",
            "runner_source_sha256",
            "support_source_sha256",
            "runner_sha256",
            "measure_process_sha256",
        ],
        "term_dag_run.build_identity",
    )?;
    let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?;
    let rustflags = decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?;
    let rustc_vv_sha256 = term_dag_performance::sha256(rustc_vv.as_bytes());
    let source_identity = runtime_source_identity(cfg!(test))?;
    for (value, expected, path) in [
        (
            build[0].value(),
            source_identity.as_str(),
            "source_identity",
        ),
        (
            build[1].value(),
            env!("NPA_BUILD_CARGO_LOCK_SHA256"),
            "cargo_lock_sha256",
        ),
        (
            build[2].value(),
            rustc_vv_sha256.as_str(),
            "rustc_vv_sha256",
        ),
        (build[3].value(), env!("NPA_BUILD_TARGET"), "target"),
        (build[4].value(), env!("NPA_BUILD_CARGO_PROFILE"), "profile"),
        (build[6].value(), rustflags.as_str(), "rustflags"),
        (
            build[7].value(),
            env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256"),
            "tdag_source_set_sha256",
        ),
        (
            build[8].value(),
            env!("NPA_BUILD_TDAG_RUNNER_SOURCE_SHA256"),
            "runner_source_sha256",
        ),
        (
            build[9].value(),
            env!("NPA_BUILD_TDAG_SUPPORT_SOURCE_SHA256"),
            "support_source_sha256",
        ),
        (build[10].value(), runner_sha256, "runner_sha256"),
        (
            build[11].value(),
            measure_process_sha256,
            "measure_process_sha256",
        ),
    ] {
        expect_string(
            value,
            expected,
            &format!("term_dag_run.build_identity.{path}"),
        )?;
    }
    let expected_features = env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .collect::<Vec<_>>();
    let features = build[5]
        .value()
        .array_elements()
        .ok_or("term_dag_run.build_identity.features must be an array")?;
    if features.len() != expected_features.len()
        || features
            .iter()
            .zip(expected_features)
            .any(|(value, expected)| value.string_value() != Some(expected))
    {
        return Err("term_dag_run.build_identity.features mismatch".to_owned());
    }
    let rows = root[7]
        .value()
        .array_elements()
        .ok_or("term_dag_run.rows must be an array")?;
    let cases = term_dag_performance::cases();
    if rows.len() != cases.len() * 3 {
        return Err("term_dag_run requires exactly 54 rows".to_owned());
    }
    let manifest_hash = term_dag_performance::sha256(&manifest);
    let baseline_hash = term_dag_performance::sha256(&baseline);
    let mut summary_inputs = Vec::with_capacity(rows.len());
    let mut canonical_rows = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().enumerate() {
        let sample = u64::try_from(index / cases.len()).map_err(display_error)?;
        let case = &cases[index % cases.len()];
        let fields = exact_object(
            row,
            &[
                "schema",
                "scenario_id",
                "case_id",
                "requested_jobs",
                "sample_index",
                "fixture_tree_sha256",
                "manifest_sha256",
                "baseline_sha256",
                "inner_elapsed_ns",
                "deterministic_observation",
                "process_elapsed_seconds",
                "peak_rss_kib",
                "exit_code",
            ],
            "term_dag_run.rows[]",
        )?;
        expect_string(
            fields[0].value(),
            term_dag_performance::CHILD_SCHEMA,
            "row.schema",
        )?;
        expect_string(fields[1].value(), case.scenario_id, "row.scenario_id")?;
        expect_string(fields[2].value(), &case.case_id, "row.case_id")?;
        expect_u64(fields[3].value(), case.requested_jobs, "row.requested_jobs")?;
        expect_u64(fields[4].value(), sample, "row.sample_index")?;
        let scenario = term_dag_performance::scenario(case.scenario_id)
            .ok_or("closed case references unknown scenario")?;
        expect_string(
            fields[5].value(),
            &term_dag_performance::fixture_tree_hash_for_descriptor(scenario),
            "row.fixture_tree_sha256",
        )?;
        expect_string(fields[6].value(), &manifest_hash, "row.manifest_sha256")?;
        expect_string(fields[7].value(), &baseline_hash, "row.baseline_sha256")?;
        let inner = canonical_u64(fields[8].value(), "row.inner_elapsed_ns")?;
        if fields[9].value().raw_slice()
            != term_dag_performance::expected_production_observation_json(case)?
        {
            return Err("row deterministic observation mismatch".to_owned());
        }
        let process = fields[10]
            .value()
            .string_value()
            .ok_or("row process elapsed must be a string")?;
        parse_wrapper(&format!(
            "{process}\t{}\t{}\n",
            fields[11].value().raw_slice(),
            fields[12].value().raw_slice()
        ))?;
        let rss = canonical_u64(fields[11].value(), "row.peak_rss_kib")?;
        expect_u64(fields[12].value(), 0, "row.exit_code")?;
        summary_inputs.push((
            case.scenario_id,
            case.case_id.clone(),
            case.requested_jobs,
            inner,
            rss,
        ));
        canonical_rows.push(format!(
            "{{\"schema\":{},\"scenario_id\":{},\"case_id\":{},\"requested_jobs\":{},\"sample_index\":{},\"fixture_tree_sha256\":{},\"manifest_sha256\":{},\"baseline_sha256\":{},\"inner_elapsed_ns\":{},\"deterministic_observation\":{},\"process_elapsed_seconds\":{},\"peak_rss_kib\":{},\"exit_code\":0}}",
            quoted(term_dag_performance::CHILD_SCHEMA),
            quoted(case.scenario_id),
            quoted(&case.case_id),
            case.requested_jobs,
            sample,
            quoted(&term_dag_performance::fixture_tree_hash_for_descriptor(scenario)),
            quoted(&manifest_hash),
            quoted(&baseline_hash),
            inner,
            term_dag_performance::expected_production_observation_json(case)?,
            quoted(process),
            rss,
        ));
    }
    let summaries = root[8]
        .value()
        .array_elements()
        .ok_or("term_dag_run.summaries must be an array")?;
    if summaries.len() != cases.len() {
        return Err("term_dag_run requires exactly 18 summaries".to_owned());
    }
    let mut canonical_summaries = Vec::with_capacity(summaries.len());
    for (summary, case) in summaries.iter().zip(&cases) {
        let selected = summary_inputs
            .iter()
            .filter(|row| {
                row.0 == case.scenario_id && row.1 == case.case_id && row.2 == case.requested_jobs
            })
            .collect::<Vec<_>>();
        let expected = format!(
            "{{\"scenario_id\":\"{}\",\"case_id\":\"{}\",\"requested_jobs\":{},\"inner_elapsed_ns\":{},\"process_peak_rss_kib\":{}}}",
            case.scenario_id,
            case.case_id,
            case.requested_jobs,
            statistics_json(&selected.iter().map(|row| row.3).collect::<Vec<_>>())?,
            statistics_json(&selected.iter().map(|row| row.4).collect::<Vec<_>>())?,
        );
        if summary.raw_slice() != expected {
            return Err(format!(
                "summary mismatch for {}/{}",
                case.scenario_id, case.case_id
            ));
        }
        canonical_summaries.push(expected);
    }
    let canonical = controller_report_from_parts(
        arguments,
        runner_sha256,
        measure_process_sha256,
        &canonical_rows.join(","),
        &canonical_summaries.join(","),
    )?;
    if source != canonical {
        return Err("run report is not the canonical serialized object".to_owned());
    }
    Ok(())
}

fn expect_string(value: &JsonValue<'_>, expected: &str, path: &str) -> Result<(), String> {
    if value.string_value() == Some(expected) {
        Ok(())
    } else {
        Err(format!("{path} mismatch"))
    }
}

fn canonical_u64(value: &JsonValue<'_>, path: &str) -> Result<u64, String> {
    let raw = value
        .number_raw()
        .ok_or_else(|| format!("{path} must be a number"))?;
    if raw.is_empty()
        || (raw.len() > 1 && raw.starts_with('0'))
        || !raw.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{path} must be a canonical unsigned integer"));
    }
    raw.parse().map_err(|_| format!("{path} overflows u64"))
}

fn expect_u64(value: &JsonValue<'_>, expected: u64, path: &str) -> Result<(), String> {
    if canonical_u64(value, path)? == expected {
        Ok(())
    } else {
        Err(format!("{path} mismatch"))
    }
}

fn quoted(value: &str) -> String {
    let mut result = String::with_capacity(value.len() + 2);
    result.push('"');
    for character in value.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                let _ = write!(&mut result, "\\u{:04x}", u32::from(character));
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

fn decode_build_hex(encoded: &str) -> Result<String, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("embedded build hex has odd length".to_owned());
    }
    let mut bytes = Vec::with_capacity(encoded.len() / 2);
    for pair in encoded.as_bytes().as_chunks::<2>().0 {
        let high = hex_nibble(pair[0]).ok_or("embedded build hex contains a non-hex digit")?;
        let low = hex_nibble(pair[1]).ok_or("embedded build hex contains a non-hex digit")?;
        bytes.push((high << 4) | low);
    }
    String::from_utf8(bytes).map_err(|_| "embedded build value is not UTF-8".to_owned())
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn statistics_json(values: &[u64]) -> Result<String, String> {
    if values.len() != 3 {
        return Err(format!(
            "statistics require exactly three samples, got {}",
            values.len()
        ));
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let median = sorted[1];
    let mut deviations = sorted
        .iter()
        .map(|value| value.abs_diff(median))
        .collect::<Vec<_>>();
    deviations.sort_unstable();
    Ok(format!(
        "{{\"samples\":[{},{},{}],\"median\":{},\"mad\":{},\"min\":{},\"max\":{}}}",
        values[0], values[1], values[2], median, deviations[1], sorted[0], sorted[2]
    ))
}

fn valid_source_identity(value: &str) -> bool {
    let oid = value.strip_suffix("-dirty").unwrap_or(value);
    oid.len() == 40
        && oid
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn command_stdout(executable: &str, arguments: &[&str]) -> Result<String, String> {
    let output = Command::new(executable)
        .args(arguments)
        .current_dir(workspace_root())
        .output()
        .map_err(display_error)?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!("{executable} failed or wrote stderr"));
    }
    let value = String::from_utf8(output.stdout).map_err(display_error)?;
    value
        .strip_suffix('\n')
        .filter(|line| !line.contains(['\n', '\r']))
        .map(str::to_owned)
        .ok_or_else(|| format!("{executable} output must be exactly one line"))
}

fn runtime_source_identity(allow_unbound_for_test: bool) -> Result<String, String> {
    let oid = command_stdout("/usr/bin/git", &["rev-parse", "HEAD"])?;
    if oid.ends_with("-dirty") || !valid_source_identity(&oid) {
        return Err("runtime Git HEAD is not a lowercase 40-digit OID".to_owned());
    }
    let output = Command::new("/usr/bin/git")
        .args(["status", "--porcelain", "--untracked-files=normal"])
        .current_dir(workspace_root())
        .output()
        .map_err(display_error)?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err("Git status failed or wrote stderr".to_owned());
    }
    let runtime = if output.stdout.is_empty() {
        oid
    } else {
        format!("{oid}-dirty")
    };
    let embedded = env!("NPA_BUILD_SOURCE_IDENTITY");
    if embedded == "unbound" && cfg!(test) && allow_unbound_for_test {
        return Ok("unbound".to_owned());
    }
    if embedded == "unbound" || !valid_source_identity(embedded) {
        return Err("term-DAG runner has no valid build-bound source identity".to_owned());
    }
    if embedded != runtime {
        return Err("runtime Git source identity differs from the term-DAG build".to_owned());
    }
    Ok(embedded.to_owned())
}

fn runtime_tdag_source_set_sha256() -> Result<String, String> {
    let workspace = fs::canonicalize(workspace_root()).map_err(display_error)?;
    runtime_source_set::validate_runtime_source_set(
        &workspace,
        env!("NPA_BUILD_TDAG_SOURCE_SET_PATHS"),
        b"npa-tdag-source-set-v2\0",
        env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256"),
        "term-DAG",
    )
    .map(|hash| hash.trim_start_matches("sha256:").to_owned())
}

fn validate_runtime_build_inputs(allow_unbound_for_test: bool) -> Result<(), String> {
    validate_runtime_build_inputs_against(
        env!("NPA_BUILD_CARGO_LOCK_SHA256"),
        env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256"),
        allow_unbound_for_test,
    )
}

fn validate_runtime_build_inputs_against(
    expected_cargo_lock_sha256: &str,
    expected_source_set_sha256: &str,
    allow_unbound_for_test: bool,
) -> Result<(), String> {
    let cargo_lock_path = workspace_root()
        .canonicalize()
        .map_err(display_error)?
        .join("Cargo.lock");
    let cargo_lock = read_absolute_regular_file(
        &cargo_lock_path,
        MAX_CARGO_LOCK_BYTES,
        "workspace Cargo.lock",
    )?;
    if term_dag_performance::sha256(&cargo_lock) != expected_cargo_lock_sha256 {
        return Err("runtime Cargo.lock differs from the lock used to build the runner".to_owned());
    }
    if runtime_tdag_source_set_sha256()? != expected_source_set_sha256 {
        return Err(
            "runtime term-DAG source set differs from bytes used to build the runner".to_owned(),
        );
    }
    runtime_source_identity(allow_unbound_for_test).map(|_| ())
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read_utf8(path: &Path) -> Result<String, String> {
    String::from_utf8(read_bounded(path, MAX_DESCRIPTOR_BYTES, "JSON input")?)
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn read_bounded(path: &Path, maximum_bytes: u64, label: &str) -> Result<Vec<u8>, String> {
    read_invocation_regular_file(path, maximum_bytes, label)
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_dag_manifest_baseline_parser() {
        let manifest = term_dag_performance::render_manifest().unwrap();
        let baseline = term_dag_performance::render_baseline().unwrap();
        term_dag_performance::validate_manifest(&manifest).unwrap();
        term_dag_performance::validate_baseline(&baseline).unwrap();
        assert!(term_dag_performance::validate_manifest(&manifest.replacen(
            "\"warmup\":1",
            "\"warmup\":2",
            1
        ))
        .is_err());
        assert!(term_dag_performance::validate_baseline(&baseline.replacen(
            "\"status\":\"passed\"",
            "\"status\":\"failed\"",
            1
        ))
        .is_err());
    }

    #[test]
    fn term_dag_child_protocol() {
        let case = term_dag_performance::cases().remove(0);
        let observation =
            term_dag_performance::expected_production_observation_json(&case).unwrap();
        npa_api::JsonDocument::parse(&observation).unwrap();
        assert!(observation.contains("\"case_id\":\"height-8\""));
        assert!(observation.contains("\"certificate.term_unique_nodes_materialized\":9"));
        let fixture_hash = "a".repeat(64);
        let manifest_hash = "b".repeat(64);
        let baseline_hash = "c".repeat(64);
        let child = child_json(
            &case,
            0,
            &fixture_hash,
            &manifest_hash,
            &baseline_hash,
            17,
            &observation,
        );
        assert_eq!(
            validate_child_output(
                &child,
                &case,
                0,
                &fixture_hash,
                &manifest_hash,
                &baseline_hash,
            )
            .unwrap(),
            17
        );
        assert!(validate_child_output(
            &child.replacen("\"sample_index\":0", "\"sample_index\":1", 1),
            &case,
            0,
            &fixture_hash,
            &manifest_hash,
            &baseline_hash,
        )
        .is_err());
        assert!(validate_child_output(
            &child.replacen("\"schema\":", "\"unknown\":0,\"schema\":", 1),
            &case,
            0,
            &fixture_hash,
            &manifest_hash,
            &baseline_hash,
        )
        .is_err());
    }

    #[test]
    fn term_dag_controller_protocol() {
        let cases = term_dag_performance::cases();
        assert_eq!(cases.len() * 3, 54);
        for case in &cases {
            let summary = statistics_json(&[
                case.requested_jobs,
                case.requested_jobs + 1,
                case.requested_jobs + 2,
            ])
            .unwrap();
            npa_api::JsonDocument::parse(&summary).unwrap();
            assert!(summary.contains("\"samples\""));
            assert!(summary.contains("\"mad\":1"));
        }
        assert_eq!(
            parse_wrapper("1.000000009\t2048\t0\n").unwrap(),
            ("1.000000009".to_owned(), 2_048, 0)
        );
        assert!(parse_wrapper("x.000000009\t2048\t0\n").is_err());
        assert!(parse_wrapper("1.000000009\t2048\t0\n\n").is_err());

        let mut rows = Vec::new();
        for _sample in 0..3 {
            for case in &cases {
                rows.push(ControllerRow {
                    child: "{}".to_owned(),
                    scenario_id: case.scenario_id.to_owned(),
                    case_id: case.case_id.clone(),
                    requested_jobs: case.requested_jobs,
                    inner_elapsed_ns: 1,
                    process_elapsed_seconds: "1.000000000".to_owned(),
                    peak_rss_kib: 1,
                    exit_code: 0,
                });
            }
        }
        validate_controller_rows(&rows).unwrap();
        rows.swap(0, 1);
        assert!(validate_controller_rows(&rows).is_err());

        let workspace = workspace_root().canonicalize().unwrap();
        let manifest = workspace.join(term_dag_performance::MANIFEST_PATH);
        let baseline = workspace.join(term_dag_performance::BASELINE_PATH);
        let arguments = Arguments {
            mode: Mode::Controller,
            manifest: manifest.clone(),
            baseline: baseline.clone(),
            scenario: None,
            case_id: None,
            requested_jobs: None,
            sample_index: None,
            measure_process: Some(std::env::current_exe().unwrap()),
            output: Some(std::env::temp_dir().join("unused-tdag-report.json")),
        };
        assert!(Arguments::parse(&[
            "--controller".to_owned(),
            "--manifest".to_owned(),
            "relative-manifest.json".to_owned(),
            "--baseline".to_owned(),
            baseline.to_string_lossy().into_owned(),
            "--measure-process".to_owned(),
            std::env::current_exe()
                .unwrap()
                .to_string_lossy()
                .into_owned(),
            "--output".to_owned(),
            "/tmp/tdag-report.json".to_owned(),
        ])
        .is_err());
        let manifest_hash = term_dag_performance::sha256(&fs::read(&manifest).unwrap());
        let baseline_hash = term_dag_performance::sha256(&fs::read(&baseline).unwrap());
        let mut valid_rows = Vec::new();
        for sample in 0..3 {
            for case in &cases {
                let scenario = term_dag_performance::scenario(case.scenario_id).unwrap();
                let observation =
                    term_dag_performance::expected_production_observation_json(case).unwrap();
                valid_rows.push(ControllerRow {
                    child: child_json(
                        case,
                        sample,
                        &term_dag_performance::fixture_tree_hash_for_descriptor(scenario),
                        &manifest_hash,
                        &baseline_hash,
                        sample + case.requested_jobs,
                        &observation,
                    ),
                    scenario_id: case.scenario_id.to_owned(),
                    case_id: case.case_id.clone(),
                    requested_jobs: case.requested_jobs,
                    inner_elapsed_ns: sample + case.requested_jobs,
                    process_elapsed_seconds: "1.000000000".to_owned(),
                    peak_rss_kib: 2_048 + sample,
                    exit_code: 0,
                });
            }
        }
        let executable = std::env::current_exe().unwrap();
        let report = controller_report(&arguments, &executable, &executable, &valid_rows).unwrap();
        validate_controller_report(&report, &arguments, &executable, &executable).unwrap();
        for invalid in [
            report.replacen("\"schema\":", "\"unknown\":0,\"schema\":", 1),
            report.replacen("\"manifest_sha256\":", "\"baseline_sha256_copy\":", 1),
            report.replacen(
                &format!(
                    "\"source_identity\":\"{}\"",
                    runtime_source_identity(true).unwrap()
                ),
                &format!("\"source_identity\":\"{}\"", "0".repeat(40)),
                1,
            ),
            report.replacen(
                env!("NPA_BUILD_TDAG_RUNNER_SOURCE_SHA256"),
                &"0".repeat(64),
                1,
            ),
            report.replacen(env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256"), &"0".repeat(64), 1),
            report.replacen(&manifest_hash, &"0".repeat(64), 2),
            report.replacen("\"sample_index\":0", "\"sample_index\":1", 1),
            report.replacen("\"summaries\":[", "\"summaries\":[{}", 1),
            report.replacen("{\"schema\"", "{ \"schema\"", 1),
            report.replacen(
                "\"interleave\":\"sample-major-scenario-job-order\"",
                "\"interleave\":\"sample-major-scenario-job-\\u006frder\"",
                1,
            ),
        ] {
            assert!(
                validate_controller_report(&invalid, &arguments, &executable, &executable).is_err()
            );
        }

        let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX")).unwrap();
        assert!(rustc_vv.ends_with('\n'));
        assert!(rustc_vv.lines().any(|line| line.starts_with("host: ")));
        assert!(!env!("NPA_BUILD_TARGET").is_empty());
        assert_eq!(env!("NPA_BUILD_CARGO_LOCK_SHA256").len(), 64);
        assert!(env!("NPA_BUILD_CARGO_LOCK_SHA256")
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f')));
        assert_ne!(env!("NPA_BUILD_CARGO_LOCK_SHA256"), "0".repeat(64));
        assert_eq!(env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256").len(), 64);
        assert_eq!(
            runtime_tdag_source_set_sha256().unwrap(),
            env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256")
        );
        assert!(validate_runtime_build_inputs_against(
            &"0".repeat(64),
            env!("NPA_BUILD_TDAG_SOURCE_SET_SHA256"),
            true,
        )
        .is_err());
        assert_eq!(
            quoted("\0\u{0008}\u{000c}\u{001f}"),
            "\"\\u0000\\u0008\\u000c\\u001f\""
        );
        assert!(validate_runtime_build_inputs_against(
            env!("NPA_BUILD_CARGO_LOCK_SHA256"),
            &"0".repeat(64),
            true,
        )
        .is_err());
        let source_paths = env!("NPA_BUILD_TDAG_SOURCE_SET_PATHS");
        assert!(source_paths.starts_with("Cargo.toml,"));
        assert!(source_paths.contains("crates/npa-api/src/package_verifier.rs"));
        assert!(source_paths.contains("crates/npa-cert/src/kernel.rs"));
        assert!(source_paths.contains("crates/npa-checker-ref/src/lib.rs"));
        assert!(source_paths.contains("crates/npa-frontend/src/elaborator.rs"));
        assert!(source_paths.contains("crates/npa-package/src/lib.rs"));
        assert!(source_paths.contains("crates/npa-kernel/src/env.rs"));
        assert!(source_paths.contains("crates/npa-tactic/src/lib.rs"));
        assert!(source_paths.contains("bench_certificate_term_dag_materialization.rs"));
        assert!(
            env!("NPA_BUILD_SOURCE_IDENTITY") == "unbound"
                || valid_source_identity(env!("NPA_BUILD_SOURCE_IDENTITY"))
        );
        for hash in [
            env!("NPA_BUILD_TDAG_RUNNER_SOURCE_SHA256"),
            env!("NPA_BUILD_TDAG_SUPPORT_SOURCE_SHA256"),
        ] {
            assert_eq!(hash.len(), 64);
            assert!(hash
                .bytes()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f')));
        }
        assert_ne!(
            term_dag_performance::sha256(rustc_vv.as_bytes()),
            term_dag_performance::sha256(env!("NPA_BUILD_RUSTC_VV_HEX").as_bytes())
        );
        assert!(matches!(env!("NPA_BUILD_CARGO_PROFILE"), "dev" | "release"));
        let features = env!("NPA_BUILD_CARGO_FEATURES")
            .split(',')
            .filter(|feature| !feature.is_empty())
            .collect::<Vec<_>>();
        assert!(features
            .iter()
            .all(|feature| matches!(*feature, "default" | "planning-benchmark")));
        assert!(!features.iter().any(|feature| feature.contains('_')));
        assert!(decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX")).is_ok());
        assert!(decode_build_hex("0").is_err());
        assert!(decode_build_hex("GG").is_err());

        let temporary = make_controller_temp_dir().unwrap();
        assert!(canonical_new_output_path(
            &temporary.path().unwrap().join("report.json"),
            "test output",
        )
        .is_ok());
        assert!(canonical_new_output_path(
            &temporary.path().unwrap().join("-report.json"),
            "test output",
        )
        .is_err());
        fs::create_dir(temporary.path().unwrap().join("nested")).unwrap();
        assert!(canonical_new_output_path(
            &temporary
                .path()
                .unwrap()
                .join("nested")
                .join("..")
                .join("report.json"),
            "test output",
        )
        .is_err());
        fs::remove_dir(temporary.path().unwrap().join("nested")).unwrap();
        #[cfg(unix)]
        {
            fs::create_dir(temporary.path().unwrap().join("real-parent")).unwrap();
            std::os::unix::fs::symlink(
                temporary.path().unwrap().join("real-parent"),
                temporary.path().unwrap().join("linked-parent"),
            )
            .unwrap();
            assert!(canonical_new_output_path(
                &temporary
                    .path()
                    .unwrap()
                    .join("linked-parent")
                    .join("report.json"),
                "test output",
            )
            .is_err());
            std::os::unix::fs::symlink("missing", temporary.path().unwrap().join("dangling.json"))
                .unwrap();
            assert!(canonical_new_output_path(
                &temporary.path().unwrap().join("dangling.json"),
                "test output",
            )
            .is_err());
            fs::remove_file(temporary.path().unwrap().join("dangling.json")).unwrap();
            fs::remove_file(temporary.path().unwrap().join("linked-parent")).unwrap();
            fs::remove_dir(temporary.path().unwrap().join("real-parent")).unwrap();
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                fs::symlink_metadata(temporary.path().unwrap())
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o777,
                0o700
            );
        }
        let path = temporary.path().unwrap().to_owned();
        temporary.cleanup_exact(BTreeSet::new()).unwrap();
        assert!(!path.exists());

        let suspicious = make_controller_temp_dir().unwrap();
        fs::create_dir(suspicious.path().unwrap().join("nested")).unwrap();
        assert!(suspicious
            .0
            .as_ref()
            .unwrap()
            .remove_allowed_root(&controller_temp_catalog())
            .is_err());
        fs::remove_dir(suspicious.path().unwrap().join("nested")).unwrap();
        suspicious.cleanup_exact(BTreeSet::new()).unwrap();

        #[cfg(unix)]
        {
            let symlinked = make_controller_temp_dir().unwrap();
            std::os::unix::fs::symlink("missing", symlinked.path().unwrap().join("link")).unwrap();
            assert!(symlinked
                .0
                .as_ref()
                .unwrap()
                .remove_allowed_root(&controller_temp_catalog())
                .is_err());
            fs::remove_file(symlinked.path().unwrap().join("link")).unwrap();
            symlinked.cleanup_exact(BTreeSet::new()).unwrap();

            let renamed = make_controller_temp_dir().unwrap();
            let original = renamed.path().unwrap().to_owned();
            let relocated = original.with_extension("relocated");
            fs::write(original.join("sentinel"), b"keep").unwrap();
            fs::rename(&original, &relocated).unwrap();
            fs::create_dir(&original).unwrap();
            drop(renamed);
            assert_eq!(fs::read(relocated.join("sentinel")).unwrap(), b"keep");
            assert!(original.is_dir());
            fs::remove_dir(original).unwrap();
            fs::remove_file(relocated.join("sentinel")).unwrap();
            fs::remove_dir(relocated).unwrap();
        }
    }

    #[test]
    fn term_dag_controller_temp_directory_is_private_closed_and_replacement_safe() {
        let temporary = make_controller_temp_dir().unwrap();
        let path = temporary.path().unwrap().to_owned();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                fs::symlink_metadata(&path).unwrap().permissions().mode() & 0o777,
                0o700
            );
        }
        temporary.cleanup_exact(BTreeSet::new()).unwrap();
        assert!(!path.exists());

        let executable_swap = make_controller_temp_dir().unwrap();
        let executable = std::env::current_exe().unwrap();
        let snapshot = executable_swap
            .create_executable_snapshot(
                Path::new("runner"),
                &executable,
                MAX_EXECUTABLE_BYTES,
                "TDAG swap probe",
            )
            .unwrap();
        let path = snapshot.path().to_owned();
        let relocated = path.with_extension("opened");
        fs::rename(&path, &relocated).unwrap();
        fs::write(&path, b"replacement").unwrap();
        assert!(snapshot.verify().is_err());
        fs::remove_file(&path).unwrap();
        fs::rename(&relocated, &path).unwrap();
        drop(snapshot);
        executable_swap
            .cleanup_exact(BTreeSet::from([PathBuf::from("runner")]))
            .unwrap();

        let input_swap = make_controller_temp_dir().unwrap();
        let input = input_swap
            .create_input_snapshot(Path::new("manifest.json"), b"original\n")
            .unwrap();
        assert_eq!(
            input.read_all_bounded(MAX_DESCRIPTOR_BYTES).unwrap(),
            b"original\n"
        );
        let path = input_swap.path().unwrap().join("manifest.json");
        let relocated = path.with_extension("opened");
        fs::rename(&path, &relocated).unwrap();
        fs::write(&path, b"replacement\n").unwrap();
        assert!(input.read_all_bounded(MAX_DESCRIPTOR_BYTES).is_err());
        fs::remove_file(&path).unwrap();
        fs::rename(&relocated, &path).unwrap();
        drop(input);
        input_swap
            .cleanup_exact(BTreeSet::from([PathBuf::from("manifest.json")]))
            .unwrap();

        let suspicious = make_controller_temp_dir().unwrap();
        fs::create_dir(suspicious.path().unwrap().join("nested")).unwrap();
        assert!(suspicious
            .0
            .as_ref()
            .unwrap()
            .remove_allowed_root(&controller_temp_catalog())
            .is_err());
        fs::remove_dir(suspicious.path().unwrap().join("nested")).unwrap();
        suspicious.cleanup_exact(BTreeSet::new()).unwrap();

        #[cfg(unix)]
        {
            let renamed = make_controller_temp_dir().unwrap();
            let original = renamed.path().unwrap().to_owned();
            let relocated = original.with_extension("relocated-exact-test");
            fs::write(original.join("sentinel"), b"keep").unwrap();
            fs::rename(&original, &relocated).unwrap();
            fs::create_dir(&original).unwrap();
            drop(renamed);
            assert_eq!(fs::read(relocated.join("sentinel")).unwrap(), b"keep");
            assert!(original.is_dir());
            fs::remove_dir(original).unwrap();
            fs::remove_file(relocated.join("sentinel")).unwrap();
            fs::remove_dir(relocated).unwrap();
        }
    }
}
