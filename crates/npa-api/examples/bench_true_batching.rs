//! Advisory elapsed-time harness for proof-authoring true batching.

#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/runtime_source_set.rs"]
mod runtime_source_set;

use std::{
    collections::BTreeSet,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use closed_private_tree::read_absolute_regular_file;
use npa_api::{
    create_machine_session, machine_tactic_batch_response_canonical_json,
    run_machine_tactic_batch_request, JsonDocument, JsonMember, JsonValue,
};
use npa_cert::{
    check_core_decl_candidates, check_core_decl_candidates_with_measurement, CandidateBatch,
    CandidateBatchResult, CandidateStatus, CoreDeclCandidate, ProducerBatchMeasurement,
    ProducerLimits,
};
use npa_kernel::{Decl, Expr, Level};
use sha2::{Digest, Sha256};

const CANDIDATE_COUNTS: [usize; 4] = [1, 8, 32, 256];
const STATE_FIXTURES: [(&str, usize); 3] = [("small", 0), ("medium", 8), ("large", 24)];
const RUN_SCHEMA: &str = "npa.true-batching.elapsed.v0.2";

fn main() {
    if let Err(error) = run(std::env::args().skip(1).collect()) {
        let _ = writeln!(
            std::io::stderr().lock(),
            "true-batching benchmark: {}",
            error.replace(['\n', '\r'], " ")
        );
        std::process::exit(2);
    }
}

fn run(arguments: Vec<String>) -> Result<(), String> {
    let args = Args::parse(arguments)?;
    let build = validate_runtime_build_identity(&args.source_identity)?;
    if let Some(path) = args.validate_report.as_deref() {
        let source = read_published_report(path)?;
        return validate_report(&source, &args, &build);
    }
    let mut results = Vec::new();

    for (fixture, let_depth) in STATE_FIXTURES {
        for candidate_count in CANDIDATE_COUNTS {
            let samples_ns = sample_elapsed(args.warmup, args.samples, || {
                run_machine_tactic_once(let_depth, candidate_count)
            })?;
            results.push(ScenarioResult::new(
                "machine-tactic",
                fixture,
                candidate_count,
                samples_ns,
                None,
            ));
        }
    }

    for candidate_count in CANDIDATE_COUNTS {
        let samples_ns = sample_elapsed(args.warmup, args.samples, || {
            run_certificate_producer_once(candidate_count)
        })?;
        let measurement = measure_certificate_producer_once(candidate_count)?;
        results.push(ScenarioResult::new(
            "certificate-producer",
            "accepted-chain",
            candidate_count,
            samples_ns,
            Some(measurement),
        ));
    }

    let scenarios = results
        .iter()
        .map(ScenarioResult::json)
        .collect::<Vec<_>>()
        .join(",");
    let report = format!(
        "{{\"schema\":\"{RUN_SCHEMA}\",\"trusted\":false,\
         \"proof_evidence\":false,\"source_identity\":\"{}\",\
         \"build_identity\":{{\"executable_sha256\":\"{}\",\"cargo_lock_sha256\":\"{}\",\
         \"true_batching_source_set_sha256\":\"{}\",\"true_batching_source_set_paths\":{},\
         \"rustc_vv\":\"{}\",\"target\":\"{}\",\"cargo_profile\":\"{}\",\
         \"cargo_features\":{},\"rustflags\":\"{}\"}},\
         \"warmup\":{},\"sample_count\":{},\"elapsed_gate\":\"advisory\",\
         \"status\":\"passed\",\"scenarios\":[{}]}}",
        json_escape(&args.source_identity),
        build.executable_sha256,
        build.cargo_lock_sha256,
        build.source_set_sha256,
        json_string_array(&build.source_set_paths),
        json_escape(&build.rustc_vv),
        json_escape(env!("NPA_BUILD_TARGET")),
        env!("NPA_BUILD_CARGO_PROFILE"),
        json_string_array(&embedded_build_features()),
        json_escape(&decode_build_hex_result(env!("NPA_BUILD_RUSTFLAGS_HEX"))?),
        args.warmup,
        args.samples,
        scenarios,
    );
    validate_report(&report, &args, &build)?;
    writeln!(std::io::stdout().lock(), "{report}").map_err(|error| format!("write report: {error}"))
}

fn run_machine_tactic_once(let_depth: usize, candidate_count: usize) -> Result<(), String> {
    let theorem_type = theorem_type_fixture(let_depth);
    let mut session = create_machine_session(&minimal_session_json(&theorem_type))
        .map_err(|error| format!("machine session fixture failed: {error:?}"))?
        .session;
    let candidates = (0..candidate_count)
        .map(|index| {
            format!(
                r#"{{"candidate_id":"c{index}","candidate":{{"kind":"exact","term":{{"source":"Prop"}}}}}}"#
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let request = batch_json(
        &session,
        session.initial_snapshot.state_fingerprint,
        &format!("[{candidates}]"),
    );
    let response = run_machine_tactic_batch_request(&request, &mut session)
        .map_err(|error| format!("machine tactic benchmark failed: {error:?}"))?;
    let response_json = machine_tactic_batch_response_canonical_json(&response);
    if !response_json.starts_with(r#"{"status":"ok""#) {
        return Err("machine tactic fixture did not complete successfully".to_owned());
    }
    std::hint::black_box(response_json);
    Ok(())
}

fn run_certificate_producer_once(candidate_count: usize) -> Result<(), String> {
    let result = check_core_decl_candidates(certificate_producer_batch(candidate_count))
        .map_err(|error| format!("producer batch fixture failed: {error:?}"))?;
    validate_certificate_producer_result(&result, candidate_count)?;
    std::hint::black_box(result);
    Ok(())
}

fn measure_certificate_producer_once(
    candidate_count: usize,
) -> Result<ProducerBatchMeasurement, String> {
    let batch = certificate_producer_batch(candidate_count);
    let mut measurement = ProducerBatchMeasurement::default();
    let result = check_core_decl_candidates_with_measurement(batch, &mut measurement)
        .map_err(|error| format!("measured producer batch fixture failed: {error:?}"))?;
    validate_certificate_producer_result(&result, candidate_count)?;
    std::hint::black_box(result);
    Ok(measurement)
}

fn certificate_producer_batch(candidate_count: usize) -> CandidateBatch<'static> {
    let candidates = (0..candidate_count)
        .map(|index| CoreDeclCandidate {
            declaration: Decl::Axiom {
                name: format!("Bench.P{index}"),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            },
        })
        .collect();
    CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates,
        limits: ProducerLimits {
            max_declarations: 256,
            max_expr_nodes: 32,
            max_level_nodes: 32,
            max_name_components: 8,
            max_reduction_steps: 10_000,
            max_conversion_steps: 10_000,
        },
    }
}

fn validate_certificate_producer_result(
    result: &CandidateBatchResult,
    candidate_count: usize,
) -> Result<(), String> {
    if result.statuses.len() != candidate_count
        || !result
            .statuses
            .iter()
            .all(|status| matches!(status, CandidateStatus::Accepted(_)))
    {
        return Err("producer fixture did not accept the exact candidate catalog".to_owned());
    }
    Ok(())
}

fn sample_elapsed(
    warmup: usize,
    samples: usize,
    mut run_once: impl FnMut() -> Result<(), String>,
) -> Result<Vec<u64>, String> {
    for _ in 0..warmup {
        run_once()?;
    }
    (0..samples)
        .map(|_| {
            let started = Instant::now();
            run_once()?;
            Ok(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX))
        })
        .collect()
}

fn theorem_type_fixture(let_depth: usize) -> String {
    let mut source = "Type 0".to_owned();
    for index in (0..let_depth).rev() {
        source = format!("let BenchA{index} : Type 1 := Type 0 in {source}");
    }
    source
}

fn minimal_session_json(theorem_type: &str) -> String {
    format!(
        r#"{{
          "protocol_version":"npa.machine-api.v2",
          "root":{{
            "module":"Scratch",
            "theorem_name":"Scratch.t",
            "source_index":0,
            "universe_params":[],
            "theorem_type":{{"format":"machine_surface_v1","source":"{theorem_type}"}}
          }},
          "import_closure":[],
          "imports":[],
          "checked_current_decls":[],
          "options":{{
            "kernel_check_profile":"npa.kernel.v0.1.builtin-nat-eq-rec",
            "allow_axioms":[],
            "tactic_options":{{
              "simp_rules":[],
              "eq_family":null,
              "nat_family":null,
              "max_simp_rewrite_steps":100,
              "max_open_goals":32,
              "max_metas":64
            }}
          }}
        }}"#
    )
}

fn batch_json(
    session: &npa_api::MachineProofSession,
    state_fingerprint: npa_cert::Hash,
    candidates: &str,
) -> String {
    format!(
        r#"{{
          "session_id":"{}",
          "snapshot_id":"{}",
          "state_fingerprint":"{}",
          "goal_id":"g0",
          "candidates":{},
          "deterministic_budget":{{
            "max_tactic_steps":64,
            "max_whnf_steps":10000,
            "max_conversion_steps":10000,
            "max_rewrite_steps":100,
            "max_meta_allocations":8,
            "max_expr_nodes":20000
          }},
          "batch_policy":{{
            "max_evaluated_candidates":256,
            "stop_after_successes":256,
            "stop_after_failures":256
          }}
        }}"#,
        session.session_id.wire(),
        session.initial_snapshot.snapshot_id.wire(),
        npa_api::format_hash_string(&state_fingerprint),
        candidates,
    )
}

struct Args {
    source_identity: String,
    warmup: usize,
    samples: usize,
    validate_report: Option<PathBuf>,
}

impl Args {
    fn parse(arguments: Vec<String>) -> Result<Self, String> {
        let mut source_identity = None;
        let mut warmup = 3;
        let mut samples = 9;
        let mut validate_report = None;
        let mut args = arguments.into_iter();
        let mut seen = BTreeSet::new();
        while let Some(flag) = args.next() {
            if !seen.insert(flag.clone()) {
                return Err(format!("duplicate option {flag}"));
            }
            let value = args
                .next()
                .ok_or_else(|| format!("missing value for {flag}"))?;
            match flag.as_str() {
                "--source-identity" => source_identity = Some(value),
                "--warmup" => warmup = value.parse().map_err(|_| "--warmup must be an integer")?,
                "--samples" => {
                    samples = value.parse().map_err(|_| "--samples must be an integer")?
                }
                "--validate-report" => validate_report = Some(PathBuf::from(value)),
                _ => return Err(format!("unknown option {flag}")),
            }
        }
        if samples == 0 {
            return Err("--samples must be positive".to_owned());
        }
        let source_identity = source_identity.ok_or("--source-identity is required")?;
        if !valid_source_identity(&source_identity) {
            return Err(
                "--source-identity must be a lowercase 40-digit Git object id with optional -dirty suffix"
                    .to_owned(),
            );
        }
        Ok(Self {
            source_identity,
            warmup,
            samples,
            validate_report,
        })
    }
}

fn read_published_report(path: &Path) -> Result<String, String> {
    let source = String::from_utf8(read_absolute_regular_file(
        path,
        64 * 1024 * 1024,
        "true-batching report",
    )?)
    .map_err(|_| "true-batching report must be UTF-8".to_owned())?;
    let body = source
        .strip_suffix('\n')
        .ok_or("published report must end with exactly one LF")?;
    if body.ends_with(['\n', '\r']) {
        return Err("published report must end with exactly one LF".to_owned());
    }
    Ok(body.to_owned())
}

struct BuildIdentity {
    executable_sha256: String,
    cargo_lock_sha256: String,
    source_set_sha256: String,
    source_set_paths: Vec<String>,
    rustc_vv: String,
}

fn validate_runtime_build_identity(source_identity: &str) -> Result<BuildIdentity, String> {
    let embedded_source_identity = env!("NPA_BUILD_SOURCE_IDENTITY");
    if embedded_source_identity == "unbound" {
        return Err("true-batching evidence requires a build-bound source identity".to_owned());
    }
    if source_identity != embedded_source_identity {
        return Err(format!(
            "requested source identity {source_identity} differs from build identity {embedded_source_identity}"
        ));
    }
    let runtime_source_identity = current_source_identity()?;
    if runtime_source_identity != embedded_source_identity {
        return Err(format!(
            "runtime source identity {runtime_source_identity} differs from build identity {embedded_source_identity}"
        ));
    }
    let workspace = canonical_workspace_root()?;
    let cargo_lock_sha256 =
        hash_canonical_regular_file(&workspace.join("Cargo.lock"), "Cargo.lock")?;
    if cargo_lock_sha256 != env!("NPA_BUILD_CARGO_LOCK_SHA256") {
        return Err("runtime Cargo.lock differs from the build input".to_owned());
    }
    let source_set_paths =
        parse_source_set_paths(env!("NPA_BUILD_TRUE_BATCHING_SOURCE_SET_PATHS"))?;
    let source_set_sha256 = runtime_source_set::validate_runtime_source_set(
        &workspace,
        env!("NPA_BUILD_TRUE_BATCHING_SOURCE_SET_PATHS"),
        b"npa-true-batching-source-set-v1\0",
        env!("NPA_BUILD_TRUE_BATCHING_SOURCE_SET_SHA256"),
        "true-batching",
    )?
    .trim_start_matches("sha256:")
    .to_owned();
    if source_set_sha256 != env!("NPA_BUILD_TRUE_BATCHING_SOURCE_SET_SHA256") {
        return Err("runtime true-batching source set differs from the build inputs".to_owned());
    }
    let executable =
        std::env::current_exe().map_err(|error| format!("resolve current executable: {error}"))?;
    let executable_sha256 = hash_canonical_regular_file(&executable, "current executable")?;
    let rustc_vv = decode_build_hex_result(env!("NPA_BUILD_RUSTC_VV_HEX"))?;
    if !rustc_vv.ends_with('\n') {
        return Err("embedded rustc -Vv must retain its terminal newline".to_owned());
    }
    if env!("NPA_BUILD_TARGET").is_empty() || env!("NPA_BUILD_CARGO_PROFILE").is_empty() {
        return Err("embedded target/profile must be nonempty".to_owned());
    }
    let features = embedded_build_features();
    if features.windows(2).any(|pair| pair[0] >= pair[1])
        || features
            .iter()
            .any(|feature| !matches!(feature.as_str(), "default" | "planning-benchmark"))
    {
        return Err("embedded Cargo features are not canonical manifest feature names".to_owned());
    }
    Ok(BuildIdentity {
        executable_sha256,
        cargo_lock_sha256,
        source_set_sha256,
        source_set_paths,
        rustc_vv,
    })
}

fn current_source_identity() -> Result<String, String> {
    let head = command_stdout("/usr/bin/git", &["rev-parse", "HEAD"])?;
    if !valid_source_identity(&head) || head.ends_with("-dirty") {
        return Err("Git HEAD is not a lowercase 40-digit object id".to_owned());
    }
    let status = command_stdout(
        "/usr/bin/git",
        &["status", "--porcelain", "--untracked-files=normal"],
    )?;
    Ok(if status.is_empty() {
        head
    } else {
        format!("{head}-dirty")
    })
}

fn command_stdout(program: &str, arguments: &[&str]) -> Result<String, String> {
    let output = Command::new(program)
        .args(arguments)
        .current_dir(canonical_workspace_root()?)
        .output()
        .map_err(|error| format!("run {program}: {error}"))?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!(
            "{program} failed or wrote stderr: status={:?}, stderr={}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map(|source| source.trim_end().to_owned())
        .map_err(|error| format!("{program} output is not UTF-8: {error}"))
}

fn canonical_workspace_root() -> Result<PathBuf, String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    std::fs::canonicalize(&path)
        .map_err(|error| format!("canonicalize workspace {}: {error}", path.display()))
}

fn hash_canonical_regular_file(path: &Path, label: &str) -> Result<String, String> {
    read_absolute_regular_file(path, 512 * 1024 * 1024, label).map(|bytes| sha256_hex(&bytes))
}

fn parse_source_set_paths(source: &str) -> Result<Vec<String>, String> {
    let paths = source.split(',').map(str::to_owned).collect::<Vec<_>>();
    if paths.is_empty()
        || paths.iter().any(|path| {
            path.is_empty()
                || Path::new(path).is_absolute()
                || path
                    .split('/')
                    .any(|component| matches!(component, "" | "." | ".."))
        })
        || paths.windows(2).any(|pair| pair[0] >= pair[1])
    {
        return Err("embedded true-batching source paths are not canonical".to_owned());
    }
    Ok(paths)
}

fn embedded_build_features() -> Vec<String> {
    env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(str::to_owned)
        .collect()
}

fn json_string_array(values: &[String]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!("\"{}\"", json_escape(value)))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn validate_report(source: &str, args: &Args, build: &BuildIdentity) -> Result<(), String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid report JSON at {}", error.offset))?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "trusted",
            "proof_evidence",
            "source_identity",
            "build_identity",
            "warmup",
            "sample_count",
            "elapsed_gate",
            "status",
            "scenarios",
        ],
        "report",
    )?;
    expect_string(root[0].value(), RUN_SCHEMA, "report.schema")?;
    expect_bool(root[1].value(), false, "report.trusted")?;
    expect_bool(root[2].value(), false, "report.proof_evidence")?;
    expect_string(
        root[3].value(),
        &args.source_identity,
        "report.source_identity",
    )?;
    let identity = exact_object(
        root[4].value(),
        &[
            "executable_sha256",
            "cargo_lock_sha256",
            "true_batching_source_set_sha256",
            "true_batching_source_set_paths",
            "rustc_vv",
            "target",
            "cargo_profile",
            "cargo_features",
            "rustflags",
        ],
        "report.build_identity",
    )?;
    for (index, expected, label) in [
        (0, build.executable_sha256.as_str(), "executable_sha256"),
        (1, build.cargo_lock_sha256.as_str(), "cargo_lock_sha256"),
        (2, build.source_set_sha256.as_str(), "source_set_sha256"),
        (4, build.rustc_vv.as_str(), "rustc_vv"),
        (5, env!("NPA_BUILD_TARGET"), "target"),
        (6, env!("NPA_BUILD_CARGO_PROFILE"), "cargo_profile"),
    ] {
        expect_string(
            identity[index].value(),
            expected,
            &format!("report.build_identity.{label}"),
        )?;
    }
    validate_string_array(identity[3].value(), &build.source_set_paths, "source paths")?;
    validate_string_array(
        identity[7].value(),
        &embedded_build_features(),
        "Cargo features",
    )?;
    expect_string(
        identity[8].value(),
        &decode_build_hex_result(env!("NPA_BUILD_RUSTFLAGS_HEX"))?,
        "report.build_identity.rustflags",
    )?;
    expect_u64(
        root[5].value(),
        u64::try_from(args.warmup).map_err(|_| "warmup overflow")?,
        "report.warmup",
    )?;
    expect_u64(
        root[6].value(),
        u64::try_from(args.samples).map_err(|_| "sample count overflow")?,
        "report.sample_count",
    )?;
    expect_string(root[7].value(), "advisory", "report.elapsed_gate")?;
    expect_string(root[8].value(), "passed", "report.status")?;
    let scenarios = root[9]
        .value()
        .array_elements()
        .ok_or("report.scenarios must be an array")?;
    if scenarios.len() != 16 {
        return Err(format!(
            "report.scenarios must contain 16 rows, got {}",
            scenarios.len()
        ));
    }
    for (index, scenario) in scenarios.iter().enumerate() {
        let fields = exact_object(
            scenario,
            &[
                "path",
                "fixture",
                "candidate_count",
                "samples_ns",
                "elapsed_summary_ns",
                "work_counters",
            ],
            &format!("report.scenarios[{index}]"),
        )?;
        let (expected_path, expected_fixture, expected_count) = if index < 12 {
            let fixture_index = index / CANDIDATE_COUNTS.len();
            (
                "machine-tactic",
                STATE_FIXTURES[fixture_index].0,
                CANDIDATE_COUNTS[index % CANDIDATE_COUNTS.len()],
            )
        } else {
            (
                "certificate-producer",
                "accepted-chain",
                CANDIDATE_COUNTS[index - 12],
            )
        };
        expect_string(fields[0].value(), expected_path, "scenario.path")?;
        expect_string(fields[1].value(), expected_fixture, "scenario.fixture")?;
        expect_u64(
            fields[2].value(),
            u64::try_from(expected_count).map_err(|_| "candidate count overflow")?,
            "scenario.candidate_count",
        )?;
        let samples = fields[3]
            .value()
            .array_elements()
            .ok_or("scenario.samples_ns must be an array")?;
        let samples = samples
            .iter()
            .map(|sample| {
                sample
                    .number_raw()
                    .and_then(|raw| raw.parse::<u64>().ok())
                    .ok_or_else(|| "scenario.samples_ns must contain u64 values".to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        if samples.len() != args.samples {
            return Err("scenario.samples_ns shape mismatch".to_owned());
        }
        let elapsed = exact_object(
            fields[4].value(),
            &["median", "median_absolute_deviation", "minimum", "maximum"],
            "scenario.elapsed_summary_ns",
        )?;
        let expected_elapsed = elapsed_statistics(&samples);
        for (field, expected, label) in [
            (elapsed[0].value(), expected_elapsed.median, "median"),
            (
                elapsed[1].value(),
                expected_elapsed.median_absolute_deviation,
                "median_absolute_deviation",
            ),
            (elapsed[2].value(), expected_elapsed.minimum, "minimum"),
            (elapsed[3].value(), expected_elapsed.maximum, "maximum"),
        ] {
            expect_u64(
                field,
                expected,
                &format!("scenario.elapsed_summary_ns.{label}"),
            )?;
        }
        if expected_path == "machine-tactic" {
            if fields[5].value().kind() != npa_api::JsonValueKind::Null {
                return Err("machine scenario work_counters must be null".to_owned());
            }
        } else {
            let counters = exact_object(
                fields[5].value(),
                &[
                    "prepared_chains",
                    "name_index_rebuilds",
                    "environment_clones",
                    "copied_prefix_elements",
                    "canonical_bytes_hashed",
                    "candidates_evaluated",
                    "candidates_accepted",
                    "candidates_rejected",
                ],
                "scenario.work_counters",
            )?;
            let expected = measure_certificate_producer_once(expected_count)?;
            for (index, expected, label) in [
                (0, expected.prepared_chains, "prepared_chains"),
                (1, expected.name_index_rebuilds, "name_index_rebuilds"),
                (2, expected.environment_clones, "environment_clones"),
                (3, expected.copied_prefix_elements, "copied_prefix_elements"),
                (4, expected.canonical_bytes_hashed, "canonical_bytes_hashed"),
                (5, expected.candidates_evaluated, "candidates_evaluated"),
                (6, expected.candidates_accepted, "candidates_accepted"),
                (7, expected.candidates_rejected, "candidates_rejected"),
            ] {
                expect_u64(counters[index].value(), expected, label)?;
            }
        }
    }
    Ok(())
}

fn exact_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    keys: &[&str],
    path: &str,
) -> Result<&'value [JsonMember<'source>], String> {
    let members = value
        .object_members()
        .ok_or_else(|| format!("{path} must be an object"))?;
    if members.iter().map(JsonMember::key).collect::<Vec<_>>() != keys {
        return Err(format!("{path} keys/order mismatch"));
    }
    Ok(members)
}

fn expect_string(value: &JsonValue<'_>, expected: &str, path: &str) -> Result<(), String> {
    if value.string_value() != Some(expected) {
        return Err(format!("{path} mismatch"));
    }
    Ok(())
}

fn expect_bool(value: &JsonValue<'_>, expected: bool, path: &str) -> Result<(), String> {
    if value.bool_value() != Some(expected) {
        return Err(format!("{path} mismatch"));
    }
    Ok(())
}

fn expect_u64(value: &JsonValue<'_>, expected: u64, path: &str) -> Result<(), String> {
    if value.number_raw().and_then(|raw| raw.parse::<u64>().ok()) != Some(expected) {
        return Err(format!("{path} mismatch"));
    }
    Ok(())
}

fn validate_string_array(
    value: &JsonValue<'_>,
    expected: &[String],
    path: &str,
) -> Result<(), String> {
    let values = value
        .array_elements()
        .ok_or_else(|| format!("{path} must be an array"))?;
    if values.len() != expected.len()
        || values
            .iter()
            .zip(expected)
            .any(|(actual, expected)| actual.string_value() != Some(expected))
    {
        return Err(format!("{path} mismatch"));
    }
    Ok(())
}

struct ScenarioResult {
    path: &'static str,
    fixture: &'static str,
    candidate_count: usize,
    samples_ns: Vec<u64>,
    elapsed: ElapsedStatistics,
    producer_measurement: Option<ProducerBatchMeasurement>,
}

impl ScenarioResult {
    fn new(
        path: &'static str,
        fixture: &'static str,
        candidate_count: usize,
        samples_ns: Vec<u64>,
        producer_measurement: Option<ProducerBatchMeasurement>,
    ) -> Self {
        let elapsed = elapsed_statistics(&samples_ns);
        Self {
            path,
            fixture,
            candidate_count,
            samples_ns,
            elapsed,
            producer_measurement,
        }
    }

    fn json(&self) -> String {
        let samples = self
            .samples_ns
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let work_counters = self.producer_measurement.map_or_else(
            || "null".to_owned(),
            |measurement| {
                format!(
                    "{{\"prepared_chains\":{},\"name_index_rebuilds\":{},\
                     \"environment_clones\":{},\"copied_prefix_elements\":{},\
                     \"canonical_bytes_hashed\":{},\"candidates_evaluated\":{},\
                     \"candidates_accepted\":{},\"candidates_rejected\":{}}}",
                    measurement.prepared_chains,
                    measurement.name_index_rebuilds,
                    measurement.environment_clones,
                    measurement.copied_prefix_elements,
                    measurement.canonical_bytes_hashed,
                    measurement.candidates_evaluated,
                    measurement.candidates_accepted,
                    measurement.candidates_rejected,
                )
            },
        );
        format!(
            "{{\"path\":\"{}\",\"fixture\":\"{}\",\"candidate_count\":{},\
             \"samples_ns\":[{}],\"elapsed_summary_ns\":{{\"median\":{},\
             \"median_absolute_deviation\":{},\"minimum\":{},\"maximum\":{}}},\
             \"work_counters\":{}}}",
            self.path,
            self.fixture,
            self.candidate_count,
            samples,
            self.elapsed.median,
            self.elapsed.median_absolute_deviation,
            self.elapsed.minimum,
            self.elapsed.maximum,
            work_counters,
        )
    }
}

struct ElapsedStatistics {
    median: u64,
    median_absolute_deviation: u64,
    minimum: u64,
    maximum: u64,
}

fn elapsed_statistics(samples: &[u64]) -> ElapsedStatistics {
    debug_assert!(!samples.is_empty(), "sample count is validated as positive");
    let median_ns = median(samples);
    let deviations = samples
        .iter()
        .map(|sample| sample.abs_diff(median_ns))
        .collect::<Vec<_>>();
    ElapsedStatistics {
        median: median_ns,
        median_absolute_deviation: median(&deviations),
        minimum: samples.iter().copied().min().unwrap_or(0),
        maximum: samples.iter().copied().max().unwrap_or(0),
    }
}

fn median(values: &[u64]) -> u64 {
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let middle = sorted.len() / 2;
    if sorted.len() % 2 == 1 {
        sorted[middle]
    } else {
        sorted[middle - 1] / 2
            + sorted[middle] / 2
            + (sorted[middle - 1] % 2 + sorted[middle] % 2) / 2
    }
}

fn json_escape(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                let _ = write!(&mut output, "\\u{:04x}", u32::from(character));
            }
            character => output.push(character),
        }
    }
    output
}

fn valid_source_identity(value: &str) -> bool {
    let object_id = value.strip_suffix("-dirty").unwrap_or(value);
    object_id.len() == 40
        && object_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn decode_build_hex_result(encoded: &str) -> Result<String, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("build metadata hex has odd length".to_owned());
    }
    let bytes = encoded
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok((hex_digit(pair[0])? << 4) | hex_digit(pair[1])?))
        .collect::<Result<Vec<_>, String>>()?;
    String::from_utf8(bytes).map_err(|_| "embedded build metadata is not UTF-8".to_owned())
}

fn hex_digit(value: u8) -> Result<u8, String> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err("build metadata contains invalid hex".to_owned()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn true_batching_arguments_are_controlled() {
        assert!(Args::parse(vec![]).is_err());
        assert!(Args::parse(vec!["--unknown".to_owned(), "x".to_owned()]).is_err());
        assert!(Args::parse(vec!["--warmup".to_owned()]).is_err());
        assert!(Args::parse(vec![
            "--source-identity".to_owned(),
            "a".repeat(40),
            "--samples".to_owned(),
            "zero".to_owned(),
        ])
        .is_err());
        assert!(Args::parse(vec!["--source-identity".to_owned(), "a".repeat(64),]).is_err());
        assert!(Args::parse(vec![
            "--source-identity".to_owned(),
            "a".repeat(40),
            "--samples".to_owned(),
            "3".to_owned(),
            "--samples".to_owned(),
            "4".to_owned(),
        ])
        .is_err());
        assert!(Args::parse(vec![
            "--source-identity".to_owned(),
            "a".repeat(40),
            "--samples".to_owned(),
            "0".to_owned(),
        ])
        .is_err());
        assert!(decode_build_hex_result("0").is_err());
        assert!(decode_build_hex_result("gg").is_err());
        assert_eq!(
            json_escape("\0\u{0008}\u{000c}\u{001f}"),
            "\\u0000\\u0008\\u000c\\u001f"
        );
        let escaped = format!("\"{}\"", json_escape("a\u{001f}b"));
        assert_eq!(
            JsonDocument::parse(&escaped).unwrap().root().string_value(),
            Some("a\u{001f}b")
        );
    }

    #[test]
    fn true_batching_build_identity_and_strict_report() {
        let source_identity = env!("NPA_BUILD_SOURCE_IDENTITY");
        if source_identity == "unbound" {
            assert!(validate_runtime_build_identity(source_identity).is_err());
            return;
        }
        let build = validate_runtime_build_identity(source_identity).unwrap();
        assert_eq!(build.cargo_lock_sha256, env!("NPA_BUILD_CARGO_LOCK_SHA256"));
        assert_eq!(
            build.source_set_sha256,
            env!("NPA_BUILD_TRUE_BATCHING_SOURCE_SET_SHA256")
        );
        assert!(build
            .source_set_paths
            .starts_with(&["Cargo.toml".to_owned()]));
        assert!(build
            .source_set_paths
            .iter()
            .any(|path| path.ends_with("bench_true_batching.rs")));
        assert!(build.rustc_vv.ends_with('\n'));
        assert_ne!(
            sha256_hex(build.rustc_vv.as_bytes()),
            sha256_hex(env!("NPA_BUILD_RUSTC_VV_HEX").as_bytes())
        );
    }

    #[test]
    fn true_batching_closed_report_parser() {
        let args = Args {
            source_identity: "a".repeat(40),
            warmup: 1,
            samples: 3,
            validate_report: None,
        };
        let build = BuildIdentity {
            executable_sha256: "b".repeat(64),
            cargo_lock_sha256: "c".repeat(64),
            source_set_sha256: "d".repeat(64),
            source_set_paths: vec!["Cargo.toml".to_owned()],
            rustc_vv: "rustc 1.0\nhost: test\n".to_owned(),
        };
        let make_result = |path, fixture, count, counters| {
            ScenarioResult::new(path, fixture, count, vec![1, 2, 3], counters)
        };
        let mut results = Vec::new();
        for (fixture, _) in STATE_FIXTURES {
            for count in CANDIDATE_COUNTS {
                results.push(make_result("machine-tactic", fixture, count, None));
            }
        }
        for count in CANDIDATE_COUNTS {
            results.push(make_result(
                "certificate-producer",
                "accepted-chain",
                count,
                Some(measure_certificate_producer_once(count).unwrap()),
            ));
        }
        let scenarios = results
            .iter()
            .map(ScenarioResult::json)
            .collect::<Vec<_>>()
            .join(",");
        let source = format!(
            "{{\"schema\":\"{RUN_SCHEMA}\",\"trusted\":false,\"proof_evidence\":false,\"source_identity\":\"{}\",\"build_identity\":{{\"executable_sha256\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"true_batching_source_set_sha256\":\"{}\",\"true_batching_source_set_paths\":[\"Cargo.toml\"],\"rustc_vv\":\"rustc 1.0\\nhost: test\\n\",\"target\":\"{}\",\"cargo_profile\":\"{}\",\"cargo_features\":{},\"rustflags\":\"{}\"}},\"warmup\":1,\"sample_count\":3,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"scenarios\":[{}]}}",
            args.source_identity,
            build.executable_sha256,
            build.cargo_lock_sha256,
            build.source_set_sha256,
            env!("NPA_BUILD_TARGET"),
            env!("NPA_BUILD_CARGO_PROFILE"),
            json_string_array(&embedded_build_features()),
            json_escape(&decode_build_hex_result(env!("NPA_BUILD_RUSTFLAGS_HEX")).unwrap()),
            scenarios,
        );
        validate_report(&source, &args, &build).unwrap();
        for invalid in [
            source.replacen("\"schema\":", "\"unknown\":0,\"schema\":", 1),
            source.replacen(&build.cargo_lock_sha256, &"0".repeat(64), 1),
            source.replacen(&build.source_set_sha256, &"0".repeat(64), 1),
            source.replacen("\"candidate_count\":1", "\"candidate_count\":8", 1),
            format!("{source}x"),
        ] {
            assert!(validate_report(&invalid, &args, &build).is_err());
        }

        let root = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("npa-true-batching-report-{}", std::process::id()));
        std::fs::write(&root, format!("{source}\n")).unwrap();
        assert_eq!(read_published_report(&root).unwrap(), source);
        std::fs::write(&root, format!("{source}\n\n")).unwrap();
        assert!(read_published_report(&root).is_err());
        std::fs::write(&root, format!("{source}\r\n")).unwrap();
        assert!(read_published_report(&root).is_err());
        std::fs::remove_file(root).unwrap();
    }
}
