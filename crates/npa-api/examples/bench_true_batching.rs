//! Advisory elapsed-time harness for proof-authoring true batching.

use std::time::Instant;

use npa_api::{
    create_machine_session, machine_tactic_batch_response_canonical_json,
    run_machine_tactic_batch_request,
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

fn main() {
    let args = Args::parse();
    assert!(
        valid_source_identity(&args.source_identity),
        "--source-identity must be a lowercase Git object id with optional -dirty suffix"
    );
    let executable = std::env::current_exe().expect("current executable path available");
    let build_identity_hash =
        sha256_hex(&std::fs::read(executable).expect("current executable is readable"));
    let cargo_lock_hash = sha256_hex(
        &std::fs::read(workspace_root().join("Cargo.lock")).expect("Cargo.lock is readable"),
    );
    let mut results = Vec::new();

    for (fixture, let_depth) in STATE_FIXTURES {
        for candidate_count in CANDIDATE_COUNTS {
            let samples_ns = sample_elapsed(args.warmup, args.samples, || {
                run_machine_tactic_once(let_depth, candidate_count)
            });
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
            run_certificate_producer_once(candidate_count);
        });
        let measurement = measure_certificate_producer_once(candidate_count);
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
    println!(
        "{{\"schema\":\"npa.true-batching.elapsed.v0.1\",\"trusted\":false,\
         \"proof_evidence\":false,\"source_identity\":\"{}\",\
         \"build_identity_hash\":\"{}\",\"cargo_lock_hash\":\"{}\",\
         \"rustc_vv\":\"{}\",\"cargo_profile\":\"{}\",\
         \"warmup\":{},\"sample_count\":{},\"elapsed_gate\":\"advisory\",\
         \"status\":\"passed\",\"scenarios\":[{}]}}",
        json_escape(&args.source_identity),
        build_identity_hash,
        cargo_lock_hash,
        json_escape(&decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))),
        env!("NPA_BUILD_CARGO_PROFILE"),
        args.warmup,
        args.samples,
        scenarios,
    );
}

fn run_machine_tactic_once(let_depth: usize, candidate_count: usize) {
    let theorem_type = theorem_type_fixture(let_depth);
    let mut session = create_machine_session(&minimal_session_json(&theorem_type))
        .expect("machine session fixture is valid")
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
        .expect("machine tactic batch request is structurally valid");
    let response_json = machine_tactic_batch_response_canonical_json(&response);
    assert!(
        response_json.starts_with(r#"{"status":"ok""#),
        "machine tactic fixture must complete successfully"
    );
    std::hint::black_box(response_json);
}

fn run_certificate_producer_once(candidate_count: usize) {
    let result = check_core_decl_candidates(certificate_producer_batch(candidate_count))
        .expect("producer batch fixture is structurally valid");
    validate_certificate_producer_result(&result, candidate_count);
    std::hint::black_box(result);
}

fn measure_certificate_producer_once(candidate_count: usize) -> ProducerBatchMeasurement {
    let batch = certificate_producer_batch(candidate_count);
    let mut measurement = ProducerBatchMeasurement::default();
    let result = check_core_decl_candidates_with_measurement(batch, &mut measurement)
        .expect("producer batch fixture is structurally valid");
    validate_certificate_producer_result(&result, candidate_count);
    std::hint::black_box(result);
    measurement
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

fn validate_certificate_producer_result(result: &CandidateBatchResult, candidate_count: usize) {
    assert_eq!(result.statuses.len(), candidate_count);
    assert!(
        result
            .statuses
            .iter()
            .all(|status| matches!(status, CandidateStatus::Accepted(_))),
        "producer fixture candidates must all be accepted"
    );
}

fn sample_elapsed(warmup: usize, samples: usize, mut run_once: impl FnMut()) -> Vec<u64> {
    for _ in 0..warmup {
        run_once();
    }
    (0..samples)
        .map(|_| {
            let started = Instant::now();
            run_once();
            u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
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
          "protocol_version":"npa.machine-api.v1",
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
}

impl Args {
    fn parse() -> Self {
        let mut source_identity = None;
        let mut warmup = 3;
        let mut samples = 9;
        let mut args = std::env::args().skip(1);
        while let Some(flag) = args.next() {
            let value = args
                .next()
                .unwrap_or_else(|| panic!("missing value for {flag}"));
            match flag.as_str() {
                "--source-identity" => source_identity = Some(value),
                "--warmup" => warmup = value.parse().expect("--warmup is an integer"),
                "--samples" => samples = value.parse().expect("--samples is an integer"),
                _ => panic!("unknown option {flag}"),
            }
        }
        assert!(samples > 0, "--samples must be positive");
        Self {
            source_identity: source_identity.expect("--source-identity is required"),
            warmup,
            samples,
        }
    }
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
    let median_ns = median(samples);
    let deviations = samples
        .iter()
        .map(|sample| sample.abs_diff(median_ns))
        .collect::<Vec<_>>();
    ElapsedStatistics {
        median: median_ns,
        median_absolute_deviation: median(&deviations),
        minimum: samples.iter().copied().min().expect("samples are nonempty"),
        maximum: samples.iter().copied().max().expect("samples are nonempty"),
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
    value
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

fn valid_source_identity(value: &str) -> bool {
    let object_id = value.strip_suffix("-dirty").unwrap_or(value);
    matches!(object_id.len(), 40 | 64)
        && object_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn workspace_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("npa-api crate lives under crates/")
        .to_path_buf()
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn decode_build_hex(encoded: &str) -> String {
    assert!(
        encoded.len().is_multiple_of(2),
        "build metadata hex is even"
    );
    let bytes = encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| (hex_digit(pair[0]) << 4) | hex_digit(pair[1]))
        .collect::<Vec<_>>();
    String::from_utf8(bytes).expect("embedded rustc -Vv metadata is UTF-8")
}

fn hex_digit(value: u8) -> u8 {
    match value {
        b'0'..=b'9' => value - b'0',
        b'a'..=b'f' => value - b'a' + 10,
        _ => panic!("build metadata contains invalid hex"),
    }
}
