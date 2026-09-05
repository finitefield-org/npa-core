//! Deterministic application-spine WHNF benchmark.
//!
//! This executable is deliberately untrusted performance evidence.  Kernel
//! unit tests own the private transition audit; this harness reports only the
//! public result, fuel, and `KernelWorkCounters` surface.

#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/runtime_source_set.rs"]
mod runtime_source_set;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use std::time::Instant;

use closed_private_tree::{
    create_new_absolute_file, read_absolute_regular_file, read_invocation_regular_file,
    AttachedExecutable, AttachedOutputFile, ClosedPrivateDirectory,
};
use npa_api::{JsonDocument, JsonMember, JsonValue, JsonValueKind};
use npa_cert::core_expr_hash;
use npa_kernel::{
    Binder, ConstructorDecl, Ctx, Env, Expr, InductiveDecl, KernelExecutionOptions,
    KernelWorkCounters, Level, RecursorDecl, RecursorRules, Reducibility,
};
use sha2::{Digest, Sha256};

const FIXTURE_SCHEMA: &str = "npa.kernel-whnf-application-spine.fixtures.v0.1";
const BASELINE_SCHEMA: &str = "npa.kernel-whnf-application-spine.measurements.v0.2";
const MICRO_CHILD_SCHEMA: &str = "npa.kernel-whnf-application-spine.micro-child.v0.2";
const PACKAGE_CHILD_SCHEMA: &str = "npa.kernel-whnf-application-spine.package-child.v0.2";
const RUN_SCHEMA: &str = "npa.kernel-whnf-application-spine.run.v0.2";
const ELAPSED_BASELINE_SCHEMA: &str = "npa.kernel-whnf-application-spine.elapsed-baseline.v0.2";
const ELAPSED_PROFILE_SCHEMA: &str = "npa.kernel-whnf-application-spine.elapsed-profile.v0.1";
const PRE_SWITCH_ARTIFACT_SCHEMA: &str =
    "npa.kernel-whnf-application-spine.pre-switch-artifact.v0.2";
const PRE_SWITCH_IMPLEMENTATION: &str = "recursive-pre-switch";
const REVIEWED_PROFILE_ID: &str = "kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1";
const REVIEWED_BASELINE_PATH: &str = "testdata/performance/baselines/elapsed/kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1.baseline.v0.1.json";
const FIXTURE_MANIFEST_PATH: &str =
    "testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json";
const DETERMINISTIC_BASELINE_PATH: &str =
    "testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json";
const MICRO_SOURCE_PATH: &str = "crates/npa-api/examples/bench_whnf_application_spine.rs";
const MICRO_BINARY_PATH: &str = "target/release/examples/bench_whnf_application_spine";
const PACKAGE_SOURCE_PATH: &str = "crates/npa-api/examples/check_whnf_application_spine_package.rs";
const PACKAGE_BINARY_PATH: &str = "target/release/examples/check_whnf_application_spine_package";
const MEASURE_SOURCE_PATH: &str = "crates/npa-cli/examples/measure_process.rs";
const MEASURE_BINARY_PATH: &str = "target/release/examples/measure_process";
const WIDTHS: [usize; 5] = [32, 128, 512, 2_048, 8_192];
const MODES: [&str; 3] = ["memo-off", "repetition-probe", "ephemeral"];
const PACKAGE_IDS: [&str; 3] = [
    "checked-package.off",
    "checked-package.ephemeral",
    "checked-package.compare",
];
const WORK_KEYS: [&str; 50] = [
    "check_calls",
    "infer_calls",
    "whnf_calls",
    "defeq_calls",
    "quick_equality_hits",
    "beta_steps",
    "delta_steps",
    "iota_steps",
    "fuel",
    "logical_fuel",
    "successful_fuel",
    "exhausted_fuel",
    "physical_reductions",
    "context_lookups",
    "context_shifts",
    "memo_eligible_calls",
    "memo_ineligible_borrowed",
    "memo_ineligible_fresh",
    "memo_ineligible_diagnosed",
    "memo_identity_capacity_stops",
    "whnf_memo_lookups",
    "whnf_memo_hits",
    "whnf_memo_misses",
    "whnf_memo_inserts",
    "whnf_memo_capacity_stops",
    "defeq_memo_lookups",
    "defeq_memo_hits",
    "defeq_memo_misses",
    "defeq_memo_inserts",
    "defeq_memo_capacity_stops",
    "memo_expr_identities",
    "memo_local_identities",
    "memo_context_identities",
    "memo_parameter_profiles",
    "memo_entry_capacity",
    "whnf_memo_entries",
    "defeq_memo_entries",
    "memo_retained_node_occurrences",
    "memo_retained_context_occurrences",
    "memo_retained_parameter_occurrences",
    "memo_retained_bytes",
    "memo_logical_fuel_replayed",
    "memo_bypassed_call_bodies",
    "memo_accounting_overflows",
    "memo_probe_lookups",
    "memo_probe_repetitions",
    "memo_probe_inserts",
    "memo_probe_capacity_stops",
    "memo_probe_truncated",
    "overflowed",
];

const USAGE: &str = "usage: bench_whnf_application_spine --fixture-manifest PATH --baseline PATH (--list | [--child --phase candidate --sample-index 0..8] --scenario-id ID | --controller --phase candidate --measure-process PATH --package-harness PATH --output PATH [--elapsed-profile PATH] | --validate-report REPORT --phase candidate --measure-process PATH --package-harness PATH [--elapsed-profile PATH] | --validate-archived-artifact MANIFEST | --validate-bootstrap-profile PROFILE --archived-artifact MANIFEST --measure-process PATH --package-harness PATH | --seal-recursive-baseline RAW --archived-artifact MANIFEST --output PATH | --collect-archived-recursive-baseline --archived-artifact MANIFEST --review-reason TEXT --output PATH)\n\nThe post-switch executable rejects direct --phase recursive work. Archived collection runs only identity-bound private snapshots of the validated pre-switch artifact; report, artifact, profile, and seal modes execute no post-switch kernel work.";

fn main() {
    exit_with_result(run_from_args(std::env::args().skip(1).collect()));
}

fn exit_with_result(result: Result<(), String>) {
    if let Err(error) = result {
        let _ = writeln!(
            std::io::stderr().lock(),
            "kernel WHNF benchmark: {}",
            one_line_error(&error)
        );
        std::process::exit(2);
    }
}

fn one_line_error(error: &str) -> String {
    error.replace(['\n', '\r'], " ")
}

fn run_from_args(raw_arguments: Vec<String>) -> Result<(), String> {
    if matches!(raw_arguments.as_slice(), [argument] if matches!(argument.as_str(), "--help" | "-h"))
    {
        writeln!(std::io::stdout().lock(), "{USAGE}")
            .map_err(|error| format!("write help: {error}"))?;
        return Ok(());
    }
    let args = Args::parse_from(raw_arguments)?;
    if args.child && args.list {
        return Err("child mode selects exactly one scenario".to_owned());
    }
    if let Some(profile_path) = args.validate_bootstrap_profile.as_deref() {
        validate_bootstrap_profile(
            profile_path,
            args.archived_artifact
                .as_deref()
                .ok_or("bootstrap profile validation requires --archived-artifact")?,
            &args.fixture_manifest,
            &args.baseline,
            args.measure_process
                .as_deref()
                .ok_or("bootstrap profile validation requires --measure-process")?,
            args.package_harness
                .as_deref()
                .ok_or("bootstrap profile validation requires --package-harness")?,
        )?;
        return Ok(());
    }
    if args.validate_report.is_some() {
        validate_candidate_run_report(&args)?;
        return Ok(());
    }
    if let Some(artifact_path) = args.validate_archived_artifact.as_deref() {
        validate_pre_switch_artifact_path(artifact_path, &args.fixture_manifest, &args.baseline)?;
        return Ok(());
    }
    if let Some(raw_baseline) = args.seal_recursive_baseline.as_deref() {
        seal_recursive_baseline(
            raw_baseline,
            args.archived_artifact
                .as_deref()
                .ok_or("seal mode requires --archived-artifact")?,
            &args.fixture_manifest,
            &args.baseline,
            args.output
                .as_deref()
                .ok_or("seal mode requires --output")?,
        )?;
        return Ok(());
    }
    if args.collect_archived_recursive_baseline {
        collect_archived_recursive_baseline(
            args.archived_artifact
                .as_deref()
                .ok_or("archived collection requires --archived-artifact")?,
            &args.fixture_manifest,
            &args.baseline,
            args.output
                .as_deref()
                .ok_or("archived collection requires --output")?,
            args.review_reason
                .as_deref()
                .ok_or("archived collection requires --review-reason")?,
        )?;
        return Ok(());
    }
    reject_recursive_phase_on_post_switch_binary(&args.phase)?;
    if args.controller {
        run_controller(&args)?;
        return Ok(());
    }
    let manifest = read_json_input(&args.fixture_manifest, "fixture manifest")?;
    validate_manifest(&manifest)?;
    let baseline = read_json_input(&args.baseline, "deterministic baseline")?;
    validate_baseline(&baseline)?;
    validate_baseline_manifest_hash(&baseline, &sha256_bytes(manifest.as_bytes()))?;

    if args.list {
        let mut stdout = std::io::stdout().lock();
        for scenario in expected_scenarios() {
            writeln!(stdout, "{scenario}").map_err(|error| format!("write catalog: {error}"))?;
        }
        for scenario in PACKAGE_IDS {
            writeln!(stdout, "{scenario}").map_err(|error| format!("write catalog: {error}"))?;
        }
        return Ok(());
    }

    let scenario = args
        .scenario
        .as_deref()
        .ok_or("--scenario-id is required unless --list is selected")?
        .to_owned();
    let (_, width, _) =
        parse_scenario(&scenario).ok_or_else(|| format!("unknown scenario {scenario}"))?;
    if width == 8_192 {
        std::thread::Builder::new()
            .name("whnf-machine-only-child".to_owned())
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_selected(&args, &scenario))
            .map_err(|error| format!("spawn machine-only child worker: {error}"))?
            .join()
            .map_err(|_| "machine-only child worker panicked".to_owned())??;
    } else {
        run_selected(&args, &scenario)?;
    }
    Ok(())
}

fn reject_recursive_phase_on_post_switch_binary(phase: &str) -> Result<(), &'static str> {
    if phase == "recursive" {
        Err(
            "this executable is built from the post-switch WHNF machine; collect the recursive baseline with the archived pre-switch executable instead of relabeling candidate work",
        )
    } else {
        Ok(())
    }
}

fn run_selected(args: &Args, scenario: &str) -> Result<(), String> {
    let (kind, width, mode) =
        parse_scenario(scenario).ok_or_else(|| format!("unknown scenario {scenario}"))?;
    run_and_print(args, scenario, build_fixture(kind, width, mode)?)
}

enum Operation {
    Whnf(Expr),
    Defeq(Expr, Expr),
}

struct Fixture {
    env: Env,
    operation: Operation,
    retained_function: Option<Arc<Expr>>,
}

enum OperationResult {
    Whnf(Expr),
    Defeq(bool),
}

fn run_operation(
    fixture: &Fixture,
    counters: &mut KernelWorkCounters,
) -> Result<OperationResult, String> {
    match &fixture.operation {
        Operation::Whnf(term) => fixture
            .env
            .whnf_with_work_counters(&Ctx::new(), &[], term, Some(counters))
            .map(OperationResult::Whnf)
            .map_err(|_| "kernel WHNF operation failed".to_owned()),
        Operation::Defeq(lhs, rhs) => fixture
            .env
            .is_defeq_with_work_counters(&Ctx::new(), &[], lhs, rhs, Some(counters))
            .map(OperationResult::Defeq)
            .map_err(|_| "kernel definitional-equality operation failed".to_owned()),
    }
}

fn run_and_print(args: &Args, scenario: &str, fixture: Fixture) -> Result<(), String> {
    let (kind, width, mode) =
        parse_scenario(scenario).ok_or_else(|| format!("unknown scenario {scenario}"))?;
    if fixture.retained_function.is_some() != (kind == "retained-function-ephemeral-defeq") {
        return Err("fixture retained-function ownership mismatch".to_owned());
    }
    let warmup_fixture = build_fixture(kind, width, mode)?;
    let mut warmup = KernelWorkCounters::default();
    let warmup_result = run_operation(&warmup_fixture, &mut warmup)?;
    if width == 8_192 {
        // Dropping the adversarial rebuilt App root recursively is outside the
        // WHNF operation and would make the harness stack, rather than the
        // machine, the limiting resource.
        std::mem::forget(warmup_result);
    }
    let mut counters = KernelWorkCounters::default();
    let started = Instant::now();
    let result = run_operation(&fixture, &mut counters)?;
    let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    let result_json = match &result {
        OperationResult::Whnf(result) => format!(
            "{{\"kind\":\"whnf\",\"expr_hash\":\"{}\"}}",
            hex_hash(&core_expr_hash_on_sized_stack(result, width)?)
        ),
        OperationResult::Defeq(equal) => {
            if !equal {
                return Err("retained-function fixture was not definitionally equal".to_owned());
            }
            "{\"kind\":\"defeq\",\"equal\":true}".to_owned()
        }
    };
    let delta_events = if kind == "delta-exposed-long-spine" {
        "[\"Bench.KernelWhnfApplicationSpine.deltaHead\"]"
    } else {
        "[]"
    };
    if width == 8_192 {
        validate_machine_only_observation(&fixture, kind, width, mode, &result, &counters)?;
    } else {
        validate_selected_baseline(
            &read_json_input(&args.baseline, "deterministic baseline")?,
            scenario,
            &result_json,
            &work_json(&counters),
            delta_events,
        )?;
    }
    writeln!(
        std::io::stdout().lock(),
        "{{\"schema\":\"{MICRO_CHILD_SCHEMA}\",\"phase\":\"{}\",\"scenario_id\":\"{scenario}\",\"sample_index\":{},\"mode\":\"{mode}\",\"operation_elapsed_ns\":{elapsed},\"result\":{result_json},\"error\":null,\"work\":{},\"named_delta_events\":{delta_events}}}",
        args.phase,
        args.sample_index,
        work_json(&counters),
    )
    .map_err(|error| format!("write child result: {error}"))?;
    if width == 8_192 {
        if let OperationResult::Whnf(result) = result {
            std::mem::forget(result);
        }
        std::mem::forget(fixture);
        std::mem::forget(warmup_fixture);
    }
    Ok(())
}

fn core_expr_hash_on_sized_stack(expr: &Expr, width: usize) -> Result<[u8; 32], String> {
    if width != 8_192 {
        return Ok(core_expr_hash(expr));
    }
    let retained_root = expr.clone();
    std::thread::Builder::new()
        .name("whnf-machine-only-core-hash".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || core_expr_hash(&retained_root))
        .map_err(|error| format!("spawn machine-only hash worker: {error}"))?
        .join()
        .map_err(|_| "machine-only hash worker panicked".to_owned())
}

fn validate_machine_only_observation(
    fixture: &Fixture,
    kind: &str,
    width: usize,
    mode: &str,
    result: &OperationResult,
    work: &KernelWorkCounters,
) -> Result<(), String> {
    match (&fixture.operation, result) {
        (Operation::Defeq(_, _), OperationResult::Defeq(true)) => {}
        (Operation::Defeq(_, _), OperationResult::Defeq(false)) => {
            return Err("machine-only definitional equality returned false".to_owned())
        }
        (Operation::Whnf(original), OperationResult::Whnf(observed)) => match kind {
            "opaque-neutral-head" | "delta-exposed-long-spine" => {
                validate_neutral_spine_shape(observed, width)?
            }
            "partial-recursor" | "saturated-neutral-major" => {
                validate_atomic_application_spines_equal(observed, original)?
            }
            "matching-constructor" => {
                let family = format!("Bench.KernelWhnfApplicationSpine.Saturated.w{width}");
                let expected = left_fold_apps(
                    Expr::konst(format!("{family}.minor.m00000"), vec![]),
                    (width..width + 8).map(argument),
                );
                if *observed != expected {
                    return Err("matching-constructor result shape mismatch".to_owned());
                }
            }
            _ => return Err(format!("unknown machine-only kind {kind}")),
        },
        _ => return Err("machine-only operation/result kind mismatch".to_owned()),
    }

    if work.overflowed || work.fuel.whnf.overflowed || work.fuel.conversion.overflowed {
        return Err("machine-only work counters overflowed".to_owned());
    }
    let expected_logical_fuel = match kind {
        "opaque-neutral-head" | "partial-recursor" => (width + 1, 0),
        "saturated-neutral-major" => (width + 10, 0),
        "matching-constructor" => (width + 3, 0),
        "delta-exposed-long-spine" => (width + 2, 0),
        "retained-function-ephemeral-defeq" => (0, width * 2 + 11),
        _ => return Err(format!("unknown machine-only kind {kind}")),
    };
    let observed_logical_fuel = (
        usize::try_from(work.fuel.whnf.logical_spent)
            .map_err(|_| "machine-only WHNF fuel does not fit usize")?,
        usize::try_from(work.fuel.conversion.logical_spent)
            .map_err(|_| "machine-only conversion fuel does not fit usize")?,
    );
    if observed_logical_fuel != expected_logical_fuel {
        return Err(format!(
            "machine-only logical fuel mismatch: expected {expected_logical_fuel:?}, observed {observed_logical_fuel:?}"
        ));
    }
    if work.delta_steps != u64::from(kind == "delta-exposed-long-spine")
        || work.iota_steps != u64::from(kind == "matching-constructor")
    {
        return Err("machine-only delta/iota work mismatch".to_owned());
    }
    match mode {
        "memo-off" => {
            if work.whnf_memo_lookups != 0
                || work.defeq_memo_lookups != 0
                || work.memo_probe_lookups != 0
            {
                return Err("memo-off machine-only run performed memo lookups".to_owned());
            }
        }
        "repetition-probe" => {
            if work.whnf_memo_lookups != 0
                || work.defeq_memo_lookups != 0
                || work.memo_probe_lookups == 0
            {
                return Err("repetition-probe machine-only lookup model mismatch".to_owned());
            }
        }
        "ephemeral" => {
            if work
                .whnf_memo_lookups
                .saturating_add(work.defeq_memo_lookups)
                == 0
                || work.memo_probe_lookups != 0
            {
                return Err("ephemeral machine-only lookup model mismatch".to_owned());
            }
        }
        _ => return Err(format!("unknown machine-only mode {mode}")),
    }
    Ok(())
}

fn validate_neutral_spine_shape(term: &Expr, width: usize) -> Result<(), String> {
    let mut current = term;
    for index in (0..width).rev() {
        let Expr::App(function, argument) = current else {
            return Err(format!("neutral fixture ended before width {width}"));
        };
        if argument.as_ref()
            != &Expr::konst(
                format!("Bench.KernelWhnfApplicationSpine.arg.a{index:05}"),
                vec![],
            )
        {
            return Err(format!("neutral fixture argument mismatch at {index}"));
        }
        current = function;
    }
    if current
        != &Expr::konst(
            format!("Bench.KernelWhnfApplicationSpine.neutralHead.w{width}"),
            vec![],
        )
    {
        return Err("neutral fixture head mismatch".to_owned());
    }
    Ok(())
}

fn validate_atomic_application_spines_equal(left: &Expr, right: &Expr) -> Result<(), String> {
    let mut left = left;
    let mut right = right;
    loop {
        match (left, right) {
            (
                Expr::App(left_function, left_argument),
                Expr::App(right_function, right_argument),
            ) => {
                if left_argument != right_argument {
                    return Err("atomic application spine argument mismatch".to_owned());
                }
                left = left_function;
                right = right_function;
            }
            _ => {
                return if left == right {
                    Ok(())
                } else {
                    Err("atomic application spine head mismatch".to_owned())
                };
            }
        }
    }
}

fn build_fixture(kind: &str, width: usize, mode: &str) -> Result<Fixture, String> {
    let mut env = common_env(width, mode)?;
    let (operation, retained_function) = match kind {
        "opaque-neutral-head" => (Operation::Whnf(neutral_spine(width)), None),
        "partial-recursor" => {
            let family = add_recursor_family(&mut env, "Partial", width, width - 1)?;
            let mut arguments = vec![Expr::konst(format!("{family}.motive"), vec![])];
            arguments.extend(
                (0..width - 1)
                    .map(|index| Expr::konst(format!("{family}.minor.m{index:05}"), vec![])),
            );
            (
                Operation::Whnf(left_fold_apps(
                    Expr::konst(format!("{family}.R"), vec![]),
                    arguments,
                )),
                None,
            )
        }
        "saturated-neutral-major" | "matching-constructor" => {
            let constructor_count = width - 10;
            let family = add_recursor_family(&mut env, "Saturated", width, constructor_count)?;
            let mut arguments = vec![Expr::konst(format!("{family}.motive"), vec![])];
            arguments.extend(
                (0..constructor_count)
                    .map(|index| Expr::konst(format!("{family}.minor.m{index:05}"), vec![])),
            );
            arguments.push(if kind == "matching-constructor" {
                Expr::konst(format!("{family}.C00000"), vec![])
            } else {
                Expr::konst(
                    format!("Bench.KernelWhnfApplicationSpine.neutralMajor.w{width}"),
                    vec![],
                )
            });
            arguments.extend((width..width + 8).map(argument));
            (
                Operation::Whnf(left_fold_apps(
                    Expr::konst(format!("{family}.R"), vec![]),
                    arguments,
                )),
                None,
            )
        }
        "delta-exposed-long-spine" => (
            Operation::Whnf(Expr::konst(
                "Bench.KernelWhnfApplicationSpine.deltaHead",
                vec![],
            )),
            None,
        ),
        "retained-function-ephemeral-defeq" => {
            let function = Arc::new(neutral_spine(width));
            let lhs = Expr::App(Arc::clone(&function), Arc::new(outer()));
            let rhs = Expr::App(
                Arc::clone(&function),
                Arc::new(Expr::App(
                    Arc::new(Expr::Lam {
                        binder: "_".to_owned(),
                        ty: Arc::new(Expr::sort(Level::zero())),
                        body: Arc::new(Expr::bvar(0)),
                    }),
                    Arc::new(outer()),
                )),
            );
            (Operation::Defeq(lhs, rhs), Some(function))
        }
        _ => return Err(format!("unknown fixture kind {kind}")),
    };
    Ok(Fixture {
        env,
        operation,
        retained_function,
    })
}

fn common_env(width: usize, mode: &str) -> Result<Env, String> {
    let sort = Expr::sort(Level::zero());
    let mut env = Env::with_execution_options(mode_options(mode)?);
    for index in 0..width + 8 {
        env.add_axiom(
            format!("Bench.KernelWhnfApplicationSpine.arg.a{index:05}"),
            vec![],
            sort.clone(),
        )
        .map_err(|_| format!("cannot admit argument axiom {index}"))?;
    }
    env.add_axiom(
        "Bench.KernelWhnfApplicationSpine.outer",
        vec![],
        sort.clone(),
    )
    .map_err(|_| "cannot admit outer axiom".to_owned())?;
    let head_type = (0..width).fold(sort.clone(), |body, _| Expr::pi("_", sort.clone(), body));
    env.add_axiom(
        format!("Bench.KernelWhnfApplicationSpine.neutralHead.w{width}"),
        vec![],
        head_type,
    )
    .map_err(|_| "cannot admit neutral-head axiom".to_owned())?;
    env.add_def(
        "Bench.KernelWhnfApplicationSpine.deltaHead",
        vec![],
        sort,
        neutral_spine(width),
        Reducibility::Reducible,
    )
    .map_err(|_| "cannot admit delta fixture".to_owned())?;
    Ok(env)
}

fn add_recursor_family(
    env: &mut Env,
    stem: &str,
    width: usize,
    constructor_count: usize,
) -> Result<String, String> {
    let family = format!("Bench.KernelWhnfApplicationSpine.{stem}.w{width}");
    let family_expr = Expr::konst(family.clone(), vec![]);
    let sort = Expr::sort(Level::zero());
    let constructors = (0..constructor_count)
        .map(|index| ConstructorDecl::new(format!("{family}.C{index:05}"), family_expr.clone()))
        .collect::<Vec<_>>();
    let mut body = Expr::pi(
        "major",
        family_expr.clone(),
        Expr::app(
            Expr::bvar(
                u32::try_from(constructor_count + 1)
                    .map_err(|_| "fixture constructor count does not fit u32")?,
            ),
            Expr::bvar(0),
        ),
    );
    for index in (0..constructor_count).rev() {
        let minor_type = Expr::app(
            Expr::bvar(u32::try_from(index).map_err(|_| "fixture index does not fit u32")?),
            Expr::konst(format!("{family}.C{index:05}"), vec![]),
        );
        body = Expr::pi(format!("minor_{index:05}"), minor_type, body);
    }
    let recursor_type = Expr::pi("motive", Expr::pi("_", family_expr.clone(), sort), body);
    env.add_inductive(InductiveDecl::new(
        family.clone(),
        vec![],
        Vec::<Binder>::new(),
        Vec::<Binder>::new(),
        Level::zero(),
        constructors,
        Some(RecursorDecl::with_rules(
            format!("{family}.R"),
            vec![],
            recursor_type,
            RecursorRules::new(1, constructor_count + 1),
        )),
    ))
    .map_err(|_| "cannot admit benchmark recursor family".to_owned())?;
    Ok(family)
}

fn left_fold_apps(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, |function, argument| {
        Expr::App(Arc::new(function), Arc::new(argument))
    })
}

fn argument(index: usize) -> Expr {
    Expr::konst(
        format!("Bench.KernelWhnfApplicationSpine.arg.a{index:05}"),
        vec![],
    )
}

fn outer() -> Expr {
    Expr::konst("Bench.KernelWhnfApplicationSpine.outer", vec![])
}

fn neutral_spine(width: usize) -> Expr {
    let head = Expr::konst(
        format!("Bench.KernelWhnfApplicationSpine.neutralHead.w{width}"),
        vec![],
    );
    left_fold_apps(head, (0..width).map(argument))
}

fn mode_options(mode: &str) -> Result<KernelExecutionOptions, String> {
    match mode {
        "memo-off" => Ok(KernelExecutionOptions::memo_off()),
        "repetition-probe" => Ok(KernelExecutionOptions::repetition_probe()),
        "ephemeral" => Ok(KernelExecutionOptions::ephemeral_memo()),
        _ => Err(format!("unknown fixture mode {mode}")),
    }
}

fn expected_scenarios() -> Vec<String> {
    let kinds = [
        "opaque-neutral-head",
        "partial-recursor",
        "saturated-neutral-major",
        "matching-constructor",
        "delta-exposed-long-spine",
        "retained-function-ephemeral-defeq",
    ];
    let mut result = Vec::with_capacity(90);
    for kind in kinds {
        for width in WIDTHS {
            for mode in MODES {
                result.push(format!("{kind}.w{width}.{mode}"));
            }
        }
    }
    result
}

fn parse_scenario(value: &str) -> Option<(&str, usize, &str)> {
    let (prefix, mode) = value.rsplit_once('.')?;
    let (kind, width) = prefix.rsplit_once(".w")?;
    let width = width.parse().ok()?;
    if WIDTHS.contains(&width)
        && MODES.contains(&mode)
        && expected_scenarios()
            .iter()
            .any(|expected| expected == value)
    {
        Some((kind, width, mode))
    } else {
        None
    }
}

fn validate_manifest(source: &str) -> Result<(), String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid JSON at {}: {:?}", error.offset, error.kind))?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "warmup",
            "samples",
            "whnf_fuel",
            "conversion_fuel",
            "micro_scenarios",
            "package_scenarios",
        ],
        "fixture",
    )?;
    expect_string(root[0].value(), FIXTURE_SCHEMA, "fixture.schema")?;
    expect_unsigned_eq(root[1].value(), 1, "fixture.warmup")?;
    expect_unsigned_eq(root[2].value(), 9, "fixture.samples")?;
    expect_unsigned_eq(root[3].value(), 100_000, "fixture.whnf_fuel")?;
    expect_unsigned_eq(root[4].value(), 5_000_000, "fixture.conversion_fuel")?;

    let micro = expect_array(root[5].value(), "fixture.micro_scenarios")?;
    let expected = expected_scenarios();
    if micro.len() != expected.len() {
        return Err(format!(
            "fixture.micro_scenarios has {} rows, expected {}",
            micro.len(),
            expected.len()
        ));
    }
    for (index, (row, expected_id)) in micro.iter().zip(&expected).enumerate() {
        let path = format!("fixture.micro_scenarios[{index}]");
        let fields = exact_object(
            row,
            &[
                "id",
                "kind",
                "width",
                "mode",
                "trailing_arguments",
                "machine_only",
                "deterministic_baseline_key",
            ],
            &path,
        )?;
        let (kind, width, mode) = parse_scenario(expected_id)
            .ok_or_else(|| format!("closed fixture scenario no longer parses: {expected_id}"))?;
        expect_string(fields[0].value(), expected_id, &format!("{path}.id"))?;
        expect_string(fields[1].value(), kind, &format!("{path}.kind"))?;
        expect_unsigned_eq(fields[2].value(), width as u64, &format!("{path}.width"))?;
        expect_string(fields[3].value(), mode, &format!("{path}.mode"))?;
        let trailing = match kind {
            "saturated-neutral-major" | "matching-constructor" => 8,
            "retained-function-ephemeral-defeq" => 1,
            _ => 0,
        };
        expect_unsigned_eq(
            fields[4].value(),
            trailing,
            &format!("{path}.trailing_arguments"),
        )?;
        expect_bool(
            fields[5].value(),
            width == 8_192,
            &format!("{path}.machine_only"),
        )?;
        if width == 8_192 {
            expect_kind(
                fields[6].value(),
                JsonValueKind::Null,
                &format!("{path}.deterministic_baseline_key"),
            )?;
        } else {
            expect_string(
                fields[6].value(),
                expected_id,
                &format!("{path}.deterministic_baseline_key"),
            )?;
        }
    }

    let package = expect_array(root[6].value(), "fixture.package_scenarios")?;
    if package.len() != 3 {
        return Err(format!(
            "fixture.package_scenarios has {} rows, expected 3",
            package.len()
        ));
    }
    for (index, row) in package.iter().enumerate() {
        let path = format!("fixture.package_scenarios[{index}]");
        let fields = exact_object(
            row,
            &[
                "id",
                "kind",
                "package_root",
                "package_manifest",
                "package_lock",
                "kernel_mode",
                "cache_policy",
                "deterministic_baseline_keys",
            ],
            &path,
        )?;
        let id = PACKAGE_IDS[index];
        let mode = ["off", "ephemeral", "compare"][index];
        expect_string(fields[0].value(), id, &format!("{path}.id"))?;
        expect_string(
            fields[1].value(),
            "checked-package",
            &format!("{path}.kind"),
        )?;
        expect_string(
            fields[2].value(),
            "testdata/package/proofs",
            &format!("{path}.package_root"),
        )?;
        expect_string(
            fields[3].value(),
            "testdata/package/proofs/npa-package.toml",
            &format!("{path}.package_manifest"),
        )?;
        expect_string(
            fields[4].value(),
            "checked",
            &format!("{path}.package_lock"),
        )?;
        expect_string(fields[5].value(), mode, &format!("{path}.kernel_mode"))?;
        expect_string(fields[6].value(), "none", &format!("{path}.cache_policy"))?;
        let keys = expect_array(
            fields[7].value(),
            &format!("{path}.deterministic_baseline_keys"),
        )?;
        let expected_keys: &[&str] = match mode {
            "off" => &["checked-package.off"],
            "ephemeral" => &["checked-package.ephemeral"],
            "compare" => &["checked-package.off", "checked-package.ephemeral"],
            _ => return Err(format!("unknown package scenario mode {mode}")),
        };
        if keys.len() != expected_keys.len() {
            return Err(format!(
                "{path}.deterministic_baseline_keys length mismatch"
            ));
        }
        for (key_index, (value, expected)) in keys.iter().zip(expected_keys).enumerate() {
            expect_string(
                value,
                expected,
                &format!("{path}.deterministic_baseline_keys[{key_index}]"),
            )?;
        }
    }
    Ok(())
}

fn validate_baseline(source: &str) -> Result<(), String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid JSON at {}: {:?}", error.offset, error.kind))?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "fixture_manifest_sha256",
            "micro_rows",
            "package_rows",
        ],
        "baseline",
    )?;
    expect_string(root[0].value(), BASELINE_SCHEMA, "baseline.schema")?;
    expect_hash(root[1].value(), "baseline.fixture_manifest_sha256")?;

    let expected_micro = expected_scenarios()
        .into_iter()
        .map(|id| {
            let width = parse_scenario(&id)
                .ok_or_else(|| format!("closed baseline scenario no longer parses: {id}"))?
                .1;
            Ok((id, width))
        })
        .collect::<Result<Vec<_>, String>>()?
        .into_iter()
        .filter_map(|(id, width)| (width != 8_192).then_some(id))
        .collect::<Vec<_>>();
    let micro = expect_array(root[2].value(), "baseline.micro_rows")?;
    if micro.len() != expected_micro.len() {
        return Err(format!(
            "baseline.micro_rows has {} rows, expected 72",
            micro.len()
        ));
    }
    for (index, (row, expected_id)) in micro.iter().zip(&expected_micro).enumerate() {
        let path = format!("baseline.micro_rows[{index}]");
        let fields = exact_object(
            row,
            &[
                "key",
                "scenario_id",
                "result",
                "error",
                "whnf_fuel",
                "conversion_fuel",
                "work",
                "named_delta_events",
            ],
            &path,
        )?;
        expect_string(fields[0].value(), expected_id, &format!("{path}.key"))?;
        expect_string(
            fields[1].value(),
            expected_id,
            &format!("{path}.scenario_id"),
        )?;
        let (kind, _, _) = parse_scenario(expected_id)
            .ok_or_else(|| format!("closed baseline scenario no longer parses: {expected_id}"))?;
        validate_result(fields[2].value(), kind, &format!("{path}.result"))?;
        expect_kind(
            fields[3].value(),
            JsonValueKind::Null,
            &format!("{path}.error"),
        )?;
        expect_unsigned_eq(fields[4].value(), 100_000, &format!("{path}.whnf_fuel"))?;
        expect_unsigned_eq(
            fields[5].value(),
            5_000_000,
            &format!("{path}.conversion_fuel"),
        )?;
        validate_work(fields[6].value(), &format!("{path}.work"))?;
        let events = expect_array(fields[7].value(), &format!("{path}.named_delta_events"))?;
        if kind == "delta-exposed-long-spine" {
            if events.len() != 1 {
                return Err(format!("{path}.named_delta_events must contain one event"));
            }
            expect_string(
                &events[0],
                "Bench.KernelWhnfApplicationSpine.deltaHead",
                &format!("{path}.named_delta_events[0]"),
            )?;
        } else if !events.is_empty() {
            return Err(format!("{path}.named_delta_events must be empty"));
        }
    }

    let package = expect_array(root[3].value(), "baseline.package_rows")?;
    if package.len() != 2 {
        return Err(format!(
            "baseline.package_rows has {} rows, expected 2",
            package.len()
        ));
    }
    let mut identity_shapes = Vec::new();
    for (index, row) in package.iter().enumerate() {
        let path = format!("baseline.package_rows[{index}]");
        let fields = exact_object(
            row,
            &[
                "key",
                "scenario_id",
                "accepted",
                "module_order",
                "verified_modules",
                "input_certificate_hashes",
                "aggregate_work",
            ],
            &path,
        )?;
        let id = PACKAGE_IDS[index];
        expect_string(fields[0].value(), id, &format!("{path}.key"))?;
        expect_string(fields[1].value(), id, &format!("{path}.scenario_id"))?;
        expect_bool(fields[2].value(), true, &format!("{path}.accepted"))?;
        validate_string_array(fields[3].value(), &format!("{path}.module_order"), false)?;
        validate_verified_modules(fields[4].value(), &format!("{path}.verified_modules"))?;
        validate_input_hashes(
            fields[5].value(),
            &format!("{path}.input_certificate_hashes"),
        )?;
        validate_work(fields[6].value(), &format!("{path}.aggregate_work"))?;
        identity_shapes.push((
            compact_json(fields[3].value().raw_slice())?,
            compact_json(fields[4].value().raw_slice())?,
            compact_json(fields[5].value().raw_slice())?,
        ));
    }
    if identity_shapes[0] != identity_shapes[1] {
        return Err("baseline package identities differ between off and ephemeral".to_owned());
    }
    Ok(())
}

fn validate_baseline_manifest_hash(source: &str, expected: &str) -> Result<(), String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid JSON at {}: {:?}", error.offset, error.kind))?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "fixture_manifest_sha256",
            "micro_rows",
            "package_rows",
        ],
        "baseline",
    )?;
    expect_string(
        root[1].value(),
        expected,
        "baseline.fixture_manifest_sha256",
    )
}

fn exact_object<'value, 'source>(
    value: &'value JsonValue<'source>,
    keys: &[&str],
    path: &str,
) -> Result<&'value [JsonMember<'source>], String> {
    let members = value
        .object_members()
        .ok_or_else(|| format!("{path} must be an object"))?;
    let actual = members.iter().map(JsonMember::key).collect::<Vec<_>>();
    if actual != keys {
        return Err(format!("{path} keys/order mismatch: {actual:?}"));
    }
    Ok(members)
}

fn expect_array<'value, 'source>(
    value: &'value JsonValue<'source>,
    path: &str,
) -> Result<&'value [JsonValue<'source>], String> {
    value
        .array_elements()
        .ok_or_else(|| format!("{path} must be an array"))
}

fn expect_kind(value: &JsonValue<'_>, expected: JsonValueKind, path: &str) -> Result<(), String> {
    if value.kind() == expected {
        Ok(())
    } else {
        Err(format!(
            "{path} has kind {:?}, expected {expected:?}",
            value.kind()
        ))
    }
}

fn expect_string(value: &JsonValue<'_>, expected: &str, path: &str) -> Result<(), String> {
    match value.string_value() {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!("{path} is {actual:?}, expected {expected:?}")),
        None => Err(format!("{path} must be a string")),
    }
}

fn expect_unsigned(value: &JsonValue<'_>, path: &str) -> Result<u64, String> {
    value
        .number_raw()
        .ok_or_else(|| format!("{path} must be an unsigned integer"))?
        .parse::<u64>()
        .map_err(|_| format!("{path} must be an unsigned integer"))
}

fn expect_unsigned_eq(value: &JsonValue<'_>, expected: u64, path: &str) -> Result<(), String> {
    let actual = expect_unsigned(value, path)?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{path} is {actual}, expected {expected}"))
    }
}

fn validate_u64_array(
    value: &JsonValue<'_>,
    path: &str,
    expected_len: usize,
) -> Result<Vec<u64>, String> {
    let values = expect_array(value, path)?;
    if values.len() != expected_len {
        return Err(format!(
            "{path} has {} values, expected {expected_len}",
            values.len()
        ));
    }
    values
        .iter()
        .enumerate()
        .map(|(index, value)| expect_unsigned(value, &format!("{path}[{index}]")))
        .collect()
}

fn expect_bool(value: &JsonValue<'_>, expected: bool, path: &str) -> Result<(), String> {
    match value.bool_value() {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!("{path} is {actual}, expected {expected}")),
        None => Err(format!("{path} must be boolean")),
    }
}

fn expect_hash(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let hash = value
        .string_value()
        .ok_or_else(|| format!("{path} must be a string"))?;
    validate_lower_hex_hash(hash, path)
}

fn validate_result(value: &JsonValue<'_>, kind: &str, path: &str) -> Result<(), String> {
    if kind == "retained-function-ephemeral-defeq" {
        let fields = exact_object(value, &["kind", "equal"], path)?;
        expect_string(fields[0].value(), "defeq", &format!("{path}.kind"))?;
        expect_bool(fields[1].value(), true, &format!("{path}.equal"))
    } else {
        let fields = exact_object(value, &["kind", "expr_hash"], path)?;
        expect_string(fields[0].value(), "whnf", &format!("{path}.kind"))?;
        expect_hash(fields[1].value(), &format!("{path}.expr_hash"))
    }
}

fn validate_work(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let fields = exact_object(value, &WORK_KEYS, path)?;
    for (index, field) in fields.iter().enumerate() {
        match WORK_KEYS[index] {
            "fuel" => validate_fuel(field.value(), &format!("{path}.fuel"))?,
            "memo_probe_truncated" | "overflowed" => {
                if field.value().bool_value().is_none() {
                    return Err(format!("{path}.{} must be boolean", WORK_KEYS[index]));
                }
            }
            key => {
                expect_unsigned(field.value(), &format!("{path}.{key}"))?;
            }
        }
    }
    Ok(())
}

fn validate_fuel(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let fields = exact_object(value, &["whnf", "conversion"], path)?;
    for (index, domain) in fields.iter().enumerate() {
        let domain_path = format!("{path}.{}", ["whnf", "conversion"][index]);
        let totals = exact_object(
            domain.value(),
            &[
                "calls",
                "logical_spent",
                "successful_operation_fuel",
                "exhausted_operation_fuel",
                "overflowed",
            ],
            &domain_path,
        )?;
        for total in &totals[..4] {
            expect_unsigned(total.value(), &format!("{domain_path}.{}", total.key()))?;
        }
        if totals[4].value().bool_value().is_none() {
            return Err(format!("{domain_path}.overflowed must be boolean"));
        }
    }
    Ok(())
}

fn validate_string_array(
    value: &JsonValue<'_>,
    path: &str,
    empty_allowed: bool,
) -> Result<(), String> {
    let values = expect_array(value, path)?;
    if !empty_allowed && values.is_empty() {
        return Err(format!("{path} must not be empty"));
    }
    let mut seen = std::collections::BTreeSet::new();
    for (index, value) in values.iter().enumerate() {
        let string = value
            .string_value()
            .ok_or_else(|| format!("{path}[{index}] must be a string"))?;
        if !seen.insert(string) {
            return Err(format!("{path} contains duplicate {string:?}"));
        }
    }
    Ok(())
}

fn validate_verified_modules(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let values = expect_array(value, path)?;
    if values.is_empty() {
        return Err(format!("{path} must not be empty"));
    }
    for (index, value) in values.iter().enumerate() {
        let row_path = format!("{path}[{index}]");
        let fields = exact_object(
            value,
            &["lock_name", "module", "export_hash", "certificate_hash"],
            &row_path,
        )?;
        for field in &fields[..2] {
            if field.value().string_value().is_none() {
                return Err(format!("{row_path}.{} must be a string", field.key()));
            }
        }
        expect_hash(fields[2].value(), &format!("{row_path}.export_hash"))?;
        expect_hash(fields[3].value(), &format!("{row_path}.certificate_hash"))?;
    }
    Ok(())
}

fn validate_input_hashes(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let values = expect_array(value, path)?;
    if values.is_empty() {
        return Err(format!("{path} must not be empty"));
    }
    for (index, value) in values.iter().enumerate() {
        let row_path = format!("{path}[{index}]");
        let fields = exact_object(value, &["lock_name", "sha256"], &row_path)?;
        if fields[0].value().string_value().is_none() {
            return Err(format!("{row_path}.lock_name must be a string"));
        }
        expect_hash(fields[1].value(), &format!("{row_path}.sha256"))?;
    }
    Ok(())
}

fn validate_selected_baseline(
    source: &str,
    scenario: &str,
    result: &str,
    work: &str,
    named_delta_events: &str,
) -> Result<(), String> {
    let compact = compact_json(source)?;
    let expected = format!(
        "{{\"key\":\"{scenario}\",\"scenario_id\":\"{scenario}\",\"result\":{result},\"error\":null,\"whnf_fuel\":100000,\"conversion_fuel\":5000000,\"work\":{work},\"named_delta_events\":{named_delta_events}}}"
    );
    if compact.contains(&expected) {
        Ok(())
    } else {
        Err(format!("missing or mismatched row {scenario}"))
    }
}

#[derive(Clone, Debug)]
struct ControllerRow {
    scenario_id: String,
    series_kind: &'static str,
    mode: String,
    sample_index: u64,
    operation_elapsed_ns: u64,
    process_elapsed_ns: u64,
    peak_rss_kib: u64,
    child_output_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SeriesSummary {
    scenario_id: String,
    series_kind: &'static str,
    mode: String,
    samples_ns: Vec<u64>,
    process_samples_ns: Vec<u64>,
    peak_rss_samples_kib: Vec<u64>,
    median_ns: u64,
    median_absolute_deviation_ns: u64,
    min_ns: u64,
    max_ns: u64,
    peak_rss_kib: u64,
}

#[derive(Clone, Debug)]
struct ExecutableIdentity {
    source_path: &'static str,
    source_sha256: String,
    binary_path: &'static str,
    binary_sha256: String,
}

#[derive(Clone, Debug)]
struct RunIdentity {
    source_identity: String,
    dirty: bool,
    cargo_lock_sha256: String,
    kwhnf_source_set_sha256: String,
    kwhnf_source_set_paths: Vec<String>,
    rustc_vv: String,
    target: String,
    profile: &'static str,
    features: Vec<String>,
    rustflags: String,
    fixture_manifest_sha256: String,
    micro: ExecutableIdentity,
    package: ExecutableIdentity,
    measure: ExecutableIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArchivedExecutableIdentity {
    source_path: String,
    source_sha256: String,
    binary_path: String,
    binary_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArchivedRunIdentity {
    source_identity: String,
    cargo_lock_sha256: String,
    kwhnf_source_set_sha256: String,
    kwhnf_source_set_paths: Vec<String>,
    rustc_vv: String,
    target: String,
    profile: String,
    features: Vec<String>,
    rustflags: String,
    fixture_manifest_sha256: String,
    micro: ArchivedExecutableIdentity,
    package: ArchivedExecutableIdentity,
    measure: ArchivedExecutableIdentity,
}

#[derive(Clone, Debug)]
struct PreSwitchArtifact {
    archive_root: PathBuf,
    deterministic_baseline_sha256: String,
    identity: ArchivedRunIdentity,
}

fn run_controller(args: &Args) -> Result<(), String> {
    let measure_process = args
        .measure_process
        .as_deref()
        .ok_or("--measure-process is required in controller mode")?;
    let package_harness = args
        .package_harness
        .as_deref()
        .ok_or("--package-harness is required in controller mode")?;
    let output = args
        .output
        .as_deref()
        .ok_or("--output is required in controller mode")?;
    let manifest = read_json_input(&args.fixture_manifest, "fixture manifest")?;
    validate_manifest(&manifest)?;
    let baseline = read_json_input(&args.baseline, "deterministic baseline")?;
    validate_baseline(&baseline)?;
    let fixture_manifest_sha256 = sha256_bytes(manifest.as_bytes());
    validate_baseline_manifest_hash(&baseline, &fixture_manifest_sha256)?;
    let deterministic_baseline_sha256 = sha256_bytes(baseline.as_bytes());
    let identity = collect_run_identity(
        &fixture_manifest_sha256,
        measure_process,
        package_harness,
        args.elapsed_profile.is_some(),
    )?;
    let profile = match args.elapsed_profile.as_deref() {
        Some(path) => Some(validate_elapsed_profile(
            path,
            &identity,
            &args.fixture_manifest,
            &deterministic_baseline_sha256,
        )?),
        None => None,
    };
    validate_elapsed_profile_for_phase(&args.phase, profile.as_ref())?;
    if args.phase == "recursive"
        && !args
            .review_reason
            .as_deref()
            .is_some_and(|reason| !reason.trim().is_empty())
    {
        return Err("recursive baseline collection requires nonempty --review-reason".to_owned());
    }
    let executable = std::env::current_exe()
        .map_err(|error| format!("resolve micro child executable: {error}"))?;
    let temporary_directory = make_controller_temp_dir()?;
    let micro_snapshot = temporary_directory.create_executable_snapshot(
        Path::new("micro-child"),
        &executable,
        512 * 1024 * 1024,
        "KWHNF micro child",
    )?;
    let package_snapshot = temporary_directory.create_executable_snapshot(
        Path::new("package-child"),
        package_harness,
        512 * 1024 * 1024,
        "KWHNF package child",
    )?;
    let measure_snapshot = temporary_directory.create_executable_snapshot(
        Path::new("measure-process"),
        measure_process,
        512 * 1024 * 1024,
        "KWHNF measure-process",
    )?;
    require_snapshot_hash(
        &micro_snapshot,
        &identity.micro.binary_sha256,
        "micro child",
    )?;
    require_snapshot_hash(
        &package_snapshot,
        &identity.package.binary_sha256,
        "package child",
    )?;
    require_snapshot_hash(
        &measure_snapshot,
        &identity.measure.binary_sha256,
        "measure-process",
    )?;
    let manifest_snapshot = temporary_directory
        .create_input_snapshot(Path::new("fixture-manifest.json"), manifest.as_bytes())?;
    let baseline_snapshot = temporary_directory.create_input_snapshot(
        Path::new("deterministic-baseline.json"),
        baseline.as_bytes(),
    )?;
    let manifest_snapshot_path = temporary_directory.path()?.join("fixture-manifest.json");
    let baseline_snapshot_path = temporary_directory
        .path()?
        .join("deterministic-baseline.json");
    let collection = collect_controller_rows(
        args,
        &measure_snapshot,
        &package_snapshot,
        &micro_snapshot,
        &manifest_snapshot_path,
        &baseline_snapshot_path,
        &manifest_snapshot,
        manifest.as_bytes(),
        &baseline_snapshot,
        baseline.as_bytes(),
        &temporary_directory,
    );
    let rows = collection?;
    validate_controller_rows(&rows, &args.phase)?;
    let summaries = summarize_rows(&rows)?;
    let run_json = controller_report_json(
        args,
        &fixture_manifest_sha256,
        &deterministic_baseline_sha256,
        &identity,
        profile.as_ref(),
        &rows,
        &summaries,
    )?;
    micro_snapshot.verify()?;
    package_snapshot.verify()?;
    measure_snapshot.verify()?;
    verify_input_snapshot(&manifest_snapshot, manifest.as_bytes(), "fixture manifest")?;
    verify_input_snapshot(
        &baseline_snapshot,
        baseline.as_bytes(),
        "deterministic baseline",
    )?;
    drop(micro_snapshot);
    drop(package_snapshot);
    drop(measure_snapshot);
    drop(manifest_snapshot);
    drop(baseline_snapshot);
    temporary_directory.cleanup_exact(whnf_controller_temp_catalog(&args.phase)?)?;
    write_new_file(output, run_json.as_bytes())?;
    Ok(())
}

fn require_snapshot_hash(
    snapshot: &AttachedExecutable,
    expected: &str,
    label: &str,
) -> Result<(), String> {
    if snapshot.sha256() != expected {
        return Err(format!(
            "{label} changed between build-identity hashing and executable snapshotting"
        ));
    }
    snapshot.verify()
}

fn verify_input_snapshot(
    snapshot: &AttachedOutputFile,
    expected: &[u8],
    label: &str,
) -> Result<(), String> {
    if snapshot.read_all_bounded(16 * 1024 * 1024)? != expected {
        return Err(format!("private {label} snapshot bytes changed"));
    }
    Ok(())
}

fn validate_candidate_run_report(args: &Args) -> Result<(), String> {
    let report_path = args
        .validate_report
        .as_deref()
        .ok_or("--validate-report is required in report-validation mode")?;
    let measure_process = args
        .measure_process
        .as_deref()
        .ok_or("--measure-process is required in report-validation mode")?;
    let package_harness = args
        .package_harness
        .as_deref()
        .ok_or("--package-harness is required in report-validation mode")?;
    let manifest = read_json_input(&args.fixture_manifest, "fixture manifest")?;
    validate_manifest(&manifest)?;
    let baseline = read_json_input(&args.baseline, "deterministic baseline")?;
    validate_baseline(&baseline)?;
    let fixture_manifest_sha256 = sha256_bytes(manifest.as_bytes());
    validate_baseline_manifest_hash(&baseline, &fixture_manifest_sha256)?;
    let deterministic_baseline_sha256 = sha256_bytes(baseline.as_bytes());
    let identity = collect_run_identity(
        &fixture_manifest_sha256,
        measure_process,
        package_harness,
        args.elapsed_profile.is_some(),
    )?;
    let profile = match args.elapsed_profile.as_deref() {
        Some(path) => Some(validate_elapsed_profile(
            path,
            &identity,
            &args.fixture_manifest,
            &deterministic_baseline_sha256,
        )?),
        None => None,
    };
    validate_elapsed_profile_for_phase("candidate", profile.as_ref())?;
    let report_bytes = read_bounded_regular_file(report_path, 16 * 1024 * 1024, "run report")?;
    let report =
        std::str::from_utf8(&report_bytes).map_err(|_| "run report must be UTF-8".to_owned())?;
    validate_candidate_run_report_source(
        report,
        args,
        &fixture_manifest_sha256,
        &deterministic_baseline_sha256,
        &identity,
        profile.as_ref(),
    )
}

fn validate_candidate_run_report_source(
    source: &str,
    args: &Args,
    fixture_manifest_sha256: &str,
    deterministic_baseline_sha256: &str,
    identity: &RunIdentity,
    profile: Option<&ElapsedProfile>,
) -> Result<(), String> {
    let document = JsonDocument::parse(source).map_err(|error| {
        format!(
            "invalid run report JSON at {}: {:?}",
            error.offset, error.kind
        )
    })?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "phase",
            "fixture_manifest_sha256",
            "deterministic_baseline_sha256",
            "identity",
            "elapsed_profile_sha256",
            "elapsed_baseline_sha256",
            "warmup_per_child",
            "samples_per_series",
            "collection_order",
            "rows",
            "summaries",
        ],
        "run_report",
    )?;
    expect_string(root[0].value(), RUN_SCHEMA, "run_report.schema")?;
    expect_string(root[1].value(), "candidate", "run_report.phase")?;
    expect_string(
        root[2].value(),
        fixture_manifest_sha256,
        "run_report.fixture_manifest_sha256",
    )?;
    expect_string(
        root[3].value(),
        deterministic_baseline_sha256,
        "run_report.deterministic_baseline_sha256",
    )?;
    if root[4].value().raw_slice() != identity_json(identity) {
        return Err(
            "run_report.identity does not match the current build/runtime identity".to_owned(),
        );
    }
    expect_unsigned_eq(root[7].value(), 1, "run_report.warmup_per_child")?;
    expect_unsigned_eq(root[8].value(), 9, "run_report.samples_per_series")?;
    expect_string(
        root[9].value(),
        "sample-major",
        "run_report.collection_order",
    )?;

    let expected = expected_series("candidate")?;
    let raw_rows = expect_array(root[10].value(), "run_report.rows")?;
    let expected_row_count = expected
        .len()
        .checked_mul(9)
        .ok_or("run-report row count overflow")?;
    if raw_rows.len() != expected_row_count {
        return Err(format!(
            "run_report.rows has {} entries, expected {expected_row_count}",
            raw_rows.len()
        ));
    }
    let mut rows = Vec::with_capacity(raw_rows.len());
    for (index, value) in raw_rows.iter().enumerate() {
        let path = format!("run_report.rows[{index}]");
        let fields = exact_object(
            value,
            &[
                "scenario_id",
                "series_kind",
                "mode",
                "sample_index",
                "operation_elapsed_ns",
                "process_elapsed_ns",
                "peak_rss_kib",
                "child_output_sha256",
            ],
            &path,
        )?;
        let series_index = index % expected.len();
        let sample_index = u64::try_from(index / expected.len())
            .map_err(|_| "run-report sample index does not fit u64")?;
        let (scenario_id, series_kind, mode) = &expected[series_index];
        expect_string(
            fields[0].value(),
            scenario_id,
            &format!("{path}.scenario_id"),
        )?;
        expect_string(
            fields[1].value(),
            series_kind,
            &format!("{path}.series_kind"),
        )?;
        expect_string(fields[2].value(), mode, &format!("{path}.mode"))?;
        expect_unsigned_eq(
            fields[3].value(),
            sample_index,
            &format!("{path}.sample_index"),
        )?;
        let child_output_sha256 = fields[7]
            .value()
            .string_value()
            .ok_or_else(|| format!("{path}.child_output_sha256 must be a string"))?
            .to_owned();
        validate_lower_hex_hash(&child_output_sha256, &format!("{path}.child_output_sha256"))?;
        rows.push(ControllerRow {
            scenario_id: scenario_id.clone(),
            series_kind,
            mode: mode.clone(),
            sample_index,
            operation_elapsed_ns: expect_unsigned(
                fields[4].value(),
                &format!("{path}.operation_elapsed_ns"),
            )?,
            process_elapsed_ns: expect_unsigned(
                fields[5].value(),
                &format!("{path}.process_elapsed_ns"),
            )?,
            peak_rss_kib: expect_unsigned(fields[6].value(), &format!("{path}.peak_rss_kib"))?,
            child_output_sha256,
        });
    }
    validate_controller_rows(&rows, "candidate")?;
    let summaries = summarize_rows(&rows)?;
    let raw_summaries = expect_array(root[11].value(), "run_report.summaries")?;
    if raw_summaries.len() != summaries.len() {
        return Err(format!(
            "run_report.summaries has {} entries, expected {}",
            raw_summaries.len(),
            summaries.len()
        ));
    }
    for (index, (raw, summary)) in raw_summaries.iter().zip(&summaries).enumerate() {
        if raw.raw_slice() != summary_json(summary) {
            return Err(format!(
                "run_report.summaries[{index}] does not exactly summarize its raw rows"
            ));
        }
    }
    let canonical = controller_report_json(
        args,
        fixture_manifest_sha256,
        deterministic_baseline_sha256,
        identity,
        profile,
        &rows,
        &summaries,
    )?;
    if source != canonical {
        return Err("run report is not the exact canonical closed-schema serialization".to_owned());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn collect_controller_rows(
    args: &Args,
    measure_process: &AttachedExecutable,
    package_harness: &AttachedExecutable,
    micro_harness: &AttachedExecutable,
    fixture_manifest: &Path,
    baseline: &Path,
    fixture_manifest_owner: &AttachedOutputFile,
    fixture_manifest_bytes: &[u8],
    baseline_owner: &AttachedOutputFile,
    baseline_bytes: &[u8],
    temporary_directory: &ControllerTempDir,
) -> Result<Vec<ControllerRow>, String> {
    let micro_scenarios = expected_scenarios()
        .into_iter()
        .filter(|scenario| {
            args.phase == "candidate"
                || parse_scenario(scenario)
                    .map(|(_, width, _)| width != 8_192)
                    .unwrap_or(false)
        })
        .collect::<Vec<_>>();
    let expected_rows = if args.phase == "recursive" { 666 } else { 828 };
    let mut rows = Vec::with_capacity(expected_rows);
    for sample_index in 0..9 {
        for scenario in &micro_scenarios {
            let (_, _, mode) = parse_scenario(scenario)
                .ok_or_else(|| format!("catalog scenario no longer parses: {scenario}"))?;
            let arguments = vec![
                "--child".to_owned(),
                "--phase".to_owned(),
                args.phase.clone(),
                "--fixture-manifest".to_owned(),
                fixture_manifest.display().to_string(),
                "--baseline".to_owned(),
                baseline.display().to_string(),
                "--scenario-id".to_owned(),
                scenario.clone(),
                "--sample-index".to_owned(),
                sample_index.to_string(),
            ];
            rows.push(run_measured_child(
                measure_process,
                micro_harness,
                fixture_manifest_owner,
                fixture_manifest_bytes,
                baseline_owner,
                baseline_bytes,
                &arguments,
                MICRO_CHILD_SCHEMA,
                &args.phase,
                scenario,
                "micro",
                mode,
                sample_index,
                temporary_directory,
                rows.len(),
            )?);
        }
        for mode in ["off", "ephemeral"] {
            let scenario = format!("checked-package.{mode}");
            let arguments = vec![
                "--child".to_owned(),
                "--phase".to_owned(),
                args.phase.clone(),
                "--root".to_owned(),
                "testdata/package/proofs".to_owned(),
                "--fixture-manifest".to_owned(),
                fixture_manifest.display().to_string(),
                "--baseline".to_owned(),
                baseline.display().to_string(),
                "--kernel-mode".to_owned(),
                mode.to_owned(),
                "--sample-index".to_owned(),
                sample_index.to_string(),
            ];
            rows.push(run_measured_child(
                measure_process,
                package_harness,
                fixture_manifest_owner,
                fixture_manifest_bytes,
                baseline_owner,
                baseline_bytes,
                &arguments,
                PACKAGE_CHILD_SCHEMA,
                &args.phase,
                &scenario,
                "package",
                mode,
                sample_index,
                temporary_directory,
                rows.len(),
            )?);
        }
    }
    if rows.len() != expected_rows {
        return Err(format!(
            "controller produced {} rows, expected {expected_rows}",
            rows.len()
        ));
    }
    Ok(rows)
}

#[allow(clippy::too_many_arguments)]
fn run_measured_child(
    measure_process: &AttachedExecutable,
    child: &AttachedExecutable,
    fixture_manifest_owner: &AttachedOutputFile,
    fixture_manifest_bytes: &[u8],
    baseline_owner: &AttachedOutputFile,
    baseline_bytes: &[u8],
    child_arguments: &[String],
    schema: &str,
    phase: &str,
    scenario_id: &str,
    series_kind: &'static str,
    mode: &str,
    sample_index: u64,
    temporary_directory: &ControllerTempDir,
    row_index: usize,
) -> Result<ControllerRow, String> {
    measure_process.verify()?;
    child.verify()?;
    verify_input_snapshot(
        fixture_manifest_owner,
        fixture_manifest_bytes,
        "fixture manifest",
    )?;
    verify_input_snapshot(baseline_owner, baseline_bytes, "deterministic baseline")?;
    let child_output_name = PathBuf::from(format!("{row_index:04}.json"));
    let child_stderr_name = PathBuf::from(format!("{row_index:04}.stderr"));
    let child_output = temporary_directory.path()?.join(&child_output_name);
    let child_stderr = temporary_directory.path()?.join(&child_stderr_name);
    let wrapper = Command::new(measure_process.path())
        .arg("--output")
        .arg(&child_output)
        .arg("--stderr")
        .arg(&child_stderr)
        .arg("--")
        .arg(child.path())
        .args(child_arguments)
        .output()
        .map_err(|error| format!("spawn measure_process for {scenario_id}: {error}"))?;
    measure_process.verify()?;
    child.verify()?;
    verify_input_snapshot(
        fixture_manifest_owner,
        fixture_manifest_bytes,
        "fixture manifest",
    )?;
    verify_input_snapshot(baseline_owner, baseline_bytes, "deterministic baseline")?;
    if !wrapper.status.success() {
        return Err(format!(
            "measure_process failed for {scenario_id}: status={:?}, stderr={}",
            wrapper.status.code(),
            String::from_utf8_lossy(&wrapper.stderr)
        ));
    }
    if !wrapper.stderr.is_empty() {
        return Err(format!(
            "measure_process wrote stderr for {scenario_id}: {}",
            String::from_utf8_lossy(&wrapper.stderr)
        ));
    }
    let child_stderr_bytes =
        temporary_directory.read_regular_file(&child_stderr_name, 1024 * 1024)?;
    if !child_stderr_bytes.is_empty() {
        return Err(format!(
            "child wrote stderr for {scenario_id}: {}",
            String::from_utf8_lossy(&child_stderr_bytes)
        ));
    }
    let (process_elapsed_ns, peak_rss_kib) = parse_measure_process_tsv(
        &String::from_utf8(wrapper.stdout)
            .map_err(|error| format!("wrapper TSV is not UTF-8: {error}"))?,
    )?;
    let child_bytes =
        temporary_directory.read_regular_file(&child_output_name, 16 * 1024 * 1024)?;
    let child_text = std::str::from_utf8(&child_bytes)
        .map_err(|error| format!("child output is not UTF-8: {error}"))?;
    let child_json = child_text
        .strip_suffix('\n')
        .ok_or("child output must end with exactly one newline")?;
    if child_json.contains(['\n', '\r']) || child_json.trim() != child_json {
        return Err("child output is not one canonical JSON line".to_owned());
    }
    validate_child_output(child_json, schema, phase, scenario_id, mode, sample_index)?;
    let operation_elapsed_ns = extract_u64_field(child_json, "operation_elapsed_ns")?;
    Ok(ControllerRow {
        scenario_id: scenario_id.to_owned(),
        series_kind,
        mode: mode.to_owned(),
        sample_index,
        operation_elapsed_ns,
        process_elapsed_ns,
        peak_rss_kib,
        child_output_sha256: sha256_bytes(&child_bytes),
    })
}

fn validate_child_output(
    source: &str,
    schema: &str,
    phase: &str,
    scenario_id: &str,
    mode: &str,
    sample_index: u64,
) -> Result<(), String> {
    let document = JsonDocument::parse(source)
        .map_err(|error| format!("invalid child JSON at {}: {:?}", error.offset, error.kind))?;
    if schema == MICRO_CHILD_SCHEMA {
        let fields = exact_object(
            document.root(),
            &[
                "schema",
                "phase",
                "scenario_id",
                "sample_index",
                "mode",
                "operation_elapsed_ns",
                "result",
                "error",
                "work",
                "named_delta_events",
            ],
            "micro_child",
        )?;
        expect_string(fields[0].value(), schema, "micro_child.schema")?;
        expect_string(fields[1].value(), phase, "micro_child.phase")?;
        expect_string(fields[2].value(), scenario_id, "micro_child.scenario_id")?;
        expect_unsigned_eq(fields[3].value(), sample_index, "micro_child.sample_index")?;
        expect_string(fields[4].value(), mode, "micro_child.mode")?;
        expect_unsigned(fields[5].value(), "micro_child.operation_elapsed_ns")?;
        let (kind, _, _) = parse_scenario(scenario_id).ok_or("unknown child scenario")?;
        validate_result(fields[6].value(), kind, "micro_child.result")?;
        expect_kind(fields[7].value(), JsonValueKind::Null, "micro_child.error")?;
        validate_work(fields[8].value(), "micro_child.work")?;
        let events = expect_array(fields[9].value(), "micro_child.named_delta_events")?;
        if kind == "delta-exposed-long-spine" {
            if events.len() != 1 {
                return Err("micro_child.named_delta_events must contain one event".to_owned());
            }
            expect_string(
                &events[0],
                "Bench.KernelWhnfApplicationSpine.deltaHead",
                "micro_child.named_delta_events[0]",
            )?;
        } else if !events.is_empty() {
            return Err("micro_child.named_delta_events must be empty".to_owned());
        }
    } else {
        if schema != PACKAGE_CHILD_SCHEMA {
            return Err(format!("unknown child schema {schema}"));
        }
        let fields = exact_object(
            document.root(),
            &[
                "schema",
                "phase",
                "scenario_id",
                "sample_index",
                "kernel_mode",
                "operation_elapsed_ns",
                "accepted",
                "module_order",
                "verified_modules",
                "input_certificate_hashes",
                "aggregate_work",
            ],
            "package_child",
        )?;
        expect_string(fields[0].value(), schema, "package_child.schema")?;
        expect_string(fields[1].value(), phase, "package_child.phase")?;
        expect_string(fields[2].value(), scenario_id, "package_child.scenario_id")?;
        expect_unsigned_eq(
            fields[3].value(),
            sample_index,
            "package_child.sample_index",
        )?;
        expect_string(fields[4].value(), mode, "package_child.kernel_mode")?;
        expect_unsigned(fields[5].value(), "package_child.operation_elapsed_ns")?;
        expect_bool(fields[6].value(), true, "package_child.accepted")?;
        validate_string_array(fields[7].value(), "package_child.module_order", false)?;
        validate_verified_modules(fields[8].value(), "package_child.verified_modules")?;
        validate_input_hashes(fields[9].value(), "package_child.input_certificate_hashes")?;
        validate_work(fields[10].value(), "package_child.aggregate_work")?;
    }
    Ok(())
}

fn parse_measure_process_tsv(source: &str) -> Result<(u64, u64), String> {
    let row = source
        .strip_suffix('\n')
        .ok_or("wrapper TSV must end with exactly one newline")?;
    if row.contains(['\n', '\r']) || row.trim() != row {
        return Err("wrapper TSV is not one canonical line".to_owned());
    }
    let mut fields = row.split('\t');
    let seconds = fields.next().ok_or("wrapper TSV lacks elapsed seconds")?;
    let peak_rss_kib = fields
        .next()
        .ok_or("wrapper TSV lacks peak RSS")?
        .parse::<u64>()
        .map_err(|_| "wrapper peak RSS is not unsigned".to_owned())?;
    let exit_code = fields
        .next()
        .ok_or("wrapper TSV lacks exit code")?
        .parse::<u32>()
        .map_err(|_| "wrapper exit code is not unsigned".to_owned())?;
    if fields.next().is_some() || exit_code != 0 {
        return Err(format!(
            "invalid wrapper TSV or child exit code {exit_code}"
        ));
    }
    let process_elapsed_ns = parse_nine_decimal_seconds(seconds)?;
    Ok((process_elapsed_ns, peak_rss_kib))
}

fn parse_nine_decimal_seconds(source: &str) -> Result<u64, String> {
    let (seconds, fraction) = source
        .split_once('.')
        .ok_or("wrapper elapsed seconds lacks decimal point")?;
    if seconds.is_empty()
        || fraction.len() != 9
        || !seconds.bytes().all(|byte| byte.is_ascii_digit())
        || !fraction.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err("wrapper elapsed seconds is not canonical nine-decimal syntax".to_owned());
    }
    seconds
        .parse::<u64>()
        .map_err(|_| "wrapper elapsed seconds overflows".to_owned())?
        .checked_mul(1_000_000_000)
        .and_then(|whole| {
            fraction
                .parse::<u64>()
                .ok()
                .and_then(|part| whole.checked_add(part))
        })
        .ok_or_else(|| "wrapper elapsed nanoseconds overflow".to_owned())
}

fn extract_u64_field(source: &str, field: &str) -> Result<u64, String> {
    let marker = format!("\"{field}\":");
    let value = source
        .split_once(&marker)
        .ok_or_else(|| format!("missing child field {field}"))?
        .1;
    let digits = value
        .bytes()
        .take_while(|byte| byte.is_ascii_digit())
        .collect::<Vec<_>>();
    if digits.is_empty() {
        return Err(format!("child field {field} is not unsigned"));
    }
    std::str::from_utf8(&digits)
        .map_err(|error| error.to_string())?
        .parse()
        .map_err(|_| format!("child field {field} overflows"))
}

fn validate_controller_rows(rows: &[ControllerRow], phase: &str) -> Result<(), String> {
    let scenarios = expected_series(phase)?;
    let expected_count = scenarios
        .len()
        .checked_mul(9)
        .ok_or("expected row count overflow")?;
    if rows.len() != expected_count {
        return Err(format!(
            "controller row count {}, expected {expected_count}",
            rows.len()
        ));
    }
    for sample_index in 0..9 {
        for (series_index, (scenario_id, series_kind, mode)) in scenarios.iter().enumerate() {
            let index = usize::try_from(sample_index)
                .map_err(|_| "sample index does not fit usize")?
                .checked_mul(scenarios.len())
                .and_then(|base| base.checked_add(series_index))
                .ok_or("controller row index overflow")?;
            let row = &rows[index];
            if row.sample_index != sample_index
                || &row.scenario_id != scenario_id
                || row.series_kind != *series_kind
                || &row.mode != mode
            {
                return Err(format!("controller collection-order drift at row {index}"));
            }
        }
    }
    Ok(())
}

fn expected_series(phase: &str) -> Result<Vec<(String, &'static str, String)>, String> {
    let mut result = expected_scenarios()
        .into_iter()
        .filter(|scenario| {
            phase == "candidate"
                || parse_scenario(scenario)
                    .map(|(_, width, _)| width != 8_192)
                    .unwrap_or(false)
        })
        .map(|scenario| {
            let mode = parse_scenario(&scenario)
                .ok_or_else(|| format!("catalog scenario no longer parses: {scenario}"))?
                .2
                .to_owned();
            Ok((scenario, "micro", mode))
        })
        .collect::<Result<Vec<_>, String>>()?;
    result.push((
        "checked-package.off".to_owned(),
        "package",
        "off".to_owned(),
    ));
    result.push((
        "checked-package.ephemeral".to_owned(),
        "package",
        "ephemeral".to_owned(),
    ));
    Ok(result)
}

fn summarize_rows(rows: &[ControllerRow]) -> Result<Vec<SeriesSummary>, String> {
    let mut grouped = BTreeMap::<(String, &'static str, String), Vec<&ControllerRow>>::new();
    for row in rows {
        grouped
            .entry((row.scenario_id.clone(), row.series_kind, row.mode.clone()))
            .or_default()
            .push(row);
    }
    let first_phase = if rows.len() == 666 {
        "recursive"
    } else {
        "candidate"
    };
    expected_series(first_phase)?
        .into_iter()
        .map(|key| {
            let selected = grouped
                .remove(&key)
                .ok_or_else(|| format!("missing series {}", key.0))?;
            if selected.len() != 9
                || !selected
                    .iter()
                    .enumerate()
                    .all(|(index, row)| row.sample_index == index as u64)
            {
                return Err(format!("series {} has invalid sample indexes", key.0));
            }
            let samples_ns = selected
                .iter()
                .map(|row| row.operation_elapsed_ns)
                .collect::<Vec<_>>();
            let process_samples_ns = selected
                .iter()
                .map(|row| row.process_elapsed_ns)
                .collect::<Vec<_>>();
            let peak_rss_samples_kib = selected
                .iter()
                .map(|row| row.peak_rss_kib)
                .collect::<Vec<_>>();
            let median_ns = median(&samples_ns)?;
            let deviations = samples_ns
                .iter()
                .map(|sample| sample.abs_diff(median_ns))
                .collect::<Vec<_>>();
            Ok(SeriesSummary {
                scenario_id: key.0,
                series_kind: key.1,
                mode: key.2,
                median_ns,
                median_absolute_deviation_ns: median(&deviations)?,
                min_ns: *samples_ns.iter().min().ok_or("empty sample series")?,
                max_ns: *samples_ns.iter().max().ok_or("empty sample series")?,
                peak_rss_kib: *peak_rss_samples_kib
                    .iter()
                    .max()
                    .ok_or("empty RSS series")?,
                samples_ns,
                process_samples_ns,
                peak_rss_samples_kib,
            })
        })
        .collect()
}

fn median(values: &[u64]) -> Result<u64, String> {
    if values.len() != 9 {
        return Err("median requires exactly nine samples".to_owned());
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    Ok(sorted[4])
}

fn controller_report_json(
    args: &Args,
    fixture_manifest_sha256: &str,
    deterministic_baseline_sha256: &str,
    identity: &RunIdentity,
    profile: Option<&ElapsedProfile>,
    rows: &[ControllerRow],
    summaries: &[SeriesSummary],
) -> Result<String, String> {
    let (schema, elapsed_profile_sha256, elapsed_baseline_sha256) = if args.phase == "recursive" {
        (
            ELAPSED_BASELINE_SCHEMA,
            "null".to_owned(),
            "null".to_owned(),
        )
    } else {
        match profile {
            Some(profile) => {
                validate_elapsed_gates(profile, summaries)?;
                (
                    RUN_SCHEMA,
                    quoted(&profile.sha256),
                    quoted(&profile.baseline_sha256),
                )
            }
            None => (RUN_SCHEMA, "null".to_owned(), "null".to_owned()),
        }
    };
    Ok(format!(
        "{{\"schema\":\"{schema}\",\"phase\":\"{}\",\"fixture_manifest_sha256\":\"{fixture_manifest_sha256}\",\"deterministic_baseline_sha256\":\"{deterministic_baseline_sha256}\",\"identity\":{},\"elapsed_profile_sha256\":{elapsed_profile_sha256},\"elapsed_baseline_sha256\":{elapsed_baseline_sha256},\"warmup_per_child\":1,\"samples_per_series\":9,\"collection_order\":\"sample-major\",\"rows\":[{}],\"summaries\":[{}]}}",
        args.phase,
        identity_json(identity),
        rows.iter().map(controller_row_json).collect::<Vec<_>>().join(","),
        summaries.iter().map(summary_json).collect::<Vec<_>>().join(","),
    ))
}

fn controller_row_json(row: &ControllerRow) -> String {
    format!(
        "{{\"scenario_id\":\"{}\",\"series_kind\":\"{}\",\"mode\":\"{}\",\"sample_index\":{},\"operation_elapsed_ns\":{},\"process_elapsed_ns\":{},\"peak_rss_kib\":{},\"child_output_sha256\":\"{}\"}}",
        row.scenario_id,
        row.series_kind,
        row.mode,
        row.sample_index,
        row.operation_elapsed_ns,
        row.process_elapsed_ns,
        row.peak_rss_kib,
        row.child_output_sha256,
    )
}

fn summary_json(summary: &SeriesSummary) -> String {
    format!(
        "{{\"scenario_id\":\"{}\",\"series_kind\":\"{}\",\"mode\":\"{}\",\"samples_ns\":{},\"process_samples_ns\":{},\"peak_rss_samples_kib\":{},\"median_ns\":{},\"median_absolute_deviation_ns\":{},\"min_ns\":{},\"max_ns\":{},\"peak_rss_kib\":{}}}",
        summary.scenario_id,
        summary.series_kind,
        summary.mode,
        u64_array_json(&summary.samples_ns),
        u64_array_json(&summary.process_samples_ns),
        u64_array_json(&summary.peak_rss_samples_kib),
        summary.median_ns,
        summary.median_absolute_deviation_ns,
        summary.min_ns,
        summary.max_ns,
        summary.peak_rss_kib,
    )
}

fn u64_array_json(values: &[u64]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn quoted(value: &str) -> String {
    format!("\"{}\"", json_escape(value))
}

fn json_escape(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '\"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                output.push_str(&format!("\\u{:04x}", u32::from(character)))
            }
            character => output.push(character),
        }
    }
    output
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let hash = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in hash {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

fn sha256_file(path: &Path) -> Result<String, String> {
    read_absolute_regular_file(path, 512 * 1024 * 1024, "KWHNF hashed input")
        .map(|bytes| sha256_bytes(&bytes))
}

fn read_bounded_regular_file(
    path: &Path,
    maximum_bytes: u64,
    label: &str,
) -> Result<Vec<u8>, String> {
    read_absolute_regular_file(path, maximum_bytes, label)
}

fn read_json_input(path: &Path, label: &str) -> Result<String, String> {
    let bytes = read_invocation_regular_file(path, 16 * 1024 * 1024, label)?;
    String::from_utf8(bytes).map_err(|_| format!("{label} must be UTF-8"))
}

fn collect_run_identity(
    fixture_manifest_sha256: &str,
    measure_process: &Path,
    package_harness: &Path,
    blocking: bool,
) -> Result<RunIdentity, String> {
    let source_identity = command_stdout("/usr/bin/git", &["rev-parse", "HEAD"])?;
    let dirty_output = command_stdout(
        "/usr/bin/git",
        &["status", "--porcelain", "--untracked-files=all"],
    )?;
    let dirty = !dirty_output.is_empty();
    if blocking && dirty {
        return Err("blocking elapsed run requires a clean checkout".to_owned());
    }
    let runtime_source_identity = if dirty {
        format!("{source_identity}-dirty")
    } else {
        source_identity
    };
    let build_source_identity = env!("NPA_BUILD_SOURCE_IDENTITY");
    validate_build_bound_source_identity(build_source_identity, &runtime_source_identity)?;
    let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?;
    let target = env!("NPA_BUILD_TARGET").to_owned();
    let current_exe =
        std::env::current_exe().map_err(|error| format!("resolve current executable: {error}"))?;
    let micro = executable_identity(
        MICRO_SOURCE_PATH,
        env!("NPA_BUILD_WHNF_MICRO_SOURCE_SHA256"),
        MICRO_BINARY_PATH,
        &current_exe,
        true,
    )?;
    let package = executable_identity(
        PACKAGE_SOURCE_PATH,
        env!("NPA_BUILD_WHNF_PACKAGE_SOURCE_SHA256"),
        PACKAGE_BINARY_PATH,
        package_harness,
        true,
    )?;
    let measure = executable_identity(
        MEASURE_SOURCE_PATH,
        env!("NPA_BUILD_MEASURE_PROCESS_SOURCE_SHA256"),
        MEASURE_BINARY_PATH,
        measure_process,
        true,
    )?;
    let (kwhnf_source_set_sha256, kwhnf_source_set_paths) = validate_runtime_kwhnf_source_set()?;
    Ok(RunIdentity {
        source_identity: format!("git:{build_source_identity}"),
        dirty,
        cargo_lock_sha256: embedded_file_hash_matches_runtime(
            "Cargo.lock",
            env!("NPA_BUILD_CARGO_LOCK_SHA256"),
        )?,
        kwhnf_source_set_sha256,
        kwhnf_source_set_paths,
        rustc_vv,
        target,
        profile: env!("NPA_BUILD_CARGO_PROFILE"),
        features: embedded_build_features(),
        rustflags: decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?,
        fixture_manifest_sha256: fixture_manifest_sha256.to_owned(),
        micro,
        package,
        measure,
    })
}

#[cfg(test)]
fn assert_snapshot_rejects_swap(
    temporary_directory: &ControllerTempDir,
    source: &Path,
) -> Result<(), String> {
    let snapshot = temporary_directory.create_executable_snapshot(
        Path::new("snapshot-swap-probe"),
        source,
        512 * 1024 * 1024,
        "KWHNF swap probe",
    )?;
    let path = snapshot.path().to_owned();
    let relocated = path.with_extension("opened");
    std::fs::rename(&path, &relocated).map_err(|error| error.to_string())?;
    std::fs::write(&path, b"replacement").map_err(|error| error.to_string())?;
    let result = snapshot.verify();
    std::fs::remove_file(&path).map_err(|error| error.to_string())?;
    std::fs::rename(&relocated, &path).map_err(|error| error.to_string())?;
    drop(snapshot);
    if result.is_ok() {
        return Err("attached executable accepted a swapped basename".to_owned());
    }
    Ok(())
}

fn validate_build_bound_source_identity(
    build_identity: &str,
    runtime_identity: &str,
) -> Result<(), String> {
    let valid = |value: &str| {
        let oid = value.strip_suffix("-dirty").unwrap_or(value);
        oid.len() == 40
            && oid
                .bytes()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    };
    if build_identity == "unbound" {
        return Err("WHNF release evidence requires a build-bound source identity".to_owned());
    }
    if !valid(build_identity) || !valid(runtime_identity) {
        return Err("source identity must be a lowercase Git OID with optional -dirty".to_owned());
    }
    if build_identity != runtime_identity {
        return Err(format!(
            "runtime source identity {runtime_identity} differs from build identity {build_identity}"
        ));
    }
    Ok(())
}

fn embedded_build_features() -> Vec<String> {
    env!("NPA_BUILD_CARGO_FEATURES")
        .split(',')
        .filter(|feature| !feature.is_empty())
        .map(str::to_owned)
        .collect()
}

fn parse_kwhnf_source_set_paths(source: &str) -> Result<Vec<String>, String> {
    let mut paths = Vec::new();
    let mut previous = None::<&str>;
    for relative in source.split(',') {
        if relative.is_empty()
            || relative.starts_with('/')
            || relative
                .split('/')
                .any(|component| matches!(component, "" | "." | ".."))
            || previous.is_some_and(|last| Path::new(last) >= Path::new(relative))
        {
            return Err("invalid embedded KWHNF source-set path/order".to_owned());
        }
        paths.push(relative.to_owned());
        previous = Some(relative);
    }
    if paths.is_empty() {
        return Err("KWHNF source-set path catalog must not be empty".to_owned());
    }
    Ok(paths)
}

fn validate_runtime_kwhnf_source_set() -> Result<(String, Vec<String>), String> {
    let workspace = std::fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."))
        .map_err(|error| format!("canonicalize KWHNF workspace: {error}"))?;
    let paths = parse_kwhnf_source_set_paths(env!("NPA_BUILD_KWHNF_SOURCE_SET_PATHS"))?;
    let expected = env!("NPA_BUILD_KWHNF_SOURCE_SET_SHA256");
    runtime_source_set::validate_runtime_source_set(
        &workspace,
        env!("NPA_BUILD_KWHNF_SOURCE_SET_PATHS"),
        b"npa-kwhnf-source-set-v2\0",
        expected,
        "KWHNF",
    )?;
    Ok((expected.to_owned(), paths))
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

fn executable_identity(
    source_path: &'static str,
    build_source_sha256: &'static str,
    binary_path: &'static str,
    actual_binary: &Path,
    blocking: bool,
) -> Result<ExecutableIdentity, String> {
    let source_sha256 = embedded_file_hash_matches_runtime(source_path, build_source_sha256)?;
    if blocking {
        let expected = std::fs::canonicalize(binary_path)
            .map_err(|error| format!("canonicalize {binary_path}: {error}"))?;
        let actual = std::fs::canonicalize(actual_binary)
            .map_err(|error| format!("canonicalize {}: {error}", actual_binary.display()))?;
        if expected != actual {
            return Err(format!(
                "blocking executable role mismatch: expected {}, got {}",
                expected.display(),
                actual.display()
            ));
        }
    }
    Ok(ExecutableIdentity {
        source_path,
        source_sha256,
        binary_path,
        binary_sha256: sha256_file(actual_binary)?,
    })
}

fn embedded_file_hash_matches_runtime(path: &str, build_sha256: &str) -> Result<String, String> {
    validate_lower_hex_hash(build_sha256, "embedded build file hash")?;
    let runtime_path = runtime_workspace_root()?.join(path);
    let runtime = sha256_file(&runtime_path)?;
    if runtime != build_sha256 {
        return Err(format!(
            "runtime file does not match the bytes used for this binary: {path}"
        ));
    }
    Ok(build_sha256.to_owned())
}

fn command_stdout(program: &str, arguments: &[&str]) -> Result<String, String> {
    let output = Command::new(program)
        .args(arguments)
        .current_dir(runtime_workspace_root()?)
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
        .map(|value| value.trim_end().to_owned())
        .map_err(|error| format!("{program} output is not UTF-8: {error}"))
}

fn runtime_workspace_root() -> Result<PathBuf, String> {
    std::fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."))
        .map_err(|error| format!("canonicalize KWHNF workspace: {error}"))
}

fn identity_json(identity: &RunIdentity) -> String {
    format!(
        "{{\"source_identity\":{},\"dirty\":{},\"cargo_lock_sha256\":\"{}\",\"kwhnf_source_set_sha256\":\"{}\",\"kwhnf_source_set_paths\":{},\"rustc_vv\":{},\"target\":{},\"profile\":\"{}\",\"features\":{},\"rustflags\":{},\"fixture_manifest_sha256\":\"{}\",\"executables\":{{\"micro_child\":{},\"package_child\":{},\"measure_process\":{}}}}}",
        quoted(&identity.source_identity),
        identity.dirty,
        identity.cargo_lock_sha256,
        identity.kwhnf_source_set_sha256,
        json_string_array(&identity.kwhnf_source_set_paths),
        quoted(&identity.rustc_vv),
        quoted(&identity.target),
        identity.profile,
        json_string_array(&identity.features),
        quoted(&identity.rustflags),
        identity.fixture_manifest_sha256,
        executable_identity_json(&identity.micro),
        executable_identity_json(&identity.package),
        executable_identity_json(&identity.measure),
    )
}

fn executable_identity_json(identity: &ExecutableIdentity) -> String {
    format!(
        "{{\"source_path\":\"{}\",\"source_sha256\":\"{}\",\"binary_path\":\"{}\",\"binary_sha256\":\"{}\"}}",
        identity.source_path,
        identity.source_sha256,
        identity.binary_path,
        identity.binary_sha256,
    )
}

fn json_string_array(values: &[String]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| quoted(value))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn parse_archived_executable_identity(
    value: &JsonValue<'_>,
    path: &str,
    expected_source_path: &str,
    expected_binary_path: &str,
) -> Result<ArchivedExecutableIdentity, String> {
    let fields = exact_object(
        value,
        &[
            "source_path",
            "source_sha256",
            "binary_path",
            "binary_sha256",
        ],
        path,
    )?;
    let source_path = fields[0]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.source_path must be a string"))?;
    if source_path != expected_source_path {
        return Err(format!("{path}.source_path must be {expected_source_path}"));
    }
    let source_sha256 = fields[1]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.source_sha256 must be a string"))?;
    validate_lower_hex_hash(source_sha256, &format!("{path}.source_sha256"))?;
    let binary_path = fields[2]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.binary_path must be a string"))?;
    if binary_path != expected_binary_path {
        return Err(format!("{path}.binary_path must be {expected_binary_path}"));
    }
    let binary_sha256 = fields[3]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.binary_sha256 must be a string"))?;
    validate_lower_hex_hash(binary_sha256, &format!("{path}.binary_sha256"))?;
    Ok(ArchivedExecutableIdentity {
        source_path: source_path.to_owned(),
        source_sha256: source_sha256.to_owned(),
        binary_path: binary_path.to_owned(),
        binary_sha256: binary_sha256.to_owned(),
    })
}

fn parse_archived_run_identity(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<ArchivedRunIdentity, String> {
    let fields = exact_object(
        value,
        &[
            "source_identity",
            "dirty",
            "cargo_lock_sha256",
            "kwhnf_source_set_sha256",
            "kwhnf_source_set_paths",
            "rustc_vv",
            "target",
            "profile",
            "features",
            "rustflags",
            "fixture_manifest_sha256",
            "executables",
        ],
        path,
    )?;
    let source_identity = fields[0]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.source_identity must be a string"))?;
    if source_identity.len() != 44
        || !source_identity.starts_with("git:")
        || !source_identity[4..]
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return Err(format!("{path}.source_identity must be git:<40-hex>"));
    }
    expect_bool(fields[1].value(), false, &format!("{path}.dirty"))?;
    let cargo_lock_sha256 = fields[2]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.cargo_lock_sha256 must be a string"))?;
    validate_lower_hex_hash(cargo_lock_sha256, &format!("{path}.cargo_lock_sha256"))?;
    let kwhnf_source_set_sha256 = fields[3]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.kwhnf_source_set_sha256 must be a string"))?;
    validate_lower_hex_hash(
        kwhnf_source_set_sha256,
        &format!("{path}.kwhnf_source_set_sha256"),
    )?;
    let source_path_values =
        expect_array(fields[4].value(), &format!("{path}.kwhnf_source_set_paths"))?;
    let kwhnf_source_set_paths = source_path_values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value
                .string_value()
                .map(str::to_owned)
                .ok_or_else(|| format!("{path}.kwhnf_source_set_paths[{index}] must be a string"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let joined_source_paths = kwhnf_source_set_paths.join(",");
    if parse_kwhnf_source_set_paths(&joined_source_paths)? != kwhnf_source_set_paths {
        return Err(format!("{path}.kwhnf_source_set_paths must be canonical"));
    }
    let rustc_vv = fields[5]
        .value()
        .string_value()
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| format!("{path}.rustc_vv must be a nonempty string"))?;
    let target = fields[6]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.target must be a string"))?;
    if target != "x86_64-unknown-linux-gnu" {
        return Err(format!("{path}.target must be x86_64-unknown-linux-gnu"));
    }
    let profile = fields[7]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.profile must be a string"))?;
    if profile != "release" {
        return Err(format!("{path}.profile must be release"));
    }
    let feature_values = expect_array(fields[8].value(), &format!("{path}.features"))?;
    let features = feature_values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value
                .string_value()
                .map(str::to_owned)
                .ok_or_else(|| format!("{path}.features[{index}] must be a string"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if features.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(format!("{path}.features must be sorted and duplicate-free"));
    }
    let rustflags = fields[9]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.rustflags must be a string"))?;
    let fixture_manifest_sha256 = fields[10]
        .value()
        .string_value()
        .ok_or_else(|| format!("{path}.fixture_manifest_sha256 must be a string"))?;
    validate_lower_hex_hash(
        fixture_manifest_sha256,
        &format!("{path}.fixture_manifest_sha256"),
    )?;
    let executable_roles = exact_object(
        fields[11].value(),
        &["micro_child", "package_child", "measure_process"],
        &format!("{path}.executables"),
    )?;
    let micro = parse_archived_executable_identity(
        executable_roles[0].value(),
        &format!("{path}.executables.micro_child"),
        MICRO_SOURCE_PATH,
        MICRO_BINARY_PATH,
    )?;
    let package = parse_archived_executable_identity(
        executable_roles[1].value(),
        &format!("{path}.executables.package_child"),
        PACKAGE_SOURCE_PATH,
        PACKAGE_BINARY_PATH,
    )?;
    let measure = parse_archived_executable_identity(
        executable_roles[2].value(),
        &format!("{path}.executables.measure_process"),
        MEASURE_SOURCE_PATH,
        MEASURE_BINARY_PATH,
    )?;
    Ok(ArchivedRunIdentity {
        source_identity: source_identity.to_owned(),
        cargo_lock_sha256: cargo_lock_sha256.to_owned(),
        kwhnf_source_set_sha256: kwhnf_source_set_sha256.to_owned(),
        kwhnf_source_set_paths,
        rustc_vv: rustc_vv.to_owned(),
        target: target.to_owned(),
        profile: profile.to_owned(),
        features,
        rustflags: rustflags.to_owned(),
        fixture_manifest_sha256: fixture_manifest_sha256.to_owned(),
        micro,
        package,
        measure,
    })
}

fn parse_pre_switch_artifact(
    source: &str,
    expected_fixture_manifest_sha256: &str,
    expected_deterministic_baseline_sha256: &str,
) -> Result<PreSwitchArtifact, String> {
    let document = JsonDocument::parse(source).map_err(|error| {
        format!(
            "invalid pre-switch artifact JSON at {}: {:?}",
            error.offset, error.kind
        )
    })?;
    let fields = exact_object(
        document.root(),
        &[
            "schema",
            "implementation",
            "archive_root",
            "deterministic_baseline_sha256",
            "identity",
        ],
        "pre_switch_artifact",
    )?;
    expect_string(
        fields[0].value(),
        PRE_SWITCH_ARTIFACT_SCHEMA,
        "pre_switch_artifact.schema",
    )?;
    expect_string(
        fields[1].value(),
        PRE_SWITCH_IMPLEMENTATION,
        "pre_switch_artifact.implementation",
    )?;
    let archive_root = PathBuf::from(
        fields[2]
            .value()
            .string_value()
            .ok_or("pre_switch_artifact.archive_root must be a string")?,
    );
    if !archive_root.is_absolute() {
        return Err("pre_switch_artifact.archive_root must be absolute".to_owned());
    }
    let deterministic_baseline_sha256 = fields[3]
        .value()
        .string_value()
        .ok_or("pre_switch_artifact.deterministic_baseline_sha256 must be a string")?;
    expect_string(
        fields[3].value(),
        expected_deterministic_baseline_sha256,
        "pre_switch_artifact.deterministic_baseline_sha256",
    )?;
    let identity = parse_archived_run_identity(fields[4].value(), "pre_switch_artifact.identity")?;
    if identity.fixture_manifest_sha256 != expected_fixture_manifest_sha256 {
        return Err("pre-switch artifact fixture-manifest hash mismatch".to_owned());
    }
    Ok(PreSwitchArtifact {
        archive_root,
        deterministic_baseline_sha256: deterministic_baseline_sha256.to_owned(),
        identity,
    })
}

fn validate_pre_switch_artifact_files(artifact: &PreSwitchArtifact) -> Result<(), String> {
    let archive_root = canonical_archive_root(&artifact.archive_root)?;
    let archive_root_text = archive_root
        .to_str()
        .ok_or("pre-switch archive root must be UTF-8")?;
    let archived_head = command_stdout(
        "/usr/bin/git",
        &["-C", archive_root_text, "rev-parse", "HEAD"],
    )?;
    if artifact.identity.source_identity != format!("git:{archived_head}") {
        return Err("pre-switch artifact Git source identity mismatch".to_owned());
    }
    let archived_dirty = command_stdout(
        "/usr/bin/git",
        &[
            "-C",
            archive_root_text,
            "status",
            "--porcelain",
            "--untracked-files=all",
        ],
    )?;
    if !archived_dirty.is_empty() {
        return Err("pre-switch archive checkout must be clean".to_owned());
    }
    let current_head = command_stdout("/usr/bin/git", &["rev-parse", "HEAD"])?;
    if current_head == archived_head {
        return Err(
            "pre-switch archive source identity must differ from the post-switch checkout"
                .to_owned(),
        );
    }
    let cargo_lock = canonical_archive_regular_file(&archive_root, "Cargo.lock")?;
    if sha256_file(&cargo_lock)? != artifact.identity.cargo_lock_sha256 {
        return Err("pre-switch artifact Cargo.lock hash mismatch".to_owned());
    }
    if archived_kwhnf_source_set_sha256(&archive_root, &artifact.identity.kwhnf_source_set_paths)?
        != artifact.identity.kwhnf_source_set_sha256
    {
        return Err("pre-switch artifact KWHNF source-set hash mismatch".to_owned());
    }
    let fixture_manifest = canonical_archive_regular_file(&archive_root, FIXTURE_MANIFEST_PATH)?;
    if sha256_file(&fixture_manifest)? != artifact.identity.fixture_manifest_sha256 {
        return Err("pre-switch artifact fixture-manifest file hash mismatch".to_owned());
    }
    let deterministic_baseline =
        canonical_archive_regular_file(&archive_root, DETERMINISTIC_BASELINE_PATH)?;
    if sha256_file(&deterministic_baseline)? != artifact.deterministic_baseline_sha256 {
        return Err("pre-switch artifact deterministic-baseline file hash mismatch".to_owned());
    }
    for executable in [
        &artifact.identity.micro,
        &artifact.identity.package,
        &artifact.identity.measure,
    ] {
        let source = canonical_archive_regular_file(&archive_root, &executable.source_path)?;
        if sha256_file(&source)? != executable.source_sha256 {
            return Err(format!(
                "pre-switch source hash mismatch for {}",
                executable.source_path
            ));
        }
        let binary = canonical_archive_regular_file(&archive_root, &executable.binary_path)?;
        if sha256_file(&binary)? != executable.binary_sha256 {
            return Err(format!(
                "pre-switch binary hash mismatch for {}",
                executable.binary_path
            ));
        }
    }
    Ok(())
}

fn collect_archived_recursive_baseline(
    archived_artifact_path: &Path,
    fixture_manifest_path: &Path,
    deterministic_baseline_path: &Path,
    output_path: &Path,
    review_reason: &str,
) -> Result<(), String> {
    if review_reason.trim().is_empty() {
        return Err("archived collection review reason must be nonempty".to_owned());
    }
    let artifact = load_and_validate_pre_switch_artifact(
        archived_artifact_path,
        fixture_manifest_path,
        deterministic_baseline_path,
    )?;
    let fixture_manifest = read_json_input(fixture_manifest_path, "fixture manifest")?;
    let deterministic_baseline =
        read_json_input(deterministic_baseline_path, "deterministic baseline")?;
    let temporary = make_controller_temp_dir()?;
    let archived_micro = canonical_archive_regular_file(
        &artifact.archive_root,
        &artifact.identity.micro.binary_path,
    )?;
    let archived_package = canonical_archive_regular_file(
        &artifact.archive_root,
        &artifact.identity.package.binary_path,
    )?;
    let archived_measure = canonical_archive_regular_file(
        &artifact.archive_root,
        &artifact.identity.measure.binary_path,
    )?;
    let micro = temporary.create_executable_snapshot(
        Path::new("micro-child"),
        &archived_micro,
        512 * 1024 * 1024,
        "archived KWHNF controller",
    )?;
    let package = temporary.create_executable_snapshot(
        Path::new("package-child"),
        &archived_package,
        512 * 1024 * 1024,
        "archived KWHNF package child",
    )?;
    let measure = temporary.create_executable_snapshot(
        Path::new("measure-process"),
        &archived_measure,
        512 * 1024 * 1024,
        "archived KWHNF measure-process",
    )?;
    for (snapshot, expected, label) in [
        (
            &micro,
            artifact.identity.micro.binary_sha256.as_str(),
            "micro",
        ),
        (
            &package,
            artifact.identity.package.binary_sha256.as_str(),
            "package",
        ),
        (
            &measure,
            artifact.identity.measure.binary_sha256.as_str(),
            "measure",
        ),
    ] {
        require_snapshot_hash(snapshot, expected, label)?;
    }
    let manifest = temporary.create_input_snapshot(
        Path::new("fixture-manifest.json"),
        fixture_manifest.as_bytes(),
    )?;
    let baseline = temporary.create_input_snapshot(
        Path::new("deterministic-baseline.json"),
        deterministic_baseline.as_bytes(),
    )?;
    let raw_output_path = temporary.path()?.join("recursive.raw.json");
    let arguments = [
        "--controller".to_owned(),
        "--phase".to_owned(),
        "recursive".to_owned(),
        "--fixture-manifest".to_owned(),
        temporary
            .path()?
            .join("fixture-manifest.json")
            .display()
            .to_string(),
        "--baseline".to_owned(),
        temporary
            .path()?
            .join("deterministic-baseline.json")
            .display()
            .to_string(),
        "--measure-process".to_owned(),
        measure.path().display().to_string(),
        "--package-harness".to_owned(),
        package.path().display().to_string(),
        "--output".to_owned(),
        raw_output_path.display().to_string(),
        "--review-reason".to_owned(),
        review_reason.to_owned(),
    ];
    micro.verify()?;
    package.verify()?;
    measure.verify()?;
    verify_input_snapshot(&manifest, fixture_manifest.as_bytes(), "fixture manifest")?;
    verify_input_snapshot(
        &baseline,
        deterministic_baseline.as_bytes(),
        "deterministic baseline",
    )?;
    let status = Command::new(micro.path())
        .args(&arguments)
        .current_dir(&artifact.archive_root)
        .status()
        .map_err(|error| format!("run archived KWHNF controller: {error}"))?;
    micro.verify()?;
    package.verify()?;
    measure.verify()?;
    verify_input_snapshot(&manifest, fixture_manifest.as_bytes(), "fixture manifest")?;
    verify_input_snapshot(
        &baseline,
        deterministic_baseline.as_bytes(),
        "deterministic baseline",
    )?;
    if !status.success() {
        return Err(format!(
            "archived KWHNF controller failed with status {:?}",
            status.code()
        ));
    }
    let raw = temporary
        .directory()?
        .read_regular_file(Path::new("recursive.raw.json"), 64 * 1024 * 1024)?;
    let raw = String::from_utf8(raw).map_err(|_| "archived report must be UTF-8".to_owned())?;
    validate_elapsed_baseline_identity(
        &raw,
        BaselineIdentityExpectation::ArchivedArtifact(&artifact.identity),
        &artifact.deterministic_baseline_sha256,
    )?;
    let canonical = format!("{}\n", compact_json(&raw)?);
    write_new_file(output_path, canonical.as_bytes())?;
    drop(micro);
    drop(package);
    drop(measure);
    drop(manifest);
    drop(baseline);
    temporary.cleanup_exact(BTreeSet::from([
        PathBuf::from("micro-child"),
        PathBuf::from("package-child"),
        PathBuf::from("measure-process"),
        PathBuf::from("fixture-manifest.json"),
        PathBuf::from("deterministic-baseline.json"),
        PathBuf::from("recursive.raw.json"),
    ]))
}

fn archived_kwhnf_source_set_sha256(
    archive_root: &Path,
    source_set_paths: &[String],
) -> Result<String, String> {
    let mut digest = Sha256::new();
    digest.update(b"npa-kwhnf-source-set-v2\0");
    let canonical_paths = parse_kwhnf_source_set_paths(&source_set_paths.join(","))?;
    if canonical_paths != source_set_paths {
        return Err("archived KWHNF source-set paths are not canonical".to_owned());
    }
    for relative in source_set_paths {
        let path = canonical_archive_regular_file(archive_root, relative)?;
        let bytes = read_absolute_regular_file(
            &path,
            64 * 1024 * 1024,
            &format!("archived KWHNF source {relative}"),
        )?;
        digest.update(
            u64::try_from(relative.len())
                .map_err(|_| "KWHNF source path length overflow")?
                .to_le_bytes(),
        );
        digest.update(relative.as_bytes());
        digest.update(
            u64::try_from(bytes.len())
                .map_err(|_| "KWHNF source byte length overflow")?
                .to_le_bytes(),
        );
        digest.update(&bytes);
    }
    Ok(digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn canonical_archive_root(archive_root: &Path) -> Result<PathBuf, String> {
    if !archive_root.is_absolute() {
        return Err("pre-switch archive root must be absolute".to_owned());
    }
    let mut cursor = PathBuf::new();
    for component in archive_root.components() {
        cursor.push(component.as_os_str());
        let metadata = std::fs::symlink_metadata(&cursor).map_err(|error| {
            format!(
                "inspect pre-switch archive component {}: {error}",
                cursor.display()
            )
        })?;
        if metadata.file_type().is_symlink() {
            return Err("pre-switch archive root path must not contain symbolic links".to_owned());
        }
    }
    let metadata = std::fs::symlink_metadata(archive_root).map_err(|error| {
        format!(
            "inspect pre-switch archive root {}: {error}",
            archive_root.display()
        )
    })?;
    if metadata.file_type().is_symlink() {
        return Err("pre-switch archive root must not be a symbolic link".to_owned());
    }
    if !metadata.is_dir() {
        return Err("pre-switch archive root must be a directory".to_owned());
    }
    let canonical = std::fs::canonicalize(archive_root).map_err(|error| {
        format!(
            "canonicalize pre-switch archive root {}: {error}",
            archive_root.display()
        )
    })?;
    if canonical != archive_root {
        return Err("pre-switch archive root must be an absolute canonical path".to_owned());
    }
    Ok(canonical)
}

fn canonical_archive_regular_file(
    canonical_archive_root: &Path,
    relative_path: &str,
) -> Result<PathBuf, String> {
    let relative = Path::new(relative_path);
    if relative.is_absolute() {
        return Err(format!(
            "pre-switch archive file path must be relative: {relative_path}"
        ));
    }
    let components = relative.components().collect::<Vec<_>>();
    if components.is_empty()
        || components
            .iter()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(format!(
            "pre-switch archive file path must contain only normal components: {relative_path}"
        ));
    }
    let mut candidate = canonical_archive_root.to_owned();
    for (index, component) in components.iter().enumerate() {
        candidate.push(component.as_os_str());
        let metadata = std::fs::symlink_metadata(&candidate).map_err(|error| {
            format!(
                "inspect pre-switch archive path {}: {error}",
                candidate.display()
            )
        })?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "pre-switch archive path must not contain symbolic links: {}",
                candidate.display()
            ));
        }
        if index + 1 == components.len() {
            if !metadata.is_file() {
                return Err(format!(
                    "pre-switch archive path must be a regular file: {}",
                    candidate.display()
                ));
            }
        } else if !metadata.is_dir() {
            return Err(format!(
                "pre-switch archive path component must be a directory: {}",
                candidate.display()
            ));
        }
    }
    let canonical = std::fs::canonicalize(&candidate).map_err(|error| {
        format!(
            "canonicalize pre-switch archive file {}: {error}",
            candidate.display()
        )
    })?;
    if !canonical.starts_with(canonical_archive_root) || canonical != candidate {
        return Err(format!(
            "pre-switch archive file escapes its canonical root: {relative_path}"
        ));
    }
    Ok(canonical)
}

fn seal_recursive_baseline(
    raw_baseline_path: &Path,
    archived_artifact_path: &Path,
    fixture_manifest_path: &Path,
    deterministic_baseline_path: &Path,
    output_path: &Path,
) -> Result<(), String> {
    if fixture_manifest_path != Path::new(FIXTURE_MANIFEST_PATH) {
        return Err(format!(
            "seal mode fixture manifest must be {FIXTURE_MANIFEST_PATH}"
        ));
    }
    if deterministic_baseline_path != Path::new(DETERMINISTIC_BASELINE_PATH) {
        return Err(format!(
            "seal mode deterministic baseline must be {DETERMINISTIC_BASELINE_PATH}"
        ));
    }
    let fixture_manifest = read_json_input(fixture_manifest_path, "fixture manifest")?;
    validate_manifest(&fixture_manifest)?;
    let fixture_manifest_sha256 = sha256_bytes(fixture_manifest.as_bytes());
    let deterministic_baseline =
        read_json_input(deterministic_baseline_path, "deterministic baseline")?;
    validate_baseline(&deterministic_baseline)?;
    validate_baseline_manifest_hash(&deterministic_baseline, &fixture_manifest_sha256)?;
    let deterministic_baseline_sha256 = sha256_bytes(deterministic_baseline.as_bytes());
    let artifact_source = read_json_input(archived_artifact_path, "pre-switch artifact")?;
    let artifact = parse_pre_switch_artifact(
        &artifact_source,
        &fixture_manifest_sha256,
        &deterministic_baseline_sha256,
    )?;
    validate_pre_switch_artifact_files(&artifact)?;
    let raw_baseline = read_json_input(raw_baseline_path, "raw recursive baseline")?;
    validate_elapsed_baseline_identity(
        &raw_baseline,
        BaselineIdentityExpectation::ArchivedArtifact(&artifact.identity),
        &deterministic_baseline_sha256,
    )?;
    let canonical = compact_json(&raw_baseline)?;
    let canonical = format!("{canonical}\n");
    write_new_file(output_path, canonical.as_bytes())
}

fn validate_pre_switch_artifact_path(
    archived_artifact_path: &Path,
    fixture_manifest_path: &Path,
    deterministic_baseline_path: &Path,
) -> Result<(), String> {
    load_and_validate_pre_switch_artifact(
        archived_artifact_path,
        fixture_manifest_path,
        deterministic_baseline_path,
    )
    .map(|_| ())
}

fn load_and_validate_pre_switch_artifact(
    archived_artifact_path: &Path,
    fixture_manifest_path: &Path,
    deterministic_baseline_path: &Path,
) -> Result<PreSwitchArtifact, String> {
    if fixture_manifest_path != Path::new(FIXTURE_MANIFEST_PATH) {
        return Err(format!(
            "artifact validation fixture manifest must be {FIXTURE_MANIFEST_PATH}"
        ));
    }
    if deterministic_baseline_path != Path::new(DETERMINISTIC_BASELINE_PATH) {
        return Err(format!(
            "artifact validation deterministic baseline must be {DETERMINISTIC_BASELINE_PATH}"
        ));
    }
    let fixture_manifest = read_json_input(fixture_manifest_path, "fixture manifest")?;
    validate_manifest(&fixture_manifest)?;
    let fixture_manifest_sha256 = sha256_bytes(fixture_manifest.as_bytes());
    let deterministic_baseline =
        read_json_input(deterministic_baseline_path, "deterministic baseline")?;
    validate_baseline(&deterministic_baseline)?;
    validate_baseline_manifest_hash(&deterministic_baseline, &fixture_manifest_sha256)?;
    let deterministic_baseline_sha256 = sha256_bytes(deterministic_baseline.as_bytes());
    let artifact_source = read_json_input(archived_artifact_path, "pre-switch artifact")?;
    let artifact = parse_pre_switch_artifact(
        &artifact_source,
        &fixture_manifest_sha256,
        &deterministic_baseline_sha256,
    )?;
    validate_pre_switch_artifact_files(&artifact)?;
    Ok(artifact)
}

fn validate_bootstrap_profile(
    profile_path: &Path,
    archived_artifact_path: &Path,
    fixture_manifest_path: &Path,
    deterministic_baseline_path: &Path,
    measure_process: &Path,
    package_harness: &Path,
) -> Result<(), String> {
    let artifact = load_and_validate_pre_switch_artifact(
        archived_artifact_path,
        fixture_manifest_path,
        deterministic_baseline_path,
    )?;
    let fixture_manifest = read_json_input(fixture_manifest_path, "fixture manifest")?;
    let fixture_manifest_sha256 = sha256_bytes(fixture_manifest.as_bytes());
    let deterministic_baseline =
        read_json_input(deterministic_baseline_path, "deterministic baseline")?;
    let deterministic_baseline_sha256 = sha256_bytes(deterministic_baseline.as_bytes());
    let identity = collect_run_identity(
        &fixture_manifest_sha256,
        measure_process,
        package_harness,
        true,
    )?;
    validate_archived_identity_expectation(
        &artifact.identity,
        BaselineIdentityExpectation::Candidate(&identity),
    )?;
    let profile = validate_elapsed_profile(
        profile_path,
        &identity,
        fixture_manifest_path,
        &deterministic_baseline_sha256,
    )?;
    validate_elapsed_profile_for_phase("recursive", Some(&profile))?;
    if profile.baseline_summaries.is_some() {
        return Err("bootstrap profile validation requires an absent baseline target".to_owned());
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum BaselineIdentityExpectation<'a> {
    Candidate(&'a RunIdentity),
    ArchivedArtifact(&'a ArchivedRunIdentity),
}

fn validate_archived_identity_expectation(
    observed: &ArchivedRunIdentity,
    expectation: BaselineIdentityExpectation<'_>,
) -> Result<(), String> {
    match expectation {
        BaselineIdentityExpectation::ArchivedArtifact(expected) => {
            if observed != expected {
                return Err("elapsed baseline identity does not match archived artifact".to_owned());
            }
        }
        BaselineIdentityExpectation::Candidate(candidate) => {
            if observed.source_identity == candidate.source_identity {
                return Err(
                    "elapsed baseline must come from a distinct pre-switch source identity"
                        .to_owned(),
                );
            }
            for (label, observed_value, candidate_value) in [
                (
                    "cargo_lock_sha256",
                    observed.cargo_lock_sha256.as_str(),
                    candidate.cargo_lock_sha256.as_str(),
                ),
                (
                    "rustc_vv",
                    observed.rustc_vv.as_str(),
                    candidate.rustc_vv.as_str(),
                ),
                (
                    "target",
                    observed.target.as_str(),
                    candidate.target.as_str(),
                ),
                ("profile", observed.profile.as_str(), candidate.profile),
                (
                    "rustflags",
                    observed.rustflags.as_str(),
                    candidate.rustflags.as_str(),
                ),
                (
                    "fixture_manifest_sha256",
                    observed.fixture_manifest_sha256.as_str(),
                    candidate.fixture_manifest_sha256.as_str(),
                ),
            ] {
                if observed_value != candidate_value {
                    return Err(format!("elapsed baseline identity.{label} mismatch"));
                }
            }
            if observed.features != candidate.features {
                return Err("elapsed baseline identity.features mismatch".to_owned());
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct ElapsedProfile {
    sha256: String,
    baseline_sha256: String,
    baseline_summaries: Option<BTreeMap<(String, String), BaselineSummary>>,
}

#[derive(Clone, Copy, Debug)]
struct BaselineSummary {
    median_ns: u64,
    median_absolute_deviation_ns: u64,
    peak_rss_kib: u64,
}

fn validate_elapsed_profile_for_phase(
    phase: &str,
    profile: Option<&ElapsedProfile>,
) -> Result<(), String> {
    if phase == "candidate" && profile.is_some_and(|profile| profile.baseline_summaries.is_none()) {
        return Err(
            "candidate elapsed profile requires its reviewed baseline file and matching hash"
                .to_owned(),
        );
    }
    Ok(())
}

fn validate_elapsed_profile(
    profile_path: &Path,
    identity: &RunIdentity,
    fixture_manifest_path: &Path,
    deterministic_baseline_sha256: &str,
) -> Result<ElapsedProfile, String> {
    validate_elapsed_profile_with_baseline_path(
        profile_path,
        identity,
        fixture_manifest_path,
        deterministic_baseline_sha256,
        Path::new(REVIEWED_BASELINE_PATH),
    )
}

fn validate_elapsed_profile_with_baseline_path(
    profile_path: &Path,
    identity: &RunIdentity,
    fixture_manifest_path: &Path,
    deterministic_baseline_sha256: &str,
    expected_baseline_path: &Path,
) -> Result<ElapsedProfile, String> {
    let source = read_json_input(profile_path, "elapsed profile")?;
    let document = JsonDocument::parse(&source)
        .map_err(|error| format!("invalid profile JSON at {}: {:?}", error.offset, error.kind))?;
    let profile = exact_object(
        document.root(),
        &[
            "schema",
            "profile_id",
            "host",
            "target",
            "rustc_vv",
            "cargo_profile",
            "features",
            "rustflags",
            "warmup",
            "samples",
            "fixture_manifest_sha256",
            "baseline_path",
            "baseline_hash",
            "review_reason",
            "gates",
        ],
        "elapsed_profile",
    )?;
    expect_string(
        profile[0].value(),
        ELAPSED_PROFILE_SCHEMA,
        "elapsed_profile.schema",
    )?;
    expect_string(
        profile[1].value(),
        REVIEWED_PROFILE_ID,
        "elapsed_profile.profile_id",
    )?;
    if identity.dirty {
        return Err("reviewed elapsed profile requires a clean checkout".to_owned());
    }
    if identity.target != "x86_64-unknown-linux-gnu" {
        return Err(format!(
            "reviewed elapsed profile requires x86_64-unknown-linux-gnu, got {}",
            identity.target
        ));
    }
    if !matches!(
        profile[2].value().string_value(),
        Some(host) if !host.is_empty()
    ) {
        return Err("elapsed_profile.host must be a nonempty reviewed description".to_owned());
    }
    expect_string(
        profile[3].value(),
        &identity.target,
        "elapsed_profile.target",
    )?;
    expect_string(
        profile[4].value(),
        &identity.rustc_vv,
        "elapsed_profile.rustc_vv",
    )?;
    expect_string(
        profile[5].value(),
        identity.profile,
        "elapsed_profile.cargo_profile",
    )?;
    expect_string(
        profile[7].value(),
        &identity.rustflags,
        "elapsed_profile.rustflags",
    )?;
    expect_unsigned_eq(profile[8].value(), 1, "elapsed_profile.warmup")?;
    expect_unsigned_eq(profile[9].value(), 9, "elapsed_profile.samples")?;
    let features = expect_array(profile[6].value(), "elapsed_profile.features")?;
    let parsed_features = features
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value
                .string_value()
                .map(str::to_owned)
                .ok_or_else(|| format!("elapsed_profile.features[{index}] must be a string"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if parsed_features != identity.features
        || parsed_features.windows(2).any(|pair| pair[0] >= pair[1])
    {
        return Err("elapsed_profile.features identity/order mismatch".to_owned());
    }
    let review_reason = profile[13]
        .value()
        .string_value()
        .ok_or("elapsed_profile.review_reason must be a string")?;
    if review_reason.trim().is_empty() {
        return Err("elapsed_profile.review_reason must be nonempty".to_owned());
    }
    let profile_fixture_hash = profile[10]
        .value()
        .string_value()
        .ok_or("elapsed_profile.fixture_manifest_sha256 must be a string")?;
    if profile_fixture_hash != identity.fixture_manifest_sha256 {
        return Err("elapsed profile fixture-manifest hash mismatch".to_owned());
    }
    let baseline_path = PathBuf::from(
        profile[11]
            .value()
            .string_value()
            .ok_or("elapsed_profile.baseline_path must be a string")?,
    );
    if baseline_path != expected_baseline_path {
        return Err(format!(
            "elapsed_profile.baseline_path must be {}",
            expected_baseline_path.display()
        ));
    }
    let baseline_sha256 = profile[12]
        .value()
        .string_value()
        .ok_or("elapsed_profile.baseline_hash must be a string")?
        .to_owned();
    validate_lower_hex_hash(&baseline_sha256, "elapsed profile baseline hash")?;
    let gates = expect_array(profile[14].value(), "elapsed_profile.gates")?;
    let ratios = [(3, 4), (6, 1), (11, 10), (23, 20), (21, 20), (1, 10)];
    if gates.len() != ratios.len() + 2 {
        return Err(
            "elapsed_profile.gates must contain six ratios and two RSS allowances".to_owned(),
        );
    }
    for (index, (gate, (numerator, denominator))) in gates.iter().zip(ratios).enumerate() {
        let path = format!("elapsed_profile.gates[{index}]");
        let fields = exact_object(gate, &["numerator", "denominator"], &path)?;
        expect_unsigned_eq(fields[0].value(), numerator, &format!("{path}.numerator"))?;
        expect_unsigned_eq(
            fields[1].value(),
            denominator,
            &format!("{path}.denominator"),
        )?;
    }
    for (offset, allowance) in [16_384, 8_192].into_iter().enumerate() {
        let index = ratios.len() + offset;
        let path = format!("elapsed_profile.gates[{index}]");
        let fields = exact_object(&gates[index], &["rss"], &path)?;
        expect_unsigned_eq(fields[0].value(), allowance, &format!("{path}.rss"))?;
    }
    let _ = std::fs::canonicalize(fixture_manifest_path)
        .map_err(|error| format!("canonicalize fixture manifest: {error}"))?;
    if !baseline_path.exists() {
        return Ok(ElapsedProfile {
            sha256: sha256_bytes(source.as_bytes()),
            baseline_sha256,
            baseline_summaries: None,
        });
    }
    let actual_baseline_sha256 = sha256_file(&baseline_path)?;
    if actual_baseline_sha256 != baseline_sha256 {
        return Err("elapsed profile baseline hash mismatch".to_owned());
    }
    let baseline_source = read_json_input(&baseline_path, "reviewed elapsed baseline")?;
    let baseline_compact = compact_json(&baseline_source)?;
    if !baseline_compact.contains(&format!("\"schema\":\"{ELAPSED_BASELINE_SCHEMA}\"")) {
        return Err("reviewed elapsed baseline schema mismatch".to_owned());
    }
    if !baseline_compact.contains(&format!(
        "\"fixture_manifest_sha256\":\"{}\"",
        identity.fixture_manifest_sha256
    )) {
        return Err("reviewed elapsed baseline fixture hash mismatch".to_owned());
    }
    let baseline_summaries = validate_elapsed_baseline_identity(
        &baseline_source,
        BaselineIdentityExpectation::Candidate(identity),
        deterministic_baseline_sha256,
    )?;
    Ok(ElapsedProfile {
        sha256: sha256_bytes(source.as_bytes()),
        baseline_sha256,
        baseline_summaries: Some(baseline_summaries),
    })
}

fn validate_elapsed_baseline_identity(
    source: &str,
    identity_expectation: BaselineIdentityExpectation<'_>,
    deterministic_baseline_sha256: &str,
) -> Result<BTreeMap<(String, String), BaselineSummary>, String> {
    let document = JsonDocument::parse(source).map_err(|error| {
        format!(
            "invalid elapsed baseline JSON at {}: {:?}",
            error.offset, error.kind
        )
    })?;
    let root = exact_object(
        document.root(),
        &[
            "schema",
            "phase",
            "fixture_manifest_sha256",
            "deterministic_baseline_sha256",
            "identity",
            "elapsed_profile_sha256",
            "elapsed_baseline_sha256",
            "warmup_per_child",
            "samples_per_series",
            "collection_order",
            "rows",
            "summaries",
        ],
        "elapsed_baseline",
    )?;
    expect_string(
        root[0].value(),
        ELAPSED_BASELINE_SCHEMA,
        "elapsed_baseline.schema",
    )?;
    expect_string(root[1].value(), "recursive", "elapsed_baseline.phase")?;
    let expected_fixture_manifest_sha256 = match identity_expectation {
        BaselineIdentityExpectation::Candidate(candidate) => &candidate.fixture_manifest_sha256,
        BaselineIdentityExpectation::ArchivedArtifact(artifact) => {
            &artifact.fixture_manifest_sha256
        }
    };
    expect_string(
        root[2].value(),
        expected_fixture_manifest_sha256,
        "elapsed_baseline.fixture_manifest_sha256",
    )?;
    expect_string(
        root[3].value(),
        deterministic_baseline_sha256,
        "elapsed_baseline.deterministic_baseline_sha256",
    )?;
    expect_kind(
        root[5].value(),
        JsonValueKind::Null,
        "elapsed_baseline.elapsed_profile_sha256",
    )?;
    expect_kind(
        root[6].value(),
        JsonValueKind::Null,
        "elapsed_baseline.elapsed_baseline_sha256",
    )?;
    expect_unsigned_eq(root[7].value(), 1, "elapsed_baseline.warmup_per_child")?;
    expect_unsigned_eq(root[8].value(), 9, "elapsed_baseline.samples_per_series")?;
    expect_string(
        root[9].value(),
        "sample-major",
        "elapsed_baseline.collection_order",
    )?;
    let rows = expect_array(root[10].value(), "elapsed_baseline.rows")?;
    if rows.len() != 666 {
        return Err("elapsed_baseline.rows must contain 666 samples".to_owned());
    }
    let summaries = expect_array(root[11].value(), "elapsed_baseline.summaries")?;
    if summaries.len() != 74 {
        return Err("elapsed_baseline.summaries must contain 74 series".to_owned());
    }

    let observed_identity =
        parse_archived_run_identity(root[4].value(), "elapsed_baseline.identity")?;
    validate_archived_identity_expectation(&observed_identity, identity_expectation)?;
    let expected = expected_series("recursive")?;
    let mut observed_samples = BTreeMap::<(String, String), (Vec<u64>, Vec<u64>, Vec<u64>)>::new();
    for sample_index in 0..9_u64 {
        for (series_index, (scenario_id, series_kind, mode)) in expected.iter().enumerate() {
            let index = usize::try_from(sample_index)
                .map_err(|_| "sample index does not fit usize")?
                .checked_mul(expected.len())
                .and_then(|base| base.checked_add(series_index))
                .ok_or("elapsed baseline row index overflow")?;
            let path = format!("elapsed_baseline.rows[{index}]");
            let fields = exact_object(
                &rows[index],
                &[
                    "scenario_id",
                    "series_kind",
                    "mode",
                    "sample_index",
                    "operation_elapsed_ns",
                    "process_elapsed_ns",
                    "peak_rss_kib",
                    "child_output_sha256",
                ],
                &path,
            )?;
            expect_string(
                fields[0].value(),
                scenario_id,
                &format!("{path}.scenario_id"),
            )?;
            expect_string(
                fields[1].value(),
                series_kind,
                &format!("{path}.series_kind"),
            )?;
            expect_string(fields[2].value(), mode, &format!("{path}.mode"))?;
            expect_unsigned_eq(
                fields[3].value(),
                sample_index,
                &format!("{path}.sample_index"),
            )?;
            let operation_elapsed_ns =
                expect_unsigned(fields[4].value(), &format!("{path}.operation_elapsed_ns"))?;
            let process_elapsed_ns =
                expect_unsigned(fields[5].value(), &format!("{path}.process_elapsed_ns"))?;
            let peak_rss_kib = expect_unsigned(fields[6].value(), &format!("{path}.peak_rss_kib"))?;
            expect_hash(fields[7].value(), &format!("{path}.child_output_sha256"))?;
            let samples = observed_samples
                .entry((scenario_id.clone(), mode.clone()))
                .or_default();
            samples.0.push(operation_elapsed_ns);
            samples.1.push(process_elapsed_ns);
            samples.2.push(peak_rss_kib);
        }
    }

    let mut parsed = BTreeMap::new();
    for (index, ((scenario_id, series_kind, mode), summary)) in
        expected.iter().zip(summaries).enumerate()
    {
        let path = format!("elapsed_baseline.summaries[{index}]");
        let fields = exact_object(
            summary,
            &[
                "scenario_id",
                "series_kind",
                "mode",
                "samples_ns",
                "process_samples_ns",
                "peak_rss_samples_kib",
                "median_ns",
                "median_absolute_deviation_ns",
                "min_ns",
                "max_ns",
                "peak_rss_kib",
            ],
            &path,
        )?;
        expect_string(
            fields[0].value(),
            scenario_id,
            &format!("{path}.scenario_id"),
        )?;
        expect_string(
            fields[1].value(),
            series_kind,
            &format!("{path}.series_kind"),
        )?;
        expect_string(fields[2].value(), mode, &format!("{path}.mode"))?;
        let samples = validate_u64_array(fields[3].value(), &format!("{path}.samples_ns"), 9)?;
        let process_samples =
            validate_u64_array(fields[4].value(), &format!("{path}.process_samples_ns"), 9)?;
        let rss = validate_u64_array(
            fields[5].value(),
            &format!("{path}.peak_rss_samples_kib"),
            9,
        )?;
        let observed = observed_samples
            .remove(&(scenario_id.clone(), mode.clone()))
            .ok_or_else(|| format!("{path} has no matching raw rows"))?;
        if (
            samples.as_slice(),
            process_samples.as_slice(),
            rss.as_slice(),
        ) != (
            observed.0.as_slice(),
            observed.1.as_slice(),
            observed.2.as_slice(),
        ) {
            return Err(format!("{path} sample arrays do not match raw rows"));
        }
        let median_ns = median(&samples)?;
        let deviations = samples
            .iter()
            .map(|sample| sample.abs_diff(median_ns))
            .collect::<Vec<_>>();
        let median_absolute_deviation_ns = median(&deviations)?;
        let min_ns = *samples.iter().min().ok_or("empty baseline sample series")?;
        let max_ns = *samples.iter().max().ok_or("empty baseline sample series")?;
        let peak_rss_kib = *rss.iter().max().ok_or("empty baseline RSS series")?;
        for (field, expected_value) in [
            (&fields[6], median_ns),
            (&fields[7], median_absolute_deviation_ns),
            (&fields[8], min_ns),
            (&fields[9], max_ns),
            (&fields[10], peak_rss_kib),
        ] {
            expect_unsigned_eq(
                field.value(),
                expected_value,
                &format!("{path}.{}", field.key()),
            )?;
        }
        let key = (scenario_id.clone(), mode.clone());
        if parsed
            .insert(
                key,
                BaselineSummary {
                    median_ns,
                    median_absolute_deviation_ns,
                    peak_rss_kib,
                },
            )
            .is_some()
        {
            return Err(format!("duplicate elapsed baseline summary {scenario_id}"));
        }
    }
    if !observed_samples.is_empty() {
        return Err("elapsed baseline contains raw rows without summaries".to_owned());
    }
    Ok(parsed)
}

fn validate_lower_hex_hash(value: &str, label: &str) -> Result<(), String> {
    if value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        Ok(())
    } else {
        Err(format!(
            "{label} is not a 64-character lowercase hexadecimal hash"
        ))
    }
}

fn validate_elapsed_gates(
    profile: &ElapsedProfile,
    candidate: &[SeriesSummary],
) -> Result<(), String> {
    let Some(baseline_summaries) = profile.baseline_summaries.as_ref() else {
        return Ok(());
    };
    for summary in candidate {
        if !checked_ratio_le(
            summary.median_absolute_deviation_ns,
            summary.median_ns,
            1,
            10,
        )? {
            return Err(format!(
                "candidate series {} is unstable",
                summary.scenario_id
            ));
        }
        if let Some(baseline) =
            baseline_summaries.get(&(summary.scenario_id.clone(), summary.mode.clone()))
        {
            if !checked_ratio_le(
                baseline.median_absolute_deviation_ns,
                baseline.median_ns,
                1,
                10,
            )? {
                return Err(format!(
                    "baseline series {} is unstable",
                    summary.scenario_id
                ));
            }
            let (numerator, denominator) = if summary.series_kind == "package" {
                (21, 20)
            } else if matches!(
                summary.scenario_id.as_str(),
                "opaque-neutral-head.w2048.memo-off" | "partial-recursor.w2048.memo-off"
            ) {
                (3, 4)
            } else if summary.scenario_id.contains(".w32.") {
                (11, 10)
            } else {
                (23, 20)
            };
            if !checked_ratio_le(
                summary.median_ns,
                baseline.median_ns,
                numerator,
                denominator,
            )? {
                return Err(format!(
                    "elapsed median gate failed for {}",
                    summary.scenario_id
                ));
            }
            let allowance = if summary.series_kind == "package" {
                8_192
            } else {
                16_384
            };
            let ten_percent = baseline.peak_rss_kib / 10;
            let permitted = baseline
                .peak_rss_kib
                .checked_add(ten_percent.max(allowance))
                .ok_or("peak RSS allowance overflow")?;
            if summary.peak_rss_kib > permitted {
                return Err(format!("peak RSS gate failed for {}", summary.scenario_id));
            }
        }
    }
    validate_scaling_gates(candidate)
}

fn validate_scaling_gates(candidate: &[SeriesSummary]) -> Result<(), String> {
    for kind in ["opaque-neutral-head", "partial-recursor"] {
        let width = |value: usize| {
            candidate
                .iter()
                .find(|summary| summary.scenario_id == format!("{kind}.w{value}.memo-off"))
        };
        if let (Some(width_512), Some(width_2_048)) = (width(512), width(2_048)) {
            if !checked_ratio_le(width_2_048.median_ns, width_512.median_ns, 6, 1)? {
                return Err(format!("scaling gate 512->2048 failed for {kind}"));
            }
        }
        if let (Some(width_2_048), Some(width_8_192)) = (width(2_048), width(8_192)) {
            if !checked_ratio_le(width_8_192.median_ns, width_2_048.median_ns, 6, 1)? {
                return Err(format!("scaling gate 2048->8192 failed for {kind}"));
            }
        }
    }
    Ok(())
}

fn checked_ratio_le(
    actual: u64,
    reference: u64,
    numerator: u64,
    denominator: u64,
) -> Result<bool, String> {
    if denominator == 0 {
        return Err("ratio denominator is zero".to_owned());
    }
    let left = u128::from(actual)
        .checked_mul(u128::from(denominator))
        .ok_or("ratio left product overflow")?;
    let right = u128::from(reference)
        .checked_mul(u128::from(numerator))
        .ok_or("ratio right product overflow")?;
    Ok(left <= right)
}

struct ControllerTempDir(Option<ClosedPrivateDirectory>);

impl ControllerTempDir {
    fn path(&self) -> Result<&Path, String> {
        self.0
            .as_ref()
            .map(ClosedPrivateDirectory::path)
            .ok_or_else(|| "controller temporary directory was already cleaned".to_owned())
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
        output
            .write_all(bytes)
            .map_err(|error| format!("write {}: {error}", relative.display()))?;
        output
            .sync_all()
            .map_err(|error| format!("sync {}: {error}", relative.display()))?;
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
            if let Ok(catalog) = whnf_controller_temp_catalog("candidate") {
                let _ = directory.remove_allowed_root(&catalog);
            }
        }
    }
}

fn make_controller_temp_dir() -> Result<ControllerTempDir, String> {
    ClosedPrivateDirectory::new("npa-whnf-application-spine-controller")
        .map(|directory| ControllerTempDir(Some(directory)))
}

fn whnf_controller_temp_catalog(phase: &str) -> Result<BTreeSet<PathBuf>, String> {
    let rows = expected_series(phase)?
        .len()
        .checked_mul(9)
        .ok_or("WHNF temporary-file catalog size overflow")?;
    let mut files = BTreeSet::new();
    for fixed in [
        "micro-child",
        "package-child",
        "measure-process",
        "fixture-manifest.json",
        "deterministic-baseline.json",
    ] {
        files.insert(PathBuf::from(fixed));
    }
    for index in 0..rows {
        files.insert(PathBuf::from(format!("{index:04}.json")));
        files.insert(PathBuf::from(format!("{index:04}.stderr")));
    }
    Ok(files)
}

fn write_new_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let _ = validate_absolute_output_path(path)?;
    let mut file = create_new_absolute_file(path, "KWHNF output")?;
    file.write_all(bytes)
        .map_err(|error| format!("write output {}: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("sync output {}: {error}", path.display()))
}

fn validate_absolute_output_path(path: &Path) -> Result<(&Path, &str), String> {
    if !path.is_absolute() {
        return Err("output path must be absolute".to_owned());
    }
    let parent = path.parent().ok_or("output path has no parent")?;
    let canonical_parent = parent
        .canonicalize()
        .map_err(|error| format!("canonicalize output parent: {error}"))?;
    if canonical_parent != parent {
        return Err(
            "output parent must already be canonical and contain no symlink or ..".to_owned(),
        );
    }
    let basename = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("output basename must be UTF-8")?;
    if basename.is_empty()
        || !basename
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
        || !basename.as_bytes()[0].is_ascii_alphanumeric()
    {
        return Err("output basename is outside the closed grammar".to_owned());
    }
    Ok((parent, basename))
}

fn compact_json(source: &str) -> Result<String, String> {
    let mut output = String::with_capacity(source.len());
    let mut in_string = false;
    let mut escaped = false;
    for byte in source.bytes() {
        if in_string {
            output.push(char::from(byte));
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
        } else if byte == b'"' {
            in_string = true;
            output.push('"');
        } else if !byte.is_ascii_whitespace() {
            output.push(char::from(byte));
        }
    }
    if in_string || escaped {
        Err("unterminated JSON string".to_owned())
    } else {
        Ok(output)
    }
}

fn hex_hash(hash: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for byte in hash {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn fuel_domain_json(domain: npa_kernel::KernelFuelDomainTotals) -> String {
    format!(
        "{{\"calls\":{},\"logical_spent\":{},\"successful_operation_fuel\":{},\"exhausted_operation_fuel\":{},\"overflowed\":{}}}",
        domain.calls,
        domain.logical_spent,
        domain.successful_operation_fuel,
        domain.exhausted_operation_fuel,
        domain.overflowed,
    )
}

fn work_json(work: &KernelWorkCounters) -> String {
    let fuel = format!(
        "{{\"whnf\":{},\"conversion\":{}}}",
        fuel_domain_json(work.fuel.whnf),
        fuel_domain_json(work.fuel.conversion),
    );
    format!(
        concat!(
            "{{\"check_calls\":{},\"infer_calls\":{},\"whnf_calls\":{},",
            "\"defeq_calls\":{},\"quick_equality_hits\":{},\"beta_steps\":{},",
            "\"delta_steps\":{},\"iota_steps\":{},\"fuel\":{},",
            "\"logical_fuel\":{},\"successful_fuel\":{},\"exhausted_fuel\":{},",
            "\"physical_reductions\":{},\"context_lookups\":{},\"context_shifts\":{},",
            "\"memo_eligible_calls\":{},\"memo_ineligible_borrowed\":{},",
            "\"memo_ineligible_fresh\":{},\"memo_ineligible_diagnosed\":{},",
            "\"memo_identity_capacity_stops\":{},\"whnf_memo_lookups\":{},",
            "\"whnf_memo_hits\":{},\"whnf_memo_misses\":{},\"whnf_memo_inserts\":{},",
            "\"whnf_memo_capacity_stops\":{},\"defeq_memo_lookups\":{},",
            "\"defeq_memo_hits\":{},\"defeq_memo_misses\":{},\"defeq_memo_inserts\":{},",
            "\"defeq_memo_capacity_stops\":{},\"memo_expr_identities\":{},",
            "\"memo_local_identities\":{},\"memo_context_identities\":{},",
            "\"memo_parameter_profiles\":{},\"memo_entry_capacity\":{},",
            "\"whnf_memo_entries\":{},\"defeq_memo_entries\":{},",
            "\"memo_retained_node_occurrences\":{},\"memo_retained_context_occurrences\":{},",
            "\"memo_retained_parameter_occurrences\":{},\"memo_retained_bytes\":{},",
            "\"memo_logical_fuel_replayed\":{},\"memo_bypassed_call_bodies\":{},",
            "\"memo_accounting_overflows\":{},\"memo_probe_lookups\":{},",
            "\"memo_probe_repetitions\":{},\"memo_probe_inserts\":{},",
            "\"memo_probe_capacity_stops\":{},\"memo_probe_truncated\":{},",
            "\"overflowed\":{}}}"
        ),
        work.check_calls,
        work.infer_calls,
        work.whnf_calls,
        work.defeq_calls,
        work.quick_equality_hits,
        work.beta_steps,
        work.delta_steps,
        work.iota_steps,
        fuel,
        work.logical_fuel,
        work.successful_fuel,
        work.exhausted_fuel,
        work.physical_reductions,
        work.context_lookups,
        work.context_shifts,
        work.memo_eligible_calls,
        work.memo_ineligible_borrowed,
        work.memo_ineligible_fresh,
        work.memo_ineligible_diagnosed,
        work.memo_identity_capacity_stops,
        work.whnf_memo_lookups,
        work.whnf_memo_hits,
        work.whnf_memo_misses,
        work.whnf_memo_inserts,
        work.whnf_memo_capacity_stops,
        work.defeq_memo_lookups,
        work.defeq_memo_hits,
        work.defeq_memo_misses,
        work.defeq_memo_inserts,
        work.defeq_memo_capacity_stops,
        work.memo_expr_identities,
        work.memo_local_identities,
        work.memo_context_identities,
        work.memo_parameter_profiles,
        work.memo_entry_capacity,
        work.whnf_memo_entries,
        work.defeq_memo_entries,
        work.memo_retained_node_occurrences,
        work.memo_retained_context_occurrences,
        work.memo_retained_parameter_occurrences,
        work.memo_retained_bytes,
        work.memo_logical_fuel_replayed,
        work.memo_bypassed_call_bodies,
        work.memo_accounting_overflows,
        work.memo_probe_lookups,
        work.memo_probe_repetitions,
        work.memo_probe_inserts,
        work.memo_probe_capacity_stops,
        work.memo_probe_truncated,
        work.overflowed,
    )
}

struct Args {
    fixture_manifest: PathBuf,
    baseline: PathBuf,
    scenario: Option<String>,
    list: bool,
    child: bool,
    controller: bool,
    phase: String,
    sample_index: u64,
    measure_process: Option<PathBuf>,
    package_harness: Option<PathBuf>,
    output: Option<PathBuf>,
    elapsed_profile: Option<PathBuf>,
    review_reason: Option<String>,
    seal_recursive_baseline: Option<PathBuf>,
    archived_artifact: Option<PathBuf>,
    validate_report: Option<PathBuf>,
    validate_archived_artifact: Option<PathBuf>,
    validate_bootstrap_profile: Option<PathBuf>,
    collect_archived_recursive_baseline: bool,
}

impl Args {
    fn parse_from(arguments: Vec<String>) -> Result<Self, String> {
        let mut fixture_manifest = None;
        let mut baseline = None;
        let mut scenario = None;
        let mut list = false;
        let mut child = false;
        let mut controller = false;
        let mut phase = "candidate".to_owned();
        let mut sample_index = 0;
        let mut measure_process = None;
        let mut package_harness = None;
        let mut output = None;
        let mut elapsed_profile = None;
        let mut review_reason = None;
        let mut seal_recursive_baseline = None;
        let mut archived_artifact = None;
        let mut validate_report = None;
        let mut validate_archived_artifact = None;
        let mut validate_bootstrap_profile = None;
        let mut collect_archived_recursive_baseline = false;
        let mut args = arguments.into_iter();
        while let Some(argument) = args.next() {
            match argument.as_str() {
                "--fixture-manifest" => {
                    fixture_manifest = Some(PathBuf::from(
                        args.next().ok_or("--fixture-manifest needs a value")?,
                    ))
                }
                "--baseline" => {
                    baseline = Some(PathBuf::from(
                        args.next().ok_or("--baseline needs a value")?,
                    ))
                }
                "--scenario-id" => {
                    scenario = Some(args.next().ok_or("--scenario-id needs a value")?)
                }
                "--list" => list = true,
                "--child" => child = true,
                "--controller" => controller = true,
                "--phase" => phase = args.next().ok_or("--phase needs a value")?,
                "--sample-index" => {
                    sample_index = args
                        .next()
                        .ok_or("--sample-index needs a value")?
                        .parse()
                        .map_err(|_| "sample index must be unsigned")?
                }
                "--measure-process" => {
                    measure_process = Some(PathBuf::from(
                        args.next().ok_or("--measure-process needs a value")?,
                    ))
                }
                "--package-harness" => {
                    package_harness = Some(PathBuf::from(
                        args.next().ok_or("--package-harness needs a value")?,
                    ))
                }
                "--output" => {
                    output = Some(PathBuf::from(args.next().ok_or("--output needs a value")?))
                }
                "--elapsed-profile" => {
                    elapsed_profile = Some(PathBuf::from(
                        args.next().ok_or("--elapsed-profile needs a value")?,
                    ))
                }
                "--review-reason" => {
                    review_reason = Some(args.next().ok_or("--review-reason needs a value")?)
                }
                "--seal-recursive-baseline" => {
                    seal_recursive_baseline = Some(PathBuf::from(
                        args.next()
                            .ok_or("--seal-recursive-baseline needs a value")?,
                    ))
                }
                "--archived-artifact" => {
                    archived_artifact = Some(PathBuf::from(
                        args.next().ok_or("--archived-artifact needs a value")?,
                    ))
                }
                "--validate-report" => {
                    validate_report = Some(PathBuf::from(
                        args.next().ok_or("--validate-report needs a value")?,
                    ))
                }
                "--validate-archived-artifact" => {
                    validate_archived_artifact = Some(PathBuf::from(
                        args.next()
                            .ok_or("--validate-archived-artifact needs a value")?,
                    ))
                }
                "--validate-bootstrap-profile" => {
                    validate_bootstrap_profile = Some(PathBuf::from(
                        args.next()
                            .ok_or("--validate-bootstrap-profile needs a value")?,
                    ))
                }
                "--collect-archived-recursive-baseline" => {
                    collect_archived_recursive_baseline = true
                }
                other => return Err(format!("unknown argument {other}")),
            }
        }
        if !matches!(phase.as_str(), "recursive" | "candidate") {
            return Err("--phase must be recursive or candidate".to_owned());
        }
        if sample_index >= 9 {
            return Err("sample index must be in 0..8".to_owned());
        }
        let seal = seal_recursive_baseline.is_some();
        let validate_archive = validate_archived_artifact.is_some();
        let validate_profile = validate_bootstrap_profile.is_some();
        let validate_run = validate_report.is_some();
        let collect_archived = collect_archived_recursive_baseline;
        if u8::from(list)
            + u8::from(child)
            + u8::from(controller)
            + u8::from(seal)
            + u8::from(validate_archive)
            + u8::from(validate_profile)
            + u8::from(validate_run)
            + u8::from(collect_archived)
            > 1
        {
            return Err("--list, --child, --controller, report/artifact/profile validation, seal mode, and archived collection are mutually exclusive".to_owned());
        }
        if collect_archived {
            if phase != "candidate" || scenario.is_some() {
                return Err("archived collection rejects --phase/--scenario-id".to_owned());
            }
            if archived_artifact.is_none() || output.is_none() {
                return Err(
                    "archived collection requires --archived-artifact and --output".to_owned(),
                );
            }
            if !review_reason
                .as_deref()
                .is_some_and(|reason| !reason.trim().is_empty())
            {
                return Err("archived collection requires nonempty --review-reason".to_owned());
            }
            if measure_process.is_some()
                || package_harness.is_some()
                || elapsed_profile.is_some()
                || seal_recursive_baseline.is_some()
            {
                return Err("archived collection rejects candidate controller options".to_owned());
            }
        } else if validate_run {
            if phase != "candidate" || scenario.is_some() {
                return Err(
                    "report validation requires candidate phase and rejects --scenario-id"
                        .to_owned(),
                );
            }
            if measure_process.is_none() || package_harness.is_none() {
                return Err("report validation requires measure/package inputs".to_owned());
            }
            if output.is_some()
                || review_reason.is_some()
                || seal_recursive_baseline.is_some()
                || archived_artifact.is_some()
            {
                return Err("report validation rejects execution/output/archive options".to_owned());
            }
        } else if validate_profile {
            if phase != "candidate" || scenario.is_some() {
                return Err("profile validation rejects --phase/--scenario-id".to_owned());
            }
            if archived_artifact.is_none() || measure_process.is_none() || package_harness.is_none()
            {
                return Err(
                    "profile validation requires archived/measure/package inputs".to_owned(),
                );
            }
            if output.is_some()
                || elapsed_profile.is_some()
                || review_reason.is_some()
                || seal_recursive_baseline.is_some()
            {
                return Err("profile validation rejects execution/output options".to_owned());
            }
        } else if validate_archive {
            if phase != "candidate" || scenario.is_some() {
                return Err("artifact validation rejects --phase/--scenario-id".to_owned());
            }
            if measure_process.is_some()
                || package_harness.is_some()
                || output.is_some()
                || elapsed_profile.is_some()
                || review_reason.is_some()
                || archived_artifact.is_some()
            {
                return Err("artifact validation rejects execution/output options".to_owned());
            }
        } else if seal {
            if phase != "candidate" || scenario.is_some() {
                return Err("seal mode rejects --phase/--scenario-id".to_owned());
            }
            if archived_artifact.is_none() || output.is_none() {
                return Err("seal mode requires --archived-artifact and --output".to_owned());
            }
            if measure_process.is_some()
                || package_harness.is_some()
                || elapsed_profile.is_some()
                || review_reason.is_some()
            {
                return Err("seal mode rejects controller execution options".to_owned());
            }
        } else if controller {
            if scenario.is_some() {
                return Err("controller mode rejects --scenario-id".to_owned());
            }
            if measure_process.is_none() || package_harness.is_none() || output.is_none() {
                return Err("controller mode requires all three prebuilt/output paths".to_owned());
            }
            if phase == "candidate" && review_reason.is_some() {
                return Err("candidate controller rejects --review-reason".to_owned());
            }
        } else {
            if measure_process.is_some()
                || package_harness.is_some()
                || output.is_some()
                || elapsed_profile.is_some()
                || review_reason.is_some()
                || archived_artifact.is_some()
            {
                return Err("controller-only options require --controller".to_owned());
            }
        }
        if child && scenario.is_none() {
            return Err("child mode requires --scenario-id".to_owned());
        }
        if phase == "recursive" && !controller {
            if let Some(scenario) = scenario.as_deref() {
                let (_, width, _) = parse_scenario(scenario)
                    .ok_or_else(|| format!("unknown scenario {scenario}"))?;
                if width == 8_192 {
                    return Err("recursive phase excludes machine-only width".to_owned());
                }
            }
        }
        Ok(Self {
            fixture_manifest: fixture_manifest.ok_or("--fixture-manifest is required")?,
            baseline: baseline.ok_or("--baseline is required")?,
            scenario,
            list,
            child,
            controller,
            phase,
            sample_index,
            measure_process,
            package_harness,
            output,
            elapsed_profile,
            review_reason,
            seal_recursive_baseline,
            archived_artifact,
            validate_report,
            validate_archived_artifact,
            validate_bootstrap_profile,
            collect_archived_recursive_baseline,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_common_spine_fixture() {
        for width in WIDTHS {
            let term = neutral_spine(width);
            let mut count = 0;
            let mut current = &term;
            while let Expr::App(function, _) = current {
                count += 1;
                current = function;
            }
            assert_eq!(count, width);
        }
    }

    #[test]
    fn exact_variable_width_recursor_fixture() {
        for (kind, width) in [
            ("partial-recursor", 32),
            ("saturated-neutral-major", 32),
            ("matching-constructor", 32),
        ] {
            let fixture = build_fixture(kind, width, "memo-off").unwrap();
            let Operation::Whnf(term) = &fixture.operation else {
                panic!("recursor fixture is a WHNF operation");
            };
            let mut app_count = 0;
            let mut current = term;
            while let Expr::App(function, _) = current {
                app_count += 1;
                current = function;
            }
            assert_eq!(app_count, width);
            let mut counters = KernelWorkCounters::default();
            assert!(matches!(
                run_operation(&fixture, &mut counters),
                Ok(OperationResult::Whnf(_))
            ));
        }
    }

    #[test]
    fn exact_retained_function_fixture() {
        let fixture = build_fixture("retained-function-ephemeral-defeq", 32, "ephemeral").unwrap();
        let retained = fixture
            .retained_function
            .as_ref()
            .expect("fixture retains the complete-spine owner");
        let Operation::Defeq(
            Expr::App(left_function, left_argument),
            Expr::App(right_function, right_argument),
        ) = &fixture.operation
        else {
            panic!("retained fixture has the exact two application roots");
        };
        assert!(Arc::ptr_eq(left_function, retained));
        assert!(Arc::ptr_eq(right_function, retained));
        assert_eq!(Arc::strong_count(retained), 3);
        assert!(!Arc::ptr_eq(left_argument, right_argument));
        assert_ne!(
            left_argument, right_argument,
            "right outer argument starts as the distinct beta redex"
        );
        let mut counters = KernelWorkCounters::default();
        assert!(matches!(
            run_operation(&fixture, &mut counters),
            Ok(OperationResult::Defeq(true))
        ));
    }

    #[test]
    fn whnf_micro_child_protocol() {
        assert_eq!(MODES, ["memo-off", "repetition-probe", "ephemeral"]);
        assert_eq!(expected_scenarios().len(), 90);
        assert_eq!(PACKAGE_IDS.len(), 3);
        assert!(parse_scenario("opaque-neutral-head.w8192.memo-off").is_some());
        assert!(parse_scenario("opaque-neutral-head.w8193.memo-off").is_none());
    }

    #[test]
    fn whnf_controlled_failure_protocol() {
        assert_eq!(one_line_error("first\nsecond\rthird"), "first second third");
        assert!(Args::parse_from(vec!["--unknown".to_owned()]).is_err());
        assert!(Args::parse_from(vec!["--phase".to_owned()]).is_err());
        assert!(Args::parse_from(vec![
            "--fixture-manifest".to_owned(),
            "fixture.json".to_owned(),
            "--baseline".to_owned(),
            "baseline.json".to_owned(),
            "--sample-index".to_owned(),
            "9".to_owned(),
            "--list".to_owned(),
        ])
        .is_err());
        let validation_args = |report: &str| {
            Args::parse_from(vec![
                "--fixture-manifest".to_owned(),
                "fixture.json".to_owned(),
                "--baseline".to_owned(),
                "baseline.json".to_owned(),
                "--validate-report".to_owned(),
                report.to_owned(),
                "--phase".to_owned(),
                "candidate".to_owned(),
                "--measure-process".to_owned(),
                "measure".to_owned(),
                "--package-harness".to_owned(),
                "package".to_owned(),
            ])
        };
        assert!(validation_args("/tmp/report.json").is_ok());
        assert!(validation_args("relative.json")
            .and_then(|args| validate_candidate_run_report(&args))
            .is_err());
        let mut conflicting = vec![
            "--fixture-manifest".to_owned(),
            "fixture.json".to_owned(),
            "--baseline".to_owned(),
            "baseline.json".to_owned(),
            "--validate-report".to_owned(),
            "/tmp/report.json".to_owned(),
            "--measure-process".to_owned(),
            "measure".to_owned(),
            "--package-harness".to_owned(),
            "package".to_owned(),
            "--controller".to_owned(),
        ];
        assert!(Args::parse_from(std::mem::take(&mut conflicting)).is_err());

        let archived_collection = Args::parse_from(vec![
            "--fixture-manifest".to_owned(),
            "fixture.json".to_owned(),
            "--baseline".to_owned(),
            "baseline.json".to_owned(),
            "--collect-archived-recursive-baseline".to_owned(),
            "--archived-artifact".to_owned(),
            "artifact.json".to_owned(),
            "--review-reason".to_owned(),
            "reviewed recursive baseline".to_owned(),
            "--output".to_owned(),
            "output.json".to_owned(),
        ])
        .unwrap();
        assert!(archived_collection.collect_archived_recursive_baseline);
        assert_eq!(
            archived_collection.archived_artifact.as_deref(),
            Some(Path::new("artifact.json"))
        );
        assert_eq!(
            archived_collection.review_reason.as_deref(),
            Some("reviewed recursive baseline")
        );
        assert!(Args::parse_from(vec![
            "--fixture-manifest".to_owned(),
            "fixture.json".to_owned(),
            "--baseline".to_owned(),
            "baseline.json".to_owned(),
            "--collect-archived-recursive-baseline".to_owned(),
            "--archived-artifact".to_owned(),
            "artifact.json".to_owned(),
            "--review-reason".to_owned(),
            " ".to_owned(),
            "--output".to_owned(),
            "output.json".to_owned(),
        ])
        .is_err());
        assert!(Args::parse_from(vec![
            "--fixture-manifest".to_owned(),
            "fixture.json".to_owned(),
            "--baseline".to_owned(),
            "baseline.json".to_owned(),
            "--collect-archived-recursive-baseline".to_owned(),
            "--archived-artifact".to_owned(),
            "artifact.json".to_owned(),
            "--review-reason".to_owned(),
            "reviewed".to_owned(),
            "--output".to_owned(),
            "output.json".to_owned(),
            "--controller".to_owned(),
        ])
        .is_err());

        let temporary = make_controller_temp_dir().unwrap();
        let manifest_path = temporary.path().unwrap().join("fixture.json");
        let baseline_path = temporary.path().unwrap().join("baseline.json");
        let missing_path = temporary.path().unwrap().join("missing.json");
        let valid_manifest = include_str!(
            "../../../testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
        );
        let valid_baseline = include_str!(
            "../../../testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
        );
        std::fs::write(&baseline_path, valid_baseline).unwrap();
        let arguments = |manifest: &Path, baseline: &Path, tail: &[&str]| {
            let mut arguments = vec![
                "--fixture-manifest".to_owned(),
                manifest.display().to_string(),
                "--baseline".to_owned(),
                baseline.display().to_string(),
            ];
            arguments.extend(tail.iter().map(|argument| (*argument).to_owned()));
            arguments
        };
        assert!(run_from_args(arguments(&missing_path, &baseline_path, &["--list"])).is_err());
        std::fs::write(&manifest_path, "{}\n").unwrap();
        assert!(run_from_args(arguments(&manifest_path, &baseline_path, &["--list"])).is_err());
        std::fs::write(&manifest_path, valid_manifest).unwrap();
        std::fs::write(&baseline_path, "{}\n").unwrap();
        assert!(run_from_args(arguments(&manifest_path, &baseline_path, &["--list"])).is_err());
        std::fs::write(&baseline_path, valid_baseline).unwrap();
        assert!(run_from_args(arguments(
            &manifest_path,
            &baseline_path,
            &["--child", "--scenario-id", "unknown-scenario"],
        ))
        .is_err());

        #[cfg(unix)]
        {
            let linked_manifest = temporary.path().unwrap().join("linked-fixture.json");
            std::os::unix::fs::symlink(&manifest_path, &linked_manifest).unwrap();
            assert!(
                run_from_args(arguments(&linked_manifest, &baseline_path, &["--list"],)).is_err()
            );
            std::fs::remove_file(linked_manifest).unwrap();
        }
        let oversized = temporary.path().unwrap().join("oversized.json");
        let oversized_file = std::fs::File::create(&oversized).unwrap();
        oversized_file.set_len(16 * 1024 * 1024 + 1).unwrap();
        assert!(read_json_input(&oversized, "oversized JSON").is_err());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let failed_wrapper = temporary.path().unwrap().join("failed-wrapper.sh");
            std::fs::write(
                &failed_wrapper,
                "#!/bin/sh\n[ \"$1\" = --output ] || exit 90\n: >\"$2\"\nshift 2\n[ \"$1\" = --stderr ] || exit 91\n: >\"$2\"\nprintf '0.000000001\\t1\\t1\\n'\n",
            )
            .unwrap();
            std::fs::set_permissions(&failed_wrapper, std::fs::Permissions::from_mode(0o700))
                .unwrap();
            let wrapper_snapshot = temporary
                .create_executable_snapshot(
                    Path::new("failed-wrapper-snapshot"),
                    &failed_wrapper,
                    1024 * 1024,
                    "failed wrapper",
                )
                .unwrap();
            let child_snapshot = temporary
                .create_executable_snapshot(
                    Path::new("false-child-snapshot"),
                    Path::new("/usr/bin/false"),
                    16 * 1024 * 1024,
                    "false child",
                )
                .unwrap();
            let fixture_snapshot = temporary
                .create_input_snapshot(
                    Path::new("fixture-snapshot.json"),
                    valid_manifest.as_bytes(),
                )
                .unwrap();
            let baseline_snapshot = temporary
                .create_input_snapshot(
                    Path::new("baseline-snapshot.json"),
                    valid_baseline.as_bytes(),
                )
                .unwrap();
            assert!(run_measured_child(
                &wrapper_snapshot,
                &child_snapshot,
                &fixture_snapshot,
                valid_manifest.as_bytes(),
                &baseline_snapshot,
                valid_baseline.as_bytes(),
                &[],
                MICRO_CHILD_SCHEMA,
                "candidate",
                "opaque-neutral-head.w32.memo-off",
                "micro",
                "memo-off",
                0,
                &temporary,
                0,
            )
            .is_err());
            drop(wrapper_snapshot);
            drop(child_snapshot);
            drop(fixture_snapshot);
            drop(baseline_snapshot);
        }
        let files = BTreeSet::from([
            PathBuf::from("0000.json"),
            PathBuf::from("0000.stderr"),
            PathBuf::from("baseline.json"),
            PathBuf::from("failed-wrapper.sh"),
            PathBuf::from("failed-wrapper-snapshot"),
            PathBuf::from("false-child-snapshot"),
            PathBuf::from("fixture.json"),
            PathBuf::from("fixture-snapshot.json"),
            PathBuf::from("baseline-snapshot.json"),
            PathBuf::from("oversized.json"),
        ]);
        temporary.cleanup_exact(files).unwrap();

        let output_root = make_controller_temp_dir().unwrap();
        let canonical_output = output_root.path().unwrap().join("report.json");
        write_new_file(&canonical_output, b"{}\n").unwrap();
        assert_eq!(std::fs::read(&canonical_output).unwrap(), b"{}\n");
        assert!(write_new_file(&canonical_output, b"second").is_err());
        assert!(write_new_file(Path::new("relative.json"), b"{}").is_err());
        assert!(write_new_file(&output_root.path().unwrap().join(".hidden"), b"{}").is_err());
        #[cfg(unix)]
        {
            let symlink_parent = output_root.path().unwrap().join("linked");
            std::os::unix::fs::symlink(".", &symlink_parent).unwrap();
            assert!(write_new_file(&symlink_parent.join("escaped.json"), b"{}").is_err());
            std::fs::remove_file(symlink_parent).unwrap();
        }
        output_root
            .cleanup_exact(BTreeSet::from([PathBuf::from("report.json")]))
            .unwrap();
    }

    #[test]
    fn whnf_fixture_manifest_parser() {
        let source = include_str!(
            "../../../testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
        );
        assert!(validate_manifest(source).is_ok());
        assert!(validate_manifest("{}").is_err());
        assert!(validate_manifest(&source.replacen(
            "\"warmup\": 1,",
            "\"warmup\": 1, \"unknown\": 0,",
            1,
        ))
        .is_err());
        assert!(validate_manifest(&source.replacen(
            "opaque-neutral-head.w32.memo-off",
            "unknown.w32.memo-off",
            1,
        ))
        .is_err());
    }

    #[test]
    fn whnf_deterministic_baseline_parser() {
        let source = include_str!(
            "../../../testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
        );
        assert!(validate_baseline(source).is_ok());
        assert!(validate_baseline("{}").is_err());
        assert!(validate_baseline(&source.replacen("\"key\":", "\"unknown\":", 1)).is_err());
        assert!(validate_baseline(&source.replacen(
            "\"memo_probe_truncated\": false",
            "\"memo_probe_truncated\": 0",
            1,
        ))
        .is_err());
        assert!(compact_json("{ \"x\" : \"a b\" }")
            .unwrap()
            .contains("\"a b\""));
    }

    #[test]
    fn whnf_measurement_controller_protocol() {
        assert_eq!(parse_nine_decimal_seconds("0.000000001").unwrap(), 1);
        assert_eq!(
            parse_nine_decimal_seconds("12.345678901").unwrap(),
            12_345_678_901
        );
        assert!(parse_nine_decimal_seconds("1.2").is_err());
        assert_eq!(
            parse_measure_process_tsv("1.000000009\t2048\t0\n").unwrap(),
            (1_000_000_009, 2_048)
        );
        assert!(parse_measure_process_tsv("1.000000009\t2048\t1\n").is_err());
        assert!(parse_measure_process_tsv("1.000000009\t2048\t0").is_err());
        assert!(parse_measure_process_tsv("1.000000009\t2048\t0\n\n").is_err());
        assert_eq!(expected_series("recursive").unwrap().len(), 74);
        assert_eq!(expected_series("candidate").unwrap().len(), 92);
        let work = work_json(&KernelWorkCounters::default());
        let hash = "a".repeat(64);
        let micro = format!(
            "{{\"schema\":\"{MICRO_CHILD_SCHEMA}\",\"phase\":\"candidate\",\"scenario_id\":\"opaque-neutral-head.w32.memo-off\",\"sample_index\":0,\"mode\":\"memo-off\",\"operation_elapsed_ns\":1,\"result\":{{\"kind\":\"whnf\",\"expr_hash\":\"{hash}\"}},\"error\":null,\"work\":{work},\"named_delta_events\":[]}}"
        );
        assert!(validate_child_output(
            &micro,
            MICRO_CHILD_SCHEMA,
            "candidate",
            "opaque-neutral-head.w32.memo-off",
            "memo-off",
            0,
        )
        .is_ok());
        assert!(validate_child_output(
            &micro.replacen("\"phase\":", "\"unknown\":0,\"phase\":", 1),
            MICRO_CHILD_SCHEMA,
            "candidate",
            "opaque-neutral-head.w32.memo-off",
            "memo-off",
            0,
        )
        .is_err());
        let package = format!(
            "{{\"schema\":\"{PACKAGE_CHILD_SCHEMA}\",\"phase\":\"candidate\",\"scenario_id\":\"checked-package.off\",\"sample_index\":0,\"kernel_mode\":\"off\",\"operation_elapsed_ns\":1,\"accepted\":true,\"module_order\":[\"M\"],\"verified_modules\":[{{\"lock_name\":\"M\",\"module\":\"M\",\"export_hash\":\"{hash}\",\"certificate_hash\":\"{hash}\"}}],\"input_certificate_hashes\":[{{\"lock_name\":\"M\",\"sha256\":\"{hash}\"}}],\"aggregate_work\":{work}}}"
        );
        assert!(validate_child_output(
            &package,
            PACKAGE_CHILD_SCHEMA,
            "candidate",
            "checked-package.off",
            "off",
            0,
        )
        .is_ok());

        let temporary = make_controller_temp_dir().unwrap();
        let executable = std::env::current_exe().unwrap();
        assert_snapshot_rejects_swap(&temporary, &executable).unwrap();
        temporary
            .cleanup_exact(BTreeSet::from([PathBuf::from("snapshot-swap-probe")]))
            .unwrap();
    }

    #[test]
    fn whnf_candidate_run_report_strict_parser() {
        let identity = RunIdentity {
            source_identity: format!("git:{}-dirty", "a".repeat(40)),
            dirty: true,
            cargo_lock_sha256: "b".repeat(64),
            kwhnf_source_set_sha256: "c".repeat(64),
            kwhnf_source_set_paths: vec!["Cargo.toml".to_owned()],
            rustc_vv: "rustc test\nhost: test".to_owned(),
            target: "aarch64-apple-darwin".to_owned(),
            profile: "release",
            features: vec!["planning-benchmark".to_owned()],
            rustflags: "-Copt-level=3\u{1f}-Ctarget-cpu=native".to_owned(),
            fixture_manifest_sha256: "d".repeat(64),
            micro: ExecutableIdentity {
                source_path: MICRO_SOURCE_PATH,
                source_sha256: "e".repeat(64),
                binary_path: MICRO_BINARY_PATH,
                binary_sha256: "f".repeat(64),
            },
            package: ExecutableIdentity {
                source_path: PACKAGE_SOURCE_PATH,
                source_sha256: "1".repeat(64),
                binary_path: PACKAGE_BINARY_PATH,
                binary_sha256: "2".repeat(64),
            },
            measure: ExecutableIdentity {
                source_path: MEASURE_SOURCE_PATH,
                source_sha256: "3".repeat(64),
                binary_path: MEASURE_BINARY_PATH,
                binary_sha256: "4".repeat(64),
            },
        };
        let mut rows = Vec::new();
        for sample_index in 0..9_u64 {
            for (series_index, (scenario_id, series_kind, mode)) in expected_series("candidate")
                .unwrap()
                .into_iter()
                .enumerate()
            {
                let series_index = u64::try_from(series_index).unwrap();
                rows.push(ControllerRow {
                    scenario_id,
                    series_kind,
                    mode,
                    sample_index,
                    operation_elapsed_ns: 100 + sample_index + series_index,
                    process_elapsed_ns: 200 + sample_index + series_index,
                    peak_rss_kib: 300 + sample_index + series_index,
                    child_output_sha256: "5".repeat(64),
                });
            }
        }
        validate_controller_rows(&rows, "candidate").unwrap();
        let summaries = summarize_rows(&rows).unwrap();
        assert_eq!(rows.len(), 828);
        assert_eq!(summaries.len(), 92);
        let args = Args {
            fixture_manifest: PathBuf::from("fixture.json"),
            baseline: PathBuf::from("baseline.json"),
            scenario: None,
            list: false,
            child: false,
            controller: false,
            phase: "candidate".to_owned(),
            sample_index: 0,
            measure_process: Some(PathBuf::from(MEASURE_BINARY_PATH)),
            package_harness: Some(PathBuf::from(PACKAGE_BINARY_PATH)),
            output: None,
            elapsed_profile: None,
            review_reason: None,
            seal_recursive_baseline: None,
            archived_artifact: None,
            validate_report: Some(PathBuf::from("report.json")),
            validate_archived_artifact: None,
            validate_bootstrap_profile: None,
            collect_archived_recursive_baseline: false,
        };
        let deterministic_hash = "6".repeat(64);
        let report = controller_report_json(
            &args,
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
            &identity,
            None,
            &rows,
            &summaries,
        )
        .unwrap();
        assert!(validate_candidate_run_report_source(
            &report,
            &args,
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
            &identity,
            None,
        )
        .is_ok());
        for invalid in [
            report.replacen("\"schema\":", "\"unknown\":", 1),
            report.replacen(
                &identity.source_identity,
                &format!("git:{}-dirty", "7".repeat(40)),
                1,
            ),
            report.replacen("\"sample_index\":0", "\"sample_index\":1", 1),
            report.replacen("\"median_ns\":104", "\"median_ns\":105", 1),
            report.replacen(&"5".repeat(64), &"A".repeat(64), 1),
            format!("{report}\n"),
        ] {
            assert!(validate_candidate_run_report_source(
                &invalid,
                &args,
                &identity.fixture_manifest_sha256,
                &deterministic_hash,
                &identity,
                None,
            )
            .is_err());
        }
        assert_eq!(
            json_escape("\0\u{8}\u{c}\u{1f}"),
            "\\u0000\\u0008\\u000c\\u001f"
        );
    }

    #[test]
    fn post_switch_binary_rejects_recursive_phase_relabeling() {
        assert!(reject_recursive_phase_on_post_switch_binary("recursive").is_err());
        assert!(reject_recursive_phase_on_post_switch_binary("candidate").is_ok());
    }

    #[test]
    fn whnf_elapsed_baseline_parser() {
        let identity = RunIdentity {
            source_identity: format!("git:{}", "a".repeat(40)),
            dirty: false,
            cargo_lock_sha256: "b".repeat(64),
            kwhnf_source_set_sha256: "3".repeat(64),
            kwhnf_source_set_paths: vec!["Cargo.toml".to_owned()],
            rustc_vv: "rustc test".to_owned(),
            target: "x86_64-unknown-linux-gnu".to_owned(),
            profile: "release",
            features: vec![],
            rustflags: String::new(),
            fixture_manifest_sha256: "c".repeat(64),
            micro: ExecutableIdentity {
                source_path: MICRO_SOURCE_PATH,
                source_sha256: "d".repeat(64),
                binary_path: MICRO_BINARY_PATH,
                binary_sha256: "e".repeat(64),
            },
            package: ExecutableIdentity {
                source_path: PACKAGE_SOURCE_PATH,
                source_sha256: "f".repeat(64),
                binary_path: PACKAGE_BINARY_PATH,
                binary_sha256: "1".repeat(64),
            },
            measure: ExecutableIdentity {
                source_path: MEASURE_SOURCE_PATH,
                source_sha256: "2".repeat(64),
                binary_path: MEASURE_BINARY_PATH,
                binary_sha256: "3".repeat(64),
            },
        };
        let mut rows = Vec::new();
        for sample_index in 0..9_u64 {
            for (scenario_id, series_kind, mode) in expected_series("recursive").unwrap() {
                rows.push(ControllerRow {
                    scenario_id,
                    series_kind,
                    mode,
                    sample_index,
                    operation_elapsed_ns: sample_index + 1,
                    process_elapsed_ns: sample_index + 11,
                    peak_rss_kib: sample_index + 101,
                    child_output_sha256: "4".repeat(64),
                });
            }
        }
        validate_controller_rows(&rows, "recursive").unwrap();
        let summaries = summarize_rows(&rows).unwrap();
        let args = Args {
            fixture_manifest: PathBuf::from("fixture.json"),
            baseline: PathBuf::from("baseline.json"),
            scenario: None,
            list: false,
            child: false,
            controller: true,
            phase: "recursive".to_owned(),
            sample_index: 0,
            measure_process: Some(PathBuf::from(MEASURE_BINARY_PATH)),
            package_harness: Some(PathBuf::from(PACKAGE_BINARY_PATH)),
            output: Some(PathBuf::from("report.json")),
            elapsed_profile: None,
            review_reason: Some("test".to_owned()),
            seal_recursive_baseline: None,
            archived_artifact: None,
            validate_report: None,
            validate_archived_artifact: None,
            validate_bootstrap_profile: None,
            collect_archived_recursive_baseline: false,
        };
        let deterministic_hash = "5".repeat(64);
        let report = controller_report_json(
            &args,
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
            &identity,
            None,
            &rows,
            &summaries,
        )
        .unwrap();
        let mut candidate = identity.clone();
        candidate.source_identity = format!("git:{}", "6".repeat(40));
        candidate.micro.source_sha256 = "8".repeat(64);
        candidate.package.source_sha256 = "9".repeat(64);
        assert_eq!(
            validate_elapsed_baseline_identity(
                &report,
                BaselineIdentityExpectation::Candidate(&candidate),
                &deterministic_hash,
            )
            .unwrap()
            .len(),
            74
        );
        assert!(validate_elapsed_baseline_identity(
            &report.replacen("\"sample_index\":0", "\"sample_index\":9", 1),
            BaselineIdentityExpectation::Candidate(&candidate),
            &deterministic_hash,
        )
        .is_err());
        assert!(validate_elapsed_baseline_identity(
            &report.replacen("\"median_ns\":5", "\"median_ns\":6", 1),
            BaselineIdentityExpectation::Candidate(&candidate),
            &deterministic_hash,
        )
        .is_err());
        assert!(validate_elapsed_baseline_identity(
            &report,
            BaselineIdentityExpectation::Candidate(&identity),
            &deterministic_hash,
        )
        .is_err());
    }

    #[test]
    fn whnf_pre_switch_artifact_parser() {
        let identity = RunIdentity {
            source_identity: format!("git:{}", "a".repeat(40)),
            dirty: false,
            cargo_lock_sha256: "b".repeat(64),
            kwhnf_source_set_sha256: "3".repeat(64),
            kwhnf_source_set_paths: vec!["Cargo.toml".to_owned()],
            rustc_vv: "rustc reviewed".to_owned(),
            target: "x86_64-unknown-linux-gnu".to_owned(),
            profile: "release",
            features: vec![],
            rustflags: String::new(),
            fixture_manifest_sha256: "c".repeat(64),
            micro: ExecutableIdentity {
                source_path: MICRO_SOURCE_PATH,
                source_sha256: "d".repeat(64),
                binary_path: MICRO_BINARY_PATH,
                binary_sha256: "e".repeat(64),
            },
            package: ExecutableIdentity {
                source_path: PACKAGE_SOURCE_PATH,
                source_sha256: "f".repeat(64),
                binary_path: PACKAGE_BINARY_PATH,
                binary_sha256: "1".repeat(64),
            },
            measure: ExecutableIdentity {
                source_path: MEASURE_SOURCE_PATH,
                source_sha256: "2".repeat(64),
                binary_path: MEASURE_BINARY_PATH,
                binary_sha256: "3".repeat(64),
            },
        };
        let deterministic_hash = "4".repeat(64);
        let source = format!(
            "{{\"schema\":\"{PRE_SWITCH_ARTIFACT_SCHEMA}\",\"implementation\":\"{PRE_SWITCH_IMPLEMENTATION}\",\"archive_root\":\"/reviewed/pre-switch\",\"deterministic_baseline_sha256\":\"{deterministic_hash}\",\"identity\":{}}}",
            identity_json(&identity),
        );
        let parsed = parse_pre_switch_artifact(
            &source,
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
        )
        .unwrap();
        assert_eq!(parsed.identity.source_identity, identity.source_identity);
        assert_eq!(parsed.identity.micro.source_sha256, "d".repeat(64));
        assert!(parse_pre_switch_artifact(
            &source.replace(PRE_SWITCH_IMPLEMENTATION, "machine-post-switch"),
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
        )
        .is_err());
        assert!(parse_pre_switch_artifact(
            &source.replace(MICRO_SOURCE_PATH, PACKAGE_SOURCE_PATH),
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
        )
        .is_err());
        assert!(parse_pre_switch_artifact(
            &source.replacen("\"kwhnf_source_set_paths\":[\"Cargo.toml\"],", "", 1),
            &identity.fixture_manifest_sha256,
            &deterministic_hash,
        )
        .is_err());
        assert!(parse_pre_switch_artifact(&source, &"5".repeat(64), &deterministic_hash,).is_err());

        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let parent = std::fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!(
                "npa-whnf-archive-containment-{}-{unique}",
                std::process::id()
            ));
        let archive = parent.join("archive");
        let binary = archive.join(MICRO_BINARY_PATH);
        std::fs::create_dir_all(binary.parent().unwrap()).unwrap();
        std::fs::write(&binary, b"reviewed executable").unwrap();
        assert_eq!(canonical_archive_root(&archive).unwrap(), archive);
        assert_eq!(
            canonical_archive_regular_file(&archive, MICRO_BINARY_PATH).unwrap(),
            binary
        );

        let outside = parent.join("outside-executable");
        std::fs::write(&outside, b"reviewed executable").unwrap();
        std::fs::remove_file(&binary).unwrap();
        std::os::unix::fs::symlink(&outside, &binary).unwrap();
        assert!(canonical_archive_regular_file(&archive, MICRO_BINARY_PATH).is_err());

        let archive_link = parent.join("archive-link");
        std::os::unix::fs::symlink(&archive, &archive_link).unwrap();
        assert!(canonical_archive_root(&archive_link).is_err());
        std::fs::remove_dir_all(&parent).unwrap();
    }

    #[test]
    fn whnf_pre_switch_candidate_identity_contract() {
        let archived = ArchivedRunIdentity {
            source_identity: format!("git:{}", "a".repeat(40)),
            cargo_lock_sha256: "b".repeat(64),
            kwhnf_source_set_sha256: "c".repeat(64),
            kwhnf_source_set_paths: vec!["Cargo.toml".to_owned()],
            rustc_vv: "rustc reviewed".to_owned(),
            target: "x86_64-unknown-linux-gnu".to_owned(),
            profile: "release".to_owned(),
            features: vec![],
            rustflags: String::new(),
            fixture_manifest_sha256: "c".repeat(64),
            micro: ArchivedExecutableIdentity {
                source_path: MICRO_SOURCE_PATH.to_owned(),
                source_sha256: "d".repeat(64),
                binary_path: MICRO_BINARY_PATH.to_owned(),
                binary_sha256: "e".repeat(64),
            },
            package: ArchivedExecutableIdentity {
                source_path: PACKAGE_SOURCE_PATH.to_owned(),
                source_sha256: "f".repeat(64),
                binary_path: PACKAGE_BINARY_PATH.to_owned(),
                binary_sha256: "1".repeat(64),
            },
            measure: ArchivedExecutableIdentity {
                source_path: MEASURE_SOURCE_PATH.to_owned(),
                source_sha256: "2".repeat(64),
                binary_path: MEASURE_BINARY_PATH.to_owned(),
                binary_sha256: "3".repeat(64),
            },
        };
        let mut candidate = RunIdentity {
            source_identity: format!("git:{}", "4".repeat(40)),
            dirty: false,
            cargo_lock_sha256: archived.cargo_lock_sha256.clone(),
            kwhnf_source_set_sha256: "d".repeat(64),
            kwhnf_source_set_paths: vec!["different/Cargo.toml".to_owned()],
            rustc_vv: archived.rustc_vv.clone(),
            target: archived.target.clone(),
            profile: "release",
            features: vec![],
            rustflags: String::new(),
            fixture_manifest_sha256: archived.fixture_manifest_sha256.clone(),
            micro: ExecutableIdentity {
                source_path: MICRO_SOURCE_PATH,
                source_sha256: "5".repeat(64),
                binary_path: MICRO_BINARY_PATH,
                binary_sha256: "6".repeat(64),
            },
            package: ExecutableIdentity {
                source_path: PACKAGE_SOURCE_PATH,
                source_sha256: "7".repeat(64),
                binary_path: PACKAGE_BINARY_PATH,
                binary_sha256: "8".repeat(64),
            },
            measure: ExecutableIdentity {
                source_path: MEASURE_SOURCE_PATH,
                source_sha256: "9".repeat(64),
                binary_path: MEASURE_BINARY_PATH,
                binary_sha256: "0".repeat(64),
            },
        };
        assert!(validate_archived_identity_expectation(
            &archived,
            BaselineIdentityExpectation::Candidate(&candidate),
        )
        .is_ok());
        candidate.cargo_lock_sha256 = "a".repeat(64);
        assert!(validate_archived_identity_expectation(
            &archived,
            BaselineIdentityExpectation::Candidate(&candidate),
        )
        .is_err());
        candidate.cargo_lock_sha256 = archived.cargo_lock_sha256.clone();
        candidate.source_identity = archived.source_identity.clone();
        assert!(validate_archived_identity_expectation(
            &archived,
            BaselineIdentityExpectation::Candidate(&candidate),
        )
        .is_err());
    }

    #[test]
    fn whnf_harness_identity_uses_embedded_build_provenance() {
        let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX")).unwrap();
        assert!(!rustc_vv.trim().is_empty());
        assert!(rustc_vv.ends_with('\n'));
        assert!(rustc_vv.lines().any(|line| line.starts_with("host: ")));
        assert!(!env!("NPA_BUILD_TARGET").is_empty());
        for hash in [
            env!("NPA_BUILD_CARGO_LOCK_SHA256"),
            env!("NPA_BUILD_KWHNF_SOURCE_SET_SHA256"),
            env!("NPA_BUILD_WHNF_MICRO_SOURCE_SHA256"),
            env!("NPA_BUILD_WHNF_PACKAGE_SOURCE_SHA256"),
            env!("NPA_BUILD_MEASURE_PROCESS_SOURCE_SHA256"),
        ] {
            validate_lower_hex_hash(hash, "embedded build file hash").unwrap();
        }
        let embedded_source = embedded_file_hash_matches_runtime(
            MICRO_SOURCE_PATH,
            env!("NPA_BUILD_WHNF_MICRO_SOURCE_SHA256"),
        );
        assert!(embedded_source.is_ok(), "{embedded_source:?}");
        let source_set = validate_runtime_kwhnf_source_set();
        assert_eq!(
            source_set.as_ref().map(|(hash, _)| hash.as_str()),
            Ok(env!("NPA_BUILD_KWHNF_SOURCE_SET_SHA256"))
        );
        assert_eq!(
            source_set.unwrap().1,
            parse_kwhnf_source_set_paths(env!("NPA_BUILD_KWHNF_SOURCE_SET_PATHS")).unwrap()
        );
        let source_paths = env!("NPA_BUILD_KWHNF_SOURCE_SET_PATHS");
        assert!(source_paths.starts_with("Cargo.toml,"));
        assert!(source_paths.contains("crates/npa-api/src/lib.rs"));
        assert!(source_paths.contains("crates/npa-cert/src/kernel.rs"));
        assert!(source_paths.contains("crates/npa-checker-ref/src/lib.rs"));
        assert!(source_paths.contains("crates/npa-frontend/src/elaborator.rs"));
        assert!(source_paths.contains("crates/npa-kernel/src/env.rs"));
        assert!(source_paths.contains("crates/npa-package/src/lib.rs"));
        assert!(source_paths.contains("crates/npa-tactic/src/lib.rs"));
        assert!(source_paths.contains("bench_whnf_application_spine.rs"));
        assert!(source_paths.contains("measure_process.rs"));
        assert!(embedded_file_hash_matches_runtime(MICRO_SOURCE_PATH, &"0".repeat(64)).is_err());
        assert_eq!(
            decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX")).unwrap(),
            decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX")).unwrap()
        );
        assert!(matches!(env!("NPA_BUILD_CARGO_PROFILE"), "dev" | "release"));
        let features = embedded_build_features();
        assert!(features.windows(2).all(|pair| pair[0] < pair[1]));
        assert_eq!(features.join(","), env!("NPA_BUILD_CARGO_FEATURES"));
        assert!(features
            .iter()
            .all(|feature| matches!(feature.as_str(), "default" | "planning-benchmark")));
        assert!(!features.iter().any(|feature| feature.contains('_')));
        assert!(decode_build_hex("0").is_err());
        assert!(decode_build_hex("xz").is_err());
        let clean = "a".repeat(40);
        let dirty = format!("{clean}-dirty");
        assert!(validate_build_bound_source_identity(&clean, &clean).is_ok());
        assert!(validate_build_bound_source_identity(&dirty, &dirty).is_ok());
        assert!(validate_build_bound_source_identity("unbound", &clean).is_err());
        assert!(validate_build_bound_source_identity(&clean, &dirty).is_err());
        assert!(validate_build_bound_source_identity(&"g".repeat(40), &clean).is_err());
    }

    #[test]
    fn whnf_archived_source_set_uses_artifact_catalog() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let archive = std::fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!(
                "npa-whnf-source-set-{}-{unique}",
                std::process::id()
            ));
        std::fs::create_dir(&archive).unwrap();
        let workspace =
            std::fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")).unwrap();
        let paths = parse_kwhnf_source_set_paths(env!("NPA_BUILD_KWHNF_SOURCE_SET_PATHS")).unwrap();
        for relative in &paths {
            let destination = archive.join(relative);
            std::fs::create_dir_all(destination.parent().unwrap()).unwrap();
            std::fs::copy(workspace.join(relative), destination).unwrap();
        }
        assert_eq!(
            archived_kwhnf_source_set_sha256(&archive, &paths).unwrap(),
            env!("NPA_BUILD_KWHNF_SOURCE_SET_SHA256")
        );
        std::fs::write(archive.join(&paths[0]), b"mutated").unwrap();
        assert_ne!(
            archived_kwhnf_source_set_sha256(&archive, &paths).unwrap(),
            env!("NPA_BUILD_KWHNF_SOURCE_SET_SHA256")
        );
        assert!(archived_kwhnf_source_set_sha256(&archive, &["../escape.rs".to_owned()]).is_err());
        std::fs::remove_dir_all(archive).unwrap();
    }

    #[test]
    fn whnf_controller_temp_directory_is_private_and_guarded() {
        let temporary = make_controller_temp_dir().unwrap();
        assert!(temporary.path().unwrap().is_absolute());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                std::fs::symlink_metadata(temporary.path().unwrap())
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

        let input_swap = make_controller_temp_dir().unwrap();
        let input = input_swap
            .create_input_snapshot(Path::new("fixture-manifest.json"), b"original\n")
            .unwrap();
        assert_eq!(
            input.read_all_bounded(16 * 1024 * 1024).unwrap(),
            b"original\n"
        );
        let path = input_swap.path().unwrap().join("fixture-manifest.json");
        let relocated = path.with_extension("opened");
        std::fs::rename(&path, &relocated).unwrap();
        std::fs::write(&path, b"replacement\n").unwrap();
        assert!(input.read_all_bounded(16 * 1024 * 1024).is_err());
        std::fs::remove_file(&path).unwrap();
        std::fs::rename(&relocated, &path).unwrap();
        drop(input);
        input_swap
            .cleanup_exact(BTreeSet::from([PathBuf::from("fixture-manifest.json")]))
            .unwrap();

        let suspicious = make_controller_temp_dir().unwrap();
        std::fs::create_dir(suspicious.path().unwrap().join("nested")).unwrap();
        assert!(suspicious
            .0
            .as_ref()
            .unwrap()
            .remove_allowed_root(&whnf_controller_temp_catalog("candidate").unwrap())
            .is_err());
        std::fs::remove_dir(suspicious.path().unwrap().join("nested")).unwrap();
        suspicious.cleanup_exact(BTreeSet::new()).unwrap();

        #[cfg(unix)]
        {
            let symlinked = make_controller_temp_dir().unwrap();
            std::os::unix::fs::symlink("missing", symlinked.path().unwrap().join("link")).unwrap();
            assert!(symlinked
                .0
                .as_ref()
                .unwrap()
                .remove_allowed_root(&whnf_controller_temp_catalog("candidate").unwrap())
                .is_err());
            std::fs::remove_file(symlinked.path().unwrap().join("link")).unwrap();
            symlinked.cleanup_exact(BTreeSet::new()).unwrap();

            let renamed = make_controller_temp_dir().unwrap();
            let original = renamed.path().unwrap().to_owned();
            let relocated = original.with_extension("relocated");
            std::fs::write(original.join("sentinel"), b"keep").unwrap();
            std::fs::rename(&original, &relocated).unwrap();
            std::fs::create_dir(&original).unwrap();
            drop(renamed);
            assert_eq!(std::fs::read(relocated.join("sentinel")).unwrap(), b"keep");
            assert!(original.is_dir());
            std::fs::remove_dir(original).unwrap();
            std::fs::remove_file(relocated.join("sentinel")).unwrap();
            std::fs::remove_dir(relocated).unwrap();
        }
    }

    #[test]
    fn whnf_elapsed_profile_parser() {
        assert!(validate_lower_hex_hash(&"a".repeat(64), "test").is_ok());
        assert!(validate_lower_hex_hash(&"A".repeat(64), "test").is_err());
        assert!(validate_lower_hex_hash(&"a".repeat(63), "test").is_err());
        assert_eq!(
            REVIEWED_PROFILE_ID,
            "kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1"
        );
        let missing = ElapsedProfile {
            sha256: "a".repeat(64),
            baseline_sha256: "b".repeat(64),
            baseline_summaries: None,
        };
        assert!(validate_elapsed_gates(&missing, &[]).is_ok());

        let canonical_temp = std::env::temp_dir().canonicalize().unwrap();
        let profile_path = canonical_temp.join(format!(
            "npa-whnf-profile-parser-{}.json",
            std::process::id()
        ));
        let missing_baseline = canonical_temp.join(format!(
            "npa-whnf-profile-parser-missing-baseline-{}.json",
            std::process::id()
        ));
        let fixture_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json");
        let identity = RunIdentity {
            source_identity: format!("git:{}", "a".repeat(40)),
            dirty: false,
            cargo_lock_sha256: "b".repeat(64),
            kwhnf_source_set_sha256: "3".repeat(64),
            kwhnf_source_set_paths: vec!["Cargo.toml".to_owned()],
            rustc_vv: "rustc test".to_owned(),
            target: "x86_64-unknown-linux-gnu".to_owned(),
            profile: "release",
            features: vec![],
            rustflags: String::new(),
            fixture_manifest_sha256: "c".repeat(64),
            micro: ExecutableIdentity {
                source_path: MICRO_SOURCE_PATH,
                source_sha256: "d".repeat(64),
                binary_path: MICRO_BINARY_PATH,
                binary_sha256: "e".repeat(64),
            },
            package: ExecutableIdentity {
                source_path: PACKAGE_SOURCE_PATH,
                source_sha256: "f".repeat(64),
                binary_path: PACKAGE_BINARY_PATH,
                binary_sha256: "1".repeat(64),
            },
            measure: ExecutableIdentity {
                source_path: MEASURE_SOURCE_PATH,
                source_sha256: "2".repeat(64),
                binary_path: MEASURE_BINARY_PATH,
                binary_sha256: "3".repeat(64),
            },
        };
        let profile_source = format!(
            "{{\"schema\":\"{ELAPSED_PROFILE_SCHEMA}\",\"profile_id\":\"{REVIEWED_PROFILE_ID}\",\"host\":\"reviewed Linux x86_64 test host\",\"target\":\"x86_64-unknown-linux-gnu\",\"rustc_vv\":\"rustc test\",\"cargo_profile\":\"release\",\"features\":[],\"rustflags\":\"\",\"warmup\":1,\"samples\":9,\"fixture_manifest_sha256\":\"{}\",\"baseline_path\":{},\"baseline_hash\":\"{}\",\"review_reason\":\"reviewed fixture\",\"gates\":[{{\"numerator\":3,\"denominator\":4}},{{\"numerator\":6,\"denominator\":1}},{{\"numerator\":11,\"denominator\":10}},{{\"numerator\":23,\"denominator\":20}},{{\"numerator\":21,\"denominator\":20}},{{\"numerator\":1,\"denominator\":10}},{{\"rss\":16384}},{{\"rss\":8192}}]}}",
            identity.fixture_manifest_sha256,
            quoted(&missing_baseline.display().to_string()),
            "4".repeat(64),
        );
        let mut profile_file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&profile_path)
            .unwrap();
        use std::io::Write as _;
        profile_file.write_all(profile_source.as_bytes()).unwrap();
        drop(profile_file);
        let parsed = validate_elapsed_profile_with_baseline_path(
            &profile_path,
            &identity,
            &fixture_path,
            &"5".repeat(64),
            &missing_baseline,
        )
        .unwrap();
        assert!(parsed.baseline_summaries.is_none());
        assert!(validate_elapsed_profile_for_phase("recursive", Some(&parsed)).is_ok());
        assert!(validate_elapsed_profile_for_phase("candidate", Some(&parsed)).is_err());
        std::fs::write(
            &profile_path,
            profile_source.replacen("\"gates\":[", "\"unknown\":0,\"gates\":[", 1),
        )
        .unwrap();
        assert!(validate_elapsed_profile_with_baseline_path(
            &profile_path,
            &identity,
            &fixture_path,
            &"5".repeat(64),
            &missing_baseline,
        )
        .is_err());
        std::fs::write(
            &profile_path,
            profile_source.replacen(
                "\"numerator\":3,\"denominator\":4",
                "\"numerator\":4,\"denominator\":4",
                1,
            ),
        )
        .unwrap();
        assert!(validate_elapsed_profile_with_baseline_path(
            &profile_path,
            &identity,
            &fixture_path,
            &"5".repeat(64),
            &missing_baseline,
        )
        .is_err());
        std::fs::remove_file(&profile_path).unwrap();
    }

    #[test]
    fn whnf_harness_identity_binding() {
        whnf_harness_identity_uses_embedded_build_provenance();
        let identity = ExecutableIdentity {
            source_path: MICRO_SOURCE_PATH,
            source_sha256: "a".repeat(64),
            binary_path: MICRO_BINARY_PATH,
            binary_sha256: "b".repeat(64),
        };
        let json = executable_identity_json(&identity);
        assert!(json.contains(MICRO_SOURCE_PATH));
        assert!(json.contains(MICRO_BINARY_PATH));
        assert!(!json.contains(PACKAGE_BINARY_PATH));
    }

    #[test]
    fn whnf_elapsed_rss_gate_arithmetic() {
        assert!(checked_ratio_le(3, 4, 3, 4).unwrap());
        assert!(!checked_ratio_le(4, 4, 3, 4).unwrap());
        assert!(checked_ratio_le(u64::MAX, u64::MAX, 1, 1).unwrap());
        assert!(checked_ratio_le(11, 10, 11, 10).unwrap());
        assert!(!checked_ratio_le(12, 10, 11, 10).unwrap());
        assert!(checked_ratio_le(23, 20, 23, 20).unwrap());
        assert!(!checked_ratio_le(24, 20, 23, 20).unwrap());
        assert!(checked_ratio_le(21, 20, 21, 20).unwrap());
        assert!(!checked_ratio_le(22, 20, 21, 20).unwrap());
        assert!(checked_ratio_le(60, 10, 6, 1).unwrap());
        assert!(!checked_ratio_le(61, 10, 6, 1).unwrap());
        assert!(checked_ratio_le(1, 10, 1, 10).unwrap());
        assert!(!checked_ratio_le(2, 10, 1, 10).unwrap());
        assert!(checked_ratio_le(0, 0, 1, 10).unwrap());
        assert!(checked_ratio_le(1, 0, 1, 10).unwrap() == false);
        assert!(checked_ratio_le(1, 1, 1, 0).is_err());
        let baseline = 100_000_u64;
        let micro_limit = baseline + (baseline / 10).max(16_384);
        let package_limit = baseline + (baseline / 10).max(8_192);
        assert_eq!(micro_limit, 116_384);
        assert_eq!(package_limit, 110_000);
        assert!(micro_limit <= micro_limit);
        assert!(micro_limit + 1 > micro_limit);
        assert!(package_limit <= package_limit);
        assert!(package_limit + 1 > package_limit);
    }
}
