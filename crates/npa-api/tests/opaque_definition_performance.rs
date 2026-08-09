use npa_cert::{
    build_module_cert_from_import_refs, encode_module_cert, verified_module_to_kernel_decls,
    verify_module_cert_with_import_refs_and_kernel_options_and_work_counters, AxiomPolicy,
    CoreModule, Name, VerifiedModule,
};
use npa_frontend::{
    compile_human_source_to_core, compile_machine_source_to_core, FileId, HumanCompileOptions,
    MachineCompileOptions,
};
use npa_kernel::{
    prop, Ctx, Decl, Env, Expr, KernelExecutionOptions, KernelWorkCounters, Reducibility,
};
use std::process::Command;

const CHILD_ENV: &str = "NPA_ODS18_OPAQUE_PERFORMANCE_CHILD";
const SNAPSHOT_PREFIX: &str = "ODS18_OPAQUE_PERFORMANCE=";
const REDUCTION_DEPTH: usize = 32;

#[derive(Clone, Copy)]
struct PairCounters {
    defining_opaque: KernelWorkCounters,
    defining_reducible: KernelWorkCounters,
    consumer_opaque: KernelWorkCounters,
    consumer_reducible: KernelWorkCounters,
    downstream_opaque: KernelWorkCounters,
    downstream_reducible: KernelWorkCounters,
}

fn nested_identity_source() -> String {
    let mut body = "fun (P : Prop) => P".to_owned();
    for _ in 0..REDUCTION_DEPTH {
        body = format!("(fun (f : forall (P : Prop), Prop) => f) ({body})");
    }
    body
}

fn leaf_source(module: &str, reducibility: Reducibility) -> String {
    let modifier = match reducibility {
        Reducibility::Opaque => "opaque ",
        Reducibility::Reducible => "",
    };
    let body = nested_identity_source();
    format!(
        "{modifier}def {module}.evaluator : forall (P : Prop), Prop := {body}\n\
         theorem {module}.evaluator_spec (P : Prop) (p : P) : \
         {module}.evaluator P := p"
    )
}

fn compile_leaf(module: &str, reducibility: Reducibility) -> CoreModule {
    let source = leaf_source(module, reducibility);
    let module_name = Name::from_dotted(module);
    let human = compile_human_source_to_core(
        FileId(0),
        module_name.clone(),
        &source,
        &[],
        &HumanCompileOptions::default(),
    )
    .expect("Human parsing and elaboration must accept the paired fixture");
    let machine = compile_machine_source_to_core(
        FileId(0),
        module_name,
        &source,
        &[],
        &MachineCompileOptions::default(),
    )
    .expect("Machine parsing and elaboration must accept the paired fixture");
    assert_eq!(
        human, machine,
        "Human and Machine must elaborate identically"
    );
    human
}

fn verify_with_counters(
    module: CoreModule,
    imports: &[&VerifiedModule],
    options: KernelExecutionOptions,
) -> (VerifiedModule, KernelWorkCounters) {
    let cert = build_module_cert_from_import_refs(module, imports).expect("fixture must certify");
    let bytes = encode_module_cert(&cert).expect("fixture certificate must encode");
    let mut counters = KernelWorkCounters::default();
    let verified = verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
        &bytes,
        imports,
        &AxiomPolicy::normal(),
        options,
        &mut counters,
    )
    .expect("fixture certificate must verify");
    (verified, counters)
}

fn consumer_module(module: &str, leaf_module: &str) -> CoreModule {
    let evaluator = format!("{leaf_module}.evaluator");
    let specification = format!("{leaf_module}.evaluator_spec");
    CoreModule {
        name: Name::from_dotted(module),
        declarations: vec![Decl::Theorem {
            name: format!("{module}.uses_evaluator_spec"),
            universe_params: vec![],
            ty: Expr::pi(
                "P",
                Expr::sort(prop()),
                Expr::pi(
                    "p",
                    Expr::bvar(0),
                    Expr::app(Expr::konst(evaluator, vec![]), Expr::bvar(1)),
                ),
            ),
            proof: Expr::konst(specification, vec![]),
        }],
    }
}

fn downstream_normalization(
    module: &VerifiedModule,
    evaluator: &str,
    options: KernelExecutionOptions,
) -> (Expr, KernelWorkCounters) {
    let mut env = Env::with_builtins_and_execution_options(options)
        .expect("fixture environment must install builtins");
    for declaration in
        verified_module_to_kernel_decls(module).expect("verified exports must project")
    {
        env.add_decl_diagnosed(declaration)
            .expect("verified export must install");
    }
    let mut counters = KernelWorkCounters::default();
    let result = env
        .whnf_with_work_counters(
            &Ctx::new(),
            &[],
            &Expr::konst(evaluator, vec![]),
            Some(&mut counters),
        )
        .expect("downstream normalization query must complete");
    (result, counters)
}

fn measure_pair(options: KernelExecutionOptions) -> PairCounters {
    let (opaque, defining_opaque) = verify_with_counters(
        compile_leaf("OdsOpaque", Reducibility::Opaque),
        &[],
        options,
    );
    let (reducible, defining_reducible) = verify_with_counters(
        compile_leaf("OdsReducible", Reducibility::Reducible),
        &[],
        options,
    );

    let (_, consumer_opaque) = verify_with_counters(
        consumer_module("OdsOpaqueConsumer", "OdsOpaque"),
        &[&opaque],
        options,
    );
    let (_, consumer_reducible) = verify_with_counters(
        consumer_module("OdsReducibleConsumer", "OdsReducible"),
        &[&reducible],
        options,
    );

    let (opaque_result, downstream_opaque) =
        downstream_normalization(&opaque, "OdsOpaque.evaluator", options);
    let (reducible_result, downstream_reducible) =
        downstream_normalization(&reducible, "OdsReducible.evaluator", options);

    assert_eq!(
        opaque_result,
        Expr::konst("OdsOpaque.evaluator", vec![]),
        "the imported opaque body must remain unavailable"
    );
    assert_eq!(
        reducible_result,
        Expr::lam("_", Expr::sort(prop()), Expr::bvar(0)),
        "the paired reducible evaluator must normalize to its specified result"
    );
    assert_eq!(
        stable_counter_fields(defining_opaque),
        stable_counter_fields(defining_reducible),
        "opaque must not skip defining-module body checking or fuel accounting"
    );
    assert!(defining_opaque.check_calls > 0);
    assert!(defining_opaque.physical_reductions > 0);
    assert!(defining_opaque.logical_fuel > 0);
    assert_eq!(consumer_opaque.exhausted_fuel, 0);
    assert_eq!(consumer_reducible.exhausted_fuel, 0);
    assert!(
        consumer_opaque.logical_fuel <= consumer_reducible.logical_fuel,
        "using the opaque specification API must not increase downstream logical fuel"
    );
    assert!(
        downstream_opaque.physical_reductions < downstream_reducible.physical_reductions,
        "opaque downstream normalization must perform fewer physical reductions"
    );
    assert_eq!(downstream_opaque.exhausted_fuel, 0);
    assert_eq!(downstream_reducible.exhausted_fuel, 0);

    PairCounters {
        defining_opaque,
        defining_reducible,
        consumer_opaque,
        consumer_reducible,
        downstream_opaque,
        downstream_reducible,
    }
}

fn stable_counter_fields(counters: KernelWorkCounters) -> String {
    format!(
        "checks={},infer={},whnf={},defeq={},beta={},delta={},physical={},logical_fuel={},successful_fuel={},exhausted_fuel={}",
        counters.check_calls,
        counters.infer_calls,
        counters.whnf_calls,
        counters.defeq_calls,
        counters.beta_steps,
        counters.delta_steps,
        counters.physical_reductions,
        counters.logical_fuel,
        counters.successful_fuel,
        counters.exhausted_fuel,
    )
}

fn stable_snapshot() -> String {
    let modes = [
        ("memo_off", KernelExecutionOptions::memo_off()),
        ("ephemeral_memo", KernelExecutionOptions::ephemeral_memo()),
    ];
    let mut sections = Vec::new();
    for (name, options) in modes {
        let counters = measure_pair(options);
        sections.push(format!(
            "{name}[defining_opaque:({});defining_reducible:({});consumer_opaque:({});consumer_reducible:({});downstream_opaque:({});downstream_reducible:({})]",
            stable_counter_fields(counters.defining_opaque),
            stable_counter_fields(counters.defining_reducible),
            stable_counter_fields(counters.consumer_opaque),
            stable_counter_fields(counters.consumer_reducible),
            stable_counter_fields(counters.downstream_opaque),
            stable_counter_fields(counters.downstream_reducible),
        ));
    }
    sections.join("|")
}

fn baseline_snapshot() -> String {
    let modes = [
        ("memo_off", KernelExecutionOptions::memo_off()),
        ("ephemeral_memo", KernelExecutionOptions::ephemeral_memo()),
    ];
    let mut rows = vec![
        "mode\tphase\treducibility\taccepted\tphysical_reductions\tlogical_fuel\texhausted_fuel"
            .to_owned(),
    ];
    for (mode, options) in modes {
        let counters = measure_pair(options);
        for (phase, reducibility, work) in [
            ("defining", "opaque", counters.defining_opaque),
            ("defining", "reducible", counters.defining_reducible),
            ("consumer", "opaque", counters.consumer_opaque),
            ("consumer", "reducible", counters.consumer_reducible),
            (
                "downstream_normalization",
                "opaque",
                counters.downstream_opaque,
            ),
            (
                "downstream_normalization",
                "reducible",
                counters.downstream_reducible,
            ),
        ] {
            rows.push(format!(
                "{mode}\t{phase}\t{reducibility}\ttrue\t{}\t{}\t{}",
                work.physical_reductions, work.logical_fuel, work.exhausted_fuel
            ));
        }
    }
    rows.join("\n")
}

fn child_snapshot() -> String {
    let output = Command::new(std::env::current_exe().expect("test executable must exist"))
        .arg("--exact")
        .arg("opaque_definition_performance_is_deterministic_across_fresh_processes")
        .arg("--nocapture")
        .env(CHILD_ENV, "1")
        .output()
        .expect("fresh fixture process must start");
    assert!(
        output.status.success(),
        "fresh fixture process failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("fixture stdout must be UTF-8")
        .lines()
        .find_map(|line| line.strip_prefix(SNAPSHOT_PREFIX).map(str::to_owned))
        .expect("fresh fixture process must emit its deterministic snapshot")
}

#[test]
fn opaque_definition_performance_is_deterministic_across_fresh_processes() {
    if std::env::var_os(CHILD_ENV).is_some() {
        assert_eq!(
            baseline_snapshot(),
            include_str!("../../../testdata/performance/baselines/opaque-definition.v0.1.tsv")
                .trim_end(),
            "trusted opacity counters must match the checked-in deterministic baseline"
        );
        println!("{SNAPSHOT_PREFIX}{}", stable_snapshot());
        return;
    }

    let first = child_snapshot();
    let second = child_snapshot();
    assert_eq!(
        first, second,
        "trusted performance evidence must be identical across fresh processes"
    );
}
