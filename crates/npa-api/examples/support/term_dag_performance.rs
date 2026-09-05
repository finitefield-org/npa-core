//! Closed host-independent catalog for the certificate term-DAG release harness.

#![allow(dead_code)]

use std::{
    collections::BTreeSet,
    path::{Component, Path, PathBuf},
    time::Instant,
};

use super::closed_private_tree::{
    read_absolute_regular_file, read_absolute_regular_tree, ClosedPrivateDirectory,
};

use npa_api::JsonDocument;
use npa_cert::{
    benchmark_term_materialization_plan_v1, build_module_cert,
    CertificateTermMaterializationObservation, CoreModule, ModuleCert, Name,
    TermMaterializationBenchmarkResultV1,
};
use npa_kernel::{Decl, Expr, Level};
use sha2::{Digest, Sha256};

pub const MANIFEST_SCHEMA: &str = "npa.certificate-term-dag-materialization.fixtures.v0.1";
pub const BASELINE_SCHEMA: &str = "npa.certificate-term-dag-materialization.measurements.v0.1";
pub const CHILD_SCHEMA: &str = "npa.certificate-term-dag-materialization.child.v0.1";
pub const RUN_SCHEMA: &str = "npa.certificate-term-dag-materialization.run.v0.2";
pub const MEASUREMENT_SCHEMA: &str = "npa.performance.measurements.v0.9";
pub const BUDGET_POLICY: &str = "npa.certificate-term-materialization-budget.v1";
pub const CHARGED_BYTE_LIMIT: u64 = 268_435_456;
pub const EXPR_INLINE_BYTES: u64 = 64;
pub const ARC_NODE_METADATA_BYTES: u64 = 64;
pub const ARC_LAYOUT_ALLOWANCE_BYTES: u64 = 48;
pub const OPTION_ARC_SLOT_BYTES: u64 = 8;
pub const TERM_ID_SLOT_BYTES: u64 = 8;
pub const SELECTION_SLOT_BYTES: u64 = 1;
pub const LEVEL_NODE_BYTES: u64 = 64;
pub const PLANNER_RECORD_BYTES: u64 = 256;
pub const FIXTURE_ROOT: &str = "testdata/performance/certificate-term-dag-materialization";
pub const MANIFEST_PATH: &str =
    "testdata/performance/fixtures/certificate-term-dag-materialization.v0.1.json";
pub const BASELINE_PATH: &str =
    "testdata/performance/baselines/certificate-term-dag-materialization.measurements.v0.1.json";
pub const MEMORY_MODEL: &str = "npa.fast-shard-memory.v3-term-materialization-prepared-retention";
pub const PER_WORKER_BYTES: u64 = 343_932_932;
const MAX_DESCRIPTOR_BYTES: u64 = 4 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScenarioSpec {
    pub id: &'static str,
    pub kind: &'static str,
}

pub const SCENARIOS: [ScenarioSpec; 7] = [
    ScenarioSpec {
        id: "shared-doubling",
        kind: "shared-doubling",
    },
    ScenarioSpec {
        id: "nonsharing-chain",
        kind: "nonsharing-chain",
    },
    ScenarioSpec {
        id: "repeated-declaration-roots",
        kind: "repeated-declaration-roots",
    },
    ScenarioSpec {
        id: "sparse-import",
        kind: "sparse-import",
    },
    ScenarioSpec {
        id: "import-diamond",
        kind: "import-diamond",
    },
    ScenarioSpec {
        id: "term-materialization-near-limit",
        kind: "near-limit-lifetime",
    },
    ScenarioSpec {
        id: "wide-term-materialization-package",
        kind: "wide-package-model",
    },
];

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TermCounters {
    pub root_requests: u64,
    pub unique_nodes: u64,
    pub selected_edges: u64,
    pub reused_child_arcs: u64,
    pub owned_root_handoffs: u64,
    pub leaf_root_clones: u64,
    pub compound_root_clones: u64,
    pub materialization_slots: u64,
    pub charged_bytes: u64,
    pub capacity_stops: u64,
    pub legacy_fallbacks: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseSpec {
    pub scenario_id: &'static str,
    pub case_id: String,
    pub requested_jobs: u64,
    pub accepted: bool,
    pub modeled_module_slots: u64,
    pub counters: TermCounters,
    pub kernel_logical_fuel: u64,
    pub effective_jobs: u64,
    pub reduction_reason: &'static str,
}

#[derive(Clone, Debug)]
pub struct PreparedMaterializer {
    pub cert: ModuleCert,
    pub declaration_indices: Vec<usize>,
    pub root_repetitions: u64,
}

#[derive(Clone, Debug)]
pub struct PreparedProductionCase {
    pub materializers: Vec<PreparedMaterializer>,
    pub admission_probe: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct ProductionCaseResult {
    pub materialized_observation: CertificateTermMaterializationObservation,
    pub materialized_planned_charged_bytes: u64,
    pub materialized_module_count: u64,
    pub materialized_certificate_hashes_sha256: String,
    pub admission_probe_observation: Option<CertificateTermMaterializationObservation>,
    pub kernel_logical_fuel: u64,
}

pub fn prepare_production_case(case: &CaseSpec) -> Result<PreparedProductionCase, String> {
    let (terms, root_repetitions) = match case.scenario_id {
        "shared-doubling" => {
            let height = parse_case_number(&case.case_id, "height-")?;
            (vec![doubling(height)?], 1)
        }
        "nonsharing-chain" => {
            let length = parse_case_number(&case.case_id, "length-")?;
            (vec![chain(length)?], 1)
        }
        "repeated-declaration-roots" => (vec![doubling(8)?; 4_096], 1),
        "sparse-import" => (vec![sparse_selected_root(64)?], 1),
        "import-diamond" => {
            let root = chain(4_096)?;
            (vec![root; 16], 1)
        }
        "term-materialization-near-limit" => (vec![doubling(8)?], 1),
        "wide-term-materialization-package" => {
            let _jobs = parse_case_number(&case.case_id, "jobs-")?;
            (vec![doubling(8)?], 1)
        }
        _ => return Err(format!("unknown production case: {}", case.scenario_id)),
    };
    let mut declarations = Vec::new();
    declarations.extend(
        terms
            .into_iter()
            .enumerate()
            .map(|(index, ty)| Decl::Axiom {
                name: format!("root_{index}"),
                universe_params: Vec::new(),
                ty,
            })
            .collect::<Vec<_>>(),
    );
    let declaration_indices = (0..declarations.len()).collect::<Vec<_>>();
    let materializer_count = if case.scenario_id == "wide-term-materialization-package" {
        16_u64
    } else {
        1_u64
    };
    let mut materializers =
        Vec::with_capacity(usize::try_from(materializer_count).map_err(display_error)?);
    for module_index in 0..materializer_count {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted(format!(
                    "Bench.Tdag.{}.{}.Module{module_index:02}",
                    pascal(case.scenario_id),
                    pascal(&case.case_id)
                )),
                declarations: declarations.clone(),
            },
            &[],
        )
        .map_err(|error| format!("certificate build failed: {error:?}"))?;
        materializers.push(PreparedMaterializer {
            cert,
            declaration_indices: declaration_indices.clone(),
            root_repetitions,
        });
    }
    Ok(PreparedProductionCase {
        materializers,
        admission_probe: if matches!(
            case.scenario_id,
            "term-materialization-near-limit" | "wide-term-materialization-package"
        ) {
            Some(if case.scenario_id == "term-materialization-near-limit" {
                parse_case_number(&case.case_id, "charge-")?
            } else {
                CHARGED_BYTE_LIMIT
            })
        } else {
            None
        },
    })
}

impl PreparedProductionCase {
    pub fn execute(&self) -> Result<ProductionCaseResult, String> {
        self.execute_inner(false).map(|(result, _)| result)
    }

    pub fn execute_measured(&self) -> Result<(ProductionCaseResult, u64), String> {
        self.execute_inner(true)
    }

    fn execute_inner(&self, measure_adapters: bool) -> Result<(ProductionCaseResult, u64), String> {
        let mut observation = CertificateTermMaterializationObservation::default();
        let mut planned_charged_bytes = 0_u64;
        let mut adapter_elapsed_ns = 0_u128;
        let mut hash_hasher = Sha256::new();
        hash_hasher.update(b"npa.certificate-term-dag-materialization.real-hashes.v0.1\0");
        for materializer in &self.materializers {
            let adapter_result = if measure_adapters {
                let started = Instant::now();
                let result = benchmark_term_materialization_plan_v1(
                    &materializer.cert,
                    &materializer.declaration_indices,
                    materializer.root_repetitions,
                );
                adapter_elapsed_ns =
                    adapter_elapsed_ns.saturating_add(started.elapsed().as_nanos());
                result
            } else {
                benchmark_term_materialization_plan_v1(
                    &materializer.cert,
                    &materializer.declaration_indices,
                    materializer.root_repetitions,
                )
            };
            let TermMaterializationBenchmarkResultV1 {
                observation: module_observation,
                planned_charged_bytes: module_charged_bytes,
                certificate_hash,
            } = adapter_result
                .map_err(|error| format!("production materialization failed: {error:?}"))?;
            observation.merge(module_observation);
            planned_charged_bytes = planned_charged_bytes
                .checked_add(module_charged_bytes)
                .ok_or("aggregate planned charge overflow")?;
            frame(&mut hash_hasher, &certificate_hash);
        }
        Ok((
            ProductionCaseResult {
                materialized_observation: observation,
                materialized_planned_charged_bytes: planned_charged_bytes,
                materialized_module_count: u64::try_from(self.materializers.len())
                    .unwrap_or(u64::MAX),
                materialized_certificate_hashes_sha256: hex(&hash_hasher.finalize()),
                admission_probe_observation: self
                    .admission_probe
                    .map(npa_cert::benchmark_term_materialization_admission_v1),
                kernel_logical_fuel: 0,
            },
            u64::try_from(adapter_elapsed_ns).unwrap_or(u64::MAX),
        ))
    }
}

pub fn validate_production_result(
    case: &CaseSpec,
    result: &ProductionCaseResult,
) -> Result<(), String> {
    let observation = &result.materialized_observation;
    let mut expected = case.counters;
    if case.scenario_id == "sparse-import" {
        expected.selected_edges = 2 * (expected.unique_nodes.saturating_sub(1));
        expected.reused_child_arcs = expected.selected_edges;
        expected.materialization_slots = expected.unique_nodes;
        expected.charged_bytes = result.materialized_planned_charged_bytes;
    } else if case.scenario_id == "import-diamond" {
        expected.unique_nodes = 4_096;
        expected.selected_edges = 2 * (expected.unique_nodes.saturating_sub(1));
        expected.reused_child_arcs = expected.selected_edges;
        expected.materialization_slots = expected.unique_nodes;
        expected.charged_bytes = result.materialized_planned_charged_bytes;
    } else if matches!(
        case.scenario_id,
        "wide-term-materialization-package" | "term-materialization-near-limit"
    ) {
        let multiplicity = if case.scenario_id == "wide-term-materialization-package" {
            16
        } else {
            1
        };
        expected.root_requests = multiplicity;
        expected.unique_nodes = 9 * multiplicity;
        expected.selected_edges = 16 * multiplicity;
        expected.reused_child_arcs = 16 * multiplicity;
        expected.owned_root_handoffs = multiplicity;
        expected.compound_root_clones = multiplicity;
        expected.materialization_slots = 9 * multiplicity;
        expected.charged_bytes = result.materialized_planned_charged_bytes;
        expected.capacity_stops = 0;
        expected.legacy_fallbacks = 0;
    } else {
        expected.charged_bytes = result.materialized_planned_charged_bytes;
    }
    let actual = TermCounters {
        root_requests: observation.root_requests,
        unique_nodes: observation.unique_nodes_materialized,
        selected_edges: observation.selected_edges,
        reused_child_arcs: observation.reused_child_arcs,
        owned_root_handoffs: observation.owned_root_handoffs,
        leaf_root_clones: observation.leaf_root_clones,
        compound_root_clones: observation.compound_root_clones,
        materialization_slots: observation.materialization_slots,
        charged_bytes: observation.materialization_charged_bytes,
        capacity_stops: observation.materialization_capacity_stops,
        legacy_fallbacks: observation.materialization_legacy_fallbacks,
    };
    if actual != expected {
        return Err(format!(
            "production materialization counters drift for {}/{}: expected {expected:?}, got {actual:?}",
            case.scenario_id, case.case_id
        ));
    }
    let expected_materialized_modules = if case.scenario_id == "wide-term-materialization-package" {
        16
    } else {
        1
    };
    if result.materialized_module_count != expected_materialized_modules
        || result.materialized_certificate_hashes_sha256.len() != 64
        || !result
            .materialized_certificate_hashes_sha256
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return Err("production certificate hash shape drift".to_owned());
    }
    let expected_hashes = expected_materialized_certificate_hashes_sha256(case)?;
    if result.materialized_certificate_hashes_sha256 != expected_hashes {
        return Err(format!(
            "production certificate hash identity drift for {}/{}: expected {expected_hashes}, got {}",
            case.scenario_id, case.case_id, result.materialized_certificate_hashes_sha256
        ));
    }
    match (case.scenario_id, result.admission_probe_observation) {
        ("term-materialization-near-limit", Some(probe)) => {
            let target = parse_case_number(&case.case_id, "charge-")?;
            let fallback = target > CHARGED_BYTE_LIMIT;
            if probe.materialization_charged_bytes != if fallback { 0 } else { target }
                || probe.materialization_capacity_stops != u64::from(fallback)
                || probe.materialization_legacy_fallbacks != u64::from(fallback)
            {
                return Err("production admission probe drift".to_owned());
            }
        }
        ("wide-term-materialization-package", Some(probe)) => {
            if probe.materialization_charged_bytes != CHARGED_BYTE_LIMIT
                || probe.materialization_capacity_stops != 0
                || probe.materialization_legacy_fallbacks != 0
            {
                return Err("wide production admission probe drift".to_owned());
            }
        }
        ("term-materialization-near-limit" | "wide-term-materialization-package", None) => {
            return Err("required production admission probe missing".to_owned())
        }
        (_, Some(_)) => return Err("unexpected production admission probe".to_owned()),
        (_, None) => {}
    }
    if result.kernel_logical_fuel != case.kernel_logical_fuel {
        return Err("kernel logical fuel drift".to_owned());
    }
    Ok(())
}

pub fn production_observation_json(case: &CaseSpec, result: &ProductionCaseResult) -> String {
    let observation = &result.materialized_observation;
    let counters = TermCounters {
        root_requests: observation.root_requests,
        unique_nodes: observation.unique_nodes_materialized,
        selected_edges: observation.selected_edges,
        reused_child_arcs: observation.reused_child_arcs,
        owned_root_handoffs: observation.owned_root_handoffs,
        leaf_root_clones: observation.leaf_root_clones,
        compound_root_clones: observation.compound_root_clones,
        materialization_slots: observation.materialization_slots,
        charged_bytes: observation.materialization_charged_bytes,
        capacity_stops: observation.materialization_capacity_stops,
        legacy_fallbacks: observation.materialization_legacy_fallbacks,
    };
    let admission_probe = result.admission_probe_observation.map_or_else(
        || "null".to_owned(),
        |probe| {
            format!(
                "{{\"charged_bytes\":{},\"capacity_stops\":{},\"legacy_fallbacks\":{}}}",
                probe.materialization_charged_bytes,
                probe.materialization_capacity_stops,
                probe.materialization_legacy_fallbacks
            )
        },
    );
    format!(
        "{{\"case_id\":\"{}\",\"requested_jobs\":{},\"accepted\":{},\"materialized_module_count\":{},\"materialized_certificate_hashes_sha256\":\"{}\",\"materialized_counters\":{},\"materialized_planned_charged_bytes\":{},\"admission_probe\":{},\"modeled_module_slots\":{},\"kernel_logical_fuel\":{},\"memory_model\":{}}}",
        case.case_id,
        case.requested_jobs,
        case.accepted,
        result.materialized_module_count,
        result.materialized_certificate_hashes_sha256,
        counters_json(counters),
        result.materialized_planned_charged_bytes,
        admission_probe,
        case.modeled_module_slots,
        result.kernel_logical_fuel,
        memory_model_json(case),
    )
}

pub fn expected_production_observation_json(case: &CaseSpec) -> Result<String, String> {
    let admission_probe = match case.scenario_id {
        "term-materialization-near-limit" => {
            let target = parse_case_number(&case.case_id, "charge-")?;
            let fallback = target > CHARGED_BYTE_LIMIT;
            format!(
                "{{\"charged_bytes\":{},\"capacity_stops\":{},\"legacy_fallbacks\":{}}}",
                if fallback { 0 } else { target },
                u64::from(fallback),
                u64::from(fallback),
            )
        }
        "wide-term-materialization-package" => format!(
            "{{\"charged_bytes\":{CHARGED_BYTE_LIMIT},\"capacity_stops\":0,\"legacy_fallbacks\":0}}"
        ),
        _ => "null".to_owned(),
    };
    Ok(format!(
        "{{\"case_id\":\"{}\",\"requested_jobs\":{},\"accepted\":{},\"materialized_module_count\":{},\"materialized_certificate_hashes_sha256\":\"{}\",\"materialized_counters\":{},\"materialized_planned_charged_bytes\":{},\"admission_probe\":{},\"modeled_module_slots\":{},\"kernel_logical_fuel\":{},\"memory_model\":{}}}",
        case.case_id,
        case.requested_jobs,
        case.accepted,
        expected_materialized_module_count(case),
        expected_materialized_certificate_hashes_sha256(case)?,
        counters_json(case.counters),
        case.counters.charged_bytes,
        admission_probe,
        case.modeled_module_slots,
        case.kernel_logical_fuel,
        memory_model_json(case),
    ))
}

fn doubling(height: u64) -> Result<Expr, String> {
    let mut expression = Expr::sort(Level::zero());
    for _ in 0..height {
        expression = Expr::pi("_", expression.clone(), expression);
    }
    Ok(expression)
}

fn chain(length: u64) -> Result<Expr, String> {
    if length == 0 {
        return Err("chain length must be positive".to_owned());
    }
    let zero = Expr::sort(Level::zero());
    let mut expression = zero.clone();
    for _ in 1..length {
        expression = Expr::pi("_", expression, zero.clone());
    }
    Ok(expression)
}

fn sparse_selected_root(selected_nodes: u64) -> Result<Expr, String> {
    chain(selected_nodes)
}

fn parse_case_number(case_id: &str, prefix: &str) -> Result<u64, String> {
    case_id
        .strip_prefix(prefix)
        .ok_or_else(|| format!("invalid case id: {case_id}"))?
        .parse()
        .map_err(display_error)
}

fn pascal(value: &str) -> String {
    value
        .split(['-', '_'])
        .filter(|part| !part.is_empty())
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(first) => format!("{}{}", first.to_ascii_uppercase(), chars.as_str()),
                None => String::new(),
            }
        })
        .collect()
}

pub fn cases() -> Vec<CaseSpec> {
    let mut result = Vec::with_capacity(18);
    for height in [8_u64, 12, 16, 18] {
        let unique = height + 1;
        result.push(CaseSpec {
            scenario_id: "shared-doubling",
            case_id: format!("height-{height}"),
            requested_jobs: 1,
            accepted: true,
            modeled_module_slots: 1,
            counters: TermCounters {
                root_requests: 1,
                unique_nodes: unique,
                selected_edges: 2 * height,
                reused_child_arcs: 2 * height,
                owned_root_handoffs: 1,
                compound_root_clones: 1,
                materialization_slots: unique,
                charged_bytes: 282 + 146 * height,
                ..TermCounters::default()
            },
            kernel_logical_fuel: 0,
            effective_jobs: 1,
            reduction_reason: "requested_one",
        });
    }
    for length in [256_u64, 2_048, 8_191] {
        result.push(CaseSpec {
            scenario_id: "nonsharing-chain",
            case_id: format!("length-{length}"),
            requested_jobs: 1,
            accepted: true,
            modeled_module_slots: 1,
            counters: TermCounters {
                root_requests: 1,
                unique_nodes: length,
                selected_edges: 2 * (length - 1),
                reused_child_arcs: 2 * (length - 1),
                owned_root_handoffs: 1,
                compound_root_clones: 1,
                materialization_slots: length,
                charged_bytes: 146 * length + 136,
                ..TermCounters::default()
            },
            kernel_logical_fuel: 0,
            effective_jobs: 1,
            reduction_reason: "requested_one",
        });
    }
    result.push(CaseSpec {
        scenario_id: "repeated-declaration-roots",
        case_id: "declarations-4096".to_owned(),
        requested_jobs: 1,
        accepted: true,
        modeled_module_slots: 1,
        counters: TermCounters {
            root_requests: 4_096,
            unique_nodes: 9,
            selected_edges: 16,
            reused_child_arcs: 16,
            owned_root_handoffs: 4_096,
            compound_root_clones: 4_096,
            materialization_slots: 9,
            charged_bytes: 300_385,
            ..TermCounters::default()
        },
        kernel_logical_fuel: 0,
        effective_jobs: 1,
        reduction_reason: "requested_one",
    });
    result.push(CaseSpec {
        scenario_id: "sparse-import",
        case_id: "selected-64".to_owned(),
        requested_jobs: 1,
        accepted: true,
        modeled_module_slots: 2,
        counters: TermCounters {
            root_requests: 1,
            unique_nodes: 64,
            selected_edges: 126,
            reused_child_arcs: 126,
            owned_root_handoffs: 1,
            compound_root_clones: 1,
            materialization_slots: 64,
            charged_bytes: 9_480,
            ..TermCounters::default()
        },
        kernel_logical_fuel: 0,
        effective_jobs: 1,
        reduction_reason: "requested_one",
    });
    result.push(CaseSpec {
        scenario_id: "import-diamond",
        case_id: "arms-8".to_owned(),
        requested_jobs: 1,
        accepted: true,
        modeled_module_slots: 10,
        counters: TermCounters {
            root_requests: 16,
            unique_nodes: 4_096,
            selected_edges: 8_190,
            reused_child_arcs: 8_190,
            owned_root_handoffs: 16,
            compound_root_clones: 16,
            materialization_slots: 4_096,
            charged_bytes: 599_247,
            ..TermCounters::default()
        },
        kernel_logical_fuel: 0,
        effective_jobs: 1,
        reduction_reason: "requested_one",
    });
    for target in [268_435_455_u64, 268_435_456, 268_435_457] {
        result.push(CaseSpec {
            scenario_id: "term-materialization-near-limit",
            case_id: format!("charge-{target}"),
            requested_jobs: 1,
            accepted: true,
            modeled_module_slots: 1,
            counters: TermCounters {
                root_requests: 1,
                unique_nodes: 9,
                selected_edges: 16,
                reused_child_arcs: 16,
                owned_root_handoffs: 1,
                compound_root_clones: 1,
                materialization_slots: 9,
                charged_bytes: 1_450,
                ..TermCounters::default()
            },
            kernel_logical_fuel: 0,
            effective_jobs: 1,
            reduction_reason: "requested_one",
        });
    }
    for jobs in [1_u64, 2, 3, 4, 16] {
        let effective = jobs.min(3);
        result.push(CaseSpec {
            scenario_id: "wide-term-materialization-package",
            case_id: format!("jobs-{jobs}"),
            requested_jobs: jobs,
            accepted: true,
            modeled_module_slots: 16,
            counters: TermCounters {
                root_requests: 16,
                unique_nodes: 144,
                selected_edges: 256,
                reused_child_arcs: 256,
                owned_root_handoffs: 16,
                compound_root_clones: 16,
                materialization_slots: 144,
                charged_bytes: 23_200,
                ..TermCounters::default()
            },
            kernel_logical_fuel: 0,
            effective_jobs: effective,
            reduction_reason: if jobs == 1 {
                "requested_one"
            } else if jobs <= 3 {
                "none"
            } else {
                "memory_budget"
            },
        });
    }
    assert_eq!(result.len(), 18);
    result
}

pub fn scenario(id: &str) -> Option<ScenarioSpec> {
    SCENARIOS.iter().copied().find(|scenario| scenario.id == id)
}

pub fn fixture_descriptor_json(scenario: ScenarioSpec) -> String {
    let case_ids = cases()
        .into_iter()
        .filter(|case| case.scenario_id == scenario.id)
        .map(|case| format!("\"{}\"", case.case_id))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"schema\":\"npa.certificate-term-dag-materialization.fixture.v0.1\",\"id\":\"{}\",\"kind\":\"{}\",\"artifact_kind\":\"runtime-generation-recipe\",\"production_adapter\":\"selected-plan-v1\",\"case_ids\":[{}],\"generator\":\"canonical-graph-v2\"}}\n",
        scenario.id, scenario.kind, case_ids,
    )
}

pub fn fixture_tree_hash_for_descriptor(scenario: ScenarioSpec) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"npa.certificate-term-dag-materialization.fixture-tree.v0.1\0");
    frame(&mut hasher, b"fixture.json");
    frame(&mut hasher, fixture_descriptor_json(scenario).as_bytes());
    hex(&hasher.finalize())
}

#[derive(Debug, PartialEq, Eq)]
struct CanonicalFixtureTree {
    directories: Vec<String>,
    files: Vec<(String, Vec<u8>)>,
}

impl CanonicalFixtureTree {
    fn hash(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(b"npa.certificate-term-dag-materialization.fixture-tree.v0.1\0");
        for (path, bytes) in &self.files {
            frame(&mut hasher, path.as_bytes());
            frame(&mut hasher, bytes);
        }
        hex(&hasher.finalize())
    }
}

fn canonical_fixture_tree(root: &Path) -> Result<CanonicalFixtureTree, String> {
    let snapshot = read_absolute_regular_tree(
        root,
        32,
        1024 * 1024,
        8 * 1024 * 1024,
        "term-DAG fixture tree",
    )?;
    let mut directories = snapshot
        .directories
        .into_iter()
        .filter(|path| !path.as_os_str().is_empty())
        .map(|path| normalized_utf8_relative_path(&path))
        .collect::<Result<Vec<_>, _>>()?;
    let mut files = snapshot
        .files
        .into_iter()
        .map(|(path, bytes)| Ok((normalized_utf8_relative_path(&path)?, bytes)))
        .collect::<Result<Vec<_>, String>>()?;
    directories.sort();
    files.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(CanonicalFixtureTree { directories, files })
}

pub fn normalized_utf8_relative_path(path: &Path) -> Result<String, String> {
    if path.is_absolute() || path.as_os_str().is_empty() {
        return Err("fixture tree path must be a nonempty relative path".to_owned());
    }
    let mut components = Vec::new();
    for component in path.components() {
        let Component::Normal(component) = component else {
            return Err(format!(
                "fixture tree path contains a non-normal component: {}",
                path.display()
            ));
        };
        components.push(
            component
                .to_str()
                .ok_or_else(|| format!("fixture tree path is not UTF-8: {}", path.display()))?
                .to_owned(),
        );
    }
    Ok(components.join("/"))
}

pub fn fixture_tree_hash(root: &Path) -> Result<String, String> {
    canonical_fixture_tree(root).map(|tree| tree.hash())
}

pub fn validate_scenario_fixture_root(root: &Path, scenario: ScenarioSpec) -> Result<(), String> {
    let tree = canonical_fixture_tree(root)?;
    if !tree.directories.is_empty() || tree.files.len() != 1 || tree.files[0].0 != "fixture.json" {
        return Err(format!(
            "fixture scenario root contains entries outside the closed catalog: {}",
            root.display()
        ));
    }
    if tree.files[0].1 != fixture_descriptor_json(scenario).as_bytes() {
        return Err(format!("fixture descriptor drift: {}", root.display()));
    }
    let expected_hash = fixture_tree_hash_for_descriptor(scenario);
    let actual_hash = tree.hash();
    if actual_hash != expected_hash {
        return Err(format!(
            "fixture tree hash mismatch for {}: expected {expected_hash}, got {actual_hash}",
            root.display()
        ));
    }
    Ok(())
}

pub fn validate_fixture_catalog_root(root: &Path) -> Result<(), String> {
    let snapshot = read_absolute_regular_tree(
        root,
        32,
        1024 * 1024,
        8 * 1024 * 1024,
        "term-DAG fixture catalog",
    )?;
    let mut actual_files = snapshot
        .files
        .keys()
        .map(|path| normalized_utf8_relative_path(path))
        .collect::<Result<Vec<_>, _>>()?;
    actual_files.sort();
    let mut expected_files = SCENARIOS
        .iter()
        .map(|scenario| format!("{}/fixture.json", scenario.id))
        .collect::<Vec<_>>();
    expected_files.sort();
    if actual_files != expected_files {
        return Err(format!(
            "fixture catalog files differ: expected {expected_files:?}, got {actual_files:?}"
        ));
    }
    let mut actual = snapshot
        .directories
        .into_iter()
        .filter(|path| !path.as_os_str().is_empty())
        .map(|path| normalized_utf8_relative_path(&path))
        .collect::<Result<Vec<_>, _>>()?;
    actual.sort();
    let mut expected = SCENARIOS
        .iter()
        .map(|scenario| scenario.id.to_owned())
        .collect::<Vec<_>>();
    expected.sort();
    if actual != expected {
        return Err(format!(
            "fixture catalog directories differ: expected {expected:?}, got {actual:?}"
        ));
    }
    Ok(())
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update(u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_be_bytes());
    hasher.update(bytes);
}

pub fn render_manifest() -> Result<String, String> {
    let rows = SCENARIOS
        .iter()
        .map(|scenario| manifest_row(*scenario))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!(
        "{{\n  \"schema\": \"{MANIFEST_SCHEMA}\",\n  \"budget_policy\": \"{BUDGET_POLICY}\",\n  \"charged_byte_limit\": {CHARGED_BYTE_LIMIT},\n  \"expr_inline_charge_bytes\": {EXPR_INLINE_BYTES},\n  \"arc_node_metadata_charge_bytes\": {ARC_NODE_METADATA_BYTES},\n  \"arc_layout_allowance_bytes\": {ARC_LAYOUT_ALLOWANCE_BYTES},\n  \"option_arc_slot_charge_bytes\": {OPTION_ARC_SLOT_BYTES},\n  \"term_id_slot_charge_bytes\": {TERM_ID_SLOT_BYTES},\n  \"selection_slot_charge_bytes\": {SELECTION_SLOT_BYTES},\n  \"level_node_charge_bytes\": {LEVEL_NODE_BYTES},\n  \"planner_record_charge_bytes\": {PLANNER_RECORD_BYTES},\n  \"scenarios\": [\n    {}\n  ]\n}}\n",
        rows.join(",\n    ")
    ))
}

fn manifest_row(scenario: ScenarioSpec) -> Result<String, String> {
    let common = format!(
        "\"id\":\"{}\",\"kind\":\"{}\",\"fixture_root\":\"{FIXTURE_ROOT}/{}\",\"fixture_tree_sha256\":\"{}\",\"verifier\":\"fast\",\"package_lock\":\"checked\",\"decode_cache\":\"off\",\"verifier_memo\":\"off\",\"measurement_mode\":\"detailed\",\"warmup\":1,\"samples\":3,",
        scenario.id, scenario.kind, scenario.id, fixture_tree_hash_for_descriptor(scenario),
    );
    let specific = match scenario.id {
        "shared-doubling" => "\"requested_jobs\":[1],\"process_rss_required\":true,\"baseline_key\":\"shared-doubling\",\"heights\":[8,12,16,18]",
        "nonsharing-chain" => "\"requested_jobs\":[1],\"process_rss_required\":true,\"baseline_key\":\"nonsharing-chain\",\"lengths\":[256,2048,8191]",
        "repeated-declaration-roots" => "\"requested_jobs\":[1],\"process_rss_required\":true,\"baseline_key\":\"repeated-declaration-roots\",\"declaration_count\":4096,\"shared_dag_height\":8",
        "sparse-import" => "\"requested_jobs\":[1],\"process_rss_required\":true,\"baseline_key\":\"sparse-import\",\"evidence_scope\":\"selected-plan-microfixture-only\",\"modeled_provider_term_nodes\":262144,\"materialized_selected_nodes\":64,\"materialized_table_slots\":64",
        "import-diamond" => "\"requested_jobs\":[1],\"process_rss_required\":true,\"baseline_key\":\"import-diamond\",\"evidence_scope\":\"shared-roots-microfixture-only\",\"modeled_diamond_arms\":8,\"modeled_module_slots\":10,\"materialized_selected_nodes\":4096",
        "term-materialization-near-limit" => "\"requested_jobs\":[1],\"process_rss_required\":true,\"baseline_key\":\"term-materialization-near-limit\",\"materialized_fixture_charge_bytes\":1450,\"admission_probe_charge_targets_bytes\":[268435455,268435456,268435457]",
        "wide-term-materialization-package" => "\"requested_jobs\":[1,2,3,4,16],\"process_rss_required\":true,\"baseline_key\":\"wide-term-materialization-package\",\"materialized_module_count\":16,\"materialized_per_module_charge_bytes\":1450,\"admission_probe_per_module_charge_bytes\":268435456,\"model_case\":\"active-guarded\"",
        other => return Err(format!("unknown closed TDAG scenario {other}")),
    };
    Ok(format!("{{{common}{specific}}}"))
}

pub fn render_baseline() -> Result<String, String> {
    let rows = SCENARIOS
        .iter()
        .map(|scenario| baseline_row(*scenario))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!(
        "{{\n  \"schema\": \"{BASELINE_SCHEMA}\",\n  \"measurement_schema\": \"{MEASUREMENT_SCHEMA}\",\n  \"budget_policy\": \"{BUDGET_POLICY}\",\n  \"charged_byte_limit\": {CHARGED_BYTE_LIMIT},\n  \"expr_inline_charge_bytes\": {EXPR_INLINE_BYTES},\n  \"arc_node_metadata_charge_bytes\": {ARC_NODE_METADATA_BYTES},\n  \"arc_layout_allowance_bytes\": {ARC_LAYOUT_ALLOWANCE_BYTES},\n  \"option_arc_slot_charge_bytes\": {OPTION_ARC_SLOT_BYTES},\n  \"term_id_slot_charge_bytes\": {TERM_ID_SLOT_BYTES},\n  \"selection_slot_charge_bytes\": {SELECTION_SLOT_BYTES},\n  \"level_node_charge_bytes\": {LEVEL_NODE_BYTES},\n  \"planner_record_charge_bytes\": {PLANNER_RECORD_BYTES},\n  \"scenarios\": [\n    {}\n  ],\n  \"update_policy\": \"reviewed-manual-only\"\n}}\n",
        rows.join(",\n    ")
    ))
}

fn baseline_row(scenario: ScenarioSpec) -> Result<String, String> {
    let observations = cases()
        .into_iter()
        .filter(|case| case.scenario_id == scenario.id)
        .map(|case| observation_json(&case))
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    let decision = if scenario.id == "sparse-import" {
        ",\"decision\":\"NotSelectedImportPerformanceEvidence\""
    } else {
        ""
    };
    Ok(format!(
        "{{\"key\":\"{}\",\"scenario_id\":\"{}\",\"fixture_tree_sha256\":\"{}\",\"status\":\"passed\",\"observations\":[{}],\"fixture_oracle\":{}{} }}",
        scenario.id,
        scenario.id,
        fixture_tree_hash_for_descriptor(scenario),
        observations,
        fixture_oracle_json(scenario)?,
        decision,
    ).replace("} }", "}}"))
}

pub fn observation_json(case: &CaseSpec) -> Result<String, String> {
    Ok(format!(
        "{{\"case_id\":\"{}\",\"requested_jobs\":{},\"accepted\":{},\"fixture_identity_sha256\":\"{}\",\"materialized_module_count\":{},\"materialized_certificate_hashes_sha256\":\"{}\",\"materialized_expected_counters\":{},\"materialized_planned_charged_bytes\":{},\"admission_probe_expected\":{},\"modeled_module_slots\":{},\"kernel_logical_fuel\":{},\"memory_model\":{}}}",
        case.case_id,
        case.requested_jobs,
        case.accepted,
        case_module_hash(case),
        expected_materialized_module_count(case),
        expected_materialized_certificate_hashes_sha256(case)?,
        counters_json(case.counters),
        case.counters.charged_bytes,
        admission_probe_expected_json(case)?,
        case.modeled_module_slots,
        case.kernel_logical_fuel,
        memory_model_json(case),
    ))
}

pub fn deterministic_observation_json(case: &CaseSpec) -> Result<String, String> {
    observation_json(case)
}

fn counters_json(counters: TermCounters) -> String {
    format!(
        "{{\"certificate.term_root_requests\":{},\"certificate.term_unique_nodes_materialized\":{},\"certificate.term_selected_edges\":{},\"certificate.term_reused_child_arcs\":{},\"certificate.term_owned_root_handoffs\":{},\"certificate.term_leaf_root_clones\":{},\"certificate.term_compound_root_clones\":{},\"certificate.term_materialization_slots\":{},\"certificate.term_materialization_charged_bytes\":{},\"certificate.term_materialization_capacity_stops\":{},\"certificate.term_materialization_legacy_fallbacks\":{}}}",
        counters.root_requests,
        counters.unique_nodes,
        counters.selected_edges,
        counters.reused_child_arcs,
        counters.owned_root_handoffs,
        counters.leaf_root_clones,
        counters.compound_root_clones,
        counters.materialization_slots,
        counters.charged_bytes,
        counters.capacity_stops,
        counters.legacy_fallbacks,
    )
}

fn memory_model_json(case: &CaseSpec) -> String {
    format!(
        "{{\"identifier\":\"{MEMORY_MODEL}\",\"per_worker_bytes\":{PER_WORKER_BYTES},\"prepared_shared_bytes\":0,\"shared_planner_bytes\":0,\"requested_jobs\":{},\"effective_jobs\":{},\"reduction_reason\":\"{}\",\"overflowed\":false}}",
        case.requested_jobs, case.effective_jobs, case.reduction_reason,
    )
}

fn fixture_oracle_json(scenario: ScenarioSpec) -> Result<String, String> {
    Ok(match scenario.id {
        "shared-doubling" => "{\"kind\":\"shared-doubling\",\"cases\":[{\"height\":8,\"unique_nodes\":9,\"selected_edges\":16,\"root_requests\":1,\"unfolded_term_occurrences\":511,\"root_structural_expansion\":767},{\"height\":12,\"unique_nodes\":13,\"selected_edges\":24,\"root_requests\":1,\"unfolded_term_occurrences\":8191,\"root_structural_expansion\":12287},{\"height\":16,\"unique_nodes\":17,\"selected_edges\":32,\"root_requests\":1,\"unfolded_term_occurrences\":131071,\"root_structural_expansion\":196607},{\"height\":18,\"unique_nodes\":19,\"selected_edges\":36,\"root_requests\":1,\"unfolded_term_occurrences\":524287,\"root_structural_expansion\":786431}]}".to_owned(),
        "nonsharing-chain" => "{\"kind\":\"nonsharing-chain\",\"cases\":[{\"length\":256,\"unique_nodes\":256,\"selected_edges\":510,\"root_requests\":1,\"unfolded_term_occurrences\":511,\"root_structural_expansion\":767,\"combined_depth\":257},{\"length\":2048,\"unique_nodes\":2048,\"selected_edges\":4094,\"root_requests\":1,\"unfolded_term_occurrences\":4095,\"root_structural_expansion\":6143,\"combined_depth\":2049},{\"length\":8191,\"unique_nodes\":8191,\"selected_edges\":16380,\"root_requests\":1,\"unfolded_term_occurrences\":16381,\"root_structural_expansion\":24572,\"combined_depth\":8192}]}".to_owned(),
        "repeated-declaration-roots" => "{\"kind\":\"repeated-declaration-roots\",\"declarations\":4096,\"unique_nodes\":9,\"selected_edges\":16,\"root_requests\":4096,\"quick_equality_checks\":4095,\"physical_reductions\":0}".to_owned(),
        "sparse-import" => "{\"kind\":\"sparse-import\",\"evidence_scope\":\"selected-plan-microfixture-only\",\"selected_import_execution\":\"not-measured\",\"modeled_provider_table_nodes\":262144,\"materialized_selected_nodes\":64,\"materialized_selected_edges\":126,\"materialized_table_slots\":64,\"unselected_expr_allocations\":0}".to_owned(),
        "import-diamond" => "{\"kind\":\"import-diamond\",\"evidence_scope\":\"shared-roots-microfixture-only\",\"import_graph_execution\":\"not-measured\",\"modeled_diamond_arms\":8,\"modeled_module_slots\":10,\"materialized_module_count\":1,\"materialized_selected_nodes\":4096,\"materialized_selected_edges\":8190,\"materialized_root_requests\":16}".to_owned(),
        "term-materialization-near-limit" => "{\"kind\":\"near-limit-lifetime\",\"materialized_fixture_charge_bytes\":1450,\"admission_probe_cases\":[{\"candidate_charged_bytes\":268435455,\"expected_lane\":\"forward\",\"capacity_stops\":0,\"legacy_fallbacks\":0},{\"candidate_charged_bytes\":268435456,\"expected_lane\":\"forward\",\"capacity_stops\":0,\"legacy_fallbacks\":0},{\"candidate_charged_bytes\":268435457,\"expected_lane\":\"legacy\",\"capacity_stops\":1,\"legacy_fallbacks\":1}]}".to_owned(),
        "wide-term-materialization-package" => "{\"kind\":\"wide-package-model\",\"runnable_width\":16,\"materialized_module_count\":16,\"materialized_per_module_charge_bytes\":1450,\"admission_probe_per_module_charge_bytes\":268435456}".to_owned(),
        other => return Err(format!("unknown closed TDAG scenario {other}")),
    })
}

fn expected_materialized_module_count(case: &CaseSpec) -> u64 {
    if case.scenario_id == "wide-term-materialization-package" {
        16
    } else {
        1
    }
}

fn admission_probe_expected_json(case: &CaseSpec) -> Result<String, String> {
    let candidate = match case.scenario_id {
        "term-materialization-near-limit" => Some(parse_case_number(&case.case_id, "charge-")?),
        "wide-term-materialization-package" => Some(CHARGED_BYTE_LIMIT),
        _ => None,
    };
    Ok(candidate.map_or_else(
        || "null".to_owned(),
        |candidate| {
            let fallback = candidate > CHARGED_BYTE_LIMIT;
            format!(
                "{{\"candidate_charged_bytes\":{candidate},\"charged_bytes\":{},\"capacity_stops\":{},\"legacy_fallbacks\":{}}}",
                if fallback { 0 } else { candidate },
                u64::from(fallback),
                u64::from(fallback),
            )
        },
    ))
}

fn expected_materialized_certificate_hashes_sha256(
    case: &CaseSpec,
) -> Result<&'static str, String> {
    Ok(match (case.scenario_id, case.case_id.as_str()) {
        ("shared-doubling", "height-8") => {
            "0af3ae84f9767351291e21836efd38d21eae88c70b3e5d836e669eda4163f9a1"
        }
        ("shared-doubling", "height-12") => {
            "eba903e6e69032150c0455e01ca3384e06f8f02c38276514e294d59b74d55a82"
        }
        ("shared-doubling", "height-16") => {
            "a8a9fc642865c86dd8ba99ebd294b08ec0d3f1b3ba83dedaeb2e0b997f8b702e"
        }
        ("shared-doubling", "height-18") => {
            "1f862a66765ae996bbb76b8f530c7711eab87ea1b0315ed18623cd24f74d7313"
        }
        ("nonsharing-chain", "length-256") => {
            "302d5051694b8a3ff145bb490eaf66ea9333ca191dd4a173942101cf41e5c6be"
        }
        ("nonsharing-chain", "length-2048") => {
            "e23190aa1e5f4c054bc1a3e2c342d8ffe11ccd80c72760fb2708ae9a6413ebde"
        }
        ("nonsharing-chain", "length-8191") => {
            "c28df7b826e6b1f570fa7102142d082239d4c6b56d7c13aa1f5c8232ffabcb71"
        }
        ("repeated-declaration-roots", "declarations-4096") => {
            "b0e9da03acd840cc58df7c7bdb178644d69bd4073e3678cee14285ae5a04e1c8"
        }
        ("sparse-import", "selected-64") => {
            "770d2a49785d1dbf5097d7d41530b3b83a6a0c8f6ec735cc50e37e4cd619b4aa"
        }
        ("import-diamond", "arms-8") => {
            "e852304c240196829c3232ab6e4a27c82f33eb9cb04d33d9b2a2cc798ab07017"
        }
        ("term-materialization-near-limit", "charge-268435455") => {
            "2a705bdc310e8aef37fc6bcc5e3a4e061201d7a7ad87d024dd6cbb135b54f4a7"
        }
        ("term-materialization-near-limit", "charge-268435456") => {
            "82d55c4c27d66e71dfc3009e84297a7d9b37d90abb0126f92d75e127ce2011a6"
        }
        ("term-materialization-near-limit", "charge-268435457") => {
            "8b465398e7cd400475d603280f61d0abb9541a917d1710696e304a9bbd30d675"
        }
        ("wide-term-materialization-package", "jobs-1") => {
            "377e70c6eaf910cc4bf7c838a5597cdafd1a6a522352c43e04df5729167e1287"
        }
        ("wide-term-materialization-package", "jobs-2") => {
            "74ecbf952135c2fafc882500d5e47fd538777498eb6ebbb400acb1a2d4cff7b1"
        }
        ("wide-term-materialization-package", "jobs-3") => {
            "f9eeb47f3d624ee71c3a023e70875329ab2fc6abdeea21a0efa45b7010360129"
        }
        ("wide-term-materialization-package", "jobs-4") => {
            "68773b9553fa48764bc7ef1a740de23003d2ba593c56631f69d62f6563af0879"
        }
        ("wide-term-materialization-package", "jobs-16") => {
            "0d9680731637dd2ea765e5b5f76d5845c73083390c156120fe162075336cc7c7"
        }
        (scenario, case_id) => {
            return Err(format!("unknown closed TDAG case {scenario}/{case_id}"))
        }
    })
}

fn case_module_hash(case: &CaseSpec) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"npa.certificate-term-dag-materialization.production-fixture.v0.1\0");
    hasher.update(case.scenario_id.as_bytes());
    hasher.update([0]);
    hasher.update(case.case_id.as_bytes());
    hex(&hasher.finalize())
}

pub fn validate_manifest(source: &str) -> Result<(), String> {
    JsonDocument::parse(source)
        .map_err(|error| format!("invalid manifest JSON at byte {}", error.offset))?;
    if source != render_manifest()? {
        return Err("manifest is not the exact closed canonical catalog".to_owned());
    }
    Ok(())
}

pub fn validate_baseline(source: &str) -> Result<(), String> {
    JsonDocument::parse(source)
        .map_err(|error| format!("invalid baseline JSON at byte {}", error.offset))?;
    if source != render_baseline()? {
        return Err("baseline is not the exact closed canonical catalog".to_owned());
    }
    Ok(())
}

pub fn validate_artifacts(workspace: &Path) -> Result<(), String> {
    let workspace = workspace.canonicalize().map_err(display_error)?;
    let manifest = String::from_utf8(read_absolute_regular_file(
        &workspace.join(MANIFEST_PATH),
        MAX_DESCRIPTOR_BYTES,
        "term-DAG manifest",
    )?)
    .map_err(display_error)?;
    validate_manifest(&manifest)?;
    let baseline = String::from_utf8(read_absolute_regular_file(
        &workspace.join(BASELINE_PATH),
        MAX_DESCRIPTOR_BYTES,
        "term-DAG baseline",
    )?)
    .map_err(display_error)?;
    validate_baseline(&baseline)?;
    validate_fixture_catalog_root(&workspace.join(FIXTURE_ROOT))?;
    for scenario in SCENARIOS {
        let root = workspace.join(FIXTURE_ROOT).join(scenario.id);
        validate_scenario_fixture_root(&root, scenario)?;
    }
    Ok(())
}

pub fn generate_fixture_roots(output: &Path, selected: Option<&str>) -> Result<(), String> {
    validate_output_path(output)?;
    let output = ClosedPrivateDirectory::open_existing(output, "npa-tdag-fixtures")?;
    let selected_spec = selected
        .map(|id| scenario(id).ok_or_else(|| format!("unknown scenario: {id}")))
        .transpose()?;
    for scenario in SCENARIOS {
        if selected_spec.is_some_and(|selected| selected != scenario) {
            continue;
        }
        let directory = Path::new(scenario.id);
        output.create_directory(directory)?;
        output.create_new_file(
            &directory.join("fixture.json"),
            fixture_descriptor_json(scenario).as_bytes(),
        )?;
    }
    Ok(())
}

/// Remove the complete generated fixture catalog and its private root through
/// retained identities.
///
/// Cleanup deliberately accepts only the full seven-scenario catalog. Each
/// descriptor must still contain the exact deterministic bytes before its
/// directory is removed through the retained root descriptor.
pub fn clean_fixture_roots(output: &Path) -> Result<(), String> {
    validate_output_path(output)?;
    let output = ClosedPrivateDirectory::open_existing(output, "npa-tdag-fixtures")?;
    let expected_files = SCENARIOS
        .iter()
        .map(|scenario| PathBuf::from(scenario.id).join("fixture.json"))
        .collect::<BTreeSet<_>>();
    let expected_directories = SCENARIOS
        .iter()
        .map(|scenario| PathBuf::from(scenario.id))
        .collect::<BTreeSet<_>>();
    let (actual_files, actual_directories) = output.catalog_root_paths()?;
    if actual_files != expected_files || actual_directories != expected_directories {
        return Err("generated fixture root differs from the exact cleanup catalog".to_owned());
    }
    for scenario in SCENARIOS {
        let fixture = PathBuf::from(scenario.id).join("fixture.json");
        let expected = fixture_descriptor_json(scenario);
        if output.read_regular_file(&fixture, MAX_DESCRIPTOR_BYTES)? != expected.as_bytes() {
            return Err(format!(
                "generated fixture descriptor changed before cleanup: {}",
                scenario.id
            ));
        }
    }
    for scenario in SCENARIOS {
        let directory = PathBuf::from(scenario.id);
        let fixture = directory.join("fixture.json");
        output.remove_exact_file(&fixture, fixture_descriptor_json(scenario).as_bytes())?;
        output.remove_exact_subtree(
            &directory,
            &BTreeSet::new(),
            &BTreeSet::from([directory.clone()]),
        )?;
    }
    output.remove_allowed_contents(&BTreeSet::new())?;
    output.remove_empty_root()
}

fn validate_output_path(output: &Path) -> Result<(), String> {
    if output.as_os_str().is_empty() || output == Path::new(".") || output == Path::new("..") {
        return Err("output must be an explicit non-root directory".to_owned());
    }
    if output.is_absolute() && output.parent().is_none() {
        return Err("filesystem root is not an output directory".to_owned());
    }
    if output
        .components()
        .any(|component| matches!(component, Component::ParentDir))
    {
        return Err("output must not contain '..'".to_owned());
    }
    Ok(())
}

pub fn compare_fixture_roots(expected: &Path, actual: &Path) -> Result<(), String> {
    validate_fixture_catalog_root(expected)?;
    validate_fixture_catalog_root(actual)?;
    for scenario in SCENARIOS {
        let relative = PathBuf::from(scenario.id);
        let expected_tree = canonical_fixture_tree(&expected.join(&relative))?;
        let actual_tree = canonical_fixture_tree(&actual.join(&relative))?;
        if expected_tree != actual_tree {
            return Err(format!(
                "fixture regeneration mismatch: {}",
                relative.display()
            ));
        }
    }
    Ok(())
}

pub fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push(char::from(DIGITS[usize::from(byte >> 4)]));
        result.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    result
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}
