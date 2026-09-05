//! Direct checked-package traversal for the application-spine WHNF benchmark.
//!
//! This example deliberately bypasses the package-verifier orchestration
//! layer. It validates the checked lock, traverses it in dependency order, and
//! invokes the public certificate/kernel boundary with explicit memo options.

#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use npa_api::{JsonDocument, JsonMember, JsonValue, JsonValueKind};
use npa_cert::{
    verify_module_cert_with_import_refs_and_kernel_options_and_work_counters, AxiomPolicy, Name,
    VerifiedModule,
};
use npa_kernel::{KernelExecutionOptions, KernelWorkCounters};
use npa_package::{
    build_package_lock_graph, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_package_lock_json,
    validate_package_lock_against_manifest_graph, PackageHash, PackageLockEntry,
    PackageLockManifest,
};

use closed_private_tree::read_invocation_regular_file;

const MAX_JSON_INPUT_BYTES: u64 = 16 * 1024 * 1024;
const MAX_CERTIFICATE_BYTES: u64 = 512 * 1024 * 1024;

const FIXTURE_SCHEMA: &str = "npa.kernel-whnf-application-spine.fixtures.v0.1";
const BASELINE_SCHEMA: &str = "npa.kernel-whnf-application-spine.measurements.v0.2";
const PACKAGE_CHILD_SCHEMA: &str = "npa.kernel-whnf-application-spine.package-child.v0.2";
const PACKAGE_COMPARE_SCHEMA: &str = "npa.kernel-whnf-application-spine.package-compare.v0.2";
const PACKAGE_IDS: [&str; 3] = [
    "checked-package.off",
    "checked-package.ephemeral",
    "checked-package.compare",
];
const WIDTHS: [u64; 5] = [32, 128, 512, 2_048, 8_192];
const MODES: [&str; 3] = ["memo-off", "repetition-probe", "ephemeral"];
const MICRO_KINDS: [&str; 6] = [
    "opaque-neutral-head",
    "partial-recursor",
    "saturated-neutral-major",
    "matching-constructor",
    "delta-exposed-long-spine",
    "retained-function-ephemeral-defeq",
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

fn main() {
    if let Err(error) = run(std::env::args().skip(1).collect()) {
        eprintln!("WHNF package harness: {error}");
        std::process::exit(2);
    }
}

fn run(arguments: Vec<String>) -> Result<(), String> {
    if arguments == ["--help"] || arguments == ["-h"] {
        println!("{}", usage());
        return Ok(());
    }
    let args = Args::parse_from(arguments)?;
    reject_recursive_phase_on_post_switch_binary(&args.phase)
        .map_err(|error| format!("invalid benchmark phase: {error}"))?;
    let fixture_source = read_utf8(&args.fixture_manifest, "fixture manifest")?;
    validate_fixture_manifest(&fixture_source)
        .map_err(|error| format!("invalid fixture manifest: {error}"))?;
    let baseline_source = read_utf8(&args.baseline, "deterministic baseline")?;
    validate_baseline_schema(&baseline_source)
        .map_err(|error| format!("invalid deterministic baseline: {error}"))?;
    validate_baseline_fixture_hash(
        &baseline_source,
        &raw_hash(package_file_hash(fixture_source.as_bytes()))?,
    )
    .map_err(|error| format!("deterministic baseline identity mismatch: {error}"))?;
    let inputs = PackageInputs::load(&args.root)?;

    match args.kernel_mode.as_str() {
        "off" | "ephemeral" => {
            let mode = args.kernel_mode.as_str();
            let scenario_id = format!("checked-package.{mode}");
            if fixture_source
                .matches(&format!("\"id\": \"{scenario_id}\""))
                .count()
                != 1
            {
                return Err(format!(
                    "fixture must contain exactly one {scenario_id} row"
                ));
            }
            let warmup = traverse(&inputs, mode)?;
            if !warmup.accepted {
                return Err("package warmup was not accepted".to_owned());
            }
            let started = Instant::now();
            let result = traverse(&inputs, mode)?;
            let elapsed_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
            validate_baseline_row(&baseline_source, &result)?;
            println!(
                "{{\"schema\":\"{PACKAGE_CHILD_SCHEMA}\",\"phase\":\"{}\",\"scenario_id\":\"{}\",\"sample_index\":{},\"kernel_mode\":\"{}\",\"operation_elapsed_ns\":{},\"accepted\":{},\"module_order\":{},\"verified_modules\":{},\"input_certificate_hashes\":{},\"aggregate_work\":{}}}",
                args.phase,
                scenario_id,
                args.sample_index,
                mode,
                elapsed_ns,
                result.accepted,
                string_array_json(&result.module_order),
                verified_modules_json(&result.verified_modules),
                input_hashes_json(&result.input_certificate_hashes),
                work_json(&result.aggregate_work),
            );
        }
        "compare" => {
            if args.child {
                return Err("compare is not a child timing series".to_owned());
            }
            let off = traverse(&inputs, "off")?;
            let ephemeral = traverse(&inputs, "ephemeral")?;
            validate_baseline_row(&baseline_source, &off)?;
            validate_baseline_row(&baseline_source, &ephemeral)?;
            if off.accepted != ephemeral.accepted
                || off.module_order != ephemeral.module_order
                || off.verified_modules != ephemeral.verified_modules
                || off.input_certificate_hashes != ephemeral.input_certificate_hashes
            {
                return Err("off/ephemeral accepted package identities differ".to_owned());
            }
            println!(
                "{{\"schema\":\"{PACKAGE_COMPARE_SCHEMA}\",\"accepted\":true,\"module_order\":{},\"verified_modules\":{},\"input_certificate_hashes\":{},\"off_aggregate_work\":{},\"ephemeral_aggregate_work\":{}}}",
                string_array_json(&off.module_order),
                verified_modules_json(&off.verified_modules),
                input_hashes_json(&off.input_certificate_hashes),
                work_json(&off.aggregate_work),
                work_json(&ephemeral.aggregate_work),
            );
        }
        mode => return Err(format!("unsupported package kernel mode: {mode}")),
    }
    Ok(())
}

fn reject_recursive_phase_on_post_switch_binary(phase: &str) -> Result<(), &'static str> {
    if phase == "recursive" {
        Err(
            "this package harness is built from the post-switch WHNF machine; use the archived pre-switch executable for recursive evidence",
        )
    } else {
        Ok(())
    }
}

struct PackageInputs {
    lock: PackageLockManifest,
    graph: npa_package::PackageLockGraph,
    policy: AxiomPolicy,
    bytes: BTreeMap<Name, Vec<u8>>,
}

impl PackageInputs {
    fn load(root: &Path) -> Result<Self, String> {
        let manifest_source = read_utf8(&root.join("npa-package.toml"), "package manifest")?;
        let validated = parse_and_validate_manifest_str(&manifest_source)
            .map_err(|error| format!("invalid package manifest: {error}"))?;
        if validated.manifest().policy.allow_custom_axioms {
            return Err("benchmark package must use the closed high-trust axiom policy".to_owned());
        }
        let lock_source = read_utf8(
            &root.join("generated/package-lock.json"),
            "checked package lock",
        )?;
        let lock = parse_package_lock_json(&lock_source)
            .map_err(|error| format!("invalid checked package lock: {error}"))?;
        validate_package_lock_against_manifest_graph(&validated, &lock)
            .map_err(|error| format!("checked lock does not match package manifest: {error}"))?;
        let graph = build_package_lock_graph(&lock)
            .map_err(|error| format!("invalid checked lock graph: {error}"))?;
        let mut policy = AxiomPolicy::high_trust();
        policy
            .allowlisted_axioms
            .extend(validated.manifest().policy.allowed_axioms.iter().cloned());
        let bytes = lock
            .entries
            .iter()
            .map(|entry| {
                let label = format!("locked certificate {}", entry.module.as_dotted());
                let bytes = read_invocation_regular_file(
                    &root.join(entry.certificate.as_str()),
                    MAX_CERTIFICATE_BYTES,
                    &label,
                )?;
                if package_file_hash(&bytes) != entry.certificate_file_hash {
                    return Err(format!("{label} file hash mismatch"));
                }
                Ok((entry.module.clone(), bytes))
            })
            .collect::<Result<BTreeMap<_, _>, String>>()?;
        Ok(Self {
            lock,
            graph,
            policy,
            bytes,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VerifiedEvidence {
    lock_name: String,
    module: String,
    export_hash: String,
    certificate_hash: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct InputHash {
    lock_name: String,
    sha256: String,
}

struct Traversal {
    scenario_id: String,
    accepted: bool,
    module_order: Vec<String>,
    verified_modules: Vec<VerifiedEvidence>,
    input_certificate_hashes: Vec<InputHash>,
    aggregate_work: KernelWorkCounters,
}

fn traverse(inputs: &PackageInputs, mode: &str) -> Result<Traversal, String> {
    let options = match mode {
        "off" => KernelExecutionOptions::memo_off(),
        "ephemeral" => KernelExecutionOptions::ephemeral_memo(),
        _ => return Err(format!("unsupported package kernel mode: {mode}")),
    };
    let entries_by_module = inputs
        .lock
        .entries
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.module.clone(), (index, entry)))
        .collect::<BTreeMap<_, _>>();
    let mut verified = BTreeMap::<Name, VerifiedModule>::new();
    let mut verified_modules = Vec::new();
    let mut input_certificate_hashes = Vec::new();
    let mut aggregate_work = KernelWorkCounters::default();

    for module in &inputs.graph.topological_order {
        let (entry_index, entry) = entries_by_module
            .get(module)
            .copied()
            .ok_or_else(|| format!("lock graph contains unknown module {}", module.as_dotted()))?;
        let bytes = inputs
            .bytes
            .get(module)
            .ok_or_else(|| format!("certificate bytes missing for {}", module.as_dotted()))?;
        let mut work = KernelWorkCounters::default();
        let checked = {
            let import_refs = inputs.graph.resolved_entry_imports[entry_index]
                .iter()
                .map(|import| {
                    verified.get(&import.module).ok_or_else(|| {
                        format!(
                            "dependency-first traversal has not verified import {}",
                            import.module.as_dotted()
                        )
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
                bytes,
                &import_refs,
                &inputs.policy,
                options,
                &mut work,
            )
            .map_err(|error| {
                format!(
                    "locked certificate {} failed direct verification: {error:?}",
                    module.as_dotted()
                )
            })?
        };
        validate_verified_identity(entry, &checked)?;
        aggregate_work.merge(work);
        verified_modules.push(VerifiedEvidence {
            lock_name: module.as_dotted(),
            module: checked.module().as_dotted(),
            export_hash: raw_hash(PackageHash::from(checked.export_hash()))?,
            certificate_hash: raw_hash(PackageHash::from(checked.certificate_hash()))?,
        });
        input_certificate_hashes.push(InputHash {
            lock_name: module.as_dotted(),
            sha256: raw_hash(package_file_hash(bytes))?,
        });
        verified.insert(module.clone(), checked);
    }

    Ok(Traversal {
        scenario_id: format!("checked-package.{mode}"),
        accepted: true,
        module_order: inputs
            .graph
            .topological_order
            .iter()
            .map(Name::as_dotted)
            .collect(),
        verified_modules,
        input_certificate_hashes,
        aggregate_work,
    })
}

fn validate_verified_identity(
    entry: &PackageLockEntry,
    checked: &VerifiedModule,
) -> Result<(), String> {
    if checked.module() != &entry.module
        || PackageHash::from(checked.export_hash()) != entry.export_hash
        || PackageHash::from(checked.certificate_hash()) != entry.certificate_hash
    {
        return Err(format!(
            "verified identity mismatch for {}",
            entry.module.as_dotted()
        ));
    }
    Ok(())
}

fn validate_fixture_manifest(source: &str) -> Result<(), String> {
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
    expect_unsigned(root[1].value(), 1, "fixture.warmup")?;
    expect_unsigned(root[2].value(), 9, "fixture.samples")?;
    expect_unsigned(root[3].value(), 100_000, "fixture.whnf_fuel")?;
    expect_unsigned(root[4].value(), 5_000_000, "fixture.conversion_fuel")?;
    let micro = expect_array(root[5].value(), "fixture.micro_scenarios")?;
    if micro.len() != 90 {
        return Err("fixture.micro_scenarios must contain 90 rows".to_owned());
    }
    let mut index = 0;
    for kind in MICRO_KINDS {
        for width in WIDTHS {
            for mode in MODES {
                let path = format!("fixture.micro_scenarios[{index}]");
                let fields = exact_object(
                    &micro[index],
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
                let id = format!("{kind}.w{width}.{mode}");
                expect_string(fields[0].value(), &id, &format!("{path}.id"))?;
                expect_string(fields[1].value(), kind, &format!("{path}.kind"))?;
                expect_unsigned(fields[2].value(), width, &format!("{path}.width"))?;
                expect_string(fields[3].value(), mode, &format!("{path}.mode"))?;
                let trailing = match kind {
                    "saturated-neutral-major" | "matching-constructor" => 8,
                    "retained-function-ephemeral-defeq" => 1,
                    _ => 0,
                };
                expect_unsigned(
                    fields[4].value(),
                    trailing,
                    &format!("{path}.trailing_arguments"),
                )?;
                if fields[5].value().bool_value() != Some(width == 8_192) {
                    return Err(format!("{path}.machine_only mismatch"));
                }
                if width == 8_192 {
                    if fields[6].value().kind() != JsonValueKind::Null {
                        return Err(format!("{path}.deterministic_baseline_key must be null"));
                    }
                } else {
                    expect_string(
                        fields[6].value(),
                        &id,
                        &format!("{path}.deterministic_baseline_key"),
                    )?;
                }
                index += 1;
            }
        }
    }
    let packages = expect_array(root[6].value(), "fixture.package_scenarios")?;
    if packages.len() != 3 {
        return Err("fixture.package_scenarios must contain three rows".to_owned());
    }
    for (index, row) in packages.iter().enumerate() {
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
        let mode = ["off", "ephemeral", "compare"][index];
        expect_string(fields[0].value(), PACKAGE_IDS[index], &format!("{path}.id"))?;
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
        let expected: &[&str] = match mode {
            "off" => &["checked-package.off"],
            "ephemeral" => &["checked-package.ephemeral"],
            "compare" => &["checked-package.off", "checked-package.ephemeral"],
            _ => return Err(format!("{path}.kernel_mode is outside the closed catalog")),
        };
        if keys.len() != expected.len() {
            return Err(format!(
                "{path}.deterministic_baseline_keys length mismatch"
            ));
        }
        for (key_index, (value, expected)) in keys.iter().zip(expected).enumerate() {
            expect_string(
                value,
                expected,
                &format!("{path}.deterministic_baseline_keys[{key_index}]"),
            )?;
        }
    }
    Ok(())
}

fn validate_baseline_schema(source: &str) -> Result<(), String> {
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
    let hash = root[1]
        .value()
        .string_value()
        .ok_or("baseline.fixture_manifest_sha256 must be a string")?;
    if hash.len() != 64
        || !hash
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return Err("baseline.fixture_manifest_sha256 must be lowercase SHA-256".to_owned());
    }
    if expect_array(root[2].value(), "baseline.micro_rows")?.len() != 72 {
        return Err("baseline.micro_rows must contain 72 rows".to_owned());
    }
    let packages = expect_array(root[3].value(), "baseline.package_rows")?;
    if packages.len() != 2 {
        return Err("baseline.package_rows must contain two rows".to_owned());
    }
    let mut identity_shapes = Vec::with_capacity(2);
    for (index, row) in packages.iter().enumerate() {
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
        expect_string(
            fields[0].value(),
            PACKAGE_IDS[index],
            &format!("{path}.key"),
        )?;
        expect_string(
            fields[1].value(),
            PACKAGE_IDS[index],
            &format!("{path}.scenario_id"),
        )?;
        if fields[2].value().bool_value() != Some(true) {
            return Err(format!("{path}.accepted must be true"));
        }
        validate_string_array(fields[3].value(), &format!("{path}.module_order"))?;
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

fn validate_baseline_fixture_hash(source: &str, expected: &str) -> Result<(), String> {
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

fn expect_string(value: &JsonValue<'_>, expected: &str, path: &str) -> Result<(), String> {
    match value.string_value() {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!("{path} is {actual:?}, expected {expected:?}")),
        None => Err(format!("{path} must be a string")),
    }
}

fn expect_unsigned(value: &JsonValue<'_>, expected: u64, path: &str) -> Result<(), String> {
    let actual = value
        .number_raw()
        .ok_or_else(|| format!("{path} must be an unsigned integer"))?
        .parse::<u64>()
        .map_err(|_| format!("{path} must be an unsigned integer"))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{path} is {actual}, expected {expected}"))
    }
}

fn parse_unsigned(value: &JsonValue<'_>, path: &str) -> Result<u64, String> {
    value
        .number_raw()
        .ok_or_else(|| format!("{path} must be an unsigned integer"))?
        .parse::<u64>()
        .map_err(|_| format!("{path} must be an unsigned integer"))
}

fn validate_hash(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let hash = value
        .string_value()
        .ok_or_else(|| format!("{path} must be a string"))?;
    if hash.len() == 64
        && hash
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        Ok(())
    } else {
        Err(format!("{path} must be lowercase SHA-256"))
    }
}

fn validate_string_array(value: &JsonValue<'_>, path: &str) -> Result<(), String> {
    let values = expect_array(value, path)?;
    if values.is_empty() {
        return Err(format!("{path} must not be empty"));
    }
    let mut seen = std::collections::BTreeSet::new();
    for (index, value) in values.iter().enumerate() {
        let item = value
            .string_value()
            .ok_or_else(|| format!("{path}[{index}] must be a string"))?;
        if !seen.insert(item) {
            return Err(format!("{path} contains duplicate {item:?}"));
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
        validate_hash(fields[2].value(), &format!("{row_path}.export_hash"))?;
        validate_hash(fields[3].value(), &format!("{row_path}.certificate_hash"))?;
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
        validate_hash(fields[1].value(), &format!("{row_path}.sha256"))?;
    }
    Ok(())
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
                parse_unsigned(field.value(), &format!("{path}.{key}"))?;
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
            parse_unsigned(total.value(), &format!("{domain_path}.{}", total.key()))?;
        }
        if totals[4].value().kind() != JsonValueKind::Bool {
            return Err(format!("{domain_path}.overflowed must be boolean"));
        }
    }
    Ok(())
}

fn validate_baseline_row(source: &str, result: &Traversal) -> Result<(), String> {
    let expected = package_row_json(result);
    let compact = compact_json(source)?;
    if compact.contains(&expected) {
        Ok(())
    } else {
        Err(format!(
            "missing or mismatched deterministic package row; expected={expected}"
        ))
    }
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

fn package_row_json(result: &Traversal) -> String {
    format!(
        "{{\"key\":\"{}\",\"scenario_id\":\"{}\",\"accepted\":{},\"module_order\":{},\"verified_modules\":{},\"input_certificate_hashes\":{},\"aggregate_work\":{}}}",
        result.scenario_id,
        result.scenario_id,
        result.accepted,
        string_array_json(&result.module_order),
        verified_modules_json(&result.verified_modules),
        input_hashes_json(&result.input_certificate_hashes),
        work_json(&result.aggregate_work),
    )
}

fn string_array_json(values: &[String]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!("\"{value}\""))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn verified_modules_json(values: &[VerifiedEvidence]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!(
                "{{\"lock_name\":\"{}\",\"module\":\"{}\",\"export_hash\":\"{}\",\"certificate_hash\":\"{}\"}}",
                value.lock_name, value.module, value.export_hash, value.certificate_hash
            ))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn input_hashes_json(values: &[InputHash]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!(
                "{{\"lock_name\":\"{}\",\"sha256\":\"{}\"}}",
                value.lock_name, value.sha256
            ))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn raw_hash(hash: PackageHash) -> Result<String, String> {
    format_package_hash(&hash)
        .strip_prefix("sha256:")
        .map(str::to_owned)
        .ok_or_else(|| "package hash formatter omitted sha256 prefix".to_owned())
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
    root: PathBuf,
    fixture_manifest: PathBuf,
    baseline: PathBuf,
    kernel_mode: String,
    child: bool,
    phase: String,
    sample_index: u64,
}

impl Args {
    fn parse_from(arguments: Vec<String>) -> Result<Self, String> {
        let mut root = None;
        let mut fixture_manifest = None;
        let mut baseline = None;
        let mut kernel_mode = None;
        let mut child = false;
        let mut phase = "candidate".to_owned();
        let mut phase_seen = false;
        let mut sample_index = 0;
        let mut sample_index_seen = false;
        let mut args = arguments.into_iter();
        while let Some(argument) = args.next() {
            match argument.as_str() {
                "--root" if root.is_none() => {
                    root = Some(PathBuf::from(args.next().ok_or("--root needs a value")?))
                }
                "--fixture-manifest" if fixture_manifest.is_none() => {
                    fixture_manifest = Some(PathBuf::from(
                        args.next().ok_or("--fixture-manifest needs a value")?,
                    ))
                }
                "--baseline" if baseline.is_none() => {
                    baseline = Some(PathBuf::from(
                        args.next().ok_or("--baseline needs a value")?,
                    ))
                }
                "--kernel-mode" if kernel_mode.is_none() => {
                    kernel_mode = Some(args.next().ok_or("--kernel-mode needs a value")?)
                }
                "--child" if !child => child = true,
                "--phase" if !phase_seen => {
                    phase = args.next().ok_or("--phase needs a value")?;
                    phase_seen = true;
                }
                "--sample-index" if !sample_index_seen => {
                    sample_index = args
                        .next()
                        .ok_or("--sample-index needs a value")?
                        .parse()
                        .map_err(|_| "sample index must be unsigned")?;
                    sample_index_seen = true;
                }
                other => return Err(format!("unknown or duplicate argument: {other}")),
            }
        }
        if !matches!(phase.as_str(), "recursive" | "candidate") {
            return Err("--phase must be recursive or candidate".to_owned());
        }
        if sample_index >= 9 {
            return Err("sample index must be in 0..8".to_owned());
        }
        let kernel_mode = kernel_mode.ok_or("--kernel-mode is required")?;
        if !matches!(kernel_mode.as_str(), "off" | "ephemeral" | "compare") {
            return Err("--kernel-mode must be off, ephemeral, or compare".to_owned());
        }
        let root = root.ok_or("--root is required")?;
        if root != Path::new("testdata/package/proofs") {
            return Err(
                "package harness accepts only testdata/package/proofs as the checked package"
                    .to_owned(),
            );
        }
        Ok(Self {
            root,
            fixture_manifest: fixture_manifest.ok_or("--fixture-manifest is required")?,
            baseline: baseline.ok_or("--baseline is required")?,
            kernel_mode,
            child,
            phase,
            sample_index,
        })
    }
}

fn read_utf8(path: &Path, label: &str) -> Result<String, String> {
    String::from_utf8(read_invocation_regular_file(
        path,
        MAX_JSON_INPUT_BYTES,
        label,
    )?)
    .map_err(|_| format!("{label} must be UTF-8"))
}

fn usage() -> &'static str {
    "usage: check_whnf_application_spine_package [--child --phase candidate --sample-index 0..8] --root testdata/package/proofs --fixture-manifest PATH --baseline PATH --kernel-mode off|ephemeral|compare\n\nThe post-switch executable rejects --phase recursive. Use the archived pre-switch executable for recursive evidence."
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn post_switch_package_binary_rejects_recursive_phase_relabeling() {
        assert!(reject_recursive_phase_on_post_switch_binary("recursive").is_err());
        assert!(reject_recursive_phase_on_post_switch_binary("candidate").is_ok());
    }

    #[test]
    fn package_fixture_manifest_parser() {
        let source = include_str!(
            "../../../testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
        );
        assert!(validate_fixture_manifest(source).is_ok());
        assert!(validate_fixture_manifest("{}").is_err());
        assert!(validate_fixture_manifest(
            &source.replace("checked-package.compare", "checked-package.off")
        )
        .is_err());
        assert!(validate_fixture_manifest(&source.replacen(
            "opaque-neutral-head.w32.memo-off",
            "unknown.w32.memo-off",
            1,
        ))
        .is_err());
    }

    #[test]
    fn package_deterministic_baseline_parser() {
        let source = include_str!(
            "../../../testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
        );
        assert!(validate_baseline_schema(source).is_ok());
        assert!(validate_baseline_schema("{}").is_err());
        assert!(validate_baseline_schema(&source.replace(
            "\"memo_probe_truncated\":false",
            "\"memo_probe_truncated\":0",
        ))
        .is_err());
        assert!(validate_baseline_schema(
            &source.replace("\"export_hash\":", "\"unknown\": 0, \"export_hash\":",)
        )
        .is_err());
        assert!(compact_json("{ \"x\" : \"a b\" }")
            .unwrap()
            .contains("\"a b\""));
    }

    #[test]
    fn whnf_package_child_protocol() {
        assert_eq!(PACKAGE_IDS.len(), 3);
        assert!(matches!("off", "off" | "ephemeral"));
        let base = vec![
            "--root".to_owned(),
            "testdata/package/proofs".to_owned(),
            "--fixture-manifest".to_owned(),
            "fixture.json".to_owned(),
            "--baseline".to_owned(),
            "baseline.json".to_owned(),
            "--kernel-mode".to_owned(),
            "off".to_owned(),
        ];
        assert!(Args::parse_from(base.clone()).is_ok());
        assert!(Args::parse_from([base.clone(), vec!["--unknown".to_owned()]].concat()).is_err());
        assert!(Args::parse_from(
            [
                base.clone(),
                vec!["--sample-index".to_owned(), "9".to_owned()]
            ]
            .concat()
        )
        .is_err());
        assert!(Args::parse_from(
            [
                base.clone(),
                vec![
                    "--phase".to_owned(),
                    "candidate".to_owned(),
                    "--phase".to_owned(),
                    "candidate".to_owned(),
                ],
            ]
            .concat(),
        )
        .is_err());
        assert!(Args::parse_from(
            [
                base,
                vec!["--root".to_owned(), "testdata/package/npa-std".to_owned(),],
            ]
            .concat(),
        )
        .is_err());
    }
}
