use std::env;
use std::fmt::Write as _;
use std::process::Command;
use std::thread;

use npa_cert::Name;
use npa_package::{
    build_package_lock_graph, parse_and_validate_manifest_str, parse_package_hash, PackageHash,
    PackageId, PackageLockEntry, PackageLockEntryOrigin, PackageLockErrorKind,
    PackageLockErrorReason, PackageLockImport, PackageLockManifest, PackageLockManifestReference,
    PackageLockResult, PackageManifestError, PackageManifestErrorKind, PackageManifestErrorReason,
    PackageManifestResult, PackagePath, PackageVersion, PACKAGE_LOCK_SCHEMA,
};

const DEEP_GRAPH_TEST_ENTRIES: usize = 4096;
const SMALL_STACK_BYTES: usize = 256 * 1024;
const DIFFERENTIAL_GRAPH_ENTRIES: usize = 3;
const DIFFERENTIAL_ENTRY_PERMUTATIONS: [[usize; DIFFERENTIAL_GRAPH_ENTRIES]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];
const CHILD_PROBE_ENV: &str = "NPA_PACKAGE_GRAPH_SMALL_STACK_CHILD";
const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

#[test]
fn deep_manifest_graph_is_stack_safe() {
    run_isolated_small_stack_probe("manifest", deep_manifest_graph_probe);
}

#[test]
fn deep_package_lock_graph_is_stack_safe() {
    run_isolated_small_stack_probe("package-lock", deep_package_lock_graph_probe);
}

#[test]
fn manifest_graph_matches_recursive_reference_for_all_small_graphs() {
    for permutation in DIFFERENTIAL_ENTRY_PERMUTATIONS {
        let names = differential_names(permutation);
        for edge_mask in 0..(1 << (DIFFERENTIAL_GRAPH_ENTRIES * DIFFERENTIAL_GRAPH_ENTRIES)) {
            for reverse_imports in [false, true] {
                let edges = differential_edges(edge_mask, reverse_imports);
                let expected = recursive_manifest_order(&edges, &names);
                let actual =
                    parse_and_validate_manifest_str(&differential_manifest_source(&edges, &names))
                        .map(|manifest| manifest.graph().topological_order.clone());
                assert_eq!(
                    actual, expected,
                    "manifest mismatch for permutation={permutation:?}, edge_mask={edge_mask:#x}, reverse_imports={reverse_imports}"
                );
            }
        }
    }
}

#[test]
fn package_lock_graph_matches_recursive_reference_for_all_small_graphs() {
    for permutation in DIFFERENTIAL_ENTRY_PERMUTATIONS {
        let names = differential_names(permutation);
        for edge_mask in 0..(1 << (DIFFERENTIAL_GRAPH_ENTRIES * DIFFERENTIAL_GRAPH_ENTRIES)) {
            for reverse_imports in [false, true] {
                let edges = differential_edges(edge_mask, reverse_imports);
                let (normalized_edges, normalized_names) =
                    normalized_differential_lock_graph(&edges, &names);
                let expected = recursive_lock_order(&normalized_edges, &normalized_names);
                let actual = build_package_lock_graph(&differential_package_lock(&edges, &names))
                    .map(|graph| {
                        graph
                            .topological_order
                            .iter()
                            .map(Name::as_dotted)
                            .collect::<Vec<_>>()
                    });
                assert_eq!(
                    actual, expected,
                    "package-lock mismatch for permutation={permutation:?}, edge_mask={edge_mask:#x}, reverse_imports={reverse_imports}"
                );
            }
        }
    }
}

fn run_isolated_small_stack_probe(probe: &str, workload: fn()) {
    if env::var(CHILD_PROBE_ENV).as_deref() == Ok(probe) {
        thread::Builder::new()
            .name(format!("package-graph-{probe}-small-stack"))
            .stack_size(SMALL_STACK_BYTES)
            .spawn(workload)
            .expect("small-stack probe thread should start")
            .join()
            .expect("small-stack probe thread should complete");
        return;
    }

    let test_name = match probe {
        "manifest" => "deep_manifest_graph_is_stack_safe",
        "package-lock" => "deep_package_lock_graph_is_stack_safe",
        _ => panic!("unknown package graph probe {probe}"),
    };
    let output = Command::new(env::current_exe().expect("current test executable should resolve"))
        .args(["--exact", test_name, "--nocapture"])
        .env(CHILD_PROBE_ENV, probe)
        .output()
        .expect("isolated small-stack probe should run");

    assert!(
        output.status.success(),
        "isolated {probe} probe failed with {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

fn deep_manifest_graph_probe() {
    let acyclic = parse_and_validate_manifest_str(&deep_manifest_source(false))
        .expect("deep acyclic manifest should validate");
    assert_eq!(
        acyclic.graph().topological_order,
        (0..DEEP_GRAPH_TEST_ENTRIES).rev().collect::<Vec<_>>()
    );

    let error = parse_and_validate_manifest_str(&deep_manifest_source(true))
        .expect_err("deep manifest cycle should be rejected");
    assert_eq!(error.kind, PackageManifestErrorKind::Graph);
    assert_eq!(error.reason_code, PackageManifestErrorReason::ImportCycle);
    assert_eq!(
        error.path,
        format!("modules[{}].imports[0]", DEEP_GRAPH_TEST_ENTRIES - 1)
    );
    assert_eq!(
        error.actual_value.as_deref(),
        Some(deep_module_name(0).as_str())
    );
}

fn deep_manifest_source(cycle: bool) -> String {
    let mut source = r#"schema = "npa.package.v0.1"
package = "npa-deep-graph-test"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

"#
    .to_owned();

    for index in 0..DEEP_GRAPH_TEST_ENTRIES {
        let imports = if index + 1 < DEEP_GRAPH_TEST_ENTRIES {
            format!(r#"["{}"]"#, deep_module_name(index + 1))
        } else if cycle {
            format!(r#"["{}"]"#, deep_module_name(0))
        } else {
            "[]".to_owned()
        };
        writeln!(
            source,
            r#"[[modules]]
module = "{module}"
source = "Proofs/Deep/M{index:04}/source.npa"
certificate = "Proofs/Deep/M{index:04}/certificate.npcert"
imports = {imports}
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
inductives = []
definitions = []
theorems = []
axioms = []
tags = []
"#,
            module = deep_module_name(index),
        )
        .expect("writing to a String should succeed");
    }

    source.push_str(
        r#"[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
    );
    source
}

fn deep_package_lock_graph_probe() {
    let acyclic = build_package_lock_graph(&deep_package_lock(false))
        .expect("deep acyclic package lock should validate");
    assert_eq!(
        acyclic
            .topological_order
            .iter()
            .map(Name::as_dotted)
            .collect::<Vec<_>>(),
        (0..DEEP_GRAPH_TEST_ENTRIES)
            .rev()
            .map(deep_module_name)
            .collect::<Vec<_>>()
    );

    let error = build_package_lock_graph(&deep_package_lock(true))
        .expect_err("deep package-lock cycle should be rejected");
    assert_eq!(error.kind, PackageLockErrorKind::Graph);
    assert_eq!(error.reason_code, PackageLockErrorReason::LockImportCycle);
    assert_eq!(
        error.path,
        format!("entries[{}].imports", DEEP_GRAPH_TEST_ENTRIES - 1)
    );
    assert_eq!(
        error.module.as_ref().map(|module| module.as_str()),
        Some(deep_module_name(DEEP_GRAPH_TEST_ENTRIES - 1).as_str())
    );

    let mut expected_cycle = (0..DEEP_GRAPH_TEST_ENTRIES)
        .map(deep_module_name)
        .collect::<Vec<_>>();
    expected_cycle.push(deep_module_name(0));
    assert_eq!(
        error.actual_value.as_deref(),
        Some(expected_cycle.join(" -> ").as_str())
    );
}

fn deep_package_lock(cycle: bool) -> PackageLockManifest {
    let zero_hash = zero_hash();
    let entries = (0..DEEP_GRAPH_TEST_ENTRIES)
        .map(|index| {
            let imports = if index + 1 < DEEP_GRAPH_TEST_ENTRIES {
                vec![deep_lock_import(index + 1)]
            } else if cycle {
                vec![deep_lock_import(0)]
            } else {
                Vec::new()
            };
            PackageLockEntry {
                module: Name::from_dotted(deep_module_name(index)),
                origin: PackageLockEntryOrigin::Local,
                certificate: PackagePath::new(format!(
                    "Proofs/Deep/M{index:04}/certificate.npcert"
                )),
                certificate_file_hash: zero_hash,
                export_hash: zero_hash,
                axiom_report_hash: zero_hash,
                certificate_hash: zero_hash,
                imports,
                package: None,
                version: None,
            }
        })
        .collect();

    PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: PackageId::new("npa-deep-graph-test"),
        version: PackageVersion::new("0.1.0"),
        manifest: PackageLockManifestReference {
            path: PackagePath::new("npa-package.toml"),
            file_hash: zero_hash,
        },
        entries,
    }
}

fn deep_lock_import(index: usize) -> PackageLockImport {
    PackageLockImport {
        module: Name::from_dotted(deep_module_name(index)),
        export_hash: zero_hash(),
        certificate_hash: zero_hash(),
    }
}

fn deep_module_name(index: usize) -> String {
    format!("Proofs.Deep.M{index:04}")
}

fn zero_hash() -> PackageHash {
    parse_package_hash(ZERO_HASH, "test.zero_hash").expect("zero hash should parse")
}

fn differential_names(
    permutation: [usize; DIFFERENTIAL_GRAPH_ENTRIES],
) -> [String; DIFFERENTIAL_GRAPH_ENTRIES] {
    permutation.map(|index| format!("Proofs.Differential.M{index}"))
}

fn differential_edges(edge_mask: usize, reverse_imports: bool) -> Vec<Vec<usize>> {
    (0..DIFFERENTIAL_GRAPH_ENTRIES)
        .map(|owner| {
            let mut imports = (0..DIFFERENTIAL_GRAPH_ENTRIES)
                .filter(|target| {
                    edge_mask & (1 << (owner * DIFFERENTIAL_GRAPH_ENTRIES + target)) != 0
                })
                .collect::<Vec<_>>();
            if reverse_imports {
                imports.reverse();
            }
            imports
        })
        .collect()
}

fn differential_manifest_source(edges: &[Vec<usize>], names: &[String]) -> String {
    let mut source = r#"schema = "npa.package.v0.1"
package = "npa-differential-graph-test"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

"#
    .to_owned();

    for (index, name) in names.iter().enumerate() {
        let imports = edges[index]
            .iter()
            .map(|target| format!(r#""{}""#, names[*target]))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            source,
            r#"[[modules]]
module = "{name}"
source = "Proofs/Differential/M{index}/source.npa"
certificate = "Proofs/Differential/M{index}/certificate.npcert"
imports = [{imports}]
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
inductives = []
definitions = []
theorems = []
axioms = []
tags = []
"#,
        )
        .expect("writing to a String should succeed");
    }

    source.push_str(
        r#"[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
    );
    source
}

fn differential_package_lock(edges: &[Vec<usize>], names: &[String]) -> PackageLockManifest {
    let hash = zero_hash();
    let entries = names
        .iter()
        .enumerate()
        .map(|(index, name)| PackageLockEntry {
            module: Name::from_dotted(name),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new(format!(
                "Proofs/Differential/M{index}/certificate.npcert"
            )),
            certificate_file_hash: hash,
            export_hash: hash,
            axiom_report_hash: hash,
            certificate_hash: hash,
            imports: edges[index]
                .iter()
                .map(|target| PackageLockImport {
                    module: Name::from_dotted(&names[*target]),
                    export_hash: hash,
                    certificate_hash: hash,
                })
                .collect(),
            package: None,
            version: None,
        })
        .collect();

    PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: PackageId::new("npa-differential-graph-test"),
        version: PackageVersion::new("0.1.0"),
        manifest: PackageLockManifestReference {
            path: PackagePath::new("npa-package.toml"),
            file_hash: hash,
        },
        entries,
    }
}

fn normalized_differential_lock_graph(
    edges: &[Vec<usize>],
    names: &[String],
) -> (Vec<Vec<usize>>, Vec<String>) {
    let mut original_indices = (0..names.len()).collect::<Vec<_>>();
    original_indices.sort_by_key(|index| &names[*index]);

    let mut normalized_index_by_original = vec![0; names.len()];
    for (normalized_index, original_index) in original_indices.iter().copied().enumerate() {
        normalized_index_by_original[original_index] = normalized_index;
    }

    let normalized_names = original_indices
        .iter()
        .map(|index| names[*index].clone())
        .collect::<Vec<_>>();
    let normalized_edges = original_indices
        .iter()
        .map(|original_index| {
            let mut imports = edges[*original_index]
                .iter()
                .map(|target| normalized_index_by_original[*target])
                .collect::<Vec<_>>();
            imports.sort_unstable();
            imports
        })
        .collect::<Vec<_>>();

    (normalized_edges, normalized_names)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReferenceVisitState {
    Unvisited,
    Visiting,
    Visited,
}

fn recursive_manifest_order(
    edges: &[Vec<usize>],
    names: &[String],
) -> PackageManifestResult<Vec<usize>> {
    fn visit(
        owner: usize,
        edges: &[Vec<usize>],
        names: &[String],
        states: &mut [ReferenceVisitState],
        order: &mut Vec<usize>,
    ) -> PackageManifestResult<()> {
        states[owner] = ReferenceVisitState::Visiting;
        for (import_index, target) in edges[owner].iter().copied().enumerate() {
            match states[target] {
                ReferenceVisitState::Unvisited => {
                    visit(target, edges, names, states, order)?;
                }
                ReferenceVisitState::Visiting => {
                    return Err(PackageManifestError::import_cycle(
                        format!("modules[{owner}].imports[{import_index}]"),
                        names[target].clone(),
                    ));
                }
                ReferenceVisitState::Visited => {}
            }
        }
        states[owner] = ReferenceVisitState::Visited;
        order.push(owner);
        Ok(())
    }

    let mut states = vec![ReferenceVisitState::Unvisited; edges.len()];
    let mut order = Vec::with_capacity(edges.len());
    for root in 0..edges.len() {
        if states[root] == ReferenceVisitState::Unvisited {
            visit(root, edges, names, &mut states, &mut order)?;
        }
    }
    Ok(order)
}

fn recursive_lock_order(edges: &[Vec<usize>], names: &[String]) -> PackageLockResult<Vec<String>> {
    fn visit(
        owner: usize,
        edges: &[Vec<usize>],
        names: &[String],
        states: &mut [ReferenceVisitState],
        stack: &mut Vec<usize>,
        order: &mut Vec<String>,
    ) -> PackageLockResult<()> {
        match states[owner] {
            ReferenceVisitState::Visited => return Ok(()),
            ReferenceVisitState::Visiting => {
                return Err(lock_cycle_error(owner, owner, stack, names));
            }
            ReferenceVisitState::Unvisited => {}
        }

        states[owner] = ReferenceVisitState::Visiting;
        stack.push(owner);
        for target in edges[owner].iter().copied() {
            if states[target] == ReferenceVisitState::Visiting {
                return Err(lock_cycle_error(owner, target, stack, names));
            }
            visit(target, edges, names, states, stack, order)?;
        }
        stack.pop();
        states[owner] = ReferenceVisitState::Visited;
        order.push(names[owner].clone());
        Ok(())
    }

    let mut states = vec![ReferenceVisitState::Unvisited; edges.len()];
    let mut stack = Vec::new();
    let mut order = Vec::with_capacity(edges.len());
    for root in 0..edges.len() {
        visit(root, edges, names, &mut states, &mut stack, &mut order)?;
    }
    Ok(order)
}

fn lock_cycle_error(
    owner: usize,
    repeated: usize,
    stack: &[usize],
    names: &[String],
) -> npa_package::PackageLockError {
    let start = stack
        .iter()
        .position(|entry_index| *entry_index == repeated)
        .unwrap_or(0);
    let mut cycle = stack[start..]
        .iter()
        .map(|entry_index| names[*entry_index].clone())
        .collect::<Vec<_>>();
    cycle.push(names[repeated].clone());
    npa_package::PackageLockError::lock_import_cycle(
        format!("entries[{owner}].imports"),
        cycle.join(" -> "),
    )
    .with_module(names[owner].clone())
}
