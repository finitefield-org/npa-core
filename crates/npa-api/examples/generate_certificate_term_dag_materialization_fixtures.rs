#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;
#[path = "support/term_dag_performance.rs"]
mod term_dag_performance;

use std::path::PathBuf;

fn main() {
    if let Err(error) = run() {
        eprintln!("generate certificate term-DAG fixtures: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    if arguments == ["--list"] {
        for scenario in term_dag_performance::SCENARIOS {
            println!("{}", scenario.id);
        }
        return Ok(());
    }
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
    let mut output = None;
    let mut clean_output = None;
    let mut scenario = None;
    let mut index = 0;
    while index < arguments.len() {
        let value = arguments.get(index + 1).ok_or_else(usage)?;
        match arguments[index].as_str() {
            "--output" if output.is_none() && clean_output.is_none() => {
                output = Some(PathBuf::from(value))
            }
            "--clean-output" if output.is_none() && clean_output.is_none() => {
                clean_output = Some(PathBuf::from(value))
            }
            "--scenario" if scenario.is_none() => scenario = Some(value.clone()),
            option => {
                return Err(format!(
                    "unknown or duplicate option: {option}\n{}",
                    usage()
                ))
            }
        }
        index += 2;
    }
    if let Some(output) = clean_output {
        if scenario.is_some() {
            return Err(format!(
                "--scenario cannot be used with --clean-output\n{}",
                usage()
            ));
        }
        return term_dag_performance::clean_fixture_roots(&output);
    }
    let output = output.ok_or_else(usage)?;
    term_dag_performance::generate_fixture_roots(&output, scenario.as_deref())
}

fn usage() -> String {
    "usage: generate_certificate_term_dag_materialization_fixtures --output PATH [--scenario ID]\n       generate_certificate_term_dag_materialization_fixtures --clean-output PATH\n       generate_certificate_term_dag_materialization_fixtures --list\n       generate_certificate_term_dag_materialization_fixtures --print-canonical-manifest\n       generate_certificate_term_dag_materialization_fixtures --print-canonical-baseline".to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use closed_private_tree::ClosedPrivateDirectory;
    use npa_cert::{
        build_module_cert, encode_module_cert,
        verify_module_cert_with_import_refs_and_kernel_options_and_observations, AxiomPolicy,
        CertificateTermMaterializationObservation, CertificateVerificationObservationSinks,
        CoreModule, Name,
    };
    use npa_kernel::{Decl, Expr, KernelExecutionOptions, Level};
    use std::path::Path;

    fn doubling(height: usize) -> Expr {
        let mut expression = Expr::sort(Level::zero());
        for _ in 0..height {
            expression = Expr::pi("_", expression.clone(), expression);
        }
        expression
    }

    fn chain(length: usize) -> Expr {
        assert!(length > 0);
        let zero = Expr::sort(Level::zero());
        let mut expression = zero.clone();
        for _ in 1..length {
            expression = Expr::pi("_", expression, zero.clone());
        }
        expression
    }

    fn observe(name: &str, ty: Expr) -> CertificateTermMaterializationObservation {
        let certificate = build_module_cert(
            CoreModule {
                name: Name::from_dotted(name),
                declarations: vec![Decl::Axiom {
                    name: "root".to_owned(),
                    universe_params: Vec::new(),
                    ty,
                }],
            },
            &[],
        )
        .unwrap();
        let bytes = encode_module_cert(&certificate).unwrap();
        let mut term = CertificateTermMaterializationObservation::default();
        verify_module_cert_with_import_refs_and_kernel_options_and_observations(
            &bytes,
            &[],
            &AxiomPolicy::normal(),
            KernelExecutionOptions::memo_off(),
            CertificateVerificationObservationSinks::new().with_term(&mut term),
        )
        .unwrap();
        term
    }

    #[test]
    fn canonical_term_dag_graph_grammar() {
        let doubling_observation = observe("Bench.Tdag.Test.Doubling", doubling(8));
        assert_eq!(doubling_observation.unique_nodes_materialized, 9);
        assert_eq!(doubling_observation.selected_edges, 16);
        assert_eq!(doubling_observation.root_requests, 1);

        let chain_observation = observe("Bench.Tdag.Test.Chain", chain(256));
        assert_eq!(chain_observation.unique_nodes_materialized, 256);
        assert_eq!(chain_observation.selected_edges, 510);
        assert_eq!(chain_observation.root_requests, 1);
    }

    #[test]
    fn canonical_term_dag_case_package() {
        assert_eq!(term_dag_performance::SCENARIOS.len(), 7);
        assert_eq!(term_dag_performance::cases().len(), 18);
        for scenario in term_dag_performance::SCENARIOS {
            let descriptor = term_dag_performance::fixture_descriptor_json(scenario);
            npa_api::JsonDocument::parse(&descriptor).unwrap();
            assert_eq!(
                term_dag_performance::fixture_tree_hash_for_descriptor(scenario).len(),
                64
            );
        }
    }

    #[test]
    fn term_dag_fixture_tree_trust_boundary() {
        let scenario = term_dag_performance::SCENARIOS[0];
        let parent = ClosedPrivateDirectory::new("npa-tdag-test-parent").unwrap();
        parent.create_directory(Path::new("fixture")).unwrap();
        parent
            .create_new_file(
                Path::new("fixture/fixture.json"),
                term_dag_performance::fixture_descriptor_json(scenario).as_bytes(),
            )
            .unwrap();
        let root = parent.path().join("fixture");
        assert_eq!(
            term_dag_performance::fixture_tree_hash(&root).unwrap(),
            term_dag_performance::fixture_tree_hash_for_descriptor(scenario)
        );
        term_dag_performance::validate_scenario_fixture_root(&root, scenario).unwrap();

        std::fs::write(root.join("extra.json"), b"{}\n").unwrap();
        assert!(term_dag_performance::validate_scenario_fixture_root(&root, scenario).is_err());
        std::fs::remove_file(root.join("extra.json")).unwrap();
        std::fs::create_dir(root.join("extra-directory")).unwrap();
        assert!(term_dag_performance::validate_scenario_fixture_root(&root, scenario).is_err());
        std::fs::remove_dir(root.join("extra-directory")).unwrap();

        #[cfg(unix)]
        {
            use std::os::unix::{ffi::OsStringExt as _, fs::symlink};

            let outside = parent.path().join("outside.json");
            std::fs::write(
                &outside,
                term_dag_performance::fixture_descriptor_json(scenario),
            )
            .unwrap();
            std::fs::remove_file(root.join("fixture.json")).unwrap();
            symlink(&outside, root.join("fixture.json")).unwrap();
            assert!(term_dag_performance::validate_scenario_fixture_root(&root, scenario).is_err());
            std::fs::remove_file(root.join("fixture.json")).unwrap();
            std::fs::write(
                root.join("fixture.json"),
                term_dag_performance::fixture_descriptor_json(scenario),
            )
            .unwrap();

            let socket = std::os::unix::net::UnixListener::bind(root.join("socket")).unwrap();
            assert!(term_dag_performance::validate_scenario_fixture_root(&root, scenario).is_err());
            drop(socket);
            std::fs::remove_file(root.join("socket")).unwrap();

            let non_utf8 = std::ffi::OsString::from_vec(vec![0xff]);
            assert!(
                term_dag_performance::normalized_utf8_relative_path(std::path::Path::new(
                    &non_utf8
                ))
                .is_err()
            );
        }

        let catalog_owner = ClosedPrivateDirectory::new("npa-tdag-fixtures").unwrap();
        let catalog = catalog_owner.path().to_owned();
        term_dag_performance::generate_fixture_roots(&catalog, None).unwrap();
        term_dag_performance::validate_fixture_catalog_root(&catalog).unwrap();
        catalog_owner
            .create_directory(Path::new("unexpected-scenario"))
            .unwrap();
        assert!(term_dag_performance::validate_fixture_catalog_root(&catalog).is_err());

        #[cfg(unix)]
        {
            let linked = parent.path().join("linked-catalog");
            std::os::unix::fs::symlink(&catalog, &linked).unwrap();
            assert!(term_dag_performance::validate_fixture_catalog_root(&linked).is_err());
            std::fs::remove_file(linked).unwrap();
        }
    }

    #[test]
    fn charge_tuned_term_dag_family() {
        for target in [268_435_455_u64, 268_435_456, 268_435_457] {
            let observation = npa_cert::benchmark_term_materialization_admission_v1(target);
            if target <= npa_cert::TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT {
                assert_eq!(observation.materialization_charged_bytes, target);
                assert_eq!(observation.materialization_capacity_stops, 0);
                assert_eq!(observation.materialization_legacy_fallbacks, 0);
            } else {
                assert_eq!(observation.materialization_charged_bytes, 0);
                assert_eq!(observation.materialization_capacity_stops, 1);
                assert_eq!(observation.materialization_legacy_fallbacks, 1);
            }
        }
    }

    #[test]
    fn shared_doubling_fixture() {
        let cases = term_dag_performance::cases();
        assert_eq!(
            cases
                .iter()
                .filter(|case| case.scenario_id == "shared-doubling")
                .count(),
            4
        );
        assert_eq!(cases[3].counters.unique_nodes, 19);
        assert_eq!(cases[3].counters.selected_edges, 36);
    }

    #[test]
    fn nonsharing_chain_fixture() {
        let case = term_dag_performance::cases()
            .into_iter()
            .find(|case| case.case_id == "length-8191")
            .unwrap();
        assert_eq!(case.counters.unique_nodes, 8_191);
        assert_eq!(case.counters.selected_edges, 16_380);
    }

    #[test]
    fn repeated_declaration_roots_fixture() {
        let case = term_dag_performance::cases()
            .into_iter()
            .find(|case| case.case_id == "declarations-4096")
            .unwrap();
        assert_eq!(case.counters.root_requests, 4_096);
        assert_eq!(case.counters.unique_nodes, 9);
    }

    #[test]
    fn sparse_import_fixture() {
        let baseline = term_dag_performance::render_baseline().unwrap();
        assert!(baseline.contains("\"modeled_provider_table_nodes\":262144"));
        assert!(baseline.contains("\"materialized_table_slots\":64"));
        assert!(baseline.contains("\"unselected_expr_allocations\":0"));
        assert!(baseline.contains("\"decision\":\"NotSelectedImportPerformanceEvidence\""));
    }

    #[test]
    fn import_diamond_fixture() {
        let baseline = term_dag_performance::render_baseline().unwrap();
        assert!(baseline.contains("\"modeled_module_slots\":10"));
        assert!(baseline.contains("\"materialized_root_requests\":16"));
    }

    #[test]
    fn near_limit_fixture() {
        charge_tuned_term_dag_family();
    }

    #[test]
    fn wide_package_fixture() {
        let cases = term_dag_performance::cases();
        let wide = cases
            .iter()
            .filter(|case| case.scenario_id == "wide-term-materialization-package")
            .collect::<Vec<_>>();
        assert_eq!(wide.len(), 5);
        assert_eq!(wide[3].effective_jobs, 3);
        assert_eq!(wide[3].reduction_reason, "memory_budget");
    }

    #[test]
    fn all_term_dag_fixtures_reproducible() {
        let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        term_dag_performance::validate_artifacts(&workspace).unwrap();
        let generated = ClosedPrivateDirectory::new("npa-tdag-fixtures").unwrap();
        term_dag_performance::generate_fixture_roots(generated.path(), None).unwrap();
        let checked = workspace
            .canonicalize()
            .unwrap()
            .join(term_dag_performance::FIXTURE_ROOT);
        term_dag_performance::compare_fixture_roots(&checked, generated.path()).unwrap();
        let generated_path = generated.path().to_owned();
        term_dag_performance::clean_fixture_roots(generated.path()).unwrap();
        assert!(!generated_path.exists());
    }

    #[test]
    fn fixture_cleanup_is_closed_and_preimage_bound() {
        let extra = ClosedPrivateDirectory::new("npa-tdag-fixtures").unwrap();
        term_dag_performance::generate_fixture_roots(extra.path(), None).unwrap();
        extra
            .create_new_file(Path::new("unexpected"), b"x")
            .unwrap();
        assert!(term_dag_performance::clean_fixture_roots(extra.path()).is_err());

        let changed = ClosedPrivateDirectory::new("npa-tdag-fixtures").unwrap();
        term_dag_performance::generate_fixture_roots(changed.path(), None).unwrap();
        let fixture = Path::new("shared-doubling/fixture.json");
        let expected = changed.read_regular_file(fixture, 4 * 1024 * 1024).unwrap();
        changed
            .replace_exact_file(fixture, &expected, b"{}\n")
            .unwrap();
        assert!(term_dag_performance::clean_fixture_roots(changed.path()).is_err());
    }
}
