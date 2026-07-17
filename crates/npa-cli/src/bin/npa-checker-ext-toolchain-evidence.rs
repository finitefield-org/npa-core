use std::env;
use std::path::{Path, PathBuf};

use npa_cli::checker_ext_toolchain_evidence as evidence;

fn usage() -> ! {
    eprintln!("usage: npa-checker-ext-toolchain-evidence <prepare-fixture|prepare-inputs|inventory|capture-run|compare-runs|check-trace|collect-build|build-release|check-metadata|json-field|contract> [options]");
    std::process::exit(2);
}

fn take(args: &mut Vec<String>, option: &str) -> String {
    let Some(index) = args.iter().position(|value| value == option) else {
        eprintln!("missing required option: {option}");
        usage();
    };
    if index + 1 >= args.len() {
        usage();
    }
    args.remove(index);
    args.remove(index)
}

fn take_many(args: &mut Vec<String>, option: &str) -> Vec<PathBuf> {
    let mut values = Vec::new();
    while args.iter().any(|value| value == option) {
        values.push(PathBuf::from(take(args, option)));
    }
    values
}

fn finish(args: &[String]) {
    if !args.is_empty() {
        eprintln!("unknown option: {}", args[0]);
        usage();
    }
}

fn main() {
    let mut args = env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() {
        usage();
    }
    let command = args.remove(0);
    let result = match command.as_str() {
        "prepare-inputs" => {
            let root = take(&mut args, "--root");
            let checker = take(&mut args, "--checker");
            let version_file = take(&mut args, "--version-file");
            finish(&args);
            evidence::prepare_inputs(
                Path::new(&root),
                Path::new(&checker),
                Path::new(&version_file),
            )
        }
        "prepare-fixture" => {
            let run_dir = take(&mut args, "--run-dir");
            let fixture = take(&mut args, "--fixture");
            let core_root = take(&mut args, "--core-root");
            finish(&args);
            evidence::prepare_fixture(
                Path::new(&run_dir),
                Path::new(&fixture),
                Path::new(&core_root),
            )
        }
        "inventory" => {
            let root = take(&mut args, "--root");
            let extras = take_many(&mut args, "--extra");
            finish(&args);
            evidence::inventory(Path::new(&root), &extras)
        }
        "capture-run" => {
            let root = take(&mut args, "--root");
            let command_result = take(&mut args, "--command-result");
            let evidence_dir = take(&mut args, "--evidence-dir");
            let fixture_record = take(&mut args, "--fixture-record");
            let preflight = take(&mut args, "--preflight");
            finish(&args);
            evidence::capture_run(
                Path::new(&root),
                Path::new(&command_result),
                Path::new(&evidence_dir),
                Path::new(&fixture_record),
                Path::new(&preflight),
            )
        }
        "compare-runs" => {
            let runs = take_many(&mut args, "--run");
            finish(&args);
            evidence::compare_runs(&runs)
        }
        "check-trace" => {
            let trace_prefix = take(&mut args, "--trace-prefix");
            let source_root = take(&mut args, "--source-root");
            let package_root = take(&mut args, "--package-root");
            let fixture_record = take(&mut args, "--fixture-record");
            finish(&args);
            evidence::check_trace(
                Path::new(&trace_prefix),
                Path::new(&source_root),
                Path::new(&package_root),
                Path::new(&fixture_record),
            )
        }
        "collect-build" => {
            let core_root = take(&mut args, "--core-root");
            let source_root = take(&mut args, "--source-root");
            let fixture_record = take(&mut args, "--fixture-record");
            let metadata = take(&mut args, "--metadata");
            let preflight = take(&mut args, "--preflight");
            let checker = take(&mut args, "--checker");
            let require_clean =
                if let Some(index) = args.iter().position(|value| value == "--require-clean") {
                    args.remove(index);
                    true
                } else {
                    false
                };
            finish(&args);
            evidence::collect_build(
                Path::new(&core_root),
                Path::new(&source_root),
                Path::new(&fixture_record),
                Path::new(&metadata),
                Path::new(&preflight),
                Path::new(&checker),
                require_clean,
            )
        }
        "build-release" => {
            let source_root = take(&mut args, "--source-root");
            let core_root = take(&mut args, "--core-root");
            let package_root = take(&mut args, "--package-root");
            let assets_root = take(&mut args, "--assets-root");
            let fixture_record = take(&mut args, "--fixture-record");
            let preflight = take(&mut args, "--preflight");
            let build_record = take(&mut args, "--build-record");
            let final_evidence = take(&mut args, "--final-evidence");
            let generated_at_utc = take(&mut args, "--generated-at-utc");
            finish(&args);
            evidence::build_release(
                Path::new(&source_root),
                Path::new(&core_root),
                Path::new(&package_root),
                Path::new(&assets_root),
                Path::new(&fixture_record),
                Path::new(&preflight),
                Path::new(&build_record),
                Path::new(&final_evidence),
                &generated_at_utc,
            )
        }
        "check-metadata" => {
            let metadata = take(&mut args, "--metadata");
            finish(&args);
            evidence::check_metadata(Path::new(&metadata))
        }
        "json-field" => {
            let path = take(&mut args, "--path");
            let field = take(&mut args, "--field");
            finish(&args);
            evidence::json_field(Path::new(&path), &field)
        }
        "contract" => {
            finish(&args);
            Ok(evidence::contract())
        }
        _ => usage(),
    };
    match result {
        Ok(output) => print!("{output}"),
        Err(error) => {
            eprintln!("toolchain_v0_7_evidence: {error}");
            std::process::exit(1);
        }
    }
}
