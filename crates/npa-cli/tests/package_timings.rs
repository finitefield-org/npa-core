use std::path::{Path, PathBuf};

use npa_cli::args::{
    PackageAuditCacheMode, PackageAxiomReportOptions, PackageChecker, PackageCommonOptions,
    PackageIndexOptions, PackageTimingMode, PackageVerifierMemoMode, PackageVerifyCertsOptions,
};
use npa_cli::diagnostic::{CommandExitCode, PACKAGE_TIMINGS_SCHEMA};
use npa_cli::package_axiom_report::run_package_axiom_report;
use npa_cli::package_index::run_package_index;
use npa_cli::package_verify::run_package_verify_certs;

#[test]
fn package_timings_axiom_report_summary_json_is_opt_in_and_normalizable() {
    let off = run_axiom_report(PackageTimingMode::Off);
    let summary = run_axiom_report(PackageTimingMode::Summary);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_eq!(summary.exit_code(), CommandExitCode::Success);

    let off_json = off.render_json();
    let summary_json = summary.render_json();
    assert!(!off_json.contains("\"timings\""));
    assert!(summary_json.contains("\"timings\""));
    assert_eq!(strip_timings(&summary_json), off_json);
    assert_timing_header(&summary_json, "summary");
    for field in [
        "load_root_ms",
        "load_lock_ms",
        "decode_certificates_ms",
        "checker_ms",
        "projection_ms",
        "json_write_ms",
        "artifact_compare_ms",
        "total_ms",
    ] {
        assert_timing_field(&summary_json, field);
    }
}

#[test]
fn package_timings_index_summary_json_uses_projection_phase_fields() {
    let result = run_index(PackageTimingMode::Summary);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let json = result.render_json();
    assert_timing_header(&json, "summary");
    for field in [
        "load_root_ms",
        "load_lock_ms",
        "decode_certificates_ms",
        "checker_ms",
        "projection_ms",
        "json_write_ms",
        "artifact_compare_ms",
        "total_ms",
    ] {
        assert_timing_field(&json, field);
    }
}

#[test]
fn package_timings_verify_certs_detailed_json_has_stable_phase_fields() {
    let result = run_verify_certs(PackageTimingMode::Detailed);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let json = result.render_json();
    assert_timing_header(&json, "detailed");
    for field in [
        "load_root_ms",
        "load_lock_ms",
        "decode_certificates_ms",
        "build_graph_ms",
        "checker_ms",
        "total_ms",
    ] {
        assert_timing_field(&json, field);
    }
    assert!(!json.contains("\"proof_evidence\":true"));
    assert!(!json.contains("\"build_evidence\":true"));
}

fn run_axiom_report(timings: PackageTimingMode) -> npa_cli::diagnostic::CommandResult {
    run_package_axiom_report(PackageAxiomReportOptions {
        common: PackageCommonOptions {
            root: fixture_root(),
            json: true,
        },
        check: true,
        timings,
    })
}

fn run_index(timings: PackageTimingMode) -> npa_cli::diagnostic::CommandResult {
    run_package_index(PackageIndexOptions {
        common: PackageCommonOptions {
            root: fixture_root(),
            json: true,
        },
        check: true,
        timings,
    })
}

fn run_verify_certs(timings: PackageTimingMode) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(PackageVerifyCertsOptions {
        common: PackageCommonOptions {
            root: fixture_root(),
            json: true,
        },
        checker: PackageChecker::Fast,
        audit_cache: PackageAuditCacheMode::Off,
        verifier_memo: PackageVerifierMemoMode::Off,
        jobs: 1,
        external: None,
        timings,
    })
}

fn assert_timing_header(json: &str, mode: &str) {
    assert!(json.contains(&format!(
        "\"timings\":{{\"schema\":\"{PACKAGE_TIMINGS_SCHEMA}\""
    )));
    assert!(json.contains(&format!("\"mode\":\"{mode}\"")));
    assert!(json.contains("\"unit\":\"ms\""));
    assert!(json.contains("\"proof_evidence\":false"));
    assert!(json.contains("\"build_evidence\":false"));
}

fn assert_timing_field(json: &str, field: &str) {
    assert!(
        json.contains(&format!("\"{field}\":")),
        "missing timing field {field} in {json}"
    );
}

fn strip_timings(json: &str) -> String {
    let Some(start) = json.find(",\"timings\":{") else {
        return json.to_owned();
    };
    let object_start = json[start..]
        .find('{')
        .map(|offset| start + offset)
        .expect("timings marker contains an object start");
    let mut depth = 0usize;
    for (offset, character) in json[object_start..].char_indices() {
        match character {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let end = object_start + offset + character.len_utf8();
                    let mut normalized = String::with_capacity(json.len() - (end - start));
                    normalized.push_str(&json[..start]);
                    normalized.push_str(&json[end..]);
                    return normalized;
                }
            }
            _ => {}
        }
    }
    panic!("unterminated timings object");
}

fn fixture_root() -> PathBuf {
    repo_root().join("../npa/fixtures/npa-std")
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-cli crate lives under crates/")
        .to_path_buf()
}
