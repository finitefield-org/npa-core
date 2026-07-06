use npa_cli::args::parse_cli_args;
use npa_cli::diagnostic::{
    CommandDiagnostic, CommandExitCode, CommandResult, DiagnosticKind,
    PACKAGE_COMMAND_RESULT_SCHEMA,
};

#[test]
fn package_cli_diagnostics_renders_stable_success_json() {
    let result = CommandResult::passed("package check", "proofs");

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(
        result.render_json(),
        format!(
            "{{\"schema\":\"{PACKAGE_COMMAND_RESULT_SCHEMA}\",\"command\":\"package check\",\"root\":\"proofs\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}}"
        )
    );
}

#[test]
fn package_cli_diagnostics_maps_usage_errors_to_exit_two() {
    let error = parse_cli_args(["package", "verify-certs", "--checker", "external"]).unwrap_err();
    let result = CommandResult::usage_error("package verify-certs", ".", &error);

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    let json = result.render_json();
    assert!(json.contains("\"kind\":\"Usage\""));
    assert!(json.contains("\"reason_code\":\"missing_required_flag\""));
    assert!(json.contains("\"field\":\"--runner-policy\""));
    assert!(!json.contains("\"actual_value\""));
}

#[test]
fn package_cli_diagnostics_preserves_manifest_error_fields() {
    let report = npa_package::validate_manifest_source_report(
        r#"schema = "npa.package.v0.1"
trusted_status = "verified_by_certificate"
"#,
    );
    let error = report.first_error().unwrap();
    let diagnostic = CommandDiagnostic::from_package_manifest_error(error);

    assert_eq!(diagnostic.kind, DiagnosticKind::PackageManifest);
    assert_eq!(diagnostic.reason_code, "unknown_field");
    assert_eq!(diagnostic.path.as_deref(), Some("$"));
    assert_eq!(diagnostic.field.as_deref(), Some("trusted_status"));
    assert_eq!(diagnostic.expected_value, None);
    assert_eq!(diagnostic.actual_value, None);
}

#[test]
fn package_cli_diagnostics_preserves_package_lock_module_context() {
    let error = npa_package::PackageLockError::manifest_import_missing(
        "entries[263].imports[24].module",
        "Std.Logic.Eq",
    )
    .with_module("Proofs.Ai.Foundation");

    let diagnostic = CommandDiagnostic::from_package_lock_error(&error);

    assert_eq!(diagnostic.kind, DiagnosticKind::PackageGraph);
    assert_eq!(diagnostic.reason_code, "manifest_import_missing");
    assert_eq!(
        diagnostic.path.as_deref(),
        Some("entries[263].imports[24].module")
    );
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Foundation"));
    assert_eq!(diagnostic.field.as_deref(), Some("module"));

    let result = CommandResult::failed("package verify", "proofs", vec![diagnostic]);
    assert!(result
        .render_json()
        .contains("\"module\":\"Proofs.Ai.Foundation\""));
    assert!(result
        .render_human()
        .contains("module=Proofs.Ai.Foundation"));
}

#[test]
fn package_cli_diagnostics_json_escapes_strings_without_host_data() {
    let diagnostic = CommandDiagnostic::error(DiagnosticKind::PackageManifest, "manifest_missing")
        .with_path("npa-package.toml")
        .with_actual_value("line\nquoted \"value\"");
    let result = CommandResult::failed("package check", "<absolute-root>", vec![diagnostic]);

    let json = result.render_json();
    assert!(json.contains("\"root\":\"<absolute-root>\""));
    assert!(json.contains("line\\nquoted \\\"value\\\""));
    assert!(!json.contains("/tmp/"));
    assert!(!json.contains("/root/"));
}
