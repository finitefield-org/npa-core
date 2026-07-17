use npa_cli::args::parse_cli_args;
use npa_cli::diagnostic::{
    CommandDiagnostic, CommandDiagnosticSourceContext, CommandExitCode, CommandResult,
    DiagnosticKind, PACKAGE_COMMAND_RESULT_SCHEMA,
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
fn package_cli_diagnostics_preserves_package_lock_usage_fields() {
    let invalid = parse_cli_args(["package", "verify-certs", "--package-lock=auto"])
        .expect_err("auto package-lock selection must be rejected");
    let invalid_result = CommandResult::usage_error("package verify-certs", ".", &invalid);

    assert_eq!(invalid_result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(
        invalid_result.render_human(),
        "package verify-certs: failed\nerror Usage invalid_flag_value field=--package-lock actual=auto"
    );
    let invalid_json = invalid_result.render_json();
    assert!(invalid_json.contains("\"reason_code\":\"invalid_flag_value\""));
    assert!(invalid_json.contains("\"field\":\"--package-lock\""));
    assert!(invalid_json.contains("\"actual_value\":\"auto\""));

    let unsupported = parse_cli_args([
        "package",
        "verify-certs",
        "--root=missing-package-root",
        "--package-lock=reconstructed",
        "--checker=external",
    ])
    .expect_err("external checking must reject reconstructed package-lock input");
    let unsupported_result = CommandResult::usage_error("package verify-certs", ".", &unsupported);

    assert_eq!(
        unsupported_result.render_human(),
        "package verify-certs: failed\nerror Usage unsupported_flag field=--package-lock actual=reconstructed;checker=external"
    );
    let unsupported_json = unsupported_result.render_json();
    assert!(unsupported_json.contains("\"reason_code\":\"unsupported_flag\""));
    assert!(unsupported_json.contains("\"field\":\"--package-lock\""));
    assert!(unsupported_json.contains("\"actual_value\":\"reconstructed;checker=external\""));
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

#[test]
fn command_diagnostic_source_context_construction_validates_and_exposes_fields() {
    assert!(CommandDiagnosticSourceContext::new("", 0, 0).is_none());
    assert!(CommandDiagnosticSourceContext::new("Proofs/A.npa", 2, 1).is_none());

    let source = CommandDiagnosticSourceContext::new("Proofs/A.npa", 0, 0)
        .expect("an empty byte range is valid")
        .with_declaration("")
        .with_declaration("Enumeration.Product.intro");
    assert_eq!(source.path(), "Proofs/A.npa");
    assert_eq!(source.start_byte(), 0);
    assert_eq!(source.end_byte(), 0);
    assert_eq!(source.declaration(), Some("Enumeration.Product.intro"));
}

#[test]
fn command_diagnostic_source_context_renders_exact_json_and_human_order() {
    let source =
        CommandDiagnosticSourceContext::new("Proofs/Ai/ExplicitFinite/source.npa", 4821, 4822)
            .unwrap()
            .with_declaration("explicit_finite_product_intro");
    let diagnostic = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
        .with_module("Proofs.Ai.ExplicitFinite")
        .with_path("modules[12].source")
        .with_field("elaborator")
        .with_actual_value("unannotated Human lambda binder requires an expected function type")
        .with_checker("frontend")
        .with_source(source);
    let result = CommandResult::failed("package build-certs", "<absolute-root>", vec![diagnostic]);

    assert_eq!(
        result.render_json(),
        "{\"schema\":\"npa.package.command_result.v0.3\",\"command\":\"package build-certs\",\"root\":\"<absolute-root>\",\"status\":\"failed\",\"diagnostics\":[{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"module\":\"Proofs.Ai.ExplicitFinite\",\"path\":\"modules[12].source\",\"field\":\"elaborator\",\"actual_value\":\"unannotated Human lambda binder requires an expected function type\",\"checker\":\"frontend\",\"source\":{\"path\":\"Proofs/Ai/ExplicitFinite/source.npa\",\"start_byte\":4821,\"end_byte\":4822,\"declaration\":\"explicit_finite_product_intro\"}}],\"artifacts\":[]}"
    );
    assert_eq!(
        result.render_human(),
        "package build-certs: failed\nerror Build build_failed path=modules[12].source module=Proofs.Ai.ExplicitFinite field=elaborator source=Proofs/Ai/ExplicitFinite/source.npa:byte[4821..4822] declaration=explicit_finite_product_intro actual=unannotated Human lambda binder requires an expected function type"
    );
}

#[test]
fn command_diagnostic_source_context_omits_optional_members_and_escapes_strings() {
    let source =
        CommandDiagnosticSourceContext::new("Proofs/quoted \"source\"\n.npa", 3, 3).unwrap();
    let diagnostic =
        CommandDiagnostic::info(DiagnosticKind::Build, "source_context").with_source(source);
    let result = CommandResult::failed("package build-certs", ".", vec![diagnostic]);
    let json = result.render_json();

    assert!(json.contains(
        "\"source\":{\"path\":\"Proofs/quoted \\\"source\\\"\\n.npa\",\"start_byte\":3,\"end_byte\":3}"
    ));
    assert!(!json.contains("\"declaration\""));

    let no_source = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed");
    assert!(no_source.source.is_none());
    assert!(
        !CommandResult::failed("package build-certs", ".", vec![no_source])
            .render_json()
            .contains("\"source\"")
    );
}
