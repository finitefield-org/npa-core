use std::fs;
use std::path::{Path, PathBuf};

use npa_cli::args::{PackageCommand, PackageCommonOptions, PackageInventoryInterfaceOptions};
use npa_cli::diagnostic::CommandStatus;
use npa_cli::package::run_package_command;

const REVISION: &str = "c5ea00351c28e24afc9f0f84379aa41082b1188f";
const REPOSITORY: &str = "https://github.com/leanprover-community/mathlib4";

fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/interface-inventory/lean4-mathlib4")
}

fn inventory_options(
    root: impl Into<PathBuf>,
    paths: &[&str],
    declarations: &[&str],
) -> PackageCommand {
    let mut common = PackageCommonOptions::default();
    common.root = root.into();
    common.json = true;
    PackageCommand::InventoryInterface(PackageInventoryInterfaceOptions {
        common,
        ecosystem: "lean4-mathlib4".to_owned(),
        repository: REPOSITORY.to_owned(),
        revision: REVISION.to_owned(),
        license: "Apache-2.0".to_owned(),
        license_note: None,
        paths: paths.iter().map(PathBuf::from).collect(),
        declarations: declarations.iter().map(ToString::to_string).collect(),
    })
}

fn result_for(
    root: impl Into<PathBuf>,
    paths: &[&str],
    declarations: &[&str],
) -> npa_cli::diagnostic::CommandResult {
    run_package_command(inventory_options(root, paths, declarations))
}

fn output_json(root: impl Into<PathBuf>, paths: &[&str], declarations: &[&str]) -> String {
    result_for(root, paths, declarations).render_json()
}

fn temp_root(label: &str) -> PathBuf {
    let base = fs::canonicalize(std::env::temp_dir()).unwrap_or_else(|_| PathBuf::from("/tmp"));
    base.join(format!(
        "npa-cli-interface-inventory-{label}-{}",
        std::process::id()
    ))
}

fn write_temp_source(label: &str, relative: &str, bytes: &[u8]) -> PathBuf {
    let root = temp_root(label);
    let _ = fs::remove_dir_all(&root);
    let path = root.join(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
    root
}

fn file_snapshot(root: &Path) -> Vec<(String, Vec<u8>)> {
    fn visit(root: &Path, current: &Path, output: &mut Vec<(String, Vec<u8>)>) {
        let mut entries = fs::read_dir(current)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect::<Vec<_>>();
        entries.sort();
        for path in entries {
            let metadata = fs::symlink_metadata(&path).unwrap();
            if metadata.is_dir() {
                visit(root, &path, output);
            } else if metadata.is_file() {
                output.push((
                    path.strip_prefix(root)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                    fs::read(path).unwrap(),
                ));
            }
        }
    }

    let mut output = Vec::new();
    visit(root, root, &mut output);
    output
}

#[test]
fn positive_interface_inventory_is_deterministic_provenance_complete_and_read_only() {
    let root = fixture_root();
    let before_fixture = file_snapshot(&root);
    let proposal_root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../npa-mathlib/interface-proposals");
    let before_proposals = file_snapshot(&proposal_root);

    let first = result_for(
        &root,
        &[
            "Mathlib/Logic/Function/Defs.lean",
            "Mathlib/Logic/Function/Iterate.lean",
        ],
        &["Function.comp_assoc", "Function.iterate_invariant"],
    );
    let second = result_for(
        &root,
        &[
            "Mathlib/Logic/Function/Defs.lean",
            "Mathlib/Logic/Function/Iterate.lean",
        ],
        &["Function.comp_assoc", "Function.iterate_invariant"],
    );
    assert_eq!(first, second);
    assert_eq!(first.status, CommandStatus::Passed);

    let output = first.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "ok");
    assert_eq!(output.pin.as_ref().unwrap().revision, REVISION);
    assert_eq!(output.pin.as_ref().unwrap().license, "Apache-2.0");
    assert_eq!(output.input_files.len(), 2);
    assert!(output.source_set_hash.is_some());
    assert_eq!(output.diagnostics, Vec::new());
    assert!(output
        .rows
        .iter()
        .any(|row| row.row_kind == "module_layout"));
    assert!(output
        .rows
        .iter()
        .any(|row| row.row_kind == "module_import"
            && row.import_visibility.as_deref() == Some("public")));
    assert!(output.rows.iter().any(|row| {
        row.row_kind == "declaration"
            && row.source_declaration.as_deref() == Some("Function.comp_assoc")
            && row.declaration_kind.as_deref() == Some("theorem")
    }));
    let rewrite = output.rows.iter().find(|row| {
        row.row_kind == "use_site"
            && row.referenced_declaration.as_deref() == Some("Function.comp_assoc")
            && row.usage_kind == "rewrite"
    });
    assert_eq!(rewrite.unwrap().usage_kind, "rewrite");
    assert!(output.rows.iter().any(|row| {
        row.row_kind == "use_site"
            && row.referenced_declaration.as_deref() == Some("Function.comp_assoc")
            && row.usage_kind == "direct_application"
    }));
    for row in &output.rows {
        assert_eq!(row.repository, REPOSITORY);
        assert_eq!(row.revision, REVISION);
        assert_eq!(row.revision_kind, "git_commit");
        assert_eq!(row.license, "Apache-2.0");
    }

    let json = first.render_json();
    assert!(json.starts_with(
        "{\"schema\":\"npa.mathlib.interface_inventory.v1\",\"proof_evidence\":false,\"status\":\"ok\""
    ));
    assert!(!json.contains(root.to_str().unwrap()));
    assert!(!json.contains("interface_status"));
    assert!(!json.contains("proof_evidence\":true"));
    assert_eq!(before_fixture, file_snapshot(&root));
    assert_eq!(before_proposals, file_snapshot(&proposal_root));
}

#[test]
fn invalid_interface_inventory_pins_and_paths_fail_closed_without_rows() {
    let mut floating_command = inventory_options(
        fixture_root(),
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let PackageCommand::InventoryInterface(ref mut options) = floating_command else {
        unreachable!();
    };
    options.revision = "main".to_owned();
    let floating = run_package_command(floating_command);
    let floating_output = floating.interface_inventory.as_deref().unwrap();
    assert_eq!(floating_output.status, "invalid");
    assert_eq!(floating_output.pin, None);
    assert!(floating_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "floating_revision"));
    assert!(floating_output.rows.is_empty());

    let mut missing_pin = inventory_options(
        fixture_root(),
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let PackageCommand::InventoryInterface(ref mut options) = missing_pin else {
        unreachable!();
    };
    options.repository.clear();
    options.revision.clear();
    options.license.clear();
    let missing_pin = run_package_command(missing_pin);
    let missing_output = missing_pin.interface_inventory.as_deref().unwrap();
    assert_eq!(missing_output.status, "invalid");
    assert!(missing_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "missing_repository"));
    assert!(missing_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "missing_revision"));
    assert!(missing_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "missing_license"));

    let escaped = result_for(
        fixture_root(),
        &["../outside.lean"],
        &["Function.comp_assoc"],
    );
    let escaped_output = escaped.interface_inventory.as_deref().unwrap();
    assert_eq!(escaped_output.status, "invalid");
    assert!(escaped_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "path_escape"));
    assert!(escaped_output.rows.is_empty());
}

#[cfg(unix)]
#[test]
fn interface_inventory_symlink_source_is_rejected_before_reading_target() {
    use std::os::unix::fs::symlink;

    let root = temp_root("symlink");
    let _ = fs::remove_dir_all(&root);
    let target = root.join("target.lean");
    let selected = root.join("Mathlib/Logic/Function/Defs.lean");
    fs::create_dir_all(selected.parent().unwrap()).unwrap();
    fs::write(
        &target,
        b"theorem Function.comp_assoc : True := by exact True.intro\n",
    )
    .unwrap();
    symlink(&target, &selected).unwrap();

    let result = result_for(
        &root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let output = result.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "invalid");
    assert!(output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "symlink_entry"));
    assert!(output.rows.is_empty());
    let _ = fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn interface_inventory_symlink_root_preserves_the_frozen_diagnostic() {
    use std::os::unix::fs::symlink;

    let target = write_temp_source(
        "root-symlink-target",
        "Mathlib/Logic/Function/Defs.lean",
        b"theorem Function.comp_assoc : True := by exact True.intro\n",
    );
    let root = temp_root("root-symlink");
    let _ = fs::remove_file(&root);
    let _ = fs::remove_dir_all(&root);
    symlink(&target, &root).unwrap();

    let result = result_for(
        &root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let output = result.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "invalid");
    assert!(output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "root_symlink"));
    assert!(output.rows.is_empty());

    fs::remove_file(root).unwrap();
    fs::remove_dir_all(target).unwrap();
}

#[test]
fn interface_inventory_oversized_source_is_rejected_before_source_scan() {
    let root = temp_root("oversized");
    let _ = fs::remove_dir_all(&root);
    let path = root.join("Mathlib/Logic/Function/Large.lean");
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, vec![b'a'; 16_777_217]).unwrap();

    let result = result_for(
        &root,
        &["Mathlib/Logic/Function/Large.lean"],
        &["Function.large"],
    );
    let output = result.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "invalid");
    assert!(output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "source_file_bytes_exceeded"));
    assert!(output.rows.is_empty());
    let _ = fs::remove_dir_all(root);
}

#[test]
fn interface_inventory_malformed_utf8_and_lean_source_are_diagnostics() {
    let utf8_root = write_temp_source(
        "invalid-utf8",
        "Mathlib/Logic/Function/Defs.lean",
        &[0xff, 0xfe],
    );
    let utf8_result = result_for(
        &utf8_root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let utf8_output = utf8_result.interface_inventory.as_deref().unwrap();
    assert!(utf8_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "invalid_utf8"));
    assert!(utf8_output.rows.is_empty());
    let _ = fs::remove_dir_all(utf8_root);

    let lean_root = write_temp_source(
        "invalid-lean",
        "Mathlib/Logic/Function/Defs.lean",
        b"theorem comp_assoc : \"unterminated\n",
    );
    let lean_result = result_for(
        &lean_root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["comp_assoc"],
    );
    let lean_output = lean_result.interface_inventory.as_deref().unwrap();
    assert!(lean_output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "malformed_comment_or_literal"));
    assert!(lean_output.rows.is_empty());
    let _ = fs::remove_dir_all(lean_root);
}

#[test]
fn interface_inventory_unsupported_inference_is_never_promoted_to_a_use_row() {
    let root = write_temp_source(
        "unsupported-inference",
        "Mathlib/Logic/Function/Defs.lean",
        b"namespace Function\ntheorem comp_assoc : True := by\n  exact infer_instance\nend Function\n",
    );
    let result = result_for(
        &root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let output = result.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "invalid");
    assert!(output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "unsupported_inference_use"));
    assert!(output.rows.is_empty());
    let _ = fs::remove_dir_all(root);
}

#[test]
fn interface_inventory_unsupported_commands_are_diagnostics() {
    let root = write_temp_source(
        "unsupported-command",
        "Mathlib/Logic/Function/Defs.lean",
        b"namespace Function\ntheorem comp_assoc : True := by\n  run_tac do pure ()\nend Function\n",
    );
    let result = result_for(
        &root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let output = result.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "invalid");
    assert!(output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "unsupported_command"));
    assert!(output.rows.is_empty());
    let _ = fs::remove_dir_all(root);
}

#[test]
fn interface_inventory_dot_notation_is_not_a_false_positive() {
    let root = write_temp_source(
        "dot-notation",
        "Mathlib/Logic/Function/Defs.lean",
        b"namespace Function\ntheorem comp_assoc : True := by\n  exact value.comp_assoc\nend Function\n",
    );
    let result = result_for(
        &root,
        &["Mathlib/Logic/Function/Defs.lean"],
        &["Function.comp_assoc"],
    );
    let output = result.interface_inventory.as_deref().unwrap();
    assert_eq!(output.status, "invalid");
    assert!(output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason == "unsupported_reference"));
    assert!(output.rows.is_empty());
    let _ = fs::remove_dir_all(root);
}

#[test]
fn interface_inventory_json_is_stable_for_the_exact_pilot_command_inputs() {
    let first = output_json(
        fixture_root(),
        &[
            "Mathlib/Logic/Function/Defs.lean",
            "Mathlib/Logic/Function/Iterate.lean",
        ],
        &["Function.comp_assoc", "Function.iterate_invariant"],
    );
    let second = output_json(
        fixture_root(),
        &[
            "Mathlib/Logic/Function/Defs.lean",
            "Mathlib/Logic/Function/Iterate.lean",
        ],
        &["Function.comp_assoc", "Function.iterate_invariant"],
    );
    assert_eq!(first, second);
    assert!(first.contains("\"source_set_hash\":\"sha256:"));
    assert!(first.contains("\"usage_kind\":\"rewrite\""));
}
