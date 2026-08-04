use std::fs;
use std::path::{Path, PathBuf};

use npa_cli::args::{PackageCheckInterfaceProposalsOptions, PackageCommand, PackageCommonOptions};
use npa_cli::package::run_package_command;
use npa_package::{
    format_package_hash, interface_proposal_file_hash, package_file_hash,
    parse_and_validate_interface_proposal, InterfaceProposalErrorReason,
};

fn mathlib_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../npa-mathlib")
}

fn proposal_source() -> PathBuf {
    mathlib_root().join("interface-proposals/Mathlib/Logic/Function/Basic.toml")
}

fn compact_fixture_root(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/package")
        .join(name)
}

fn fixture_snapshot(root: &Path) -> Vec<(String, Vec<u8>)> {
    fn visit(root: &Path, current: &Path, output: &mut Vec<(String, Vec<u8>)>) {
        let mut entries = fs::read_dir(current)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect::<Vec<_>>();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                visit(root, &path, output);
            } else {
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

fn temp_root(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "npa-cli-interface-proposals-{label}-{}",
        std::process::id()
    ))
}

fn create_fixture(label: &str, proposal_bytes: &[u8]) -> PathBuf {
    let root = temp_root(label);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("interface-proposals/Mathlib/Logic/Function")).unwrap();
    fs::copy(
        mathlib_root().join("npa-package.toml"),
        root.join("npa-package.toml"),
    )
    .unwrap();
    fs::write(
        root.join("interface-proposals/Mathlib/Logic/Function/Basic.toml"),
        proposal_bytes,
    )
    .unwrap();
    root
}

fn options(
    root: impl Into<PathBuf>,
    proposal_root: Option<PathBuf>,
    previous_proposal_root: Option<PathBuf>,
    json: bool,
) -> PackageCommand {
    let mut common = PackageCommonOptions::default();
    common.root = root.into();
    common.json = json;
    PackageCommand::CheckInterfaceProposals(PackageCheckInterfaceProposalsOptions {
        common,
        proposal_root,
        previous_proposal_root,
    })
}

fn result_json(command: PackageCommand) -> String {
    run_package_command(command).render_json()
}

#[test]
fn pilot_json_is_stable_and_has_no_absolute_paths() {
    let root = mathlib_root().canonicalize().unwrap();
    let first = result_json(options(
        &root,
        Some(PathBuf::from("interface-proposals")),
        None,
        true,
    ));
    let second = result_json(options(
        &root,
        Some(PathBuf::from("interface-proposals")),
        None,
        true,
    ));

    assert_eq!(first, second);
    assert!(first.contains("\"schema\":\"npa.mathlib.interface_proposal_check.v1\""));
    assert!(first.contains("\"proof_evidence\":false"));
    assert!(first.contains("\"status\":\"ok\""));
    assert!(first.contains("\"proposal_count\":3"));
    assert!(first.contains("\"interface_status\":\"adopted\""));
    assert!(!first.contains(root.to_str().unwrap()));
}

#[test]
fn previous_snapshot_mode_checks_identical_valid_snapshots_without_git() {
    let root = mathlib_root().canonicalize().unwrap();
    let previous_root = temp_root("previous");
    let _ = fs::remove_dir_all(&previous_root);
    let current_proposal_root = root.join("interface-proposals");
    for (relative_path, bytes) in fixture_snapshot(&current_proposal_root) {
        let target = previous_root.join(relative_path);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(target, bytes).unwrap();
    }

    let output = result_json(options(
        &root,
        Some(PathBuf::from("interface-proposals")),
        Some(previous_root.clone()),
        true,
    ));

    assert!(output.contains("\"status\":\"ok\""));
    assert!(output.contains("\"previous\":{"));
    assert!(output.contains("\"proposal_set_hash\":\"sha256:"));
    assert!(!output.contains(previous_root.to_str().unwrap()));
    fs::remove_dir_all(previous_root).unwrap();
}

#[test]
fn identical_current_and_previous_roots_are_a_stable_package_failure() {
    let root = mathlib_root().canonicalize().unwrap();
    let result = run_package_command(options(
        &root,
        Some(PathBuf::from("interface-proposals")),
        Some(PathBuf::from("interface-proposals")),
        true,
    ));
    assert_eq!(result.exit_code().as_u8(), 1);
    let output = result.render_json();
    assert!(output.contains("\"status\":\"invalid\""));
    assert!(output.contains("previous_root_same_as_current"));
    assert!(!output.contains(root.to_str().unwrap()));
}

#[test]
fn malformed_proposal_returns_null_metadata_and_does_not_write() {
    let mut bytes = fs::read(proposal_source()).unwrap();
    bytes.extend_from_slice(b"\nunknown_field = true\n");
    let root = create_fixture("malformed", &bytes);
    let proposal = root.join("interface-proposals/Mathlib/Logic/Function/Basic.toml");
    let before = fs::read(&proposal).unwrap();

    let result = run_package_command(options(
        &root,
        Some(PathBuf::from("interface-proposals")),
        None,
        true,
    ));
    let output = result.render_json();

    assert_eq!(result.exit_code().as_u8(), 1);
    assert!(output.contains("\"status\":\"invalid\""));
    assert!(output.contains("\"proposal_id\":null"));
    assert!(output.contains("\"reason\":\"unknown_field\""));
    assert_eq!(before, fs::read(&proposal).unwrap());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn human_output_states_the_curation_boundary() {
    let result = run_package_command(options(
        mathlib_root(),
        Some(PathBuf::from("interface-proposals")),
        None,
        false,
    ));
    let human = result.render_human();
    assert!(human.contains("network-free curation validation"));
    assert!(human.contains("not proof verification or catalog admission"));
    assert!(human.contains("immediately preceding validated snapshot"));
    assert!(human.contains("locally detectable per-record continuity"));
}

#[test]
fn compact_fixture_command_is_local_network_free_and_no_write() {
    let root = compact_fixture_root("interface-proposals-valid");
    let before = fixture_snapshot(&root);
    let result = run_package_command(options(&root, Some(PathBuf::from("proposals")), None, true));
    let output = result.render_json();

    assert_eq!(result.exit_code().as_u8(), 0);
    assert!(output.contains("\"status\":\"ok\""));
    assert!(output.contains("\"interface_status\":\"observed\""));
    assert!(output.contains("\"proof_evidence\":false"));
    assert!(!output.contains("example.invalid"));
    assert!(!output.contains(".npcert"));
    assert!(!output.contains("source.npa"));
    assert_eq!(before, fixture_snapshot(&root));
}

#[test]
fn compact_invalid_fixture_rejects_proof_boundary_metadata() {
    let root = compact_fixture_root("interface-proposals-invalid");
    let result = run_package_command(options(&root, Some(PathBuf::from("proposals")), None, true));
    let output = result.render_json();

    assert_eq!(result.exit_code().as_u8(), 1);
    assert!(output.contains("\"status\":\"invalid\""));
    assert!(output.contains("proof_evidence_not_false"));
    assert!(output.contains("\"proof_evidence\":false"));
}

#[test]
fn public_security_cases_and_hash_vectors_are_explicit() {
    let valid_proposal = compact_fixture_root("interface-proposals-valid")
        .join("proposals/Mathlib/Fixture/Observed.toml");
    let source = fs::read_to_string(valid_proposal).unwrap();

    let floating_revision = source.replace(
        "revision = \"c5ea00351c28e24afc9f0f84379aa41082b1188f\"",
        "revision = \"HEAD\"",
    );
    assert_eq!(
        parse_and_validate_interface_proposal(floating_revision.as_bytes())
            .unwrap_err()
            .reason_code,
        InterfaceProposalErrorReason::FloatingRevision
    );

    let missing_license = source.replace("license = \"Apache-2.0\"", "license = \"UNKNOWN\"");
    assert_eq!(
        parse_and_validate_interface_proposal(missing_license.as_bytes())
            .unwrap_err()
            .reason_code,
        InterfaceProposalErrorReason::LicenseUnknownWithoutNote
    );
    assert_eq!(
        parse_and_validate_interface_proposal(&[0xff, 0xfe])
            .unwrap_err()
            .reason_code,
        InterfaceProposalErrorReason::InvalidUtf8
    );

    assert_eq!(
        format_package_hash(&interface_proposal_file_hash(b"abc")),
        "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    let proposal_set_rows = b"npa.mathlib.interface_proposal_set.v1\nMathlib/Logic/A.toml\tsha256:87428fc522803d31065e7bce3cf03fe475096631e5e07bbd7a0fde60c4cf25c7\nMathlib/Z.toml\tsha256:c865f6c5ab8d1b0bcd383a5e1e3879d22681c96bf462c269b7581d523fbe70ab\n";
    assert_eq!(
        format_package_hash(&package_file_hash(proposal_set_rows)),
        "sha256:52f6b60fcea9ff2a64d94497500e9f9f0ce8a448c0aacf0adf1990e1a7a1f978"
    );
}
