use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use npa_cert::{DeclPayload, Name};
use npa_cli::args::{
    parse_cli_args, CliAction, CliCommand, HelpTopic, PackageCheckInterfaceProposalSurfaceOptions,
    PackageCommand, PackageCommonOptions, UsageReason,
};
use npa_cli::package::run_package_command;
use npa_package::{format_package_hash, package_file_hash};

const TARGET_MODULE: &str = "Mathlib.Core.Reduction";
const TARGET_SOURCE: &str = "Mathlib/Core/Reduction/source.npa";
const TARGET_CERTIFICATE: &str = "Mathlib/Core/Reduction/certificate.npcert";
const PROPOSAL_PATH: &str = "Mathlib/Core/Reduction.toml";
const REVISION: &str = "c5ea00351c28e24afc9f0f84379aa41082b1188f";

#[derive(Clone, Debug)]
struct DeclarationSpec {
    name: String,
    kind: &'static str,
    signature: String,
    body: Option<String>,
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

fn package_fixture_root() -> PathBuf {
    repository_root().join("npa-core/testdata/package/npa-mathlib")
}

fn temp_root(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "npa-cli-interface-proposal-surface-{label}-{}",
        std::process::id()
    ))
}

fn toml_string(value: &str) -> String {
    format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\""))
}

fn source_specs(source: &str) -> (Vec<String>, Vec<DeclarationSpec>) {
    let lines = source.lines().collect::<Vec<_>>();
    let mut imports = Vec::new();
    let mut declarations = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let trimmed = lines[index].trim();
        if let Some(import) = trimmed.strip_prefix("import ") {
            imports.push(import.to_owned());
            index += 1;
            continue;
        }
        let Some((kind, rest)) = trimmed
            .strip_prefix("def ")
            .map(|rest| ("definition", rest))
            .or_else(|| {
                trimmed
                    .strip_prefix("theorem ")
                    .map(|rest| ("theorem", rest))
            })
        else {
            index += 1;
            continue;
        };
        let Some(colon) = rest.find(" :") else {
            panic!("fixture declaration has no signature separator: {trimmed}");
        };
        let name = rest[..colon]
            .split(".{")
            .next()
            .expect("declaration name")
            .to_owned();
        index += 1;
        let mut signature = String::new();
        while index < lines.len() {
            let part = lines[index].trim();
            if let Some(last) = part.strip_suffix(":=") {
                if !signature.is_empty() {
                    signature.push(' ');
                }
                signature.push_str(last.trim());
                index += 1;
                break;
            }
            if !signature.is_empty() {
                signature.push(' ');
            }
            signature.push_str(part);
            index += 1;
        }
        let mut body = String::new();
        while index < lines.len() {
            let part = lines[index].trim();
            if part.starts_with("def ") || part.starts_with("theorem ") {
                break;
            }
            if !part.is_empty() {
                if !body.is_empty() {
                    body.push(' ');
                }
                body.push_str(part);
            }
            index += 1;
        }
        declarations.push(DeclarationSpec {
            name,
            kind,
            signature,
            body: (kind == "definition").then_some(body),
        });
    }
    (imports, declarations)
}

fn proposal_bytes(imports: &[String], declarations: &[DeclarationSpec]) -> Vec<u8> {
    let mut output = String::new();
    writeln!(output, "schema = \"npa.mathlib.interface_proposal.v1\"").unwrap();
    writeln!(output, "proposal_id = \"{TARGET_MODULE}\"").unwrap();
    writeln!(output, "proposal_revision = 1").unwrap();
    writeln!(output, "module = \"{TARGET_MODULE}\"").unwrap();
    writeln!(output, "change_kind = \"add\"").unwrap();
    writeln!(output, "source_modules = []").unwrap();
    writeln!(output, "interface_status = \"adopted\"").unwrap();
    writeln!(output, "proof_evidence = false").unwrap();
    writeln!(
        output,
        "summary = \"The complete prepared reduction surface fixture.\""
    )
    .unwrap();
    writeln!(output, "scope = \"The selected target module surface.\"").unwrap();
    write!(output, "imports = [").unwrap();
    for (index, import) in imports.iter().enumerate() {
        if index > 0 {
            output.push_str(", ");
        }
        output.push_str(&toml_string(import));
    }
    writeln!(output, "]").unwrap();
    writeln!(output, "adoption_date = \"2026-08-02\"").unwrap();
    writeln!(output, "adoption_rationale = \"The fixture is independently generated from prepared target bytes.\"").unwrap();
    writeln!(
        output,
        "alternatives_review = \"The fixture has no unselected surface alternative.\""
    )
    .unwrap();
    writeln!(output, "supersedes = []").unwrap();

    for (index, declaration) in declarations.iter().enumerate() {
        let evidence_id = format!("fixture-observation-{index}");
        writeln!(output, "\n[[declarations]]").unwrap();
        writeln!(output, "name = {}", toml_string(&declaration.name)).unwrap();
        writeln!(output, "kind = \"{}\"", declaration.kind).unwrap();
        writeln!(output, "surface = \"public\"").unwrap();
        writeln!(
            output,
            "signature = {}",
            toml_string(&declaration.signature)
        )
        .unwrap();
        if let Some(body) = &declaration.body {
            writeln!(output, "body = {}", toml_string(body)).unwrap();
        }
        writeln!(
            output,
            "semantic_role = \"Prepared target declaration fixture.\""
        )
        .unwrap();
        writeln!(output, "depends_on = []").unwrap();
        writeln!(output, "evidence_ids = [\"{evidence_id}\"]").unwrap();
        if declaration.kind == "theorem" {
            writeln!(output, "proof_reference_ids = [\"{evidence_id}-proof\"]").unwrap();
        }
    }

    for (index, declaration) in declarations.iter().enumerate() {
        let evidence_id = format!("fixture-observation-{index}");
        writeln!(output, "\n[[observations]]").unwrap();
        writeln!(output, "id = \"{evidence_id}\"").unwrap();
        writeln!(output, "repository = \"https://example.invalid/npa-core\"").unwrap();
        writeln!(output, "revision_kind = \"git_commit\"").unwrap();
        writeln!(output, "revision = \"{REVISION}\"").unwrap();
        writeln!(output, "license = \"Apache-2.0\"").unwrap();
        writeln!(output, "path = \"{TARGET_SOURCE}\"").unwrap();
        writeln!(output, "source_module = \"{TARGET_MODULE}\"").unwrap();
        writeln!(
            output,
            "source_declaration = {}",
            toml_string(&declaration.name)
        )
        .unwrap();
        writeln!(output, "usage_kind = \"declaration\"").unwrap();
        writeln!(
            output,
            "notes = \"The prepared target declaration is used only as a local test fixture.\""
        )
        .unwrap();
        if declaration.kind == "theorem" {
            writeln!(output, "\n[[proof_references]]").unwrap();
            writeln!(output, "id = \"{evidence_id}-proof\"").unwrap();
            writeln!(output, "repository = \"https://example.invalid/npa-core\"").unwrap();
            writeln!(output, "revision_kind = \"git_commit\"").unwrap();
            writeln!(output, "revision = \"{REVISION}\"").unwrap();
            writeln!(output, "license = \"Apache-2.0\"").unwrap();
            writeln!(output, "path = \"{TARGET_SOURCE}\"").unwrap();
            writeln!(output, "source_module = \"{TARGET_MODULE}\"").unwrap();
            writeln!(
                output,
                "source_declaration = {}",
                toml_string(&declaration.name)
            )
            .unwrap();
            writeln!(output, "reference_role = \"proof_structure\"").unwrap();
            writeln!(output, "notes = \"The proof reference is metadata only.\"").unwrap();
        }
    }
    output.into_bytes()
}

fn fixture_proposal() -> (Vec<u8>, Vec<DeclarationSpec>, Vec<String>) {
    let source = fs::read_to_string(package_fixture_root().join(TARGET_SOURCE)).unwrap();
    let (imports, declarations) = source_specs(&source);
    let certificate = npa_cert::decode_module_cert(
        &fs::read(package_fixture_root().join(TARGET_CERTIFICATE)).unwrap(),
    )
    .unwrap();
    let mut by_name = declarations
        .into_iter()
        .map(|declaration| (declaration.name.clone(), declaration))
        .collect::<std::collections::BTreeMap<_, _>>();
    let declarations = certificate
        .declarations
        .iter()
        .map(|declaration| match &declaration.decl {
            DeclPayload::Axiom { name, .. }
            | DeclPayload::AxiomConstrained { name, .. }
            | DeclPayload::Def { name, .. }
            | DeclPayload::DefConstrained { name, .. }
            | DeclPayload::Theorem { name, .. }
            | DeclPayload::TheoremConstrained { name, .. }
            | DeclPayload::Inductive { name, .. }
            | DeclPayload::InductiveConstrained { name, .. }
            | DeclPayload::MutualInductiveBlock { name, .. } => {
                certificate.name_table[*name].as_dotted()
            }
        })
        .map(|name| by_name.remove(&name).unwrap())
        .collect::<Vec<_>>();
    assert!(by_name.is_empty());
    (
        proposal_bytes(&imports, &declarations),
        declarations,
        imports,
    )
}

fn copy_file(root: &Path, relative: &str) {
    let source = package_fixture_root().join(relative);
    let destination = root.join(relative);
    fs::create_dir_all(destination.parent().unwrap()).unwrap();
    fs::copy(source, destination).unwrap();
}

fn make_root(label: &str) -> PathBuf {
    let root = temp_root(label);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    copy_file(&root, "npa-package.toml");
    copy_file(&root, TARGET_SOURCE);
    copy_file(&root, TARGET_CERTIFICATE);
    copy_file(&root, "vendor/npa-std/Std/Nat/Basic/certificate.npcert");
    root
}

fn run_surface(root: &Path, proposal: &[u8]) -> npa_cli::diagnostic::CommandResult {
    run_surface_with_hash(
        root,
        proposal,
        &format_package_hash(&package_file_hash(proposal)),
    )
}

fn run_surface_with_hash(
    root: &Path,
    proposal: &[u8],
    proposal_sha256: &str,
) -> npa_cli::diagnostic::CommandResult {
    let proposal_path = root.join("interface-proposals").join(PROPOSAL_PATH);
    fs::create_dir_all(proposal_path.parent().unwrap()).unwrap();
    fs::write(&proposal_path, proposal).unwrap();
    let mut common = PackageCommonOptions::default();
    common.root = root.to_owned();
    common.json = true;
    run_package_command(PackageCommand::CheckInterfaceProposalSurface(
        PackageCheckInterfaceProposalSurfaceOptions {
            common,
            proposal_root: Some(PathBuf::from("interface-proposals")),
            proposal_path: PathBuf::from(PROPOSAL_PATH),
            proposal_sha256: proposal_sha256.to_owned(),
            target_module: Name::from_dotted(TARGET_MODULE),
        },
    ))
}

fn reasons(result: &npa_cli::diagnostic::CommandResult) -> Vec<String> {
    result
        .interface_proposal_surface
        .as_ref()
        .unwrap()
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.reason.clone())
        .collect()
}

fn finish_root(root: PathBuf) {
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn parser_and_help_follow_the_frozen_contract() {
    let action = parse_cli_args([
        "package",
        "check-interface-proposal-surface",
        "--root=package",
        "--proposal-root",
        "interface-proposals",
        "--proposal-path",
        PROPOSAL_PATH,
        "--proposal-sha256=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--target-module",
        TARGET_MODULE,
        "--json",
    ])
    .unwrap();
    let CliAction::Run(CliCommand::Package(PackageCommand::CheckInterfaceProposalSurface(options))) =
        action
    else {
        panic!("expected surface command");
    };
    assert_eq!(options.common.root, PathBuf::from("package"));
    assert_eq!(
        options.proposal_root,
        Some(PathBuf::from("interface-proposals"))
    );
    assert_eq!(options.proposal_path, PathBuf::from(PROPOSAL_PATH));
    assert_eq!(options.target_module.as_dotted(), TARGET_MODULE);

    assert_eq!(
        parse_cli_args(["package", "check-interface-proposal-surface", "--help"]).unwrap(),
        CliAction::Help(HelpTopic::PackageCheckInterfaceProposalSurface)
    );
    let error = parse_cli_args([
        "package",
        "check-interface-proposal-surface",
        "--proposal-path",
        PROPOSAL_PATH,
        "--proposal-sha256",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "--target-module",
        TARGET_MODULE,
    ])
    .unwrap_err();
    assert_eq!(error.reason, UsageReason::MissingRequiredFlag);
    assert_eq!(error.flag.as_deref(), Some("--json"));
}

#[test]
fn exact_parity_is_stable_and_non_mutating() {
    let (proposal, _, _) = fixture_proposal();
    let root = make_root("parity");
    let proposal_file = root.join("interface-proposals").join(PROPOSAL_PATH);
    let before_target = fs::read(root.join(TARGET_SOURCE)).unwrap();
    let before_certificate = fs::read(root.join(TARGET_CERTIFICATE)).unwrap();
    let first = run_surface(&root, &proposal);
    let first_json = first.render_json();
    let second = run_surface(&root, &proposal);
    let second_json = second.render_json();

    assert_eq!(first.exit_code().as_u8(), 0, "{}", first_json);
    assert_eq!(
        first.interface_proposal_surface.as_ref().unwrap().status,
        "parity"
    );
    assert_eq!(first_json, second_json);
    assert!(first_json.contains("\"proof_evidence\":false"));
    assert!(!first_json.contains(root.to_str().unwrap()));
    assert_eq!(proposal, fs::read(&proposal_file).unwrap());
    assert_eq!(before_target, fs::read(root.join(TARGET_SOURCE)).unwrap());
    assert_eq!(
        before_certificate,
        fs::read(root.join(TARGET_CERTIFICATE)).unwrap()
    );
    finish_root(root);
}

#[test]
fn proposal_hash_mismatch_is_invalid_before_target_comparison() {
    let (proposal, _, _) = fixture_proposal();
    let root = make_root("hash-mismatch");
    let result = run_surface_with_hash(
        &root,
        &proposal,
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    );
    let json = result.render_json();
    assert_eq!(result.exit_code().as_u8(), 1, "{json}");
    assert_eq!(
        result.interface_proposal_surface.as_ref().unwrap().status,
        "invalid"
    );
    assert!(reasons(&result).contains(&"proposal_hash_mismatch".to_owned()));
    assert!(json.contains("\"module\":null"));
    finish_root(root);
}

#[test]
fn invalid_absolute_proposal_paths_are_sanitized() {
    let mut common = PackageCommonOptions::default();
    common.root = PathBuf::from("/tmp/surface-package");
    common.json = true;
    let result = run_package_command(PackageCommand::CheckInterfaceProposalSurface(
        PackageCheckInterfaceProposalSurfaceOptions {
            common,
            proposal_root: None,
            proposal_path: PathBuf::from("/tmp/outside.toml"),
            proposal_sha256:
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_owned(),
            target_module: Name::from_dotted(TARGET_MODULE),
        },
    ));
    let json = result.render_json();
    assert_eq!(result.exit_code().as_u8(), 1, "{json}");
    assert!(json.contains("<absolute-path>"));
    assert!(!json.contains("/tmp/outside.toml"));
}

#[test]
fn axis_fixtures_report_designated_drift_reasons() {
    let (_, declarations, imports) = fixture_proposal();
    let definition_index = declarations
        .iter()
        .position(|declaration| declaration.name == "reduction_id_nat")
        .unwrap();

    let mut cases = Vec::new();
    let mut names_changed = declarations.clone();
    names_changed[0].name = "reduction_id_nat_renamed".to_owned();
    cases.push((
        "names",
        proposal_bytes(&imports, &names_changed),
        "declaration_name_drift",
    ));

    let mut reordered_declarations = declarations.clone();
    reordered_declarations.swap(0, 1);
    let reordered = proposal_bytes(&imports, &reordered_declarations);
    cases.push(("order", reordered, "declaration_order_drift"));

    let mut kind_changed = declarations.clone();
    kind_changed[definition_index].kind = "theorem";
    kind_changed[definition_index].body = None;
    cases.push((
        "kind",
        proposal_bytes(&imports, &kind_changed),
        "declaration_kind_drift",
    ));

    let surface_changed = declarations.clone();
    let mut surface = proposal_bytes(&imports, &surface_changed);
    let public = b"surface = \"public\"";
    let support = b"surface = \"support\"";
    let position = surface
        .windows(public.len())
        .position(|window| window == public)
        .unwrap();
    surface.splice(position..position + public.len(), support.iter().copied());
    surface = {
        let mut text = String::from_utf8(surface).unwrap();
        text = text.replacen(
            "semantic_role = \"Prepared target declaration fixture.\"",
            "semantic_role = \"Prepared target declaration fixture.\"\nsupport_rationale = \"Support closure fixture.\"",
            1,
        );
        let marker = "depends_on = []";
        let first = text.find(marker).unwrap();
        let second = text[first + marker.len()..].find(marker).unwrap() + first + marker.len();
        let dependency = format!("depends_on = [{}]", toml_string(&surface_changed[0].name));
        text.replace_range(second..second + marker.len(), &dependency);
        text.into_bytes()
    };
    cases.push(("surface", surface, "declaration_surface_drift"));

    let mut signature_changed = declarations.clone();
    let signature_index = signature_changed
        .iter()
        .position(|declaration| declaration.name == "beta_id_nat")
        .unwrap();
    signature_changed[signature_index].signature =
        "forall (n : Nat), forall (m : Nat), Nat".to_owned();
    cases.push((
        "signature",
        proposal_bytes(&imports, &signature_changed),
        "signature_drift",
    ));

    let mut body_changed = declarations.clone();
    body_changed[definition_index].body = Some("fun n => Nat.zero".to_owned());
    cases.push((
        "body",
        proposal_bytes(&imports, &body_changed),
        "definition_body_drift",
    ));

    let mut imports_changed = imports.clone();
    imports_changed.clear();
    cases.push((
        "imports",
        proposal_bytes(&imports_changed, &declarations),
        "direct_imports_drift",
    ));

    for (label, proposal, expected_reason) in cases {
        let root = make_root(label);
        let result = run_surface(&root, &proposal);
        let json = result.render_json();
        assert_eq!(result.exit_code().as_u8(), 1, "{label}: {json}");
        assert_eq!(
            result.interface_proposal_surface.as_ref().unwrap().status,
            "drift",
            "{label}: {json}"
        );
        assert!(
            reasons(&result).contains(&expected_reason.to_owned()),
            "{label}: {json}"
        );
        if label == "surface" {
            assert!(
                reasons(&result).contains(&"exported_support_removed".to_owned()),
                "{label}: {json}"
            );
        }
        finish_root(root);
    }
}
