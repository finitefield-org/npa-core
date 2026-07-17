//! Implementation of `npa package export-candidate-metadata`.

use std::{fs, io, path::Path};

use npa_package::{
    format_package_hash, package_file_hash, parse_package_theorem_index_json, PackagePath,
    PackageTheoremIndex, PackageTheoremIndexEntry, PackageTheoremIndexKind,
};

use crate::args::PackageCandidateMetadataOptions;
use crate::diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{
    join_package_path, render_package_path, render_package_root, validate_package_output_path,
};
use crate::package::PACKAGE_MANIFEST_PATH;
use crate::package_artifacts::{PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH};

const COMMAND: &str = "package export-candidate-metadata";
const METADATA_SCHEMA_ID: &str = "npa.candidate-verification-metadata.v1";

/// Run `package export-candidate-metadata`.
pub fn run_package_export_candidate_metadata(
    options: PackageCandidateMetadataOptions,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let target = PackagePath::new(options.out.to_string_lossy().as_ref());
    if let Err(diagnostic) = validate_package_output_path(&options.common.root, &target, "--out") {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let target_display = render_package_path(&target);

    let manifest_bytes = match read_package_file(&options.common.root, PACKAGE_MANIFEST_PATH) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let lock_bytes = match read_package_file(&options.common.root, PACKAGE_LOCK_PATH) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let theorem_index_json =
        match read_package_file_to_string(&options.common.root, PACKAGE_THEOREM_INDEX_PATH) {
            Ok(source) => source,
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
            }
        };
    let theorem_index = match parse_package_theorem_index_json(&theorem_index_json) {
        Ok(index) => index,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::TheoremIndex,
                    error.reason_code.as_str(),
                )
                .with_path(PACKAGE_THEOREM_INDEX_PATH)
                .with_field(error.path)],
            );
        }
    };

    let Some(entry) = candidate_entry(&theorem_index, &options.module, &options.declaration) else {
        let module_exists = theorem_index
            .entries
            .iter()
            .any(|entry| entry.global_ref.module.as_dotted() == options.module);
        let reason = if module_exists {
            "candidate_metadata_declaration_missing"
        } else {
            "candidate_metadata_module_missing"
        };
        return CommandResult::failed(
            COMMAND,
            root_display,
            vec![
                CommandDiagnostic::error(DiagnosticKind::TheoremIndex, reason)
                    .with_path(PACKAGE_THEOREM_INDEX_PATH)
                    .with_module(options.module)
                    .with_field("declaration")
                    .with_actual_value(options.declaration),
            ],
        );
    };

    let metadata = candidate_metadata_json(
        entry,
        &format_package_hash(&package_file_hash(&manifest_bytes)),
        &format_package_hash(&package_file_hash(&lock_bytes)),
        &format_package_hash(&theorem_index.theorem_index_hash),
    );
    if let Err(diagnostic) = write_output(&options.common.root, &target, metadata.as_bytes()) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }

    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "candidate_verification_metadata".to_owned(),
        path: target_display,
    });
    result
}

fn candidate_entry<'a>(
    theorem_index: &'a PackageTheoremIndex,
    module: &str,
    declaration: &str,
) -> Option<&'a PackageTheoremIndexEntry> {
    theorem_index.entries.iter().find(|entry| {
        entry.kind == PackageTheoremIndexKind::Theorem
            && entry.global_ref.module.as_dotted() == module
            && entry.global_ref.name.as_dotted() == declaration
    })
}

fn candidate_metadata_json(
    entry: &PackageTheoremIndexEntry,
    package_manifest_hash: &str,
    package_lock_hash: &str,
    theorem_index_hash: &str,
) -> String {
    let module = entry.global_ref.module.as_dotted();
    let declaration = entry.global_ref.name.as_dotted();
    let statement_hash = format_package_hash(&entry.statement.core_hash);
    let export_hash = format_package_hash(&entry.global_ref.export_hash);
    let environment_hash = candidate_environment_hash(entry);
    let snapshot_hash = candidate_snapshot_hash(
        &module,
        &export_hash,
        package_manifest_hash,
        package_lock_hash,
        theorem_index_hash,
    );
    format!(
        "{{\n  \"schema_id\": \"{}\",\n  \"module_name\": {},\n  \"declaration_name\": {},\n  \"statement_hash\": \"{}\",\n  \"environment_hash\": \"{}\",\n  \"snapshot_hash\": \"{}\",\n  \"package_manifest_hash\": \"{}\",\n  \"package_lock_hash\": \"{}\",\n  \"theorem_package_hashes\": {{}},\n  \"export_hash\": \"{}\",\n  \"source_free_required\": true,\n  \"proof_evidence\": false\n}}\n",
        METADATA_SCHEMA_ID,
        json_string(&module),
        json_string(&declaration),
        statement_hash,
        environment_hash,
        snapshot_hash,
        package_manifest_hash,
        package_lock_hash,
        export_hash
    )
}

fn candidate_environment_hash(entry: &PackageTheoremIndexEntry) -> String {
    let mut body = String::new();
    body.push_str("schema:npa.candidate-environment.v1\n");
    body.push_str("module:");
    body.push_str(&entry.global_ref.module.as_dotted());
    body.push('\n');
    body.push_str("export_hash:");
    body.push_str(&format_package_hash(&entry.global_ref.export_hash));
    body.push('\n');
    body.push_str("certificate_hash:");
    body.push_str(&format_package_hash(&entry.global_ref.certificate_hash));
    body.push('\n');
    body.push_str("module_axiom_report_hash:");
    body.push_str(&format_package_hash(&entry.module_axiom_report_hash));
    body.push('\n');
    body.push_str("certificate:");
    body.push_str(entry.artifact.certificate.as_str());
    body.push('\n');
    format_package_hash(&package_file_hash(body.as_bytes()))
}

fn candidate_snapshot_hash(
    module: &str,
    export_hash: &str,
    package_manifest_hash: &str,
    package_lock_hash: &str,
    theorem_index_hash: &str,
) -> String {
    let mut body = String::new();
    body.push_str("schema:npa.candidate-snapshot.v1\n");
    body.push_str("module:");
    body.push_str(module);
    body.push('\n');
    body.push_str("export_hash:");
    body.push_str(export_hash);
    body.push('\n');
    body.push_str("package_manifest_hash:");
    body.push_str(package_manifest_hash);
    body.push('\n');
    body.push_str("package_lock_hash:");
    body.push_str(package_lock_hash);
    body.push('\n');
    body.push_str("theorem_index_hash:");
    body.push_str(theorem_index_hash);
    body.push('\n');
    format_package_hash(&package_file_hash(body.as_bytes()))
}

fn read_package_file(root: &Path, relative: &str) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let path = PackagePath::new(relative);
    let full_path = join_package_path(root, &path, relative)?;
    fs::read(full_path).map_err(|error| {
        if error.kind() == io::ErrorKind::NotFound {
            if let Some(diagnostic) = missing_prerequisite_diagnostic(relative) {
                return Box::new(diagnostic);
            }
        }
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_artifact_read_failed")
                .with_path(relative),
        )
    })
}

fn missing_prerequisite_diagnostic(relative: &str) -> Option<CommandDiagnostic> {
    match relative {
        PACKAGE_LOCK_PATH => Some(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "candidate_metadata_package_lock_missing",
            )
            .with_path(PACKAGE_LOCK_PATH)
            .with_expected_value("run `npa package build-certs --root <proofs> --json` first")
            .with_actual_value("missing"),
        ),
        PACKAGE_THEOREM_INDEX_PATH => Some(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "candidate_metadata_theorem_index_missing",
            )
            .with_path(PACKAGE_THEOREM_INDEX_PATH)
            .with_expected_value("run `npa package index --root <proofs> --json` first")
            .with_actual_value("missing"),
        ),
        _ => None,
    }
}

fn read_package_file_to_string(
    root: &Path,
    relative: &str,
) -> Result<String, Box<CommandDiagnostic>> {
    let bytes = read_package_file(root, relative)?;
    String::from_utf8(bytes).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_artifact_utf8_failed")
                .with_path(relative),
        )
    })
}

fn write_output(
    root: &Path,
    target: &PackagePath,
    contents: &[u8],
) -> Result<(), Box<CommandDiagnostic>> {
    let full_path = join_package_path(root, target, "/out")?;
    match fs::read(&full_path) {
        Ok(existing) if existing == contents => return Ok(()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "generated_artifact_read_failed",
                )
                .with_path(render_package_path(target)),
            ));
        }
    }
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).map_err(|_| {
            Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "generated_artifact_write_failed",
                )
                .with_path(render_package_path(target)),
            )
        })?;
    }
    fs::write(full_path, contents).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                "generated_artifact_write_failed",
            )
            .with_path(render_package_path(target)),
        )
    })
}

fn json_string(value: &str) -> String {
    let mut output = String::new();
    output.push('"');
    for ch in value.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            ch if ch.is_control() => output.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => output.push(ch),
        }
    }
    output.push('"');
    output
}
