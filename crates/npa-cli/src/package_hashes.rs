//! Implementation of `npa package check-hashes`.

use std::fs;

use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_package_lock_json, PackageHash, PackagePath,
};

use crate::args::PackageCommonOptions;
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{join_package_path, render_package_path};
use crate::package::{load_package_root, LoadedPackageRoot};

const COMMAND: &str = "package check-hashes";
const PACKAGE_LOCK_PATH: &str = "generated/package-lock.json";

/// Run checked-in artifact freshness checks.
///
/// This command reads the package manifest, local source files, local and
/// external certificate files, and `generated/package-lock.json`. It does not
/// run the frontend, either checker, tactics, AI, registry lookup, or write
/// artifacts.
pub fn run_package_check_hashes(options: PackageCommonOptions) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_source_hashes(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    let regenerated_lock = match build_package_lock_from_package_root(
        &loaded.validated,
        &loaded.root,
        loaded.manifest_path.clone(),
    ) {
        Ok(lock) => lock,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![CommandDiagnostic::from_package_lock_error(&error)],
            );
        }
    };

    let regenerated_lock_json = match regenerated_lock.canonical_json() {
        Ok(json) => json,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                loaded.root_display,
                vec![CommandDiagnostic::from_package_lock_error(&error)],
            );
        }
    };

    if let Some(diagnostic) = check_package_lock(&loaded, &regenerated_lock_json) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn check_source_hashes(loaded: &LoadedPackageRoot) -> Option<CommandDiagnostic> {
    for (index, module) in loaded.validated.manifest().modules.iter().enumerate() {
        let path = match join_package_path(
            &loaded.root,
            &module.source,
            format!("modules[{index}].source"),
        ) {
            Ok(path) => path,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "source_missing")
                        .with_path(render_package_path(&module.source)),
                );
            }
        };
        let actual = package_file_hash(&bytes);
        if actual != module.expected_source_hash {
            return Some(hash_mismatch(
                "source_hash_mismatch",
                render_package_path(&module.source),
                "expected_source_hash",
                module.expected_source_hash,
                actual,
            ));
        }
    }
    None
}

fn check_package_lock(
    loaded: &LoadedPackageRoot,
    regenerated_lock_json: &str,
) -> Option<CommandDiagnostic> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let full_lock_path = match join_package_path(&loaded.root, &lock_path, "package_lock.path") {
        Ok(path) => path,
        Err(diagnostic) => return Some(*diagnostic),
    };
    let lock_source = match fs::read_to_string(&full_lock_path) {
        Ok(source) => source,
        Err(_) => {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::PackageLock, "package_lock_missing")
                    .with_path(PACKAGE_LOCK_PATH),
            );
        }
    };
    if let Err(error) = parse_package_lock_json(&lock_source) {
        return Some(
            CommandDiagnostic::from_package_lock_error(&error).with_path(PACKAGE_LOCK_PATH),
        );
    }
    if lock_source != regenerated_lock_json {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "package_lock_stale")
                .with_path(PACKAGE_LOCK_PATH)
                .with_hashes(
                    format_package_hash(&package_file_hash(regenerated_lock_json.as_bytes())),
                    format_package_hash(&package_file_hash(lock_source.as_bytes())),
                ),
        );
    }
    None
}

fn hash_mismatch(
    reason_code: &'static str,
    path: String,
    field: &'static str,
    expected: PackageHash,
    actual: PackageHash,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::HashMismatch, reason_code)
        .with_path(path)
        .with_field(field)
        .with_hashes(format_package_hash(&expected), format_package_hash(&actual))
}
