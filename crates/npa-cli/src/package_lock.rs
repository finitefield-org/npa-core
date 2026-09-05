//! Implementation of `npa package lock`.

use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_package_lock_json, PackagePath,
};

use crate::args::{PackageCommonOptions, PackageLockCommand};
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::generated_artifact_writer::{
    read_package_generated_artifact_no_follow, write_package_generated_artifact_under_lock,
};
use crate::package::{load_package_root, LoadedPackageRoot};
use crate::package_artifacts::PACKAGE_LOCK_PATH;
use crate::package_promotion_transaction::TargetLock;

const COMMAND_CHECK: &str = "package lock check";
const COMMAND_WRITE: &str = "package lock write";

/// Run a package-lock command.
pub fn run_package_lock_command(command: PackageLockCommand) -> CommandResult {
    match command {
        PackageLockCommand::Check(options) => run_package_lock_check(options),
        PackageLockCommand::Write(options) => run_package_lock_write(options),
    }
}

/// Run `package lock check`.
pub fn run_package_lock_check(options: PackageCommonOptions) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND_CHECK) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    let regenerated_lock_json = match regenerated_package_lock_json(&loaded, COMMAND_CHECK) {
        Ok(json) => json,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_package_lock(&loaded, &regenerated_lock_json) {
        return CommandResult::failed(COMMAND_CHECK, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND_CHECK, loaded.root_display)
}

/// Run `package lock write`.
pub fn run_package_lock_write(options: PackageCommonOptions) -> CommandResult {
    let mutation_lock = match TargetLock::acquire(&options.root) {
        Ok(lock) => lock,
        Err(_) => {
            return CommandResult::failed(
                COMMAND_WRITE,
                crate::fs::render_package_root(&options.root),
                vec![CommandDiagnostic::error(
                    DiagnosticKind::ArtifactIo,
                    "package_lock_concurrent_update",
                )
                .with_path(PACKAGE_LOCK_PATH)],
            )
        }
    };
    let loaded = match load_package_root(&options.root, COMMAND_WRITE) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    let regenerated_lock_json = match regenerated_package_lock_json(&loaded, COMMAND_WRITE) {
        Ok(json) => json,
        Err(result) => return result,
    };

    if let Some(diagnostic) =
        write_package_lock(&loaded, regenerated_lock_json.as_bytes(), &mutation_lock)
    {
        return CommandResult::failed(COMMAND_WRITE, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND_WRITE, loaded.root_display)
}

fn regenerated_package_lock_json(
    loaded: &LoadedPackageRoot,
    command: &'static str,
) -> Result<String, CommandResult> {
    let regenerated_lock = match build_package_lock_from_package_root(
        &loaded.validated,
        &loaded.root,
        loaded.manifest_path.clone(),
    ) {
        Ok(lock) => lock,
        Err(error) => {
            return Err(CommandResult::failed(
                command,
                loaded.root_display.clone(),
                vec![CommandDiagnostic::from_package_lock_error(&error)],
            ));
        }
    };

    regenerated_lock.canonical_json().map_err(|error| {
        CommandResult::failed(
            command,
            loaded.root_display.clone(),
            vec![CommandDiagnostic::from_package_lock_error(&error)],
        )
    })
}

fn check_package_lock(
    loaded: &LoadedPackageRoot,
    regenerated_lock_json: &str,
) -> Option<CommandDiagnostic> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let lock_source = match read_package_generated_artifact_no_follow(&loaded.root, &lock_path)
        .ok()
        .and_then(|bytes| String::from_utf8(bytes).ok())
    {
        Some(source) => source,
        None => {
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

fn write_package_lock(
    loaded: &LoadedPackageRoot,
    bytes: &[u8],
    mutation_lock: &TargetLock,
) -> Option<CommandDiagnostic> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    write_package_generated_artifact_under_lock(&loaded.root, &lock_path, bytes, mutation_lock)
        .err()
        .map(|_| write_artifact_diagnostic(&lock_path))
}

fn write_artifact_diagnostic(path: &PackagePath) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_lock_write_failed")
        .with_path(path.as_str())
}
