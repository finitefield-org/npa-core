//! Implementation of `npa package lock`.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_file_hash,
    parse_package_lock_json, PackagePath,
};

use crate::args::{PackageCommonOptions, PackageLockCommand};
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::join_package_path;
use crate::package::{load_package_root, LoadedPackageRoot};
use crate::package_artifacts::PACKAGE_LOCK_PATH;

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
    let loaded = match load_package_root(&options.root, COMMAND_WRITE) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    let regenerated_lock_json = match regenerated_package_lock_json(&loaded, COMMAND_WRITE) {
        Ok(json) => json,
        Err(result) => return result,
    };

    if let Some(diagnostic) = write_package_lock(&loaded, regenerated_lock_json.as_bytes()) {
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

fn write_package_lock(loaded: &LoadedPackageRoot, bytes: &[u8]) -> Option<CommandDiagnostic> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let pending = match prepare_pending_write(&loaded.root, &lock_path, bytes) {
        Ok(Some(write)) => write,
        Ok(None) => return None,
        Err(diagnostic) => return Some(*diagnostic),
    };
    commit_pending_write(pending)
}

struct PendingWrite {
    path: PackagePath,
    full_path: PathBuf,
    temp_path: PathBuf,
}

fn prepare_pending_write(
    root: &Path,
    package_path: &PackagePath,
    bytes: &[u8],
) -> Result<Option<PendingWrite>, Box<CommandDiagnostic>> {
    let full_path = join_package_path(root, package_path, "package_lock.path")?;
    match fs::read(&full_path) {
        Ok(existing) if existing == bytes => return Ok(None),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err(Box::new(write_artifact_diagnostic(package_path))),
    }

    if let Some(parent) = full_path.parent() {
        if fs::create_dir_all(parent).is_err() {
            return Err(Box::new(write_artifact_diagnostic(package_path)));
        }
    }

    let temp_path = temporary_write_path(&full_path);
    if fs::write(&temp_path, bytes).is_err() {
        return Err(Box::new(write_artifact_diagnostic(package_path)));
    }

    Ok(Some(PendingWrite {
        path: package_path.clone(),
        full_path,
        temp_path,
    }))
}

fn commit_pending_write(write: PendingWrite) -> Option<CommandDiagnostic> {
    if fs::rename(&write.temp_path, &write.full_path).is_err() {
        let _ = fs::remove_file(&write.temp_path);
        return Some(write_artifact_diagnostic(&write.path));
    }
    None
}

fn temporary_write_path(path: &Path) -> PathBuf {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("package-lock.json");
    path.with_file_name(format!(".{file_name}.npa-package-lock.tmp"))
}

fn write_artifact_diagnostic(path: &PackagePath) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "package_lock_write_failed")
        .with_path(path.as_str())
}
