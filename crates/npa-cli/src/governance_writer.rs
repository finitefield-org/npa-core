//! Atomic package-confined writer for promotion governance artifacts.

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

use npa_package::{validate_package_path, PackagePath};

use crate::{
    diagnostic::{CommandDiagnostic, DiagnosticKind},
    fs::render_package_path,
};

/// Resolve a package-relative governance path while rejecting symlink traversal.
pub fn confined_governance_path(
    root: &Path,
    path: &PackagePath,
    field: &str,
    reason: &str,
) -> Result<std::path::PathBuf, Box<CommandDiagnostic>> {
    validate_package_path(path, field).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                .with_path(render_package_path(path)),
        )
    })?;
    let mut candidate = root.to_path_buf();
    for component in Path::new(path.as_str()).components() {
        candidate.push(component.as_os_str());
        match fs::symlink_metadata(&candidate) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                        .with_path(render_package_path(path)),
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => break,
            Err(_) => {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                        .with_path(render_package_path(path)),
                ));
            }
        }
    }
    Ok(root.join(path.as_str()))
}

/// Existing-output policy for governance artifacts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GovernanceOutputPolicy {
    /// Create a new file or accept exact existing bytes; never replace.
    CreateOrIdentical,
    /// Atomically replace after the caller validated an explicit in-place merge.
    ReplaceAfterValidatedMerge,
}

/// Held sibling lock for a governance artifact update.
pub(crate) struct GovernanceArtifactLock {
    target: PathBuf,
    logical: PackagePath,
    lock_path: PathBuf,
    lock_file: Option<File>,
    reason_prefix: String,
}

impl GovernanceArtifactLock {
    /// Read the current destination while retaining the update lock.
    pub(crate) fn read_existing(&self) -> io::Result<Vec<u8>> {
        fs::read(&self.target)
    }

    /// Replace the validated destination while retaining the same update lock.
    pub(crate) fn replace_if_unchanged(
        &self,
        bytes: &[u8],
        expected_existing: &[u8],
    ) -> Result<(), Box<CommandDiagnostic>> {
        write_locked(
            &self.target,
            &self.logical,
            bytes,
            GovernanceOutputPolicy::ReplaceAfterValidatedMerge,
            Some(expected_existing),
            &self.reason_prefix,
        )
    }
}

impl Drop for GovernanceArtifactLock {
    fn drop(&mut self) {
        self.lock_file.take();
        let _ = fs::remove_file(&self.lock_path);
    }
}

/// Acquire and retain the sibling lock used for a governance artifact update.
pub(crate) fn lock_governance_artifact(
    root: &Path,
    path: &PackagePath,
    reason_prefix: &str,
) -> Result<GovernanceArtifactLock, Box<CommandDiagnostic>> {
    validate_package_path(path, "--out").map_err(|_| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                format!("{reason_prefix}_output_not_package_relative"),
            )
            .with_path(render_package_path(path)),
        )
    })?;
    let target = confined_governance_path(
        root,
        path,
        "--out",
        &format!("{reason_prefix}_output_not_package_relative"),
    )?;
    if let Some(parent) = target.parent() {
        fs::create_dir_all(parent).map_err(|_| write_error(path, reason_prefix))?;
    }
    let lock_path = target.with_extension(format!(
        "{}lock",
        target
            .extension()
            .map(|value| format!("{}.", value.to_string_lossy()))
            .unwrap_or_default()
    ));
    let lock_file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&lock_path)
        .map_err(|error| {
            if error.kind() == io::ErrorKind::AlreadyExists {
                Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::GeneratedArtifact,
                        format!("{reason_prefix}_concurrent_update"),
                    )
                    .with_path(render_package_path(path)),
                )
            } else {
                write_error(path, reason_prefix)
            }
        })?;
    Ok(GovernanceArtifactLock {
        target,
        logical: path.clone(),
        lock_path,
        lock_file: Some(lock_file),
        reason_prefix: reason_prefix.to_owned(),
    })
}

/// Write one canonical governance artifact atomically.
pub fn write_governance_artifact(
    root: &Path,
    path: &PackagePath,
    bytes: &[u8],
    policy: GovernanceOutputPolicy,
    reason_prefix: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    write_governance_artifact_with_snapshot(root, path, bytes, policy, None, reason_prefix)
}

/// Atomically replace a previously validated artifact only if its captured bytes are unchanged.
pub fn replace_governance_artifact_if_unchanged(
    root: &Path,
    path: &PackagePath,
    bytes: &[u8],
    expected_existing: &[u8],
    reason_prefix: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    write_governance_artifact_with_snapshot(
        root,
        path,
        bytes,
        GovernanceOutputPolicy::ReplaceAfterValidatedMerge,
        Some(expected_existing),
        reason_prefix,
    )
}

fn write_governance_artifact_with_snapshot(
    root: &Path,
    path: &PackagePath,
    bytes: &[u8],
    policy: GovernanceOutputPolicy,
    expected_existing: Option<&[u8]>,
    reason_prefix: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    let lock = lock_governance_artifact(root, path, reason_prefix)?;
    write_locked(
        &lock.target,
        path,
        bytes,
        policy,
        expected_existing,
        reason_prefix,
    )
}

fn write_locked(
    target: &Path,
    logical: &PackagePath,
    bytes: &[u8],
    policy: GovernanceOutputPolicy,
    expected_existing: Option<&[u8]>,
    reason_prefix: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    if let Some(expected) = expected_existing {
        if fs::read(target).ok().as_deref() != Some(expected) {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    format!("{reason_prefix}_concurrent_update"),
                )
                .with_path(render_package_path(logical)),
            ));
        }
    }
    match fs::read(target) {
        Ok(existing) if existing == bytes => return Ok(()),
        Ok(_) if policy == GovernanceOutputPolicy::CreateOrIdentical => {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    format!("{reason_prefix}_output_conflict"),
                )
                .with_path(render_package_path(logical)),
            ));
        }
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err(write_error(logical, reason_prefix)),
    }
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let temp = target.with_extension(format!("npa-tmp-{}-{nonce}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temp)
        .map_err(|_| write_error(logical, reason_prefix))?;
    let write_result = (|| {
        file.write_all(bytes)?;
        file.sync_all()?;
        drop(file);
        if policy == GovernanceOutputPolicy::CreateOrIdentical && target.exists() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "output appeared",
            ));
        }
        fs::rename(&temp, target)?;
        if let Some(parent) = target.parent() {
            if let Ok(parent_file) = OpenOptions::new().read(true).open(parent) {
                let _ = parent_file.sync_all();
            }
        }
        Ok::<(), io::Error>(())
    })();
    let _ = fs::remove_file(&temp);
    match write_result {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                format!("{reason_prefix}_output_conflict"),
            )
            .with_path(render_package_path(logical)),
        )),
        Err(_) => Err(write_error(logical, reason_prefix)),
    }
}

fn write_error(path: &PackagePath, reason_prefix: &str) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(
            DiagnosticKind::GeneratedArtifact,
            format!("{reason_prefix}_output_write_failed"),
        )
        .with_path(render_package_path(path)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_lock_blocks_other_writers_and_is_released_on_drop() {
        let root = std::env::temp_dir().join(format!(
            "npa-governance-retained-lock-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let path = PackagePath::new("l2-acceptance.json");
        fs::write(root.join(path.as_str()), b"old").unwrap();

        let lock = lock_governance_artifact(&root, &path, "test").unwrap();
        let existing = lock.read_existing().unwrap();
        let competing = write_governance_artifact(
            &root,
            &path,
            b"new",
            GovernanceOutputPolicy::CreateOrIdentical,
            "test",
        )
        .unwrap_err();
        assert_eq!(competing.reason_code, "test_concurrent_update");
        lock.replace_if_unchanged(b"new", &existing).unwrap();
        drop(lock);

        assert_eq!(fs::read(root.join(path.as_str())).unwrap(), b"new");
        write_governance_artifact(
            &root,
            &path,
            b"new",
            GovernanceOutputPolicy::CreateOrIdentical,
            "test",
        )
        .unwrap();
        fs::remove_dir_all(root).unwrap();
    }
}
