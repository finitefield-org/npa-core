//! Atomic package-confined writer for promotion governance artifacts.

use std::{
    ffi::{OsStr, OsString},
    fs::{self, File},
    io::{self, Read, Write},
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};

#[cfg(unix)]
use std::os::{fd::AsRawFd, unix::fs::MetadataExt};

use npa_package::{validate_package_path, PackagePath};

use crate::{
    diagnostic::{CommandDiagnostic, DiagnosticKind},
    fs::{
        no_follow_directory::{regular_file_identity, Directory, Identity},
        render_package_path,
    },
    generated_artifact_writer::{
        open_package_parent_no_follow, read_package_regular_file_no_follow,
    },
};

const MAX_GOVERNANCE_ARTIFACT_BYTES: u64 = 134_217_728;

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

/// Read one validated package-relative governance artifact from the same
/// retained, no-follow descriptor chain used by writers.
pub(crate) fn read_governance_artifact(
    root: &Path,
    path: &PackagePath,
    field: &str,
    reason: &str,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    validate_package_path(path, field).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::GeneratedArtifact, reason)
                .with_path(render_package_path(path)),
        )
    })?;
    read_package_regular_file_no_follow(root, path).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason)
                .with_path(render_package_path(path)),
        )
    })
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
    directory: Directory,
    target: OsString,
    logical: PackagePath,
    lock_name: OsString,
    lock_identity: Identity,
    lock_file: File,
    reason_prefix: String,
}

impl GovernanceArtifactLock {
    fn verify_retained_lock(&self) -> io::Result<()> {
        let metadata = self.lock_file.metadata()?;
        #[cfg(unix)]
        if metadata.mode() & 0o7777 != 0o600 || metadata.nlink() != 1 {
            return Err(io::Error::other(
                "governance lock policy changed while retained",
            ));
        }
        if regular_file_identity(&self.lock_file)? != self.lock_identity {
            return Err(io::Error::other(
                "governance lock descriptor identity changed",
            ));
        }
        self.directory
            .require_named_regular_file_identity(&self.lock_name, self.lock_identity)
    }

    /// Read the current destination while retaining the update lock.
    pub(crate) fn read_existing(&self) -> io::Result<Vec<u8>> {
        self.verify_retained_lock()?;
        let result = read_entry(&self.directory, &self.target)?.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                "governance artifact is unavailable",
            )
        })?;
        self.verify_retained_lock()?;
        Ok(result)
    }

    /// Replace the validated destination while retaining the same update lock.
    pub(crate) fn replace_if_unchanged(
        &self,
        bytes: &[u8],
        expected_existing: &[u8],
    ) -> Result<(), Box<CommandDiagnostic>> {
        write_locked(
            self,
            bytes,
            GovernanceOutputPolicy::ReplaceAfterValidatedMerge,
            Some(expected_existing),
        )
    }
}

impl Drop for GovernanceArtifactLock {
    fn drop(&mut self) {
        #[cfg(unix)]
        unsafe {
            libc::flock(self.lock_file.as_raw_fd(), libc::LOCK_UN);
        }
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
    let (directory, target) = open_package_parent_no_follow(root, path, true)
        .map_err(|_| write_error(path, reason_prefix))?;
    let lock_name = Path::new(&target).with_extension(format!(
        "{}lock",
        Path::new(&target)
            .extension()
            .map(|value| format!("{}.", value.to_string_lossy()))
            .unwrap_or_default()
    ));
    let lock_name = lock_name
        .file_name()
        .ok_or_else(|| write_error(path, reason_prefix))?
        .to_owned();
    let lock_file = directory
        .open_or_create_regular_file(&lock_name)
        .map_err(|error| {
            let _ = error;
            write_error(path, reason_prefix)
        })?;
    #[cfg(unix)]
    {
        let metadata = lock_file
            .metadata()
            .map_err(|_| write_error(path, reason_prefix))?;
        if metadata.mode() & 0o7777 != 0o600 || metadata.nlink() != 1 {
            return Err(write_error(path, reason_prefix));
        }
        if unsafe { libc::flock(lock_file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    format!("{reason_prefix}_concurrent_update"),
                )
                .with_path(render_package_path(path)),
            ));
        }
    }
    let lock_identity =
        regular_file_identity(&lock_file).map_err(|_| write_error(path, reason_prefix))?;
    let lock = GovernanceArtifactLock {
        directory,
        target,
        logical: path.clone(),
        lock_name,
        lock_identity,
        lock_file,
        reason_prefix: reason_prefix.to_owned(),
    };
    lock.verify_retained_lock()
        .map_err(|_| write_error(path, reason_prefix))?;
    Ok(lock)
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
    require_governance_artifact_size(bytes.len(), path, reason_prefix)?;
    let lock = lock_governance_artifact(root, path, reason_prefix)?;
    write_locked(&lock, bytes, policy, expected_existing)
}

fn write_locked(
    lock: &GovernanceArtifactLock,
    bytes: &[u8],
    policy: GovernanceOutputPolicy,
    expected_existing: Option<&[u8]>,
) -> Result<(), Box<CommandDiagnostic>> {
    let directory = &lock.directory;
    let target = &lock.target;
    let logical = &lock.logical;
    let reason_prefix = &lock.reason_prefix;
    lock.verify_retained_lock()
        .map_err(|_| write_error(logical, reason_prefix))?;
    require_governance_artifact_size(bytes.len(), logical, reason_prefix)?;
    if let Some(expected) = expected_existing {
        if read_entry(directory, target).ok().flatten().as_deref() != Some(expected) {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    format!("{reason_prefix}_concurrent_update"),
                )
                .with_path(render_package_path(logical)),
            ));
        }
    }
    match read_entry(directory, target) {
        Ok(Some(existing)) if existing == bytes => return Ok(()),
        Ok(Some(_)) if policy == GovernanceOutputPolicy::CreateOrIdentical => {
            return Err(Box::new(
                CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    format!("{reason_prefix}_output_conflict"),
                )
                .with_path(render_package_path(logical)),
            ));
        }
        Ok(_) => {}
        Err(_) => return Err(write_error(logical, reason_prefix)),
    }
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let temp = OsString::from(format!(
        ".{}.npa-tmp-{}-{nonce}",
        target.to_string_lossy(),
        std::process::id()
    ));
    let mut file = directory
        .create_new_regular_file(&temp)
        .map_err(|_| write_error(logical, reason_prefix))?;
    let write_result = (|| {
        file.write_all(bytes)?;
        file.sync_all()?;
        drop(file);
        if policy == GovernanceOutputPolicy::CreateOrIdentical {
            directory.publish_file_no_replace(&temp, target)?;
        } else {
            // Reject a symbolic link or non-regular destination rather than
            // allowing rename to silently replace a hostile entry.
            let _ = directory.open_regular_file(target)?;
            lock.verify_retained_lock()?;
            directory.replace_file_under_cooperative_lock(&temp, target)?;
        }
        directory.sync_all()?;
        lock.verify_retained_lock()
    })();
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

fn require_governance_artifact_size(
    actual_bytes: usize,
    path: &PackagePath,
    reason_prefix: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    let actual_bytes = u64::try_from(actual_bytes).unwrap_or(u64::MAX);
    if actual_bytes > MAX_GOVERNANCE_ARTIFACT_BYTES {
        return Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                format!("{reason_prefix}_output_too_large"),
            )
            .with_path(render_package_path(path))
            .with_expected_value(MAX_GOVERNANCE_ARTIFACT_BYTES.to_string())
            .with_actual_value(actual_bytes.to_string()),
        ));
    }
    Ok(())
}

fn read_entry(directory: &Directory, target: &OsStr) -> io::Result<Option<Vec<u8>>> {
    let Some(mut file) = directory.open_regular_file(target)? else {
        return Ok(None);
    };
    let metadata = file.metadata()?;
    if metadata.len() > MAX_GOVERNANCE_ARTIFACT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "governance artifact exceeds the 128 MiB byte limit",
        ));
    }
    let mut bytes = Vec::new();
    std::io::Read::by_ref(&mut file)
        .take(MAX_GOVERNANCE_ARTIFACT_BYTES + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_GOVERNANCE_ARTIFACT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "governance artifact exceeds the 128 MiB byte limit",
        ));
    }
    Ok(Some(bytes))
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
    fn governance_artifact_write_size_limit_is_exact() {
        let path = PackagePath::new("governance.json");
        assert!(require_governance_artifact_size(
            MAX_GOVERNANCE_ARTIFACT_BYTES as usize,
            &path,
            "test",
        )
        .is_ok());
        let error = require_governance_artifact_size(
            MAX_GOVERNANCE_ARTIFACT_BYTES as usize + 1,
            &path,
            "test",
        )
        .unwrap_err();
        assert_eq!(error.reason_code, "test_output_too_large");
        assert_eq!(error.expected_value.as_deref(), Some("134217728"));
        assert_eq!(error.actual_value.as_deref(), Some("134217729"));
    }

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

    #[test]
    fn retained_lock_replacement_stops_publication_without_deleting_either_lock() {
        let root = std::env::temp_dir().join(format!(
            "npa-governance-lock-replacement-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let path = PackagePath::new("l2-acceptance.json");
        fs::write(root.join(path.as_str()), b"old").unwrap();

        let lock = lock_governance_artifact(&root, &path, "test").unwrap();
        let existing = lock.read_existing().unwrap();
        let original_lock = root.join(&lock.lock_name);
        let relocated_lock = root.join("relocated-lock");
        fs::rename(&original_lock, &relocated_lock).unwrap();
        fs::write(&original_lock, b"replacement lock must survive").unwrap();

        let error = lock.replace_if_unchanged(b"new", &existing).unwrap_err();
        assert_eq!(error.reason_code, "test_output_write_failed");
        assert_eq!(fs::read(root.join(path.as_str())).unwrap(), b"old");
        assert_eq!(
            fs::read(&original_lock).unwrap(),
            b"replacement lock must survive"
        );
        assert!(relocated_lock.is_file());
        drop(lock);
        assert!(original_lock.is_file());
        assert!(relocated_lock.is_file());

        fs::remove_dir_all(root).unwrap();
    }
}
