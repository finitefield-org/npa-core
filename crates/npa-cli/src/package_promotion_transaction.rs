//! Shared cooperative locking for promotion materialization transactions.

use std::{
    ffi::{OsStr, OsString},
    fs::File,
    io::{self, Seek, Write},
    os::fd::AsRawFd,
    path::Path,
};

use npa_package::{format_package_hash, package_file_hash, PackageHash};

use crate::fs::no_follow_directory::{
    open_absolute_directory, regular_file_identity, Directory, Identity,
};

const TARGET_LOCK_PREFIX: &str = ".npa-promotion-lock-";

/// Retained, non-blocking advisory lock for one canonical target root.
pub(crate) struct TargetLock {
    file: File,
    target_path_hash: PackageHash,
    parent: Directory,
    target: Directory,
    target_name: OsString,
    target_identity: Identity,
    canonical_target: std::path::PathBuf,
    lock_name: OsString,
    lock_identity: Identity,
    exclusive: bool,
    active_transaction: Option<(OsString, Identity)>,
}

impl TargetLock {
    /// Acquire the target-specific sibling lock until this value is dropped.
    pub(crate) fn acquire(target: &Path) -> io::Result<Self> {
        Self::acquire_mode(target, true)
    }

    /// Acquire a shared target-specific lock for a read-only dry-run.
    pub(crate) fn acquire_shared(target: &Path) -> io::Result<Self> {
        Self::acquire_mode(target, false)
    }

    fn acquire_mode(target: &Path, exclusive: bool) -> io::Result<Self> {
        let target_name = target
            .file_name()
            .ok_or_else(|| io::Error::other("target root has no final component"))?
            .to_owned();
        // Retain the caller-selected parent before any pathname
        // canonicalization. Reopening a canonical string would allow an
        // ancestor rename/replacement to redirect the transaction between
        // validation and the first mutation.
        let parent_directory =
            open_absolute_directory(target.parent().unwrap_or_else(|| Path::new(".")), false)?;
        let target_directory = parent_directory.open_or_create_directory(&target_name, false)?;
        let target_identity = target_directory.identity()?;
        let canonical = std::fs::canonicalize(target)?;
        let canonical_name = canonical
            .file_name()
            .ok_or_else(|| io::Error::other("canonical target root has no final component"))?;
        let canonical_parent =
            open_absolute_directory(canonical.parent().unwrap_or_else(|| Path::new(".")), false)?;
        let canonical_identity = canonical_parent
            .open_or_create_directory(canonical_name, false)?
            .identity()?;
        if canonical_identity != target_identity {
            return Err(io::Error::other(
                "target root identity changed during canonicalization",
            ));
        }
        let lock_hash = package_file_hash(canonical.to_string_lossy().as_bytes());
        let lock_name = OsString::from(format!(
            "{TARGET_LOCK_PREFIX}{}",
            format_package_hash(&lock_hash).trim_start_matches("sha256:")
        ));
        let file = parent_directory.open_or_create_regular_file(&lock_name)?;
        let lock_identity = regular_file_identity(&file)?;
        // SAFETY: `file` owns this live descriptor for the guard's full
        // lifetime; `flock` neither dereferences pointers nor transfers it.
        let operation = if exclusive {
            libc::LOCK_EX
        } else {
            libc::LOCK_SH
        };
        let result = unsafe { libc::flock(file.as_raw_fd(), operation | libc::LOCK_NB) };
        if result != 0 {
            return Err(io::Error::last_os_error());
        }
        let mut lock = Self {
            file,
            target_path_hash: lock_hash,
            parent: parent_directory,
            target: target_directory,
            target_name,
            target_identity,
            canonical_target: canonical,
            lock_name,
            lock_identity,
            exclusive,
            active_transaction: None,
        };
        if exclusive {
            lock.record(None, "locked", None)?;
        }
        Ok(lock)
    }

    pub(crate) fn parent_directory(&self) -> io::Result<Directory> {
        self.parent.try_clone()
    }

    pub(crate) fn target_directory(&self) -> io::Result<Directory> {
        self.ensure_target_identity()?;
        self.target.try_clone()
    }

    pub(crate) fn canonical_target(&self) -> &Path {
        &self.canonical_target
    }

    pub(crate) fn target_path_hash(&self) -> PackageHash {
        self.target_path_hash
    }

    pub(crate) fn ensure_target_identity(&self) -> io::Result<()> {
        self.ensure_lock_identity()?;
        let current = self
            .parent
            .open_or_create_directory(&self.target_name, false)?
            .identity()?;
        if current != self.target_identity || self.target.identity()? != self.target_identity {
            return Err(io::Error::other("target root identity changed"));
        }
        Ok(())
    }

    fn ensure_lock_identity(&self) -> io::Result<()> {
        let current = self
            .parent
            .open_regular_file(&self.lock_name)?
            .ok_or_else(|| io::Error::other("promotion lock entry disappeared"))?;
        if regular_file_identity(&current)? != self.lock_identity {
            return Err(io::Error::other("promotion lock entry identity changed"));
        }
        Ok(())
    }

    fn ensure_exclusive(&self) -> io::Result<()> {
        if self.exclusive {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "promotion mutation requires the exclusive target lock",
            ))
        }
    }

    pub(crate) fn attach_transaction(
        &mut self,
        name: OsString,
        directory: &Directory,
    ) -> io::Result<()> {
        self.ensure_exclusive()?;
        let identity = directory.identity()?;
        if self
            .parent
            .open_or_create_directory(&name, false)?
            .identity()?
            != identity
        {
            return Err(io::Error::other("transaction identity changed"));
        }
        self.active_transaction = Some((name, identity));
        Ok(())
    }

    pub(crate) fn attach_existing_transaction(&mut self, name: OsString) -> io::Result<Directory> {
        let directory = self.parent.open_or_create_directory(&name, false)?;
        self.attach_transaction(name, &directory)?;
        Ok(directory)
    }

    pub(crate) fn active_transaction_directory(&self) -> io::Result<Option<Directory>> {
        self.ensure_target_identity()?;
        let Some((name, expected)) = &self.active_transaction else {
            return Ok(None);
        };
        let directory = self.parent.open_or_create_directory(name, false)?;
        if directory.identity()? != *expected {
            return Err(io::Error::other("transaction identity changed"));
        }
        Ok(Some(directory))
    }

    pub(crate) fn ensure_active_transaction_identity(&self) -> io::Result<()> {
        self.active_transaction_directory()?
            .ok_or_else(|| io::Error::other("transaction unavailable"))?;
        Ok(())
    }

    pub(crate) fn ensure_active_transaction_child_identity(
        &self,
        name: &std::ffi::OsStr,
        expected: Identity,
    ) -> io::Result<()> {
        let transaction = self
            .active_transaction_directory()?
            .ok_or_else(|| io::Error::other("transaction unavailable"))?;
        let child = transaction.open_or_create_directory(name, false)?;
        if child.identity()? != expected {
            return Err(io::Error::other("transaction child identity changed"));
        }
        Ok(())
    }

    /// Replace one file while this guard proves the promotion namespace's
    /// cooperative exclusive-writer contract on both sides of the syscall.
    pub(crate) fn replace_file_under_lock(
        &self,
        directory: &Directory,
        source: &OsStr,
        destination: &OsStr,
    ) -> io::Result<()> {
        self.ensure_exclusive()?;
        self.ensure_target_identity()?;
        directory.replace_file_under_cooperative_lock(source, destination)?;
        self.ensure_target_identity()
    }

    /// Remove an exact regular file while retaining exclusive promotion
    /// namespace authority. Generic identity-only removal remains fail-closed.
    pub(crate) fn remove_regular_file_under_lock(
        &self,
        directory: &Directory,
        name: &OsStr,
        identity: Identity,
    ) -> io::Result<()> {
        self.ensure_exclusive()?;
        self.ensure_target_identity()?;
        directory.remove_regular_file_under_cooperative_lock(name, identity)?;
        self.ensure_target_identity()
    }

    /// Remove an exact empty directory under the same exclusive authority.
    pub(crate) fn remove_empty_directory_under_lock(
        &self,
        directory: &Directory,
        name: &OsStr,
        identity: Identity,
    ) -> io::Result<()> {
        self.ensure_exclusive()?;
        self.ensure_target_identity()?;
        directory.remove_empty_directory_under_cooperative_lock(name, identity)?;
        self.ensure_target_identity()
    }

    pub(crate) fn remove_empty_active_transaction(&mut self) -> io::Result<()> {
        self.ensure_exclusive()?;
        let Some((name, identity)) = self.active_transaction.as_ref() else {
            return Ok(());
        };
        self.ensure_target_identity()?;
        let named = self.parent.open_or_create_directory(name, false)?;
        if named.identity()? != *identity {
            return Err(io::Error::other("transaction identity changed"));
        }
        self.parent
            .remove_empty_directory_under_cooperative_lock(name, *identity)?;
        self.ensure_target_identity()?;
        self.active_transaction = None;
        self.parent.sync_all()
    }

    /// Replace and fsync the sanitized diagnostic lock contents.
    pub(crate) fn record(
        &mut self,
        promotion_id: Option<PackageHash>,
        operation: &str,
        journal: Option<&str>,
    ) -> io::Result<()> {
        self.ensure_exclusive()?;
        self.ensure_target_identity()?;
        if !operation
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte == b'-')
            || journal.is_some_and(|value| {
                value.contains('/')
                    || value.contains('\\')
                    || !value.starts_with(".npa-promotion-transaction-")
            })
        {
            return Err(io::Error::other("invalid lock diagnostic"));
        }
        let promotion_id = promotion_id
            .map(|hash| format_package_hash(&hash))
            .unwrap_or_else(|| "none".to_owned());
        let journal = journal.unwrap_or("none");
        let contents = format!(
            "target_path_hash={}\npromotion_id={promotion_id}\noperation={operation}\njournal={journal}\n",
            format_package_hash(&self.target_path_hash)
        );
        self.file.set_len(0)?;
        self.file.rewind()?;
        self.file.write_all(contents.as_bytes())?;
        self.file.sync_all()
    }
}

impl Drop for TargetLock {
    fn drop(&mut self) {
        // SAFETY: the guard still owns the descriptor, and unlocking it
        // cannot outlive or alias the `File` being dropped.
        unsafe {
            libc::flock(self.file.as_raw_fd(), libc::LOCK_UN);
        }
    }
}
