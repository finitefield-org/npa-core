//! Shared cooperative locking for promotion materialization transactions.

use std::{
    fs::{File, OpenOptions},
    io::{self, Seek, Write},
    os::fd::AsRawFd,
    os::unix::fs::OpenOptionsExt,
    path::Path,
};

use npa_package::{format_package_hash, package_file_hash, PackageHash};

const TARGET_LOCK_PREFIX: &str = ".npa-promotion-lock-";

/// Retained, non-blocking advisory lock for one canonical target root.
pub(crate) struct TargetLock {
    file: File,
    target_path_hash: PackageHash,
}

impl TargetLock {
    /// Acquire the target-specific sibling lock until this value is dropped.
    pub(crate) fn acquire(target: &Path) -> io::Result<Self> {
        let canonical = std::fs::canonicalize(target)?;
        let parent = canonical.parent().unwrap_or_else(|| Path::new("."));
        let lock_hash = package_file_hash(canonical.to_string_lossy().as_bytes());
        let file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(parent.join(format!(
                "{TARGET_LOCK_PREFIX}{}",
                format_package_hash(&lock_hash).trim_start_matches("sha256:")
            )))?;
        // SAFETY: `file` owns this live descriptor for the guard's full
        // lifetime; `flock` neither dereferences pointers nor transfers it.
        let result = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
        if result != 0 {
            return Err(io::Error::last_os_error());
        }
        let mut lock = Self {
            file,
            target_path_hash: lock_hash,
        };
        lock.record(None, "locked", None)?;
        Ok(lock)
    }

    /// Replace and fsync the sanitized diagnostic lock contents.
    pub(crate) fn record(
        &mut self,
        promotion_id: Option<PackageHash>,
        operation: &str,
        journal: Option<&str>,
    ) -> io::Result<()> {
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
