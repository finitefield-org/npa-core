//! Capability-style creation and cleanup for benchmark-owned private trees.
//!
//! On Unix, every mutation is relative to retained directory descriptors. The
//! complete expected catalog is validated before deletion, and the retained
//! parent/root identities are rechecked immediately before every `unlinkat`.
//! There is deliberately no recursive "delete whatever is present" operation.

#![allow(dead_code)]

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{Read as _, Seek as _, Write as _},
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

#[cfg(test)]
use std::cell::Cell;

use sha2::{Digest as _, Sha256};

#[cfg(unix)]
use std::{
    ffi::{CStr, CString, OsStr, OsString},
    os::{
        fd::{AsRawFd, FromRawFd, OwnedFd, RawFd},
        unix::ffi::{OsStrExt as _, OsStringExt as _},
    },
};

static NEXT_PRIVATE_ROOT: AtomicU64 = AtomicU64::new(0);

#[cfg(test)]
thread_local! {
    static TEST_READDIR_ERROR_AFTER_ENTRIES: Cell<Option<usize>> = const { Cell::new(None) };
}

/// One no-follow snapshot of a closed absolute directory tree.
#[derive(Debug, PartialEq, Eq)]
pub struct AbsoluteRegularTree {
    pub directories: BTreeSet<PathBuf>,
    pub files: BTreeMap<PathBuf, Vec<u8>>,
}

/// Read a regular-file-only absolute tree through retained directory
/// descriptors. Entry count and both per-file and aggregate bytes are bounded.
pub fn read_absolute_regular_tree(
    root: &Path,
    maximum_entries: usize,
    maximum_file_bytes: u64,
    maximum_total_bytes: u64,
    label: &str,
) -> Result<AbsoluteRegularTree, String> {
    if maximum_entries == 0 || maximum_file_bytes == 0 || maximum_total_bytes == 0 {
        return Err(format!("{label} limits must all be positive"));
    }
    #[cfg(unix)]
    {
        let root_path = open_absolute_directory(root)?;
        root_path.verify(label)?;
        let root_status = file_status(root_path.as_raw_fd())?;
        if file_kind(&root_status) != libc::S_IFDIR {
            return Err(format!("{label} root is not a directory"));
        }
        let mut tree = AbsoluteRegularTree {
            directories: BTreeSet::new(),
            files: BTreeMap::new(),
        };
        let mut total_bytes = 0_u64;
        read_regular_tree_directory_fd(
            root_path.as_raw_fd(),
            root_status.st_dev,
            Path::new(""),
            maximum_entries,
            maximum_file_bytes,
            maximum_total_bytes,
            &mut total_bytes,
            &mut tree,
            label,
        )?;
        root_path.verify(label)?;
        Ok(tree)
    }
    #[cfg(not(unix))]
    {
        validate_absolute_directory_path(root, label)?;
        let mut pending = vec![(PathBuf::new(), root.to_owned())];
        let mut tree = AbsoluteRegularTree {
            directories: BTreeSet::new(),
            files: BTreeMap::new(),
        };
        let mut total_bytes = 0_u64;
        while let Some((relative, absolute)) = pending.pop() {
            tree.directories.insert(relative.clone());
            for entry in fs::read_dir(&absolute).map_err(display_error)? {
                let entry = entry.map_err(display_error)?;
                let child_relative = relative.join(entry.file_name());
                validate_relative(&child_relative)?;
                let metadata = fs::symlink_metadata(entry.path()).map_err(display_error)?;
                if metadata.file_type().is_symlink() {
                    return Err(format!("{label} contains a symbolic link"));
                }
                if metadata.is_dir() {
                    pending.push((child_relative, entry.path()));
                } else if metadata.is_file() {
                    if metadata.len() > maximum_file_bytes {
                        return Err(format!("{label} file exceeds its byte limit"));
                    }
                    let bytes = fs::read(entry.path()).map_err(display_error)?;
                    total_bytes = total_bytes
                        .checked_add(u64::try_from(bytes.len()).map_err(display_error)?)
                        .ok_or_else(|| format!("{label} aggregate byte count overflowed"))?;
                    if total_bytes > maximum_total_bytes {
                        return Err(format!("{label} exceeds its aggregate byte limit"));
                    }
                    tree.files.insert(child_relative, bytes);
                } else {
                    return Err(format!("{label} contains a special file"));
                }
                if tree.directories.len() + tree.files.len() > maximum_entries {
                    return Err(format!("{label} exceeds its entry limit"));
                }
            }
        }
        Ok(tree)
    }
}

/// Open one absolute regular file through a retained, no-follow parent
/// descriptor and read at most `maximum_bytes` from that opened inode.
pub fn read_absolute_regular_file(
    path: &Path,
    maximum_bytes: u64,
    label: &str,
) -> Result<Vec<u8>, String> {
    #[cfg(unix)]
    {
        let (parent, basename) = open_absolute_parent(path, label)?;
        read_bounded_regular_file_at(&parent, &basename, maximum_bytes, label)
    }
    #[cfg(not(unix))]
    {
        validate_absolute_path(path, label)?;
        let metadata = fs::symlink_metadata(path).map_err(display_error)?;
        if !metadata.file_type().is_file()
            || metadata.file_type().is_symlink()
            || metadata.len() > maximum_bytes
        {
            return Err(format!("{label} is not a bounded real regular file"));
        }
        let bytes = fs::read(path).map_err(display_error)?;
        if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
            return Err(format!("{label} grew beyond its byte limit"));
        }
        Ok(bytes)
    }
}

/// Read one caller-supplied regular file without reopening a stringified cwd.
///
/// Relative paths are walked from a descriptor retained for `.` and absolute
/// paths from a descriptor retained for `/`.  Every directory component and
/// the final file are opened with `O_NOFOLLOW`; parent components are rejected
/// rather than interpreted outside the retained invocation root.
pub fn read_invocation_regular_file(
    path: &Path,
    maximum_bytes: u64,
    label: &str,
) -> Result<Vec<u8>, String> {
    if maximum_bytes == 0 {
        return Err(format!("{label} byte limit must be positive"));
    }
    #[cfg(unix)]
    {
        let (parent, basename) = open_invocation_parent(path, label)?;
        read_bounded_regular_file_at(&parent, &basename, maximum_bytes, label)
    }
    #[cfg(not(unix))]
    {
        if path.as_os_str().is_empty()
            || path.file_name().is_none()
            || path.components().any(|component| {
                !matches!(
                    component,
                    Component::RootDir | Component::CurDir | Component::Normal(_)
                )
            })
        {
            return Err(format!("{label} path is not normalized"));
        }
        let metadata = fs::symlink_metadata(path).map_err(display_error)?;
        if !metadata.file_type().is_file()
            || metadata.file_type().is_symlink()
            || metadata.len() > maximum_bytes
        {
            return Err(format!("{label} is not one bounded real regular file"));
        }
        let bytes = fs::read(path).map_err(display_error)?;
        if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
            return Err(format!("{label} grew beyond its byte limit"));
        }
        Ok(bytes)
    }
}

/// One retained invocation-root capability for a transaction that must read
/// several relative files from the same namespace snapshot. Every read
/// rechecks the retained root and all newly opened descendants, so replacing
/// the invocation cwd/root between reads fails closed instead of producing a
/// mixed transaction.
pub struct InvocationReadRoot {
    path: PathBuf,
    #[cfg(unix)]
    root: RetainedDirectoryPath,
    #[cfg(unix)]
    reads: RefCell<Vec<InvocationReadBinding>>,
}

#[cfg(unix)]
struct InvocationReadBinding {
    parent: RetainedDirectoryPath,
    basename: CString,
    identity: EntryIdentity,
}

impl InvocationReadRoot {
    /// Retain the invocation current directory as the transaction root.
    pub fn current(label: &str) -> Result<Self, String> {
        #[cfg(unix)]
        {
            let current = CString::new(".").map_err(|_| "cwd path contains NUL".to_owned())?;
            let opened_current = owned_fd(
                unsafe {
                    libc::open(
                        current.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                    )
                },
                "open invocation cwd",
            )?;
            let opened_identity = status_identity(&file_status(opened_current.as_raw_fd())?);
            let path = fs::canonicalize(".").map_err(display_error)?;
            let root = open_absolute_directory(&path)?;
            if status_identity(&file_status(root.as_raw_fd())?) != opened_identity {
                return Err(format!(
                    "{label} current directory changed while it was bound"
                ));
            }
            root.verify(label)?;
            Ok(Self {
                path,
                root,
                reads: RefCell::new(Vec::new()),
            })
        }
        #[cfg(not(unix))]
        {
            let path = std::env::current_dir().map_err(display_error)?;
            Ok(Self { path })
        }
    }

    /// Recheck the transaction root plus every directory and regular-file
    /// identity already read through it.
    pub fn verify(&self, label: &str) -> Result<(), String> {
        #[cfg(unix)]
        {
            self.root.verify(label)?;
            for binding in self.reads.borrow().iter() {
                binding.parent.verify(label)?;
                let named = status_at(binding.parent.as_raw_fd(), &binding.basename)?;
                if file_kind(&named) != libc::S_IFREG || status_identity(&named) != binding.identity
                {
                    return Err(format!("{label} previously read file changed identity"));
                }
            }
            self.root.verify(label)
        }
        #[cfg(not(unix))]
        {
            let _ = label;
            if fs::canonicalize(&self.path).map_err(display_error)? != self.path {
                return Err("invocation read root changed".to_owned());
            }
            Ok(())
        }
    }

    /// Read one normalized relative regular file through this retained root.
    pub fn read(&self, path: &Path, maximum_bytes: u64, label: &str) -> Result<Vec<u8>, String> {
        if maximum_bytes == 0 {
            return Err(format!("{label} byte limit must be positive"));
        }
        let relative = if path.is_absolute() {
            path.strip_prefix(&self.path)
                .map_err(|_| format!("{label} absolute path is outside the invocation root"))?
        } else {
            path
        };
        validate_relative(relative).map_err(|_| format!("{label} path is not normalized"))?;
        #[cfg(unix)]
        {
            self.verify(label)?;
            let components = relative.components().collect::<Vec<_>>();
            let (last, parents) = components
                .split_last()
                .ok_or_else(|| format!("{label} path is empty"))?;
            let duplicate =
                RetainedDirectoryPath::from_anchor(duplicate_fd(self.root.as_raw_fd())?, label)?;
            let parent = parents.iter().try_fold(duplicate, |parent, component| {
                let Component::Normal(component) = component else {
                    return Err(format!("{label} path is not normalized"));
                };
                parent.open_child(c_string(component)?, label)
            })?;
            let Component::Normal(basename) = last else {
                return Err(format!("{label} path has no normalized basename"));
            };
            let basename = c_string(basename)?;
            let (bytes, identity) = read_bounded_regular_file_at_with_identity(
                &parent,
                &basename,
                maximum_bytes,
                label,
            )?;
            parent.verify(label)?;
            self.reads.borrow_mut().push(InvocationReadBinding {
                parent,
                basename,
                identity,
            });
            self.verify(label)?;
            Ok(bytes)
        }
        #[cfg(not(unix))]
        {
            self.verify(label)?;
            read_invocation_regular_file(&self.path.join(relative), maximum_bytes, label)
        }
    }
}

/// Create one caller-selected output exactly once through the retained
/// invocation path. The returned capability keeps every ancestor and the
/// created basename bound to the opened inode until the caller has written and
/// synced it.
pub fn create_new_invocation_file(path: &Path, label: &str) -> Result<AttachedOutputFile, String> {
    #[cfg(unix)]
    {
        let (parent, basename) = open_invocation_parent(path, label)?;
        create_new_file_at(parent, basename, label)
    }
    #[cfg(not(unix))]
    {
        if path.as_os_str().is_empty()
            || path.file_name().is_none()
            || path.components().any(|component| {
                !matches!(
                    component,
                    Component::RootDir | Component::CurDir | Component::Normal(_)
                )
            })
        {
            return Err(format!("{label} path is not normalized"));
        }
        let file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(display_error)?;
        Ok(AttachedOutputFile { file })
    }
}

/// Atomically replace one caller-selected regular file only when its current
/// bytes still equal the exact expected preimage. Both the preimage and the
/// temporary replacement are identity-bound beneath one retained invocation
/// parent; ancestor or leaf replacement makes the operation fail closed.
pub fn replace_invocation_regular_file_exact(
    path: &Path,
    expected: &[u8],
    replacement: &[u8],
    maximum_bytes: u64,
    label: &str,
) -> Result<(), String> {
    if maximum_bytes == 0
        || u64::try_from(expected.len()).map_err(display_error)? > maximum_bytes
        || u64::try_from(replacement.len()).map_err(display_error)? > maximum_bytes
    {
        return Err(format!("{label} exceeds its byte limit"));
    }
    #[cfg(unix)]
    {
        let (parent, basename) = open_invocation_parent(path, label)?;
        replace_invocation_regular_file_exact_with_hook(
            &parent,
            &basename,
            expected,
            replacement,
            maximum_bytes,
            label,
            |_, _| {},
        )
    }
    #[cfg(not(unix))]
    {
        let current = read_invocation_regular_file(path, maximum_bytes, label)?;
        if current != expected {
            return Err(format!("{label} preimage does not match"));
        }
        let temporary = path.with_extension(format!(
            "npa-replace-{}-{}",
            std::process::id(),
            NEXT_PRIVATE_ROOT.fetch_add(1, Ordering::SeqCst)
        ));
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(display_error)?;
        file.write_all(replacement).map_err(display_error)?;
        file.sync_all().map_err(display_error)?;
        fs::rename(temporary, path).map_err(display_error)
    }
}

/// Create one caller-selected output exactly once, or accept an existing
/// regular file only when its bytes already equal the requested canonical
/// contents. The parent walk is retained/no-follow just like the invocation
/// reader, and an existing symlink or different preimage is never replaced.
pub fn write_invocation_regular_file_create_or_same(
    path: &Path,
    bytes: &[u8],
    maximum_bytes: u64,
    label: &str,
) -> Result<(), String> {
    if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
        return Err(format!("{label} exceeds its byte limit"));
    }
    #[cfg(unix)]
    {
        let (parent, basename) = open_invocation_parent(path, label)?;
        parent.verify(label)?;
        let raw = unsafe {
            libc::openat(
                parent.as_raw_fd(),
                basename.as_ptr(),
                libc::O_RDWR | libc::O_CLOEXEC | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW,
                0o600,
            )
        };
        if raw < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() != std::io::ErrorKind::AlreadyExists {
                return Err(format!("create {label}: {error}"));
            }
            let existing = read_bounded_regular_file_at(&parent, &basename, maximum_bytes, label)?;
            return if existing == bytes {
                Ok(())
            } else {
                Err(format!("existing {label} has different bytes"))
            };
        }
        let mut file = fs::File::from(owned_fd(raw, &format!("create {label}"))?);
        let opened = file_status(file.as_raw_fd())?;
        let named = status_at(parent.as_raw_fd(), &basename)?;
        if file_kind(&opened) != libc::S_IFREG
            || status_identity(&opened) != status_identity(&named)
            || opened.st_dev != parent.device
        {
            return Err(format!("created {label} identity is invalid"));
        }
        file.write_all(bytes).map_err(display_error)?;
        file.sync_all().map_err(display_error)?;
        let named_after = status_at(parent.as_raw_fd(), &basename)?;
        if status_identity(&named_after) != status_identity(&opened)
            || file_kind(&named_after) != libc::S_IFREG
        {
            return Err(format!("created {label} changed while writing"));
        }
        parent.verify(label)?;
        sync_directory(parent.as_raw_fd())
    }
    #[cfg(not(unix))]
    {
        use std::io::ErrorKind;
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
        {
            Ok(mut file) => {
                file.write_all(bytes).map_err(display_error)?;
                file.sync_all().map_err(display_error)
            }
            Err(error) if error.kind() == ErrorKind::AlreadyExists => {
                let existing = read_invocation_regular_file(path, maximum_bytes, label)?;
                if existing == bytes {
                    Ok(())
                } else {
                    Err(format!("existing {label} has different bytes"))
                }
            }
            Err(error) => Err(display_error(error)),
        }
    }
}

/// Create one absolute owner-only regular file through a retained, no-follow
/// parent descriptor. The caller owns the returned opened inode and may write
/// and sync it without reopening the path.
pub fn create_new_absolute_file(path: &Path, label: &str) -> Result<AttachedOutputFile, String> {
    #[cfg(unix)]
    {
        let (parent, basename) = open_absolute_parent(path, label)?;
        create_new_file_at(parent, basename, label)
    }
    #[cfg(not(unix))]
    {
        validate_absolute_path(path, label)?;
        let file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(display_error)?;
        Ok(AttachedOutputFile { file })
    }
}

#[cfg(unix)]
fn create_new_file_at(
    parent: RetainedDirectoryPath,
    basename: CString,
    label: &str,
) -> Result<AttachedOutputFile, String> {
    parent.verify(label)?;
    let raw = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            basename.as_ptr(),
            libc::O_RDWR | libc::O_CLOEXEC | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW,
            0o600,
        )
    };
    let file = fs::File::from(owned_fd(raw, &format!("create {label}"))?);
    let opened = file_status(file.as_raw_fd())?;
    let identity = status_identity(&opened);
    let validation = (|| {
        let named = status_at(parent.as_raw_fd(), &basename)?;
        if file_kind(&opened) != libc::S_IFREG
            || file_kind(&named) != libc::S_IFREG
            || identity != status_identity(&named)
            || opened.st_dev != parent.device
            || opened.st_mode & 0o777 != 0o600
            || opened.st_nlink != 1
        {
            return Err(format!(
                "created {label} has invalid identity, device, kind, or mode"
            ));
        }
        parent.verify(label)?;
        sync_directory(parent.as_raw_fd())
    })();
    // There is no portable Unix primitive that unlinks a directory entry only
    // if it still identifies this opened inode. On validation failure, leave
    // the unique partial name for explicit quiescent recovery instead of
    // risking deletion of a same-uid replacement installed after inspection.
    validation?;
    Ok(AttachedOutputFile {
        file,
        parent,
        basename,
        identity,
        label: label.to_owned(),
    })
}

#[cfg(unix)]
fn replace_invocation_regular_file_exact_with_hook<F>(
    parent: &RetainedDirectoryPath,
    basename: &CString,
    expected: &[u8],
    replacement: &[u8],
    maximum_bytes: u64,
    label: &str,
    before_rename: F,
) -> Result<(), String>
where
    F: FnOnce(RawFd, &CString),
{
    let (preimage, original_identity) =
        read_bounded_regular_file_at_with_identity(parent, basename, maximum_bytes, label)?;
    if preimage != expected {
        return Err(format!("{label} preimage does not match"));
    }
    let sequence = NEXT_PRIVATE_ROOT.fetch_add(1, Ordering::SeqCst);
    let temporary = CString::new(format!(".npa-replace-{}-{sequence}", std::process::id()))
        .map_err(|_| format!("{label} temporary name contains NUL"))?;
    parent.verify(label)?;
    let raw = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            temporary.as_ptr(),
            libc::O_RDWR | libc::O_CLOEXEC | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW,
            0o600,
        )
    };
    let mut file = fs::File::from(owned_fd(raw, &format!("create temporary {label}"))?);
    let opened_temporary = file_status(file.as_raw_fd())?;
    let temporary_identity = status_identity(&opened_temporary);
    let result = (|| -> Result<(), String> {
        let named_temporary = status_at(parent.as_raw_fd(), &temporary)?;
        if file_kind(&opened_temporary) != libc::S_IFREG
            || file_kind(&named_temporary) != libc::S_IFREG
            || temporary_identity != status_identity(&named_temporary)
            || opened_temporary.st_dev != parent.device
            || opened_temporary.st_mode & 0o777 != 0o600
        {
            return Err(format!("{label} temporary has invalid identity"));
        }
        file.write_all(replacement).map_err(display_error)?;
        file.sync_all().map_err(display_error)?;
        before_rename(parent.as_raw_fd(), &temporary);
        parent.verify(label)?;
        let named_temporary = status_at(parent.as_raw_fd(), &temporary)?;
        let opened_temporary_after = file_status(file.as_raw_fd())?;
        if file_kind(&named_temporary) != libc::S_IFREG
            || status_identity(&named_temporary) != temporary_identity
            || file_kind(&opened_temporary_after) != libc::S_IFREG
            || status_identity(&opened_temporary_after) != temporary_identity
        {
            return Err(format!("{label} temporary changed before publication"));
        }
        let current = status_at(parent.as_raw_fd(), basename)?;
        if file_kind(&current) != libc::S_IFREG || status_identity(&current) != original_identity {
            return Err(format!("{label} preimage changed before publication"));
        }
        if unsafe {
            libc::renameat(
                parent.as_raw_fd(),
                temporary.as_ptr(),
                parent.as_raw_fd(),
                basename.as_ptr(),
            )
        } != 0
        {
            return Err(display_error(std::io::Error::last_os_error()));
        }
        parent.verify(label)?;
        let published = status_at(parent.as_raw_fd(), basename)?;
        if file_kind(&published) != libc::S_IFREG
            || status_identity(&published) != temporary_identity
            || status_at_optional(parent.as_raw_fd(), &temporary)?.is_some()
        {
            return Err(format!("{label} publication changed identity"));
        }
        sync_directory(parent.as_raw_fd())
    })();
    // A failed replacement keeps its unique temporary name. Inspect-then-
    // unlink is not inode-conditional, so automatic cleanup could delete an
    // attacker-installed replacement. Explicit quiescent recovery owns it.
    result
}

/// A create-new output whose successful `sync_all` also proves that every
/// requested ancestor and the final basename still identify the opened inode.
pub struct AttachedOutputFile {
    file: fs::File,
    #[cfg(unix)]
    parent: RetainedDirectoryPath,
    #[cfg(unix)]
    basename: CString,
    #[cfg(unix)]
    identity: EntryIdentity,
    #[cfg(unix)]
    label: String,
}

/// An owner-only executable copied into a private root and retained together
/// with its opened inode, path ancestry, and exact source-byte digest.
pub struct AttachedExecutable {
    path: PathBuf,
    file: fs::File,
    maximum_bytes: u64,
    sha256: String,
    #[cfg(unix)]
    parent: RetainedDirectoryPath,
    #[cfg(unix)]
    basename: CString,
    #[cfg(unix)]
    identity: EntryIdentity,
    #[cfg(unix)]
    label: String,
}

/// A private executable capability retained outside every sealed output tree.
/// Linux executes the unlinked inode through its inherited descriptor. macOS,
/// where `/dev/fd` cannot execute the unlinked regular file, retains the
/// component-walked private scratch pathname and proves it still names the
/// same inode before and after every child. The exact pre-exec bytes are kept
/// separately for the final audit copy on both platforms.
pub struct DetachedExecutable {
    file: fs::File,
    maximum_bytes: u64,
    bytes: Vec<u8>,
    sha256: String,
    #[cfg(target_os = "macos")]
    path: PathBuf,
    #[cfg(target_os = "macos")]
    parent: RetainedDirectoryPath,
    #[cfg(target_os = "macos")]
    basename: CString,
    #[cfg(unix)]
    identity: EntryIdentity,
    #[cfg(unix)]
    label: String,
}

impl AttachedExecutable {
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn sha256(&self) -> &str {
        &self.sha256
    }

    /// Duplicate the retained executable inode for descriptor-based exec.
    /// The caller must keep this capability alive and call `verify` before
    /// and after the spawned process lifetime.
    pub fn try_clone_file(&self) -> Result<fs::File, String> {
        self.verify()?;
        self.file.try_clone().map_err(display_error)
    }

    pub fn read_all_bounded(&self) -> Result<Vec<u8>, String> {
        self.verify()?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::FileExt as _;
            let status = file_status(self.file.as_raw_fd())?;
            let length = usize::try_from(status.st_size).map_err(display_error)?;
            let mut bytes = vec![0_u8; length];
            let mut offset = 0_usize;
            while offset < bytes.len() {
                let read = self
                    .file
                    .read_at(
                        &mut bytes[offset..],
                        u64::try_from(offset).map_err(display_error)?,
                    )
                    .map_err(display_error)?;
                if read == 0 {
                    return Err("attached executable was truncated while reading".to_owned());
                }
                offset = offset
                    .checked_add(read)
                    .ok_or("executable read overflowed")?;
            }
            self.verify()?;
            Ok(bytes)
        }
        #[cfg(not(unix))]
        {
            Err("attached executable reads require Unix".to_owned())
        }
    }

    /// Close the writable creation descriptor before any benchmark process
    /// exists and return a read-only execution capability. Linux removes the
    /// scratch name; macOS retains its private, identity-bound name because
    /// that platform rejects execution through `/dev/fd`.
    pub fn detach_for_trusted_execution(self) -> Result<DetachedExecutable, String> {
        self.verify()?;
        let bytes = self.read_all_bounded()?;
        #[cfg(unix)]
        {
            self.parent.verify(&self.label)?;
            let opened = file_status(self.file.as_raw_fd())?;
            let named = status_at(self.parent.as_raw_fd(), &self.basename)?;
            if file_kind(&opened) != libc::S_IFREG
                || file_kind(&named) != libc::S_IFREG
                || status_identity(&opened) != self.identity
                || status_identity(&named) != self.identity
                || opened.st_mode & 0o777 != 0o700
                || opened.st_nlink != 1
            {
                return Err(format!("attached {} changed before detachment", self.label));
            }
            let read_only_raw = unsafe {
                libc::openat(
                    self.parent.as_raw_fd(),
                    self.basename.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
                )
            };
            if read_only_raw < 0 {
                return Err(format!(
                    "reopen {} read-only: {}",
                    self.label,
                    std::io::Error::last_os_error()
                ));
            }
            let read_only = unsafe { fs::File::from_raw_fd(read_only_raw) };
            let read_only_status = file_status(read_only.as_raw_fd())?;
            if file_kind(&read_only_status) != libc::S_IFREG
                || status_identity(&read_only_status) != self.identity
                || read_only_status.st_mode & 0o777 != 0o700
                || read_only_status.st_nlink != 1
            {
                return Err(format!("read-only {} identity changed", self.label));
            }
            // The O_RDWR creation descriptor must not cross the benchmark
            // process boundary. Only this independently opened read-only
            // descriptor survives the detach transition.
            drop(self.file);
            #[cfg(not(target_os = "macos"))]
            {
                if unsafe { libc::unlinkat(self.parent.as_raw_fd(), self.basename.as_ptr(), 0) }
                    != 0
                {
                    return Err(format!(
                        "detach {}: {}",
                        self.label,
                        std::io::Error::last_os_error()
                    ));
                }
                sync_directory(self.parent.as_raw_fd())?;
                self.parent.verify(&self.label)?;
                if status_at_optional(self.parent.as_raw_fd(), &self.basename)?.is_some() {
                    return Err(format!("detached {} name still exists", self.label));
                }
            }
            let detached = file_status(read_only.as_raw_fd())?;
            #[cfg(target_os = "macos")]
            let expected_links = 1;
            #[cfg(not(target_os = "macos"))]
            let expected_links = 0;
            if file_kind(&detached) != libc::S_IFREG
                || status_identity(&detached) != self.identity
                || detached.st_mode & 0o777 != 0o700
                || detached.st_nlink != expected_links
                || detached.st_size != opened.st_size
            {
                return Err(format!("detached {} inode is invalid", self.label));
            }
            #[cfg(target_os = "macos")]
            {
                self.parent.verify(&self.label)?;
                let named = status_at(self.parent.as_raw_fd(), &self.basename)?;
                if status_identity(&named) != self.identity
                    || file_kind(&named) != libc::S_IFREG
                    || named.st_mode & 0o777 != 0o700
                    || named.st_nlink != 1
                {
                    return Err(format!("private named {} changed", self.label));
                }
            }
            Ok(DetachedExecutable {
                file: read_only,
                maximum_bytes: self.maximum_bytes,
                bytes,
                sha256: self.sha256,
                #[cfg(target_os = "macos")]
                path: self.path,
                #[cfg(target_os = "macos")]
                parent: self.parent,
                #[cfg(target_os = "macos")]
                basename: self.basename,
                identity: self.identity,
                label: self.label,
            })
        }
        #[cfg(not(unix))]
        {
            let _ = bytes;
            Err("detached executable snapshots require Unix".to_owned())
        }
    }

    /// Prove that the executable remains attached at the requested path and
    /// that its same opened inode still contains the exact snapshotted bytes.
    pub fn verify(&self) -> Result<(), String> {
        #[cfg(unix)]
        {
            self.parent.verify(&self.label)?;
            let opened = file_status(self.file.as_raw_fd())?;
            let named = status_at(self.parent.as_raw_fd(), &self.basename)?;
            if file_kind(&opened) != libc::S_IFREG
                || file_kind(&named) != libc::S_IFREG
                || status_identity(&opened) != self.identity
                || status_identity(&named) != self.identity
                || opened.st_dev != self.parent.device
                || opened.st_mode & 0o777 != 0o700
                || opened.st_nlink != 1
                || opened.st_size < 0
                || u64::try_from(opened.st_size).map_err(display_error)? > self.maximum_bytes
            {
                return Err(format!("attached {} identity or mode changed", self.label));
            }
            let length = usize::try_from(opened.st_size).map_err(display_error)?;
            let digest = hash_open_file_fixed_chunks(&self.file, length, &self.label)?;
            let opened_after = file_status(self.file.as_raw_fd())?;
            let named_after = status_at(self.parent.as_raw_fd(), &self.basename)?;
            self.parent.verify(&self.label)?;
            if status_identity(&opened_after) != self.identity
                || status_identity(&named_after) != self.identity
                || opened_after.st_size != opened.st_size
                || digest != self.sha256
            {
                return Err(format!("attached {} bytes changed", self.label));
            }
            Ok(())
        }
        #[cfg(not(unix))]
        {
            let bytes = read_invocation_regular_file(&self.path, self.maximum_bytes, "executable")?;
            if hex_sha256(&bytes) != self.sha256 {
                return Err("attached executable bytes changed".to_owned());
            }
            Ok(())
        }
    }
}

/// Copy one executable into a temporary private directory before any child is
/// launched, then close its writable creation descriptor. Linux removes the
/// scratch pathname; macOS retains an identity-bound private name solely for
/// execution because anonymous `/dev/fd` execution is unavailable there.
pub fn detached_executable_snapshot(
    source_path: &Path,
    maximum_bytes: u64,
    label: &str,
) -> Result<DetachedExecutable, String> {
    #[cfg(unix)]
    {
        let scratch = ClosedPrivateDirectory::new("npa-detached-executable")?;
        let attached = scratch.create_executable_snapshot(
            Path::new("runner"),
            source_path,
            maximum_bytes,
            label,
        )?;
        let detached = attached.detach_for_trusted_execution()?;
        // Do not use an inspect-then-rmdir primitive at an online trust
        // boundary. Linux leaves an empty root and macOS leaves the named
        // private executable; explicit quiescent recovery owns either residue.
        scratch.leave_in_place();
        Ok(detached)
    }
    #[cfg(not(unix))]
    {
        let _ = (source_path, maximum_bytes, label);
        Err("detached executable snapshots require Unix".to_owned())
    }
}

/// Consume the dedicated descriptor through which this process was executed
/// and return its exact bytes. The descriptor must identify the read-only,
/// owner-executable inode produced by `DetachedExecutable` (anonymous on Linux
/// and privately named on macOS); taking ownership here also ensures it cannot
/// leak into any later child process.
pub fn consume_inherited_detached_executable(
    descriptor: i32,
    maximum_bytes: u64,
    label: &str,
) -> Result<Vec<u8>, String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileExt as _;

        if descriptor < 3 || maximum_bytes == 0 {
            return Err(format!("{label} inherited descriptor is invalid"));
        }
        // SAFETY: the closed controller contract dedicates this inherited fd
        // to the callee, which consumes and closes it exactly once here.
        let file = unsafe { fs::File::from_raw_fd(descriptor) };
        let before = file_status(file.as_raw_fd())?;
        // The mere presence of a well-formed inherited fd is not proof that
        // this process was executed from it. Cross-bind that capability to the
        // kernel's executing image before accepting its bytes as provenance.
        #[cfg(target_os = "linux")]
        let executing = {
            let path = CString::new("/proc/self/exe")
                .map_err(|_| format!("{label} executing-image path contains NUL"))?;
            let raw = unsafe { libc::open(path.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC) };
            fs::File::from(owned_fd(raw, &format!("open executing {label}"))?)
        };
        #[cfg(target_os = "macos")]
        let executing = {
            let current = std::env::current_exe().map_err(display_error)?;
            let (parent, basename) = open_absolute_parent(&current, label)?;
            parent.verify(label)?;
            let raw = unsafe {
                libc::openat(
                    parent.as_raw_fd(),
                    basename.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
                )
            };
            fs::File::from(owned_fd(raw, &format!("open executing {label}"))?)
        };
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        return Err(format!(
            "{label} executing-image identity is unsupported on this Unix platform"
        ));
        let executing_status = file_status(executing.as_raw_fd())?;
        if file_kind(&executing_status) != libc::S_IFREG
            || status_identity(&executing_status) != status_identity(&before)
        {
            return Err(format!(
                "{label} inherited executable does not identify the running image"
            ));
        }
        #[cfg(target_os = "macos")]
        let expected_links = 1;
        #[cfg(not(target_os = "macos"))]
        let expected_links = 0;
        if file_kind(&before) != libc::S_IFREG
            || before.st_mode & 0o777 != 0o700
            || before.st_nlink != expected_links
            || before.st_size < 0
            || u64::try_from(before.st_size).map_err(display_error)? > maximum_bytes
        {
            return Err(format!(
                "{label} inherited executable is not one bounded private owner executable"
            ));
        }
        let length = usize::try_from(before.st_size).map_err(display_error)?;
        let mut bytes = vec![0_u8; length];
        let mut offset = 0_usize;
        while offset < bytes.len() {
            let read = file
                .read_at(
                    &mut bytes[offset..],
                    u64::try_from(offset).map_err(display_error)?,
                )
                .map_err(display_error)?;
            if read == 0 {
                return Err(format!("{label} inherited executable was truncated"));
            }
            offset = offset
                .checked_add(read)
                .ok_or_else(|| format!("{label} inherited read offset overflowed"))?;
        }
        let after = file_status(file.as_raw_fd())?;
        let executing_after = file_status(executing.as_raw_fd())?;
        if status_identity(&after) != status_identity(&before)
            || status_identity(&executing_after) != status_identity(&before)
            || after.st_mode & 0o777 != 0o700
            || after.st_nlink != expected_links
            || after.st_size != before.st_size
        {
            return Err(format!(
                "{label} inherited executable changed while reading"
            ));
        }
        Ok(bytes)
    }
    #[cfg(not(unix))]
    {
        let _ = (descriptor, maximum_bytes);
        Err(format!(
            "{label} inherited executable binding requires Unix"
        ))
    }
}

impl DetachedExecutable {
    pub fn sha256(&self) -> &str {
        &self.sha256
    }

    pub fn audit_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Exact retained allocation charged by bounded long-lived controllers.
    pub fn audit_allocation_bytes(&self) -> usize {
        self.bytes.capacity()
    }

    /// Duplicate only the private scratch inode. No final-tree descriptor or
    /// pathname is exposed to the child.
    pub fn try_clone_file(&self) -> Result<fs::File, String> {
        self.verify()?;
        self.file.try_clone().map_err(display_error)
    }

    /// Return the platform execution path for a duplicate inherited fd.
    pub fn execution_path(&self, descriptor: RawFd) -> Result<PathBuf, String> {
        self.verify()?;
        #[cfg(target_os = "linux")]
        {
            Ok(PathBuf::from(format!("/proc/self/fd/{descriptor}")))
        }
        #[cfg(target_os = "macos")]
        {
            let _ = descriptor;
            Ok(self.path.clone())
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            let _ = descriptor;
            Err("private descriptor-bound execution is unsupported here".to_owned())
        }
    }

    pub fn verify(&self) -> Result<(), String> {
        #[cfg(unix)]
        {
            let before = file_status(self.file.as_raw_fd())?;
            #[cfg(target_os = "macos")]
            let expected_links = 1;
            #[cfg(not(target_os = "macos"))]
            let expected_links = 0;
            if file_kind(&before) != libc::S_IFREG
                || status_identity(&before) != self.identity
                || before.st_mode & 0o777 != 0o700
                || before.st_nlink != expected_links
                || before.st_size < 0
                || u64::try_from(before.st_size).map_err(display_error)? > self.maximum_bytes
            {
                return Err(format!("detached {} inode changed", self.label));
            }
            let digest =
                hash_and_compare_open_file_fixed_chunks(&self.file, &self.bytes, &self.label)?;
            #[cfg(target_os = "macos")]
            {
                self.parent.verify(&self.label)?;
                let named = status_at(self.parent.as_raw_fd(), &self.basename)?;
                if file_kind(&named) != libc::S_IFREG
                    || status_identity(&named) != self.identity
                    || named.st_mode & 0o777 != 0o700
                    || named.st_nlink != 1
                {
                    return Err(format!("private named {} changed", self.label));
                }
            }
            let after = file_status(self.file.as_raw_fd())?;
            if status_identity(&after) != self.identity
                || after.st_mode & 0o777 != 0o700
                || after.st_nlink != expected_links
                || after.st_size != before.st_size
                || digest != self.sha256
            {
                return Err(format!("detached {} bytes changed", self.label));
            }
            Ok(())
        }
        #[cfg(not(unix))]
        {
            Err("detached executable verification requires Unix".to_owned())
        }
    }
}

impl std::io::Write for AttachedOutputFile {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.file.write(bytes)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.file.flush()
    }
}

impl AttachedOutputFile {
    /// Duplicate the opened inode for a child process while retaining this
    /// capability so the caller can revalidate the named path after the child
    /// has finished writing.
    pub fn try_clone_file(&self) -> std::io::Result<fs::File> {
        self.file.try_clone()
    }

    pub fn sync_all(&self) -> std::io::Result<()> {
        self.file.sync_all()?;
        #[cfg(unix)]
        {
            self.parent
                .verify(&self.label)
                .map_err(std::io::Error::other)?;
            let named = status_at(self.parent.as_raw_fd(), &self.basename)
                .map_err(std::io::Error::other)?;
            if file_kind(&named) != libc::S_IFREG || status_identity(&named) != self.identity {
                return Err(std::io::Error::other(format!(
                    "created {} changed while writing",
                    self.label
                )));
            }
            let opened = file_status(self.file.as_raw_fd()).map_err(std::io::Error::other)?;
            if opened.st_mode & 0o777 != 0o600 || opened.st_nlink != 1 {
                return Err(std::io::Error::other(format!(
                    "created {} is not owner-only and single-link",
                    self.label
                )));
            }
            sync_directory(self.parent.as_raw_fd()).map_err(std::io::Error::other)?;
        }
        Ok(())
    }

    /// Read the stable opened inode without reopening its pathname. The file
    /// must still be attached to the retained parent chain and its size must
    /// remain unchanged for the complete bounded read.
    pub fn read_all_bounded(&self, maximum_bytes: u64) -> Result<Vec<u8>, String> {
        self.sync_all().map_err(display_error)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::FileExt as _;

            let before = file_status(self.file.as_raw_fd())?;
            if file_kind(&before) != libc::S_IFREG
                || status_identity(&before) != self.identity
                || before.st_size < 0
                || u64::try_from(before.st_size).map_err(display_error)? > maximum_bytes
            {
                return Err(format!(
                    "created {} is not a bounded regular file",
                    self.label
                ));
            }
            let length = usize::try_from(before.st_size).map_err(display_error)?;
            let mut bytes = vec![0_u8; length];
            let mut offset = 0_usize;
            while offset < bytes.len() {
                let read = self
                    .file
                    .read_at(
                        &mut bytes[offset..],
                        u64::try_from(offset).map_err(display_error)?,
                    )
                    .map_err(display_error)?;
                if read == 0 {
                    return Err(format!(
                        "created {} was truncated while reading",
                        self.label
                    ));
                }
                offset = offset
                    .checked_add(read)
                    .ok_or_else(|| format!("created {} read offset overflowed", self.label))?;
            }
            let after = file_status(self.file.as_raw_fd())?;
            if status_identity(&after) != self.identity
                || file_kind(&after) != libc::S_IFREG
                || after.st_size != before.st_size
                || after.st_mode & 0o777 != 0o600
                || after.st_nlink != 1
            {
                return Err(format!("created {} changed while reading", self.label));
            }
            self.parent.verify(&self.label)?;
            let named = status_at(self.parent.as_raw_fd(), &self.basename)?;
            if file_kind(&named) != libc::S_IFREG || status_identity(&named) != self.identity {
                return Err(format!("created {} changed while reading", self.label));
            }
            Ok(bytes)
        }
        #[cfg(not(unix))]
        {
            use std::io::{Seek as _, SeekFrom};

            let mut file = self.file.try_clone().map_err(display_error)?;
            file.seek(SeekFrom::Start(0)).map_err(display_error)?;
            let mut bytes = Vec::new();
            let read_limit = maximum_bytes
                .checked_add(1)
                .ok_or("created output byte limit cannot be u64::MAX")?;
            file.take(read_limit)
                .read_to_end(&mut bytes)
                .map_err(display_error)?;
            if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
                return Err("created output exceeds its byte limit".to_owned());
            }
            Ok(bytes)
        }
    }

    /// Replace the complete contents of this same opened, still-attached inode.
    /// This never renames or reopens the output name; a partial write failure
    /// leaves an unsealed residue for explicit recovery.
    pub fn replace_contents(
        &mut self,
        expected: &[u8],
        replacement: &[u8],
        maximum_bytes: u64,
    ) -> Result<(), String> {
        if u64::try_from(replacement.len()).map_err(display_error)? > maximum_bytes {
            return Err("replacement output exceeds its byte limit".to_owned());
        }
        if self.read_all_bounded(maximum_bytes)? != expected {
            return Err("attached output preimage changed before replacement".to_owned());
        }
        self.file.set_len(0).map_err(display_error)?;
        self.file
            .seek(std::io::SeekFrom::Start(0))
            .map_err(display_error)?;
        self.file.write_all(replacement).map_err(display_error)?;
        self.sync_all().map_err(display_error)?;
        if self.read_all_bounded(maximum_bytes)? != replacement {
            return Err("attached output replacement bytes did not persist".to_owned());
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EntryIdentity {
    device: u64,
    inode: u64,
}

#[cfg(unix)]
fn status_identity(status: &libc::stat) -> EntryIdentity {
    EntryIdentity {
        device: u64::try_from(status.st_dev).unwrap_or(u64::MAX),
        inode: status.st_ino,
    }
}

/// Every opened directory in one requested path, retained together with the
/// parent/name relation by which it was reached. A live final directory fd is
/// not sufficient: after an ancestor rename it would still access a detached
/// tree while falsely labelling it with the caller's original path.
#[cfg(unix)]
struct RetainedDirectoryPath {
    anchor: OwnedFd,
    descendants: Vec<OwnedFd>,
    names: Vec<CString>,
    identities: Vec<EntryIdentity>,
    device: libc::dev_t,
}

#[cfg(unix)]
impl RetainedDirectoryPath {
    fn from_anchor(anchor: OwnedFd, label: &str) -> Result<Self, String> {
        let status = file_status(anchor.as_raw_fd())?;
        if file_kind(&status) != libc::S_IFDIR {
            return Err(format!("{label} path anchor is not a directory"));
        }
        Ok(Self {
            anchor,
            descendants: Vec::new(),
            names: Vec::new(),
            identities: vec![status_identity(&status)],
            device: status.st_dev,
        })
    }

    fn open_child(mut self, name: CString, label: &str) -> Result<Self, String> {
        self.verify(label)?;
        let parent = self.descendants.last().unwrap_or(&self.anchor);
        let named = status_at(parent.as_raw_fd(), &name)?;
        if file_kind(&named) != libc::S_IFDIR || named.st_dev != self.device {
            return Err(format!(
                "{label} traverses a non-directory or different device"
            ));
        }
        let child = open_directory_at(parent.as_raw_fd(), &name)?;
        let opened = file_status(child.as_raw_fd())?;
        if file_kind(&opened) != libc::S_IFDIR
            || opened.st_dev != self.device
            || status_identity(&opened) != status_identity(&named)
        {
            return Err(format!("{label} directory changed while it was opened"));
        }
        self.names.push(name);
        self.identities.push(status_identity(&opened));
        self.descendants.push(child);
        self.verify(label)?;
        Ok(self)
    }

    fn verify(&self, label: &str) -> Result<(), String> {
        if self.descendants.len().saturating_add(1) != self.identities.len()
            || self.names.len() != self.descendants.len()
        {
            return Err(format!("{label} retained path is internally inconsistent"));
        }
        for (index, directory) in std::iter::once(&self.anchor)
            .chain(self.descendants.iter())
            .enumerate()
        {
            let opened = file_status(directory.as_raw_fd())?;
            if file_kind(&opened) != libc::S_IFDIR
                || opened.st_dev != self.device
                || status_identity(&opened) != self.identities[index]
            {
                return Err(format!("{label} directory identity changed"));
            }
            if let Some(name) = self.names.get(index) {
                let named = status_at(directory.as_raw_fd(), name)?;
                if file_kind(&named) != libc::S_IFDIR
                    || named.st_dev != self.device
                    || status_identity(&named) != self.identities[index + 1]
                {
                    return Err(format!("{label} ancestor binding changed"));
                }
            }
        }
        Ok(())
    }
}

#[cfg(unix)]
impl AsRawFd for RetainedDirectoryPath {
    fn as_raw_fd(&self) -> RawFd {
        self.descendants.last().unwrap_or(&self.anchor).as_raw_fd()
    }
}

type ClosedTreeCatalog = (
    BTreeSet<PathBuf>,
    BTreeSet<PathBuf>,
    BTreeMap<PathBuf, EntryIdentity>,
);

/// An opaque, identity-bearing snapshot of one complete private-tree cleanup
/// catalog. It can only be consumed by the same still-attached root from which
/// it was captured.
pub struct ClosedCleanupCatalog {
    root_path: PathBuf,
    root_identity: EntryIdentity,
    files: BTreeSet<PathBuf>,
    directories: BTreeSet<PathBuf>,
    identities: BTreeMap<PathBuf, EntryIdentity>,
}

/// Authenticated metadata and bytes for one exact sealed-tree member. The
/// metadata is taken from and rechecked against the same opened inode; callers
/// must not synthesize mode/link claims from a pathname-only catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SealedRegularFile {
    pub bytes: Vec<u8>,
    pub mode: u32,
    pub link_count: u64,
}

#[cfg(not(unix))]
fn metadata_identity(_metadata: &fs::Metadata) -> EntryIdentity {
    EntryIdentity {
        device: 0,
        inode: 0,
    }
}

/// A newly-created, owner-only directory anchored in a canonical real parent.
pub struct ClosedPrivateDirectory {
    path: PathBuf,
    parent: PathBuf,
    parent_identity: EntryIdentity,
    root_identity: EntryIdentity,
    name_prefix: String,
    remove_empty_on_drop: bool,
    #[cfg(unix)]
    parent_fd: RetainedDirectoryPath,
    #[cfg(unix)]
    root_fd: OwnedFd,
    #[cfg(unix)]
    root_name: CString,
}

/// A caller-selected final-directory destination whose complete parent chain
/// and initial absence were retained before any measured child was started.
/// Creating the directory later consumes this capability and never reopens
/// the parent by pathname.
pub struct PreparedPrivateDirectoryDestination {
    path: PathBuf,
    parent: PathBuf,
    name_prefix: String,
    label: String,
    #[cfg(unix)]
    parent_fd: RetainedDirectoryPath,
    #[cfg(unix)]
    root_name: CString,
}

/// Retain an absent absolute destination without creating it.  This is the
/// preparation half of direct-final sealed publication: callers prepare before
/// child execution and consume only after the child phase is quiescent.
pub fn prepare_new_absolute_private_directory(
    path: &Path,
    label: &str,
) -> Result<PreparedPrivateDirectoryDestination, String> {
    #[cfg(not(unix))]
    {
        let _ = path;
        return Err(format!(
            "{label} sealed final-directory preparation requires Unix file-mode and link-count verification"
        ));
    }
    if label.is_empty()
        || !label
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        || path
            .file_name()
            .and_then(|name| name.to_str())
            .is_none_or(|name| {
                name.is_empty()
                    || !name.bytes().all(|byte| {
                        byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.')
                    })
            })
    {
        return Err(format!("{label} is not a safe private-directory label"));
    }
    #[cfg(unix)]
    {
        let (parent_fd, root_name) = open_absolute_parent(path, label)?;
        parent_fd.verify(label)?;
        if status_at_optional(parent_fd.as_raw_fd(), &root_name)?.is_some() {
            return Err(format!("{label} already exists"));
        }
        let parent = path
            .parent()
            .ok_or_else(|| format!("{label} has no parent"))?
            .to_owned();
        let name_prefix = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("{label} basename is not UTF-8"))?
            .to_owned();
        Ok(PreparedPrivateDirectoryDestination {
            path: path.to_owned(),
            parent,
            name_prefix,
            label: label.to_owned(),
            parent_fd,
            root_name,
        })
    }
}

impl PreparedPrivateDirectoryDestination {
    /// Recheck the retained parent chain and continued absence without
    /// consuming this destination.
    pub fn verify_absent(&self) -> Result<(), String> {
        #[cfg(unix)]
        {
            self.parent_fd.verify(&self.label)?;
            if status_at_optional(self.parent_fd.as_raw_fd(), &self.root_name)?.is_some() {
                return Err(format!("{} appeared after preparation", self.label));
            }
            self.parent_fd.verify(&self.label)
        }
        #[cfg(not(unix))]
        {
            Err(format!("{} requires Unix", self.label))
        }
    }

    pub fn create(self) -> Result<ClosedPrivateDirectory, String> {
        #[cfg(unix)]
        {
            self.create_with_hook(|| Ok(()))
        }
        #[cfg(not(unix))]
        {
            Err(format!("{} requires Unix", self.label))
        }
    }

    #[cfg(unix)]
    fn create_with_hook<F>(self, after_mkdir: F) -> Result<ClosedPrivateDirectory, String>
    where
        F: FnOnce() -> Result<(), String>,
    {
        self.verify_absent()?;
        if unsafe { libc::mkdirat(self.parent_fd.as_raw_fd(), self.root_name.as_ptr(), 0o700) } != 0
        {
            return Err(format!(
                "create {}: {}",
                self.label,
                std::io::Error::last_os_error()
            ));
        }
        // Any failure after mkdir preserves the unique name. There is no
        // portable identity-conditional rmdir under same-owner namespace
        // mutation.
        after_mkdir()?;
        let root_fd = open_directory_at(self.parent_fd.as_raw_fd(), &self.root_name)?;
        let parent_status = file_status(self.parent_fd.as_raw_fd())?;
        let root_status = file_status(root_fd.as_raw_fd())?;
        let named_status = status_at(self.parent_fd.as_raw_fd(), &self.root_name)?;
        let parent_identity = status_identity(&parent_status);
        let root_identity = status_identity(&root_status);
        if file_kind(&parent_status) != libc::S_IFDIR
            || file_kind(&root_status) != libc::S_IFDIR
            || file_kind(&named_status) != libc::S_IFDIR
            || status_identity(&named_status) != root_identity
            || root_identity.device != parent_identity.device
            || root_status.st_mode & 0o777 != 0o700
        {
            return Err(format!(
                "created {} has invalid identity or mode",
                self.label
            ));
        }
        self.parent_fd.verify(&self.label)?;
        sync_directory(self.parent_fd.as_raw_fd())?;
        Ok(ClosedPrivateDirectory {
            path: self.path,
            parent: self.parent,
            parent_identity,
            root_identity,
            name_prefix: self.name_prefix,
            remove_empty_on_drop: false,
            parent_fd: self.parent_fd,
            root_fd,
            root_name: self.root_name,
        })
    }
}

/// Create a new owner-only directory at a caller-selected absolute path and
/// retain its complete parent/name chain. Unlike staging publication, this
/// creates the final namespace entry itself and never renames a source name.
pub fn create_new_absolute_private_directory(
    path: &Path,
    label: &str,
) -> Result<ClosedPrivateDirectory, String> {
    prepare_new_absolute_private_directory(path, label)?.create()
}

impl ClosedPrivateDirectory {
    /// Sync the retained directory and its retained parent after every named
    /// child has been written, validated, and (for a sealed commit) the seal
    /// has been created last.
    pub fn sync_root_and_parent(&self) -> Result<(), String> {
        self.verify_attached_root()?;
        #[cfg(unix)]
        {
            sync_directory(self.root_fd.as_raw_fd())?;
            self.verify_attached_root()?;
            sync_directory(self.parent_fd.as_raw_fd())
        }
        #[cfg(not(unix))]
        {
            Ok(())
        }
    }
}

impl ClosedPrivateDirectory {
    pub fn new(label: &str) -> Result<Self, String> {
        let parent = std::env::temp_dir().canonicalize().map_err(display_error)?;
        Self::new_in(&parent, label)
    }

    pub fn new_in(raw_parent: &Path, label: &str) -> Result<Self, String> {
        if label.is_empty()
            || !label
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        {
            return Err("private-directory label is not a safe path component".to_owned());
        }
        if !raw_parent.is_absolute() {
            return Err("temporary parent must be absolute".to_owned());
        }
        let raw_metadata = fs::symlink_metadata(raw_parent).map_err(display_error)?;
        if !raw_metadata.file_type().is_dir() || raw_metadata.file_type().is_symlink() {
            return Err("temporary parent is not a real directory".to_owned());
        }
        let parent = raw_parent.canonicalize().map_err(display_error)?;
        if parent != raw_parent {
            return Err("temporary parent must already be canonical".to_owned());
        }
        let name_prefix = format!("{label}-{}-", std::process::id());

        #[cfg(unix)]
        {
            let parent_fd = open_absolute_directory(&parent)?;
            parent_fd.verify("private-directory parent")?;
            let parent_status = file_status(parent_fd.as_raw_fd())?;
            if file_kind(&parent_status) != libc::S_IFDIR {
                return Err("canonical temporary parent is not a directory".to_owned());
            }
            let parent_identity = status_identity(&parent_status);
            for _ in 0..1_000 {
                let sequence = NEXT_PRIVATE_ROOT.fetch_add(1, Ordering::SeqCst);
                let name = format!("{name_prefix}{sequence}");
                let root_name = CString::new(name.as_bytes())
                    .map_err(|_| "private-directory name contains NUL".to_owned())?;
                parent_fd.verify("private-directory parent")?;
                let created =
                    unsafe { libc::mkdirat(parent_fd.as_raw_fd(), root_name.as_ptr(), 0o700) };
                if created != 0 {
                    let error = std::io::Error::last_os_error();
                    if error.kind() == std::io::ErrorKind::AlreadyExists {
                        continue;
                    }
                    return Err(format!("create private directory: {error}"));
                }
                let root_fd = match open_directory_at(parent_fd.as_raw_fd(), &root_name) {
                    Ok(root_fd) => root_fd,
                    Err(error) => {
                        let _ = unsafe {
                            libc::unlinkat(
                                parent_fd.as_raw_fd(),
                                root_name.as_ptr(),
                                libc::AT_REMOVEDIR,
                            )
                        };
                        return Err(error);
                    }
                };
                let root_status = file_status(root_fd.as_raw_fd())?;
                let root_identity = status_identity(&root_status);
                if file_kind(&root_status) != libc::S_IFDIR
                    || root_identity.device != parent_identity.device
                    || root_status.st_mode & 0o777 != 0o700
                {
                    return Err("private directory identity, device, or mode is invalid".to_owned());
                }
                let named_status = status_at(parent_fd.as_raw_fd(), &root_name)?;
                if status_identity(&named_status) != root_identity
                    || file_kind(&named_status) != libc::S_IFDIR
                {
                    return Err("private directory changed during creation".to_owned());
                }
                parent_fd.verify("private-directory parent")?;
                return Ok(Self {
                    path: parent.join(name),
                    parent,
                    parent_identity,
                    root_identity,
                    name_prefix,
                    remove_empty_on_drop: true,
                    parent_fd,
                    root_fd,
                    root_name,
                });
            }
            Err("could not allocate a unique private directory".to_owned())
        }

        #[cfg(not(unix))]
        {
            let parent_metadata = fs::symlink_metadata(&parent).map_err(display_error)?;
            let parent_identity = metadata_identity(&parent_metadata);
            for _ in 0..1_000 {
                let sequence = NEXT_PRIVATE_ROOT.fetch_add(1, Ordering::SeqCst);
                let path = parent.join(format!("{name_prefix}{sequence}"));
                match fs::create_dir(&path) {
                    Ok(()) => {
                        let metadata = fs::symlink_metadata(&path).map_err(display_error)?;
                        return Ok(Self {
                            path,
                            parent,
                            parent_identity,
                            root_identity: metadata_identity(&metadata),
                            name_prefix,
                            remove_empty_on_drop: true,
                        });
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => return Err(display_error(error)),
                }
            }
            Err("could not allocate a unique private directory".to_owned())
        }
    }

    /// Adopt an already-created owner-only empty directory. This is used when
    /// a shell controller creates a private root before launching Rust.
    pub fn open_existing(path: &Path, label: &str) -> Result<Self, String> {
        if label.is_empty()
            || !label
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            || !path.is_absolute()
        {
            return Err("existing private-directory label/path is invalid".to_owned());
        }
        let parent = path
            .parent()
            .ok_or("existing private directory has no parent")?;
        let canonical_parent = parent.canonicalize().map_err(display_error)?;
        if canonical_parent != parent {
            return Err("existing private-directory parent must be canonical".to_owned());
        }
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("existing private directory has non-UTF-8 name")?;
        let shell_prefix = format!("{label}.");
        let hidden_shell_prefix = format!(".{label}.");
        let rust_prefix = format!("{label}-");
        let name_prefix = if label.ends_with("-final")
            && !name.is_empty()
            && name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
        {
            name.to_owned()
        } else if name.strip_prefix(&shell_prefix).is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_alphanumeric())
        }) {
            shell_prefix
        } else if name
            .strip_prefix(&hidden_shell_prefix)
            .is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_alphanumeric())
            })
        {
            hidden_shell_prefix
        } else if name.strip_prefix(&rust_prefix).is_some_and(|suffix| {
            suffix.split_once('-').is_some_and(|(pid, sequence)| {
                !pid.is_empty()
                    && !sequence.is_empty()
                    && pid.bytes().all(|byte| byte.is_ascii_digit())
                    && sequence.bytes().all(|byte| byte.is_ascii_digit())
            })
        }) {
            rust_prefix
        } else {
            return Err("existing private-directory name is outside its prefix grammar".to_owned());
        };
        #[cfg(unix)]
        {
            let parent_fd = open_absolute_directory(parent)?;
            parent_fd.verify("existing private-directory parent")?;
            let root_name = CString::new(name.as_bytes())
                .map_err(|_| "existing private-directory name contains NUL".to_owned())?;
            let root_fd = open_directory_at(parent_fd.as_raw_fd(), &root_name)?;
            let parent_status = file_status(parent_fd.as_raw_fd())?;
            let root_status = file_status(root_fd.as_raw_fd())?;
            let named_status = status_at(parent_fd.as_raw_fd(), &root_name)?;
            let parent_identity = status_identity(&parent_status);
            let root_identity = status_identity(&root_status);
            if file_kind(&parent_status) != libc::S_IFDIR
                || file_kind(&root_status) != libc::S_IFDIR
                || file_kind(&named_status) != libc::S_IFDIR
                || status_identity(&named_status) != root_identity
                || root_identity.device != parent_identity.device
                || root_status.st_mode & 0o777 != 0o700
            {
                return Err("existing private directory has invalid identity or mode".to_owned());
            }
            parent_fd.verify("existing private-directory parent")?;
            Ok(Self {
                path: path.to_owned(),
                parent: parent.to_owned(),
                parent_identity,
                root_identity,
                name_prefix,
                remove_empty_on_drop: !label.ends_with("-final"),
                parent_fd,
                root_fd,
                root_name,
            })
        }
        #[cfg(not(unix))]
        {
            let parent_metadata = fs::symlink_metadata(parent).map_err(display_error)?;
            let root_metadata = fs::symlink_metadata(path).map_err(display_error)?;
            Ok(Self {
                path: path.to_owned(),
                parent: parent.to_owned(),
                parent_identity: metadata_identity(&parent_metadata),
                root_identity: metadata_identity(&root_metadata),
                name_prefix,
                remove_empty_on_drop: !label.ends_with("-final"),
            })
        }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Consume this capability while deliberately leaving its namespace
    /// entry in place. Sealed final trees and unsealed failure residues use
    /// this transition: neither may be removed by a best-effort `Drop` path.
    pub fn leave_in_place(mut self) {
        self.remove_empty_on_drop = false;
    }

    /// Require this retained root to be the exact directory identified by a
    /// shell-side `device:inode:uid:mode` token captured at creation time.
    ///
    /// This closes the handoff between a shell controller that creates a
    /// private directory and a Rust process that later adopts it: replacing
    /// the directory at the same pathname cannot redirect publication or
    /// cleanup to the replacement inode.
    pub fn verify_external_identity_token(&self, expected: &str) -> Result<(), String> {
        self.verify_attached_root()?;
        #[cfg(unix)]
        {
            let status = file_status(self.root_fd.as_raw_fd())?;
            let expected_fields = expected.split(':').collect::<Vec<_>>();
            if expected_fields.len() != 4
                || !expected_fields[..3].iter().all(|field| {
                    !field.is_empty() && field.bytes().all(|byte| byte.is_ascii_digit())
                })
                || expected_fields[3].len() != 3
                || !expected_fields[3]
                    .bytes()
                    .all(|byte| matches!(byte, b'0'..=b'7'))
            {
                return Err("private-directory external identity token is malformed".to_owned());
            }
            let actual = format!(
                "{}:{}:{}:{:o}",
                status.st_dev,
                status.st_ino,
                status.st_uid,
                status.st_mode & 0o777
            );
            if actual != expected {
                return Err("private-directory external identity token mismatch".to_owned());
            }
            self.verify_attached_root()
        }
        #[cfg(not(unix))]
        {
            let _ = expected;
            Err("private-directory external identity tokens require Unix metadata".to_owned())
        }
    }

    /// Serialize the retained root identity for a shell/controller handoff.
    pub fn external_identity_token(&self) -> Result<String, String> {
        self.verify_attached_root()?;
        #[cfg(unix)]
        {
            let status = file_status(self.root_fd.as_raw_fd())?;
            Ok(format!(
                "{}:{}:{}:{:o}",
                status.st_dev,
                status.st_ino,
                status.st_uid,
                status.st_mode & 0o777
            ))
        }
        #[cfg(not(unix))]
        {
            Err("private-directory external identity tokens require Unix metadata".to_owned())
        }
    }

    /// Create a directory relative to the retained root descriptor.
    pub fn create_directory(&self, relative: &Path) -> Result<(), String> {
        validate_relative(relative)?;
        #[cfg(unix)]
        {
            let (parent, basename) = self.open_relative_parent(relative)?;
            self.verify_attached_root()?;
            if unsafe { libc::mkdirat(parent.as_raw_fd(), basename.as_ptr(), 0o700) } != 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            let directory = open_directory_at(parent.as_raw_fd(), &basename)?;
            let status = file_status(directory.as_raw_fd())?;
            let named = status_at(parent.as_raw_fd(), &basename)?;
            if file_kind(&status) != libc::S_IFDIR
                || file_kind(&named) != libc::S_IFDIR
                || status_identity(&status) != status_identity(&named)
                || status_identity(&status).device != self.root_identity.device
                || status.st_mode & 0o777 != 0o700
            {
                return Err("created private subdirectory has invalid identity or mode".to_owned());
            }
            parent.verify("private subdirectory parent")?;
            self.verify_attached_root()?;
            sync_directory(parent.as_raw_fd())?;
            Ok(())
        }
        #[cfg(not(unix))]
        {
            fs::create_dir(self.path.join(relative)).map_err(display_error)
        }
    }

    /// Create every missing directory component with mode 0700. Existing
    /// components must be same-device directories reachable without symlinks.
    pub fn create_directories(&self, relative: &Path) -> Result<(), String> {
        validate_relative(relative)?;
        #[cfg(unix)]
        {
            self.verify_attached_root()?;
            let mut parent = RetainedDirectoryPath::from_anchor(
                duplicate_fd(self.root_fd.as_raw_fd())?,
                "private directory path",
            )?;
            for component in relative.components() {
                let Component::Normal(component) = component else {
                    return Err("private path component is not normalized".to_owned());
                };
                let component = c_string(component)?;
                self.verify_attached_root()?;
                if unsafe { libc::mkdirat(parent.as_raw_fd(), component.as_ptr(), 0o700) } != 0 {
                    let error = std::io::Error::last_os_error();
                    if error.kind() != std::io::ErrorKind::AlreadyExists {
                        return Err(display_error(error));
                    }
                } else {
                    sync_directory(parent.as_raw_fd())?;
                }
                parent = parent.open_child(component, "private directory path")?;
                let status = file_status(parent.as_raw_fd())?;
                if file_kind(&status) != libc::S_IFDIR
                    || status_identity(&status).device != self.root_identity.device
                    || status.st_mode & 0o777 != 0o700
                {
                    return Err(
                        "private directory component has invalid identity or mode".to_owned()
                    );
                }
            }
            parent.verify("private directory path")?;
            self.verify_attached_root()?;
            Ok(())
        }
        #[cfg(not(unix))]
        {
            fs::create_dir_all(self.path.join(relative)).map_err(display_error)
        }
    }

    /// Create one regular file with create-new/no-follow semantics.
    pub fn create_new_file(&self, relative: &Path, bytes: &[u8]) -> Result<(), String> {
        let mut file = self.create_new_file_handle(relative)?;
        file.write_all(bytes).map_err(display_error)?;
        file.sync_all().map_err(display_error)
    }

    /// Create and retain one regular output capability without reopening its
    /// path. Callers may clone its opened inode for `Stdio`, then use
    /// `sync_all` and `read_all_bounded` to prove that the same inode remained
    /// attached after the child exits.
    pub fn create_new_file_handle(&self, relative: &Path) -> Result<AttachedOutputFile, String> {
        validate_relative(relative)?;
        #[cfg(unix)]
        {
            let (parent, basename) = self.open_relative_parent(relative)?;
            parent.verify("private file parent")?;
            self.verify_attached_root()?;
            let raw = unsafe {
                libc::openat(
                    parent.as_raw_fd(),
                    basename.as_ptr(),
                    libc::O_RDWR
                        | libc::O_CLOEXEC
                        | libc::O_CREAT
                        | libc::O_EXCL
                        | libc::O_NOFOLLOW,
                    0o600,
                )
            };
            if raw < 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            let file = unsafe { fs::File::from_raw_fd(raw) };
            let opened = file_status(file.as_raw_fd())?;
            let named = status_at(parent.as_raw_fd(), &basename)?;
            if file_kind(&opened) != libc::S_IFREG
                || file_kind(&named) != libc::S_IFREG
                || status_identity(&opened) != status_identity(&named)
                || status_identity(&opened).device != self.root_identity.device
                || opened.st_mode & 0o777 != 0o600
                || opened.st_nlink != 1
            {
                return Err(
                    "created private file has invalid identity, device, kind, or mode".to_owned(),
                );
            }
            self.verify_attached_root()?;
            parent.verify("private file parent")?;
            sync_directory(parent.as_raw_fd())?;
            Ok(AttachedOutputFile {
                file,
                parent,
                basename,
                identity: status_identity(&opened),
                label: format!("private file `{}`", relative.display()),
            })
        }
        #[cfg(not(unix))]
        {
            let file = fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(self.path.join(relative))
                .map_err(display_error)?;
            Ok(AttachedOutputFile { file })
        }
    }

    /// Snapshot one caller-selected executable into this private root. The
    /// source bytes are read through the retained invocation path and the
    /// private copy remains attached to an opened inode for pre/post-spawn
    /// verification.
    pub fn create_executable_snapshot(
        &self,
        relative: &Path,
        source_path: &Path,
        maximum_bytes: u64,
        label: &str,
    ) -> Result<AttachedExecutable, String> {
        if maximum_bytes == 0 {
            return Err(format!("{label} byte limit must be positive"));
        }
        validate_relative(relative)?;
        let bytes = read_invocation_regular_file(source_path, maximum_bytes, label)?;
        if bytes.is_empty() {
            return Err(format!("{label} is empty"));
        }
        let sha256 = hex_sha256(&bytes);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            let mut output = self.create_new_file_handle(relative)?;
            output.write_all(&bytes).map_err(display_error)?;
            output.sync_all().map_err(display_error)?;
            output
                .file
                .set_permissions(fs::Permissions::from_mode(0o700))
                .map_err(display_error)?;
            output.file.sync_all().map_err(display_error)?;
            let opened = file_status(output.file.as_raw_fd())?;
            let named = status_at(output.parent.as_raw_fd(), &output.basename)?;
            if file_kind(&opened) != libc::S_IFREG
                || file_kind(&named) != libc::S_IFREG
                || status_identity(&opened) != output.identity
                || status_identity(&named) != output.identity
                || opened.st_mode & 0o777 != 0o700
                || opened.st_nlink != 1
            {
                return Err(format!("snapshotted {label} has invalid identity or mode"));
            }
            let path = self.path.join(relative);
            let executable = AttachedExecutable {
                path,
                file: output.file,
                maximum_bytes,
                sha256,
                parent: output.parent,
                basename: output.basename,
                identity: output.identity,
                label: label.to_owned(),
            };
            executable.verify()?;
            Ok(executable)
        }
        #[cfg(not(unix))]
        {
            let path = self.path.join(relative);
            let mut output = self.create_new_file_handle(relative)?;
            output.write_all(&bytes).map_err(display_error)?;
            output.sync_all().map_err(display_error)?;
            Ok(AttachedExecutable {
                path,
                file: output.file,
                maximum_bytes,
                sha256,
            })
        }
    }

    /// Atomically publish replacement bytes only after the current regular
    /// file matches the exact expected preimage. The temporary file and rename
    /// are both relative to one retained parent descriptor.
    pub fn replace_exact_file(
        &self,
        relative: &Path,
        expected: &[u8],
        replacement: &[u8],
    ) -> Result<(), String> {
        self.replace_exact_file_with_hook(relative, expected, replacement, |_| {})
    }

    fn replace_exact_file_with_hook<F>(
        &self,
        relative: &Path,
        expected: &[u8],
        replacement: &[u8],
        before_rename: F,
    ) -> Result<(), String>
    where
        F: FnOnce(&Path),
    {
        validate_relative(relative)?;
        let maximum = u64::try_from(expected.len()).map_err(display_error)?;
        #[cfg(unix)]
        {
            let (parent, basename) = self.open_relative_parent(relative)?;
            let (preimage, original_identity) = read_bounded_regular_file_at_with_identity(
                &parent,
                &basename,
                maximum,
                "private replacement target",
            )?;
            if preimage != expected {
                return Err("private replacement preimage does not match".to_owned());
            }
            let sequence = NEXT_PRIVATE_ROOT.fetch_add(1, Ordering::SeqCst);
            let temporary = CString::new(format!(".npa-replace-{}-{sequence}", std::process::id()))
                .map_err(|_| "private replacement name contains NUL".to_owned())?;
            let raw = unsafe {
                libc::openat(
                    parent.as_raw_fd(),
                    temporary.as_ptr(),
                    libc::O_WRONLY
                        | libc::O_CLOEXEC
                        | libc::O_CREAT
                        | libc::O_EXCL
                        | libc::O_NOFOLLOW,
                    0o600,
                )
            };
            if raw < 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            let mut file = unsafe { fs::File::from_raw_fd(raw) };
            let opened_temporary = file_status(file.as_raw_fd())?;
            let temporary_identity = status_identity(&opened_temporary);
            let named_temporary = status_at(parent.as_raw_fd(), &temporary)?;
            if file_kind(&opened_temporary) != libc::S_IFREG
                || file_kind(&named_temporary) != libc::S_IFREG
                || temporary_identity != status_identity(&named_temporary)
                || temporary_identity.device != self.root_identity.device
                || opened_temporary.st_mode & 0o777 != 0o600
            {
                return Err("private replacement temporary has invalid identity".to_owned());
            }
            let result = (|| -> Result<(), String> {
                file.write_all(replacement).map_err(display_error)?;
                file.sync_all().map_err(display_error)?;
                let temporary_path = self
                    .path
                    .join(relative.parent().unwrap_or_else(|| Path::new("")))
                    .join(OsStr::from_bytes(temporary.as_bytes()));
                before_rename(&temporary_path);
                self.verify_attached_root()?;
                parent.verify("private replacement parent")?;
                let named_temporary = status_at(parent.as_raw_fd(), &temporary)?;
                if file_kind(&named_temporary) != libc::S_IFREG
                    || status_identity(&named_temporary) != temporary_identity
                {
                    return Err("private replacement temporary changed before rename".to_owned());
                }
                let opened_temporary_after = file_status(file.as_raw_fd())?;
                if file_kind(&opened_temporary_after) != libc::S_IFREG
                    || status_identity(&opened_temporary_after) != temporary_identity
                {
                    return Err("private replacement temporary inode changed".to_owned());
                }
                let current = status_at(parent.as_raw_fd(), &basename)?;
                if status_identity(&current) != original_identity
                    || file_kind(&current) != libc::S_IFREG
                {
                    return Err("private replacement target changed before rename".to_owned());
                }
                if unsafe {
                    libc::renameat(
                        parent.as_raw_fd(),
                        temporary.as_ptr(),
                        parent.as_raw_fd(),
                        basename.as_ptr(),
                    )
                } != 0
                {
                    return Err(display_error(std::io::Error::last_os_error()));
                }
                self.verify_attached_root()?;
                parent.verify("private replacement parent")?;
                let published = status_at(parent.as_raw_fd(), &basename)?;
                if file_kind(&published) != libc::S_IFREG
                    || status_identity(&published) != temporary_identity
                {
                    return Err("private replacement publication changed identity".to_owned());
                }
                if status_at_optional(parent.as_raw_fd(), &temporary)?.is_some() {
                    return Err("private replacement temporary remains after rename".to_owned());
                }
                sync_directory(parent.as_raw_fd())
            })();
            // Preserve a failed unique temporary for explicit quiescent
            // recovery. Inspect-then-unlink cannot conditionally delete this
            // inode if a same-uid process swaps the name after inspection.
            result
        }
        #[cfg(not(unix))]
        {
            if self.read_regular_file(relative, maximum)? != expected {
                return Err("private replacement preimage does not match".to_owned());
            }
            let path = self.path.join(relative);
            let temporary = path.with_extension(format!("npa-replace-{}", std::process::id()));
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)
                .map_err(display_error)?;
            file.write_all(replacement).map_err(display_error)?;
            file.sync_all().map_err(display_error)?;
            before_rename(&temporary);
            fs::rename(temporary, path).map_err(display_error)
        }
    }

    /// Read one same-device regular file through a retained descriptor.
    pub fn read_regular_file(
        &self,
        relative: &Path,
        maximum_bytes: u64,
    ) -> Result<Vec<u8>, String> {
        validate_relative(relative)?;
        #[cfg(unix)]
        {
            let (parent, basename) = self.open_relative_parent(relative)?;
            parent.verify("private file parent")?;
            self.verify_attached_root()?;
            let raw = unsafe {
                libc::openat(
                    parent.as_raw_fd(),
                    basename.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                )
            };
            if raw < 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            let mut file = unsafe { fs::File::from_raw_fd(raw) };
            let status = file_status(file.as_raw_fd())?;
            let named = status_at(parent.as_raw_fd(), &basename)?;
            if file_kind(&status) != libc::S_IFREG
                || file_kind(&named) != libc::S_IFREG
                || status_identity(&status) != status_identity(&named)
                || status_identity(&status).device != self.root_identity.device
                || status.st_size < 0
                || u64::try_from(status.st_size).map_err(display_error)? > maximum_bytes
            {
                return Err("private file is not a bounded same-device regular file".to_owned());
            }
            let capacity = usize::try_from(status.st_size).map_err(display_error)?;
            let mut bytes = Vec::with_capacity(capacity);
            let read_limit = maximum_bytes
                .checked_add(1)
                .ok_or("private file byte limit cannot be u64::MAX")?;
            std::io::Read::by_ref(&mut file)
                .take(read_limit)
                .read_to_end(&mut bytes)
                .map_err(display_error)?;
            if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
                return Err("private file grew beyond its byte limit while reading".to_owned());
            }
            let named_after = status_at(parent.as_raw_fd(), &basename)?;
            if file_kind(&named_after) != libc::S_IFREG
                || status_identity(&named_after) != status_identity(&status)
            {
                return Err("private file changed while it was read".to_owned());
            }
            self.verify_attached_root()?;
            parent.verify("private file parent")?;
            Ok(bytes)
        }
        #[cfg(not(unix))]
        {
            let bytes = fs::read(self.path.join(relative)).map_err(display_error)?;
            if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
                return Err("private file exceeds its byte limit".to_owned());
            }
            Ok(bytes)
        }
    }

    /// Remove one regular file only when the bytes read from the opened inode
    /// equal the caller's exact preimage. The named entry is required to still
    /// identify that same inode immediately before `unlinkat`.
    pub fn remove_exact_file(&self, relative: &Path, expected: &[u8]) -> Result<(), String> {
        validate_relative(relative)?;
        #[cfg(unix)]
        {
            let (parent, basename) = self.open_relative_parent(relative)?;
            parent.verify("exact-removal parent")?;
            let raw = unsafe {
                libc::openat(
                    parent.as_raw_fd(),
                    basename.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                )
            };
            if raw < 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            let mut file = unsafe { fs::File::from_raw_fd(raw) };
            let opened = file_status(file.as_raw_fd())?;
            if file_kind(&opened) != libc::S_IFREG
                || status_identity(&opened).device != self.root_identity.device
                || opened.st_size < 0
                || usize::try_from(opened.st_size).map_err(display_error)? != expected.len()
            {
                return Err("exact-removal target is not the expected bounded file".to_owned());
            }
            let maximum = u64::try_from(expected.len()).map_err(display_error)?;
            let mut bytes = Vec::with_capacity(expected.len());
            std::io::Read::by_ref(&mut file)
                .take(
                    maximum
                        .checked_add(1)
                        .ok_or("exact-removal byte limit overflowed")?,
                )
                .read_to_end(&mut bytes)
                .map_err(display_error)?;
            if bytes != expected {
                return Err("exact-removal preimage does not match".to_owned());
            }
            let named = status_at(parent.as_raw_fd(), &basename)?;
            if file_kind(&named) != libc::S_IFREG
                || status_identity(&named) != status_identity(&opened)
            {
                return Err("exact-removal target changed after opening".to_owned());
            }
            self.verify_attached_root()?;
            parent.verify("exact-removal parent")?;
            if unsafe { libc::unlinkat(parent.as_raw_fd(), basename.as_ptr(), 0) } != 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            sync_directory(parent.as_raw_fd())
        }
        #[cfg(not(unix))]
        {
            let path = self.path.join(relative);
            if fs::read(&path).map_err(display_error)? != expected {
                return Err("exact-removal preimage does not match".to_owned());
            }
            self.verify_attached_root()?;
            fs::remove_file(path).map_err(display_error)
        }
    }

    /// Remove exactly one closed subtree. Paths are relative to this root;
    /// `directories` must include the subtree root and every descendant.
    pub fn remove_exact_subtree(
        &self,
        subtree: &Path,
        files: &BTreeSet<PathBuf>,
        directories: &BTreeSet<PathBuf>,
    ) -> Result<(), String> {
        validate_relative(subtree)?;
        if !directories.contains(subtree) {
            return Err("closed cleanup catalog omits its subtree root".to_owned());
        }
        for relative in files.iter().chain(directories) {
            validate_relative(relative)?;
            if !relative.starts_with(subtree) {
                return Err("closed cleanup catalog escapes its subtree".to_owned());
            }
        }
        self.verify_attached_root()?;
        let (actual_files, actual_directories, identities) = self.catalog(subtree)?;
        if &actual_files != files || &actual_directories != directories {
            return Err(format!(
                "private tree differs from its closed cleanup catalog: expected files={files:?} directories={directories:?}; actual files={actual_files:?} directories={actual_directories:?}"
            ));
        }
        for relative in files {
            self.remove_catalog_entry(relative, false, &identities)?;
        }
        let mut ordered_directories = directories.iter().cloned().collect::<Vec<_>>();
        ordered_directories.sort_by(|left, right| {
            right
                .components()
                .count()
                .cmp(&left.components().count())
                .then_with(|| right.cmp(left))
        });
        for relative in ordered_directories {
            self.remove_catalog_entry(&relative, true, &identities)?;
        }
        Ok(())
    }

    /// Inventory one normalized subtree through retained descriptors. Callers
    /// validate the returned closed grammar before passing the exact same sets
    /// to `remove_exact_subtree`.
    pub fn catalog_subtree_paths(
        &self,
        subtree: &Path,
    ) -> Result<(BTreeSet<PathBuf>, BTreeSet<PathBuf>), String> {
        validate_relative(subtree)?;
        self.verify_attached_root()?;
        let (files, directories, _) = self.catalog(subtree)?;
        Ok((files, directories))
    }

    /// Inventory the complete retained root without accepting `.` as an
    /// externally supplied relative path. The returned directory set omits
    /// the root itself and therefore describes only named descendants.
    pub fn catalog_root_paths(&self) -> Result<(BTreeSet<PathBuf>, BTreeSet<PathBuf>), String> {
        self.verify_attached_root()?;
        let mut files = BTreeSet::new();
        let mut directories = BTreeSet::new();
        let mut identities = BTreeMap::new();
        #[cfg(unix)]
        self.catalog_directory_fd(
            self.root_fd.as_raw_fd(),
            Path::new(""),
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        #[cfg(not(unix))]
        self.catalog_directory_path(
            &self.path,
            Path::new(""),
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        directories.remove(Path::new(""));
        Ok((files, directories))
    }

    /// Inventory one flat sealed root with explicit resource bounds.  This is
    /// the hostile-artifact entry point: it stops at the first subdirectory or
    /// non-regular member and never recursively allocates an attacker-chosen
    /// tree before comparing it with the expected closed catalog.
    pub fn bounded_flat_regular_catalog(
        &self,
        maximum_entries: usize,
        maximum_filename_bytes: usize,
    ) -> Result<BTreeSet<PathBuf>, String> {
        if maximum_entries == 0 || maximum_filename_bytes == 0 {
            return Err("sealed catalog bounds must be positive".to_owned());
        }
        self.verify_attached_root()?;
        #[cfg(unix)]
        {
            let names = directory_entry_names_bounded(
                self.root_fd.as_raw_fd(),
                maximum_entries,
                maximum_filename_bytes,
            )?;
            let mut files = BTreeSet::new();
            for name in names {
                let basename = c_string(&name)?;
                let status = status_at(self.root_fd.as_raw_fd(), &basename)?;
                if file_kind(&status) != libc::S_IFREG {
                    return Err("sealed root contains a non-regular member".to_owned());
                }
                let relative = PathBuf::from(name);
                validate_relative(&relative)?;
                if !files.insert(relative) {
                    return Err("sealed root catalog contains a duplicate name".to_owned());
                }
            }
            self.verify_attached_root()?;
            Ok(files)
        }
        #[cfg(not(unix))]
        {
            let _ = (maximum_entries, maximum_filename_bytes);
            Err("bounded sealed catalogs require Unix".to_owned())
        }
    }

    /// Snapshot the exact flat regular-file catalog and bytes through this
    /// retained root. This is the input to a sealed multi-file commit digest;
    /// it rejects directories, symlinks, special entries, overlarge members,
    /// and catalog/identity drift during the read.
    pub fn read_exact_flat_regular_files(
        &self,
        expected_files: &BTreeSet<PathBuf>,
        maximum_file_bytes: u64,
        maximum_total_bytes: u64,
    ) -> Result<BTreeMap<PathBuf, SealedRegularFile>, String> {
        for relative in expected_files {
            validate_relative(relative)?;
            if relative.components().count() != 1 {
                return Err("sealed catalog must contain basenames only".to_owned());
            }
        }
        let filename_budget = expected_files
            .iter()
            .try_fold(0_usize, |total, path| {
                total.checked_add(path.as_os_str().len())
            })
            .ok_or("sealed catalog filename budget overflowed")?;
        let actual_files = self.bounded_flat_regular_catalog(
            expected_files
                .len()
                .checked_add(1)
                .ok_or("sealed catalog entry bound overflowed")?,
            filename_budget
                .checked_add(256)
                .ok_or("sealed catalog filename bound overflowed")?,
        )?;
        if actual_files != *expected_files {
            return Err("sealed root differs from its exact flat catalog".to_owned());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::FileExt as _;

            self.verify_attached_root()?;
            let root = file_status(self.root_fd.as_raw_fd())?;
            if file_kind(&root) != libc::S_IFDIR || root.st_mode & 0o777 != 0o700 {
                return Err("sealed root is not an owner-only directory".to_owned());
            }
            let mut total = 0_u64;
            let mut files = BTreeMap::new();
            for relative in expected_files {
                let (parent, basename) = self.open_relative_parent(relative)?;
                parent.verify("sealed member parent")?;
                let raw = unsafe {
                    libc::openat(
                        parent.as_raw_fd(),
                        basename.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                    )
                };
                if raw < 0 {
                    return Err(display_error(std::io::Error::last_os_error()));
                }
                let file = unsafe { fs::File::from_raw_fd(raw) };
                let opened = file_status(file.as_raw_fd())?;
                let named = status_at(parent.as_raw_fd(), &basename)?;
                if file_kind(&opened) != libc::S_IFREG
                    || file_kind(&named) != libc::S_IFREG
                    || status_identity(&opened) != status_identity(&named)
                    || status_identity(&opened).device != self.root_identity.device
                    || opened.st_mode & 0o777 != 0o600
                    || opened.st_nlink != 1
                    || opened.st_size < 0
                    || u64::try_from(opened.st_size).map_err(display_error)? > maximum_file_bytes
                {
                    return Err(
                        "sealed member is not a private single-link bounded file".to_owned()
                    );
                }
                total = total
                    .checked_add(u64::try_from(opened.st_size).map_err(display_error)?)
                    .ok_or("sealed catalog byte total overflowed")?;
                if total > maximum_total_bytes {
                    return Err("sealed catalog exceeds its aggregate byte limit".to_owned());
                }
                let length = usize::try_from(opened.st_size).map_err(display_error)?;
                let mut bytes = vec![0_u8; length];
                let mut offset = 0_usize;
                while offset < bytes.len() {
                    let read = file
                        .read_at(
                            &mut bytes[offset..],
                            u64::try_from(offset).map_err(display_error)?,
                        )
                        .map_err(display_error)?;
                    if read == 0 {
                        return Err("sealed member was truncated while reading".to_owned());
                    }
                    offset = offset
                        .checked_add(read)
                        .ok_or("sealed member read offset overflowed")?;
                }
                let opened_after = file_status(file.as_raw_fd())?;
                let named_after = status_at(parent.as_raw_fd(), &basename)?;
                parent.verify("sealed member parent")?;
                let mut reread = [0_u8; 64 * 1024];
                let mut offset = 0_usize;
                while offset < bytes.len() {
                    let remaining = bytes.len() - offset;
                    let chunk = remaining.min(reread.len());
                    let read = file
                        .read_at(
                            &mut reread[..chunk],
                            u64::try_from(offset).map_err(display_error)?,
                        )
                        .map_err(display_error)?;
                    if read == 0 {
                        return Err(
                            "sealed member was truncated during the final reread".to_owned()
                        );
                    }
                    offset = offset
                        .checked_add(read)
                        .ok_or("sealed member final reread offset overflowed")?;
                    if reread[..read] != bytes[offset - read..offset] {
                        return Err(
                            "sealed member bytes changed during the final reread".to_owned()
                        );
                    }
                }
                if status_identity(&opened_after) != status_identity(&opened)
                    || status_identity(&named_after) != status_identity(&opened)
                    || opened_after.st_size != opened.st_size
                    || opened_after.st_mode & 0o777 != opened.st_mode & 0o777
                    || opened_after.st_nlink != 1
                    || opened_after.st_mtime != opened.st_mtime
                    || opened_after.st_ctime != opened.st_ctime
                    || file_kind(&named_after) != libc::S_IFREG
                {
                    return Err("sealed member changed during the catalog snapshot".to_owned());
                }
                files.insert(
                    relative.clone(),
                    SealedRegularFile {
                        bytes,
                        mode: u32::from(opened.st_mode & 0o777),
                        link_count: 1,
                    },
                );
            }
            self.verify_attached_root()?;
            let after_files = self.bounded_flat_regular_catalog(
                expected_files
                    .len()
                    .checked_add(1)
                    .ok_or("sealed catalog entry bound overflowed")?,
                filename_budget
                    .checked_add(256)
                    .ok_or("sealed catalog filename bound overflowed")?,
            )?;
            if after_files != *expected_files {
                return Err("sealed root catalog changed while it was read".to_owned());
            }
            Ok(files)
        }
        #[cfg(not(unix))]
        {
            let _ = (expected_files, maximum_file_bytes, maximum_total_bytes);
            Err("sealed private-tree attestation requires Unix file mode and link-count verification"
                .to_owned())
        }
    }

    /// Verify an exact flat sealed payload against already-owned producer
    /// bytes without allocating a second full payload map. Each member is
    /// opened through the retained root, checked as mode 0600/nlink 1, read
    /// and reread on the same inode, and compared byte-for-byte with the
    /// caller's expected bytes. The root catalog is bounded and checked both
    /// before and after the sequential descriptor window.
    pub fn verify_exact_flat_regular_file_bytes(
        &self,
        expected_files: &BTreeMap<PathBuf, &[u8]>,
        maximum_file_bytes: u64,
        maximum_total_bytes: u64,
    ) -> Result<(), String> {
        let expected_names = expected_files.keys().cloned().collect::<BTreeSet<_>>();
        for (path, bytes) in expected_files {
            if u64::try_from(bytes.len()).map_err(display_error)? > maximum_file_bytes {
                return Err(format!(
                    "sealed expected member {} exceeds its byte limit",
                    path.display()
                ));
            }
        }
        let expected_total =
            expected_files
                .values()
                .try_fold(0_u64, |total, bytes| -> Result<u64, String> {
                    total
                        .checked_add(u64::try_from(bytes.len()).map_err(display_error)?)
                        .ok_or("sealed expected catalog byte total overflowed".to_owned())
                })?;
        if expected_total > maximum_total_bytes {
            return Err("sealed expected catalog exceeds its aggregate byte limit".to_owned());
        }
        let filename_budget = expected_names.iter().try_fold(0_usize, |total, path| {
            validate_relative(path)?;
            if path.components().count() != 1 {
                return Err("sealed catalog must contain basenames only".to_owned());
            }
            total
                .checked_add(path.as_os_str().len())
                .ok_or("sealed catalog filename budget overflowed".to_owned())
        })?;
        let catalog_bound = expected_names
            .len()
            .checked_add(1)
            .ok_or("sealed catalog entry bound overflowed")?;
        let name_bound = filename_budget
            .checked_add(256)
            .ok_or("sealed catalog filename bound overflowed")?;
        if self.bounded_flat_regular_catalog(catalog_bound, name_bound)? != expected_names {
            return Err("sealed root differs from its exact flat catalog".to_owned());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::FileExt as _;

            self.verify_attached_root()?;
            let root = file_status(self.root_fd.as_raw_fd())?;
            if file_kind(&root) != libc::S_IFDIR || root.st_mode & 0o777 != 0o700 {
                return Err("sealed root is not an owner-only directory".to_owned());
            }
            for (relative, expected) in expected_files {
                let (parent, basename) = self.open_relative_parent(relative)?;
                parent.verify("sealed member parent")?;
                let raw = unsafe {
                    libc::openat(
                        parent.as_raw_fd(),
                        basename.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                    )
                };
                if raw < 0 {
                    return Err(display_error(std::io::Error::last_os_error()));
                }
                let file = unsafe { fs::File::from_raw_fd(raw) };
                let opened = file_status(file.as_raw_fd())?;
                let named = status_at(parent.as_raw_fd(), &basename)?;
                if file_kind(&opened) != libc::S_IFREG
                    || file_kind(&named) != libc::S_IFREG
                    || status_identity(&opened) != status_identity(&named)
                    || status_identity(&opened).device != self.root_identity.device
                    || opened.st_mode & 0o777 != 0o600
                    || opened.st_nlink != 1
                    || opened.st_size < 0
                    || usize::try_from(opened.st_size).map_err(display_error)? != expected.len()
                {
                    return Err(
                        "sealed member is not the expected private single-link file".to_owned()
                    );
                }
                let verify_once = |file: &fs::File| -> Result<(), String> {
                    let mut bytes = [0_u8; 64 * 1024];
                    let mut offset = 0_usize;
                    while offset < expected.len() {
                        let remaining = expected.len() - offset;
                        let chunk = remaining.min(bytes.len());
                        let read = file
                            .read_at(
                                &mut bytes[..chunk],
                                u64::try_from(offset).map_err(display_error)?,
                            )
                            .map_err(display_error)?;
                        if read == 0 {
                            return Err("sealed member was truncated while verifying".to_owned());
                        }
                        offset = offset
                            .checked_add(read)
                            .ok_or("sealed member verification offset overflowed")?;
                        if bytes[..read] != expected[offset - read..offset] {
                            return Err("sealed member differs from producer bytes".to_owned());
                        }
                    }
                    Ok(())
                };
                verify_once(&file)?;
                let opened_after = file_status(file.as_raw_fd())?;
                let named_after = status_at(parent.as_raw_fd(), &basename)?;
                verify_once(&file)?;
                parent.verify("sealed member parent")?;
                if status_identity(&opened_after) != status_identity(&opened)
                    || status_identity(&named_after) != status_identity(&opened)
                    || opened_after.st_size != opened.st_size
                    || opened_after.st_mode & 0o777 != 0o600
                    || opened_after.st_nlink != 1
                    || file_kind(&named_after) != libc::S_IFREG
                {
                    return Err("sealed member changed or differs from producer bytes".to_owned());
                }
            }
            self.verify_attached_root()?;
            if self.bounded_flat_regular_catalog(catalog_bound, name_bound)? != expected_names {
                return Err("sealed root catalog changed while it was verified".to_owned());
            }
            Ok(())
        }
        #[cfg(not(unix))]
        {
            let _ = (maximum_file_bytes, maximum_total_bytes);
            Err("sealed private-tree verification requires Unix file mode and link-count verification"
                .to_owned())
        }
    }

    /// Capture the complete descriptor-relative file, directory, and inode
    /// catalog before handing the private tree to code that may create an
    /// arbitrary but subsequently immutable output population.
    pub fn capture_cleanup_catalog(&self) -> Result<ClosedCleanupCatalog, String> {
        self.verify_attached_root()?;
        let mut files = BTreeSet::new();
        let mut directories = BTreeSet::new();
        let mut identities = BTreeMap::new();
        #[cfg(unix)]
        self.catalog_directory_fd(
            self.root_fd.as_raw_fd(),
            Path::new(""),
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        #[cfg(not(unix))]
        self.catalog_directory_path(
            &self.path,
            Path::new(""),
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        self.verify_attached_root()?;
        Ok(ClosedCleanupCatalog {
            root_path: self.path.clone(),
            root_identity: self.root_identity,
            files,
            directories,
            identities,
        })
    }

    /// Remove a complete root only if its current catalog still exactly equals
    /// a previously captured catalog from this same root. Unknown entries or
    /// replaced identities are rejected before the first unlink.
    pub fn remove_captured_root(&self, catalog: &ClosedCleanupCatalog) -> Result<(), String> {
        self.verify_attached_root()?;
        if catalog.root_path != self.path || catalog.root_identity != self.root_identity {
            return Err("cleanup catalog belongs to a different private root".to_owned());
        }
        let current = self.capture_cleanup_catalog()?;
        if current.files != catalog.files
            || current.directories != catalog.directories
            || current.identities != catalog.identities
        {
            return Err("private root changed after its cleanup catalog was captured".to_owned());
        }
        for relative in &catalog.files {
            self.remove_catalog_entry(relative, false, &catalog.identities)?;
        }
        let mut directories = catalog
            .directories
            .iter()
            .filter(|relative| !relative.as_os_str().is_empty())
            .cloned()
            .collect::<Vec<_>>();
        directories.sort_by(|left, right| {
            right
                .components()
                .count()
                .cmp(&left.components().count())
                .then_with(|| right.cmp(left))
        });
        for relative in directories {
            self.remove_catalog_entry(&relative, true, &catalog.identities)?;
        }
        self.remove_empty_root()
    }

    /// Close and remove the complete current regular-file-only tree.
    ///
    /// The full descriptor-relative catalog and every entry identity are
    /// collected before the first mutation. Each later unlink/rmdir reopens
    /// its parent from the retained root and rechecks the cataloged identities,
    /// so a renamed-out subtree is never traversed or modified.
    pub fn remove_cataloged_root(&self) -> Result<(), String> {
        self.verify_attached_root()?;
        let mut files = BTreeSet::new();
        let mut directories = BTreeSet::new();
        let mut identities = BTreeMap::new();
        #[cfg(unix)]
        self.catalog_directory_fd(
            self.root_fd.as_raw_fd(),
            Path::new(""),
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        #[cfg(not(unix))]
        self.catalog_directory_path(
            &self.path,
            Path::new(""),
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        for relative in &files {
            self.remove_catalog_entry(relative, false, &identities)?;
        }
        directories.remove(Path::new(""));
        let mut ordered_directories = directories.into_iter().collect::<Vec<_>>();
        ordered_directories.sort_by(|left, right| {
            right
                .components()
                .count()
                .cmp(&left.components().count())
                .then_with(|| right.cmp(left))
        });
        for relative in ordered_directories {
            self.remove_catalog_entry(&relative, true, &identities)?;
        }
        self.remove_empty_root()
    }

    /// Remove a root containing exactly the supplied regular-file catalog and
    /// no subdirectories. This is the controller-output fast path.
    pub fn remove_exact_root(&self, files: &BTreeSet<PathBuf>) -> Result<(), String> {
        self.remove_exact_contents(files)?;
        self.remove_empty_root()
    }

    /// Remove exactly the supplied flat regular-file catalog while retaining
    /// the empty root. This is for a controller whose parent shell owns the
    /// root directory and verifies/removes that directory by its own retained
    /// identity.
    pub fn remove_exact_contents(&self, files: &BTreeSet<PathBuf>) -> Result<(), String> {
        for relative in files {
            validate_relative(relative)?;
            if relative.components().count() != 1 {
                return Err("root cleanup file catalog must contain basenames only".to_owned());
            }
        }
        self.verify_attached_root()?;
        let mut actual_files = BTreeSet::new();
        let mut actual_directories = BTreeSet::new();
        let mut identities = BTreeMap::new();
        #[cfg(unix)]
        self.catalog_directory_fd(
            self.root_fd.as_raw_fd(),
            Path::new(""),
            &mut actual_files,
            &mut actual_directories,
            &mut identities,
        )?;
        #[cfg(not(unix))]
        self.catalog_directory_path(
            &self.path,
            Path::new(""),
            &mut actual_files,
            &mut actual_directories,
            &mut identities,
        )?;
        if &actual_files != files || actual_directories != BTreeSet::from([PathBuf::new()]) {
            return Err(format!(
                "private root differs from its closed cleanup catalog: expected files={files:?}; actual files={actual_files:?} directories={actual_directories:?}"
            ));
        }
        for relative in files {
            self.remove_catalog_entry(relative, false, &identities)?;
        }
        Ok(())
    }

    /// Error-path cleanup for a controller whose complete possible basename
    /// catalog is known, but which may stop before creating every file.
    pub fn remove_allowed_root(&self, allowed_files: &BTreeSet<PathBuf>) -> Result<(), String> {
        self.remove_allowed_contents(allowed_files)?;
        self.remove_empty_root()
    }

    /// Remove the currently-created subset of an allowed flat file catalog,
    /// retaining the empty root for a parent shell to remove by identity.
    pub fn remove_allowed_contents(&self, allowed_files: &BTreeSet<PathBuf>) -> Result<(), String> {
        for relative in allowed_files {
            validate_relative(relative)?;
            if relative.components().count() != 1 {
                return Err("allowed root cleanup catalog must contain basenames only".to_owned());
            }
        }
        self.verify_attached_root()?;
        let mut actual_files = BTreeSet::new();
        let mut actual_directories = BTreeSet::new();
        let mut identities = BTreeMap::new();
        #[cfg(unix)]
        self.catalog_directory_fd(
            self.root_fd.as_raw_fd(),
            Path::new(""),
            &mut actual_files,
            &mut actual_directories,
            &mut identities,
        )?;
        #[cfg(not(unix))]
        self.catalog_directory_path(
            &self.path,
            Path::new(""),
            &mut actual_files,
            &mut actual_directories,
            &mut identities,
        )?;
        if !actual_files.is_subset(allowed_files)
            || actual_directories != BTreeSet::from([PathBuf::new()])
        {
            return Err(format!(
                "private root contains entries outside its closed allowed catalog: allowed={allowed_files:?}; actual files={actual_files:?} directories={actual_directories:?}"
            ));
        }
        for relative in &actual_files {
            self.remove_catalog_entry(relative, false, &identities)?;
        }
        Ok(())
    }

    /// Publish this private root to a new absolute destination without ever
    /// replacing or nesting under an entry that appeared concurrently.
    /// Both the source and destination ancestor chains remain descriptor-
    /// retained across the no-replace rename and both directories are synced.
    pub fn publish_new_root(&self, destination: &Path, label: &str) -> Result<(), String> {
        self.verify_attached_root()?;
        #[cfg(unix)]
        {
            let (destination_parent, destination_name) = open_absolute_parent(destination, label)?;
            destination_parent.verify(label)?;
            match status_at_optional(destination_parent.as_raw_fd(), &destination_name)? {
                None => {}
                Some(_) => return Err(format!("{label} already exists")),
            }
            if self.parent_identity.device
                != status_identity(&file_status(destination_parent.as_raw_fd())?).device
            {
                return Err(format!("{label} must be on the private root filesystem"));
            }
            self.verify_attached_root()?;
            destination_parent.verify(label)?;
            rename_directory_no_replace(
                self.parent_fd.as_raw_fd(),
                &self.root_name,
                destination_parent.as_raw_fd(),
                &destination_name,
                label,
            )?;
            destination_parent.verify(label)?;
            let published = status_at(destination_parent.as_raw_fd(), &destination_name)?;
            if file_kind(&published) != libc::S_IFDIR
                || status_identity(&published) != self.root_identity
            {
                return Err(format!("published {label} identity is invalid"));
            }
            match status_at_optional(self.parent_fd.as_raw_fd(), &self.root_name)? {
                None => {}
                Some(_) => return Err(format!("published {label} source name still exists")),
            }
            sync_directory(self.parent_fd.as_raw_fd())?;
            sync_directory(destination_parent.as_raw_fd())?;
            Ok(())
        }
        #[cfg(not(unix))]
        {
            let _ = destination;
            Err(format!(
                "{label} no-replace directory publication is unsupported on this platform"
            ))
        }
    }

    pub fn remove_empty_root(&self) -> Result<(), String> {
        self.verify_attached_root()?;
        #[cfg(unix)]
        {
            if !directory_entry_names(self.root_fd.as_raw_fd())?.is_empty() {
                return Err("private directory is not empty".to_owned());
            }
            self.verify_attached_root()?;
            if unsafe {
                libc::unlinkat(
                    self.parent_fd.as_raw_fd(),
                    self.root_name.as_ptr(),
                    libc::AT_REMOVEDIR,
                )
            } != 0
            {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            Ok(())
        }
        #[cfg(not(unix))]
        {
            fs::remove_dir(&self.path).map_err(display_error)
        }
    }

    fn catalog(&self, subtree: &Path) -> Result<ClosedTreeCatalog, String> {
        let mut files = BTreeSet::new();
        let mut directories = BTreeSet::new();
        let mut identities = BTreeMap::new();
        #[cfg(unix)]
        {
            self.verify_attached_root()?;
            let mut directory = RetainedDirectoryPath::from_anchor(
                duplicate_fd(self.root_fd.as_raw_fd())?,
                "private cleanup subtree",
            )?;
            let components = subtree.components().collect::<Vec<_>>();
            for (index, component) in components.iter().enumerate() {
                let Component::Normal(component) = component else {
                    return Err("private cleanup subtree is not normalized".to_owned());
                };
                directory =
                    directory.open_child(c_string(component)?, "private cleanup subtree")?;
                if index + 1 < components.len() {
                    let ancestor = components[..=index]
                        .iter()
                        .map(|component| component.as_os_str())
                        .collect::<PathBuf>();
                    identities.insert(
                        ancestor,
                        status_identity(&file_status(directory.as_raw_fd())?),
                    );
                }
            }
            directory.verify("private cleanup subtree")?;
            self.catalog_directory_fd(
                directory.as_raw_fd(),
                subtree,
                &mut files,
                &mut directories,
                &mut identities,
            )?;
            directory.verify("private cleanup subtree")?;
            self.verify_attached_root()?;
        }
        #[cfg(not(unix))]
        self.catalog_directory_path(
            &self.path.join(subtree),
            subtree,
            &mut files,
            &mut directories,
            &mut identities,
        )?;
        Ok((files, directories, identities))
    }

    #[cfg(unix)]
    fn catalog_directory_fd(
        &self,
        descriptor: RawFd,
        relative: &Path,
        files: &mut BTreeSet<PathBuf>,
        directories: &mut BTreeSet<PathBuf>,
        identities: &mut BTreeMap<PathBuf, EntryIdentity>,
    ) -> Result<(), String> {
        let status = file_status(descriptor)?;
        let identity = status_identity(&status);
        if file_kind(&status) != libc::S_IFDIR || identity.device != self.root_identity.device {
            return Err(
                "closed cleanup encountered a non-directory or cross-device entry".to_owned(),
            );
        }
        directories.insert(relative.to_path_buf());
        identities.insert(relative.to_path_buf(), identity);
        let names = directory_entry_names(descriptor)?;
        for name in &names {
            let child_relative = relative.join(name);
            validate_relative(&child_relative)?;
            let name = c_string(name)?;
            let child_status = status_at(descriptor, &name)?;
            let child_identity = status_identity(&child_status);
            if child_identity.device != self.root_identity.device
                || file_kind(&child_status) == libc::S_IFLNK
            {
                return Err("closed cleanup encountered a symlink or cross-device entry".to_owned());
            }
            match file_kind(&child_status) {
                libc::S_IFDIR => {
                    let child = open_directory_at(descriptor, &name)?;
                    let child_identity = status_identity(&file_status(child.as_raw_fd())?);
                    if child_identity != status_identity(&child_status) {
                        return Err(
                            "closed cleanup directory changed while it was opened".to_owned()
                        );
                    }
                    self.catalog_directory_fd(
                        child.as_raw_fd(),
                        &child_relative,
                        files,
                        directories,
                        identities,
                    )?;
                    let named_after = status_at(descriptor, &name)?;
                    if file_kind(&named_after) != libc::S_IFDIR
                        || status_identity(&named_after) != child_identity
                    {
                        return Err("closed cleanup directory changed during cataloging".to_owned());
                    }
                }
                libc::S_IFREG => {
                    files.insert(child_relative.clone());
                    identities.insert(child_relative, child_identity);
                }
                _ => return Err("closed cleanup encountered a special file".to_owned()),
            }
        }
        if directory_entry_names(descriptor)? != names {
            return Err("closed cleanup directory catalog changed during traversal".to_owned());
        }
        Ok(())
    }

    #[cfg(not(unix))]
    fn catalog_directory_path(
        &self,
        absolute: &Path,
        relative: &Path,
        files: &mut BTreeSet<PathBuf>,
        directories: &mut BTreeSet<PathBuf>,
        identities: &mut BTreeMap<PathBuf, EntryIdentity>,
    ) -> Result<(), String> {
        let metadata = fs::symlink_metadata(absolute).map_err(display_error)?;
        directories.insert(relative.to_path_buf());
        identities.insert(relative.to_path_buf(), metadata_identity(&metadata));
        for entry in fs::read_dir(absolute).map_err(display_error)? {
            let entry = entry.map_err(display_error)?;
            let child_relative = relative.join(entry.file_name());
            let child_metadata = fs::symlink_metadata(entry.path()).map_err(display_error)?;
            if child_metadata.file_type().is_dir() {
                self.catalog_directory_path(
                    &entry.path(),
                    &child_relative,
                    files,
                    directories,
                    identities,
                )?;
            } else if child_metadata.file_type().is_file() {
                files.insert(child_relative.clone());
                identities.insert(child_relative, metadata_identity(&child_metadata));
            } else {
                return Err("closed cleanup encountered a non-regular entry".to_owned());
            }
        }
        Ok(())
    }

    fn remove_catalog_entry(
        &self,
        relative: &Path,
        directory: bool,
        identities: &BTreeMap<PathBuf, EntryIdentity>,
    ) -> Result<(), String> {
        self.verify_attached_root()?;
        let expected = identities
            .get(relative)
            .ok_or_else(|| "closed cleanup lost an entry identity".to_owned())?;
        #[cfg(unix)]
        {
            let (parent, basename) = self.open_relative_parent(relative)?;
            let parent_relative = relative.parent().unwrap_or_else(|| Path::new(""));
            let actual_parent = status_identity(&file_status(parent.as_raw_fd())?);
            let expected_parent = if parent_relative.as_os_str().is_empty() {
                self.root_identity
            } else {
                *identities
                    .get(parent_relative)
                    .ok_or("closed cleanup lost parent identity")?
            };
            if actual_parent != expected_parent {
                return Err("private-tree parent changed before cleanup".to_owned());
            }
            let status = status_at(parent.as_raw_fd(), &basename)?;
            let actual = status_identity(&status);
            if &actual != expected
                || actual.device != self.root_identity.device
                || (directory && file_kind(&status) != libc::S_IFDIR)
                || (!directory && file_kind(&status) != libc::S_IFREG)
            {
                return Err("private-tree entry changed before cleanup".to_owned());
            }
            self.verify_attached_root()?;
            let flags = if directory { libc::AT_REMOVEDIR } else { 0 };
            if unsafe { libc::unlinkat(parent.as_raw_fd(), basename.as_ptr(), flags) } != 0 {
                return Err(display_error(std::io::Error::last_os_error()));
            }
            parent.verify("private-tree cleanup parent")?;
            self.verify_attached_root()?;
            sync_directory(parent.as_raw_fd())
        }
        #[cfg(not(unix))]
        {
            let absolute = self.path.join(relative);
            let metadata = fs::symlink_metadata(&absolute).map_err(display_error)?;
            if metadata_identity(&metadata) != *expected {
                return Err("private-tree entry changed before cleanup".to_owned());
            }
            self.verify_attached_root()?;
            if directory {
                fs::remove_dir(absolute).map_err(display_error)
            } else {
                fs::remove_file(absolute).map_err(display_error)
            }
        }
    }

    fn verify_attached_root(&self) -> Result<(), String> {
        let safe_name = self
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with(&self.name_prefix));
        if !safe_name || self.path.parent() != Some(self.parent.as_path()) {
            return Err("private-directory path/name changed".to_owned());
        }
        #[cfg(unix)]
        {
            self.parent_fd.verify("private-directory parent")?;
            let parent = file_status(self.parent_fd.as_raw_fd())?;
            let root = file_status(self.root_fd.as_raw_fd())?;
            let named = status_at(self.parent_fd.as_raw_fd(), &self.root_name)?;
            if file_kind(&parent) != libc::S_IFDIR
                || file_kind(&root) != libc::S_IFDIR
                || file_kind(&named) != libc::S_IFDIR
                || status_identity(&parent) != self.parent_identity
                || status_identity(&root) != self.root_identity
                || status_identity(&named) != self.root_identity
                || self.root_identity.device != self.parent_identity.device
            {
                return Err("private-directory root or parent identity changed".to_owned());
            }
            self.parent_fd.verify("private-directory parent")
        }
        #[cfg(not(unix))]
        {
            let parent = fs::symlink_metadata(&self.parent).map_err(display_error)?;
            let root = fs::symlink_metadata(&self.path).map_err(display_error)?;
            if metadata_identity(&parent) != self.parent_identity
                || metadata_identity(&root) != self.root_identity
                || !root.file_type().is_dir()
                || root.file_type().is_symlink()
            {
                return Err("private-directory root or parent identity changed".to_owned());
            }
            Ok(())
        }
    }

    #[cfg(unix)]
    fn open_relative_directory(&self, relative: &Path) -> Result<RetainedDirectoryPath, String> {
        validate_relative(relative)?;
        self.verify_attached_root()?;
        let duplicate = RetainedDirectoryPath::from_anchor(
            duplicate_fd(self.root_fd.as_raw_fd())?,
            "private relative path",
        )?;
        relative
            .components()
            .try_fold(duplicate, |parent, component| {
                let Component::Normal(component) = component else {
                    return Err("private path component is not normalized".to_owned());
                };
                parent.open_child(c_string(component)?, "private relative path")
            })
    }

    #[cfg(unix)]
    fn open_relative_parent(
        &self,
        relative: &Path,
    ) -> Result<(RetainedDirectoryPath, CString), String> {
        validate_relative(relative)?;
        let basename = relative.file_name().ok_or("private path has no basename")?;
        let parent = relative.parent().unwrap_or_else(|| Path::new(""));
        let descriptor = if parent.as_os_str().is_empty() {
            RetainedDirectoryPath::from_anchor(
                duplicate_fd(self.root_fd.as_raw_fd())?,
                "private relative path",
            )?
        } else {
            self.open_relative_directory(parent)?
        };
        Ok((descriptor, c_string(basename)?))
    }
}

impl Drop for ClosedPrivateDirectory {
    fn drop(&mut self) {
        // Drop never traverses an unexpected tree. Successful callers remove
        // their exact catalog; suspicious or replaced trees remain for review.
        if self.remove_empty_on_drop {
            let _ = self.remove_empty_root();
        }
    }
}

fn validate_relative(path: &Path) -> Result<(), String> {
    if path.as_os_str().is_empty()
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err("closed cleanup path is not a normalized relative path".to_owned());
    }
    Ok(())
}

fn validate_absolute_path(path: &Path, label: &str) -> Result<(), String> {
    if !path.is_absolute()
        || path.file_name().is_none()
        || path
            .components()
            .any(|component| !matches!(component, Component::RootDir | Component::Normal(_)))
    {
        return Err(format!(
            "{label} must be an absolute normalized path with a basename"
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn open_absolute_parent(
    path: &Path,
    label: &str,
) -> Result<(RetainedDirectoryPath, CString), String> {
    validate_absolute_path(path, label)?;
    let basename = path
        .file_name()
        .ok_or_else(|| format!("{label} has no basename"))?;
    let parent = path
        .parent()
        .ok_or_else(|| format!("{label} has no parent"))?;
    let descriptor = open_absolute_directory(parent)?;
    Ok((descriptor, c_string(basename)?))
}

#[cfg(unix)]
fn open_invocation_parent(
    path: &Path,
    label: &str,
) -> Result<(RetainedDirectoryPath, CString), String> {
    if path.as_os_str().is_empty() || path.file_name().is_none() {
        return Err(format!("{label} path has no basename"));
    }
    let root = if path.is_absolute() {
        let root = CString::new("/").map_err(|_| "root path contains NUL".to_owned())?;
        owned_fd(
            unsafe {
                libc::open(
                    root.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            },
            "open filesystem root",
        )?
    } else {
        let current = CString::new(".").map_err(|_| "cwd path contains NUL".to_owned())?;
        owned_fd(
            unsafe {
                libc::open(
                    current.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            },
            "open invocation cwd",
        )?
    };
    let mut parent = RetainedDirectoryPath::from_anchor(root, label)?;
    let components = path.components().collect::<Vec<_>>();
    let (last, parents) = components
        .split_last()
        .ok_or_else(|| format!("{label} path is empty"))?;
    for component in parents {
        match component {
            Component::RootDir | Component::CurDir => {}
            Component::Normal(component) => {
                parent = parent.open_child(c_string(component)?, label)?;
            }
            Component::ParentDir | Component::Prefix(_) => {
                return Err(format!("{label} path is not normalized"));
            }
        }
    }
    let Component::Normal(basename) = last else {
        return Err(format!("{label} path has no normalized basename"));
    };
    parent.verify(label)?;
    Ok((parent, c_string(basename)?))
}

#[cfg(unix)]
fn status_at_optional(parent: RawFd, name: &CString) -> Result<Option<libc::stat>, String> {
    let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe {
        libc::fstatat(
            parent,
            name.as_ptr(),
            status.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } == 0
    {
        return Ok(Some(unsafe { status.assume_init() }));
    }
    let error = std::io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::ENOENT) {
        Ok(None)
    } else {
        Err(display_error(error))
    }
}

#[cfg(target_vendor = "apple")]
fn rename_directory_no_replace(
    source_parent: RawFd,
    source_name: &CString,
    destination_parent: RawFd,
    destination_name: &CString,
    label: &str,
) -> Result<(), String> {
    if unsafe {
        libc::renameatx_np(
            source_parent,
            source_name.as_ptr(),
            destination_parent,
            destination_name.as_ptr(),
            libc::RENAME_EXCL,
        )
    } != 0
    {
        return Err(format!(
            "publish {label} without replacement: {}",
            std::io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn rename_directory_no_replace(
    source_parent: RawFd,
    source_name: &CString,
    destination_parent: RawFd,
    destination_name: &CString,
    label: &str,
) -> Result<(), String> {
    if unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            source_parent,
            source_name.as_ptr(),
            destination_parent,
            destination_name.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    } != 0
    {
        return Err(format!(
            "publish {label} without replacement: {}",
            std::io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(all(unix, not(any(target_vendor = "apple", target_os = "linux"))))]
fn rename_directory_no_replace(
    _source_parent: RawFd,
    _source_name: &CString,
    _destination_parent: RawFd,
    _destination_name: &CString,
    label: &str,
) -> Result<(), String> {
    Err(format!(
        "{label} no-replace directory publication is unsupported on this Unix platform"
    ))
}

#[cfg(unix)]
fn read_bounded_regular_file_at(
    parent: &RetainedDirectoryPath,
    basename: &CString,
    maximum_bytes: u64,
    label: &str,
) -> Result<Vec<u8>, String> {
    read_bounded_regular_file_at_with_identity(parent, basename, maximum_bytes, label)
        .map(|(bytes, _)| bytes)
}

#[cfg(unix)]
fn read_bounded_regular_file_at_with_identity(
    parent: &RetainedDirectoryPath,
    basename: &CString,
    maximum_bytes: u64,
    label: &str,
) -> Result<(Vec<u8>, EntryIdentity), String> {
    parent.verify(label)?;
    let raw = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            basename.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
        )
    };
    let mut file = fs::File::from(owned_fd(raw, &format!("open {label}"))?);
    let opened = file_status(file.as_raw_fd())?;
    let named = status_at(parent.as_raw_fd(), basename)?;
    if file_kind(&opened) != libc::S_IFREG
        || file_kind(&named) != libc::S_IFREG
        || status_identity(&opened) != status_identity(&named)
        || opened.st_dev != parent.device
        || opened.st_size < 0
        || u64::try_from(opened.st_size).map_err(display_error)? > maximum_bytes
    {
        return Err(format!(
            "{label} is not one bounded same-device regular file"
        ));
    }
    let mut bytes = Vec::with_capacity(usize::try_from(opened.st_size).map_err(display_error)?);
    let read_limit = maximum_bytes
        .checked_add(1)
        .ok_or_else(|| format!("{label} byte limit cannot be u64::MAX"))?;
    std::io::Read::by_ref(&mut file)
        .take(read_limit)
        .read_to_end(&mut bytes)
        .map_err(display_error)?;
    if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
        return Err(format!("{label} grew beyond its byte limit"));
    }
    let named_after = status_at(parent.as_raw_fd(), basename)?;
    if file_kind(&named_after) != libc::S_IFREG
        || status_identity(&named_after) != status_identity(&opened)
    {
        return Err(format!("{label} changed while it was read"));
    }
    parent.verify(label)?;
    Ok((bytes, status_identity(&opened)))
}

#[cfg(unix)]
fn open_absolute_directory(path: &Path) -> Result<RetainedDirectoryPath, String> {
    if !path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::RootDir | Component::Normal(_)))
    {
        return Err("directory path must be absolute and normalized".to_owned());
    }
    let root = CString::new("/").map_err(|_| "root path contains NUL".to_owned())?;
    let raw = unsafe {
        libc::open(
            root.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
        )
    };
    let initial = owned_fd(raw, "open filesystem root")?;
    path.components().try_fold(
        RetainedDirectoryPath::from_anchor(initial, "absolute directory")?,
        |parent, component| match component {
            Component::RootDir => Ok(parent),
            Component::Normal(component) => {
                parent.open_child(c_string(component)?, "absolute directory")
            }
            _ => Err("directory path must be absolute and normalized".to_owned()),
        },
    )
}

#[cfg(unix)]
fn open_directory_at(parent: RawFd, name: &CString) -> Result<OwnedFd, String> {
    let raw = unsafe {
        libc::openat(
            parent,
            name.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
        )
    };
    owned_fd(raw, "open private subdirectory")
}

#[allow(clippy::too_many_arguments)]
#[cfg(unix)]
fn read_regular_tree_directory_fd(
    descriptor: RawFd,
    root_device: libc::dev_t,
    relative: &Path,
    maximum_entries: usize,
    maximum_file_bytes: u64,
    maximum_total_bytes: u64,
    total_bytes: &mut u64,
    tree: &mut AbsoluteRegularTree,
    label: &str,
) -> Result<(), String> {
    let directory_status = file_status(descriptor)?;
    if file_kind(&directory_status) != libc::S_IFDIR || directory_status.st_dev != root_device {
        return Err(format!(
            "{label} contains a cross-device or non-directory entry"
        ));
    }
    tree.directories.insert(relative.to_owned());
    if tree.directories.len() + tree.files.len() > maximum_entries {
        return Err(format!("{label} exceeds its entry limit"));
    }
    let names = directory_entry_names(descriptor)?;
    for name in &names {
        let child_relative = relative.join(name);
        validate_relative(&child_relative)?;
        let name = c_string(name)?;
        let named = status_at(descriptor, &name)?;
        if named.st_dev != root_device || file_kind(&named) == libc::S_IFLNK {
            return Err(format!("{label} contains a symlink or cross-device entry"));
        }
        match file_kind(&named) {
            libc::S_IFDIR => {
                let child = open_directory_at(descriptor, &name)?;
                let opened = file_status(child.as_raw_fd())?;
                if status_identity(&opened) != status_identity(&named) {
                    return Err(format!("{label} directory changed while it was opened"));
                }
                read_regular_tree_directory_fd(
                    child.as_raw_fd(),
                    root_device,
                    &child_relative,
                    maximum_entries,
                    maximum_file_bytes,
                    maximum_total_bytes,
                    total_bytes,
                    tree,
                    label,
                )?;
                let named_after = status_at(descriptor, &name)?;
                if file_kind(&named_after) != libc::S_IFDIR
                    || status_identity(&named_after) != status_identity(&opened)
                {
                    return Err(format!("{label} directory changed during traversal"));
                }
            }
            libc::S_IFREG => {
                if named.st_size < 0
                    || u64::try_from(named.st_size).map_err(display_error)? > maximum_file_bytes
                {
                    return Err(format!("{label} file exceeds its byte limit"));
                }
                let raw = unsafe {
                    libc::openat(
                        descriptor,
                        name.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                    )
                };
                let mut file = fs::File::from(owned_fd(raw, &format!("open {label} file"))?);
                let opened = file_status(file.as_raw_fd())?;
                if file_kind(&opened) != libc::S_IFREG
                    || opened.st_dev != root_device
                    || status_identity(&opened) != status_identity(&named)
                {
                    return Err(format!("{label} file changed while it was opened"));
                }
                let mut bytes =
                    Vec::with_capacity(usize::try_from(opened.st_size).map_err(display_error)?);
                let read_limit = maximum_file_bytes
                    .checked_add(1)
                    .ok_or_else(|| format!("{label} file byte limit cannot be u64::MAX"))?;
                std::io::Read::by_ref(&mut file)
                    .take(read_limit)
                    .read_to_end(&mut bytes)
                    .map_err(display_error)?;
                if u64::try_from(bytes.len()).map_err(display_error)? > maximum_file_bytes {
                    return Err(format!("{label} file grew beyond its byte limit"));
                }
                let named_after = status_at(descriptor, &name)?;
                if status_identity(&named_after) != status_identity(&opened)
                    || file_kind(&named_after) != libc::S_IFREG
                {
                    return Err(format!("{label} file changed while it was read"));
                }
                *total_bytes = total_bytes
                    .checked_add(u64::try_from(bytes.len()).map_err(display_error)?)
                    .ok_or_else(|| format!("{label} aggregate byte count overflowed"))?;
                if *total_bytes > maximum_total_bytes {
                    return Err(format!("{label} exceeds its aggregate byte limit"));
                }
                if tree.files.insert(child_relative, bytes).is_some() {
                    return Err(format!("{label} contains duplicate normalized paths"));
                }
                if tree.directories.len() + tree.files.len() > maximum_entries {
                    return Err(format!("{label} exceeds its entry limit"));
                }
            }
            _ => return Err(format!("{label} contains a special file")),
        }
    }
    if directory_entry_names(descriptor)? != names {
        return Err(format!(
            "{label} directory catalog changed during traversal"
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn duplicate_fd(descriptor: RawFd) -> Result<OwnedFd, String> {
    owned_fd(
        unsafe { libc::fcntl(descriptor, libc::F_DUPFD_CLOEXEC, 0) },
        "duplicate directory descriptor",
    )
}

#[cfg(unix)]
fn owned_fd(raw: RawFd, operation: &str) -> Result<OwnedFd, String> {
    if raw < 0 {
        Err(format!("{operation}: {}", std::io::Error::last_os_error()))
    } else {
        Ok(unsafe { OwnedFd::from_raw_fd(raw) })
    }
}

#[cfg(unix)]
fn file_status(descriptor: RawFd) -> Result<libc::stat, String> {
    let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe { libc::fstat(descriptor, status.as_mut_ptr()) } != 0 {
        return Err(display_error(std::io::Error::last_os_error()));
    }
    Ok(unsafe { status.assume_init() })
}

#[cfg(unix)]
fn status_at(parent: RawFd, name: &CString) -> Result<libc::stat, String> {
    let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe {
        libc::fstatat(
            parent,
            name.as_ptr(),
            status.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(display_error(std::io::Error::last_os_error()));
    }
    Ok(unsafe { status.assume_init() })
}

#[cfg(unix)]
fn file_kind(status: &libc::stat) -> libc::mode_t {
    status.st_mode & libc::S_IFMT
}

#[cfg(unix)]
fn sync_directory(descriptor: RawFd) -> Result<(), String> {
    if unsafe { libc::fsync(descriptor) } != 0 {
        return Err(display_error(std::io::Error::last_os_error()));
    }
    Ok(())
}

#[cfg(unix)]
fn c_string(value: &OsStr) -> Result<CString, String> {
    CString::new(value.as_bytes()).map_err(|_| "private path contains NUL".to_owned())
}

#[cfg(unix)]
fn directory_entry_names(descriptor: RawFd) -> Result<Vec<OsString>, String> {
    directory_entry_names_bounded(descriptor, usize::MAX, usize::MAX)
}

#[cfg(unix)]
fn directory_entry_names_bounded(
    descriptor: RawFd,
    maximum_entries: usize,
    maximum_name_bytes: usize,
) -> Result<Vec<OsString>, String> {
    // `dup` would share the directory-stream offset with the retained
    // descriptor. Open `.` relative to it so every catalog pass gets an
    // independent open-file description starting at offset zero.
    let dot = CString::new(".").map_err(|_| "dot path contains NUL".to_owned())?;
    let reopened = unsafe {
        libc::openat(
            descriptor,
            dot.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
        )
    };
    if reopened < 0 {
        return Err(display_error(std::io::Error::last_os_error()));
    }
    let stream = unsafe { libc::fdopendir(reopened) };
    if stream.is_null() {
        unsafe { libc::close(reopened) };
        return Err(display_error(std::io::Error::last_os_error()));
    }
    let result = (|| {
        let mut names = Vec::new();
        let mut name_bytes = 0_usize;
        loop {
            #[cfg(test)]
            let inject_error = TEST_READDIR_ERROR_AFTER_ENTRIES
                .with(|limit| limit.get().is_some_and(|limit| names.len() >= limit));
            #[cfg(not(test))]
            let inject_error = false;
            if inject_error {
                return Err("injected directory enumeration error".to_owned());
            }
            set_thread_errno(0);
            let entry = unsafe { libc::readdir(stream) };
            if entry.is_null() {
                let error = thread_errno();
                if error != 0 {
                    return Err(format!(
                        "read directory catalog: {}",
                        std::io::Error::from_raw_os_error(error)
                    ));
                }
                break;
            }
            let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
            if name != b"." && name != b".." {
                if names.len() >= maximum_entries {
                    return Err("directory catalog exceeds its entry bound".to_owned());
                }
                name_bytes = name_bytes
                    .checked_add(name.len())
                    .ok_or("directory catalog filename bytes overflowed")?;
                if name_bytes > maximum_name_bytes {
                    return Err("directory catalog exceeds its filename-byte bound".to_owned());
                }
                names.push(OsString::from_vec(name.to_vec()));
            }
        }
        names.sort();
        Ok(names)
    })();
    let close_result = unsafe { libc::closedir(stream) };
    match result {
        // Preserve the primary enumeration/bound error even if closing the
        // stream also fails.
        Err(error) => Err(error),
        Ok(_names) if close_result != 0 => Err(display_error(std::io::Error::last_os_error())),
        Ok(names) => Ok(names),
    }
}

#[cfg(target_os = "linux")]
fn set_thread_errno(value: libc::c_int) {
    unsafe { *libc::__errno_location() = value };
}

#[cfg(target_os = "linux")]
fn thread_errno() -> libc::c_int {
    unsafe { *libc::__errno_location() }
}

#[cfg(target_os = "android")]
fn set_thread_errno(value: libc::c_int) {
    unsafe { *libc::__errno() = value };
}

#[cfg(target_os = "android")]
fn thread_errno() -> libc::c_int {
    unsafe { *libc::__errno() }
}

#[cfg(target_vendor = "apple")]
fn set_thread_errno(value: libc::c_int) {
    unsafe { *libc::__error() = value };
}

#[cfg(target_vendor = "apple")]
fn thread_errno() -> libc::c_int {
    unsafe { *libc::__error() }
}

#[cfg(all(
    unix,
    not(any(target_os = "linux", target_os = "android", target_vendor = "apple"))
))]
fn set_thread_errno(_value: libc::c_int) {}

#[cfg(all(
    unix,
    not(any(target_os = "linux", target_os = "android", target_vendor = "apple"))
))]
fn thread_errno() -> libc::c_int {
    libc::ENOTSUP
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

#[cfg(unix)]
fn hash_open_file_fixed_chunks(
    file: &fs::File,
    length: usize,
    label: &str,
) -> Result<String, String> {
    use std::os::unix::fs::FileExt as _;

    const CHUNK_BYTES: usize = 16 * 1024;
    let mut buffer = [0_u8; CHUNK_BYTES];
    let mut hasher = Sha256::new();
    let mut offset = 0_usize;
    while offset < length {
        let remaining = length
            .checked_sub(offset)
            .ok_or_else(|| format!("{label} read length underflowed"))?;
        let requested = remaining.min(buffer.len());
        let read = file
            .read_at(
                &mut buffer[..requested],
                u64::try_from(offset).map_err(display_error)?,
            )
            .map_err(display_error)?;
        if read == 0 {
            return Err(format!("{label} was truncated while verifying"));
        }
        hasher.update(&buffer[..read]);
        offset = offset
            .checked_add(read)
            .ok_or_else(|| format!("{label} read offset overflowed"))?;
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

#[cfg(unix)]
fn hash_and_compare_open_file_fixed_chunks(
    file: &fs::File,
    expected: &[u8],
    label: &str,
) -> Result<String, String> {
    use std::os::unix::fs::FileExt as _;

    const CHUNK_BYTES: usize = 16 * 1024;
    let mut buffer = [0_u8; CHUNK_BYTES];
    let mut hasher = Sha256::new();
    let mut offset = 0_usize;
    while offset < expected.len() {
        let remaining = expected
            .len()
            .checked_sub(offset)
            .ok_or_else(|| format!("{label} comparison length underflowed"))?;
        let requested = remaining.min(buffer.len());
        let read = file
            .read_at(
                &mut buffer[..requested],
                u64::try_from(offset).map_err(display_error)?,
            )
            .map_err(display_error)?;
        if read == 0 {
            return Err(format!("{label} was truncated while verifying"));
        }
        let end = offset
            .checked_add(read)
            .ok_or_else(|| format!("{label} comparison offset overflowed"))?;
        if buffer[..read] != expected[offset..end] {
            return Err(format!("{label} bytes changed while verifying"));
        }
        hasher.update(&buffer[..read]);
        offset = end;
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    fn private_test_root(prefix: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt as _;

        let path = std::env::temp_dir().join(format!(
            "{prefix}-{}-{}",
            std::process::id(),
            NEXT_PRIVATE_ROOT.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        path.canonicalize().unwrap()
    }

    fn owned_catalog() -> (BTreeSet<PathBuf>, BTreeSet<PathBuf>) {
        (
            BTreeSet::from([PathBuf::from("owned/value")]),
            BTreeSet::from([PathBuf::from("owned")]),
        )
    }

    #[test]
    fn closed_private_tree_removes_only_exact_catalog() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        root.create_directory(Path::new("owned")).unwrap();
        root.create_new_file(Path::new("owned/value"), b"value")
            .unwrap();
        assert_eq!(
            root.read_regular_file(Path::new("owned/value"), 5).unwrap(),
            b"value"
        );
        assert!(root.read_regular_file(Path::new("owned/value"), 4).is_err());
        root.replace_exact_file(Path::new("owned/value"), b"value", b"next")
            .unwrap();
        assert_eq!(
            root.read_regular_file(Path::new("owned/value"), 4).unwrap(),
            b"next"
        );
        assert!(root
            .replace_exact_file(Path::new("owned/value"), b"wrong", b"no")
            .is_err());
        let (files, directories) = owned_catalog();
        root.remove_exact_subtree(Path::new("owned"), &files, &directories)
            .unwrap();
        root.remove_empty_root().unwrap();

        let flat = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        let mut handle = flat.create_new_file_handle(Path::new("stdout")).unwrap();
        handle.write_all(b"row").unwrap();
        handle.sync_all().unwrap();
        assert_eq!(handle.read_all_bounded(3).unwrap(), b"row");
        assert!(flat.create_new_file_handle(Path::new("stdout")).is_err());
        assert_eq!(
            flat.read_regular_file(Path::new("stdout"), 3).unwrap(),
            b"row"
        );
        flat.remove_exact_contents(&BTreeSet::from([PathBuf::from("stdout")]))
            .unwrap();
        assert!(flat.path().is_dir());
        flat.remove_empty_root().unwrap();

        let exact = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        exact
            .create_new_file(Path::new("cache-entry"), b"expected")
            .unwrap();
        assert!(exact
            .remove_exact_file(Path::new("cache-entry"), b"wrong")
            .is_err());
        assert_eq!(
            exact
                .read_regular_file(Path::new("cache-entry"), 8)
                .unwrap(),
            b"expected"
        );
        exact
            .replace_exact_file(Path::new("cache-entry"), b"expected", b"replacement")
            .unwrap();
        assert!(exact
            .remove_exact_file(Path::new("cache-entry"), b"expected")
            .is_err());
        assert_eq!(
            exact
                .read_regular_file(Path::new("cache-entry"), 11)
                .unwrap(),
            b"replacement"
        );
        exact
            .remove_exact_file(Path::new("cache-entry"), b"replacement")
            .unwrap();
        exact.remove_empty_root().unwrap();
    }

    #[test]
    fn closed_private_tree_nested_subtree_binds_ancestors_and_preserves_siblings() {
        let root = ClosedPrivateDirectory::new("npa-nested-cleanup-test").unwrap();
        root.create_directories(Path::new("generated/profile/module"))
            .unwrap();
        root.create_new_file(Path::new("generated/profile/module/value"), b"value")
            .unwrap();
        root.create_new_file(Path::new("generated/sibling"), b"preserve")
            .unwrap();
        let (files, directories) = root
            .catalog_subtree_paths(Path::new("generated/profile"))
            .unwrap();
        root.remove_exact_subtree(Path::new("generated/profile"), &files, &directories)
            .unwrap();
        assert_eq!(
            root.read_regular_file(Path::new("generated/sibling"), 8)
                .unwrap(),
            b"preserve"
        );
        root.remove_exact_file(Path::new("generated/sibling"), b"preserve")
            .unwrap();
        root.remove_exact_subtree(
            Path::new("generated"),
            &BTreeSet::new(),
            &BTreeSet::from([PathBuf::from("generated")]),
        )
        .unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn closed_private_tree_nested_cleanup_rejects_renamed_ancestor_replacement() {
        let root = ClosedPrivateDirectory::new("npa-nested-cleanup-test").unwrap();
        root.create_directories(Path::new("generated/profile"))
            .unwrap();
        root.create_new_file(Path::new("generated/profile/value"), b"original")
            .unwrap();
        let (files, directories, identities) =
            root.catalog(Path::new("generated/profile")).unwrap();
        assert!(identities.contains_key(Path::new("generated")));

        let relocated = root.path().join("generated-original");
        fs::rename(root.path().join("generated"), &relocated).unwrap();
        fs::create_dir(root.path().join("generated")).unwrap();
        fs::create_dir(root.path().join("generated/profile")).unwrap();
        fs::write(root.path().join("generated/profile/value"), b"sentinel").unwrap();
        assert!(root
            .remove_catalog_entry(Path::new("generated/profile/value"), false, &identities)
            .is_err());
        assert_eq!(
            fs::read(root.path().join("generated/profile/value")).unwrap(),
            b"sentinel"
        );
        assert_eq!(
            fs::read(relocated.join("profile/value")).unwrap(),
            b"original"
        );

        fs::remove_file(root.path().join("generated/profile/value")).unwrap();
        fs::remove_dir(root.path().join("generated/profile")).unwrap();
        fs::remove_dir(root.path().join("generated")).unwrap();
        fs::remove_file(relocated.join("profile/value")).unwrap();
        fs::remove_dir(relocated.join("profile")).unwrap();
        fs::remove_dir(relocated).unwrap();
        root.remove_empty_root().unwrap();
        let _ = (files, directories);
    }

    #[cfg(unix)]
    #[test]
    fn closed_private_tree_replacement_refuses_swapped_temporary() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        root.create_new_file(Path::new("target"), b"before")
            .unwrap();
        let mut replacement_path = None;
        let error = root
            .replace_exact_file_with_hook(Path::new("target"), b"before", b"after", |temporary| {
                let relocated = temporary.with_extension("opened");
                fs::rename(temporary, &relocated).unwrap();
                fs::write(temporary, b"sentinel").unwrap();
                replacement_path = Some(temporary.to_path_buf());
            })
            .unwrap_err();
        assert!(error.contains("temporary changed before rename"));
        assert_eq!(
            root.read_regular_file(Path::new("target"), 6).unwrap(),
            b"before"
        );
        let replacement_path = replacement_path.unwrap();
        assert_eq!(fs::read(&replacement_path).unwrap(), b"sentinel");

        fs::remove_file(&replacement_path).unwrap();
        let opened = replacement_path.with_extension("opened");
        fs::remove_file(opened).unwrap();
        root.remove_exact_file(Path::new("target"), b"before")
            .unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn closed_private_tree_output_refuses_swapped_basename() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        let output = root.create_new_file_handle(Path::new("stdout")).unwrap();
        let child = output.try_clone_file().unwrap();
        (&child).write_all(b"opened").unwrap();
        drop(child);
        let relocated = root.path().join("opened.stdout");
        fs::rename(root.path().join("stdout"), &relocated).unwrap();
        fs::write(root.path().join("stdout"), b"sentinel").unwrap();
        assert!(output.sync_all().is_err());
        assert!(output.read_all_bounded(64).is_err());
        assert_eq!(fs::read(root.path().join("stdout")).unwrap(), b"sentinel");

        drop(output);
        fs::remove_file(root.path().join("stdout")).unwrap();
        fs::remove_file(relocated).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[test]
    fn closed_private_tree_rejects_unknown_or_replaced_entry() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        root.create_directory(Path::new("owned")).unwrap();
        root.create_new_file(Path::new("owned/value"), b"value")
            .unwrap();
        root.create_new_file(Path::new("owned/unknown"), b"unknown")
            .unwrap();
        let (files, directories) = owned_catalog();
        assert!(root
            .remove_exact_subtree(Path::new("owned"), &files, &directories)
            .is_err());
        assert_eq!(fs::read(root.path().join("owned/value")).unwrap(), b"value");

        fs::remove_file(root.path().join("owned/unknown")).unwrap();
        let (_, _, identities) = root.catalog(Path::new("owned")).unwrap();
        let retained_value = root.path().with_extension("retained-value");
        fs::rename(root.path().join("owned/value"), &retained_value).unwrap();
        fs::write(root.path().join("owned/value"), b"replacement").unwrap();
        assert!(root
            .remove_catalog_entry(Path::new("owned/value"), false, &identities)
            .is_err());
        assert_eq!(
            fs::read(root.path().join("owned/value")).unwrap(),
            b"replacement"
        );
        fs::remove_file(root.path().join("owned/value")).unwrap();
        fs::remove_file(retained_value).unwrap();
        fs::remove_dir(root.path().join("owned")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[test]
    fn captured_cleanup_catalog_rejects_unknown_replacement_and_other_root() {
        let root = ClosedPrivateDirectory::new("npa-captured-cleanup").unwrap();
        root.create_directory(Path::new("owned")).unwrap();
        root.create_new_file(Path::new("owned/value"), b"value")
            .unwrap();
        let catalog = root.capture_cleanup_catalog().unwrap();

        let other = ClosedPrivateDirectory::new("npa-captured-cleanup").unwrap();
        assert!(other.remove_captured_root(&catalog).is_err());
        other.remove_empty_root().unwrap();

        root.create_new_file(Path::new("unknown"), b"sentinel")
            .unwrap();
        assert!(root.remove_captured_root(&catalog).is_err());
        assert_eq!(
            root.read_regular_file(Path::new("owned/value"), 5).unwrap(),
            b"value"
        );
        assert_eq!(
            root.read_regular_file(Path::new("unknown"), 8).unwrap(),
            b"sentinel"
        );
        root.remove_exact_file(Path::new("unknown"), b"sentinel")
            .unwrap();

        let retained_value = root.path().with_extension("retained-value");
        fs::rename(root.path().join("owned/value"), &retained_value).unwrap();
        fs::write(root.path().join("owned/value"), b"value").unwrap();
        assert!(root.remove_captured_root(&catalog).is_err());
        assert_eq!(
            root.read_regular_file(Path::new("owned/value"), 5).unwrap(),
            b"value"
        );
        root.remove_exact_file(Path::new("owned/value"), b"value")
            .unwrap();
        fs::remove_file(retained_value).unwrap();
        fs::remove_dir(root.path().join("owned")).unwrap();
        root.remove_empty_root().unwrap();

        let unchanged = ClosedPrivateDirectory::new("npa-captured-cleanup").unwrap();
        unchanged.create_directory(Path::new("owned")).unwrap();
        unchanged
            .create_new_file(Path::new("owned/value"), b"value")
            .unwrap();
        let unchanged_catalog = unchanged.capture_cleanup_catalog().unwrap();
        unchanged.remove_captured_root(&unchanged_catalog).unwrap();
        assert!(!unchanged.path().exists());
    }

    #[cfg(any(target_vendor = "apple", target_os = "linux"))]
    #[test]
    fn closed_private_tree_publishes_without_replace_or_nesting() {
        let container = ClosedPrivateDirectory::new("npa-publish-container").unwrap();
        container.create_directory(Path::new("parent")).unwrap();
        let parent = container.path().join("parent");

        let collision = ClosedPrivateDirectory::new_in(&parent, "npa-publish-source").unwrap();
        collision
            .create_new_file(Path::new("matrix.json"), b"source")
            .unwrap();
        let occupied = parent.join("occupied");
        fs::create_dir(&occupied).unwrap();
        fs::write(occupied.join("sentinel"), b"destination").unwrap();
        assert!(collision
            .publish_new_root(&occupied, "benchmark matrix")
            .is_err());
        assert_eq!(
            collision
                .read_regular_file(Path::new("matrix.json"), 6)
                .unwrap(),
            b"source"
        );
        assert_eq!(fs::read(occupied.join("sentinel")).unwrap(), b"destination");
        collision
            .remove_exact_root(&BTreeSet::from([PathBuf::from("matrix.json")]))
            .unwrap();
        fs::remove_file(occupied.join("sentinel")).unwrap();
        fs::remove_dir(&occupied).unwrap();

        let published = ClosedPrivateDirectory::new_in(&parent, "npa-publish-source").unwrap();
        published
            .create_new_file(Path::new("matrix.json"), b"published")
            .unwrap();
        let destination = parent.join("published");
        published
            .publish_new_root(&destination, "benchmark matrix")
            .unwrap();
        assert!(!published.path().exists());
        assert_eq!(
            fs::read(destination.join("matrix.json")).unwrap(),
            b"published"
        );
        fs::remove_file(destination.join("matrix.json")).unwrap();
        fs::remove_dir(&destination).unwrap();
        fs::remove_dir(&parent).unwrap();
        container.remove_empty_root().unwrap();
    }

    #[cfg(any(target_vendor = "apple", target_os = "linux"))]
    #[test]
    fn closed_private_tree_publication_rejects_renamed_destination_ancestor() {
        let container = ClosedPrivateDirectory::new("npa-publish-ancestor").unwrap();
        container
            .create_directories(Path::new("ancestor/parent"))
            .unwrap();
        let parent = container.path().join("ancestor/parent");
        let source = ClosedPrivateDirectory::new_in(&parent, "npa-publish-source").unwrap();
        source
            .create_new_file(Path::new("matrix.json"), b"source")
            .unwrap();
        let destination = parent.join("published");

        let relocated = container.path().join("relocated");
        fs::rename(container.path().join("ancestor"), &relocated).unwrap();
        fs::create_dir(container.path().join("ancestor")).unwrap();
        fs::create_dir(container.path().join("ancestor/parent")).unwrap();
        assert!(source
            .publish_new_root(&destination, "benchmark matrix")
            .is_err());
        assert_eq!(
            fs::read(
                relocated
                    .join("parent")
                    .join(
                        source
                            .path()
                            .file_name()
                            .expect("source retains its basename")
                    )
                    .join("matrix.json")
            )
            .unwrap(),
            b"source"
        );

        fs::remove_dir(container.path().join("ancestor/parent")).unwrap();
        fs::remove_dir(container.path().join("ancestor")).unwrap();
        let relocated_source = relocated.join("parent").join(
            source
                .path()
                .file_name()
                .expect("source retains its basename"),
        );
        fs::remove_file(relocated_source.join("matrix.json")).unwrap();
        fs::remove_dir(relocated_source).unwrap();
        fs::remove_dir(relocated.join("parent")).unwrap();
        fs::remove_dir(relocated).unwrap();
        drop(source);
        container.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn closed_private_tree_rejects_symlink_components_and_sparse_huge_files() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        root.create_directories(Path::new("real/nested")).unwrap();
        std::os::unix::fs::symlink(root.path().join("real"), root.path().join("linked")).unwrap();
        assert!(root
            .create_new_file(Path::new("linked/value"), b"no")
            .is_err());
        let huge = root.path().join("huge");
        let file = fs::File::create(&huge).unwrap();
        file.set_len(16 * 1024 * 1024).unwrap();
        assert!(root.read_regular_file(Path::new("huge"), 1024).is_err());
        fs::remove_file(root.path().join("linked")).unwrap();
        fs::remove_file(huge).unwrap();
        fs::remove_dir(root.path().join("real/nested")).unwrap();
        fs::remove_dir(root.path().join("real")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn absolute_regular_file_access_is_fd_anchored_and_bounded() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        let absolute = root.path().join("absolute");
        let mut file = create_new_absolute_file(&absolute, "absolute test file").unwrap();
        file.write_all(b"value").unwrap();
        file.sync_all().unwrap();
        drop(file);
        assert_eq!(
            read_absolute_regular_file(&absolute, 5, "absolute test file").unwrap(),
            b"value"
        );
        assert!(read_absolute_regular_file(&absolute, 4, "absolute test file").is_err());
        assert!(create_new_absolute_file(&absolute, "absolute test file").is_err());
        root.remove_exact_file(Path::new("absolute"), b"value")
            .unwrap();

        std::os::unix::fs::symlink("missing", &absolute).unwrap();
        assert!(read_absolute_regular_file(&absolute, 5, "absolute symlink").is_err());
        assert!(create_new_absolute_file(&absolute, "absolute symlink").is_err());
        fs::remove_file(&absolute).unwrap();

        root.create_directory(Path::new("real")).unwrap();
        std::os::unix::fs::symlink(root.path().join("real"), root.path().join("linked")).unwrap();
        assert!(
            create_new_absolute_file(&root.path().join("linked/value"), "linked output").is_err()
        );
        assert!(create_new_absolute_file(
            &root.path().join("real/../escape"),
            "unnormalized output"
        )
        .is_err());
        fs::remove_file(root.path().join("linked")).unwrap();
        fs::remove_dir(root.path().join("real")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn invocation_regular_file_access_is_relative_fd_anchored_bounded_and_no_follow() {
        let root = ClosedPrivateDirectory::new("npa-invocation-file-test").unwrap();
        root.create_directory(Path::new("real")).unwrap();
        root.create_new_file(Path::new("real/value"), b"value")
            .unwrap();
        let relative = Path::new("Cargo.toml");
        let relative_bytes = read_invocation_regular_file(relative, 1024 * 1024, "relative input")
            .expect("workspace Cargo.toml is readable from the retained invocation cwd");
        assert_eq!(relative_bytes, fs::read(relative).unwrap());
        assert!(read_invocation_regular_file(relative, 4, "relative input").is_err());
        assert!(read_invocation_regular_file(
            &root.path().join("real/../real/value"),
            5,
            "unnormalized input"
        )
        .is_err());

        std::os::unix::fs::symlink(root.path().join("real"), root.path().join("linked")).unwrap();
        assert!(read_invocation_regular_file(
            &root.path().join("linked/value"),
            5,
            "linked parent"
        )
        .is_err());
        std::os::unix::fs::symlink("real/value", root.path().join("linked-value")).unwrap();
        assert!(
            read_invocation_regular_file(&root.path().join("linked-value"), 5, "linked leaf")
                .is_err()
        );

        let output = root.path().join("output");
        write_invocation_regular_file_create_or_same(&output, b"canonical", 9, "output").unwrap();
        write_invocation_regular_file_create_or_same(&output, b"canonical", 9, "output").unwrap();
        assert!(
            write_invocation_regular_file_create_or_same(&output, b"different", 9, "output")
                .is_err()
        );
        assert_eq!(fs::read(&output).unwrap(), b"canonical");
        replace_invocation_regular_file_exact(&output, b"canonical", b"replacement", 32, "output")
            .unwrap();
        assert_eq!(fs::read(&output).unwrap(), b"replacement");
        assert!(replace_invocation_regular_file_exact(
            &output,
            b"wrong",
            b"forbidden",
            32,
            "output"
        )
        .is_err());
        assert_eq!(fs::read(&output).unwrap(), b"replacement");
        fs::remove_file(output).unwrap();

        fs::remove_file(root.path().join("linked-value")).unwrap();
        fs::remove_file(root.path().join("linked")).unwrap();
        root.remove_exact_file(Path::new("real/value"), b"value")
            .unwrap();
        fs::remove_dir(root.path().join("real")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn invocation_exact_replacement_rejects_swapped_temporary_and_ancestor() {
        let root = ClosedPrivateDirectory::new("npa-invocation-replace-test").unwrap();
        root.create_directories(Path::new("ancestor/nested"))
            .unwrap();
        root.create_new_file(Path::new("ancestor/nested/output"), b"before")
            .unwrap();
        let output = root.path().join("ancestor/nested/output");

        let (parent, basename) = open_invocation_parent(&output, "output").unwrap();
        let mut swapped = None;
        let error = replace_invocation_regular_file_exact_with_hook(
            &parent,
            &basename,
            b"before",
            b"after",
            32,
            "output",
            |parent_fd, temporary| {
                let relocated = CString::new("opened-temporary").unwrap();
                assert_eq!(
                    unsafe {
                        libc::renameat(parent_fd, temporary.as_ptr(), parent_fd, relocated.as_ptr())
                    },
                    0
                );
                let replacement = unsafe {
                    libc::openat(
                        parent_fd,
                        temporary.as_ptr(),
                        libc::O_WRONLY
                            | libc::O_CLOEXEC
                            | libc::O_CREAT
                            | libc::O_EXCL
                            | libc::O_NOFOLLOW,
                        0o600,
                    )
                };
                let mut replacement =
                    fs::File::from(owned_fd(replacement, "create sentinel").unwrap());
                replacement.write_all(b"sentinel").unwrap();
                replacement.sync_all().unwrap();
                swapped = Some((temporary.clone(), relocated));
            },
        )
        .unwrap_err();
        assert!(error.contains("temporary changed before publication"));
        assert_eq!(fs::read(&output).unwrap(), b"before");
        let (temporary, relocated_temporary) = swapped.unwrap();
        let parent_path = output.parent().unwrap();
        let temporary_path = parent_path.join(OsStr::from_bytes(temporary.as_bytes()));
        assert_eq!(fs::read(&temporary_path).unwrap(), b"sentinel");
        fs::remove_file(temporary_path).unwrap();
        fs::remove_file(parent_path.join(OsStr::from_bytes(relocated_temporary.as_bytes())))
            .unwrap();

        let (parent, basename) = open_invocation_parent(&output, "output").unwrap();
        let relocated = root.path().join("relocated");
        let error = replace_invocation_regular_file_exact_with_hook(
            &parent,
            &basename,
            b"before",
            b"after",
            32,
            "output",
            |_, _| {
                fs::rename(root.path().join("ancestor"), &relocated).unwrap();
                fs::create_dir(root.path().join("ancestor")).unwrap();
                fs::create_dir(root.path().join("ancestor/nested")).unwrap();
                fs::write(&output, b"sentinel").unwrap();
            },
        )
        .unwrap_err();
        assert!(error.contains("ancestor binding changed"));
        assert_eq!(fs::read(&output).unwrap(), b"sentinel");
        assert_eq!(
            fs::read(relocated.join("nested/output")).unwrap(),
            b"before"
        );

        fs::remove_file(&output).unwrap();
        fs::remove_dir(root.path().join("ancestor/nested")).unwrap();
        fs::remove_dir(root.path().join("ancestor")).unwrap();
        fs::remove_file(relocated.join("nested/output")).unwrap();
        for entry in fs::read_dir(relocated.join("nested")).unwrap() {
            fs::remove_file(entry.unwrap().path()).unwrap();
        }
        fs::remove_dir(relocated.join("nested")).unwrap();
        fs::remove_dir(relocated).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn retained_absolute_parent_rejects_renamed_ancestor_and_replacement() {
        let root = ClosedPrivateDirectory::new("npa-retained-parent-test").unwrap();
        root.create_directories(Path::new("ancestor/nested"))
            .unwrap();
        root.create_new_file(Path::new("ancestor/nested/value"), b"original")
            .unwrap();
        let requested = root.path().join("ancestor/nested/value");
        let (parent, basename) = open_absolute_parent(&requested, "retained input").unwrap();

        let relocated = root.path().join("relocated");
        fs::rename(root.path().join("ancestor"), &relocated).unwrap();
        fs::create_dir(root.path().join("ancestor")).unwrap();
        fs::create_dir(root.path().join("ancestor/nested")).unwrap();
        fs::write(&requested, b"replacement").unwrap();

        assert!(read_bounded_regular_file_at(&parent, &basename, 32, "retained input").is_err());
        assert_eq!(
            fs::read(relocated.join("nested/value")).unwrap(),
            b"original"
        );

        fs::remove_file(&requested).unwrap();
        fs::remove_dir(root.path().join("ancestor/nested")).unwrap();
        fs::remove_dir(root.path().join("ancestor")).unwrap();
        fs::remove_file(relocated.join("nested/value")).unwrap();
        fs::remove_dir(relocated.join("nested")).unwrap();
        fs::remove_dir(relocated).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn attached_output_sync_rejects_renamed_ancestor_and_replacement() {
        let root = ClosedPrivateDirectory::new("npa-attached-output-test").unwrap();
        root.create_directories(Path::new("ancestor/nested"))
            .unwrap();
        let requested = root.path().join("ancestor/nested/output");
        let mut output = create_new_absolute_file(&requested, "attached output").unwrap();
        output.write_all(b"original").unwrap();

        let relocated = root.path().join("relocated");
        fs::rename(root.path().join("ancestor"), &relocated).unwrap();
        fs::create_dir(root.path().join("ancestor")).unwrap();
        fs::create_dir(root.path().join("ancestor/nested")).unwrap();
        fs::write(&requested, b"replacement").unwrap();

        assert!(output.sync_all().is_err());
        drop(output);
        assert_eq!(
            fs::read(relocated.join("nested/output")).unwrap(),
            b"original"
        );

        fs::remove_file(&requested).unwrap();
        fs::remove_dir(root.path().join("ancestor/nested")).unwrap();
        fs::remove_dir(root.path().join("ancestor")).unwrap();
        fs::remove_file(relocated.join("nested/output")).unwrap();
        fs::remove_dir(relocated.join("nested")).unwrap();
        fs::remove_dir(relocated).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn private_file_reader_rejects_unrepresentable_maximum() {
        let root = ClosedPrivateDirectory::new("npa-private-read-limit").unwrap();
        root.create_new_file(Path::new("value"), b"value").unwrap();
        assert!(root
            .read_regular_file(Path::new("value"), u64::MAX)
            .is_err());
        root.remove_exact_file(Path::new("value"), b"value")
            .unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn executable_snapshot_is_mode_bound_and_rejects_path_replacement() {
        use std::os::unix::fs::PermissionsExt as _;

        let source_root = ClosedPrivateDirectory::new("npa-executable-source").unwrap();
        source_root
            .create_new_file(Path::new("runner"), b"#!/bin/sh\nexit 0\n")
            .unwrap();
        let private = ClosedPrivateDirectory::new("npa-executable-snapshot").unwrap();
        let executable = private
            .create_executable_snapshot(
                Path::new("runner"),
                &source_root.path().join("runner"),
                1024,
                "test executable",
            )
            .unwrap();
        assert_eq!(executable.sha256(), hex_sha256(b"#!/bin/sh\nexit 0\n"));
        assert_eq!(
            fs::metadata(executable.path())
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
        executable.verify().unwrap();

        let relocated = private.path().join("opened-runner");
        fs::rename(executable.path(), &relocated).unwrap();
        fs::write(executable.path(), b"#!/bin/sh\nexit 1\n").unwrap();
        fs::set_permissions(executable.path(), fs::Permissions::from_mode(0o700)).unwrap();
        assert!(executable.verify().is_err());
        assert_eq!(fs::read(executable.path()).unwrap(), b"#!/bin/sh\nexit 1\n");

        drop(executable);
        fs::remove_file(private.path().join("runner")).unwrap();
        fs::remove_file(relocated).unwrap();
        private.remove_empty_root().unwrap();
        source_root
            .remove_exact_file(Path::new("runner"), b"#!/bin/sh\nexit 0\n")
            .unwrap();
        source_root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn detached_executable_is_private_read_only_and_byte_bound() {
        use std::io::{Read as _, Seek as _, SeekFrom, Write as _};
        use std::os::fd::IntoRawFd as _;

        let source_root = ClosedPrivateDirectory::new("npa-detached-source").unwrap();
        source_root
            .create_new_file(Path::new("runner"), b"#!/bin/sh\nexit 0\n")
            .unwrap();
        let scratch = ClosedPrivateDirectory::new("npa-detached-private").unwrap();
        let attached = scratch
            .create_executable_snapshot(
                Path::new("runner"),
                &source_root.path().join("runner"),
                1024,
                "detached test executable",
            )
            .unwrap();
        let detached = attached.detach_for_trusted_execution().unwrap();
        #[cfg(target_os = "linux")]
        assert!(!scratch.path().join("runner").exists());
        #[cfg(target_os = "macos")]
        assert!(scratch.path().join("runner").is_file());
        detached.verify().unwrap();
        assert_eq!(detached.audit_bytes(), b"#!/bin/sh\nexit 0\n");

        let mut duplicate = detached.try_clone_file().unwrap();
        assert!(duplicate.write_all(b"forbidden").is_err());
        duplicate.seek(SeekFrom::Start(0)).unwrap();
        let mut bytes = Vec::new();
        duplicate.read_to_end(&mut bytes).unwrap();
        assert_eq!(bytes, detached.audit_bytes());
        detached.verify().unwrap();

        let fabricated = detached.try_clone_file().unwrap().into_raw_fd();
        let error = consume_inherited_detached_executable(
            fabricated,
            1024,
            "fabricated inherited executable",
        )
        .unwrap_err();
        assert!(error.contains("does not identify the running image"));

        #[cfg(target_os = "macos")]
        {
            drop(detached);
            scratch
                .remove_exact_file(Path::new("runner"), b"#!/bin/sh\nexit 0\n")
                .unwrap();
            scratch.remove_empty_root().unwrap();
        }
        #[cfg(not(target_os = "macos"))]
        scratch.leave_in_place();
        source_root
            .remove_exact_file(Path::new("runner"), b"#!/bin/sh\nexit 0\n")
            .unwrap();
        source_root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn sealed_flat_snapshot_rejects_mode_hardlink_and_unknown_population() {
        use std::os::unix::fs::PermissionsExt as _;

        let root = ClosedPrivateDirectory::new("npa-sealed-flat").unwrap();
        root.create_new_file(Path::new("a"), b"a").unwrap();
        root.create_new_file(Path::new("b"), b"bb").unwrap();
        let expected = BTreeSet::from([PathBuf::from("a"), PathBuf::from("b")]);
        let files = root.read_exact_flat_regular_files(&expected, 2, 3).unwrap();
        assert_eq!(files[Path::new("a")].bytes, b"a");
        assert_eq!(files[Path::new("b")].bytes, b"bb");

        fs::set_permissions(root.path().join("a"), fs::Permissions::from_mode(0o700)).unwrap();
        assert!(root.read_exact_flat_regular_files(&expected, 2, 3).is_err());
        fs::set_permissions(root.path().join("a"), fs::Permissions::from_mode(0o600)).unwrap();

        fs::hard_link(root.path().join("a"), root.path().join("alias")).unwrap();
        assert!(root.read_exact_flat_regular_files(&expected, 2, 3).is_err());
        fs::remove_file(root.path().join("alias")).unwrap();
        fs::write(root.path().join("unknown"), b"x").unwrap();
        assert!(root.read_exact_flat_regular_files(&expected, 2, 3).is_err());

        fs::remove_file(root.path().join("unknown")).unwrap();
        fs::remove_file(root.path().join("a")).unwrap();
        fs::remove_file(root.path().join("b")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn sealed_flat_snapshot_uses_a_bounded_descriptor_window_at_lane_sizes() {
        use std::os::unix::fs::PermissionsExt as _;

        const CHILD_ROOT: &str = "NPA_TEST_SEALED_LOW_NOFILE_ROOT";
        const CHILD_COUNT: &str = "NPA_TEST_SEALED_LOW_NOFILE_COUNT";

        if let (Some(root_path), Some(count)) =
            (std::env::var_os(CHILD_ROOT), std::env::var_os(CHILD_COUNT))
        {
            let count = count.to_string_lossy().parse::<usize>().unwrap();
            let root = ClosedPrivateDirectory::open_existing(Path::new(&root_path), "sealed-final")
                .unwrap();
            let expected = (0..count)
                .map(|index| PathBuf::from(format!("member-{index:04}")))
                .collect::<BTreeSet<_>>();
            let lowered = libc::rlimit {
                rlim_cur: 64,
                rlim_max: 64,
            };
            assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &lowered) }, 0);
            assert_eq!(
                root.read_exact_flat_regular_files(&expected, 1, u64::try_from(count).unwrap(),)
                    .unwrap()
                    .len(),
                count
            );
            root.leave_in_place();
            return;
        }

        fn validate_population(count: usize) {
            let outer = private_test_root("npa-sealed-low-nofile");
            let root_path = outer.join("sealed");
            fs::create_dir(&root_path).unwrap();
            fs::set_permissions(&root_path, fs::Permissions::from_mode(0o700)).unwrap();
            let mut expected = BTreeSet::new();
            for index in 0..count {
                let name = format!("member-{index:04}");
                fs::write(root_path.join(&name), b"x").unwrap();
                fs::set_permissions(root_path.join(&name), fs::Permissions::from_mode(0o600))
                    .unwrap();
                expected.insert(PathBuf::from(name));
            }
            let test_name = std::thread::current().name().unwrap().to_owned();
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", &test_name, "--nocapture"])
                .env(CHILD_ROOT, &root_path)
                .env(CHILD_COUNT, count.to_string())
                .status()
                .unwrap();
            assert!(status.success());
            for path in expected {
                fs::remove_file(root_path.join(path)).unwrap();
            }
            fs::remove_dir(root_path).unwrap();
            fs::remove_dir(outer).unwrap();
        }

        // The largest catalogs are SNAP 608 and VMSP 833 including the seal.
        validate_population(608);
        validate_population(833);
    }

    #[cfg(unix)]
    #[test]
    fn prepared_private_destination_binds_absence_and_full_parent_chain() {
        let outer = private_test_root("npa-prepared-destination");
        let parent = outer.join("parent");
        fs::create_dir(&parent).unwrap();
        let output = parent.join("sealed-run");

        let appeared = prepare_new_absolute_private_directory(&output, "sealed-run").unwrap();
        fs::create_dir(&output).unwrap();
        assert!(appeared.create().is_err());
        assert!(output.is_dir());
        fs::remove_dir(&output).unwrap();

        let swapped = prepare_new_absolute_private_directory(&output, "sealed-run").unwrap();
        let relocated = outer.join("relocated-parent");
        fs::rename(&parent, &relocated).unwrap();
        fs::create_dir(&parent).unwrap();
        fs::write(parent.join("sentinel"), b"replacement").unwrap();
        assert!(swapped.create().is_err());
        assert_eq!(fs::read(parent.join("sentinel")).unwrap(), b"replacement");
        assert!(!relocated.join("sealed-run").exists());

        fs::remove_file(parent.join("sentinel")).unwrap();
        fs::remove_dir(&parent).unwrap();
        fs::remove_dir(&relocated).unwrap();
        fs::remove_dir(&outer).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn prepared_private_destination_rejects_mkdir_to_open_replacement() {
        let outer = private_test_root("npa-prepared-create-hook");
        let output = outer.join("sealed-run");
        let destination = prepare_new_absolute_private_directory(&output, "sealed-run").unwrap();
        let relocated = outer.join("relocated-run");
        let error = match destination.create_with_hook(|| {
            fs::rename(&output, &relocated).map_err(display_error)?;
            fs::create_dir(&output).map_err(display_error)?;
            fs::write(output.join("sentinel"), b"replacement").map_err(display_error)?;
            Ok(())
        }) {
            Ok(directory) => {
                directory.leave_in_place();
                panic!("mkdir-to-open replacement was accepted")
            }
            Err(error) => error,
        };
        assert!(error.contains("invalid identity") || error.contains("changed"));
        assert_eq!(fs::read(output.join("sentinel")).unwrap(), b"replacement");
        assert!(relocated.is_dir());

        fs::remove_file(output.join("sentinel")).unwrap();
        fs::remove_dir(&output).unwrap();
        fs::remove_dir(&relocated).unwrap();
        fs::remove_dir(&outer).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn sealed_owned_byte_verifier_is_exact_bounded_and_mode_bound() {
        use std::os::unix::fs::PermissionsExt as _;

        let root = ClosedPrivateDirectory::new("npa-sealed-owned").unwrap();
        root.create_new_file(Path::new("a"), b"alpha").unwrap();
        root.create_new_file(Path::new("b"), b"beta").unwrap();
        let expected = BTreeMap::from([
            (PathBuf::from("a"), b"alpha".as_slice()),
            (PathBuf::from("b"), b"beta".as_slice()),
        ]);
        root.verify_exact_flat_regular_file_bytes(&expected, 5, 9)
            .unwrap();
        assert!(root
            .verify_exact_flat_regular_file_bytes(&expected, 4, 9)
            .is_err());
        assert!(root
            .verify_exact_flat_regular_file_bytes(&expected, 5, 8)
            .is_err());

        fs::write(root.path().join("b"), b"BETA").unwrap();
        assert!(root
            .verify_exact_flat_regular_file_bytes(&expected, 5, 9)
            .is_err());
        fs::write(root.path().join("b"), b"beta").unwrap();
        fs::set_permissions(root.path().join("b"), fs::Permissions::from_mode(0o700)).unwrap();
        assert!(root
            .verify_exact_flat_regular_file_bytes(&expected, 5, 9)
            .is_err());

        fs::set_permissions(root.path().join("b"), fs::Permissions::from_mode(0o600)).unwrap();
        fs::remove_file(root.path().join("a")).unwrap();
        fs::remove_file(root.path().join("b")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn bounded_directory_catalog_rejects_readdir_error_instead_of_truncating() {
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                TEST_READDIR_ERROR_AFTER_ENTRIES.with(|limit| limit.set(None));
            }
        }

        let root = ClosedPrivateDirectory::new("npa-readdir-error").unwrap();
        root.create_new_file(Path::new("expected"), b"value")
            .unwrap();
        root.create_new_file(Path::new("unknown"), b"sentinel")
            .unwrap();
        TEST_READDIR_ERROR_AFTER_ENTRIES.with(|limit| limit.set(Some(1)));
        let _reset = Reset;
        let error = directory_entry_names_bounded(root.root_fd.as_raw_fd(), 3, 128).unwrap_err();
        assert!(error.contains("injected directory enumeration error"));
        assert_eq!(fs::read(root.path().join("unknown")).unwrap(), b"sentinel");

        TEST_READDIR_ERROR_AFTER_ENTRIES.with(|limit| limit.set(None));
        fs::remove_file(root.path().join("expected")).unwrap();
        fs::remove_file(root.path().join("unknown")).unwrap();
        root.remove_empty_root().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn closed_private_tree_refuses_symlink_and_renamed_out_inode() {
        let root = ClosedPrivateDirectory::new("npa-closed-tree-test").unwrap();
        root.create_directory(Path::new("owned")).unwrap();
        std::os::unix::fs::symlink("missing", root.path().join("owned/link")).unwrap();
        let files = BTreeSet::new();
        let directories = BTreeSet::from([PathBuf::from("owned")]);
        assert!(root
            .remove_exact_subtree(Path::new("owned"), &files, &directories)
            .is_err());
        fs::remove_file(root.path().join("owned/link")).unwrap();
        fs::remove_dir(root.path().join("owned")).unwrap();

        let original = root.path().to_path_buf();
        let relocated = original.with_extension("relocated");
        fs::write(original.join("sentinel"), b"keep").unwrap();
        fs::rename(&original, &relocated).unwrap();
        fs::create_dir(&original).unwrap();
        drop(root);
        assert_eq!(fs::read(relocated.join("sentinel")).unwrap(), b"keep");
        assert!(original.is_dir());
        fs::remove_dir(&original).unwrap();
        fs::remove_file(relocated.join("sentinel")).unwrap();
        fs::remove_dir(&relocated).unwrap();
    }
}
