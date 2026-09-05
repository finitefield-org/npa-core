//! Filesystem helpers owned by the CLI orchestration layer.

use std::{
    ffi::{OsStr, OsString},
    path::{Component, Path, PathBuf},
};

use npa_package::{validate_package_path, PackagePath};

use crate::diagnostic::{CommandDiagnostic, DiagnosticKind};

/// Read one bounded regular file without following any symbolic-link path
/// component. Relative paths are resolved below a retained descriptor for the
/// invocation's current directory; unsupported platforms fail closed.
pub fn read_bounded_regular_file(path: &Path, maximum_bytes: u64) -> std::io::Result<Vec<u8>> {
    use std::io::Read as _;

    if maximum_bytes == 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "file byte limit must be positive",
        ));
    }
    let (parent_path, basename) = split_file_path(path)?;
    let bound_parent = no_follow_directory::open_bound_directory(&parent_path)?;
    bound_parent.verify()?;
    let parent = bound_parent.root_clone()?;
    let mut file = parent
        .open_regular_file(&basename)?
        .ok_or_else(|| std::io::Error::from(std::io::ErrorKind::NotFound))?;
    let identity = no_follow_directory::regular_file_identity(&file)?;
    let metadata = file.metadata()?;
    if metadata.len() > maximum_bytes {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "regular file exceeds its byte limit",
        ));
    }
    let capacity = usize::try_from(metadata.len()).map_err(|_| {
        std::io::Error::new(std::io::ErrorKind::InvalidData, "file length is not usize")
    })?;
    let mut bytes = Vec::with_capacity(capacity);
    std::io::Read::by_ref(&mut file)
        .take(maximum_bytes.saturating_add(1))
        .read_to_end(&mut bytes)?;
    if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > maximum_bytes {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "regular file grew beyond its byte limit",
        ));
    }
    no_follow_directory::require_named_regular_file_identity(&parent, &basename, identity)?;
    bound_parent.verify()?;
    Ok(bytes)
}

/// A retained no-follow directory capability for reading a closed family of
/// caller-selected files below one root. Holding this value prevents a later
/// pathname reopen from redirecting reads after root or ancestor replacement.
#[derive(Debug)]
pub struct BoundedReadRoot {
    directory: no_follow_directory::BoundDirectory,
}

type DirectoryBinding = (
    no_follow_directory::Directory,
    OsString,
    no_follow_directory::Identity,
);

struct BoundedReadParent {
    directory: no_follow_directory::Directory,
    basename: OsString,
    bindings: Vec<DirectoryBinding>,
}

impl BoundedReadRoot {
    /// Open one existing root without following any symbolic-link component.
    pub fn open(path: &Path) -> std::io::Result<Self> {
        Ok(Self {
            directory: no_follow_directory::open_bound_directory(path)?,
        })
    }

    /// Read one normalized relative regular file from the retained root.
    pub fn read(&self, path: &Path, maximum_bytes: u64) -> std::io::Result<Vec<u8>> {
        self.read_with_hook(path, maximum_bytes, || {})
    }

    fn read_with_hook<F>(
        &self,
        path: &Path,
        maximum_bytes: u64,
        after_open: F,
    ) -> std::io::Result<Vec<u8>>
    where
        F: FnOnce(),
    {
        use std::io::Read as _;

        if maximum_bytes == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "file byte limit must be positive",
            ));
        }
        self.directory.verify()?;
        let BoundedReadParent {
            directory: parent,
            basename,
            bindings: parent_bindings,
        } = self.open_relative_parent(path)?;
        let mut file = parent
            .open_regular_file(&basename)?
            .ok_or_else(|| std::io::Error::from(std::io::ErrorKind::NotFound))?;
        let identity = no_follow_directory::regular_file_identity(&file)?;
        after_open();
        let metadata = file.metadata()?;
        if metadata.len() > maximum_bytes {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "regular file exceeds its byte limit",
            ));
        }
        let capacity = usize::try_from(metadata.len()).map_err(|_| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "file length is not usize")
        })?;
        let mut bytes = Vec::with_capacity(capacity);
        std::io::Read::by_ref(&mut file)
            .take(maximum_bytes.saturating_add(1))
            .read_to_end(&mut bytes)?;
        if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > maximum_bytes {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "regular file grew beyond its byte limit",
            ));
        }
        no_follow_directory::require_named_regular_file_identity(&parent, &basename, identity)?;
        for (ancestor, component, identity) in parent_bindings.iter().rev() {
            ancestor.require_named_directory_identity(component, *identity)?;
        }
        self.directory.verify()?;
        Ok(bytes)
    }

    fn open_relative_parent(&self, path: &Path) -> std::io::Result<BoundedReadParent> {
        if path.as_os_str().is_empty() || path.is_absolute() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "bounded root path must be nonempty and relative",
            ));
        }
        let basename = path.file_name().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "file path has no basename",
            )
        })?;
        let mut parent = self.directory.root_clone()?;
        let mut bindings = Vec::new();
        let mut components = path.components().peekable();
        while let Some(component) = components.next() {
            match component {
                Component::Normal(component) if components.peek().is_some() => {
                    let retained_parent = parent.try_clone()?;
                    let child = parent.open_or_create_directory(component, false)?;
                    bindings.push((retained_parent, component.to_owned(), child.identity()?));
                    parent = child;
                }
                Component::Normal(_) if components.peek().is_none() => {}
                _ => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        "bounded root path is not normalized",
                    ));
                }
            }
        }
        Ok(BoundedReadParent {
            directory: parent,
            basename: basename.to_owned(),
            bindings,
        })
    }
}

fn split_file_path(path: &Path) -> std::io::Result<(PathBuf, OsString)> {
    let basename = path.file_name().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "file path has no basename",
        )
    })?;
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    Ok((parent.to_owned(), basename.to_owned()))
}

/// Directory-relative filesystem primitives used by security-sensitive CLI stores.
///
/// The Unix implementation keeps every traversal below an already-open directory
/// descriptor, refuses symbolic-link final components, and verifies the opened
/// object kind. Callers must still perform their own namespace/containment policy
/// before asking this wrapper to create a directory. Unsupported platforms expose
/// the same API but always return [`std::io::ErrorKind::Unsupported`].
pub(crate) mod no_follow_directory {
    use std::{
        ffi::{OsStr, OsString},
        fs::File,
        io,
        path::{Component, Path},
    };

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) struct Identity {
        pub(crate) device: u64,
        pub(crate) inode: u64,
    }

    #[derive(Debug)]
    pub(crate) struct Directory {
        file: File,
    }

    #[derive(Debug)]
    pub(crate) struct BoundDirectory {
        root: Directory,
        bindings: Vec<(Directory, OsString, Identity)>,
    }

    impl BoundDirectory {
        pub(crate) fn root_clone(&self) -> io::Result<Directory> {
            self.root.try_clone()
        }

        pub(crate) fn verify(&self) -> io::Result<()> {
            for (parent, component, identity) in &self.bindings {
                parent.require_named_directory_identity(component, *identity)?;
            }
            Ok(())
        }
    }

    #[derive(Debug)]
    pub(crate) enum DirectoryChild {
        Directory(Directory),
        Regular(File),
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) enum EntryKind {
        Directory,
        Regular,
        SymbolicLink,
        Other,
    }

    #[cfg(unix)]
    pub(crate) fn regular_file_identity(file: &File) -> io::Result<Identity> {
        use std::os::unix::fs::MetadataExt;

        let metadata = file.metadata()?;
        if !metadata.file_type().is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "expected a regular file",
            ));
        }
        Ok(Identity {
            device: metadata.dev(),
            inode: metadata.ino(),
        })
    }

    #[cfg(not(unix))]
    pub(crate) fn regular_file_identity(_file: &File) -> io::Result<Identity> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "descriptor-relative filesystem operations require Unix",
        ))
    }

    /// Require a direct named child to remain the same regular-file inode that
    /// the caller already opened. This closes the gap between same-fd reads and
    /// later namespace-sensitive operations such as chmod or unlink.
    #[cfg(unix)]
    pub(crate) fn require_named_regular_file_identity(
        directory: &Directory,
        component: &OsStr,
        expected: Identity,
    ) -> io::Result<()> {
        directory.require_named_regular_file_identity(component, expected)
    }

    pub(crate) fn open_bound_directory(path: &Path) -> io::Result<BoundDirectory> {
        let (mut directory, components) = if path.is_absolute() {
            let mut components = normalized_components(path, false)?;
            let root = Directory::open_filesystem_root()?;
            if cfg!(target_os = "macos")
                && components.first().is_some_and(|component| {
                    component == OsStr::new("var") || component == OsStr::new("tmp")
                })
            {
                components.insert(0, OsString::from("private"));
            }
            (root, components)
        } else {
            (
                Directory::open_current_directory()?,
                normalized_components(path, true)?,
            )
        };
        let mut bindings = Vec::new();
        for component in components {
            let parent = directory.try_clone()?;
            let child = directory.open_or_create_directory(&component, false)?;
            bindings.push((parent, component, child.identity()?));
            directory = child;
        }
        let bound = BoundDirectory {
            root: directory,
            bindings,
        };
        bound.verify()?;
        Ok(bound)
    }

    #[cfg(not(unix))]
    pub(crate) fn require_named_regular_file_identity(
        _directory: &Directory,
        _component: &OsStr,
        _expected: Identity,
    ) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "descriptor-relative filesystem operations require Unix",
        ))
    }

    /// Open a selected directory path without following any symbolic-link
    /// component. Relative parent components are traversed from the retained
    /// current-directory descriptor. Missing normal components are created
    /// only when `create` is true.
    pub(crate) fn open_absolute_directory(path: &Path, create: bool) -> io::Result<Directory> {
        let (mut directory, components) = if path.is_absolute() {
            let mut components = normalized_components(path, false)?;
            let root = Directory::open_filesystem_root()?;
            // macOS exposes `/var` and `/tmp` as system-owned compatibility
            // symlinks into `/private`. Accept only these two fixed aliases by
            // rewriting before the no-follow component walk; every
            // package-controlled component remains no-follow.
            if cfg!(target_os = "macos")
                && components.first().is_some_and(|component| {
                    component == OsStr::new("var") || component == OsStr::new("tmp")
                })
            {
                components.insert(0, OsString::from("private"));
            }
            (root, components)
        } else {
            // Retain the actual cwd inode immediately. Resolving getcwd() to an
            // absolute string and reopening it would permit an ancestor rename
            // to redirect this operation between those two steps.
            (
                Directory::open_current_directory()?,
                selected_relative_components(path)?,
            )
        };
        for component in components {
            directory = if component == OsStr::new("..") {
                directory.open_parent_directory()?
            } else {
                directory.open_or_create_directory(&component, create)?
            };
        }
        Ok(directory)
    }

    fn selected_relative_components(path: &Path) -> io::Result<Vec<OsString>> {
        let mut normalized = Vec::new();
        for component in path.components() {
            match component {
                Component::CurDir => {}
                Component::Normal(component) => normalized.push(component.to_owned()),
                Component::ParentDir => {
                    if normalized
                        .last()
                        .is_some_and(|component| component != OsStr::new(".."))
                    {
                        normalized.pop();
                    } else {
                        normalized.push(OsString::from(".."));
                    }
                }
                Component::RootDir | Component::Prefix(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "relative directory path contains an absolute prefix",
                    ));
                }
            }
        }
        Ok(normalized)
    }

    fn normalized_components(path: &Path, confined_relative: bool) -> io::Result<Vec<OsString>> {
        let mut normalized = Vec::new();
        for component in path.components() {
            match component {
                Component::RootDir | Component::CurDir => {}
                Component::Normal(component) => normalized.push(component.to_owned()),
                Component::ParentDir => {
                    if normalized.pop().is_none() {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            if confined_relative {
                                "relative directory path escapes the retained cwd"
                            } else {
                                "directory path escapes the filesystem root"
                            },
                        ));
                    }
                }
                Component::Prefix(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "unsupported directory path prefix",
                    ));
                }
            }
        }
        Ok(normalized)
    }

    #[cfg(unix)]
    mod platform {
        use std::{
            ffi::{CString, OsString},
            os::{
                fd::{AsRawFd, FromRawFd, RawFd},
                unix::ffi::{OsStrExt, OsStringExt},
            },
        };

        use super::*;

        impl Directory {
            pub(crate) fn try_clone(&self) -> io::Result<Self> {
                Ok(Self {
                    file: self.file.try_clone()?,
                })
            }

            pub(crate) fn sync_all(&self) -> io::Result<()> {
                self.file.sync_all()
            }

            pub(crate) fn open_filesystem_root() -> io::Result<Self> {
                let root = CString::new("/").expect("filesystem root contains no NUL");
                // SAFETY: `root` is a valid NUL-terminated pathname and successful
                // ownership of the returned descriptor is transferred to `File` once.
                let descriptor = unsafe {
                    libc::open(
                        root.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: `descriptor` is newly returned by `open` and uniquely owned.
                let file = unsafe { File::from_raw_fd(descriptor) };
                Ok(Self { file })
            }

            pub(crate) fn open_current_directory() -> io::Result<Self> {
                let current = CString::new(".").expect("current-directory path contains no NUL");
                // SAFETY: `current` is a constant NUL-terminated pathname.
                let descriptor = unsafe {
                    libc::open(
                        current.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: descriptor is freshly returned and uniquely owned.
                Ok(Self {
                    file: unsafe { File::from_raw_fd(descriptor) },
                })
            }

            pub(crate) fn open_parent_directory(&self) -> io::Result<Self> {
                let parent = CString::new("..").expect("parent component contains no NUL");
                let descriptor = open_directory_at(self.file.as_raw_fd(), &parent)?;
                // SAFETY: `descriptor` is newly returned by `openat` and uniquely owned.
                let directory = Self {
                    file: unsafe { File::from_raw_fd(descriptor) },
                };
                directory.require_directory()?;
                Ok(directory)
            }

            pub(crate) fn open_or_create_directory(
                &self,
                component: &OsStr,
                create: bool,
            ) -> io::Result<Self> {
                let component = component_c_string(component)?;
                let descriptor = open_directory_at(self.file.as_raw_fd(), &component);
                let descriptor = match descriptor {
                    Ok(descriptor) => descriptor,
                    Err(error) if create && error.kind() == io::ErrorKind::NotFound => {
                        // SAFETY: the parent descriptor is live and `component` is one
                        // validated NUL-terminated path component.
                        let status = unsafe {
                            libc::mkdirat(self.file.as_raw_fd(), component.as_ptr(), 0o700)
                        };
                        if status != 0 {
                            let mkdir_error = io::Error::last_os_error();
                            if mkdir_error.kind() != io::ErrorKind::AlreadyExists {
                                return Err(mkdir_error);
                            }
                        }
                        open_directory_at(self.file.as_raw_fd(), &component)?
                    }
                    Err(error) => return Err(error),
                };
                // SAFETY: `descriptor` is newly returned by `openat` and uniquely owned.
                let file = unsafe { File::from_raw_fd(descriptor) };
                let directory = Self { file };
                directory.require_directory()?;
                Ok(directory)
            }

            pub(crate) fn create_new_directory(&self, component: &OsStr) -> io::Result<Self> {
                let component = component_c_string(component)?;
                // SAFETY: the retained parent descriptor and component are valid.
                if unsafe { libc::mkdirat(self.file.as_raw_fd(), component.as_ptr(), 0o700) } != 0 {
                    return Err(io::Error::last_os_error());
                }
                let descriptor = open_directory_at(self.file.as_raw_fd(), &component)?;
                // SAFETY: descriptor is freshly returned and uniquely owned.
                Ok(Self {
                    file: unsafe { File::from_raw_fd(descriptor) },
                })
            }

            pub(crate) fn rename_entry(
                &self,
                source: &OsStr,
                destination: &OsStr,
            ) -> io::Result<()> {
                let source = component_c_string(source)?;
                let destination = component_c_string(destination)?;
                // SAFETY: both names are direct children of the retained parent.
                if unsafe {
                    libc::renameat(
                        self.file.as_raw_fd(),
                        source.as_ptr(),
                        self.file.as_raw_fd(),
                        destination.as_ptr(),
                    )
                } != 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            }

            pub(crate) fn entry_names(&self) -> io::Result<Vec<OsString>> {
                directory_entry_names(self.file.as_raw_fd())
            }

            pub(crate) fn read_symbolic_link(&self, component: &OsStr) -> io::Result<OsString> {
                const MAX_SYMBOLIC_LINK_BYTES: usize = 65_536;

                let component = component_c_string(component)?;
                let before = stat_at(self.file.as_raw_fd(), &component)?;
                if before.st_mode & libc::S_IFMT != libc::S_IFLNK {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "entry is not a symbolic link",
                    ));
                }
                let mut capacity = 256usize;
                loop {
                    let mut bytes = vec![0_u8; capacity];
                    // SAFETY: parent fd, component, and output buffer are live.
                    let length = unsafe {
                        libc::readlinkat(
                            self.file.as_raw_fd(),
                            component.as_ptr(),
                            bytes.as_mut_ptr().cast(),
                            bytes.len(),
                        )
                    };
                    if length < 0 {
                        return Err(io::Error::last_os_error());
                    }
                    let length = usize::try_from(length)
                        .map_err(|_| io::Error::other("invalid symbolic-link length"))?;
                    if length < bytes.len() {
                        bytes.truncate(length);
                        let after = stat_at(self.file.as_raw_fd(), &component)?;
                        if after.st_mode & libc::S_IFMT != libc::S_IFLNK
                            || after.st_dev != before.st_dev
                            || after.st_ino != before.st_ino
                        {
                            return Err(io::Error::other(
                                "symbolic-link identity changed during read",
                            ));
                        }
                        return Ok(OsString::from_vec(bytes));
                    }
                    if capacity >= MAX_SYMBOLIC_LINK_BYTES {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "symbolic-link target exceeds the 64 KiB byte limit",
                        ));
                    }
                    capacity = capacity.saturating_mul(2).min(MAX_SYMBOLIC_LINK_BYTES);
                }
            }

            pub(crate) fn create_symbolic_link(
                &self,
                target: &OsStr,
                component: &OsStr,
            ) -> io::Result<()> {
                use std::os::unix::ffi::OsStrExt as _;

                let target = CString::new(target.as_bytes()).map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "symbolic-link target contains NUL",
                    )
                })?;
                let component = component_c_string(component)?;
                // SAFETY: target and component are NUL-terminated, and the
                // retained destination parent descriptor remains live.
                if unsafe {
                    libc::symlinkat(target.as_ptr(), self.file.as_raw_fd(), component.as_ptr())
                } != 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            }

            pub(crate) fn open_regular_file(&self, component: &OsStr) -> io::Result<Option<File>> {
                let component = component_c_string(component)?;
                // O_NONBLOCK prevents a hostile FIFO from blocking before the kind check.
                // SAFETY: the parent descriptor is live and `component` is validated.
                let descriptor = unsafe {
                    libc::openat(
                        self.file.as_raw_fd(),
                        component.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                    )
                };
                if descriptor < 0 {
                    let error = io::Error::last_os_error();
                    if error.kind() == io::ErrorKind::NotFound {
                        return Ok(None);
                    }
                    return Err(error);
                }
                // SAFETY: `descriptor` is newly returned by `openat` and uniquely owned.
                let file = unsafe { File::from_raw_fd(descriptor) };
                let status = stat(file.as_raw_fd())?;
                if status.st_mode & libc::S_IFMT != libc::S_IFREG {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "cache entry is not a regular file",
                    ));
                }
                Ok(Some(file))
            }

            /// Classify one direct child without following a symbolic link.
            /// Callers must still open and validate the entry they consume;
            /// this snapshot is intended for fail-closed kind policy and
            /// stable diagnostics.
            pub(crate) fn entry_kind(&self, component: &OsStr) -> io::Result<Option<EntryKind>> {
                let component = component_c_string(component)?;
                let status = match stat_at(self.file.as_raw_fd(), &component) {
                    Ok(status) => status,
                    Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
                    Err(error) => return Err(error),
                };
                let kind = match status.st_mode & libc::S_IFMT {
                    libc::S_IFDIR => EntryKind::Directory,
                    libc::S_IFREG => EntryKind::Regular,
                    libc::S_IFLNK => EntryKind::SymbolicLink,
                    _ => EntryKind::Other,
                };
                Ok(Some(kind))
            }

            pub(crate) fn require_named_regular_file_identity(
                &self,
                component: &OsStr,
                expected: Identity,
            ) -> io::Result<()> {
                let component = component_c_string(component)?;
                let current = stat_at(self.file.as_raw_fd(), &component)?;
                if current.st_mode & libc::S_IFMT != libc::S_IFREG
                    || current.st_dev as u64 != expected.device
                    || current.st_ino as u64 != expected.inode
                {
                    return Err(io::Error::other("named regular-file identity changed"));
                }
                Ok(())
            }

            pub(crate) fn require_named_directory_identity(
                &self,
                component: &OsStr,
                expected: Identity,
            ) -> io::Result<()> {
                let component = component_c_string(component)?;
                let current = stat_at(self.file.as_raw_fd(), &component)?;
                if current.st_mode & libc::S_IFMT != libc::S_IFDIR
                    || current.st_dev as u64 != expected.device
                    || current.st_ino as u64 != expected.inode
                {
                    return Err(io::Error::other("named directory identity changed"));
                }
                Ok(())
            }

            pub(crate) fn open_child(&self, component: &OsStr) -> io::Result<DirectoryChild> {
                let component_c = component_c_string(component)?;
                // Open once without O_DIRECTORY, then classify with fstat. This
                // avoids platform-specific ENOTDIR mapping and ensures the
                // bytes are later read from the same descriptor that was
                // classified. O_NONBLOCK prevents FIFO/device hangs.
                // SAFETY: parent and component are valid retained values.
                let descriptor = unsafe {
                    libc::openat(
                        self.file.as_raw_fd(),
                        component_c.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: descriptor is freshly returned and uniquely owned.
                let file = unsafe { File::from_raw_fd(descriptor) };
                let status = stat(file.as_raw_fd())?;
                if status.st_mode & libc::S_IFMT == libc::S_IFDIR {
                    let directory = Directory { file };
                    directory.require_directory()?;
                    Ok(DirectoryChild::Directory(directory))
                } else if status.st_mode & libc::S_IFMT == libc::S_IFREG {
                    Ok(DirectoryChild::Regular(file))
                } else {
                    drop(file);
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "child entry is neither a directory nor a regular file",
                    ))
                }
            }

            pub(crate) fn create_new_regular_file(&self, component: &OsStr) -> io::Result<File> {
                let component = component_c_string(component)?;
                // O_EXCL makes a pre-existing symlink or file a collision rather
                // than a followed target. The caller supplies a command-unique name.
                // SAFETY: the parent descriptor is live, `component` is validated,
                // and the variadic mode argument is present because O_CREAT is set.
                let descriptor = unsafe {
                    libc::openat(
                        self.file.as_raw_fd(),
                        component.as_ptr(),
                        libc::O_WRONLY
                            | libc::O_CLOEXEC
                            | libc::O_CREAT
                            | libc::O_EXCL
                            | libc::O_NOFOLLOW,
                        0o600,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: `descriptor` is newly returned by `openat` and uniquely owned.
                Ok(unsafe { File::from_raw_fd(descriptor) })
            }

            pub(crate) fn open_or_create_regular_file(
                &self,
                component: &OsStr,
            ) -> io::Result<File> {
                let component = component_c_string(component)?;
                // SAFETY: the retained parent descriptor and component are valid;
                // O_NOFOLLOW and the post-open fstat exclude links/non-files.
                let descriptor = unsafe {
                    libc::openat(
                        self.file.as_raw_fd(),
                        component.as_ptr(),
                        libc::O_RDWR
                            | libc::O_CLOEXEC
                            | libc::O_CREAT
                            | libc::O_NOFOLLOW
                            | libc::O_NONBLOCK,
                        0o600,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: descriptor is freshly returned and uniquely owned.
                let file = unsafe { File::from_raw_fd(descriptor) };
                if stat(file.as_raw_fd())?.st_mode & libc::S_IFMT != libc::S_IFREG {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "entry is not a regular file",
                    ));
                }
                Ok(file)
            }

            pub(crate) fn replace_file(
                &self,
                source: &OsStr,
                destination: &OsStr,
            ) -> io::Result<()> {
                let _ = component_c_string(source)?;
                let _ = component_c_string(destination)?;
                Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "existing-file replacement requires a typed exclusive namespace transaction",
                ))
            }

            /// Replace one file only for a caller that continuously holds and
            /// revalidates an exclusive cooperative namespace lock. Generic
            /// writers must use `replace_file`, which fails closed.
            pub(crate) fn replace_file_under_cooperative_lock(
                &self,
                source: &OsStr,
                destination: &OsStr,
            ) -> io::Result<()> {
                let source = component_c_string(source)?;
                let destination = component_c_string(destination)?;
                // SAFETY: names and retained parent descriptor are valid. The
                // caller's typed lock excludes cooperating writers for this
                // namespace; it is revalidated immediately around this call.
                if unsafe {
                    libc::renameat(
                        self.file.as_raw_fd(),
                        source.as_ptr(),
                        self.file.as_raw_fd(),
                        destination.as_ptr(),
                    )
                } != 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            }

            #[cfg_attr(not(test), allow(dead_code))]
            pub(crate) fn publish_file_no_replace(
                &self,
                source: &OsStr,
                destination: &OsStr,
            ) -> io::Result<()> {
                let source = component_c_string(source)?;
                let destination = component_c_string(destination)?;
                let source_status = stat_at(self.file.as_raw_fd(), &source)?;
                if source_status.st_mode & libc::S_IFMT != libc::S_IFREG {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "publication source is not a regular file",
                    ));
                }
                let source_identity = Identity {
                    device: source_status.st_dev as u64,
                    inode: source_status.st_ino as u64,
                };
                rename_no_replace(
                    self.file.as_raw_fd(),
                    &source,
                    self.file.as_raw_fd(),
                    &destination,
                )?;
                let destination_status = stat_at(self.file.as_raw_fd(), &destination)?;
                if destination_status.st_mode & libc::S_IFMT != libc::S_IFREG
                    || source_identity.device != destination_status.st_dev as u64
                    || source_identity.inode != destination_status.st_ino as u64
                {
                    return Err(io::Error::other(
                        "published file identity changed during no-replace publication",
                    ));
                }
                Ok(())
            }

            pub(crate) fn remove_file(&self, component: &OsStr) -> io::Result<()> {
                let _ = component_c_string(component)?;
                Err(identity_conditional_removal_unsupported())
            }

            /// Remove a direct regular-file child only when its current named
            /// identity still matches the descriptor inspected by the caller.
            pub(crate) fn remove_regular_file_if_identity(
                &self,
                component: &OsStr,
                expected: Identity,
            ) -> io::Result<()> {
                let _ = component_c_string(component)?;
                let _ = expected;
                Err(identity_conditional_removal_unsupported())
            }

            pub(crate) fn remove_empty_directory_if_identity(
                &self,
                component: &OsStr,
                expected: Identity,
            ) -> io::Result<()> {
                let _ = component_c_string(component)?;
                let _ = expected;
                Err(identity_conditional_removal_unsupported())
            }

            /// Remove a regular file inside a namespace whose caller-held
            /// cooperative lock excludes every permitted writer.
            ///
            /// This is deliberately separate from the generic identity API:
            /// identity inspection alone cannot make `unlinkat` conditional.
            /// Callers must revalidate their typed lock immediately before and
            /// after this operation.
            pub(crate) fn remove_regular_file_under_cooperative_lock(
                &self,
                component: &OsStr,
                expected: Identity,
            ) -> io::Result<()> {
                let component = component_c_string(component)?;
                let status = stat_at(self.file.as_raw_fd(), &component)?;
                if status.st_mode & libc::S_IFMT != libc::S_IFREG
                    || status.st_dev as u64 != expected.device
                    || status.st_ino as u64 != expected.inode
                {
                    return Err(io::Error::other(
                        "locked regular-file identity changed before removal",
                    ));
                }
                // SAFETY: the retained descriptor and validated component are
                // live. The caller's typed cooperative lock excludes a legal
                // replacement between the identity check and this syscall.
                if unsafe { libc::unlinkat(self.file.as_raw_fd(), component.as_ptr(), 0) } != 0 {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            }

            /// Remove an empty directory inside a caller-locked namespace.
            pub(crate) fn remove_empty_directory_under_cooperative_lock(
                &self,
                component: &OsStr,
                expected: Identity,
            ) -> io::Result<()> {
                let component = component_c_string(component)?;
                let status = stat_at(self.file.as_raw_fd(), &component)?;
                if status.st_mode & libc::S_IFMT != libc::S_IFDIR
                    || status.st_dev as u64 != expected.device
                    || status.st_ino as u64 != expected.inode
                {
                    return Err(io::Error::other(
                        "locked directory identity changed before removal",
                    ));
                }
                // SAFETY: see `remove_regular_file_under_cooperative_lock`;
                // AT_REMOVEDIR additionally requires the verified directory to
                // be empty at the syscall boundary.
                if unsafe {
                    libc::unlinkat(
                        self.file.as_raw_fd(),
                        component.as_ptr(),
                        libc::AT_REMOVEDIR,
                    )
                } != 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            }

            pub(crate) fn probe_writable(&self, component: &OsStr) -> io::Result<()> {
                let _ = component_c_string(component)?;
                let current = CString::new(".").expect("static path has no NUL");
                // This advisory permission check never exposes and later removes
                // a probe name. The actual O_EXCL write remains authoritative.
                if unsafe {
                    libc::faccessat(self.file.as_raw_fd(), current.as_ptr(), libc::W_OK, 0)
                } != 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            }

            pub(crate) fn identity(&self) -> io::Result<Identity> {
                let status = stat(self.file.as_raw_fd())?;
                Ok(Identity {
                    device: status.st_dev as u64,
                    inode: status.st_ino as u64,
                })
            }

            fn require_directory(&self) -> io::Result<()> {
                let status = stat(self.file.as_raw_fd())?;
                if status.st_mode & libc::S_IFMT == libc::S_IFDIR {
                    Ok(())
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::NotADirectory,
                        "cache path component is not a directory",
                    ))
                }
            }
        }

        fn component_c_string(component: &OsStr) -> io::Result<CString> {
            let path = Path::new(component);
            if component.is_empty()
                || path.components().count() != 1
                || matches!(component.as_bytes(), b"." | b"..")
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "expected one non-dot path component",
                ));
            }
            CString::new(component.as_bytes()).map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidInput, "path component contains NUL")
            })
        }

        fn identity_conditional_removal_unsupported() -> io::Error {
            io::Error::new(
                io::ErrorKind::Unsupported,
                "identity-conditional name removal is unavailable; residue was preserved",
            )
        }

        #[cfg(target_vendor = "apple")]
        fn rename_no_replace(
            source_parent: RawFd,
            source: &CString,
            destination_parent: RawFd,
            destination: &CString,
        ) -> io::Result<()> {
            // SAFETY: both retained descriptors and validated names are live.
            if unsafe {
                libc::renameatx_np(
                    source_parent,
                    source.as_ptr(),
                    destination_parent,
                    destination.as_ptr(),
                    libc::RENAME_EXCL,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        }

        #[cfg(any(target_os = "linux", target_os = "android"))]
        fn rename_no_replace(
            source_parent: RawFd,
            source: &CString,
            destination_parent: RawFd,
            destination: &CString,
        ) -> io::Result<()> {
            // SAFETY: both retained descriptors and validated names are live.
            if unsafe {
                libc::syscall(
                    libc::SYS_renameat2,
                    source_parent,
                    source.as_ptr(),
                    destination_parent,
                    destination.as_ptr(),
                    libc::RENAME_NOREPLACE,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        }

        #[cfg(all(
            unix,
            not(any(target_vendor = "apple", target_os = "linux", target_os = "android"))
        ))]
        fn rename_no_replace(
            _source_parent: RawFd,
            _source: &CString,
            _destination_parent: RawFd,
            _destination: &CString,
        ) -> io::Result<()> {
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "atomic no-replace file publication is unavailable",
            ))
        }

        fn open_directory_at(parent: libc::c_int, component: &CString) -> io::Result<libc::c_int> {
            // SAFETY: `parent` is live and `component` is a valid NUL-terminated name.
            let descriptor = unsafe {
                libc::openat(
                    parent,
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            };
            if descriptor < 0 {
                Err(io::Error::last_os_error())
            } else {
                Ok(descriptor)
            }
        }

        fn stat(descriptor: libc::c_int) -> io::Result<libc::stat> {
            let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
            // SAFETY: `status` points to writable storage and `descriptor` is live.
            if unsafe { libc::fstat(descriptor, status.as_mut_ptr()) } != 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: successful `fstat` initialized the complete value.
            Ok(unsafe { status.assume_init() })
        }

        fn stat_at(parent: libc::c_int, component: &CString) -> io::Result<libc::stat> {
            let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
            // SAFETY: `status` is writable, `parent` is live, and the component
            // is NUL-terminated. `AT_SYMLINK_NOFOLLOW` observes the named entry.
            if unsafe {
                libc::fstatat(
                    parent,
                    component.as_ptr(),
                    status.as_mut_ptr(),
                    libc::AT_SYMLINK_NOFOLLOW,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: successful `fstatat` initialized the complete value.
            Ok(unsafe { status.assume_init() })
        }

        fn directory_entry_names(descriptor: libc::c_int) -> io::Result<Vec<OsString>> {
            // `dup` would share the directory stream offset with the retained
            // capability. Reopen `.` relative to it so every enumeration owns
            // an independent open-file description and repeated catalogs are
            // complete.
            // SAFETY: `descriptor` is a live directory and the literal is NUL-terminated.
            let duplicate = unsafe {
                libc::openat(
                    descriptor,
                    c".".as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            };
            if duplicate < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: ownership of `duplicate` transfers to the DIR stream.
            let stream = unsafe { libc::fdopendir(duplicate) };
            if stream.is_null() {
                let error = io::Error::last_os_error();
                // SAFETY: fdopendir failed and did not take ownership.
                unsafe { libc::close(duplicate) };
                return Err(error);
            }
            let mut names = Vec::new();
            loop {
                // SAFETY: `stream` remains live until `closedir` below.
                let entry = unsafe { libc::readdir(stream) };
                if entry.is_null() {
                    break;
                }
                // SAFETY: `d_name` is NUL-terminated within the live dirent.
                let bytes =
                    unsafe { std::ffi::CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
                if matches!(bytes, b"." | b"..") {
                    continue;
                }
                names.push(OsString::from_vec(bytes.to_vec()));
            }
            // SAFETY: `stream` is live and owns the duplicated fd.
            if unsafe { libc::closedir(stream) } != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(names)
        }
    }

    #[cfg(not(unix))]
    impl Directory {
        pub(crate) fn try_clone(&self) -> io::Result<Self> {
            Err(unsupported())
        }

        pub(crate) fn sync_all(&self) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn open_filesystem_root() -> io::Result<Self> {
            Err(unsupported())
        }

        pub(crate) fn open_current_directory() -> io::Result<Self> {
            Err(unsupported())
        }

        pub(crate) fn open_parent_directory(&self) -> io::Result<Self> {
            Err(unsupported())
        }

        pub(crate) fn open_or_create_directory(
            &self,
            _component: &OsStr,
            _create: bool,
        ) -> io::Result<Self> {
            Err(unsupported())
        }

        pub(crate) fn open_regular_file(&self, _component: &OsStr) -> io::Result<Option<File>> {
            Err(unsupported())
        }

        pub(crate) fn entry_kind(&self, _component: &OsStr) -> io::Result<Option<EntryKind>> {
            Err(unsupported())
        }

        pub(crate) fn require_named_regular_file_identity(
            &self,
            _component: &OsStr,
            _expected: Identity,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn require_named_directory_identity(
            &self,
            _component: &OsStr,
            _expected: Identity,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn open_child(&self, _component: &OsStr) -> io::Result<DirectoryChild> {
            Err(unsupported())
        }

        pub(crate) fn create_new_directory(&self, _component: &OsStr) -> io::Result<Self> {
            Err(unsupported())
        }

        pub(crate) fn rename_entry(&self, _source: &OsStr, _destination: &OsStr) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn entry_names(&self) -> io::Result<Vec<OsString>> {
            Err(unsupported())
        }

        pub(crate) fn read_symbolic_link(&self, _component: &OsStr) -> io::Result<OsString> {
            Err(unsupported())
        }

        pub(crate) fn create_symbolic_link(
            &self,
            _target: &OsStr,
            _component: &OsStr,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn create_new_regular_file(&self, _component: &OsStr) -> io::Result<File> {
            Err(unsupported())
        }

        pub(crate) fn open_or_create_regular_file(&self, _component: &OsStr) -> io::Result<File> {
            Err(unsupported())
        }

        pub(crate) fn replace_file(&self, _source: &OsStr, _destination: &OsStr) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn replace_file_under_cooperative_lock(
            &self,
            _source: &OsStr,
            _destination: &OsStr,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        #[cfg_attr(not(test), allow(dead_code))]
        pub(crate) fn publish_file_no_replace(
            &self,
            _source: &OsStr,
            _destination: &OsStr,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn remove_file(&self, _component: &OsStr) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn remove_regular_file_if_identity(
            &self,
            _component: &OsStr,
            _expected: Identity,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn remove_empty_directory_if_identity(
            &self,
            _component: &OsStr,
            _expected: Identity,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn remove_regular_file_under_cooperative_lock(
            &self,
            _component: &OsStr,
            _expected: Identity,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn remove_empty_directory_under_cooperative_lock(
            &self,
            _component: &OsStr,
            _expected: Identity,
        ) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn probe_writable(&self, _component: &OsStr) -> io::Result<()> {
            Err(unsupported())
        }

        pub(crate) fn identity(&self) -> io::Result<Identity> {
            Err(unsupported())
        }
    }

    #[cfg(not(unix))]
    fn unsupported() -> io::Error {
        io::Error::new(
            io::ErrorKind::Unsupported,
            "directory-relative no-follow cache access is unavailable",
        )
    }
}

/// Render a package root without exposing host-local absolute paths.
pub fn render_package_root(root: &Path) -> String {
    if root.as_os_str().is_empty() {
        ".".to_owned()
    } else if root.is_absolute() {
        "<absolute-root>".to_owned()
    } else {
        normalize_path_separators(&root.to_string_lossy())
    }
}

/// Join a validated package-relative path to a package root.
pub fn join_package_path(
    root: &Path,
    package_path: &PackagePath,
    manifest_field_path: impl Into<String>,
) -> Result<PathBuf, Box<CommandDiagnostic>> {
    validate_package_path(package_path, manifest_field_path.into())
        .map_err(|error| Box::new(CommandDiagnostic::from_package_manifest_error(&error)))?;
    Ok(root.join(package_path.as_str()))
}

/// Validate an explicit package output path against its selected package root.
pub(crate) fn validate_package_output_path(
    root: &Path,
    package_path: &PackagePath,
    field: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    validate_package_path(package_path, field)
        .map_err(|error| Box::new(CommandDiagnostic::from_package_manifest_error(&error)))?;

    let current_dir = if root.is_relative() {
        Some(
            std::env::current_dir()
                .map_err(|_| Box::new(package_output_root_resolution_diagnostic()))?,
        )
    } else {
        None
    };
    let marker = package_root_marker(root, current_dir.as_deref())
        .map_err(|_| Box::new(package_output_root_resolution_diagnostic()))?;
    let Some(marker) = marker else {
        return Ok(());
    };

    if package_output_path_repeats_root(package_path, &marker) {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Usage, "package_output_path_repeats_root")
                .with_path(render_package_path(package_path))
                .with_field(field)
                .with_expected_value("path relative to --root without the package-root directory")
                .with_actual_value("root-qualified path"),
        ));
    }

    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PackageRootMarkerError {
    CurrentDirectoryRequired,
}

fn package_root_marker(
    root: &Path,
    current_dir: Option<&Path>,
) -> Result<Option<OsString>, PackageRootMarkerError> {
    let resolved = if root.is_relative() {
        let current_dir = current_dir.ok_or(PackageRootMarkerError::CurrentDirectoryRequired)?;
        current_dir.join(root)
    } else {
        root.to_path_buf()
    };
    let mut normal_components = Vec::new();
    for component in resolved.components() {
        match component {
            Component::Prefix(_) | Component::RootDir => normal_components.clear(),
            Component::CurDir => {}
            Component::ParentDir => {
                normal_components.pop();
            }
            Component::Normal(component) => normal_components.push(component.to_os_string()),
        }
    }
    Ok(normal_components.pop())
}

fn package_output_path_repeats_root(package_path: &PackagePath, marker: &OsStr) -> bool {
    Path::new(package_path.as_str())
        .components()
        .any(|component| matches!(component, Component::Normal(value) if value == marker))
}

fn package_output_root_resolution_diagnostic() -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::ArtifactIo,
        "package_output_root_resolution_failed",
    )
    .with_field("--root")
}

/// Return a deterministic package-relative path display string.
pub fn render_package_path(path: &PackagePath) -> String {
    path.as_str().to_owned()
}

fn normalize_path_separators(path: &str) -> String {
    path.replace('\\', "/")
}

/// Build a deterministic artifact IO diagnostic.
pub fn artifact_io_error(
    reason_code: impl Into<String>,
    package_path: impl Into<String>,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason_code).with_path(package_path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(any(target_vendor = "apple", target_os = "linux", target_os = "android"))]
    #[test]
    fn no_replace_publication_is_atomic_and_preserves_collisions() {
        let root = std::env::temp_dir().join(format!(
            "npa-cli-no-replace-publication-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir(&root).unwrap();
        let bound = no_follow_directory::open_bound_directory(&root).unwrap();
        let directory = bound.root_clone().unwrap();

        std::fs::write(root.join("source"), b"new").unwrap();
        directory
            .publish_file_no_replace(OsStr::new("source"), OsStr::new("destination"))
            .unwrap();
        assert!(!root.join("source").exists());
        assert_eq!(std::fs::read(root.join("destination")).unwrap(), b"new");

        std::fs::write(root.join("collision-source"), b"source").unwrap();
        std::fs::write(root.join("collision-destination"), b"destination").unwrap();
        assert!(directory
            .publish_file_no_replace(
                OsStr::new("collision-source"),
                OsStr::new("collision-destination")
            )
            .is_err());
        assert_eq!(
            std::fs::read(root.join("collision-source")).unwrap(),
            b"source"
        );
        assert_eq!(
            std::fs::read(root.join("collision-destination")).unwrap(),
            b"destination"
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn generic_replacement_and_removal_fail_without_mutating_names() {
        let root =
            std::env::temp_dir().join(format!("npa-cli-preserved-removal-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir(&root).unwrap();
        std::fs::write(root.join("source"), b"source").unwrap();
        std::fs::write(root.join("destination"), b"destination").unwrap();
        let bound = no_follow_directory::open_bound_directory(&root).unwrap();
        let directory = bound.root_clone().unwrap();
        let destination = directory
            .open_regular_file(OsStr::new("destination"))
            .unwrap()
            .unwrap();
        let identity = no_follow_directory::regular_file_identity(&destination).unwrap();
        drop(destination);

        let replace_error = directory
            .replace_file(OsStr::new("source"), OsStr::new("destination"))
            .unwrap_err();
        assert_eq!(replace_error.kind(), std::io::ErrorKind::Unsupported);
        let remove_error = directory
            .remove_regular_file_if_identity(OsStr::new("destination"), identity)
            .unwrap_err();
        assert_eq!(remove_error.kind(), std::io::ErrorKind::Unsupported);
        assert_eq!(std::fs::read(root.join("source")).unwrap(), b"source");
        assert_eq!(
            std::fs::read(root.join("destination")).unwrap(),
            b"destination"
        );

        directory
            .probe_writable(OsStr::new("must-not-appear"))
            .unwrap();
        assert!(!root.join("must-not-appear").exists());

        std::fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn selected_directory_open_accepts_parent_relative_paths() {
        let current = std::env::current_dir().unwrap();
        let current_name = current.file_name().unwrap();
        let selected = PathBuf::from("..").join(current_name);

        let reopened = no_follow_directory::open_absolute_directory(&selected, false).unwrap();
        let retained = no_follow_directory::Directory::open_current_directory().unwrap();

        assert_eq!(reopened.identity().unwrap(), retained.identity().unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn bounded_regular_reader_rejects_links_and_growth() {
        use std::os::unix::fs::symlink;

        let root =
            std::env::temp_dir().join(format!("npa-cli-bounded-reader-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("real")).unwrap();
        std::fs::write(root.join("real/value"), b"value").unwrap();
        assert_eq!(
            read_bounded_regular_file(&root.join("real/value"), 5).unwrap(),
            b"value"
        );
        assert!(read_bounded_regular_file(&root.join("real/value"), 4).is_err());
        symlink(root.join("real"), root.join("linked")).unwrap();
        assert!(read_bounded_regular_file(&root.join("linked/value"), 5).is_err());

        std::fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn bounded_read_root_is_relative_bounded_and_retains_the_opened_root() {
        use std::os::unix::fs::symlink;

        let base = std::env::temp_dir().join(format!(
            "npa-cli-bounded-root-reader-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&base);
        let root = base.join("root");
        let replacement = base.join("replacement");
        let relocated = base.join("relocated");
        std::fs::create_dir_all(root.join("nested")).unwrap();
        std::fs::write(root.join("nested/value"), b"original").unwrap();
        std::fs::create_dir_all(replacement.join("nested")).unwrap();
        std::fs::write(replacement.join("nested/value"), b"replacement").unwrap();
        let reader = BoundedReadRoot::open(&root).unwrap();
        assert_eq!(
            reader.read(Path::new("nested/value"), 8).unwrap(),
            b"original"
        );
        assert!(reader.read(Path::new("nested/value"), 7).is_err());
        for invalid in ["", "../value", "nested/../value", "/absolute"] {
            assert!(reader.read(Path::new(invalid), 8).is_err(), "{invalid}");
        }

        let swap_root = root.clone();
        let swap_relocated = relocated.clone();
        let swap_replacement = replacement.clone();
        assert!(reader
            .read_with_hook(Path::new("nested/value"), 8, move || {
                std::fs::rename(&swap_root, &swap_relocated).unwrap();
                std::fs::rename(&swap_replacement, &swap_root).unwrap();
            })
            .is_err());
        assert_eq!(
            std::fs::read(relocated.join("nested/value")).unwrap(),
            b"original"
        );
        assert_eq!(
            std::fs::read(root.join("nested/value")).unwrap(),
            b"replacement"
        );

        std::fs::rename(&root, &replacement).unwrap();
        std::fs::rename(&relocated, &root).unwrap();
        std::fs::rename(&root, &relocated).unwrap();
        std::fs::rename(&replacement, &root).unwrap();
        assert!(reader.read(Path::new("nested/value"), 8).is_err());
        assert_eq!(
            std::fs::read(relocated.join("nested/value")).unwrap(),
            b"original"
        );
        assert_eq!(
            std::fs::read(root.join("nested/value")).unwrap(),
            b"replacement"
        );

        let link_root = base.join("link-root");
        symlink(&relocated, &link_root).unwrap();
        assert!(BoundedReadRoot::open(&link_root).is_err());
        std::fs::remove_file(link_root).unwrap();
        std::fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn package_root_marker_resolves_absolute_relative_and_current_directory_roots() {
        let current_dir = std::env::temp_dir()
            .join("npa-cli-package-output-path-tests")
            .join("workspace")
            .join("proofs");
        let absolute = current_dir.join("nested").join("package");

        assert_eq!(
            package_root_marker(&absolute, None).unwrap(),
            Some(OsString::from("package"))
        );
        assert_eq!(
            package_root_marker(Path::new("nested/proofs"), Some(&current_dir)).unwrap(),
            Some(OsString::from("proofs"))
        );
        assert_eq!(
            package_root_marker(Path::new("."), Some(&current_dir)).unwrap(),
            Some(OsString::from("proofs"))
        );
        assert_eq!(
            package_root_marker(Path::new("temporary/.."), Some(&current_dir)).unwrap(),
            Some(OsString::from("proofs"))
        );
        assert_eq!(
            package_root_marker(Path::new("proofs"), None),
            Err(PackageRootMarkerError::CurrentDirectoryRequired)
        );
    }

    #[test]
    fn package_root_marker_returns_none_for_a_filesystem_root() {
        let root = std::env::temp_dir();
        let filesystem_root = root.ancestors().last().unwrap();

        assert_eq!(package_root_marker(filesystem_root, None).unwrap(), None);
    }

    #[test]
    fn package_output_path_classification_uses_exact_components() {
        let cases = [
            ("generated/candidate.metadata.json", "proofs", false),
            ("target/candidates/candidate.metadata.json", "proofs", false),
            ("proofs/generated/candidate.metadata.json", "proofs", true),
            (
                "npa-project-example/proofs/generated/candidate.metadata.json",
                "proofs",
                true,
            ),
            (
                "workspace/run/proofs/generated/candidate.metadata.json",
                "proofs",
                true,
            ),
            ("generated/proofs.json", "proofs", false),
            ("generated/proofs-data/candidate.json", "proofs", false),
            ("generated/candidate.json", "generated", true),
            ("target/candidates/candidate.json", "target", true),
        ];

        for (path, marker, expected) in cases {
            assert_eq!(
                package_output_path_repeats_root(&PackagePath::new(path), OsStr::new(marker)),
                expected,
                "{path} with marker {marker}"
            );
        }
    }

    #[test]
    fn package_output_path_validation_preserves_lexical_failures() {
        let root = std::env::temp_dir().join("proofs");
        for path in [
            "",
            "/absolute.json",
            ".",
            "..",
            "generated//output.json",
            "generated/../output.json",
            "https://example.invalid/output.json",
            "generated\\output.json",
        ] {
            let diagnostic =
                validate_package_output_path(&root, &PackagePath::new(path), "--out").unwrap_err();
            assert_eq!(diagnostic.kind, DiagnosticKind::PackageManifest, "{path}");
            assert_eq!(diagnostic.reason_code, "invalid_path", "{path}");
            assert_eq!(diagnostic.path.as_deref(), Some("--out"), "{path}");
            assert_eq!(diagnostic.actual_value.as_deref(), Some(path), "{path}");
        }
    }

    #[test]
    fn package_output_path_validation_returns_the_stable_repeated_root_diagnostic() {
        let root = std::env::temp_dir().join("proofs");
        let path = PackagePath::new("workspace/proofs/generated/output.json");

        let diagnostic = validate_package_output_path(&root, &path, "--out").unwrap_err();

        assert_eq!(diagnostic.kind, DiagnosticKind::Usage);
        assert_eq!(diagnostic.reason_code, "package_output_path_repeats_root");
        assert_eq!(diagnostic.path.as_deref(), Some(path.as_str()));
        assert_eq!(diagnostic.field.as_deref(), Some("--out"));
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some("path relative to --root without the package-root directory")
        );
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some("root-qualified path")
        );
    }

    #[test]
    fn package_output_root_resolution_diagnostic_is_sanitized() {
        let diagnostic = package_output_root_resolution_diagnostic();

        assert_eq!(diagnostic.kind, DiagnosticKind::ArtifactIo);
        assert_eq!(
            diagnostic.reason_code,
            "package_output_root_resolution_failed"
        );
        assert_eq!(diagnostic.field.as_deref(), Some("--root"));
        assert_eq!(diagnostic.path, None);
        assert_eq!(diagnostic.expected_value, None);
        assert_eq!(diagnostic.actual_value, None);
    }
}
