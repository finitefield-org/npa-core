use std::ffi::OsStr;
use std::path::{Component, Path};

fn has_ascii_suffix(value: &OsStr, suffix: &[u8]) -> bool {
    value.as_encoded_bytes().ends_with(suffix)
}

pub fn is_source_or_replay_path(path: &Path) -> bool {
    path.components().any(|component| match component {
        Component::Normal(value) => {
            value == OsStr::new("replay.json") || has_ascii_suffix(value, b".npa")
        }
        _ => false,
    })
}

pub fn is_certificate_path(path: &Path) -> bool {
    path.file_name()
        .is_some_and(|value| has_ascii_suffix(value, b".npcert"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceFreeFsError {
    Unavailable,
    Symlink,
    ResourceLimit {
        kind: ResourceLimitKind,
        offset: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceLimitKind {
    DirectoryDepth,
    DirectoryEntries,
    CandidateCount,
    CandidateBytes,
}

pub struct CollectedFile {
    pub bytes: Vec<u8>,
}

// The differential runners are shipped for Linux/Android and Apple hosts. On
// other platforms the public wrappers below fail closed rather than emulating
// descriptor-anchored traversal with path-based filesystem APIs.
#[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
mod unix {
    use super::{CollectedFile, ResourceLimitKind, SourceFreeFsError};
    use std::ffi::{CStr, CString, OsStr, OsString};
    use std::fs::File;
    use std::io::Read;
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
    use std::os::unix::ffi::{OsStrExt, OsStringExt};
    use std::path::{Component, Path};

    fn io_error() -> SourceFreeFsError {
        match std::io::Error::last_os_error().raw_os_error() {
            Some(libc::ELOOP) => SourceFreeFsError::Symlink,
            _ => SourceFreeFsError::Unavailable,
        }
    }

    fn c_string(value: &OsStr) -> Result<CString, SourceFreeFsError> {
        CString::new(value.as_bytes()).map_err(|_| SourceFreeFsError::Unavailable)
    }

    fn stat_at(parent: RawFd, name: &OsStr) -> Result<libc::stat, SourceFreeFsError> {
        let name = c_string(name)?;
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        let status = unsafe {
            libc::fstatat(
                parent,
                name.as_ptr(),
                stat.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        };
        if status != 0 {
            return Err(io_error());
        }
        let stat = unsafe { stat.assume_init() };
        if stat.st_mode & libc::S_IFMT == libc::S_IFLNK {
            Err(SourceFreeFsError::Symlink)
        } else {
            Ok(stat)
        }
    }

    #[derive(Clone, Copy)]
    enum OpenKind {
        Directory,
        Regular,
    }

    fn is_directory(stat: &libc::stat) -> bool {
        stat.st_mode & libc::S_IFMT == libc::S_IFDIR
    }

    fn is_regular(stat: &libc::stat) -> bool {
        stat.st_mode & libc::S_IFMT == libc::S_IFREG
    }

    fn accepts_kind(stat: &libc::stat, kind: OpenKind) -> bool {
        match kind {
            OpenKind::Directory => is_directory(stat),
            OpenKind::Regular => is_regular(stat),
        }
    }

    fn open_at(parent: RawFd, name: &OsStr, kind: OpenKind) -> Result<OwnedFd, SourceFreeFsError> {
        let stat = stat_at(parent, name)?;
        if !accepts_kind(&stat, kind) {
            return Err(SourceFreeFsError::Unavailable);
        }
        let name = c_string(name)?;
        let mut flags = libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK;
        if matches!(kind, OpenKind::Directory) {
            flags |= libc::O_DIRECTORY;
        }
        let fd = unsafe { libc::openat(parent, name.as_ptr(), flags) };
        if fd < 0 {
            Err(io_error())
        } else {
            let fd = unsafe { OwnedFd::from_raw_fd(fd) };
            let opened_stat = fstat(fd.as_raw_fd())?;
            if accepts_kind(&opened_stat, kind) {
                Ok(fd)
            } else {
                Err(SourceFreeFsError::Unavailable)
            }
        }
    }

    fn open_anchor(absolute: bool) -> Result<OwnedFd, SourceFreeFsError> {
        let name = if absolute { c"/" } else { c"." };
        let fd = unsafe {
            libc::open(
                name.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY,
            )
        };
        if fd < 0 {
            Err(io_error())
        } else {
            Ok(unsafe { OwnedFd::from_raw_fd(fd) })
        }
    }

    fn open_path(path: &Path, expect_directory: bool) -> Result<OwnedFd, SourceFreeFsError> {
        if path.as_os_str().is_empty() {
            return Err(SourceFreeFsError::Unavailable);
        }
        let components = path.components().collect::<Vec<_>>();
        let named = components
            .iter()
            .filter(|component| matches!(component, Component::Normal(_) | Component::ParentDir))
            .count();
        let mut remaining_named = named;
        let mut current = open_anchor(path.is_absolute())?;
        for component in components {
            let name = match component {
                Component::RootDir | Component::CurDir => continue,
                Component::ParentDir => OsStr::new(".."),
                Component::Normal(name) => name,
                Component::Prefix(_) => return Err(SourceFreeFsError::Unavailable),
            };
            remaining_named -= 1;
            let kind = if remaining_named != 0 || expect_directory {
                OpenKind::Directory
            } else {
                OpenKind::Regular
            };
            current = open_at(current.as_raw_fd(), name, kind)?;
        }
        Ok(current)
    }

    fn fstat(fd: RawFd) -> Result<libc::stat, SourceFreeFsError> {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        let status = unsafe { libc::fstat(fd, stat.as_mut_ptr()) };
        if status != 0 {
            Err(io_error())
        } else {
            Ok(unsafe { stat.assume_init() })
        }
    }

    fn has_extension(path: &Path, extension: &OsStr) -> bool {
        let Some(file_name) = path.file_name() else {
            return false;
        };
        let name = file_name.as_bytes();
        let extension = extension.as_bytes();
        !extension.is_empty()
            && name.len() > extension.len()
            && name[name.len() - extension.len() - 1] == b'.'
            && name.ends_with(extension)
    }

    fn read_file(fd: OwnedFd, limit: usize) -> Result<Vec<u8>, SourceFreeFsError> {
        let stat = fstat(fd.as_raw_fd())?;
        if !is_regular(&stat) {
            return Err(SourceFreeFsError::Unavailable);
        }
        let size = u64::try_from(stat.st_size).map_err(|_| SourceFreeFsError::Unavailable)?;
        if size > limit as u64 {
            return Err(SourceFreeFsError::ResourceLimit {
                kind: ResourceLimitKind::CandidateBytes,
                offset: limit,
            });
        }
        let capacity = usize::try_from(size).unwrap_or(limit).min(limit);
        let mut bytes = Vec::with_capacity(capacity);
        File::from(fd)
            .take(limit as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| SourceFreeFsError::Unavailable)?;
        if bytes.len() > limit {
            Err(SourceFreeFsError::ResourceLimit {
                kind: ResourceLimitKind::CandidateBytes,
                offset: limit,
            })
        } else {
            Ok(bytes)
        }
    }

    struct Directory(*mut libc::DIR);

    impl Drop for Directory {
        fn drop(&mut self) {
            unsafe {
                libc::closedir(self.0);
            }
        }
    }

    #[cfg(target_os = "linux")]
    fn set_errno(value: libc::c_int) {
        unsafe {
            *libc::__errno_location() = value;
        }
    }

    #[cfg(target_os = "linux")]
    fn errno_value() -> libc::c_int {
        unsafe { *libc::__errno_location() }
    }

    #[cfg(target_os = "android")]
    fn set_errno(value: libc::c_int) {
        unsafe {
            *libc::__errno() = value;
        }
    }

    #[cfg(target_os = "android")]
    fn errno_value() -> libc::c_int {
        unsafe { *libc::__errno() }
    }

    #[cfg(target_vendor = "apple")]
    fn set_errno(value: libc::c_int) {
        unsafe {
            *libc::__error() = value;
        }
    }

    #[cfg(target_vendor = "apple")]
    fn errno_value() -> libc::c_int {
        unsafe { *libc::__error() }
    }

    fn directory_names(
        fd: RawFd,
        remaining_entries: usize,
    ) -> Result<Vec<OsString>, SourceFreeFsError> {
        let duplicate = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 0) };
        if duplicate < 0 {
            return Err(io_error());
        }
        let directory = unsafe { libc::fdopendir(duplicate) };
        if directory.is_null() {
            unsafe {
                libc::close(duplicate);
            }
            return Err(io_error());
        }
        let directory = Directory(directory);
        let mut names = Vec::new();
        loop {
            set_errno(0);
            let entry = unsafe { libc::readdir(directory.0) };
            if entry.is_null() {
                if errno_value() != 0 {
                    return Err(SourceFreeFsError::Unavailable);
                }
                break;
            }
            let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
            if name == b"." || name == b".." {
                continue;
            }
            names.push(OsString::from_vec(name.to_vec()));
            if names.len() > remaining_entries {
                return Err(SourceFreeFsError::ResourceLimit {
                    kind: ResourceLimitKind::DirectoryEntries,
                    offset: 0,
                });
            }
        }
        names.sort();
        Ok(names)
    }

    struct CollectionState {
        visited_entries: usize,
        candidate_count: usize,
        total_bytes: usize,
        files: Vec<CollectedFile>,
    }

    struct CollectionLimits {
        max_depth: usize,
        max_entries: usize,
        max_candidates: usize,
        max_bytes: usize,
    }

    fn collect_directory(
        directory: &OwnedFd,
        path: &Path,
        depth: usize,
        extension: &OsStr,
        skip: &impl Fn(&Path) -> bool,
        limits: &CollectionLimits,
        state: &mut CollectionState,
    ) -> Result<(), SourceFreeFsError> {
        if depth > limits.max_depth {
            return Err(SourceFreeFsError::ResourceLimit {
                kind: ResourceLimitKind::DirectoryDepth,
                offset: 0,
            });
        }
        let remaining_entries = limits
            .max_entries
            .checked_sub(state.visited_entries)
            .ok_or(SourceFreeFsError::ResourceLimit {
                kind: ResourceLimitKind::DirectoryEntries,
                offset: 0,
            })?;
        let names = directory_names(directory.as_raw_fd(), remaining_entries)?;
        state.visited_entries += names.len();
        for name in names {
            let child_path = path.join(&name);
            if skip(&child_path) {
                continue;
            }
            let stat = match stat_at(directory.as_raw_fd(), &name) {
                Ok(stat) => stat,
                Err(SourceFreeFsError::Symlink) => continue,
                Err(error) => return Err(error),
            };
            if is_directory(&stat) {
                let child = open_at(directory.as_raw_fd(), &name, OpenKind::Directory)?;
                collect_directory(
                    &child,
                    &child_path,
                    depth + 1,
                    extension,
                    skip,
                    limits,
                    state,
                )?;
            } else if is_regular(&stat) && has_extension(&child_path, extension) {
                if state.candidate_count >= limits.max_candidates {
                    return Err(SourceFreeFsError::ResourceLimit {
                        kind: ResourceLimitKind::CandidateCount,
                        offset: 0,
                    });
                }
                state.candidate_count += 1;
                let remaining_bytes = limits.max_bytes.checked_sub(state.total_bytes).ok_or(
                    SourceFreeFsError::ResourceLimit {
                        kind: ResourceLimitKind::CandidateBytes,
                        offset: 0,
                    },
                )?;
                let child = open_at(directory.as_raw_fd(), &name, OpenKind::Regular)?;
                let bytes = read_file(child, remaining_bytes)?;
                state.total_bytes = state.total_bytes.checked_add(bytes.len()).ok_or(
                    SourceFreeFsError::ResourceLimit {
                        kind: ResourceLimitKind::CandidateBytes,
                        offset: remaining_bytes,
                    },
                )?;
                state.files.push(CollectedFile { bytes });
            }
        }
        Ok(())
    }

    pub fn read_bounded_file(path: &Path, limit: usize) -> Result<Vec<u8>, SourceFreeFsError> {
        let fd = open_path(path, false)?;
        read_file(fd, limit)
    }

    pub fn collect_bounded_files(
        root: &Path,
        extension: &OsStr,
        max_depth: usize,
        max_entries: usize,
        max_candidates: usize,
        max_bytes: usize,
        skip: &impl Fn(&Path) -> bool,
    ) -> Result<Vec<CollectedFile>, SourceFreeFsError> {
        let root_fd = open_path(root, true)?;
        let limits = CollectionLimits {
            max_depth,
            max_entries,
            max_candidates,
            max_bytes,
        };
        let mut state = CollectionState {
            visited_entries: 0,
            candidate_count: 0,
            total_bytes: 0,
            files: Vec::new(),
        };
        collect_directory(&root_fd, root, 1, extension, skip, &limits, &mut state)?;
        Ok(state.files)
    }
}

#[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
pub fn read_bounded_file(path: &Path, limit: usize) -> Result<Vec<u8>, SourceFreeFsError> {
    unix::read_bounded_file(path, limit)
}

#[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
pub fn collect_bounded_files(
    root: &Path,
    extension: &std::ffi::OsStr,
    max_depth: usize,
    max_entries: usize,
    max_candidates: usize,
    max_bytes: usize,
    skip: &impl Fn(&Path) -> bool,
) -> Result<Vec<CollectedFile>, SourceFreeFsError> {
    unix::collect_bounded_files(
        root,
        extension,
        max_depth,
        max_entries,
        max_candidates,
        max_bytes,
        skip,
    )
}

#[cfg(not(any(target_os = "linux", target_os = "android", target_vendor = "apple")))]
pub fn read_bounded_file(_path: &Path, _limit: usize) -> Result<Vec<u8>, SourceFreeFsError> {
    Err(SourceFreeFsError::Unavailable)
}

#[cfg(not(any(target_os = "linux", target_os = "android", target_vendor = "apple")))]
pub fn collect_bounded_files(
    _root: &Path,
    _extension: &std::ffi::OsStr,
    _max_depth: usize,
    _max_entries: usize,
    _max_candidates: usize,
    _max_bytes: usize,
    _skip: &impl Fn(&Path) -> bool,
) -> Result<Vec<CollectedFile>, SourceFreeFsError> {
    Err(SourceFreeFsError::Unavailable)
}
