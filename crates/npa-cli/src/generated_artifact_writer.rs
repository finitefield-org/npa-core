//! Package-confined descriptor-relative atomic generated-artifact I/O.

use std::{
    ffi::OsString,
    io::{self, Read, Write},
    path::{Component, Path},
    sync::atomic::{AtomicUsize, Ordering},
};

use npa_package::PackagePath;

use crate::fs::no_follow_directory::{
    open_absolute_directory, regular_file_identity, require_named_regular_file_identity, Directory,
    Identity,
};
use crate::package_promotion_transaction::TargetLock;

static NEXT_GENERATED_ARTIFACT_TEMP: AtomicUsize = AtomicUsize::new(0);
const MAX_PACKAGE_REGULAR_FILE_BYTES: u64 = 134_217_728;

#[cfg(test)]
thread_local! {
    static IDEMPOTENT_REOPEN_TEST_HOOK: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        std::cell::RefCell::new(None);
}

#[cfg(test)]
fn run_idempotent_reopen_test_hook() {
    IDEMPOTENT_REOPEN_TEST_HOOK.with(|hook| {
        if let Some(hook) = hook.borrow_mut().take() {
            hook();
        }
    });
}

#[cfg(not(test))]
fn run_idempotent_reopen_test_hook() {}

/// Atomically write one artifact below a package's real `generated` directory.
///
/// Every directory component is opened with `O_NOFOLLOW` relative to a retained
/// descriptor. The temporary and destination are both create-new; existing
/// different bytes are never replaced. Identical existing bytes are left
/// untouched.
pub fn write_package_generated_artifact_atomic(
    root: &Path,
    package_path: &PackagePath,
    bytes: &[u8],
) -> io::Result<()> {
    require_package_regular_file_size(bytes.len())?;
    let (parents, leaf) = validated_generated_components(package_path)?;
    let root = open_absolute_directory(root, false)?;
    let parent = open_components(root, &parents, true)?;
    write_to_directory(&parent, &leaf, bytes, 0o600)
}

/// Atomically create or confirm one arbitrary validated package-relative file.
///
/// This is the package-path counterpart of the generated-only writer above.
/// It retains every parent descriptor, creates missing parents mode 0700, and
/// never replaces an existing entry with different bytes.
pub(crate) fn write_package_regular_artifact_atomic(
    root: &Path,
    package_path: &PackagePath,
    bytes: &[u8],
) -> io::Result<()> {
    require_package_regular_file_size(bytes.len())?;
    let (parent, leaf) = open_package_parent_no_follow(root, package_path, true)?;
    write_to_directory(&parent, &leaf, bytes, 0o600)
}

/// Replace or create one generated artifact only while the caller retains the
/// package root's typed exclusive mutation lock. Generic writers deliberately
/// remain create-only so a byte comparison cannot be mistaken for a CAS.
pub(crate) fn write_package_generated_artifact_under_lock(
    root: &Path,
    package_path: &PackagePath,
    bytes: &[u8],
    mutation_lock: &TargetLock,
) -> io::Result<()> {
    require_package_regular_file_size(bytes.len())?;
    mutation_lock.ensure_target_identity()?;
    let (parents, leaf) = validated_generated_components(package_path)?;
    let root = open_absolute_directory(root, false)?;
    let parent = open_components(root, &parents, true)?;
    let result = write_to_directory_under_lock(&parent, &leaf, bytes, 0o600, mutation_lock);
    mutation_lock.ensure_target_identity()?;
    result
}

/// Atomically write one arbitrary validated path without following links.
/// Callers remain responsible for their namespace/containment policy.
pub(crate) fn write_regular_file_atomic_no_follow(path: &Path, bytes: &[u8]) -> io::Result<()> {
    write_regular_file_atomic_no_follow_with_mode(path, bytes, 0o600)
}

pub(crate) fn write_regular_file_atomic_no_follow_with_mode(
    path: &Path,
    bytes: &[u8],
    mode: u32,
) -> io::Result<()> {
    require_package_regular_file_size(bytes.len())?;
    if mode & !0o777 != 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "regular-file mode contains unsupported bits",
        ));
    }
    let parent_path = path.parent().ok_or_else(invalid_generated_artifact)?;
    let leaf = path.file_name().ok_or_else(invalid_generated_artifact)?;
    let parent = open_absolute_directory(parent_path, true)?;
    write_to_directory(&parent, leaf, bytes, mode)
}

fn write_to_directory(
    parent: &Directory,
    leaf: &std::ffi::OsStr,
    bytes: &[u8],
    mode: u32,
) -> io::Result<()> {
    require_package_regular_file_size(bytes.len())?;
    match read_from_directory_with_identity(parent, leaf) {
        Ok(Some((existing, identity))) if existing == bytes => {
            run_idempotent_reopen_test_hook();
            let file = parent
                .open_regular_file(leaf)?
                .ok_or_else(|| io::Error::other("regular file disappeared before chmod"))?;
            if regular_file_identity(&file)? != identity {
                return Err(io::Error::other(
                    "regular file identity changed before chmod",
                ));
            }
            require_named_regular_file_identity(parent, leaf, identity)?;
            set_regular_file_mode(&file, mode)?;
            file.sync_all()?;
            require_named_regular_file_identity(parent, leaf, identity)?;
            return Ok(());
        }
        Ok(Some(_)) => {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "generated artifact exists with different bytes",
            ));
        }
        Ok(None) => {}
        Err(error) => return Err(error),
    }

    let temporary = OsString::from(format!(
        ".{}.{}.{}.tmp",
        leaf.to_string_lossy(),
        std::process::id(),
        NEXT_GENERATED_ARTIFACT_TEMP.fetch_add(1, Ordering::SeqCst)
    ));
    let mut file = parent.create_new_regular_file(&temporary)?;
    let temporary_identity = regular_file_identity(&file)?;
    (|| {
        file.write_all(bytes)?;
        set_regular_file_mode(&file, mode)?;
        file.sync_all()?;
        drop(file);
        if parent.open_regular_file(leaf)?.is_some() {
            return Err(io::Error::other(
                "generated artifact appeared before publication",
            ));
        }
        let current_temporary = parent
            .open_regular_file(&temporary)?
            .ok_or_else(|| io::Error::other("generated-artifact temporary disappeared"))?;
        if regular_file_identity(&current_temporary)? != temporary_identity {
            return Err(io::Error::other(
                "generated-artifact temporary identity changed before publication",
            ));
        }
        drop(current_temporary);
        parent.publish_file_no_replace(&temporary, leaf)?;
        let published = parent
            .open_regular_file(leaf)?
            .ok_or_else(|| io::Error::other("generated artifact disappeared after publication"))?;
        if regular_file_identity(&published)? != temporary_identity {
            return Err(io::Error::other(
                "generated artifact identity changed during publication",
            ));
        }
        parent.sync_all()
    })()
}

fn write_to_directory_under_lock(
    parent: &Directory,
    leaf: &std::ffi::OsStr,
    bytes: &[u8],
    mode: u32,
    mutation_lock: &TargetLock,
) -> io::Result<()> {
    require_package_regular_file_size(bytes.len())?;
    mutation_lock.ensure_target_identity()?;
    let existing = read_from_directory_with_identity(parent, leaf)?;
    if let Some((existing_bytes, identity)) = &existing {
        if existing_bytes == bytes {
            let file = parent
                .open_regular_file(leaf)?
                .ok_or_else(|| io::Error::other("generated artifact disappeared before chmod"))?;
            if regular_file_identity(&file)? != *identity {
                return Err(io::Error::other(
                    "generated artifact identity changed before chmod",
                ));
            }
            require_named_regular_file_identity(parent, leaf, *identity)?;
            set_regular_file_mode(&file, mode)?;
            file.sync_all()?;
            require_named_regular_file_identity(parent, leaf, *identity)?;
            return mutation_lock.ensure_target_identity();
        }
    }

    let temporary = OsString::from(format!(
        ".{}.{}.{}.locked-tmp",
        leaf.to_string_lossy(),
        std::process::id(),
        NEXT_GENERATED_ARTIFACT_TEMP.fetch_add(1, Ordering::SeqCst)
    ));
    let mut file = parent.create_new_regular_file(&temporary)?;
    let temporary_identity = regular_file_identity(&file)?;
    file.write_all(bytes)?;
    set_regular_file_mode(&file, mode)?;
    file.sync_all()?;
    drop(file);
    mutation_lock.ensure_target_identity()?;
    let current_temporary = parent
        .open_regular_file(&temporary)?
        .ok_or_else(|| io::Error::other("generated-artifact temporary disappeared"))?;
    if regular_file_identity(&current_temporary)? != temporary_identity {
        return Err(io::Error::other(
            "generated-artifact temporary identity changed before publication",
        ));
    }
    drop(current_temporary);
    if existing.is_some() {
        mutation_lock.replace_file_under_lock(parent, &temporary, leaf)?;
    } else {
        parent.publish_file_no_replace(&temporary, leaf)?;
    }
    parent.sync_all()?;
    mutation_lock.ensure_target_identity()?;
    let published = parent
        .open_regular_file(leaf)?
        .ok_or_else(|| io::Error::other("generated artifact disappeared after publication"))?;
    if regular_file_identity(&published)? != temporary_identity {
        return Err(io::Error::other(
            "generated artifact identity changed during publication",
        ));
    }
    let (published_bytes, published_identity) = read_from_directory_with_identity(parent, leaf)?
        .ok_or_else(|| io::Error::other("generated artifact disappeared after readback"))?;
    if published_identity != temporary_identity || published_bytes != bytes {
        return Err(io::Error::other(
            "generated artifact bytes changed during publication",
        ));
    }
    mutation_lock.ensure_target_identity()
}

fn require_package_regular_file_size(actual_bytes: usize) -> io::Result<()> {
    let actual_bytes = u64::try_from(actual_bytes).unwrap_or(u64::MAX);
    if actual_bytes > MAX_PACKAGE_REGULAR_FILE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "package regular file exceeds the {MAX_PACKAGE_REGULAR_FILE_BYTES}-byte write limit: {actual_bytes}"
            ),
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn set_regular_file_mode(file: &std::fs::File, mode: u32) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    file.set_permissions(std::fs::Permissions::from_mode(mode))
}

#[cfg(not(unix))]
fn set_regular_file_mode(_file: &std::fs::File, _mode: u32) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "descriptor-relative mode setting requires Unix",
    ))
}

/// Read a package-generated artifact without following a symlink at any
/// directory component or at the final file.
pub fn read_package_generated_artifact_no_follow(
    root: &Path,
    package_path: &PackagePath,
) -> io::Result<Vec<u8>> {
    let (parents, leaf) = validated_generated_components(package_path)?;
    read_package_components(root, &parents, &leaf)
}

/// Read any validated package-relative regular file without following a link
/// at the package root, an intermediate component, or the final entry.
pub fn read_package_regular_file_no_follow(
    root: &Path,
    package_path: &PackagePath,
) -> io::Result<Vec<u8>> {
    npa_package::validate_package_path(package_path, "package_file.path")
        .map_err(|_| invalid_generated_artifact())?;
    let mut components = normal_components(Path::new(package_path.as_str()))?;
    let leaf = components.pop().ok_or_else(invalid_generated_artifact)?;
    read_package_components(root, &components, &leaf)
}

/// Open any validated package-relative regular file through retained
/// no-follow directory descriptors. This lets bounded readers consume the
/// same descriptor that was type-checked at the trust boundary.
pub(crate) fn open_package_regular_file_no_follow(
    root: &Path,
    package_path: &PackagePath,
) -> io::Result<std::fs::File> {
    let (parent, leaf) = open_package_parent_no_follow(root, package_path, false)?;
    parent.open_regular_file(&leaf)?.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            "package regular file is unavailable",
        )
    })
}

/// Retain the parent directory capability and final name of a validated
/// package-relative path. Transactional callers use this to ensure later
/// commit, rollback, and cleanup never re-resolve an attacker-swappable parent.
pub(crate) fn open_package_parent_no_follow(
    root: &Path,
    package_path: &PackagePath,
    create: bool,
) -> io::Result<(Directory, OsString)> {
    npa_package::validate_package_path(package_path, "package_file.path")
        .map_err(|_| invalid_generated_artifact())?;
    let mut components = normal_components(Path::new(package_path.as_str()))?;
    let leaf = components.pop().ok_or_else(invalid_generated_artifact)?;
    let root = open_absolute_directory(root, false)?;
    let parent = open_components(root, &components, create)?;
    Ok((parent, leaf))
}

pub(crate) fn open_package_parent_from_directory(
    root: &Directory,
    package_path: &PackagePath,
    create: bool,
) -> io::Result<(Directory, OsString)> {
    npa_package::validate_package_path(package_path, "package_file.path")
        .map_err(|_| invalid_generated_artifact())?;
    let mut components = normal_components(Path::new(package_path.as_str()))?;
    let leaf = components.pop().ok_or_else(invalid_generated_artifact)?;
    let parent = open_components(root.try_clone()?, &components, create)?;
    Ok((parent, leaf))
}

fn read_package_components(
    root: &Path,
    parents: &[OsString],
    leaf: &std::ffi::OsStr,
) -> io::Result<Vec<u8>> {
    let root = open_absolute_directory(root, false)?;
    let parent = open_components(root, parents, false)?;
    read_from_directory(&parent, leaf)?
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "generated artifact is unavailable"))
}

pub(crate) fn read_regular_file_no_follow(path: &Path) -> io::Result<Vec<u8>> {
    let parent = path.parent().ok_or_else(invalid_generated_artifact)?;
    let leaf = path.file_name().ok_or_else(invalid_generated_artifact)?;
    // `open_absolute_directory` deliberately anchors a relative path at a
    // retained descriptor for the current directory.  Do not turn it into an
    // ambient pathname and reopen it: that would reintroduce a cwd-swap race.
    let directory = open_absolute_directory(parent, false)?;
    read_from_directory(&directory, leaf)?
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "generated artifact is unavailable"))
}

fn validated_generated_components(
    package_path: &PackagePath,
) -> io::Result<(Vec<OsString>, OsString)> {
    npa_package::validate_package_path(package_path, "generated_artifact.path")
        .map_err(|_| invalid_generated_artifact())?;
    let mut components = normal_components(Path::new(package_path.as_str()))?;
    if components.first().and_then(|value| value.to_str()) != Some("generated") {
        return Err(invalid_generated_artifact());
    }
    let leaf = components.pop().ok_or_else(invalid_generated_artifact)?;
    if components.is_empty() {
        return Err(invalid_generated_artifact());
    }
    Ok((components, leaf))
}

fn normal_components(path: &Path) -> io::Result<Vec<OsString>> {
    path.components()
        .map(|component| match component {
            Component::Normal(component) => Ok(component.to_owned()),
            _ => Err(invalid_generated_artifact()),
        })
        .collect()
}

fn open_components(
    mut directory: Directory,
    components: &[OsString],
    create: bool,
) -> io::Result<Directory> {
    for component in components {
        directory = directory.open_or_create_directory(component, create)?;
    }
    Ok(directory)
}

fn read_from_directory(
    directory: &Directory,
    leaf: &std::ffi::OsStr,
) -> io::Result<Option<Vec<u8>>> {
    Ok(read_from_directory_with_identity(directory, leaf)?.map(|(bytes, _)| bytes))
}

fn read_from_directory_with_identity(
    directory: &Directory,
    leaf: &std::ffi::OsStr,
) -> io::Result<Option<(Vec<u8>, Identity)>> {
    let Some(mut file) = directory.open_regular_file(leaf)? else {
        return Ok(None);
    };
    let identity = regular_file_identity(&file)?;
    let metadata = file.metadata()?;
    if metadata.len() > MAX_PACKAGE_REGULAR_FILE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "package regular file exceeds the 128 MiB byte limit",
        ));
    }
    let mut bytes = Vec::new();
    std::io::Read::by_ref(&mut file)
        .take(MAX_PACKAGE_REGULAR_FILE_BYTES + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_PACKAGE_REGULAR_FILE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "package regular file exceeds the 128 MiB byte limit",
        ));
    }
    require_named_regular_file_identity(directory, leaf, identity)?;
    Ok(Some((bytes, identity)))
}

fn invalid_generated_artifact() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "generated artifact path is not a confined regular-file path",
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    static NEXT_TEST_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

    #[test]
    fn generated_artifact_write_size_limit_is_exact() {
        assert!(require_package_regular_file_size(MAX_PACKAGE_REGULAR_FILE_BYTES as usize).is_ok());
        let error = require_package_regular_file_size(MAX_PACKAGE_REGULAR_FILE_BYTES as usize + 1)
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert!(error.to_string().contains("write limit"));
    }

    #[cfg(unix)]
    #[test]
    fn idempotent_write_rejects_leaf_replacement_before_chmod() {
        use std::os::unix::fs::PermissionsExt as _;

        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-generated-writer-idempotent-swap-{}-{serial}",
            std::process::id()
        ));
        std::fs::create_dir(&root).unwrap();
        let leaf = root.join("artifact.json");
        let relocated = root.join("artifact.original");
        std::fs::write(&leaf, b"same").unwrap();
        std::fs::set_permissions(&leaf, std::fs::Permissions::from_mode(0o600)).unwrap();
        let hook_leaf = leaf.clone();
        let hook_relocated = relocated.clone();
        IDEMPOTENT_REOPEN_TEST_HOOK.with(|hook| {
            *hook.borrow_mut() = Some(Box::new(move || {
                std::fs::rename(&hook_leaf, &hook_relocated).unwrap();
                std::fs::write(&hook_leaf, b"replacement").unwrap();
                std::fs::set_permissions(&hook_leaf, std::fs::Permissions::from_mode(0o640))
                    .unwrap();
            }));
        });

        let error =
            write_regular_file_atomic_no_follow_with_mode(&leaf, b"same", 0o644).unwrap_err();
        assert!(error.to_string().contains("identity changed"));
        assert_eq!(std::fs::read(&relocated).unwrap(), b"same");
        assert_eq!(std::fs::read(&leaf).unwrap(), b"replacement");
        assert_eq!(
            std::fs::metadata(&leaf).unwrap().permissions().mode() & 0o777,
            0o640
        );
        std::fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn generated_writer_creates_new_but_never_replaces_different_bytes() {
        let serial = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "npa-generated-writer-create-only-{}-{serial}",
            std::process::id()
        ));
        std::fs::create_dir(&root).unwrap();
        let created = root.join("created.json");
        write_regular_file_atomic_no_follow(&created, b"created").unwrap();
        assert_eq!(std::fs::read(&created).unwrap(), b"created");

        let error = write_regular_file_atomic_no_follow(&created, b"replacement").unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
        assert_eq!(std::fs::read(&created).unwrap(), b"created");
        assert_eq!(std::fs::read_dir(&root).unwrap().count(), 1);

        std::fs::remove_dir_all(root).unwrap();
    }
}
