use std::collections::BTreeSet;
use std::io::Read as _;
use std::path::{Component, Path};
use std::process::Command;

#[cfg(unix)]
use std::{
    ffi::{CString, OsStr},
    fs,
    os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd},
};

use sha2::{Digest, Sha256};

const MAX_SOURCE_MEMBER_BYTES: u64 = 64 * 1024 * 1024;
const MAX_SOURCE_SET_MEMBERS: usize = 16_384;
const MAX_SOURCE_SET_BYTES: u64 = 512 * 1024 * 1024;
const RUNTIME_GIT_TEMP_DIRECTORY: &str = "/private/tmp";

pub(crate) fn validate_runtime_source_set(
    workspace: &Path,
    paths: &str,
    domain: &[u8],
    expected_sha256: &str,
    label: &str,
) -> Result<String, String> {
    if paths.is_empty() {
        return Err(format!("embedded {label} source set is empty"));
    }
    let mut digest = Sha256::new();
    digest.update(domain);
    let mut observed_paths = BTreeSet::new();
    let path_count = paths.split(',').count();
    if path_count > MAX_SOURCE_SET_MEMBERS {
        return Err(format!(
            "embedded {label} source set exceeds the member limit"
        ));
    }
    let mut total_bytes = 0_u64;

    #[cfg(unix)]
    let workspace = WorkspaceDirectory::open(workspace, label)?;
    #[cfg(not(unix))]
    let workspace = workspace
        .canonicalize()
        .map_err(|error| format!("canonicalize {label} workspace root: {error}"))?;

    for relative in paths.split(',') {
        validate_relative_source_path(relative, label)?;
        if !observed_paths.insert(relative) {
            return Err(format!("embedded {label} source paths are noncanonical"));
        }
        #[cfg(unix)]
        let bytes =
            workspace.read_bounded_regular_file(relative, MAX_SOURCE_MEMBER_BYTES, label)?;
        #[cfg(not(unix))]
        let bytes = {
            let path = workspace.join(relative);
            let metadata = std::fs::symlink_metadata(&path).map_err(|error| {
                format!("inspect {label} source-set member {relative}: {error}")
            })?;
            if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
                return Err(format!(
                    "{label} source-set member {relative} is not a real regular file"
                ));
            }
            if metadata.len() > MAX_SOURCE_MEMBER_BYTES {
                return Err(format!(
                    "{label} source-set member {relative} exceeds byte limit"
                ));
            }
            std::fs::read(path)
                .map_err(|error| format!("read {label} source-set member {relative}: {error}"))?
        };
        total_bytes = total_bytes
            .checked_add(u64::try_from(bytes.len()).map_err(display_error)?)
            .ok_or_else(|| format!("{label} source-set byte total overflow"))?;
        if total_bytes > MAX_SOURCE_SET_BYTES {
            return Err(format!(
                "runtime {label} source set exceeds the aggregate byte limit"
            ));
        }
        digest.update(
            u64::try_from(relative.len())
                .map_err(|_| format!("{label} source-set path length exceeds u64"))?
                .to_le_bytes(),
        );
        digest.update(relative.as_bytes());
        digest.update(
            u64::try_from(bytes.len())
                .map_err(|_| format!("{label} source-set byte length exceeds u64"))?
                .to_le_bytes(),
        );
        digest.update(&bytes);
    }
    let observed = encode_hex(&digest.finalize());
    if observed != expected_sha256 {
        return Err(format!(
            "runtime {label} source set {observed} does not match embedded build source set {expected_sha256}"
        ));
    }
    Ok(format!("sha256:{expected_sha256}"))
}

fn validate_relative_source_path(relative: &str, label: &str) -> Result<(), String> {
    let path = Path::new(relative);
    if relative.is_empty()
        || relative.contains(',')
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!("embedded {label} source paths are noncanonical"));
    }
    Ok(())
}

#[cfg(unix)]
struct WorkspaceDirectory {
    descriptor: OwnedFd,
    device: u64,
    absolute_anchor: OwnedFd,
    absolute_components: Vec<CString>,
    identity: (libc::dev_t, libc::ino_t),
}

#[cfg(unix)]
struct OpenedSourceFile {
    descriptor: OwnedFd,
    parent: OwnedFd,
    basename: CString,
    parent_identity: (libc::dev_t, libc::ino_t),
    identity: (libc::dev_t, libc::ino_t),
    initial_size: usize,
}

#[cfg(unix)]
impl WorkspaceDirectory {
    fn open(workspace: &Path, label: &str) -> Result<Self, String> {
        if !workspace.is_absolute() {
            return Err(format!("{label} workspace root must be absolute"));
        }
        let canonical = workspace
            .canonicalize()
            .map_err(|error| format!("canonicalize {label} workspace root: {error}"))?;
        if canonical != workspace {
            return Err(format!("{label} workspace root must already be canonical"));
        }
        let absolute_root = CString::new("/").map_err(display_error)?;
        let absolute_anchor = owned_fd(
            unsafe {
                libc::open(
                    absolute_root.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            },
            &format!("open {label} absolute anchor"),
        )?;
        let mut descriptor = duplicate_fd(absolute_anchor.as_raw_fd())?;
        let mut absolute_components = Vec::new();
        for component in workspace.components() {
            match component {
                Component::RootDir => {}
                Component::Normal(component) => {
                    let component = c_string(component, label)?;
                    descriptor = open_directory_at(descriptor.as_raw_fd(), &component, label)?;
                    absolute_components.push(component);
                }
                _ => return Err(format!("{label} workspace root is noncanonical")),
            }
        }
        let status = file_status(descriptor.as_raw_fd())?;
        if file_kind(&status) != libc::S_IFDIR {
            return Err(format!("{label} workspace root is not a directory"));
        }
        let workspace = Self {
            descriptor,
            device: u64::try_from(status.st_dev).map_err(display_error)?,
            absolute_anchor,
            absolute_components,
            identity: status_identity(&status),
        };
        workspace.verify_attached()?;
        Ok(workspace)
    }

    fn read_bounded_regular_file(
        &self,
        relative: &str,
        maximum_bytes: u64,
        label: &str,
    ) -> Result<Vec<u8>, String> {
        self.read_bounded_regular_file_with_hook(relative, maximum_bytes, label, || {})
    }

    fn read_bounded_regular_file_with_hook(
        &self,
        relative: &str,
        maximum_bytes: u64,
        label: &str,
        after_open: impl FnOnce(),
    ) -> Result<Vec<u8>, String> {
        let opened = self.open_bounded_regular_file(relative, maximum_bytes, label)?;
        after_open();
        let mut file = fs::File::from(opened.descriptor);
        let mut bytes = Vec::with_capacity(opened.initial_size);
        let read_limit = maximum_bytes
            .checked_add(1)
            .ok_or_else(|| format!("{label} source-set byte limit cannot be u64::MAX"))?;
        std::io::Read::by_ref(&mut file)
            .take(read_limit)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("read {label} source-set member {relative}: {error}"))?;
        if u64::try_from(bytes.len()).map_err(display_error)? > maximum_bytes {
            return Err(format!(
                "{label} source-set member {relative} grew beyond its byte limit"
            ));
        }
        let named_after = status_at(opened.parent.as_raw_fd(), &opened.basename)?;
        if file_kind(&named_after) != libc::S_IFREG
            || status_identity(&named_after) != opened.identity
        {
            return Err(format!(
                "{label} source-set member {relative} changed while it was read"
            ));
        }
        self.verify_attached()?;
        let attached_parent = self.open_relative_parent(relative, label)?;
        if status_identity(&file_status(attached_parent.as_raw_fd())?) != opened.parent_identity {
            return Err(format!(
                "{label} source-set member {relative} parent changed while it was read"
            ));
        }
        Ok(bytes)
    }

    fn open_bounded_regular_file(
        &self,
        relative: &str,
        maximum_bytes: u64,
        label: &str,
    ) -> Result<OpenedSourceFile, String> {
        self.verify_attached()?;
        let path = Path::new(relative);
        let components = path.components().collect::<Vec<_>>();
        let (last, parents) = components
            .split_last()
            .ok_or_else(|| format!("embedded {label} source path is empty"))?;
        let mut parent = duplicate_fd(self.descriptor.as_raw_fd())?;
        for component in parents {
            let Component::Normal(component) = component else {
                return Err(format!("embedded {label} source path is noncanonical"));
            };
            let component = c_string(component, label)?;
            parent = open_directory_at(parent.as_raw_fd(), &component, label)?;
            let status = file_status(parent.as_raw_fd())?;
            if file_kind(&status) != libc::S_IFDIR
                || u64::try_from(status.st_dev).map_err(display_error)? != self.device
            {
                return Err(format!(
                    "{label} source-set member {relative} traverses a non-directory or different device"
                ));
            }
        }
        let Component::Normal(basename) = last else {
            return Err(format!("embedded {label} source path is noncanonical"));
        };
        let basename = c_string(basename, label)?;
        let descriptor = owned_fd(
            unsafe {
                libc::openat(
                    parent.as_raw_fd(),
                    basename.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                )
            },
            &format!("open {label} source-set member {relative}"),
        )?;
        let status = file_status(descriptor.as_raw_fd())?;
        let named = status_at(parent.as_raw_fd(), &basename)?;
        if file_kind(&status) != libc::S_IFREG
            || file_kind(&named) != libc::S_IFREG
            || status_identity(&status) != status_identity(&named)
            || u64::try_from(status.st_dev).map_err(display_error)? != self.device
            || status.st_size < 0
            || u64::try_from(status.st_size).map_err(display_error)? > maximum_bytes
        {
            return Err(format!(
                "{label} source-set member {relative} is not a bounded same-device regular file"
            ));
        }
        Ok(OpenedSourceFile {
            descriptor,
            parent_identity: status_identity(&file_status(parent.as_raw_fd())?),
            parent,
            basename,
            identity: status_identity(&status),
            initial_size: usize::try_from(status.st_size).map_err(display_error)?,
        })
    }

    fn open_relative_parent(&self, relative: &str, label: &str) -> Result<OwnedFd, String> {
        let components = Path::new(relative).components().collect::<Vec<_>>();
        let (_, parents) = components
            .split_last()
            .ok_or_else(|| format!("embedded {label} source path is empty"))?;
        let mut parent = duplicate_fd(self.descriptor.as_raw_fd())?;
        for component in parents {
            let Component::Normal(component) = component else {
                return Err(format!("embedded {label} source path is noncanonical"));
            };
            parent = open_directory_at(parent.as_raw_fd(), &c_string(component, label)?, label)?;
        }
        Ok(parent)
    }

    fn verify_attached(&self) -> Result<(), String> {
        let mut attached = duplicate_fd(self.absolute_anchor.as_raw_fd())?;
        for component in &self.absolute_components {
            attached = open_directory_at(attached.as_raw_fd(), component, "runtime workspace")?;
        }
        let status = file_status(attached.as_raw_fd())?;
        if file_kind(&status) != libc::S_IFDIR || status_identity(&status) != self.identity {
            return Err("runtime workspace root changed after it was opened".to_owned());
        }
        Ok(())
    }
}

#[cfg(unix)]
fn c_string(value: &OsStr, label: &str) -> Result<CString, String> {
    use std::os::unix::ffi::OsStrExt as _;
    CString::new(value.as_bytes()).map_err(|_| format!("{label} source path contains NUL"))
}

#[cfg(unix)]
fn open_directory_at(parent: RawFd, name: &CString, label: &str) -> Result<OwnedFd, String> {
    owned_fd(
        unsafe {
            libc::openat(
                parent,
                name.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            )
        },
        &format!("open {label} source directory"),
    )
}

#[cfg(unix)]
fn duplicate_fd(descriptor: RawFd) -> Result<OwnedFd, String> {
    owned_fd(
        unsafe { libc::fcntl(descriptor, libc::F_DUPFD_CLOEXEC, 0) },
        "duplicate workspace directory descriptor",
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
fn status_identity(status: &libc::stat) -> (libc::dev_t, libc::ino_t) {
    (status.st_dev, status.st_ino)
}

#[cfg(unix)]
fn file_kind(status: &libc::stat) -> libc::mode_t {
    status.st_mode & libc::S_IFMT
}

#[allow(dead_code)]
pub(crate) fn validate_runtime_source_identity(
    workspace: &Path,
    expected: &str,
) -> Result<(), String> {
    #[cfg(unix)]
    let retained_workspace = WorkspaceDirectory::open(workspace, "runtime Git")?;
    #[cfg(not(unix))]
    let retained_workspace = workspace
        .canonicalize()
        .map_err(|error| format!("canonicalize runtime Git workspace root: {error}"))?;
    #[cfg(not(unix))]
    if retained_workspace != workspace || !workspace.is_absolute() {
        return Err("runtime Git workspace root must be absolute and canonical".to_owned());
    }
    let head = runtime_git_command()?
        .arg("-C")
        .arg(workspace)
        .args(["rev-parse", "--verify", "HEAD"])
        .output()
        .map_err(|error| format!("cannot read runtime Git HEAD: {error}"))?;
    if !head.status.success() || !head.stderr.is_empty() {
        return Err("cannot read runtime Git HEAD without diagnostics".to_owned());
    }
    let head = std::str::from_utf8(&head.stdout)
        .map_err(|_| "runtime Git HEAD is not UTF-8".to_owned())?
        .strip_suffix('\n')
        .ok_or("runtime Git HEAD must end with exactly one LF")?;
    if head.contains(['\n', '\r']) {
        return Err("runtime Git HEAD must be exactly one canonical line".to_owned());
    }
    #[cfg(unix)]
    retained_workspace.verify_attached()?;
    let status = runtime_git_command()?
        .arg("-C")
        .arg(workspace)
        .args(["status", "--porcelain", "--untracked-files=normal"])
        .output()
        .map_err(|error| format!("cannot read runtime Git status: {error}"))?;
    if !status.status.success() || !status.stderr.is_empty() {
        return Err("cannot read runtime Git status without diagnostics".to_owned());
    }
    #[cfg(unix)]
    retained_workspace.verify_attached()?;
    validate_source_identity_match(head, !status.stdout.is_empty(), expected)
}

fn runtime_git_command() -> Result<Command, String> {
    validate_runtime_git_temp_directory()?;
    let mut command = Command::new("/usr/bin/git");
    configure_runtime_git_environment(&mut command);
    Ok(command)
}

fn configure_runtime_git_environment(command: &mut Command) {
    // macOS invokes confstr(3) while Git initializes. With a fully cleared
    // environment that lookup emits a fallback warning on stderr, which would
    // make the strict provenance command fail even though Git succeeded. Bind
    // the sole required variable to the fixed, policy-checked system temp root
    // instead of inheriting any caller environment.
    command
        .env_clear()
        .env("TMPDIR", RUNTIME_GIT_TEMP_DIRECTORY);
}

#[cfg(unix)]
fn validate_runtime_git_temp_directory() -> Result<(), String> {
    let root_name = CString::new("/").map_err(display_error)?;
    let root = owned_fd(
        unsafe {
            libc::open(
                root_name.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            )
        },
        "open runtime Git temporary-directory anchor",
    )?;
    let root_status = file_status(root.as_raw_fd())?;
    validate_root_owned_directory(&root_status, false, "runtime Git root anchor")?;

    let private_name = CString::new("private").map_err(display_error)?;
    let private = open_directory_at(
        root.as_raw_fd(),
        &private_name,
        "runtime Git temporary-directory",
    )?;
    let private_status = file_status(private.as_raw_fd())?;
    let named_private = status_at(root.as_raw_fd(), &private_name)?;
    validate_root_owned_directory(&private_status, false, "runtime Git /private directory")?;
    if file_kind(&named_private) != libc::S_IFDIR
        || status_identity(&named_private) != status_identity(&private_status)
    {
        return Err("runtime Git /private directory changed while it was inspected".to_owned());
    }

    let temporary_name = CString::new("tmp").map_err(display_error)?;
    let temporary = open_directory_at(
        private.as_raw_fd(),
        &temporary_name,
        "runtime Git temporary-directory",
    )?;
    let temporary_status = file_status(temporary.as_raw_fd())?;
    let named_temporary = status_at(private.as_raw_fd(), &temporary_name)?;
    validate_root_owned_directory(
        &temporary_status,
        true,
        "runtime Git /private/tmp directory",
    )?;
    if file_kind(&named_temporary) != libc::S_IFDIR
        || status_identity(&named_temporary) != status_identity(&temporary_status)
    {
        return Err("runtime Git /private/tmp directory changed while it was inspected".to_owned());
    }

    let attached_private = status_at(root.as_raw_fd(), &private_name)?;
    let attached_temporary = status_at(private.as_raw_fd(), &temporary_name)?;
    if status_identity(&attached_private) != status_identity(&private_status)
        || status_identity(&attached_temporary) != status_identity(&temporary_status)
    {
        return Err(
            "runtime Git temporary-directory chain changed while it was inspected".to_owned(),
        );
    }
    Ok(())
}

#[cfg(unix)]
fn validate_root_owned_directory(
    status: &libc::stat,
    shared_temporary: bool,
    label: &str,
) -> Result<(), String> {
    if file_kind(status) != libc::S_IFDIR || status.st_uid != 0 {
        return Err(format!("{label} is not a root-owned directory"));
    }
    let permissions = status.st_mode & 0o7777 as libc::mode_t;
    if (shared_temporary && permissions != 0o1777)
        || (!shared_temporary && permissions & 0o022 != 0)
    {
        return Err(format!("{label} has unsafe permissions"));
    }
    Ok(())
}

#[cfg(not(unix))]
fn validate_runtime_git_temp_directory() -> Result<(), String> {
    Err("runtime Git provenance requires a Unix temporary-directory policy".to_owned())
}

#[allow(dead_code)]
fn validate_source_identity_match(head: &str, dirty: bool, expected: &str) -> Result<(), String> {
    let observed = if dirty {
        format!("{head}-dirty")
    } else {
        head.to_owned()
    };
    if observed != expected {
        return Err(format!(
            "runtime source identity {observed:?} does not match embedded build identity {expected:?}"
        ));
    }
    Ok(())
}

fn encode_hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT: AtomicU64 = AtomicU64::new(0);

    fn temporary_root() -> std::path::PathBuf {
        let parent = std::env::temp_dir().canonicalize().unwrap();
        let root = parent.join(format!(
            "npa-runtime-source-set-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        root
    }

    #[test]
    fn runtime_source_set_rejects_intermediate_directory_symlink() {
        let root = temporary_root();
        std::fs::create_dir(root.join("real")).unwrap();
        std::fs::write(root.join("real/member.rs"), b"source").unwrap();
        symlink(root.join("real"), root.join("linked")).unwrap();
        let error = validate_runtime_source_set(
            &root,
            "linked/member.rs",
            b"test-domain\0",
            &"0".repeat(64),
            "test",
        )
        .unwrap_err();
        assert!(error.contains("source directory") || error.contains("Too many levels"));
        std::fs::remove_dir_all(root).unwrap();

        let root = temporary_root();
        std::fs::write(root.join("real.rs"), b"source").unwrap();
        symlink(root.join("real.rs"), root.join("linked.rs")).unwrap();
        assert!(validate_runtime_source_set(
            &root,
            "linked.rs",
            b"test-domain\0",
            &"0".repeat(64),
            "test",
        )
        .is_err());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn runtime_source_set_rejects_noncanonical_and_oversized_catalogs() {
        let root = temporary_root();
        std::fs::write(root.join("member.rs"), b"source").unwrap();
        for path in [
            "",
            "./member.rs",
            "member.rs/../member.rs",
            "member.rs,other",
        ] {
            assert!(validate_runtime_source_set(
                &root,
                path,
                b"test-domain\0",
                &"0".repeat(64),
                "test",
            )
            .is_err());
        }
        let oversized = std::iter::repeat_n("member.rs", MAX_SOURCE_SET_MEMBERS + 1)
            .collect::<Vec<_>>()
            .join(",");
        assert!(validate_runtime_source_set(
            &root,
            &oversized,
            b"test-domain\0",
            &"0".repeat(64),
            "test",
        )
        .unwrap_err()
        .contains("member limit"));
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn runtime_source_set_reader_rejects_unrepresentable_maximum() {
        let root = temporary_root();
        std::fs::write(root.join("member.rs"), b"source").unwrap();
        let workspace = WorkspaceDirectory::open(&root, "test").unwrap();
        assert!(workspace
            .read_bounded_regular_file("member.rs", u64::MAX, "test")
            .unwrap_err()
            .contains("cannot be u64::MAX"));
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn runtime_source_set_hashes_same_opened_regular_file_and_rejects_huge_sparse() {
        let root = temporary_root();
        std::fs::write(root.join("member.rs"), b"source").unwrap();
        let workspace = WorkspaceDirectory::open(&root, "test").unwrap();
        let opened = workspace
            .open_bounded_regular_file("member.rs", MAX_SOURCE_MEMBER_BYTES, "test")
            .unwrap();
        std::fs::rename(root.join("member.rs"), root.join("moved.rs")).unwrap();
        std::fs::write(root.join("member.rs"), b"replacement").unwrap();
        let mut opened = fs::File::from(opened.descriptor);
        let mut retained = Vec::new();
        opened.read_to_end(&mut retained).unwrap();
        assert_eq!(retained, b"source");

        let replacement_error = workspace
            .read_bounded_regular_file_with_hook(
                "member.rs",
                MAX_SOURCE_MEMBER_BYTES,
                "test",
                || {
                    std::fs::rename(root.join("member.rs"), root.join("replacement-moved.rs"))
                        .unwrap();
                    std::fs::write(root.join("member.rs"), b"second replacement").unwrap();
                },
            )
            .unwrap_err();
        assert!(replacement_error.contains("changed while it was read"));

        let mut digest = Sha256::new();
        digest.update(b"test-domain\0");
        digest.update(8_u64.to_le_bytes());
        digest.update(b"moved.rs");
        digest.update(6_u64.to_le_bytes());
        digest.update(b"source");
        let expected = encode_hex(&digest.finalize());
        assert_eq!(
            validate_runtime_source_set(&root, "moved.rs", b"test-domain\0", &expected, "test")
                .unwrap(),
            format!("sha256:{expected}")
        );
        std::fs::File::create(root.join("huge.rs"))
            .unwrap()
            .set_len(MAX_SOURCE_MEMBER_BYTES + 1)
            .unwrap();
        assert!(validate_runtime_source_set(
            &root,
            "huge.rs",
            b"test-domain\0",
            &"0".repeat(64),
            "test",
        )
        .unwrap_err()
        .contains("bounded same-device regular file"));
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn runtime_source_set_rejects_symlinked_or_replaced_workspace_root() {
        let outer = temporary_root();
        std::fs::create_dir(outer.join("real")).unwrap();
        symlink(outer.join("real"), outer.join("linked")).unwrap();
        assert!(WorkspaceDirectory::open(&outer.join("linked"), "test").is_err());

        let workspace = WorkspaceDirectory::open(&outer.join("real"), "test").unwrap();
        std::fs::rename(outer.join("real"), outer.join("moved")).unwrap();
        std::fs::create_dir(outer.join("real")).unwrap();
        std::fs::write(outer.join("real/member.rs"), b"replacement").unwrap();
        assert!(workspace
            .read_bounded_regular_file("member.rs", MAX_SOURCE_MEMBER_BYTES, "test")
            .unwrap_err()
            .contains("workspace root changed"));
        std::fs::remove_dir_all(outer).unwrap();
    }

    #[test]
    fn runtime_source_identity_rejects_post_build_dirty_drift() {
        let head = "0123456789abcdef0123456789abcdef01234567";
        assert!(validate_source_identity_match(head, false, head).is_ok());
        assert!(validate_source_identity_match(head, true, head).is_err());
        assert!(validate_source_identity_match(head, false, &format!("{head}-dirty")).is_err());
        assert!(validate_source_identity_match(head, true, &format!("{head}-dirty")).is_ok());
    }

    #[test]
    fn runtime_git_environment_is_closed_except_for_deterministic_tmpdir() {
        let mut command = Command::new("ignored");
        command.env("CALLER_VALUE", "must-not-survive");
        configure_runtime_git_environment(&mut command);
        let environment = command
            .get_envs()
            .map(|(key, value)| {
                (
                    key.to_string_lossy().into_owned(),
                    value.map(|value| value.to_string_lossy().into_owned()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            environment,
            vec![(
                "TMPDIR".to_owned(),
                Some(RUNTIME_GIT_TEMP_DIRECTORY.to_owned())
            )]
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn runtime_git_tmpdir_suppresses_confstr_warning_without_ambient_env() {
        let output = runtime_git_command()
            .unwrap()
            .arg("--version")
            .output()
            .unwrap();
        assert!(output.status.success());
        assert!(output.stderr.is_empty());
        assert!(output.stdout.starts_with(b"git version "));
    }
}
