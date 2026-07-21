use std::collections::{BTreeMap, BTreeSet};
#[cfg(any(target_os = "linux", target_os = "android"))]
use std::ffi::CString;
use std::fs;
#[cfg(any(target_os = "linux", target_os = "android"))]
use std::io::{self, Read};
#[cfg(any(target_os = "linux", target_os = "android"))]
use std::os::fd::FromRawFd;
#[cfg(any(target_os = "linux", target_os = "android"))]
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};
use std::thread;

use npa_api::{
    clear_package_import_context_export_disk_cache, clear_package_verification_decode_cache,
    clear_package_verification_process_memo, format_hash_string, independent_checker_file_hash,
    package_import_context_export_disk_cache_entry_count,
    package_verification_decode_cache_entry_count, parse_independent_checker_runner_policy,
    PerformanceMeasurementLabel,
};
use npa_cert::Name;
use npa_cli::args::{
    PackageAuditCacheMode, PackageChecker, PackageExternalCheckerOptions as ExternalCheckerOptions,
    PackageLockInputMode, PackageTimingMode, PackageVerifierMemoMode, PackageVerifyCertsOptions,
};
use npa_cli::diagnostic::{CommandExitCode, DiagnosticKind, DiagnosticSeverity};
use npa_cli::package::PACKAGE_MANIFEST_PATH;
use npa_cli::package_api::v1::{
    common_options, external_checker_options, verify_certs_full, verify_changed_certificates,
};
use npa_cli::package_artifacts::{
    run_package_shared_snapshot_check_group, PackageSharedSnapshotCheckGroupOptions,
};
use npa_cli::package_verify::run_package_verify_certs;
use npa_package::{
    build_package_lock_from_package_root, format_package_hash, package_audit_disk_memo_key,
    package_audit_disk_memo_result_entry_json, package_file_hash, parse_and_validate_manifest_str,
    parse_package_audit_disk_memo_result_entry_json, parse_package_audit_result_entry_json,
    parse_package_lock_json, PackageExternalImport, PackageHash, PackageModule, PackagePath,
    PACKAGE_AUDIT_CACHE_LAYOUT_DIR, PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR,
};

const LOCK_PATH: &str = "generated/package-lock.json";

static NEXT_TEMP_DIR: AtomicUsize = AtomicUsize::new(0);

struct TestPackage {
    path: PathBuf,
    cleanup_path: PathBuf,
}

impl TestPackage {
    fn new(label: &str) -> Self {
        let index = NEXT_TEMP_DIR.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!(
            "npa-cli-package-verify-certs-{}-{label}-{index}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(&path).unwrap();
        Self {
            path: path.clone(),
            cleanup_path: path,
        }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn cleanup_path(&self) -> &Path {
        &self.cleanup_path
    }

    fn artifact_path(&self, relative: &str) -> PathBuf {
        self.path.join(relative)
    }
}

impl Drop for TestPackage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.cleanup_path);
    }
}

#[cfg(any(target_os = "linux", target_os = "android"))]
struct PackageReadAccessGuard {
    events: fs::File,
    watched: BTreeMap<i32, String>,
    mutation_watches: BTreeMap<i32, String>,
}

#[derive(Debug, Default, Eq, PartialEq)]
struct PackageIoObservation {
    accessed: BTreeSet<String>,
    mutations: BTreeSet<String>,
}

#[cfg(any(target_os = "linux", target_os = "android"))]
impl PackageReadAccessGuard {
    fn new(root: &Path, paths: &[PathBuf]) -> Self {
        Self::new_with_mutation_watch(root, paths, false)
    }

    fn new_with_package_mutation_watch(root: &Path, paths: &[PathBuf]) -> Self {
        Self::new_with_mutation_watch(root, paths, true)
    }

    fn new_with_mutation_watch(root: &Path, paths: &[PathBuf], watch_mutations: bool) -> Self {
        // SAFETY: inotify_init1 has no pointer arguments. A successful owned
        // descriptor is transferred immediately into File and closed by Drop.
        let descriptor = unsafe { libc::inotify_init1(libc::IN_CLOEXEC | libc::IN_NONBLOCK) };
        assert!(
            descriptor >= 0,
            "inotify_init1 failed: {}",
            io::Error::last_os_error()
        );
        // SAFETY: descriptor is a fresh, successful inotify descriptor owned
        // by this guard and is not used through another File.
        let events = unsafe { fs::File::from_raw_fd(descriptor) };
        let mut watched = BTreeMap::new();
        for path in paths {
            let relative = path
                .strip_prefix(root)
                .unwrap_or_else(|_| panic!("watched path must be under package root: {path:?}"))
                .to_string_lossy()
                .replace('\\', "/");
            let path = CString::new(path.as_os_str().as_bytes()).unwrap();
            // IN_OPEN catches attempted reads of directory-shaped poison
            // guards; IN_ACCESS catches ordinary file reads. Neither depends
            // on Unix permission bits, so this remains effective as root.
            // SAFETY: path is a live NUL-terminated CString and descriptor
            // remains owned by events for the lifetime of every watch.
            let watch = unsafe {
                libc::inotify_add_watch(descriptor, path.as_ptr(), libc::IN_OPEN | libc::IN_ACCESS)
            };
            assert!(
                watch >= 0,
                "inotify_add_watch failed for {relative}: {}",
                io::Error::last_os_error()
            );
            watched.insert(watch, relative);
        }
        let mut mutation_watches = BTreeMap::new();
        if watch_mutations {
            for directory in package_existing_directory_paths(root) {
                let relative = directory
                    .strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .replace('\\', "/");
                let directory = CString::new(directory.as_os_str().as_bytes()).unwrap();
                // SAFETY: directory is a live NUL-terminated CString and the
                // descriptor remains owned by events. Watching every existing
                // directory catches transient creates/removes as well as final
                // package-root mutations.
                let watch = unsafe {
                    libc::inotify_add_watch(
                        descriptor,
                        directory.as_ptr(),
                        libc::IN_ONLYDIR
                            | libc::IN_CREATE
                            | libc::IN_DELETE
                            | libc::IN_MOVED_FROM
                            | libc::IN_MOVED_TO
                            | libc::IN_CLOSE_WRITE
                            | libc::IN_ATTRIB,
                    )
                };
                assert!(
                    watch >= 0,
                    "inotify mutation watch failed for {relative}: {}",
                    io::Error::last_os_error()
                );
                mutation_watches.insert(watch, relative);
            }
        }
        Self {
            events,
            watched,
            mutation_watches,
        }
    }

    fn finish(mut self) -> PackageIoObservation {
        const HEADER_BYTES: usize = 16;
        let mut accessed = BTreeSet::new();
        let mut mutations = BTreeSet::new();
        let mut buffer = [0_u8; 16 * 1024];
        loop {
            let count = match self.events.read(&mut buffer) {
                Ok(0) => break,
                Ok(count) => count,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => panic!("inotify read failed: {error}"),
            };
            let mut offset = 0;
            while offset + HEADER_BYTES <= count {
                let watch = i32::from_ne_bytes(buffer[offset..offset + 4].try_into().unwrap());
                let mask = u32::from_ne_bytes(buffer[offset + 4..offset + 8].try_into().unwrap());
                let name_len = u32::from_ne_bytes(
                    buffer[offset + 12..offset + HEADER_BYTES]
                        .try_into()
                        .unwrap(),
                ) as usize;
                let name = &buffer[offset + HEADER_BYTES..offset + HEADER_BYTES + name_len];
                let name = name.split(|byte| *byte == 0).next().unwrap_or(&[]);
                if mask & libc::IN_Q_OVERFLOW != 0 {
                    mutations.insert("<inotify-queue-overflow>".to_owned());
                }
                if mask & (libc::IN_OPEN | libc::IN_ACCESS) != 0 {
                    if let Some(relative) = self.watched.get(&watch) {
                        accessed.insert(relative.clone());
                    }
                }
                if mask
                    & (libc::IN_CREATE
                        | libc::IN_DELETE
                        | libc::IN_MOVED_FROM
                        | libc::IN_MOVED_TO
                        | libc::IN_CLOSE_WRITE
                        | libc::IN_ATTRIB)
                    != 0
                {
                    if let Some(directory) = self.mutation_watches.get(&watch) {
                        let name = String::from_utf8_lossy(name);
                        let path = if directory.is_empty() {
                            name.into_owned()
                        } else if name.is_empty() {
                            directory.clone()
                        } else {
                            format!("{directory}/{name}")
                        };
                        mutations.insert(path);
                    }
                }
                offset += HEADER_BYTES + name_len;
            }
            assert_eq!(offset, count, "complete inotify event buffer");
        }
        PackageIoObservation {
            accessed,
            mutations,
        }
    }
}

#[cfg(target_os = "linux")]
fn install_network_input_guard() {
    const BPF_LOAD_SYSCALL_NUMBER: u16 = 0x20;
    const BPF_JUMP_EQUAL: u16 = 0x15;
    const BPF_RETURN: u16 = 0x06;
    const SECCOMP_RETURN_ERRNO: u32 = 0x0005_0000;
    const SECCOMP_RETURN_ALLOW: u32 = 0x7fff_0000;

    let statement = |code, value| libc::sock_filter {
        code,
        jt: 0,
        jf: 0,
        k: value,
    };
    let jump = |syscall| libc::sock_filter {
        code: BPF_JUMP_EQUAL,
        jt: 0,
        jf: 1,
        k: syscall,
    };
    let blocked = [
        libc::SYS_socket,
        libc::SYS_connect,
        libc::SYS_accept,
        libc::SYS_accept4,
        libc::SYS_bind,
        libc::SYS_listen,
    ];
    let mut filter = Vec::with_capacity(2 + blocked.len() * 2);
    filter.push(statement(BPF_LOAD_SYSCALL_NUMBER, 0));
    for syscall in blocked {
        filter.push(jump(u32::try_from(syscall).unwrap()));
        filter.push(statement(
            BPF_RETURN,
            SECCOMP_RETURN_ERRNO | u32::try_from(libc::EPERM).unwrap(),
        ));
    }
    filter.push(statement(BPF_RETURN, SECCOMP_RETURN_ALLOW));
    let mut program = libc::sock_fprog {
        len: u16::try_from(filter.len()).unwrap(),
        filter: filter.as_mut_ptr(),
    };

    // SAFETY: these prctl calls affect only the dedicated test thread and its
    // descendants. The BPF program remains live for the duration of the call,
    // contains only fixed seccomp_data syscall-number reads, and returns EPERM
    // for network syscalls while allowing every other syscall.
    unsafe {
        assert_eq!(
            libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0),
            0,
            "PR_SET_NO_NEW_PRIVS failed: {}",
            io::Error::last_os_error()
        );
        assert_eq!(
            libc::prctl(
                libc::PR_SET_SECCOMP,
                libc::SECCOMP_MODE_FILTER,
                &mut program as *mut libc::sock_fprog,
            ),
            0,
            "PR_SET_SECCOMP failed: {}",
            io::Error::last_os_error()
        );
    }
}

fn with_network_inputs_denied<T: Send + 'static>(
    operation: impl FnOnce() -> T + Send + 'static,
) -> T {
    thread::spawn(move || {
        #[cfg(target_os = "linux")]
        install_network_input_guard();
        operation()
    })
    .join()
    .expect("network-denied verification thread must not panic")
}

#[cfg(not(any(target_os = "linux", target_os = "android")))]
struct PackageReadAccessGuard;

#[cfg(not(any(target_os = "linux", target_os = "android")))]
impl PackageReadAccessGuard {
    fn new(_root: &Path, _paths: &[PathBuf]) -> Self {
        Self
    }

    fn new_with_package_mutation_watch(_root: &Path, _paths: &[PathBuf]) -> Self {
        Self
    }

    fn finish(self) -> PackageIoObservation {
        PackageIoObservation::default()
    }
}

#[derive(Clone, Copy, Debug)]
enum CheckedLockPoison {
    Missing,
    Malformed,
    Stale,
    Unreadable,
}

impl CheckedLockPoison {
    const ALL: [Self; 4] = [
        Self::Missing,
        Self::Malformed,
        Self::Stale,
        Self::Unreadable,
    ];

    fn label(self) -> &'static str {
        match self {
            Self::Missing => "missing",
            Self::Malformed => "malformed",
            Self::Stale => "stale",
            Self::Unreadable => "unreadable",
        }
    }

    fn checked_reason(self) -> &'static str {
        match self {
            Self::Missing | Self::Unreadable => "package_lock_missing",
            Self::Malformed => "invalid_json",
            Self::Stale => "package_lock_stale",
        }
    }

    fn checked_kind(self) -> DiagnosticKind {
        match self {
            Self::Missing | Self::Malformed => DiagnosticKind::PackageLock,
            Self::Stale => DiagnosticKind::HashMismatch,
            Self::Unreadable => DiagnosticKind::ArtifactIo,
        }
    }

    fn apply(self, package: &TestPackage) {
        let path = package.artifact_path(LOCK_PATH);
        match self {
            Self::Missing => fs::remove_file(path).unwrap(),
            Self::Malformed => fs::write(path, b"{not-json").unwrap(),
            Self::Stale => {
                let mut source = fs::read_to_string(&path).unwrap();
                source.push('\n');
                fs::write(path, source).unwrap();
            }
            Self::Unreadable => {
                fs::remove_file(&path).unwrap();
                fs::create_dir(path).unwrap();
            }
        }
    }
}

#[derive(Clone)]
struct ManifestModule {
    module: Name,
    source: String,
    certificate: String,
    meta: Option<String>,
    replay: Option<String>,
    imports: Vec<Name>,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
}

#[cfg(target_os = "linux")]
#[test]
fn package_verify_certs_access_guards_detect_file_reads_and_deny_network_inputs() {
    let package = build_source_free_fixture(
        "access-guard-calibration",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let forbidden = install_non_input_sentinels(&package, "Proofs/Ai/Basic");
    let source = package.artifact_path("Proofs/Ai/Basic/source.npa");
    let guard = PackageReadAccessGuard::new_with_package_mutation_watch(
        package.path(),
        std::slice::from_ref(&source),
    );
    fs::read(source).unwrap();
    let transient = package.artifact_path("generated/transient-package-lock.tmp");
    fs::write(&transient, b"must be observed").unwrap();
    fs::remove_file(transient).unwrap();
    let observation = guard.finish();
    assert_eq!(
        observation.accessed,
        BTreeSet::from(["Proofs/Ai/Basic/source.npa".to_owned()])
    );
    assert_eq!(
        observation.mutations,
        BTreeSet::from(["generated/transient-package-lock.tmp".to_owned()])
    );
    assert!(forbidden
        .iter()
        .any(|path| path == "generated/network-registry.json"));

    let network_error = with_network_inputs_denied(|| {
        // SAFETY: socket receives no pointers and the seccomp guard must reject
        // it before the kernel allocates a descriptor.
        let descriptor = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
        assert_eq!(descriptor, -1, "network syscall must be denied");
        io::Error::last_os_error().raw_os_error()
    });
    assert_eq!(network_error, Some(libc::EPERM));
}

#[test]
fn package_verify_certs_in_process_modes_enforce_read_scope_and_package_root_no_write() {
    for (mode, checker) in [
        (PackageLockInputMode::CheckedFile, PackageChecker::Reference),
        (PackageLockInputMode::CheckedFile, PackageChecker::Fast),
        (
            PackageLockInputMode::ReconstructedInMemory,
            PackageChecker::Reference,
        ),
        (
            PackageLockInputMode::ReconstructedInMemory,
            PackageChecker::Fast,
        ),
    ] {
        let label = format!("{}-{}", mode.as_str(), checker.as_str());
        let mut package = build_source_free_fixture(
            &format!("read-scope-{label}"),
            "Proofs.Ai.Eq",
            true,
            &["Eq.rec"],
        );
        let lock_hash = checked_lock_hash(&package);
        if mode == PackageLockInputMode::ReconstructedInMemory {
            fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
        }
        nest_package_in_worktree(&mut package, "proofs");
        let forbidden = install_non_input_sentinels(&package, "Proofs/Ai/Eq");
        init_git_worktree_baseline(&package);
        assert!(git_status_snapshot(&package).is_empty());

        let expected = expected_in_process_inputs(
            mode,
            &[
                "Proofs/Ai/Eq/certificate.npcert",
                "vendor/npa-std/Std/Logic/Eq/certificate.npcert",
                "vendor/npa-std/Std/Nat/Basic/certificate.npcert",
            ],
        );
        let result = run_guarded_read_only_verify(
            &package,
            verify_certs_full(common_options(package.path(), true), checker)
                .with_package_lock_mode(mode),
            &expected,
            &forbidden,
            &label,
        );

        assert_eq!(
            result.exit_code(),
            CommandExitCode::Success,
            "{label}: {}",
            result.render_json()
        );
        assert_lock_provenance(&result.diagnostics[1], mode, lock_hash);
        assert_eq!(lock_provenance_count(&result), 1, "{label}");
        assert_eq!(
            package.artifact_path(LOCK_PATH).is_file(),
            mode == PackageLockInputMode::CheckedFile,
            "{label}: verification must not create or remove the checked lock"
        );
    }
}

#[test]
fn package_verify_external_reads_only_checked_and_explicit_policy_inputs() {
    let mut package =
        build_source_free_fixture("external-read-scope", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    nest_package_in_worktree(&mut package, "proofs");
    let external = write_external_runner_fixture(&package, true);
    let forbidden = install_non_input_sentinels(&package, "Proofs/Ai/Eq");
    let access_guard =
        PackageReadAccessGuard::new(package.path(), &package_existing_file_paths(&package));
    let package_root = package.path().to_owned();

    let result = with_network_inputs_denied(move || {
        run_package_verify_certs(
            verify_certs_full(common_options(package_root, true), PackageChecker::External)
                .with_external(external),
        )
    });
    let accessed = access_guard.finish().accessed;
    let expected = BTreeSet::from([
        PACKAGE_MANIFEST_PATH.to_owned(),
        LOCK_PATH.to_owned(),
        "Proofs/Ai/Eq/certificate.npcert".to_owned(),
        "vendor/npa-std/Std/Logic/Eq/certificate.npcert".to_owned(),
        "vendor/npa-std/Std/Nat/Basic/certificate.npcert".to_owned(),
        "ci/runner.release.json".to_owned(),
        "ci/axiom-policy.toml".to_owned(),
        "ci/checker-binaries.json".to_owned(),
        "tools/checkers/npa-checker-ext".to_owned(),
    ]);
    assert_package_read_scope(&accessed, &expected, &forbidden, "checked-external");
    assert_eq!(
        result.exit_code(),
        CommandExitCode::Success,
        "{}",
        result.render_json()
    );
}

#[test]
fn package_verify_certs_acceleration_writes_stay_outside_package_root() {
    let _audit_guard = audit_cache_test_lock();
    let _memo_guard = disk_memo_test_lock();
    clear_audit_cache();
    clear_disk_memo();
    clear_package_verification_process_memo();

    let mut cached = build_source_free_fixture(
        "guarded-audit-cache",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.NoWrite.AuditCache"],
    );
    nest_package_in_worktree(&mut cached, "proofs");
    let cached_forbidden = install_non_input_sentinels(&cached, "Proofs/Ai/Basic");
    init_git_worktree_baseline(&cached);
    let cached_result = run_guarded_read_only_verify(
        &cached,
        verify_certs_full(
            common_options(cached.path(), true),
            PackageChecker::Reference,
        )
        .with_audit_cache(PackageAuditCacheMode::ReadThrough),
        &expected_in_process_inputs(
            PackageLockInputMode::CheckedFile,
            &["Proofs/Ai/Basic/certificate.npcert"],
        ),
        &cached_forbidden,
        "checked-audit-cache",
    );
    assert_eq!(cached_result.exit_code(), CommandExitCode::Success);
    let cache_root = std::env::current_dir()
        .unwrap()
        .join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR);
    let cache_entries = audit_cache_entries();
    assert_eq!(cache_entries.len(), 1);
    assert!(cache_entries
        .iter()
        .all(|path| path.starts_with(&cache_root)));
    assert!(cache_entries
        .iter()
        .all(|path| !path.starts_with(cached.path())));

    let mut memoized = build_source_free_fixture(
        "guarded-disk-memo",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.NoWrite.DiskMemo"],
    );
    fs::remove_file(memoized.artifact_path(LOCK_PATH)).unwrap();
    nest_package_in_worktree(&mut memoized, "proofs");
    let memo_forbidden = install_non_input_sentinels(&memoized, "Proofs/Ai/Basic");
    init_git_worktree_baseline(&memoized);
    let memo_result = run_guarded_read_only_verify(
        &memoized,
        verify_certs_full(
            common_options(memoized.path(), true),
            PackageChecker::Reference,
        )
        .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory)
        .with_verifier_memo(PackageVerifierMemoMode::Disk)
        .with_timings(PackageTimingMode::Summary),
        &expected_in_process_inputs(
            PackageLockInputMode::ReconstructedInMemory,
            &["Proofs/Ai/Basic/certificate.npcert"],
        ),
        &memo_forbidden,
        "reconstructed-disk-memo",
    );
    assert_eq!(memo_result.exit_code(), CommandExitCode::Success);
    let memo_root = std::env::current_dir()
        .unwrap()
        .join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR);
    let memo_entries = disk_memo_entries();
    assert_eq!(memo_entries.len(), 1);
    assert!(memo_entries.iter().all(|path| path.starts_with(&memo_root)));
    assert!(memo_entries
        .iter()
        .all(|path| !path.starts_with(memoized.path())));

    clear_audit_cache();
    clear_disk_memo();
}

#[test]
fn package_verify_certs_reference_succeeds_without_source_replay_or_meta() {
    let package = build_source_free_fixture(
        "reference-source-free",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Basic/replay.json")
        .exists());
    assert!(!package.artifact_path("Proofs/Ai/Basic/meta.json").exists());
    let lock_hash = checked_lock_hash(&package);

    let result = run_verify(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 3);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::ReferenceVerifier,
        "package_verified",
        Some("npa-checker-ref"),
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("mode=reference;verdict_source=npa-checker-ref;reference_checker_verdict=true;locally_accelerated=false;modules=1")
    );
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert_eq!(result.diagnostics[2].reason_code, "module_verified");
    assert_info(
        &result.diagnostics[2],
        DiagnosticKind::ReferenceVerifier,
        "module_verified",
        Some("npa-checker-ref"),
    );
    assert_eq!(
        result.diagnostics[2].module.as_deref(),
        Some("Proofs.Ai.Basic")
    );
    assert_eq!(
        result.diagnostics[2].path.as_deref(),
        Some("Proofs/Ai/Basic/certificate.npcert")
    );
    assert!(!result.render_json().contains("/tmp/"));
}

#[test]
fn package_verify_certs_fast_succeeds_and_is_labeled_fast_kernel() {
    let package =
        build_source_free_fixture("fast-source-free", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let lock_hash = checked_lock_hash(&package);

    let result = run_verify(&package, PackageChecker::Fast);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.diagnostics.len(), 3);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::FastVerifier,
        "package_verified",
        Some("fast-kernel-certificate-verifier"),
    );
    let aggregate = result.diagnostics[0].actual_value.as_deref().unwrap();
    assert!(aggregate.contains("mode=fast-kernel"));
    assert!(aggregate.contains("reference_checker_verdict=false"));
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.checker.as_deref() != Some("npa-checker-ref")));
}

#[test]
fn package_verify_certs_shared_snapshot_fast_result_has_checked_provenance() {
    let package_root = repo_root().join("testdata/package/proofs");
    let lock_hash = package_file_hash(&fs::read(package_root.join(LOCK_PATH)).unwrap());

    let group = run_package_shared_snapshot_check_group(PackageSharedSnapshotCheckGroupOptions {
        common: common_options(&package_root, true),
        timings: PackageTimingMode::Off,
    });

    assert_eq!(group.summary.exit_code(), CommandExitCode::Success);
    assert_eq!(
        group
            .command_results
            .iter()
            .map(|result| result.command.as_str())
            .collect::<Vec<_>>(),
        vec![
            "package axiom-report",
            "package index",
            "package theorem-premise-report",
            "package export-summary",
            "package publish-plan",
            "package verify-certs",
        ]
    );
    assert!(group.summary.diagnostics.iter().any(|diagnostic| {
        diagnostic.reason_code == "shared_snapshot_summary"
            && diagnostic
                .actual_value
                .as_deref()
                .is_some_and(|value| value.contains("commands=6"))
    }));
    let result = group
        .command_results
        .iter()
        .find(|result| result.command == "package verify-certs")
        .expect("shared snapshot includes package verification");
    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert_eq!(lock_provenance_count(result), 1);
}

#[test]
fn package_verify_certs_reconstructed_reference_succeeds_without_checked_lock() {
    let package = build_source_free_fixture(
        "reconstructed-reference-no-lock",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let lock_hash = checked_lock_hash(&package);
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();

    let result = run_verify_with_lock_mode(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
    );

    assert_eq!(
        result.exit_code(),
        CommandExitCode::Success,
        "{}",
        result.render_json()
    );
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        lock_hash,
    );
    assert!(!package.artifact_path(LOCK_PATH).exists());
}

#[test]
fn package_verify_certs_reconstructed_fast_is_source_free_and_writes_nothing() {
    let package = build_source_free_fixture(
        "reconstructed-fast-source-free",
        "Proofs.Ai.Eq",
        true,
        &["Eq.rec"],
    );
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
    let _ = install_non_input_sentinels(&package, "Proofs/Ai/Eq");
    let before = package_tree_snapshot(&package);

    let result = run_verify_with_lock_mode(
        &package,
        PackageChecker::Fast,
        PackageLockInputMode::ReconstructedInMemory,
    );

    assert_eq!(
        result.exit_code(),
        CommandExitCode::Success,
        "{}",
        result.render_json()
    );
    assert_eq!(package_tree_snapshot(&package), before);
    assert!(!package.artifact_path(LOCK_PATH).exists());
}

#[test]
fn package_verify_certs_reconstructed_reference_and_fast_share_lock_identities() {
    let package = build_source_free_fixture(
        "reconstructed-shared-checker-identities",
        "Proofs.Ai.Eq",
        true,
        &["Eq.rec"],
    );
    let lock_hash = checked_lock_hash(&package);
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();

    let reference = run_verify_with_lock_mode(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
    );
    let fast = run_verify_with_lock_mode(
        &package,
        PackageChecker::Fast,
        PackageLockInputMode::ReconstructedInMemory,
    );

    assert_eq!(reference.exit_code(), CommandExitCode::Success);
    assert_eq!(fast.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &reference.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        lock_hash,
    );
    assert_lock_provenance(
        &fast.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        lock_hash,
    );
    assert_eq!(
        verified_module_identities(&reference),
        verified_module_identities(&fast)
    );
    assert_eq!(verified_module_identities(&reference).len(), 3);
}

#[test]
fn package_verify_certs_reconstructed_external_fails_before_package_loading() {
    let package = TestPackage::new("reconstructed-external-pre-io");
    let missing_root = package.path().to_owned();
    fs::remove_dir_all(&missing_root).unwrap();

    let result = run_package_verify_certs(
        verify_certs_full(
            common_options(&missing_root, true),
            PackageChecker::External,
        )
        .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory)
        .with_external(external_checker_options(
            "missing/runner-policy.json",
            "sha256:missing",
            "missing/checker-registry.json",
        )),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--package-lock")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("reconstructed;checker=external")
    );
    assert_eq!(lock_provenance_count(&result), 0);
    assert!(!missing_root.exists());
}

#[test]
fn package_verify_certs_checked_mode_rejects_lock_failures_without_reconstruction() {
    for poison in CheckedLockPoison::ALL {
        let package = build_source_free_fixture(
            &format!("checked-lock-{}", poison.label()),
            "Proofs.Ai.Basic",
            false,
            &["Eq.rec"],
        );
        poison.apply(&package);
        let before = package_tree_snapshot(&package);

        let result = run_verify_with_lock_mode(
            &package,
            PackageChecker::Reference,
            PackageLockInputMode::CheckedFile,
        );

        assert_eq!(
            result.exit_code(),
            CommandExitCode::PackageFailure,
            "{}",
            poison.label()
        );
        assert_eq!(result.diagnostics.len(), 1, "{}", poison.label());
        assert_eq!(
            result.diagnostics[0].reason_code,
            poison.checked_reason(),
            "{}",
            poison.label()
        );
        assert_eq!(
            result.diagnostics[0].kind,
            poison.checked_kind(),
            "{}",
            poison.label()
        );
        assert_eq!(
            result.diagnostics[0].path.as_deref(),
            Some(LOCK_PATH),
            "{}",
            poison.label()
        );
        assert_eq!(
            package_tree_snapshot(&package),
            before,
            "{}",
            poison.label()
        );
        assert!(result
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.reason_code != "package_verified"));
    }
}

#[test]
fn package_verify_certs_reconstructed_mode_ignores_checked_lock_state() {
    let mut baseline_diagnostics = None;
    for poison in CheckedLockPoison::ALL {
        let package = build_source_free_fixture(
            &format!("reconstructed-lock-{}", poison.label()),
            "Proofs.Ai.Basic",
            false,
            &["Eq.rec"],
        );
        poison.apply(&package);
        let before = package_tree_snapshot(&package);
        let lock_path = package.artifact_path(LOCK_PATH);
        let lock_access_guard = lock_path
            .exists()
            .then(|| PackageReadAccessGuard::new(package.path(), &[lock_path]));

        let result = with_network_inputs_denied({
            let options = verify_certs_full(
                common_options(package.path(), true),
                PackageChecker::Reference,
            )
            .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory);
            move || run_package_verify_certs(options)
        });
        if let Some(guard) = lock_access_guard {
            assert!(
                guard.finish().accessed.is_empty(),
                "{}: reconstructed verification opened the checked lock",
                poison.label()
            );
        }

        assert_eq!(
            result.exit_code(),
            CommandExitCode::Success,
            "{}: {}",
            poison.label(),
            result.render_json()
        );
        assert_eq!(
            package_tree_snapshot(&package),
            before,
            "{}",
            poison.label()
        );
        if let Some(expected) = &baseline_diagnostics {
            assert_eq!(&result.diagnostics, expected, "{}", poison.label());
        } else {
            baseline_diagnostics = Some(result.diagnostics.clone());
        }
    }
}

#[test]
fn package_verify_certs_reconstructed_hash_matches_canonical_lock_write() {
    let _guard = audit_cache_test_lock();
    for (checker, label, unique_axiom) in [
        (
            PackageChecker::Reference,
            "reference",
            "Reconstruction.Hash.Reference",
        ),
        (PackageChecker::Fast, "fast", "Reconstruction.Hash.Fast"),
    ] {
        clear_audit_cache();
        let package = build_source_free_fixture(
            &format!("reconstructed-hash-{label}"),
            "Proofs.Ai.Basic",
            false,
            &["Eq.rec", unique_axiom],
        );
        let lock_path = package.artifact_path(LOCK_PATH);
        let canonical_lock = fs::read_to_string(&lock_path).unwrap();
        let expected_hash = package_file_hash(canonical_lock.as_bytes());
        fs::remove_file(&lock_path).unwrap();
        let before = package_tree_snapshot(&package);

        let result = run_verify_with_lock_mode_and_audit_cache(
            &package,
            checker,
            PackageLockInputMode::ReconstructedInMemory,
            PackageAuditCacheMode::ReadThrough,
        );

        assert_eq!(
            result.exit_code(),
            CommandExitCode::Success,
            "{label}: {}",
            result.render_json()
        );
        assert_lock_provenance(
            &result.diagnostics[1],
            PackageLockInputMode::ReconstructedInMemory,
            expected_hash,
        );
        assert_eq!(package_tree_snapshot(&package), before, "{label}");
        let entries = audit_cache_entries();
        assert_eq!(entries.len(), 1, "{label}");
        let source = fs::read_to_string(&entries[0]).unwrap();
        let entry = parse_package_audit_result_entry_json(&source).unwrap();
        assert_eq!(entry.key_input.package_lock_hash, expected_hash, "{label}");
    }
    clear_audit_cache();
}

#[test]
fn package_verify_certs_reconstructed_preserves_strict_identity_diagnostics() {
    let tampered_package = build_source_free_fixture(
        "reconstructed-certificate-bytes",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    fs::remove_file(tampered_package.artifact_path(LOCK_PATH)).unwrap();
    let certificate_path = tampered_package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
    let mut certificate = fs::read(&certificate_path).unwrap();
    certificate.push(0);
    fs::write(certificate_path, certificate).unwrap();
    let tampered_result = run_verify_with_lock_mode(
        &tampered_package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
    );
    assert_failure(
        &tampered_result,
        DiagnosticKind::HashMismatch,
        "certificate_file_hash_mismatch",
        Some("modules[0].expected_certificate_file_hash"),
        Some("expected_certificate_file_hash"),
    );

    for (manifest_field, reason) in [
        (
            "expected_certificate_file_hash",
            "certificate_file_hash_mismatch",
        ),
        ("expected_export_hash", "export_hash_mismatch"),
        ("expected_axiom_report_hash", "axiom_report_hash_mismatch"),
        ("expected_certificate_hash", "certificate_hash_mismatch"),
    ] {
        let package = build_source_free_fixture(
            &format!("reconstructed-{manifest_field}"),
            "Proofs.Ai.Basic",
            false,
            &["Eq.rec"],
        );
        fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
        replace_manifest_hash(&package, manifest_field, PackageHash::new([0_u8; 32]));

        let result = run_verify_with_lock_mode(
            &package,
            PackageChecker::Reference,
            PackageLockInputMode::ReconstructedInMemory,
        );

        assert_failure(
            &result,
            DiagnosticKind::HashMismatch,
            reason,
            Some(&format!("modules[0].{manifest_field}")),
            Some(manifest_field),
        );
    }
}

#[test]
fn package_verify_certs_reconstructed_validates_external_import_pins() {
    for (field, reason) in [
        ("export_hash", "export_hash_mismatch"),
        ("certificate_hash", "certificate_hash_mismatch"),
    ] {
        let package = build_source_free_fixture(
            &format!("reconstructed-import-{field}"),
            "Proofs.Ai.Eq",
            true,
            &["Eq.rec"],
        );
        fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
        replace_manifest_hash(&package, field, PackageHash::new([0_u8; 32]));

        let result = run_verify_with_lock_mode(
            &package,
            PackageChecker::Reference,
            PackageLockInputMode::ReconstructedInMemory,
        );

        assert_failure(
            &result,
            DiagnosticKind::HashMismatch,
            reason,
            Some(&format!("imports[0].{field}")),
            Some(field),
        );
    }
}

#[test]
fn package_verify_certs_reconstructed_rejects_missing_local_certificate_import() {
    let package = build_source_free_modules_fixture(
        "reconstructed-local-import",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec"],
    );
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
    replace_manifest_text_once(
        &package,
        "imports = [\"Std.Logic.Eq\", \"Proofs.Ai.EqReasoning\"]",
        "imports = [\"Std.Logic.Eq\", \"Proofs.Ai.EqReasoning\", \"Proofs.Ai.Basic\"]",
    );

    let result = run_verify_with_lock_mode(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
    );

    assert_failure(
        &result,
        DiagnosticKind::PackageGraph,
        "certificate_import_missing",
        Some("modules[2].imports[2]"),
        Some("module"),
    );
    assert_eq!(
        result.diagnostics[0].module.as_deref(),
        Some("Proofs.Ai.Analysis.AbstractMetricTopology")
    );
}

#[test]
fn package_verify_certs_reconstructed_uses_normal_graph_and_policy_validation() {
    let graph_package = build_source_free_fixture(
        "reconstructed-graph-policy-graph",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    fs::remove_file(graph_package.artifact_path(LOCK_PATH)).unwrap();
    replace_manifest_line(
        &graph_package,
        "imports",
        "imports = [\"Missing.Dependency\"]",
    );
    let graph_result = run_verify_with_lock_mode(
        &graph_package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
    );
    assert_failure(
        &graph_result,
        DiagnosticKind::PackageGraph,
        "unknown_import",
        Some("modules[0].imports[0]"),
        Some("imports"),
    );

    let policy_package = build_source_free_fixture(
        "reconstructed-graph-policy-policy",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    fs::remove_file(policy_package.artifact_path(LOCK_PATH)).unwrap();
    replace_manifest_line(
        &policy_package,
        "axioms",
        "axioms = [\"Policy.Disallowed\"]",
    );
    let policy_result = run_verify_with_lock_mode(
        &policy_package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
    );
    assert_failure(
        &policy_result,
        DiagnosticKind::PackageManifest,
        "disallowed_axiom",
        Some("modules[0].axioms[0]"),
        Some("axioms"),
    );
}

#[test]
fn package_verify_certs_changed_verifies_changed_certificate_path_source_free() {
    let package = build_source_free_modules_fixture(
        "changed-certificate-source-free",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec"],
    );
    assert!(!package.artifact_path("Proofs/Ai/Basic/source.npa").exists());
    assert!(!package
        .artifact_path("Proofs/Ai/EqReasoning/source.npa")
        .exists());
    assert!(!package
        .artifact_path("Proofs/Ai/Analysis/AbstractMetricTopology/source.npa")
        .exists());
    init_git_baseline(&package);
    stage_worktree_mode_changed(&package, "Proofs/Ai/EqReasoning/certificate.npcert");

    let result = run_verify_changed(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let verified_modules = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .map(|diagnostic| diagnostic.module.as_deref().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        verified_modules,
        vec!["Std.Logic.Eq", "Proofs.Ai.EqReasoning"]
    );
}

#[test]
fn package_verify_certs_changed_reconstructed_preserves_certificate_selection() {
    let mut package = build_source_free_modules_fixture(
        "changed-reconstructed-certificate-selection",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec"],
    );
    let lock_hash = checked_lock_hash(&package);
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
    nest_package_in_worktree(&mut package, "packages/proofs");
    let mut forbidden = Vec::new();
    for module_dir in [
        "Proofs/Ai/Basic",
        "Proofs/Ai/EqReasoning",
        "Proofs/Ai/Analysis/AbstractMetricTopology",
    ] {
        forbidden.extend(install_non_input_sentinels(&package, module_dir));
    }
    forbidden.sort();
    forbidden.dedup();
    init_git_worktree_baseline(&package);
    stage_worktree_mode_changed(&package, "Proofs/Ai/EqReasoning/certificate.npcert");

    let result = run_guarded_read_only_verify(
        &package,
        verify_changed_certificates(
            common_options(package.path(), true),
            PackageChecker::Reference,
        )
        .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory),
        &expected_in_process_inputs(
            PackageLockInputMode::ReconstructedInMemory,
            &[
                "Proofs/Ai/Basic/certificate.npcert",
                "Proofs/Ai/EqReasoning/certificate.npcert",
                "Proofs/Ai/Analysis/AbstractMetricTopology/certificate.npcert",
                "vendor/npa-std/Std/Logic/Eq/certificate.npcert",
            ],
        ),
        &forbidden,
        "reconstructed-changed-only",
    );

    assert_eq!(
        result.exit_code(),
        CommandExitCode::Success,
        "{}",
        result.render_json()
    );
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        lock_hash,
    );
    let verified_modules = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .map(|diagnostic| diagnostic.module.as_deref().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        verified_modules,
        vec!["Std.Logic.Eq", "Proofs.Ai.EqReasoning"]
    );
    assert!(!package.artifact_path(LOCK_PATH).exists());
}

#[test]
fn package_verify_certs_changed_preserves_untracked_and_unborn_selection() {
    for state in ["untracked", "unborn"] {
        let mut package = build_source_free_fixture(
            &format!("changed-{state}-certificate"),
            "Proofs.Ai.Basic",
            false,
            &["Eq.rec"],
        );
        nest_package_in_worktree(&mut package, "packages/proofs");
        let forbidden = install_non_input_sentinels(&package, "Proofs/Ai/Basic");
        let certificate = package.artifact_path("Proofs/Ai/Basic/certificate.npcert");
        if state == "untracked" {
            let certificate_bytes = fs::read(&certificate).unwrap();
            fs::remove_file(&certificate).unwrap();
            init_git_worktree_baseline(&package);
            fs::write(&certificate, certificate_bytes).unwrap();
        } else {
            run_git_at(package.cleanup_path(), &["init", "-q"]);
        }

        let result = run_guarded_read_only_verify(
            &package,
            verify_changed_certificates(
                common_options(package.path(), true),
                PackageChecker::Reference,
            ),
            &expected_in_process_inputs(
                PackageLockInputMode::CheckedFile,
                &["Proofs/Ai/Basic/certificate.npcert"],
            ),
            &forbidden,
            state,
        );

        assert_eq!(
            result.exit_code(),
            CommandExitCode::Success,
            "{state}: {}",
            result.render_json()
        );
        assert_eq!(
            verified_module_identities(&result),
            vec![(
                "Proofs.Ai.Basic".to_owned(),
                "Proofs/Ai/Basic/certificate.npcert".to_owned(),
            )],
            "{state}"
        );
    }
}

#[test]
fn package_verify_certs_changed_ignores_staged_certificate_when_worktree_restored_source_free() {
    let package = build_source_free_modules_fixture(
        "changed-certificate-index-only-source-free",
        &["Proofs.Ai.Basic", "Proofs.Ai.EqReasoning"],
        &["Eq.rec"],
    );
    init_git_baseline(&package);
    stage_changed_then_restore(
        &package,
        "Proofs/Ai/EqReasoning/certificate.npcert",
        b"\nchanged-index-bytes",
    );

    let result = run_verify_changed(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "module_verified"));
    let aggregate = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_verified")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("package aggregate diagnostic");
    assert!(aggregate.contains("modules=0"));
}

#[test]
fn package_verify_certs_changed_verifies_nested_package_certificate_path_source_free() {
    let mut package = build_source_free_modules_fixture(
        "changed-certificate-nested-source-free",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec"],
    );
    nest_package_in_worktree(&mut package, "packages/proofs space");
    init_git_worktree_baseline(&package);
    mark_worktree_mode_changed(&package, "Proofs/Ai/EqReasoning/certificate.npcert");

    let result = run_verify_changed(&package, PackageChecker::Reference);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let verified_modules = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .map(|diagnostic| diagnostic.module.as_deref().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        verified_modules,
        vec!["Std.Logic.Eq", "Proofs.Ai.EqReasoning"]
    );
}

#[test]
fn package_verify_certs_fast_cli_succeeds_with_json_and_human_provenance() {
    let package = build_source_free_fixture("cli-fast", "Proofs.Ai.Basic", false, &["Eq.rec"]);

    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--root"])
        .arg(package.path())
        .args(["--checker", "fast", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"npa.package.command_result.v0.3\""));
    assert!(stdout.contains("\"command\":\"package verify-certs\""));
    assert!(stdout.contains("\"status\":\"passed\""));
    assert!(stdout.contains("\"kind\":\"FastVerifier\""));
    assert!(stdout.contains("\"reason_code\":\"package_verified\""));
    assert!(stdout.contains("\"reason_code\":\"package_lock_checked\""));
    assert!(stdout.contains("\"field\":\"package_lock\""));
    assert!(stdout.contains("\"actual_value\":\"mode=checked;hash=sha256:"));
    assert!(stdout.contains("\"checker\":\"fast-kernel-certificate-verifier\""));
    assert!(!stdout.contains(&package.path().to_string_lossy().to_string()));

    let human = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--root"])
        .arg(package.path())
        .args(["--checker", "fast"])
        .output()
        .unwrap();
    assert_eq!(human.status.code(), Some(0));
    assert!(human.stderr.is_empty());
    let human_stdout = String::from_utf8(human.stdout).unwrap();
    assert!(human_stdout.contains("info PackageLock package_lock_checked"));
    assert!(human_stdout.contains("field=package_lock"));
    assert!(human_stdout.contains("actual=mode=checked;hash=sha256:"));
}

#[test]
fn package_verify_external_succeeds_with_explicit_policy_registry_imports_and_no_source() {
    let package =
        build_source_free_fixture("external-source-free", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let lock_hash = checked_lock_hash(&package);
    assert!(!package.artifact_path("Proofs/Ai/Eq/source.npa").exists());
    assert!(package
        .artifact_path("vendor/npa-std/Std/Logic/Eq/certificate.npcert")
        .exists());
    let external = write_external_runner_fixture(&package, true);

    let result = run_verify_external(&package, external);

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    assert_eq!(result.artifacts.len(), 3);
    assert!(result
        .artifacts
        .iter()
        .all(|artifact| artifact.kind == "machine_check_result"));
    assert!(result.artifacts.iter().any(|artifact| artifact.path
        == "generated/checker-results/fixture-package/0.1.0/Proofs.Ai.Eq/external/result.json"));
    assert!(result.artifacts.iter().any(|artifact| artifact.path
        == "generated/checker-results/fixture-package/0.1.0/Std.Logic.Eq/external/result.json"));
    assert!(
        package
            .artifact_path(
                "generated/checker-imports/fixture-package/0.1.0/Proofs.Ai.Eq/external/vendor/npa-std/Std/Logic/Eq/certificate.npcert"
            )
            .exists()
    );
    assert!(result
        .artifacts
        .iter()
        .all(|artifact| package.artifact_path(&artifact.path).exists()));
    assert_eq!(result.diagnostics.len(), 5);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::ExternalVerifier,
        "package_verified",
        Some("npa-checker-ext"),
    );
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert_eq!(result.diagnostics[2].reason_code, "module_verified");
    assert!(result.diagnostics[0]
        .actual_value
        .as_deref()
        .unwrap()
        .contains("mode=external"));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.reason_code == "module_verified")
            .count(),
        3
    );
    let local_result = result
        .artifacts
        .iter()
        .find(|artifact| artifact.path.contains("Proofs.Ai.Eq"))
        .unwrap();
    let result_json = fs::read_to_string(package.artifact_path(&local_result.path)).unwrap();
    assert!(result_json.contains("\"schema\":\"npa.independent-checker.machine_check_result.v1\""));
    assert!(result_json.contains("\"profile\":\"external\""));
    assert!(result_json.contains("\"status\":\"checked\""));
    assert!(!result
        .render_json()
        .contains(&package.path().to_string_lossy().to_string()));
}

#[test]
fn package_verify_external_rejects_unknown_axiom_policy_override_after_hash_validation() {
    let package = build_source_free_fixture(
        "external-invalid-axiom-policy",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let mut external = write_external_runner_fixture(&package, true);
    let lock_hash = checked_lock_hash(&package);

    let axiom_policy_path = package.artifact_path("ci/axiom-policy.toml");
    let old_axiom_policy = fs::read(&axiom_policy_path).unwrap();
    let old_axiom_policy_hash = independent_checker_file_hash(&old_axiom_policy);
    let invalid_axiom_policy = b"format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = [\"Eq.rec\"]\ndeny_custom_axioms = false\n";
    fs::write(&axiom_policy_path, invalid_axiom_policy).unwrap();
    let invalid_axiom_policy_hash = independent_checker_file_hash(invalid_axiom_policy);

    let runner_policy_path = package.artifact_path("ci/runner.release.json");
    let runner_policy_source = fs::read_to_string(&runner_policy_path).unwrap().replace(
        &format_hash_string(&old_axiom_policy_hash),
        &format_hash_string(&invalid_axiom_policy_hash),
    );
    let runner_policy_hash = parse_independent_checker_runner_policy(&runner_policy_source)
        .unwrap()
        .policy_hash();
    fs::write(&runner_policy_path, runner_policy_source).unwrap();
    external.runner_policy_hash = format_hash_string(&runner_policy_hash);

    let result = run_verify_external(&package, external);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::PackagePolicy);
    assert_eq!(diagnostic.reason_code, "axiom_policy_invalid");
    assert_eq!(
        diagnostic.field.as_deref(),
        Some("axiom_policy.deny_custom_axioms")
    );
    assert_eq!(diagnostic.expected_value.as_deref(), Some("absent"));
    assert_eq!(diagnostic.actual_value.as_deref(), Some("unknown_field"));
    assert_eq!(diagnostic.checker.as_deref(), Some("npa-checker-ext"));
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
}

#[test]
#[ignore = "requires NPA_CHECKER_EXT_BINARY_PATH built by the OCaml gate"]
fn package_verify_external_real_ocaml_checker_closes_source_free_import_dag() {
    let package =
        build_source_free_fixture("external-real-ocaml", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let lock_hash = checked_lock_hash(&package);
    let lock_source = fs::read_to_string(package.artifact_path(LOCK_PATH)).unwrap();
    let lock = parse_package_lock_json(&lock_source).unwrap();
    let checker_path = std::env::var_os("NPA_CHECKER_EXT_BINARY_PATH")
        .map(PathBuf::from)
        .expect("NPA_CHECKER_EXT_BINARY_PATH must name the built OCaml checker");
    let fixture = write_real_external_runner_fixture(&package, &checker_path);

    let result = run_verify_external(&package, fixture.options);

    assert_eq!(
        result.exit_code(),
        CommandExitCode::Success,
        "{}",
        result.render_json()
    );
    assert_eq!(result.diagnostics.len(), lock.entries.len() + 2);
    assert_info(
        &result.diagnostics[0],
        DiagnosticKind::ExternalVerifier,
        "package_verified",
        Some("npa-checker-ext"),
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some(
            format!(
                "mode=external;verdict_source=npa-checker-ext;reference_checker_verdict=false;modules={}",
                lock.entries.len()
            )
            .as_str()
        )
    );
    assert_eq!(lock_provenance_count(&result), 1);
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert_eq!(result.artifacts.len(), lock.entries.len());
    assert!(result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .all(|diagnostic| diagnostic.checker.as_deref() == Some("npa-checker-ext")));

    for artifact in &result.artifacts {
        assert_eq!(artifact.kind, "machine_check_result");
        let module = artifact
            .path
            .strip_prefix("generated/checker-results/fixture-package/0.1.0/")
            .and_then(|path| path.strip_suffix("/external/result.json"))
            .expect("real checker result must use the deterministic external layout");
        let entry = lock
            .entries
            .iter()
            .find(|entry| entry.module.as_dotted() == module)
            .expect("every result module must come from the checked lock");
        let machine = fs::read_to_string(package.artifact_path(&artifact.path)).unwrap();
        assert!(machine.contains("\"schema\":\"npa.independent-checker.machine_check_result.v1\""));
        assert!(machine.contains(&format!("\"module\":\"{}\"", entry.module.as_dotted())));
        assert!(machine.contains("\"status\":\"checked\""));
        assert!(machine.contains(&format!(
            "\"certificate_hash\":\"{}\"",
            format_package_hash(&entry.certificate_hash)
        )));
        assert!(machine.contains(&format!(
            "\"export_hash\":\"{}\"",
            format_package_hash(&entry.export_hash)
        )));
        assert!(machine.contains(&format!(
            "\"axiom_report_hash\":\"{}\"",
            format_package_hash(&entry.axiom_report_hash)
        )));
        assert!(machine.contains(&format!(
            "\"checker\":{{\"binary_hash\":\"{}\",\"binary_id\":\"npa-checker-ext-macos-aarch64\",\"build_hash\":\"{}\",\"id\":\"npa-checker-ext\",\"profile\":\"external\",\"version\":\"0.2.0\"}}",
            fixture.binary_hash, fixture.build_hash
        )));
        assert!(machine.contains(&format!(
            "\"policy\":{{\"hash\":\"{}\",\"id\":\"package-external-pr\",\"version\":1}}",
            fixture.policy_hash
        )));
        assert!(machine.contains(&format!(
            "\"runner\":{{\"build_hash\":\"{}\",\"id\":\"npa-cli-package-external-runner\",\"version\":\"0.1.0\"}}",
            fixture.runner_build_hash
        )));
        assert!(machine.contains("\"process\":{\"exit_code\":0,\"launched\":true}"));
        assert!(machine.contains("\"resource_usage\":{\"elapsed_ms\":"));
        assert!(machine.contains("\"memory_peak_mb\":0,\"steps\":0}"));

        let raw_hex = json_string_field_for_test(&machine, "raw_checker_output_hex");
        let raw = String::from_utf8(decode_lower_hex_for_test(raw_hex)).unwrap();
        assert!(raw.ends_with('\n'));
        assert!(raw.contains("\"schema\": \"npa.independent-checker.checker_raw_result.v1\""));
        assert!(raw.contains("\"checker_id\": \"npa-checker-ext\""));
        assert!(raw.contains("\"checker_version\": \"0.2.0\""));
        assert!(raw.contains(&format!(
            "\"checker_build_hash\": \"{}\"",
            fixture.build_hash
        )));
        assert!(raw.contains(&format!("\"module\": \"{}\"", entry.module.as_dotted())));
        assert!(raw.contains(&format!(
            "\"certificate_hash\": \"{}\"",
            format_package_hash(&entry.certificate_hash)
        )));
    }
}

#[test]
fn package_verify_external_rejects_missing_checker_binary_with_structured_diagnostic() {
    let package = build_source_free_fixture(
        "external-missing-binary",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let lock_hash = checked_lock_hash(&package);
    let external = write_external_runner_fixture(&package, false);

    let result = run_verify_external(&package, external);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::ArtifactIo);
    assert_eq!(diagnostic.reason_code, "checker_binary_file_unreadable");
    assert_eq!(
        diagnostic.path.as_deref(),
        Some("tools/checkers/npa-checker-ext")
    );
    assert!(diagnostic.checker.is_none());
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert!(!result.render_json().contains("/tmp/"));
}

#[test]
fn package_verify_external_requires_explicit_policy_and_registry() {
    let output = Command::new(env!("CARGO_BIN_EXE_npa"))
        .args(["package", "verify-certs", "--checker", "external", "--json"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"command\":\"package verify-certs\""));
    assert!(stdout.contains("\"kind\":\"Usage\""));
    assert!(stdout.contains("\"reason_code\":\"missing_required_flag\""));
    assert!(stdout.contains("\"field\":\"--runner-policy\""));
}

#[test]
fn package_verify_certs_rejects_stale_package_lock_before_checker_status() {
    let package = build_source_free_fixture("stale-lock", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let lock_path = package.artifact_path(LOCK_PATH);
    let mut lock_source = fs::read_to_string(&lock_path).unwrap();
    lock_source.push('\n');
    fs::write(lock_path, lock_source).unwrap();

    let result = run_verify(&package, PackageChecker::Reference);

    assert_failure(
        &result,
        DiagnosticKind::HashMismatch,
        "package_lock_stale",
        Some(LOCK_PATH),
        None,
    );
    assert!(!result.render_json().contains("module_verified"));
    assert!(!result.render_json().contains("package_verified"));
}

#[test]
fn package_verify_certs_rejects_stale_certificate_hash_before_checker_status() {
    let package =
        build_source_free_fixture("stale-certificate", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    fs::write(
        package.artifact_path("Proofs/Ai/Basic/certificate.npcert"),
        fs::read(repo_root().join("testdata/package/proofs/Proofs/Ai/Prop/certificate.npcert"))
            .unwrap(),
    )
    .unwrap();
    let before = package_tree_snapshot(&package);

    let result = run_verify(&package, PackageChecker::Reference);

    assert_failure(
        &result,
        DiagnosticKind::HashMismatch,
        "certificate_file_hash_mismatch",
        Some("modules[0].expected_certificate_file_hash"),
        Some("expected_certificate_file_hash"),
    );
    assert!(!result.render_json().contains("module_verified"));
    assert!(!result.render_json().contains("package_verified"));
    assert_eq!(package_tree_snapshot(&package), before);
    assert!(package.artifact_path(LOCK_PATH).is_file());
}

#[test]
fn package_verify_certs_reference_preserves_checker_rejection_and_lock_provenance() {
    let mut package =
        build_source_free_fixture("reference-rejection", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);
    let lock_hash = checked_lock_hash(&package);
    nest_package_in_worktree(&mut package, "proofs");
    let forbidden = install_non_input_sentinels(&package, "Proofs/Ai/Eq");
    init_git_worktree_baseline(&package);
    let certificate_inputs = [
        "Proofs/Ai/Eq/certificate.npcert",
        "vendor/npa-std/Std/Logic/Eq/certificate.npcert",
        "vendor/npa-std/Std/Nat/Basic/certificate.npcert",
    ];

    let result = run_guarded_read_only_verify(
        &package,
        verify_certs_full(
            common_options(package.path(), true),
            PackageChecker::Reference,
        ),
        &expected_in_process_inputs(PackageLockInputMode::CheckedFile, &certificate_inputs),
        &forbidden,
        "checked-post-lock-checker-failure",
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::ReferenceVerifier);
    assert_eq!(diagnostic.reason_code, "reference_checker_rejected");
    assert_eq!(diagnostic.checker.as_deref(), Some("npa-checker-ref"));
    assert_eq!(diagnostic.field.as_deref(), Some("certificate"));
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Eq"));
    let actual = diagnostic.actual_value.as_deref().unwrap();
    assert!(actual.contains("NonCanonical"), "{actual}");
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert!(!result.render_json().contains("module_verified"));
    assert!(!result.render_json().contains("package_verified"));

    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
    let reconstructed = run_guarded_read_only_verify(
        &package,
        verify_certs_full(
            common_options(package.path(), true),
            PackageChecker::Reference,
        )
        .with_package_lock_mode(PackageLockInputMode::ReconstructedInMemory),
        &expected_in_process_inputs(
            PackageLockInputMode::ReconstructedInMemory,
            &certificate_inputs,
        ),
        &forbidden,
        "reconstructed-post-lock-checker-failure",
    );
    assert_eq!(reconstructed.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(reconstructed.diagnostics.len(), 2);
    assert_eq!(
        reconstructed.diagnostics[0].reason_code,
        "reference_checker_rejected"
    );
    assert_lock_provenance(
        &reconstructed.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        lock_hash,
    );
}

#[test]
fn package_verify_certs_audit_cache_read_through_writes_then_hits() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "audit-cache-read-through",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Audit.Cache.Unique"],
    );

    let first = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let first_summary = audit_cache_summary(&first);
    assert!(first_summary.contains("mode=read-through"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("written=1"));
    assert!(first_summary.contains("live_checked=1"));
    assert!(first_summary.contains("cached=0"));
    assert!(first_summary.contains("trusted=false"));
    assert_eq!(audit_cache_entries().len(), 1);
    let entry_source = fs::read_to_string(&audit_cache_entries()[0]).unwrap();
    let entry = parse_package_audit_result_entry_json(&entry_source).unwrap();
    assert!(!entry.trusted);

    let second = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    let second_summary = audit_cache_summary(&second);
    assert!(second_summary.contains("hits=1"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("written=0"));
    assert!(second_summary.contains("cached=1"));
}

#[test]
fn package_verify_certs_audit_cache_keys_canonical_lock_and_refreshes_mode_provenance() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "audit-cache-cross-lock-mode",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.AuditCache.Identity"],
    );
    let canonical_hash = checked_lock_hash(&package);

    let warm = run_verify_with_lock_mode_and_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::CheckedFile,
        PackageAuditCacheMode::ReadThrough,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &warm.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        canonical_hash,
    );
    assert_eq!(warm.diagnostics[2].reason_code, "module_verified");
    assert_eq!(warm.diagnostics[3].reason_code, "audit_cache_summary");
    assert!(audit_cache_summary(&warm).contains("hits=0"));
    assert_eq!(audit_cache_entries().len(), 1);
    let warm_entry = parse_package_audit_result_entry_json(
        &fs::read_to_string(&audit_cache_entries()[0]).unwrap(),
    )
    .unwrap();
    assert_eq!(warm_entry.key_input.package_lock_hash, canonical_hash);

    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
    let cross_mode_hit = run_verify_with_lock_mode_and_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageAuditCacheMode::LocalHit,
    );
    assert_eq!(cross_mode_hit.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &cross_mode_hit.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        canonical_hash,
    );
    assert_eq!(cross_mode_hit.diagnostics[2].reason_code, "module_verified");
    assert_eq!(
        cross_mode_hit.diagnostics[3].reason_code,
        "audit_cache_summary"
    );
    let hit_summary = audit_cache_summary(&cross_mode_hit);
    assert!(hit_summary.contains("hits=1"), "{hit_summary}");
    assert!(hit_summary.contains("cached=1"), "{hit_summary}");
    assert!(hit_summary.contains("live_checked=0"), "{hit_summary}");
    assert_eq!(lock_provenance_count(&cross_mode_hit), 1);

    let relocated = build_source_free_fixture(
        "audit-cache-relocated-identical-lock",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.AuditCache.Identity"],
    );
    assert_eq!(checked_lock_hash(&relocated), canonical_hash);
    fs::remove_file(relocated.artifact_path(LOCK_PATH)).unwrap();
    let relocated_hit = run_verify_with_lock_mode_and_audit_cache(
        &relocated,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageAuditCacheMode::LocalHit,
    );
    assert_eq!(relocated_hit.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &relocated_hit.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        canonical_hash,
    );
    let relocated_summary = audit_cache_summary(&relocated_hit);
    assert!(relocated_summary.contains("hits=1"), "{relocated_summary}");
    assert!(
        relocated_summary.contains("cached=1"),
        "{relocated_summary}"
    );

    let changed = build_source_free_fixture(
        "audit-cache-different-canonical-lock",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.AuditCache.Identity"],
    );
    append_manifest_comment_and_write_lock(&changed, "canonical lock identity change");
    let changed_hash = checked_lock_hash(&changed);
    assert_ne!(changed_hash, canonical_hash);
    fs::remove_file(changed.artifact_path(LOCK_PATH)).unwrap();

    let changed_miss = run_verify_with_lock_mode_and_audit_cache(
        &changed,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageAuditCacheMode::LocalHit,
    );
    assert_eq!(changed_miss.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &changed_miss.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        changed_hash,
    );
    assert_eq!(changed_miss.diagnostics[2].reason_code, "module_verified");
    assert_eq!(
        changed_miss.diagnostics[3].reason_code,
        "audit_cache_summary"
    );
    let miss_summary = audit_cache_summary(&changed_miss);
    assert!(miss_summary.contains("hits=0"), "{miss_summary}");
    assert!(miss_summary.contains("misses=1"), "{miss_summary}");
    assert!(miss_summary.contains("cached=0"), "{miss_summary}");
    assert!(miss_summary.contains("trusted=false"), "{miss_summary}");
    clear_audit_cache();
}

#[test]
fn package_verify_certs_audit_cache_read_through_preserves_live_checker_failure() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package =
        build_source_free_fixture("audit-cache-failure", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);
    let lock_hash = checked_lock_hash(&package);

    let result = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "reference_checker_rejected"
    );
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert_eq!(result.diagnostics[2].reason_code, "audit_cache_summary");
    let summary = audit_cache_summary(&result);
    assert!(summary.contains("mode=read-through"));
    assert!(summary.contains("trusted=false"));
    assert!(!result
        .render_json()
        .contains("\"reason_code\":\"package_verified\""));
}

#[test]
fn package_verify_certs_audit_cache_external_read_through_is_rejected() {
    let _guard = audit_cache_test_lock();
    let package = build_source_free_fixture(
        "audit-cache-external",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let external = write_external_runner_fixture(&package, true);

    let result = run_package_verify_certs(
        verify_certs_full(
            common_options(package.path(), true),
            PackageChecker::External,
        )
        .with_audit_cache(PackageAuditCacheMode::ReadThrough)
        .with_external(external),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--audit-cache")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("read-through")
    );
}

#[test]
fn package_verify_certs_local_hit_marks_proof_evidence_false_and_follow_up() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "local-hit-proof-evidence",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let warm = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);

    let local = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::LocalHit,
    );

    assert_eq!(local.exit_code(), CommandExitCode::Success);
    let aggregate = local
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_verified")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("package aggregate diagnostic");
    assert!(aggregate.contains("reference_checker_verdict=false"));
    assert!(aggregate.contains("locally_accelerated=true"));
    let module = local
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "module_verified")
        .expect("module diagnostic");
    assert_eq!(
        module.actual_value.as_deref(),
        Some("status=passed;evidence=local-audit-cache;proof_evidence=false")
    );
    let summary = audit_cache_summary(&local);
    assert!(summary.contains("mode=local-hit"));
    assert!(summary.contains("hits=1"));
    assert!(summary.contains("cached=1"));
    assert!(summary.contains("live_checked=0"));
    let follow_up = audit_cache_follow_up(&local);
    assert!(follow_up.contains("proof_evidence=false"));
    assert!(follow_up.contains("--audit-cache off"));
    assert!(follow_up.contains("--checker reference"));
}

#[test]
fn package_verify_certs_local_hit_does_not_mask_live_miss_failure() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package =
        build_source_free_fixture("local-hit-miss-failure", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::LocalHit,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
    let summary = audit_cache_summary(&result);
    assert!(summary.contains("mode=local-hit"));
    assert!(summary.contains("cached=0"));
    assert!(summary.contains("trusted=false"));
    assert!(result
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "audit_cache_follow_up"));
    assert!(!result
        .render_json()
        .contains("\"reason_code\":\"package_verified\""));
}

#[test]
fn package_verify_certs_local_hit_live_checks_cached_dependency_needed_by_live_dependent() {
    let _guard = audit_cache_test_lock();
    clear_audit_cache();
    let package = build_source_free_fixture(
        "local-hit-live-dependency",
        "Proofs.Ai.Eq",
        true,
        &["Eq.rec"],
    );
    let warm = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::ReadThrough,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    remove_audit_cache_entries_for_module("Proofs.Ai.Eq");

    let local = run_verify_with_audit_cache(
        &package,
        PackageChecker::Reference,
        PackageAuditCacheMode::LocalHit,
    );

    assert_eq!(local.exit_code(), CommandExitCode::Success);
    let summary = audit_cache_summary(&local);
    assert!(summary.contains("mode=local-hit"));
    assert!(summary.contains("cached=0"));
    assert!(!summary.contains("live_checked=0"));
    assert!(local.diagnostics.iter().all(|diagnostic| {
        diagnostic.actual_value.as_deref()
            != Some("status=passed;evidence=local-audit-cache;proof_evidence=false")
    }));
    assert!(local
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "audit_cache_follow_up"));
}

#[test]
fn package_verify_certs_local_hit_external_is_rejected() {
    let _guard = audit_cache_test_lock();
    let package =
        build_source_free_fixture("local-hit-external", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let external = write_external_runner_fixture(&package, true);

    let result = run_package_verify_certs(
        verify_certs_full(
            common_options(package.path(), true),
            PackageChecker::External,
        )
        .with_audit_cache(PackageAuditCacheMode::LocalHit)
        .with_external(external),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--audit-cache")
    );
    assert_eq!(
        result.diagnostics[0].actual_value.as_deref(),
        Some("local-hit")
    );
}

#[test]
fn package_verify_certs_local_hit_does_not_run_from_package_gate_scripts() {
    let package_gate = fs::read_to_string(corpus_script_path("check-corpus-package.sh"))
        .expect("package gate script");
    let full_gate =
        fs::read_to_string(corpus_script_path("check-corpus-full.sh")).expect("full gate script");

    assert!(!package_gate.contains("--audit-cache"));
    assert!(!full_gate.contains("--audit-cache"));
    assert!(!package_gate.contains("--verifier-memo"));
    assert!(!full_gate.contains("--verifier-memo"));
    assert!(full_gate.contains("scripts/check-corpus-package.sh"));
}

#[test]
fn package_verify_certs_reconstructed_supports_verifier_memo_settings() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "reconstructed-verifier-memo-settings",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.ReconstructedMemo.Settings"],
    );
    let lock_hash = checked_lock_hash(&package);
    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();

    let off = run_verify_with_lock_mode_and_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageVerifierMemoMode::Off,
        PackageTimingMode::Summary,
    );
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &off.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        lock_hash,
    );
    assert!(off
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "disk_memo_summary"));

    for mode in [
        PackageVerifierMemoMode::ReadThrough,
        PackageVerifierMemoMode::Disk,
    ] {
        clear_disk_memo();
        let result = run_verify_with_lock_mode_and_verifier_memo(
            &package,
            PackageChecker::Reference,
            PackageLockInputMode::ReconstructedInMemory,
            mode,
            PackageTimingMode::Summary,
        );
        assert_eq!(
            result.exit_code(),
            CommandExitCode::Success,
            "{}: {}",
            mode.as_str(),
            result.render_json()
        );
        assert_lock_provenance(
            &result.diagnostics[1],
            PackageLockInputMode::ReconstructedInMemory,
            lock_hash,
        );
        let summary = disk_memo_summary(&result);
        assert!(
            summary.contains(&format!("mode={}", mode.as_str())),
            "{summary}"
        );
        assert!(summary.contains("trusted=false"), "{summary}");
        assert!(summary.contains("proof_evidence=false"), "{summary}");
    }
    assert!(!package.artifact_path(LOCK_PATH).exists());
    clear_disk_memo();
}

#[test]
fn package_verify_certs_disk_memo_keys_canonical_lock_and_refreshes_mode_provenance() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "disk-memo-cross-lock-mode",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.DiskMemo.Identity"],
    );
    let canonical_hash = checked_lock_hash(&package);

    let warm = run_verify_with_lock_mode_and_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::CheckedFile,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &warm.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        canonical_hash,
    );
    assert_eq!(warm.diagnostics[2].reason_code, "module_verified");
    assert_eq!(warm.diagnostics[3].reason_code, "disk_memo_summary");
    let warm_summary = disk_memo_summary(&warm);
    assert!(warm_summary.contains("hits=0"), "{warm_summary}");
    assert!(warm_summary.contains("written=1"), "{warm_summary}");
    assert_eq!(disk_memo_entries().len(), 1);
    let warm_entry = parse_package_audit_disk_memo_result_entry_json(
        &fs::read_to_string(&disk_memo_entries()[0]).unwrap(),
    )
    .unwrap();
    assert_eq!(warm_entry.key_input.package_lock_hash, canonical_hash);
    assert!(warm.timings.is_some());

    fs::remove_file(package.artifact_path(LOCK_PATH)).unwrap();
    let cross_mode_hit = run_verify_with_lock_mode_and_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(cross_mode_hit.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &cross_mode_hit.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        canonical_hash,
    );
    assert_eq!(cross_mode_hit.diagnostics[2].reason_code, "module_verified");
    assert_eq!(
        cross_mode_hit.diagnostics[3].reason_code,
        "disk_memo_summary"
    );
    let hit_summary = disk_memo_summary(&cross_mode_hit);
    assert!(hit_summary.contains("hits=1"), "{hit_summary}");
    assert!(hit_summary.contains("cached=1"), "{hit_summary}");
    assert!(hit_summary.contains("live_checked=0"), "{hit_summary}");
    assert!(hit_summary.contains("trusted=false"), "{hit_summary}");
    assert!(
        hit_summary.contains("proof_evidence=false"),
        "{hit_summary}"
    );
    assert_eq!(lock_provenance_count(&cross_mode_hit), 1);
    assert_eq!(disk_memo_entries().len(), 1);

    let relocated = build_source_free_fixture(
        "disk-memo-relocated-identical-lock",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.DiskMemo.Identity"],
    );
    assert_eq!(checked_lock_hash(&relocated), canonical_hash);
    fs::remove_file(relocated.artifact_path(LOCK_PATH)).unwrap();
    let relocated_hit = run_verify_with_lock_mode_and_verifier_memo(
        &relocated,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(relocated_hit.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &relocated_hit.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        canonical_hash,
    );
    let relocated_summary = disk_memo_summary(&relocated_hit);
    assert!(relocated_summary.contains("hits=1"), "{relocated_summary}");
    assert!(
        relocated_summary.contains("cached=1"),
        "{relocated_summary}"
    );
    assert_eq!(disk_memo_entries().len(), 1);

    let changed = build_source_free_fixture(
        "disk-memo-different-canonical-lock",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "Pav.DiskMemo.Identity"],
    );
    append_manifest_comment_and_write_lock(&changed, "canonical lock identity change");
    let changed_hash = checked_lock_hash(&changed);
    assert_ne!(changed_hash, canonical_hash);
    fs::remove_file(changed.artifact_path(LOCK_PATH)).unwrap();

    let changed_miss = run_verify_with_lock_mode_and_verifier_memo(
        &changed,
        PackageChecker::Reference,
        PackageLockInputMode::ReconstructedInMemory,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(changed_miss.exit_code(), CommandExitCode::Success);
    assert_lock_provenance(
        &changed_miss.diagnostics[1],
        PackageLockInputMode::ReconstructedInMemory,
        changed_hash,
    );
    assert_eq!(changed_miss.diagnostics[2].reason_code, "module_verified");
    assert_eq!(changed_miss.diagnostics[3].reason_code, "disk_memo_summary");
    let miss_summary = disk_memo_summary(&changed_miss);
    assert!(miss_summary.contains("hits=0"), "{miss_summary}");
    assert!(miss_summary.contains("misses=1"), "{miss_summary}");
    assert!(miss_summary.contains("cached=0"), "{miss_summary}");
    assert!(miss_summary.contains("written=1"), "{miss_summary}");
    let memo_hashes = disk_memo_entries()
        .iter()
        .map(|path| {
            parse_package_audit_disk_memo_result_entry_json(&fs::read_to_string(path).unwrap())
                .unwrap()
                .key_input
                .package_lock_hash
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(memo_hashes, BTreeSet::from([canonical_hash, changed_hash]));
    clear_disk_memo();
}

#[test]
fn package_verify_certs_disk_memo_writes_hits_and_delete_reruns_live() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "disk-memo-hit",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "DiskMemo.Unique"],
    );
    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);

    let first = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let first_summary = disk_memo_summary(&first);
    assert!(first_summary.contains("mode=disk"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("written=1"));
    assert!(first_summary.contains("live_checked=1"));
    assert!(first_summary.contains("cached=0"));
    assert!(first_summary.contains("trusted=false"));
    assert!(first_summary.contains("proof_evidence=false"));
    assert_eq!(disk_memo_entries().len(), 1);
    let entry_source = fs::read_to_string(&disk_memo_entries()[0]).unwrap();
    let entry = parse_package_audit_disk_memo_result_entry_json(&entry_source).unwrap();
    assert!(!entry.trusted);
    assert!(!entry.proof_evidence);
    assert_eq!(
        without_disk_memo_summary_and_timings(first.clone()),
        off.clone()
    );

    let second = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    let second_summary = disk_memo_summary(&second);
    assert!(second_summary.contains("hits=1"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("written=0"));
    assert!(second_summary.contains("live_checked=0"));
    assert!(second_summary.contains("cached=1"));
    let aggregate = second
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "package_verified")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("package aggregate diagnostic");
    assert!(aggregate.contains("reference_checker_verdict=false"));
    assert!(aggregate.contains("locally_accelerated=true"));
    let module = second
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "module_verified")
        .expect("module diagnostic");
    assert_eq!(
        module.actual_value.as_deref(),
        Some("status=passed;evidence=disk-verifier-memo;proof_evidence=false")
    );

    clear_disk_memo();
    let rerun = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(rerun.exit_code(), CommandExitCode::Success);
    let rerun_summary = disk_memo_summary(&rerun);
    assert!(rerun_summary.contains("hits=0"));
    assert!(rerun_summary.contains("misses=1"));
    assert!(rerun_summary.contains("live_checked=1"));
    assert_eq!(without_disk_memo_summary_and_timings(rerun), off);
}

#[test]
fn package_verify_certs_cache_aware_disk_memo_live_checks_dirty_reverse_dependents() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_modules_fixture(
        "cache-aware-dag",
        &[
            "Proofs.Ai.Basic",
            "Proofs.Ai.EqReasoning",
            "Proofs.Ai.Analysis.AbstractMetricTopology",
        ],
        &["Eq.rec", "CacheAware.Unique"],
    );
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    remove_disk_memo_entries_for_module("Proofs.Ai.EqReasoning");

    let cached = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(cached.exit_code(), CommandExitCode::Success);
    let summary = disk_memo_summary(&cached);
    assert!(summary.contains("mode=disk"));
    assert!(summary.contains("invalidated="), "{summary}");
    assert!(!summary.contains("invalidated=0"), "{summary}");
    assert!(summary.contains("cached=1"), "{summary}");
    assert_eq!(
        module_actual_value(&cached, "Proofs.Ai.Basic"),
        "status=passed;evidence=disk-verifier-memo;proof_evidence=false"
    );
    assert_eq!(
        module_actual_value(&cached, "Proofs.Ai.EqReasoning"),
        "status=passed;evidence=live-checker;proof_evidence=true"
    );
    assert_eq!(
        module_actual_value(&cached, "Proofs.Ai.Analysis.AbstractMetricTopology"),
        "status=passed;evidence=live-checker;proof_evidence=true"
    );
}

#[test]
fn package_verify_certs_persistent_cache_read_through_writes_hits_and_delete_reruns_live() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "persistent-cache-read-through",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "PersistentCache.Unique"],
    );
    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);

    let first = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(first.exit_code(), CommandExitCode::Success);
    let first_summary = disk_memo_summary(&first);
    assert!(first_summary.contains("mode=read-through"));
    assert!(first_summary.contains("hits=0"));
    assert!(first_summary.contains("misses=1"));
    assert!(first_summary.contains("written=1"));
    assert!(first_summary.contains("live_checked=1"));
    assert!(first_summary.contains("cached=0"));
    assert!(first_summary.contains("trusted=false"));
    assert!(first_summary.contains("proof_evidence=false"));
    assert_eq!(disk_memo_entries().len(), 1);
    let entry_source = fs::read_to_string(&disk_memo_entries()[0]).unwrap();
    let entry = parse_package_audit_disk_memo_result_entry_json(&entry_source).unwrap();
    assert!(!entry.trusted);
    assert!(!entry.proof_evidence);
    assert_eq!(
        without_disk_memo_summary_and_timings(first.clone()),
        off.clone()
    );

    let second = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(second.exit_code(), CommandExitCode::Success);
    let second_summary = disk_memo_summary(&second);
    assert!(second_summary.contains("hits=1"));
    assert!(second_summary.contains("misses=0"));
    assert!(second_summary.contains("written=0"));
    assert!(second_summary.contains("live_checked=1"));
    assert!(second_summary.contains("cached=0"));
    let module = second
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "module_verified")
        .expect("module diagnostic");
    assert_eq!(
        module.actual_value.as_deref(),
        Some("status=passed;evidence=live-checker;proof_evidence=true")
    );
    assert_eq!(
        without_disk_memo_summary_and_timings(second.clone()),
        off.clone()
    );

    clear_disk_memo();
    let rerun = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );
    assert_eq!(rerun.exit_code(), CommandExitCode::Success);
    let rerun_summary = disk_memo_summary(&rerun);
    assert!(rerun_summary.contains("hits=0"));
    assert!(rerun_summary.contains("misses=1"));
    assert!(rerun_summary.contains("live_checked=1"));
    assert_eq!(without_disk_memo_summary_and_timings(rerun), off);
}

#[test]
fn package_verify_certs_persistent_cache_read_through_live_dominates_stale_identity() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    let package = build_source_free_fixture(
        "persistent-cache-stale-identity",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "PersistentCache.Stale"],
    );
    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    assert!(disk_memo_summary(&warm).contains("written=1"));

    let entry_path = disk_memo_entries()[0].clone();
    let entry_source = fs::read_to_string(&entry_path).unwrap();
    let mut entry = parse_package_audit_disk_memo_result_entry_json(&entry_source).unwrap();
    entry.key_input.package_lock_schema = "npa.package.lock.changed".to_owned();
    entry.cache_key = package_audit_disk_memo_key(&entry.key_input);
    fs::write(
        &entry_path,
        package_audit_disk_memo_result_entry_json(&entry),
    )
    .unwrap();

    let result = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(result.exit_code(), CommandExitCode::Success);
    let summary = disk_memo_summary(&result);
    assert!(summary.contains("hits=0"));
    assert!(summary.contains("stale=1"));
    assert!(summary.contains("written=1"));
    assert!(summary.contains("live_checked=1"));
    assert!(summary.contains("cached=0"));
    assert_eq!(without_disk_memo_summary_and_timings(result), off);
}

#[test]
fn package_verify_certs_persistent_cache_read_through_does_not_mask_stale_certificate() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    let package = build_source_free_fixture(
        "persistent-cache-stale-certificate",
        "Proofs.Ai.Eq",
        true,
        &["Eq.rec"],
    );
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    assert!(disk_memo_summary(&warm).contains("written=3"));

    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::ReadThrough,
        PackageTimingMode::Summary,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let summary = disk_memo_summary(&result);
    assert!(summary.contains("hits=0"));
    assert!(summary.contains("cached=0"));
    assert!(summary.contains("proof_evidence=false"));
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
}

#[test]
fn package_verify_certs_disk_memo_stale_certificate_misses() {
    let _guard = disk_memo_test_lock();
    clear_disk_memo();
    let package = build_source_free_fixture("disk-memo-stale", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let warm = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );
    assert_eq!(warm.exit_code(), CommandExitCode::Success);
    let warm_summary = disk_memo_summary(&warm);
    assert!(warm_summary.contains("written=3"), "{warm_summary}");

    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let result = run_verify_with_verifier_memo(
        &package,
        PackageChecker::Reference,
        PackageVerifierMemoMode::Disk,
        PackageTimingMode::Summary,
    );

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    let summary = disk_memo_summary(&result);
    assert!(summary.contains("cached=0"));
    assert!(summary.contains("misses=3"));
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.reason_code == "reference_checker_rejected"));
}

#[test]
fn package_verify_certs_disk_memo_external_is_rejected() {
    let _guard = disk_memo_test_lock();
    let package =
        build_source_free_fixture("disk-memo-external", "Proofs.Ai.Basic", false, &["Eq.rec"]);
    let external = write_external_runner_fixture(&package, true);

    let result = run_package_verify_certs(
        verify_certs_full(
            common_options(package.path(), true),
            PackageChecker::External,
        )
        .with_verifier_memo(PackageVerifierMemoMode::Disk)
        .with_external(external),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(
        result.diagnostics[0].field.as_deref(),
        Some("--verifier-memo")
    );
    assert_eq!(result.diagnostics[0].actual_value.as_deref(), Some("disk"));
}

#[test]
fn package_verify_certs_jobs_one_matches_existing_order() {
    let package =
        build_source_free_fixture("jobs-one-order", "Proofs.Ai.Basic", false, &["Eq.rec"]);

    let default_result = run_verify(&package, PackageChecker::Fast);
    let jobs_one_result = run_verify_with_jobs(&package, PackageChecker::Fast, 1);

    assert_eq!(jobs_one_result.exit_code(), CommandExitCode::Success);
    assert_eq!(jobs_one_result.render_json(), default_result.render_json());
}

#[test]
fn package_verify_certs_shards_jobs_four_matches_jobs_one_normalized() {
    let package = build_source_free_fixture(
        "shards-jobs-four-normalized",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let jobs_one_result = run_verify_with_jobs(&package, PackageChecker::Fast, 1);
    let jobs_four_result = run_verify_with_jobs(&package, PackageChecker::Fast, 4);

    assert_eq!(jobs_four_result.exit_code(), CommandExitCode::Success);
    assert_eq!(
        jobs_four_result.render_json(),
        jobs_one_result.render_json()
    );
}

#[test]
fn package_verify_certs_shards_failure_matches_jobs_one_and_preserves_diagnostic() {
    let package = build_source_free_fixture("shards-failure", "Proofs.Ai.Eq", true, &["Eq.rec"]);
    let certificate_path = package.artifact_path("Proofs/Ai/Eq/certificate.npcert");
    tamper_certificate_payload_without_rehash(&certificate_path);
    refresh_expected_certificate_file_hash(&package, &certificate_path);
    let manifest_source = fs::read_to_string(package.artifact_path(PACKAGE_MANIFEST_PATH)).unwrap();
    write_lock(&package, &manifest_source);

    let jobs_one_result = run_verify_with_jobs(&package, PackageChecker::Fast, 1);
    let jobs_four_result = run_verify_with_jobs(&package, PackageChecker::Fast, 4);

    assert_eq!(
        jobs_four_result.exit_code(),
        CommandExitCode::PackageFailure
    );
    assert_eq!(
        jobs_four_result.render_json(),
        jobs_one_result.render_json()
    );
    let diagnostic = jobs_four_result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.kind == DiagnosticKind::FastVerifier)
        .expect("fast verifier diagnostic is preserved");
    assert_eq!(diagnostic.reason_code, "kernel_verification_failed");
    assert_eq!(diagnostic.module.as_deref(), Some("Proofs.Ai.Eq"));
    let actual = diagnostic.actual_value.as_deref().unwrap();
    assert!(actual.contains("NonCanonical"), "{actual}");
}

#[test]
fn package_verify_certs_jobs_reference_parallel_is_rejected() {
    let package = build_source_free_fixture(
        "jobs-reference-rejected",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );
    let lock_hash = checked_lock_hash(&package);

    let result = run_verify_with_jobs(&package, PackageChecker::Reference, 4);

    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 2);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::PackageLock);
    assert_eq!(
        result.diagnostics[0].reason_code,
        "unsupported_parallel_checker"
    );
    assert_eq!(
        result.diagnostics[0].path.as_deref(),
        Some("execution.jobs")
    );
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("jobs"));
    assert_lock_provenance(
        &result.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
}

#[test]
fn package_verify_certs_jobs_audit_cache_parallel_is_rejected() {
    let package = build_source_free_fixture(
        "jobs-audit-cache-rejected",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec"],
    );

    let result = run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), PackageChecker::Fast)
            .with_audit_cache(PackageAuditCacheMode::ReadThrough)
            .with_jobs(4),
    );

    assert_eq!(result.exit_code(), CommandExitCode::UsageOrInternal);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].kind, DiagnosticKind::Usage);
    assert_eq!(result.diagnostics[0].reason_code, "unsupported_flag");
    assert_eq!(result.diagnostics[0].field.as_deref(), Some("--jobs"));
}

#[test]
fn package_verify_certs_memo_counters_are_projected_into_measurements() {
    let _guard = process_memo_test_lock();
    clear_package_verification_process_memo();
    let package = build_source_free_fixture(
        "process-memo-timing",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "ProcessMemo.Unique"],
    );
    let lock_hash = checked_lock_hash(&package);

    let off = run_verify(&package, PackageChecker::Fast);
    clear_package_verification_process_memo();
    let first = run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);
    let second =
        run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);

    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(!off.render_json().contains("process_memo_summary"));
    assert!(off.timings.is_none());

    assert!(!first.render_json().contains("process_memo_summary"));
    assert!(!second.render_json().contains("process_memo_summary"));
    assert_eq!(
        measurement_counter(&first, PerformanceMeasurementLabel::PackageMemoResults),
        0
    );
    assert!(measurement_counter(&second, PerformanceMeasurementLabel::PackageMemoResults) > 0);
    assert_eq!(
        measurement_counter(&second, PerformanceMeasurementLabel::PackageLiveResults),
        0
    );
    assert_eq!(
        measurement_counter(&second, PerformanceMeasurementLabel::PackageModulesChecked),
        0
    );
    assert_lock_provenance(
        &second.diagnostics[1],
        PackageLockInputMode::CheckedFile,
        lock_hash,
    );
    assert_eq!(second.diagnostics[2].reason_code, "module_verified");
    assert!(second
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.reason_code != "process_memo_summary"));
    assert_eq!(lock_provenance_count(&second), 1);
    assert!(second.timings.is_some());

    assert_eq!(without_process_memo_decode_cache_and_timings(first), off);
    assert_eq!(without_process_memo_decode_cache_and_timings(second), off);
}

#[test]
fn package_verify_certs_timings_do_not_enable_process_local_decode_cache() {
    let _guard = decode_cache_test_lock();
    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    assert_eq!(package_verification_decode_cache_entry_count(), 0);
    let package = build_source_free_fixture(
        "decode-cache-timing",
        "Proofs.Ai.Basic",
        false,
        &["Eq.rec", "DecodeCache.Unique"],
    );

    let off = run_verify(&package, PackageChecker::Fast);
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(!off.render_json().contains("decode_cache_summary"));
    assert!(off.timings.is_none());

    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let first = run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);
    clear_package_verification_process_memo();
    let second =
        run_verify_with_timings(&package, PackageChecker::Fast, PackageTimingMode::Summary);

    assert_eq!(package_verification_decode_cache_entry_count(), 0);
    assert!(!first.render_json().contains("decode_cache_summary"));
    assert!(!second.render_json().contains("decode_cache_summary"));
    for result in [&first, &second] {
        assert_eq!(
            measurement_counter(result, PerformanceMeasurementLabel::PackageDecodeCacheHits),
            0
        );
        assert_eq!(
            measurement_counter(
                result,
                PerformanceMeasurementLabel::PackageDecodeCacheMisses
            ),
            0
        );
    }

    assert_eq!(without_process_memo_decode_cache_and_timings(first), off);
    assert_eq!(without_process_memo_decode_cache_and_timings(second), off);
}

#[test]
fn package_verify_certs_timings_do_not_enable_persistent_import_context_cache() {
    let _guard = decode_cache_test_lock();
    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    clear_package_import_context_export_disk_cache();
    assert_eq!(package_import_context_export_disk_cache_entry_count(), 0);
    let package = build_source_free_fixture(
        "import-context-export-cache",
        "Proofs.Ai.Basic",
        true,
        &["Eq.rec", "ImportContextCache.Unique"],
    );

    let off = run_verify(&package, PackageChecker::Reference);
    assert_eq!(off.exit_code(), CommandExitCode::Success);
    assert!(!off.render_json().contains("decode_cache_summary"));
    assert!(off.timings.is_none());

    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let first = run_verify_with_timings(
        &package,
        PackageChecker::Reference,
        PackageTimingMode::Summary,
    );
    clear_package_verification_process_memo();
    clear_package_verification_decode_cache();
    let second = run_verify_with_timings(
        &package,
        PackageChecker::Reference,
        PackageTimingMode::Summary,
    );

    assert_eq!(package_import_context_export_disk_cache_entry_count(), 0);
    assert_eq!(package_verification_decode_cache_entry_count(), 0);
    assert!(!first.render_json().contains("decode_cache_summary"));
    assert!(!second.render_json().contains("decode_cache_summary"));
    for result in [&first, &second] {
        assert_eq!(
            measurement_counter(result, PerformanceMeasurementLabel::PackageDecodeCacheHits),
            0
        );
        assert_eq!(
            measurement_counter(
                result,
                PerformanceMeasurementLabel::PackageDecodeCacheMisses
            ),
            0
        );
    }

    assert_eq!(without_process_memo_decode_cache_and_timings(first), off);
    assert_eq!(without_process_memo_decode_cache_and_timings(second), off);
}

fn run_verify(
    package: &TestPackage,
    checker: PackageChecker,
) -> npa_cli::diagnostic::CommandResult {
    run_verify_with_audit_cache(package, checker, PackageAuditCacheMode::Off)
}

fn run_verify_with_lock_mode(
    package: &TestPackage,
    checker: PackageChecker,
    package_lock_mode: PackageLockInputMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker)
            .with_package_lock_mode(package_lock_mode),
    )
}

fn run_verify_with_lock_mode_and_audit_cache(
    package: &TestPackage,
    checker: PackageChecker,
    package_lock_mode: PackageLockInputMode,
    audit_cache: PackageAuditCacheMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker)
            .with_package_lock_mode(package_lock_mode)
            .with_audit_cache(audit_cache),
    )
}

fn run_verify_with_lock_mode_and_verifier_memo(
    package: &TestPackage,
    checker: PackageChecker,
    package_lock_mode: PackageLockInputMode,
    verifier_memo: PackageVerifierMemoMode,
    timings: PackageTimingMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker)
            .with_package_lock_mode(package_lock_mode)
            .with_verifier_memo(verifier_memo)
            .with_timings(timings),
    )
}

fn install_non_input_sentinels(package: &TestPackage, module_dir: &str) -> Vec<String> {
    let module = module_dir.replace('/', ".");
    let paths = vec![
        format!("{module_dir}/source.npa"),
        format!("{module_dir}/replay.json"),
        format!("{module_dir}/meta.json"),
        format!("{module_dir}/tactic-trace.json"),
        format!("{module_dir}/ai-trace.json"),
        "generated/theorem-index.json".to_owned(),
        "generated/publish-plan.json".to_owned(),
        format!(
            "generated/checker-results/fixture-package/0.1.0/{module}/external/previous-result.json"
        ),
        "generated/verified-export-summary.json".to_owned(),
        "generated/network-registry.json".to_owned(),
        ".npa/hidden-verification-result.json".to_owned(),
    ];
    for relative in &paths {
        let path = package.artifact_path(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        #[cfg(any(target_os = "linux", target_os = "android"))]
        fs::write(
            path,
            format!(
                "forbidden package verification input: {relative}\nhttp://127.0.0.1:9/must-not-be-read\n"
            ),
        )
        .unwrap();
        #[cfg(not(any(target_os = "linux", target_os = "android")))]
        fs::create_dir_all(path).unwrap();
    }
    paths
}

fn package_existing_file_paths(package: &TestPackage) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    collect_package_file_paths(package.path(), &mut paths);
    paths.sort();
    paths
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn package_existing_directory_paths(root: &Path) -> Vec<PathBuf> {
    let mut paths = vec![root.to_owned()];
    collect_package_directory_paths(root, &mut paths);
    paths.sort();
    paths
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn collect_package_directory_paths(current: &Path, paths: &mut Vec<PathBuf>) {
    let mut entries = fs::read_dir(current)
        .unwrap()
        .map(|entry| entry.unwrap())
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        if entry.file_type().unwrap().is_dir() {
            let path = entry.path();
            paths.push(path.clone());
            collect_package_directory_paths(&path, paths);
        }
    }
}

fn collect_package_file_paths(current: &Path, paths: &mut Vec<PathBuf>) {
    let mut entries = fs::read_dir(current)
        .unwrap()
        .map(|entry| entry.unwrap())
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        if entry.file_type().unwrap().is_dir() {
            collect_package_file_paths(&path, paths);
        } else {
            paths.push(path);
        }
    }
}

fn expected_in_process_inputs(
    mode: PackageLockInputMode,
    certificate_paths: &[&str],
) -> BTreeSet<String> {
    let mut expected = BTreeSet::from([PACKAGE_MANIFEST_PATH.to_owned()]);
    expected.extend(certificate_paths.iter().map(|path| (*path).to_owned()));
    if mode == PackageLockInputMode::CheckedFile {
        expected.insert(LOCK_PATH.to_owned());
    }
    expected
}

fn assert_package_read_scope(
    accessed: &BTreeSet<String>,
    expected: &BTreeSet<String>,
    forbidden: &[String],
    label: &str,
) {
    for path in forbidden {
        assert!(
            !accessed.contains(path),
            "{label}: verification accessed forbidden input {path}; accessed={accessed:?}"
        );
    }
    #[cfg(any(target_os = "linux", target_os = "android"))]
    assert_eq!(accessed, expected, "{label}: package input read scope");
    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    let _ = expected;
}

fn git_status_snapshot(package: &TestPackage) -> Vec<u8> {
    let output = Command::new("/usr/bin/git")
        .args(["status", "--porcelain=v1", "--untracked-files=all"])
        .current_dir(package.cleanup_path())
        .output()
        .unwrap();
    assert!(output.status.success(), "git status failed: {output:?}");
    output.stdout
}

fn run_guarded_read_only_verify(
    package: &TestPackage,
    options: PackageVerifyCertsOptions,
    expected_inputs: &BTreeSet<String>,
    forbidden_inputs: &[String],
    label: &str,
) -> npa_cli::diagnostic::CommandResult {
    let before = package_tree_snapshot(package);
    let status_before = git_status_snapshot(package);
    let access_guard = PackageReadAccessGuard::new_with_package_mutation_watch(
        package.path(),
        &package_existing_file_paths(package),
    );
    let result = with_network_inputs_denied(move || run_package_verify_certs(options));
    let observation = access_guard.finish();
    assert_package_read_scope(
        &observation.accessed,
        expected_inputs,
        forbidden_inputs,
        label,
    );
    assert!(
        observation.mutations.is_empty(),
        "{label}: package-root mutation observed: {:?}",
        observation.mutations
    );
    assert_eq!(
        package_tree_snapshot(package),
        before,
        "{label}: package tree"
    );
    assert_eq!(
        git_status_snapshot(package),
        status_before,
        "{label}: status"
    );
    result
}

fn package_tree_snapshot(package: &TestPackage) -> BTreeMap<String, Option<Vec<u8>>> {
    let mut snapshot = BTreeMap::new();
    collect_package_tree(package.path(), package.path(), &mut snapshot);
    snapshot
}

fn collect_package_tree(
    root: &Path,
    current: &Path,
    snapshot: &mut BTreeMap<String, Option<Vec<u8>>>,
) {
    let mut entries = fs::read_dir(current)
        .unwrap()
        .map(|entry| entry.unwrap())
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let relative = path
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        if entry.file_type().unwrap().is_dir() {
            snapshot.insert(relative, None);
            collect_package_tree(root, &path, snapshot);
        } else {
            snapshot.insert(relative, Some(fs::read(path).unwrap()));
        }
    }
}

fn replace_manifest_hash(package: &TestPackage, field: &str, hash: PackageHash) {
    replace_manifest_line(
        package,
        field,
        &format!("{field} = \"{}\"", format_package_hash(&hash)),
    );
}

fn replace_manifest_line(package: &TestPackage, field: &str, replacement: &str) {
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&path).unwrap();
    let line = source
        .lines()
        .find(|line| line.starts_with(&format!("{field} = ")))
        .unwrap_or_else(|| panic!("manifest field {field} must exist"));
    fs::write(path, source.replacen(line, replacement, 1)).unwrap();
}

fn replace_manifest_text_once(package: &TestPackage, needle: &str, replacement: &str) {
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&path).unwrap();
    assert_eq!(source.matches(needle).count(), 1, "manifest replacement");
    fs::write(path, source.replacen(needle, replacement, 1)).unwrap();
}

fn append_manifest_comment_and_write_lock(package: &TestPackage, comment: &str) {
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let mut source = fs::read_to_string(&path).unwrap();
    source.push_str(&format!("# {comment}\n"));
    fs::write(path, &source).unwrap();
    write_lock(package, &source);
}

fn run_verify_changed(
    package: &TestPackage,
    checker: PackageChecker,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(verify_changed_certificates(
        common_options(package.path(), true),
        checker,
    ))
}

fn init_git_baseline(package: &TestPackage) {
    run_git_at(package.path(), &["init", "-q"]);
    run_git_at(package.path(), &["add", "."]);
    run_git_at(
        package.path(),
        &[
            "-c",
            "user.name=NPA Test",
            "-c",
            "user.email=npa-test@example.invalid",
            "commit",
            "-q",
            "-m",
            "baseline",
        ],
    );
}

fn init_git_worktree_baseline(package: &TestPackage) {
    run_git_at(package.cleanup_path(), &["init", "-q"]);
    run_git_at(package.cleanup_path(), &["add", "."]);
    run_git_at(
        package.cleanup_path(),
        &[
            "-c",
            "user.name=NPA Test",
            "-c",
            "user.email=npa-test@example.invalid",
            "commit",
            "-q",
            "-m",
            "baseline",
        ],
    );
}

fn nest_package_in_worktree(package: &mut TestPackage, relative_path: &str) {
    let original_package_root = package.path.clone();
    let worktree_root = original_package_root.with_file_name(format!(
        "{}-worktree",
        original_package_root.file_name().unwrap().to_string_lossy()
    ));
    if worktree_root.exists() {
        fs::remove_dir_all(&worktree_root).unwrap();
    }
    let nested_package_root = worktree_root.join(relative_path);
    fs::create_dir_all(nested_package_root.parent().unwrap()).unwrap();
    fs::rename(&original_package_root, &nested_package_root).unwrap();
    package.path = nested_package_root;
    package.cleanup_path = worktree_root;
}

fn stage_changed_then_restore(package: &TestPackage, relative_path: &str, suffix: &[u8]) {
    let path = package.artifact_path(relative_path);
    let original = fs::read(&path).unwrap();
    let mut staged = original.clone();
    staged.extend_from_slice(suffix);
    fs::write(&path, staged).unwrap();
    run_git(package, &["add", relative_path]);
    fs::write(&path, original).unwrap();
}

fn mark_worktree_mode_changed(package: &TestPackage, relative_path: &str) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let path = package.artifact_path(relative_path);
        let mut permissions = fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).unwrap();
    }
    #[cfg(not(unix))]
    {
        let _ = (package, relative_path);
        panic!("worktree mode-change fixture requires unix permissions");
    }
}

fn stage_worktree_mode_changed(package: &TestPackage, relative_path: &str) {
    mark_worktree_mode_changed(package, relative_path);
    run_git(package, &["add", relative_path]);
}

fn run_git(package: &TestPackage, args: &[&str]) {
    run_git_at(package.path(), args);
}

fn run_git_at(cwd: &Path, args: &[&str]) {
    let status = Command::new("git")
        .args(args)
        .current_dir(cwd)
        .status()
        .unwrap();
    assert!(status.success(), "git {args:?} failed with {status}");
}

fn run_verify_with_jobs(
    package: &TestPackage,
    checker: PackageChecker,
    jobs: usize,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker).with_jobs(jobs),
    )
}

fn run_verify_with_timings(
    package: &TestPackage,
    checker: PackageChecker,
    timings: PackageTimingMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker).with_timings(timings),
    )
}

fn run_verify_with_verifier_memo(
    package: &TestPackage,
    checker: PackageChecker,
    verifier_memo: PackageVerifierMemoMode,
    timings: PackageTimingMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker)
            .with_verifier_memo(verifier_memo)
            .with_timings(timings),
    )
}

fn run_verify_with_audit_cache(
    package: &TestPackage,
    checker: PackageChecker,
    audit_cache: PackageAuditCacheMode,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(common_options(package.path(), true), checker)
            .with_audit_cache(audit_cache),
    )
}

fn measurement_counter(
    result: &npa_cli::diagnostic::CommandResult,
    label: PerformanceMeasurementLabel,
) -> u64 {
    result
        .timings
        .as_ref()
        .and_then(|timings| timings.measurements.as_ref())
        .and_then(|measurements| {
            measurements
                .counters
                .iter()
                .find(|counter| counter.label == label)
        })
        .map(|counter| counter.value)
        .expect("measurement counter")
}

fn disk_memo_summary(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "disk_memo_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("disk memo summary diagnostic")
}

fn module_actual_value<'a>(
    result: &'a npa_cli::diagnostic::CommandResult,
    module: &str,
) -> &'a str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| {
            diagnostic.reason_code == "module_verified"
                && diagnostic.module.as_deref() == Some(module)
        })
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("module diagnostic actual value")
}

fn without_process_memo_decode_cache_and_timings(
    mut result: npa_cli::diagnostic::CommandResult,
) -> npa_cli::diagnostic::CommandResult {
    result.diagnostics.retain(|diagnostic| {
        diagnostic.reason_code != "process_memo_summary"
            && diagnostic.reason_code != "decode_cache_summary"
    });
    result.timings = None;
    result
}

fn without_disk_memo_summary_and_timings(
    mut result: npa_cli::diagnostic::CommandResult,
) -> npa_cli::diagnostic::CommandResult {
    result
        .diagnostics
        .retain(|diagnostic| diagnostic.reason_code != "disk_memo_summary");
    result.timings = None;
    result
}

fn run_verify_external(
    package: &TestPackage,
    external: ExternalCheckerOptions,
) -> npa_cli::diagnostic::CommandResult {
    run_package_verify_certs(
        verify_certs_full(
            common_options(package.path(), true),
            PackageChecker::External,
        )
        .with_external(external),
    )
}

fn audit_cache_summary(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "audit_cache_summary")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("audit cache summary diagnostic")
}

fn audit_cache_follow_up(result: &npa_cli::diagnostic::CommandResult) -> &str {
    result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.reason_code == "audit_cache_follow_up")
        .and_then(|diagnostic| diagnostic.actual_value.as_deref())
        .expect("audit cache follow-up diagnostic")
}

fn clear_audit_cache() {
    let _ = fs::remove_dir_all(
        std::env::current_dir()
            .unwrap()
            .join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR),
    );
}

fn audit_cache_entries() -> Vec<PathBuf> {
    let cache_dir = std::env::current_dir()
        .unwrap()
        .join(PACKAGE_AUDIT_CACHE_LAYOUT_DIR);
    let mut entries = fs::read_dir(cache_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

fn clear_disk_memo() {
    let _ = fs::remove_dir_all(
        std::env::current_dir()
            .unwrap()
            .join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR),
    );
}

fn disk_memo_entries() -> Vec<PathBuf> {
    let memo_dir = std::env::current_dir()
        .unwrap()
        .join(PACKAGE_AUDIT_DISK_MEMO_LAYOUT_DIR);
    let mut entries = fs::read_dir(memo_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

fn remove_audit_cache_entries_for_module(module: &str) {
    for path in audit_cache_entries() {
        let source = fs::read_to_string(&path).unwrap();
        let entry = parse_package_audit_result_entry_json(&source).unwrap();
        if entry.key_input.module.as_dotted() == module {
            fs::remove_file(path).unwrap();
        }
    }
}

fn remove_disk_memo_entries_for_module(module: &str) {
    for path in disk_memo_entries() {
        let source = fs::read_to_string(&path).unwrap();
        let entry = parse_package_audit_disk_memo_result_entry_json(&source).unwrap();
        if entry.key_input.module.as_dotted() == module {
            fs::remove_file(path).unwrap();
        }
    }
}

fn audit_cache_test_lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap()
}

fn process_memo_test_lock() -> MutexGuard<'static, ()> {
    shared_process_state_test_lock()
}

fn disk_memo_test_lock() -> MutexGuard<'static, ()> {
    shared_process_state_test_lock()
}

fn decode_cache_test_lock() -> MutexGuard<'static, ()> {
    shared_process_state_test_lock()
}

fn shared_process_state_test_lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn write_external_runner_fixture(
    package: &TestPackage,
    create_binary: bool,
) -> ExternalCheckerOptions {
    let checker_build_hash = test_hash(0x55);
    let lock_source = fs::read_to_string(package.artifact_path(LOCK_PATH)).unwrap();
    let lock = parse_package_lock_json(&lock_source).unwrap();
    let mut checker_script = "#!/bin/sh\ncase \"$2\" in\n".to_owned();
    for entry in &lock.entries {
        checker_script.push_str(&format!(
            "  '{}')\n    cat <<'JSON'\n{{\"schema\":\"npa.independent-checker.checker_raw_result.v1\",\"checker_id\":\"npa-checker-ext\",\"checker_version\":\"0.1.0\",\"checker_build_hash\":\"{}\",\"status\":\"checked\",\"module\":\"{}\",\"certificate_hash\":\"{}\",\"export_hash\":\"{}\",\"axiom_report_hash\":\"{}\"}}\nJSON\n    ;;\n",
            entry.certificate.as_str(),
            format_hash_string(&checker_build_hash),
            entry.module.as_dotted(),
            format_package_hash(&entry.certificate_hash),
            format_package_hash(&entry.export_hash),
            format_package_hash(&entry.axiom_report_hash),
        ));
    }
    checker_script
        .push_str("  *)\n    echo 'unknown certificate path' >&2\n    exit 2\n    ;;\nesac\n");
    let checker_path = package.artifact_path("tools/checkers/npa-checker-ext");
    let binary_hash = if create_binary {
        fs::create_dir_all(checker_path.parent().unwrap()).unwrap();
        fs::write(&checker_path, checker_script.as_bytes()).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let mut permissions = fs::metadata(&checker_path).unwrap().permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(&checker_path, permissions).unwrap();
        }
        independent_checker_file_hash(checker_script.as_bytes())
    } else {
        independent_checker_file_hash(b"missing external checker fixture")
    };

    let axiom_policy_path = package.artifact_path("ci/axiom-policy.toml");
    let axiom_policy_bytes =
        b"format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = [\"Eq.rec\"]\n";
    fs::create_dir_all(axiom_policy_path.parent().unwrap()).unwrap();
    fs::write(&axiom_policy_path, axiom_policy_bytes).unwrap();
    let axiom_policy_hash = independent_checker_file_hash(axiom_policy_bytes);

    let registry_source = r#"{"schema":"npa.independent-checker.checker_binary_registry.v1","root_kind":"workspace","entries":[{"binary_id":"npa-checker-ext-macos-aarch64","path":"tools/checkers/npa-checker-ext"}]}"#;
    let registry_path = package.artifact_path("ci/checker-binaries.json");
    fs::write(&registry_path, registry_source).unwrap();

    let policy_source = format!(
        r#"{{
          "schema":"npa.independent-checker.runner_policy.v1",
          "id":"package-external-pr",
          "version":1,
          "trust_mode":"pr",
          "required_checker_profiles":["reference"],
          "optional_checker_profiles":["external"],
          "checker_allowlist":[
            {{
              "profile":"external",
              "checker_id":"npa-checker-ext",
              "binary_id":"npa-checker-ext-macos-aarch64",
              "binary_hash":"{}",
              "build_hash":"{}",
              "allowed_args":[]
            }},
            {{
              "profile":"reference",
              "checker_id":"npa-checker-ref",
              "binary_id":"npa-checker-ref-macos-aarch64",
              "binary_hash":"{}",
              "build_hash":"{}",
              "allowed_args":["--json","--canonical-only"]
            }}
          ],
          "checker_identity_manifest":{{
            "kind":"file",
            "path":"ci/checker-identity.json",
            "manifest_hash":"{}"
          }},
          "import_policy":{{
            "mode":"locked_store",
            "network":"forbidden",
            "require_import_lock_hash":true
          }},
          "axiom_policy":{{
            "path":"ci/axiom-policy.toml",
            "hash":"{}"
          }},
          "budgets":{{
            "external":{{"max_steps":10000000,"max_memory_mb":2048,"timeout_ms":60000}},
            "reference":{{"max_steps":10000000,"max_memory_mb":2048,"timeout_ms":60000}}
          }},
          "on_resource_exhausted":"fail",
          "on_missing_required_checker":"fail",
          "on_profile_requested_by_ai":"ignore_unless_policy_allows"
        }}"#,
        format_hash_string(&binary_hash),
        format_hash_string(&checker_build_hash),
        format_hash_string(&test_hash(0x10)),
        format_hash_string(&test_hash(0x11)),
        format_hash_string(&test_hash(0x12)),
        format_hash_string(&axiom_policy_hash),
    );
    let policy_hash = parse_independent_checker_runner_policy(&policy_source)
        .unwrap()
        .policy_hash();
    let policy_path = package.artifact_path("ci/runner.release.json");
    fs::write(&policy_path, policy_source).unwrap();

    external_checker_options(
        "ci/runner.release.json",
        format_hash_string(&policy_hash),
        "ci/checker-binaries.json",
    )
}

struct RealExternalRunnerFixture {
    options: ExternalCheckerOptions,
    binary_hash: String,
    build_hash: String,
    policy_hash: String,
    runner_build_hash: String,
}

fn write_real_external_runner_fixture(
    package: &TestPackage,
    source_checker_path: &Path,
) -> RealExternalRunnerFixture {
    let options = write_external_runner_fixture(package, true);
    let checker_path = package.artifact_path("tools/checkers/npa-checker-ext");
    let old_binary_bytes = fs::read(&checker_path).unwrap();
    let old_binary_hash = independent_checker_file_hash(&old_binary_bytes);
    let checker_bytes = fs::read(source_checker_path).unwrap();
    let binary_hash = independent_checker_file_hash(&checker_bytes);
    fs::write(&checker_path, &checker_bytes).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let mut permissions = fs::metadata(&checker_path).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&checker_path, permissions).unwrap();
    }

    let version = Command::new(&checker_path)
        .arg("--version")
        .output()
        .unwrap();
    assert!(version.status.success());
    let version_stdout = String::from_utf8(version.stdout).unwrap();
    let build_hash = version_stdout
        .lines()
        .find_map(|line| line.strip_prefix("checker_build_hash "))
        .expect("OCaml checker --version must publish checker_build_hash");

    let axiom_policy_path = package.artifact_path("ci/axiom-policy.toml");
    let old_axiom_policy_bytes = fs::read(&axiom_policy_path).unwrap();
    let old_axiom_policy_hash = independent_checker_file_hash(&old_axiom_policy_bytes);
    let axiom_policy_bytes =
        b"format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = [\"Eq.rec\"]\n";
    fs::write(&axiom_policy_path, axiom_policy_bytes).unwrap();
    let axiom_policy_hash = independent_checker_file_hash(axiom_policy_bytes);

    let policy_path = package.artifact_path("ci/runner.release.json");
    let policy_source = fs::read_to_string(&policy_path).unwrap();
    let policy_source = policy_source
        .replace(
            &format_hash_string(&old_binary_hash),
            &format_hash_string(&binary_hash),
        )
        .replace(&format_hash_string(&test_hash(0x55)), build_hash)
        .replace(
            &format_hash_string(&old_axiom_policy_hash),
            &format_hash_string(&axiom_policy_hash),
        );
    let policy_hash = parse_independent_checker_runner_policy(&policy_source)
        .unwrap()
        .policy_hash();
    fs::write(&policy_path, policy_source).unwrap();

    RealExternalRunnerFixture {
        options: external_checker_options(
            options.runner_policy,
            format_hash_string(&policy_hash),
            options.checker_registry,
        ),
        binary_hash: format_hash_string(&binary_hash),
        build_hash: build_hash.to_owned(),
        policy_hash: format_hash_string(&policy_hash),
        runner_build_hash: format_hash_string(&independent_checker_file_hash(
            b"npa-cli-package-external-runner:0.1.0",
        )),
    }
}

fn json_string_field_for_test<'a>(source: &'a str, field: &str) -> &'a str {
    let prefix = format!("\"{field}\":\"");
    let value = source
        .split_once(&prefix)
        .unwrap_or_else(|| panic!("missing JSON string field {field}"))
        .1;
    value
        .split_once('"')
        .unwrap_or_else(|| panic!("unterminated JSON string field {field}"))
        .0
}

fn decode_lower_hex_for_test(source: &str) -> Vec<u8> {
    assert_eq!(source.len() % 2, 0, "hex must have an even length");
    source
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digit = |byte: u8| match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                _ => panic!("raw checker output must use lowercase hex"),
            };
            (digit(pair[0]) << 4) | digit(pair[1])
        })
        .collect()
}

fn test_hash(byte: u8) -> npa_cert::Hash {
    [byte; 32]
}

fn checked_lock_hash(package: &TestPackage) -> PackageHash {
    package_file_hash(&fs::read(package.artifact_path(LOCK_PATH)).unwrap())
}

fn lock_provenance_count(result: &npa_cli::diagnostic::CommandResult) -> usize {
    result
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            matches!(
                diagnostic.reason_code.as_str(),
                "package_lock_checked" | "package_lock_reconstructed"
            )
        })
        .count()
}

fn verified_module_identities(
    result: &npa_cli::diagnostic::CommandResult,
) -> Vec<(String, String)> {
    result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason_code == "module_verified")
        .map(|diagnostic| {
            (
                diagnostic.module.clone().unwrap(),
                diagnostic.path.clone().unwrap(),
            )
        })
        .collect()
}

fn assert_lock_provenance(
    diagnostic: &npa_cli::diagnostic::CommandDiagnostic,
    mode: PackageLockInputMode,
    hash: PackageHash,
) {
    let reason = match mode {
        PackageLockInputMode::CheckedFile => "package_lock_checked",
        PackageLockInputMode::ReconstructedInMemory => "package_lock_reconstructed",
        _ => unreachable!("test only covers supported package-lock modes"),
    };
    assert_info(diagnostic, DiagnosticKind::PackageLock, reason, None);
    assert_eq!(diagnostic.field.as_deref(), Some("package_lock"));
    let expected = format!("mode={};hash={}", mode.as_str(), format_package_hash(&hash));
    assert_eq!(diagnostic.actual_value.as_deref(), Some(expected.as_str()));
    let digest = diagnostic
        .actual_value
        .as_deref()
        .unwrap()
        .rsplit_once("sha256:")
        .unwrap()
        .1;
    assert_eq!(digest.len(), 64);
    assert!(digest
        .bytes()
        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)));
}

fn assert_info(
    diagnostic: &npa_cli::diagnostic::CommandDiagnostic,
    kind: DiagnosticKind,
    reason: &str,
    checker: Option<&str>,
) {
    assert_eq!(diagnostic.kind, kind);
    assert_eq!(diagnostic.reason_code, reason);
    assert_eq!(diagnostic.severity, DiagnosticSeverity::Info);
    assert_eq!(diagnostic.checker.as_deref(), checker);
}

fn assert_failure(
    result: &npa_cli::diagnostic::CommandResult,
    kind: DiagnosticKind,
    reason: &str,
    path: Option<&str>,
    field: Option<&str>,
) {
    assert_eq!(result.exit_code(), CommandExitCode::PackageFailure);
    assert_eq!(result.diagnostics.len(), 1);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.kind, kind);
    assert_eq!(diagnostic.reason_code, reason);
    if let Some(path) = path {
        assert_eq!(diagnostic.path.as_deref(), Some(path));
    }
    if let Some(field) = field {
        assert_eq!(diagnostic.field.as_deref(), Some(field));
    }
    assert!(diagnostic.checker.is_none());
    assert!(!result.render_json().contains("/tmp/"));
}

fn build_source_free_fixture(
    label: &str,
    module_name: &str,
    include_external: bool,
    allowed_axioms: &[&str],
) -> TestPackage {
    let package = TestPackage::new(label);
    let proof_manifest = proof_manifest();
    let manifest = proof_manifest.manifest();
    let module = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == module_name)
        .unwrap();
    copy_artifact(&package, module.certificate.as_str());

    let imports = if include_external {
        manifest
            .imports
            .as_deref()
            .unwrap_or(&[])
            .iter()
            .filter(|import| module.imports.contains(&import.module))
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    for import in &imports {
        copy_artifact(&package, import.certificate.as_str());
    }

    let manifest_source = fixture_manifest(
        allowed_axioms,
        &imports,
        &[manifest_module_from_package(module)],
    );
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn build_source_free_modules_fixture(
    label: &str,
    module_names: &[&str],
    allowed_axioms: &[&str],
) -> TestPackage {
    let package = TestPackage::new(label);
    let proof_manifest = proof_manifest();
    let manifest = proof_manifest.manifest();
    let local_modules = module_names
        .iter()
        .map(Name::from_dotted)
        .collect::<BTreeSet<_>>();
    let modules = module_names
        .iter()
        .map(|module_name| {
            manifest
                .modules
                .iter()
                .find(|module| module.module.as_dotted() == *module_name)
                .unwrap()
                .clone()
        })
        .collect::<Vec<_>>();
    let external_import_modules = modules
        .iter()
        .flat_map(|module| module.imports.iter().cloned())
        .filter(|module| !local_modules.contains(module))
        .collect::<BTreeSet<_>>();
    let imports = manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .filter(|import| external_import_modules.contains(&import.module))
        .cloned()
        .collect::<Vec<_>>();

    for module in &modules {
        copy_artifact(&package, module.certificate.as_str());
    }
    for import in &imports {
        copy_artifact(&package, import.certificate.as_str());
    }

    let manifest_modules = modules
        .iter()
        .map(manifest_module_from_package)
        .collect::<Vec<_>>();
    let manifest_source = fixture_manifest(allowed_axioms, &imports, &manifest_modules);
    fs::write(
        package.artifact_path(PACKAGE_MANIFEST_PATH),
        &manifest_source,
    )
    .unwrap();
    write_lock(&package, &manifest_source);
    package
}

fn manifest_module_from_package(module: &PackageModule) -> ManifestModule {
    ManifestModule {
        module: module.module.clone(),
        source: module.source.as_str().to_owned(),
        certificate: module.certificate.as_str().to_owned(),
        meta: module.meta.as_ref().map(|path| path.as_str().to_owned()),
        replay: module.replay.as_ref().map(|path| path.as_str().to_owned()),
        imports: module.imports.clone(),
        source_hash: module.expected_source_hash,
        certificate_file_hash: module.expected_certificate_file_hash,
        export_hash: module.expected_export_hash,
        axiom_report_hash: module.expected_axiom_report_hash,
        certificate_hash: module.expected_certificate_hash,
    }
}

fn fixture_manifest(
    allowed_axioms: &[&str],
    imports: &[PackageExternalImport],
    modules: &[ManifestModule],
) -> String {
    let mut source = format!(
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = {}

"#,
        name_array(allowed_axioms),
    );
    for import in imports {
        source.push_str(&format!(
            r#"[[imports]]
module = "{}"
package = "{}"
version = "{}"
certificate = "{}"
export_hash = "{}"
certificate_hash = "{}"

"#,
            import.module.as_dotted(),
            import.package.as_str(),
            import.version.as_str(),
            import.certificate.as_str(),
            format_package_hash(&import.export_hash),
            format_package_hash(&import.certificate_hash),
        ));
    }
    for module in modules {
        source.push_str(&format!(
            r#"[[modules]]
module = "{}"
source = "{}"
certificate = "{}"
"#,
            module.module.as_dotted(),
            module.source,
            module.certificate,
        ));
        if let Some(meta) = &module.meta {
            source.push_str(&format!("meta = \"{meta}\"\n"));
        }
        if let Some(replay) = &module.replay {
            source.push_str(&format!("replay = \"{replay}\"\n"));
        }
        source.push_str(&format!(
            r#"imports = {}
expected_source_hash = "{}"
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
inductives = []
definitions = []
theorems = []
axioms = []
tags = []

"#,
            module_imports_array(&module.imports),
            format_package_hash(&module.source_hash),
            format_package_hash(&module.certificate_file_hash),
            format_package_hash(&module.export_hash),
            format_package_hash(&module.axiom_report_hash),
            format_package_hash(&module.certificate_hash),
        ));
    }
    source
}

fn name_array(names: &[&str]) -> String {
    let names = names
        .iter()
        .map(|name| format!("\"{name}\""))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{names}]")
}

fn module_imports_array(imports: &[Name]) -> String {
    let imports = imports
        .iter()
        .map(|name| format!("\"{}\"", name.as_dotted()))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{imports}]")
}

fn write_lock(package: &TestPackage, manifest_source: &str) {
    let validated = parse_and_validate_manifest_str(manifest_source).unwrap();
    let lock = build_package_lock_from_package_root(
        &validated,
        package.path(),
        PackagePath::new(PACKAGE_MANIFEST_PATH),
    )
    .unwrap();
    let lock_json = lock.canonical_json().unwrap();
    let lock_path = package.artifact_path(LOCK_PATH);
    fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
    fs::write(lock_path, lock_json).unwrap();
}

fn copy_artifact(package: &TestPackage, relative: &str) {
    let source = repo_root().join("testdata/package/proofs").join(relative);
    let target = package.artifact_path(relative);
    fs::create_dir_all(target.parent().unwrap()).unwrap();
    fs::copy(source, target).unwrap();
}

fn tamper_certificate_payload_without_rehash(path: &Path) {
    let mut bytes = fs::read(path).unwrap();
    let needle = b"eq_refl_prop";
    let Some(index) = bytes
        .windows(needle.len())
        .position(|window| window == needle)
    else {
        panic!("expected Eq fixture declaration name in certificate bytes");
    };
    bytes[index] = b'f';
    fs::write(path, bytes).unwrap();
}

fn refresh_expected_certificate_file_hash(package: &TestPackage, certificate: &Path) {
    let file_hash = package_file_hash(&fs::read(certificate).unwrap());
    let path = package.artifact_path(PACKAGE_MANIFEST_PATH);
    let source = fs::read_to_string(&path).unwrap();
    let line = source
        .lines()
        .find(|line| line.starts_with("expected_certificate_file_hash = \""))
        .unwrap();
    let replacement = format!(
        "expected_certificate_file_hash = \"{}\"",
        format_package_hash(&file_hash)
    );
    fs::write(path, source.replacen(line, &replacement, 1)).unwrap();
}

fn proof_manifest() -> npa_package::ValidatedPackageManifest {
    let source =
        fs::read_to_string(repo_root().join("testdata/package/proofs/npa-package.toml")).unwrap();
    parse_and_validate_manifest_str(&source).unwrap()
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .components()
        .collect()
}

fn corpus_script_path(script: &str) -> PathBuf {
    let root = repo_root();
    let standalone_path = root.join("scripts").join(script);
    if standalone_path.exists() {
        return standalone_path;
    }
    root.join("../npa-corpus/scripts").join(script)
}
