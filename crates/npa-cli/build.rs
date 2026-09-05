use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use sha2::{Digest, Sha256};

fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo:rerun-if-env-changed=TARGET");
    println!("cargo:rerun-if-env-changed=NPA_BENCH_SOURCE_IDENTITY");
    embed_file_hash("NPA_CLI_BUILD_CARGO_LOCK_SHA256", "../../Cargo.lock");
    embed_file_hash(
        "NPA_CLI_BUILD_PERFORMANCE_MANIFEST_V02_SHA256",
        "../../testdata/performance/fixtures/manifest.v0.2.json",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_PERFORMANCE_MANIFEST_V01_SHA256",
        "../../testdata/performance/fixtures/manifest.v0.1.json",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_PERFORMANCE_BASELINE_SHA256",
        "../../testdata/performance/baselines/measurements.v0.1.json",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_FIXTURE_ORACLE_SHA256",
        "../../testdata/performance/fixture-generator.v1.tsv",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_SNAPSHOT_HARNESS_SOURCE_SHA256",
        "examples/bench_package_artifact_snapshot.rs",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_MEASURE_PROCESS_SOURCE_SHA256",
        "examples/measure_process.rs",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_VMSP_HARNESS_SOURCE_SHA256",
        "../npa-api/examples/bench_shared_payload.rs",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_VMSP_FIXTURE_PARSER_SOURCE_SHA256",
        "../npa-api/src/performance_fixture_v02.rs",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_GITSEL_HARNESS_SOURCE_SHA256",
        "examples/bench_package_changed_selection.rs",
    );
    embed_file_hash(
        "NPA_CLI_BUILD_TBAC_HARNESS_SOURCE_SHA256",
        "examples/targeted_build_certs_bench.rs",
    );
    embed_file_hash("NPA_CLI_BUILD_NPA_MAIN_SOURCE_SHA256", "src/main.rs");
    embed_snapshot_source_set();
    embed_snap_vmsp_manager_source_set();
    embed_vmsp_benchmark_source_set();
    embed_gitsel_source_set();
    embed_tbac_source_set();
    let source_revision =
        env::var("NPA_BENCH_SOURCE_IDENTITY").unwrap_or_else(|_| "unbound".to_owned());
    assert!(
        source_revision == "unbound" || valid_source_identity(&source_revision),
        "NPA_BENCH_SOURCE_IDENTITY must be a lowercase 40-digit Git OID with optional -dirty suffix"
    );
    if source_revision != "unbound" {
        assert_eq!(
            source_revision,
            current_source_identity(),
            "NPA_BENCH_SOURCE_IDENTITY must identify the current Git worktree"
        );
    }
    println!("cargo:rustc-env=NPA_CLI_BUILD_SOURCE_REVISION={source_revision}");

    let profile = env::var("PROFILE").expect("Cargo supplies PROFILE to build scripts");
    let cargo_profile = match profile.as_str() {
        "debug" => "dev",
        profile => profile,
    };
    println!("cargo:rustc-env=NPA_CLI_BUILD_CARGO_PROFILE={cargo_profile}");
    let target = env::var("TARGET").expect("Cargo supplies TARGET to build scripts");
    assert!(!target.is_empty(), "Cargo TARGET must be non-empty");
    println!("cargo:rustc-env=NPA_CLI_BUILD_TARGET={target}");

    let mut features = env::vars()
        .filter_map(|(name, _)| name.strip_prefix("CARGO_FEATURE_").map(str::to_owned))
        .map(|name| name.to_ascii_lowercase().replace('_', "-"))
        .collect::<Vec<_>>();
    features.sort();
    features.dedup();
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_CARGO_FEATURES={}",
        features.join(",")
    );
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_FEATURES={}",
        features.join(",")
    );

    let rustc = env::var_os("RUSTC").expect("Cargo supplies RUSTC to build scripts");
    let output = Command::new(rustc)
        .arg("-Vv")
        .output()
        .expect("build compiler must support rustc -Vv");
    assert!(output.status.success(), "build compiler rustc -Vv failed");
    let rustc_vv = String::from_utf8(output.stdout).expect("rustc -Vv output is UTF-8");
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_RUSTC_VV_HEX={}",
        hex(rustc_vv.as_bytes())
    );
    let rustflags = env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_RUSTFLAGS_HEX={}",
        hex(rustflags.as_bytes())
    );
    println!("cargo:rustc-env=NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_TARGET={target}");
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_RUSTC_VV_HEX={}",
        hex(rustc_vv.as_bytes())
    );
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAPSHOT_BENCHMARK_RUSTFLAGS_HEX={}",
        hex(rustflags.as_bytes())
    );
}

fn valid_source_identity(value: &str) -> bool {
    let oid = value.strip_suffix("-dirty").unwrap_or(value);
    oid.len() == 40
        && oid
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn current_source_identity() -> String {
    let manifest =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR"));
    let workspace = manifest.join("../..");
    let revision = Command::new("/usr/bin/git")
        .arg("-C")
        .arg(&workspace)
        .args(["rev-parse", "--verify", "HEAD"])
        .output()
        .expect("run git rev-parse for bound benchmark build");
    assert!(
        revision.status.success(),
        "bound benchmark build requires a readable Git HEAD"
    );
    let revision = String::from_utf8(revision.stdout)
        .expect("Git HEAD must be UTF-8")
        .trim()
        .to_owned();
    assert!(
        valid_source_identity(&revision) && !revision.ends_with("-dirty"),
        "Git HEAD must be a lowercase 40-digit object id"
    );
    let status = Command::new("/usr/bin/git")
        .arg("-C")
        .arg(&workspace)
        .args(["status", "--porcelain", "--untracked-files=normal"])
        .output()
        .expect("run git status for bound benchmark build");
    assert!(
        status.status.success(),
        "bound benchmark build requires readable Git status"
    );
    if status.stdout.is_empty() {
        revision
    } else {
        format!("{revision}-dirty")
    }
}

fn embed_file_hash(variable: &str, relative: &str) {
    println!("cargo:rerun-if-changed={relative}");
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR");
    let path = Path::new(&manifest).join(relative);
    let bytes = fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    println!("cargo:rustc-env={variable}={}", hex(&Sha256::digest(bytes)));
}

fn embed_snapshot_source_set() {
    const DOMAIN: &[u8] = b"npa-snap-source-set-v1\0";
    let manifest =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR"));
    let workspace = manifest
        .join("../..")
        .canonicalize()
        .expect("canonical npa-core workspace");
    let mut paths = Vec::new();
    push_regular_source(&workspace, &workspace.join("Cargo.toml"), &mut paths);
    for crate_name in [
        "npa-api",
        "npa-cert",
        "npa-checker-ref",
        "npa-cli",
        "npa-frontend",
        "npa-kernel",
        "npa-package",
        "npa-tactic",
    ] {
        let crate_root = workspace.join("crates").join(crate_name);
        push_regular_source(&workspace, &crate_root.join("Cargo.toml"), &mut paths);
        let build_script = crate_root.join("build.rs");
        if build_script.exists() {
            push_regular_source(&workspace, &build_script, &mut paths);
        }
        collect_rust_sources(&workspace, &crate_root.join("src"), &mut paths);
    }
    for path in [
        workspace.join("crates/npa-cli/examples/bench_package_artifact_snapshot.rs"),
        workspace.join("crates/npa-cli/examples/measure_process.rs"),
        workspace.join("crates/npa-api/examples/support/performance_fixture_generator.rs"),
        workspace.join("crates/npa-api/examples/support/closed_private_tree.rs"),
        workspace.join("crates/npa-api/examples/support/runtime_source_set.rs"),
        workspace.join("crates/npa-api/examples/support/sealed_performance_run.rs"),
        workspace.join("crates/npa-api/examples/support/snap_vmsp_controller.rs"),
    ] {
        push_regular_source(&workspace, &path, &mut paths);
    }
    paths.sort();
    paths.dedup();
    let (digest, serialized_paths) = hash_source_set(&workspace, DOMAIN, &paths);
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_SHA256={}",
        hex(&digest)
    );
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAPSHOT_SOURCE_SET_PATHS={}",
        serialized_paths.join(",")
    );
}

fn embed_snap_vmsp_manager_source_set() {
    const DOMAIN: &[u8] = b"npa-snap-vmsp-manager-source-set-v1\0";
    let manifest =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR"));
    let workspace = manifest
        .join("../..")
        .canonicalize()
        .expect("canonical npa-core workspace");
    let mut paths = Vec::new();
    push_regular_source(&workspace, &workspace.join("Cargo.toml"), &mut paths);
    for crate_name in [
        "npa-api",
        "npa-cert",
        "npa-checker-ref",
        "npa-cli",
        "npa-frontend",
        "npa-kernel",
        "npa-package",
        "npa-tactic",
    ] {
        let crate_root = workspace.join("crates").join(crate_name);
        push_regular_source(&workspace, &crate_root.join("Cargo.toml"), &mut paths);
        let build_script = crate_root.join("build.rs");
        if build_script.exists() {
            push_regular_source(&workspace, &build_script, &mut paths);
        }
        collect_rust_sources(&workspace, &crate_root.join("src"), &mut paths);
    }
    for path in [
        workspace.join("crates/npa-cli/examples/bench_package_artifact_snapshot.rs"),
        workspace.join("crates/npa-api/examples/bench_shared_payload.rs"),
        workspace.join("crates/npa-cli/examples/measure_process.rs"),
        workspace.join("crates/npa-api/examples/support/performance_fixture_generator.rs"),
        workspace.join("crates/npa-api/examples/support/closed_private_tree.rs"),
        workspace.join("crates/npa-api/examples/support/runtime_source_set.rs"),
        workspace.join("crates/npa-api/examples/support/sealed_performance_run.rs"),
        workspace.join("crates/npa-api/examples/support/snap_vmsp_controller.rs"),
        workspace.join("scripts/check-performance.sh"),
    ] {
        push_regular_source(&workspace, &path, &mut paths);
    }
    paths.sort();
    paths.dedup();
    let (digest, serialized_paths) = hash_source_set(&workspace, DOMAIN, &paths);
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAP_VMSP_MANAGER_SOURCE_SET_SHA256={}",
        hex(&digest)
    );
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_SNAP_VMSP_MANAGER_SOURCE_SET_PATHS={}",
        serialized_paths.join(",")
    );
}

fn embed_vmsp_benchmark_source_set() {
    const DOMAIN: &[u8] = b"npa-vmsp-source-set-v1\0";
    let manifest =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR"));
    let workspace = manifest
        .join("../..")
        .canonicalize()
        .expect("canonical npa-core workspace");
    let mut paths = Vec::new();
    push_regular_source(&workspace, &workspace.join("Cargo.toml"), &mut paths);
    for crate_name in [
        "npa-api",
        "npa-cert",
        "npa-checker-ref",
        "npa-frontend",
        "npa-kernel",
        "npa-package",
        "npa-tactic",
    ] {
        let crate_root = workspace.join("crates").join(crate_name);
        push_regular_source(&workspace, &crate_root.join("Cargo.toml"), &mut paths);
        let build_script = crate_root.join("build.rs");
        if build_script.exists() {
            push_regular_source(&workspace, &build_script, &mut paths);
        }
        collect_rust_sources(&workspace, &crate_root.join("src"), &mut paths);
    }
    for path in [
        workspace.join("crates/npa-api/examples/bench_shared_payload.rs"),
        workspace.join("crates/npa-api/examples/support/performance_fixture_generator.rs"),
        workspace.join("crates/npa-api/examples/support/closed_private_tree.rs"),
        workspace.join("crates/npa-api/examples/support/runtime_source_set.rs"),
        workspace.join("crates/npa-api/examples/support/sealed_performance_run.rs"),
        workspace.join("crates/npa-cli/examples/measure_process.rs"),
    ] {
        push_regular_source(&workspace, &path, &mut paths);
    }
    paths.sort();
    paths.dedup();
    let (digest, _) = hash_source_set(&workspace, DOMAIN, &paths);
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_VMSP_BENCHMARK_SOURCE_SET_SHA256={}",
        hex(&digest)
    );
}

fn embed_gitsel_source_set() {
    const DOMAIN: &[u8] = b"npa-gitsel-source-set-v1\0";
    let manifest =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR"));
    let workspace = manifest
        .join("../..")
        .canonicalize()
        .expect("canonical npa-core workspace");
    let mut paths = Vec::new();
    push_regular_source(&workspace, &workspace.join("Cargo.toml"), &mut paths);
    for crate_name in [
        "npa-api",
        "npa-cert",
        "npa-checker-ref",
        "npa-cli",
        "npa-frontend",
        "npa-kernel",
        "npa-package",
        "npa-tactic",
    ] {
        let crate_root = workspace.join("crates").join(crate_name);
        push_regular_source(&workspace, &crate_root.join("Cargo.toml"), &mut paths);
        let build_script = crate_root.join("build.rs");
        if build_script.exists() {
            push_regular_source(&workspace, &build_script, &mut paths);
        }
        collect_rust_sources(&workspace, &crate_root.join("src"), &mut paths);
    }
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-cli/examples/bench_package_changed_selection.rs"),
        &mut paths,
    );
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-api/examples/support/closed_private_tree.rs"),
        &mut paths,
    );
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-api/examples/support/sealed_performance_run.rs"),
        &mut paths,
    );
    paths.sort();
    paths.dedup();
    let (digest, serialized_paths) = hash_source_set(&workspace, DOMAIN, &paths);
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_GITSEL_SOURCE_SET_SHA256={}",
        hex(&digest)
    );
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_GITSEL_SOURCE_SET_PATHS={}",
        serialized_paths.join(",")
    );
}

fn embed_tbac_source_set() {
    const DOMAIN: &[u8] = b"npa-tbac-source-set-v1\0";
    let manifest =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR"));
    let workspace = manifest
        .join("../..")
        .canonicalize()
        .expect("canonical npa-core workspace");
    let mut paths = Vec::new();
    push_regular_source(&workspace, &workspace.join("Cargo.toml"), &mut paths);
    for crate_name in [
        "npa-api",
        "npa-cert",
        "npa-checker-ref",
        "npa-cli",
        "npa-frontend",
        "npa-kernel",
        "npa-package",
        "npa-tactic",
    ] {
        let crate_root = workspace.join("crates").join(crate_name);
        push_regular_source(&workspace, &crate_root.join("Cargo.toml"), &mut paths);
        let build_script = crate_root.join("build.rs");
        if build_script.exists() {
            push_regular_source(&workspace, &build_script, &mut paths);
        }
        collect_rust_sources(&workspace, &crate_root.join("src"), &mut paths);
    }
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-cli/examples/targeted_build_certs_bench.rs"),
        &mut paths,
    );
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-api/examples/support/closed_private_tree.rs"),
        &mut paths,
    );
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-api/examples/support/runtime_source_set.rs"),
        &mut paths,
    );
    push_regular_source(
        &workspace,
        &workspace.join("crates/npa-api/examples/support/sealed_performance_run.rs"),
        &mut paths,
    );
    paths.sort();
    paths.dedup();
    let (digest, serialized_paths) = hash_source_set(&workspace, DOMAIN, &paths);
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_TBAC_SOURCE_SET_SHA256={}",
        hex(&digest)
    );
    println!(
        "cargo:rustc-env=NPA_CLI_BUILD_TBAC_SOURCE_SET_PATHS={}",
        serialized_paths.join(",")
    );
}

fn hash_source_set(workspace: &Path, domain: &[u8], paths: &[PathBuf]) -> (Vec<u8>, Vec<String>) {
    assert!(!paths.is_empty(), "source set must not be empty");
    let mut digest = Sha256::new();
    digest.update(domain);
    let mut serialized_paths = Vec::with_capacity(paths.len());
    for relative in paths {
        let relative_text = relative
            .to_str()
            .expect("source-set path must be UTF-8")
            .replace('\\', "/");
        assert!(
            !relative_text.contains(','),
            "source-set path must not contain a comma"
        );
        let absolute = workspace.join(relative);
        let bytes = fs::read(&absolute)
            .unwrap_or_else(|error| panic!("read {}: {error}", absolute.display()));
        digest.update(
            u64::try_from(relative_text.len())
                .expect("source-set path length fits u64")
                .to_le_bytes(),
        );
        digest.update(relative_text.as_bytes());
        digest.update(
            u64::try_from(bytes.len())
                .expect("source-set byte length fits u64")
                .to_le_bytes(),
        );
        digest.update(&bytes);
        println!("cargo:rerun-if-changed={}", absolute.display());
        serialized_paths.push(relative_text);
    }
    (digest.finalize().to_vec(), serialized_paths)
}

fn collect_rust_sources(workspace: &Path, directory: &Path, paths: &mut Vec<PathBuf>) {
    let metadata = fs::symlink_metadata(directory)
        .unwrap_or_else(|error| panic!("inspect {}: {error}", directory.display()));
    assert!(
        metadata.file_type().is_dir() && !metadata.file_type().is_symlink(),
        "source-set directory must be a real directory: {}",
        directory.display()
    );
    let mut entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()))
        .map(|entry| entry.expect("read source-set directory entry").path())
        .collect::<Vec<_>>();
    entries.sort();
    for entry in entries {
        let metadata = fs::symlink_metadata(&entry)
            .unwrap_or_else(|error| panic!("inspect {}: {error}", entry.display()));
        assert!(
            !metadata.file_type().is_symlink(),
            "source set rejects symbolic links: {}",
            entry.display()
        );
        if metadata.file_type().is_dir() {
            collect_rust_sources(workspace, &entry, paths);
        } else if entry.extension().and_then(|extension| extension.to_str()) == Some("rs") {
            push_regular_source(workspace, &entry, paths);
        }
    }
}

fn push_regular_source(workspace: &Path, path: &Path, paths: &mut Vec<PathBuf>) {
    let metadata = fs::symlink_metadata(path)
        .unwrap_or_else(|error| panic!("inspect {}: {error}", path.display()));
    assert!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "source-set member must be a real regular file: {}",
        path.display()
    );
    let canonical = path
        .canonicalize()
        .unwrap_or_else(|error| panic!("canonicalize {}: {error}", path.display()));
    assert!(
        canonical.starts_with(workspace),
        "source-set member escaped workspace: {}",
        canonical.display()
    );
    let relative = canonical
        .strip_prefix(workspace)
        .expect("source-set member is inside workspace")
        .to_path_buf();
    relative.to_str().expect("source-set path must be UTF-8");
    paths.push(relative);
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    encoded
}
