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
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DEFAULT");
    println!("cargo:rerun-if-env-changed=NPA_BENCH_SOURCE_IDENTITY");

    println!("cargo:rerun-if-changed=../../Cargo.lock");
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("Cargo supplies CARGO_MANIFEST_DIR");
    let cargo_lock = Path::new(&manifest).join("../../Cargo.lock");
    let cargo_lock_bytes = fs::read(&cargo_lock)
        .unwrap_or_else(|error| panic!("read {}: {error}", cargo_lock.display()));
    println!(
        "cargo:rustc-env=NPA_BUILD_CARGO_LOCK_SHA256={}",
        hex(&Sha256::digest(cargo_lock_bytes))
    );
    let workspace = Path::new(&manifest).join("../..");
    let cvr_source_set = cvr_source_set(&workspace);
    println!(
        "cargo:rustc-env=NPA_BUILD_CVR_SOURCE_SET_SHA256={}",
        source_set_sha256(&cvr_source_set)
    );
    println!(
        "cargo:rustc-env=NPA_BUILD_CVR_SOURCE_SET_PATHS={}",
        cvr_source_set
            .iter()
            .map(|(relative, _)| relative.as_str())
            .collect::<Vec<_>>()
            .join(",")
    );

    let source_identity =
        env::var("NPA_BENCH_SOURCE_IDENTITY").unwrap_or_else(|_| "unbound".to_owned());
    assert!(
        source_identity == "unbound" || valid_source_identity(&source_identity),
        "NPA_BENCH_SOURCE_IDENTITY must be a lowercase 40-digit Git OID with optional -dirty suffix"
    );
    if source_identity != "unbound" {
        assert_eq!(
            source_identity,
            current_source_identity(&workspace),
            "NPA_BENCH_SOURCE_IDENTITY must identify the current Git worktree"
        );
    }
    println!("cargo:rustc-env=NPA_BUILD_SOURCE_IDENTITY={source_identity}");

    let profile = env::var("PROFILE").expect("Cargo supplies PROFILE to build scripts");
    let cargo_profile = match profile.as_str() {
        "debug" => "dev",
        profile => profile,
    };
    println!("cargo:rustc-env=NPA_BUILD_CARGO_PROFILE={cargo_profile}");
    let target = env::var("TARGET").expect("Cargo supplies TARGET to build scripts");
    assert!(!target.is_empty(), "Cargo TARGET must be non-empty");
    println!("cargo:rustc-env=NPA_BUILD_TARGET={target}");

    let mut features = env::vars()
        .filter_map(|(name, _)| {
            let feature = name.strip_prefix("CARGO_FEATURE_")?;
            Some(match feature {
                "DEFAULT" => "default",
                unknown => panic!("unmapped npa-cert Cargo feature {unknown}"),
            })
        })
        .collect::<Vec<_>>();
    features.sort();
    features.dedup();
    println!(
        "cargo:rustc-env=NPA_BUILD_CARGO_FEATURES={}",
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
        "cargo:rustc-env=NPA_BUILD_RUSTC_VV_HEX={}",
        hex(rustc_vv.as_bytes())
    );
    let rustflags = env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    println!(
        "cargo:rustc-env=NPA_BUILD_RUSTFLAGS_HEX={}",
        hex(rustflags.as_bytes())
    );
}

fn cvr_source_set(workspace: &Path) -> Vec<(String, PathBuf)> {
    let mut relative_paths = vec![
        "Cargo.toml".to_owned(),
        "crates/npa-api/examples/support/closed_private_tree.rs".to_owned(),
        "crates/npa-api/examples/support/runtime_source_set.rs".to_owned(),
        "crates/npa-cert/Cargo.toml".to_owned(),
        "crates/npa-cert/build.rs".to_owned(),
        "crates/npa-kernel/Cargo.toml".to_owned(),
    ];
    for directory in ["crates/npa-cert/src", "crates/npa-kernel/src"] {
        collect_rust_sources(workspace, &workspace.join(directory), &mut relative_paths);
    }
    relative_paths.sort();
    relative_paths.dedup();
    relative_paths
        .into_iter()
        .map(|relative| {
            let path = workspace.join(&relative);
            (relative, path)
        })
        .collect()
}

fn collect_rust_sources(workspace: &Path, directory: &Path, relative_paths: &mut Vec<String>) {
    println!("cargo:rerun-if-changed={}", directory.display());
    let mut entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("read source directory {}: {error}", directory.display()))
        .map(|entry| entry.unwrap_or_else(|error| panic!("read source entry: {error}")))
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("inspect {}: {error}", path.display()));
        assert!(
            !metadata.file_type().is_symlink(),
            "CVR source set may not contain a symlink: {}",
            path.display()
        );
        if metadata.is_dir() {
            collect_rust_sources(workspace, &path, relative_paths);
        } else if metadata.is_file() && path.extension().is_some_and(|value| value == "rs") {
            let relative = path
                .strip_prefix(workspace)
                .expect("CVR source must remain below workspace")
                .to_str()
                .expect("CVR source path must be UTF-8")
                .replace('\\', "/");
            relative_paths.push(relative);
        }
    }
}

fn source_set_sha256(entries: &[(String, PathBuf)]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"npa-cvr-source-set-v2\0");
    for (relative, path) in entries {
        println!("cargo:rerun-if-changed={}", path.display());
        let bytes =
            fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        let relative_bytes = relative.as_bytes();
        digest.update(
            u64::try_from(relative_bytes.len())
                .expect("source path length fits u64")
                .to_le_bytes(),
        );
        digest.update(relative_bytes);
        digest.update(
            u64::try_from(bytes.len())
                .expect("source byte length fits u64")
                .to_le_bytes(),
        );
        digest.update(&bytes);
    }
    hex(&digest.finalize())
}

fn valid_source_identity(value: &str) -> bool {
    let oid = value.strip_suffix("-dirty").unwrap_or(value);
    oid.len() == 40
        && oid
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn current_source_identity(workspace: &Path) -> String {
    let revision = Command::new("/usr/bin/git")
        .arg("-C")
        .arg(workspace)
        .args(["rev-parse", "--verify", "HEAD"])
        .output()
        .expect("run git rev-parse for bound CVR benchmark build");
    assert!(
        revision.status.success(),
        "bound CVR build requires a readable Git HEAD"
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
        .arg(workspace)
        .args(["status", "--porcelain", "--untracked-files=normal"])
        .output()
        .expect("run git status for bound CVR benchmark build");
    assert!(
        status.status.success(),
        "bound CVR benchmark build requires readable Git status"
    );
    if status.stdout.is_empty() {
        revision
    } else {
        format!("{revision}-dirty")
    }
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
