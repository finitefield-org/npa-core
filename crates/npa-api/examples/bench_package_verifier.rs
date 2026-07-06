//! Temporary benchmark harness for the source-free package verifiers.
//!
//! Mirrors the `package_verifier` corpus tests: reads `proofs/npa-package.toml`
//! and `proofs/generated/package-lock.json`, then runs the fast kernel verifier
//! and the reference checker over the full corpus, printing wall times.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use npa_api::{
    verify_package_fast_source_free, verify_package_reference_source_free,
    PackageCertificateArtifact,
};
use npa_package::{parse_and_validate_manifest_str, parse_package_lock_json, PackagePath};

fn main() {
    let root = repo_root().join("proofs");
    let manifest_source =
        std::fs::read_to_string(root.join("npa-package.toml")).expect("manifest readable");
    let validated = parse_and_validate_manifest_str(&manifest_source).expect("manifest valid");
    let lock_source = std::fs::read_to_string(root.join("generated/package-lock.json"))
        .expect("package lock readable");
    let lock = parse_package_lock_json(&lock_source).expect("package lock valid");
    let artifacts: BTreeMap<PackagePath, Vec<u8>> = lock
        .entries
        .iter()
        .map(|entry| {
            (
                entry.certificate.clone(),
                std::fs::read(root.join(entry.certificate.as_str())).expect("cert readable"),
            )
        })
        .collect();
    let total_bytes: usize = artifacts.values().map(Vec::len).sum();
    println!(
        "modules: {}, certificate bytes: {}",
        lock.entries.len(),
        total_bytes
    );

    let mode = std::env::args().nth(1).unwrap_or_else(|| "both".to_owned());

    let child = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            if mode == "fast" || mode == "both" {
                let start = Instant::now();
                let report = verify_package_fast_source_free(
                    &validated,
                    &lock,
                    package_artifacts(&artifacts),
                )
                .expect("fast verification runs");
                println!(
                    "fast-kernel: {:?} status={}",
                    start.elapsed(),
                    report.status.as_str()
                );
            }
            if mode == "reference" || mode == "both" {
                let start = Instant::now();
                let report = verify_package_reference_source_free(
                    &validated,
                    &lock,
                    package_artifacts(&artifacts),
                )
                .expect("reference verification runs");
                println!(
                    "reference: {:?} status={}",
                    start.elapsed(),
                    report.status.as_str()
                );
            }
        })
        .expect("bench thread spawns");
    child.join().expect("bench thread joins");
}

fn package_artifacts(
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Vec<PackageCertificateArtifact<'_>> {
    artifacts
        .iter()
        .map(|(path, bytes)| PackageCertificateArtifact {
            path: path.clone(),
            bytes: bytes.as_slice(),
        })
        .collect()
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-api crate lives under crates/")
        .to_path_buf()
}
