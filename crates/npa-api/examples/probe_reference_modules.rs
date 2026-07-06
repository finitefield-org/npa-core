use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

use npa_api::{
    verify_package_reference_source_free_with_options, PackageCertificateArtifact,
    PackageModuleVerificationStatus, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode,
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

    for entry in &lock.entries {
        let module = entry.module.clone();
        let start = Instant::now();
        print!("checking {} ... ", module.as_dotted());
        std::io::stdout().flush().expect("stdout flushes");
        let report = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 1,
                selected_modules: Some(BTreeSet::from([module.clone()])),
                memoization: PackageVerificationMemoMode::ProcessLocal,
                collect_decode_cache_counters: false,
            },
        )
        .expect("reference verification runs");
        let failed = report
            .modules
            .iter()
            .find(|result| result.status == PackageModuleVerificationStatus::Failed);
        match failed {
            Some(result) => {
                println!("FAILED after {:?}", start.elapsed());
                println!("failed_module={}", result.module.as_dotted());
                println!("error={:?}", result.error);
                std::process::exit(1);
            }
            None => {
                println!(
                    "ok after {:?} memo_hits={} memo_misses={} memo_inserted={}",
                    start.elapsed(),
                    report.memo_counters.hits,
                    report.memo_counters.misses,
                    report.memo_counters.inserted
                );
            }
        }
    }
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
