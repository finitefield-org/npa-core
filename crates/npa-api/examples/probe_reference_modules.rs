use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::num::{NonZeroU64, NonZeroUsize};
use std::path::{Path, PathBuf};
use std::time::Instant;

use npa_api::{
    verify_package_reference_source_free_with_options, PackageCertificateArtifact,
    PackageModuleVerificationStatus, PackageVerificationExecutionOptions,
    PackageVerificationMemoMode, PackageVerificationProcessMemoHandle,
    PackageVerificationProcessMemoLimits,
};
use npa_package::{parse_and_validate_manifest_str, parse_package_lock_json, PackagePath};

#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;

const MAX_MANIFEST_BYTES: u64 = 8 * 1024 * 1024;
const MAX_PACKAGE_LOCK_BYTES: u64 = 16 * 1024 * 1024;
const MAX_PACKAGE_CERTIFICATES: usize = 4_096;
const MAX_PACKAGE_CERTIFICATE_BYTES: u64 = npa_cert::MAX_CERTIFICATE_BYTES as u64;
const MAX_TOTAL_CERTIFICATE_BYTES: u64 = MAX_PACKAGE_CERTIFICATE_BYTES;

fn main() {
    if let Err(error) = run() {
        eprintln!("probe_reference_modules: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let root = repo_root()?.join("proofs");
    let manifest_source = read_utf8_regular_file(
        &root.join("npa-package.toml"),
        MAX_MANIFEST_BYTES,
        "package manifest",
    )?;
    let validated = parse_and_validate_manifest_str(&manifest_source)
        .map_err(|error| format!("invalid package manifest: {error}"))?;
    let lock_source = read_utf8_regular_file(
        &root.join("generated/package-lock.json"),
        MAX_PACKAGE_LOCK_BYTES,
        "package lock",
    )?;
    let lock = parse_package_lock_json(&lock_source)
        .map_err(|error| format!("invalid package lock: {error}"))?;
    if lock.entries.len() > MAX_PACKAGE_CERTIFICATES {
        return Err(format!(
            "package lock has more than {MAX_PACKAGE_CERTIFICATES} certificates"
        ));
    }
    let mut total_certificate_bytes = 0_u64;
    let artifacts: BTreeMap<PackagePath, Vec<u8>> = lock
        .entries
        .iter()
        .map(|entry| {
            let bytes = closed_private_tree::read_absolute_regular_file(
                &root.join(entry.certificate.as_str()),
                MAX_PACKAGE_CERTIFICATE_BYTES,
                "package certificate",
            )?;
            total_certificate_bytes = total_certificate_bytes
                .checked_add(u64::try_from(bytes.len()).map_err(|error| error.to_string())?)
                .ok_or_else(|| "aggregate package certificate bytes overflowed".to_owned())?;
            if total_certificate_bytes > MAX_TOTAL_CERTIFICATE_BYTES {
                return Err(format!(
                    "aggregate package certificate bytes exceed {MAX_TOTAL_CERTIFICATE_BYTES}"
                ));
            }
            Ok((entry.certificate.clone(), bytes))
        })
        .collect::<Result<_, String>>()?;
    let memo_handle =
        PackageVerificationProcessMemoHandle::new(PackageVerificationProcessMemoLimits {
            max_entries: NonZeroUsize::new(lock.entries.len())
                .ok_or_else(|| "proof package has no certificates".to_owned())?,
            max_weighted_certificate_bytes: NonZeroU64::new(
                artifacts
                    .values()
                    .map(|bytes| u64::try_from(bytes.len()).unwrap_or(u64::MAX))
                    .fold(0, u64::saturating_add),
            )
            .ok_or_else(|| "proof package certificates contain no bytes".to_owned())?,
        });

    for entry in &lock.entries {
        let module = entry.module.clone();
        let start = Instant::now();
        print!("checking {} ... ", module.as_dotted());
        std::io::stdout()
            .flush()
            .map_err(|error| format!("stdout flush failed: {error}"))?;
        let report = verify_package_reference_source_free_with_options(
            &validated,
            &lock,
            package_artifacts(&artifacts),
            PackageVerificationExecutionOptions {
                jobs: 1,
                selected_modules: Some(BTreeSet::from([module.clone()])),
                memoization: PackageVerificationMemoMode::ProcessLocal(memo_handle.clone()),
                collect_decode_cache_counters: false,
                ..PackageVerificationExecutionOptions::default()
            },
        )
        .map_err(|error| format!("reference verification failed: {error:?}"))?;
        let failed = report
            .modules
            .iter()
            .find(|result| result.status == PackageModuleVerificationStatus::Failed);
        match failed {
            Some(result) => {
                println!("FAILED after {:?}", start.elapsed());
                println!("failed_module={}", result.module.as_dotted());
                println!("error={:?}", result.error);
                return Err(format!(
                    "reference verification rejected {}",
                    result.module.as_dotted()
                ));
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
    Ok(())
}

fn read_utf8_regular_file(path: &Path, limit: u64, label: &str) -> Result<String, String> {
    let bytes = closed_private_tree::read_absolute_regular_file(path, limit, label)?;
    String::from_utf8(bytes).map_err(|error| format!("{label} is not UTF-8: {error}"))
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

fn repo_root() -> Result<PathBuf, String> {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .ok_or_else(|| "npa-api crate is not nested below the workspace root".to_owned())
}
