//! Bounded physical storage of the unchanged canonical theorem-premise report.
//!
//! Small reports keep their original bytes. Larger reports use an atomic index
//! over immutable, content-addressed byte chunks. This is transport metadata,
//! not a new theorem-report schema or any form of proof evidence.

use std::{io, path::Path};

use npa_api::{JsonDocument, JsonParseLimits, JsonValue};
use npa_package::{
    format_package_hash, package_file_hash, parse_package_hash, PackageHash, PackagePath,
};

use crate::generated_artifact_writer::{
    read_package_generated_artifact_no_follow, write_package_generated_artifact_atomic,
    write_package_generated_artifact_under_lock,
};
use crate::package_artifacts::PACKAGE_THEOREM_PREMISE_REPORT_PATH;
use crate::package_promotion_transaction::TargetLock;

const STORAGE_SCHEMA: &str = "npa.package.theorem_premise_report_chunks.v0.1";
const CHUNK_DIRECTORY: &str = "generated/theorem-premise-report-chunks";
// These do not change the shared 128 MiB regular-file I/O guard.
const INLINE_BYTES: usize = 128 * 1024 * 1024;
const CHUNK_BYTES: usize = 16 * 1024 * 1024;
const MAX_CHUNKS: usize = 32;
const MAX_REPORT_BYTES: usize = CHUNK_BYTES * MAX_CHUNKS;
const MAX_INDEX_BYTES: usize = 16 * 1024;

#[derive(Debug)]
struct Chunk {
    hash: PackageHash,
    bytes: usize,
}

#[derive(Debug)]
struct Index {
    report_hash: PackageHash,
    report_bytes: usize,
    chunks: Vec<Chunk>,
}

impl Index {
    fn canonical_json(&self) -> String {
        let chunks = self
            .chunks
            .iter()
            .map(|chunk| {
                format!(
                    "    {{\"file_hash\": \"{}\", \"bytes\": {}}}",
                    format_package_hash(&chunk.hash),
                    chunk.bytes,
                )
            })
            .collect::<Vec<_>>()
            .join(",\n");
        format!(
            "{{\n  \"schema\": \"{STORAGE_SCHEMA}\",\n  \"logical_report_file_hash\": \"{}\",\n  \"logical_report_bytes\": {},\n  \"chunks\": [\n{chunks}\n  ]\n}}\n",
            format_package_hash(&self.report_hash), self.report_bytes,
        )
    }

    fn parse(source: &str) -> io::Result<Option<Self>> {
        // Do not parse a large inline report twice just to detect its transport.
        // Non-index input is still validated by the ordinary report parser.
        let index_prefix = format!("{{\n  \"schema\": \"{STORAGE_SCHEMA}\",");
        let has_index_prefix = source.starts_with(&index_prefix);
        if source.len() > MAX_INDEX_BYTES {
            if has_index_prefix {
                return Err(invalid_storage(
                    "report storage index exceeds its byte limit",
                ));
            }
            return Ok(None);
        }
        let Ok(document) = JsonDocument::parse_with_limits(
            source,
            JsonParseLimits::bounded(8, 256, 128, MAX_INDEX_BYTES, 1024),
        ) else {
            if has_index_prefix {
                return Err(invalid_storage(
                    "invalid or over-limit report storage index",
                ));
            }
            return Ok(None);
        };
        let root = document.root();
        if field(root, "schema").and_then(JsonValue::string_value) != Some(STORAGE_SCHEMA) {
            return Ok(None);
        }
        require_fields(
            root,
            &[
                "schema",
                "logical_report_file_hash",
                "logical_report_bytes",
                "chunks",
            ],
        )?;
        let report_hash = hash_field(root, "logical_report_file_hash")?;
        let report_bytes = size_field(root, "logical_report_bytes")?;
        if report_bytes == 0 || report_bytes > MAX_REPORT_BYTES {
            return Err(invalid_storage(
                "logical report exceeds its bounded storage size",
            ));
        }
        let rows = field(root, "chunks")
            .and_then(JsonValue::array_elements)
            .ok_or_else(|| invalid_storage("missing chunk array"))?;
        if rows.is_empty() || rows.len() > MAX_CHUNKS {
            return Err(invalid_storage("invalid chunk count"));
        }
        let mut chunks = Vec::with_capacity(rows.len());
        let mut total = 0usize;
        for row in rows {
            require_fields(row, &["file_hash", "bytes"])?;
            let hash = hash_field(row, "file_hash")?;
            let bytes = size_field(row, "bytes")?;
            if bytes == 0 || bytes > CHUNK_BYTES {
                return Err(invalid_storage("invalid chunk byte length"));
            }
            total = total
                .checked_add(bytes)
                .filter(|total| *total <= MAX_REPORT_BYTES)
                .ok_or_else(|| invalid_storage("chunk byte total exceeds the storage limit"))?;
            chunks.push(Chunk { hash, bytes });
        }
        if total != report_bytes {
            return Err(invalid_storage(
                "chunk byte total differs from logical report size",
            ));
        }
        let index = Self {
            report_hash,
            report_bytes,
            chunks,
        };
        if index.canonical_json() != source {
            return Err(invalid_storage("noncanonical report storage index"));
        }
        Ok(Some(index))
    }
}

fn field<'a, 'src>(value: &'a JsonValue<'src>, name: &str) -> Option<&'a JsonValue<'src>> {
    value
        .object_members()?
        .iter()
        .find(|member| member.key() == name)
        .map(|member| member.value())
}

fn require_fields(value: &JsonValue<'_>, names: &[&str]) -> io::Result<()> {
    let members = value
        .object_members()
        .ok_or_else(|| invalid_storage("expected storage object"))?;
    if members.len() != names.len()
        || names.iter().any(|name| {
            members
                .iter()
                .filter(|member| member.key() == *name)
                .count()
                != 1
        })
    {
        return Err(invalid_storage(
            "unknown, missing, or duplicate storage field",
        ));
    }
    Ok(())
}

fn size_field(value: &JsonValue<'_>, name: &str) -> io::Result<usize> {
    field(value, name)
        .and_then(JsonValue::number_raw)
        .and_then(|value| value.parse::<usize>().ok())
        .ok_or_else(|| invalid_storage("invalid storage byte length"))
}

fn hash_field(value: &JsonValue<'_>, name: &str) -> io::Result<PackageHash> {
    let value = field(value, name)
        .and_then(JsonValue::string_value)
        .ok_or_else(|| invalid_storage("invalid storage file hash"))?;
    parse_package_hash(value, name).map_err(|_| invalid_storage("invalid storage file hash"))
}

fn chunk_path(hash: &PackageHash) -> PackagePath {
    let hash = format_package_hash(hash);
    // The locator is derived, never supplied by untrusted index paths.
    PackagePath::new(format!("{CHUNK_DIRECTORY}/{}.part", &hash[7..]))
}

fn invalid_storage(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

pub(crate) fn write_report(
    root: &Path,
    report: &str,
    lock: &TargetLock,
) -> io::Result<Vec<PackagePath>> {
    if report.len() <= INLINE_BYTES {
        write_package_generated_artifact_under_lock(
            root,
            &PackagePath::new(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
            report.as_bytes(),
            lock,
        )?;
        return Ok(Vec::new());
    }
    write_chunked_report(root, report.as_bytes(), CHUNK_BYTES, lock)
}

fn write_chunked_report(
    root: &Path,
    report: &[u8],
    chunk_bytes: usize,
    lock: &TargetLock,
) -> io::Result<Vec<PackagePath>> {
    // Validate the whole layout before any I/O. The private chunk-size argument
    // lets compact tests exercise the exact production path, without a CLI knob.
    if chunk_bytes == 0
        || chunk_bytes > CHUNK_BYTES
        || report.is_empty()
        || report.len() > MAX_REPORT_BYTES
        || report.len().div_ceil(chunk_bytes) > MAX_CHUNKS
    {
        return Err(invalid_storage(
            "report cannot fit the bounded chunk layout",
        ));
    }
    let index = Index {
        report_hash: package_file_hash(report),
        report_bytes: report.len(),
        chunks: report
            .chunks(chunk_bytes)
            .map(|bytes| Chunk {
                hash: package_file_hash(bytes),
                bytes: bytes.len(),
            })
            .collect(),
    };
    let json = index.canonical_json();
    if json.len() > MAX_INDEX_BYTES {
        return Err(invalid_storage(
            "report storage index exceeds its byte limit",
        ));
    }
    let mut paths = Vec::with_capacity(index.chunks.len());
    for (chunk, bytes) in index.chunks.iter().zip(report.chunks(chunk_bytes)) {
        lock.ensure_target_identity()?;
        let path = chunk_path(&chunk.hash);
        write_package_generated_artifact_atomic(root, &path, bytes)?;
        if !paths.contains(&path) {
            paths.push(path);
        }
    }
    // Content-addressed chunks are immutable and retained. Publish the root
    // last: concurrent readers see either complete old bytes or complete new
    // bytes; failed writes cannot invalidate an already published index.
    write_package_generated_artifact_under_lock(
        root,
        &PackagePath::new(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
        json.as_bytes(),
        lock,
    )?;
    Ok(paths)
}

pub(crate) fn read_report(root: &Path) -> io::Result<String> {
    let bytes = read_package_generated_artifact_no_follow(
        root,
        &PackagePath::new(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
    )?;
    let source = String::from_utf8(bytes).map_err(|_| invalid_storage("report is not UTF-8"))?;
    let Some(index) = Index::parse(&source)? else {
        return Ok(source);
    };
    let mut report = Vec::new();
    report
        .try_reserve_exact(index.report_bytes)
        .map_err(|_| invalid_storage("cannot allocate bounded report buffer"))?;
    for chunk in &index.chunks {
        let bytes = read_package_generated_artifact_no_follow(root, &chunk_path(&chunk.hash))?;
        if bytes.len() != chunk.bytes || package_file_hash(&bytes) != chunk.hash {
            return Err(invalid_storage("report chunk size or hash mismatch"));
        }
        report.extend_from_slice(&bytes);
    }
    if report.len() != index.report_bytes || package_file_hash(&report) != index.report_hash {
        return Err(invalid_storage("logical report size or hash mismatch"));
    }
    String::from_utf8(report).map_err(|_| invalid_storage("reconstructed report is not UTF-8"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static NEXT_TEST: AtomicUsize = AtomicUsize::new(0);

    struct TempRoot(PathBuf);

    impl TempRoot {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "npa-premise-storage-{}-{}",
                std::process::id(),
                NEXT_TEST.fetch_add(1, Ordering::SeqCst),
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn index_bytes(&self) -> Vec<u8> {
            fs::read(self.0.join(PACKAGE_THEOREM_PREMISE_REPORT_PATH)).unwrap()
        }
    }

    impl Drop for TempRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn premise_storage_inline_bytes_and_chunked_utf8_roundtrip_are_identical() {
        let root = TempRoot::new();
        let lock = TargetLock::acquire(&root.0).unwrap();
        let report = "{\"message\":\"αβγδ complete canonical bytes\"}\n";
        assert!(write_report(&root.0, report, &lock).unwrap().is_empty());
        assert_eq!(root.index_bytes(), report.as_bytes());
        assert_eq!(read_report(&root.0).unwrap(), report);
        let paths = write_chunked_report(&root.0, report.as_bytes(), 7, &lock).unwrap();
        assert!(paths.len() > 1);
        let index = root.index_bytes();
        assert_eq!(read_report(&root.0).unwrap(), report);
        let second_paths = write_chunked_report(&root.0, report.as_bytes(), 7, &lock).unwrap();
        assert_eq!(paths, second_paths);
        assert_eq!(root.index_bytes(), index);
        // Writing a small report again restores the byte-identical legacy form.
        write_report(&root.0, report, &lock).unwrap();
        assert_eq!(root.index_bytes(), report.as_bytes());
    }

    #[test]
    fn premise_storage_rejects_chunk_corruption_missing_chunks_and_bad_total_hash() {
        let root = TempRoot::new();
        let lock = TargetLock::acquire(&root.0).unwrap();
        let report = b"the complete report is never replaced by a subset";
        let paths = write_chunked_report(&root.0, report, 8, &lock).unwrap();
        let path = root.0.join(paths[0].as_str());
        let original = fs::read(&path).unwrap();
        fs::write(&path, b"tampered").unwrap();
        assert_eq!(
            read_report(&root.0).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        fs::remove_file(&path).unwrap();
        assert_eq!(
            read_report(&root.0).unwrap_err().kind(),
            io::ErrorKind::NotFound
        );
        fs::write(path, original).unwrap();
        let index_json = String::from_utf8(root.index_bytes()).unwrap();
        let mut index = Index::parse(&index_json).unwrap().unwrap();
        index.report_hash = package_file_hash(b"wrong whole-report identity");
        fs::write(
            root.0.join(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
            index.canonical_json(),
        )
        .unwrap();
        assert_eq!(
            read_report(&root.0).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn premise_storage_failed_write_preserves_previous_index_and_rejects_layout_overflow() {
        let root = TempRoot::new();
        let lock = TargetLock::acquire(&root.0).unwrap();
        write_report(&root.0, "previous complete report", &lock).unwrap();
        let previous = root.index_bytes();
        let report = b"new complete bytes";
        let conflict = root
            .0
            .join(chunk_path(&package_file_hash(&report[..4])).as_str());
        fs::create_dir_all(conflict.parent().unwrap()).unwrap();
        fs::write(conflict, b"wrong content at immutable address").unwrap();
        assert!(write_chunked_report(&root.0, report, 4, &lock).is_err());
        assert_eq!(root.index_bytes(), previous);
        assert!(write_chunked_report(&root.0, &[b'x'; MAX_CHUNKS + 1], 1, &lock).is_err());
        assert_eq!(root.index_bytes(), previous);
    }

    #[test]
    fn premise_storage_old_index_still_resolves_after_a_new_report_is_published() {
        let root = TempRoot::new();
        let lock = TargetLock::acquire(&root.0).unwrap();
        let old = b"previous complete report";
        write_chunked_report(&root.0, old, 4, &lock).unwrap();
        let old_index = root.index_bytes();
        let new = b"a different complete report";
        write_chunked_report(&root.0, new, 4, &lock).unwrap();
        assert_eq!(read_report(&root.0).unwrap().as_bytes(), new);
        // Model a reader retaining the old root snapshot across publication.
        fs::write(root.0.join(PACKAGE_THEOREM_PREMISE_REPORT_PATH), old_index).unwrap();
        assert_eq!(read_report(&root.0).unwrap().as_bytes(), old);
    }

    #[test]
    fn premise_storage_index_enforces_canonical_fields_hashes_counts_and_sizes() {
        let good = Index {
            report_hash: package_file_hash(b"data"),
            report_bytes: 4,
            chunks: vec![Chunk {
                hash: package_file_hash(b"data"),
                bytes: 4,
            }],
        }
        .canonical_json();
        assert!(Index::parse(&good).unwrap().is_some());
        for invalid in [
            good.replace("\"logical_report_bytes\": 4", "\"logical_report_bytes\": 0"),
            good.replace("\"logical_report_bytes\": 4", "\"logical_report_bytes\": 5"),
            good.replace(
                "\"logical_report_bytes\": 4",
                &format!("\"logical_report_bytes\": {}", MAX_REPORT_BYTES + 1),
            ),
            good.replace("\"bytes\": 4", &format!("\"bytes\": {}", CHUNK_BYTES + 1)),
            good.replace("\"bytes\": 4", "\"bytes\": 4, \"bytes\": 4"),
            good.replace("\"bytes\": 4", "\"bytes\": 4, \"path\": \"../../outside\""),
            good.replace("sha256:", "SHA256:"),
            format!("{good} "),
        ] {
            assert!(Index::parse(&invalid).is_err(), "{invalid}");
        }
        let over_count = Index {
            report_hash: package_file_hash(b"data"),
            report_bytes: MAX_CHUNKS + 1,
            chunks: (0..=MAX_CHUNKS)
                .map(|_| Chunk {
                    hash: package_file_hash(b"x"),
                    bytes: 1,
                })
                .collect(),
        }
        .canonical_json();
        assert!(Index::parse(&over_count).is_err());
        let over_index = format!("{good}{}", " ".repeat(MAX_INDEX_BYTES));
        assert!(Index::parse(&over_index).is_err());
        let boundary = Index {
            report_hash: package_file_hash(b"bounded transport"),
            report_bytes: MAX_REPORT_BYTES,
            chunks: (0..MAX_CHUNKS)
                .map(|_| Chunk {
                    hash: package_file_hash(b"bounded transport"),
                    bytes: CHUNK_BYTES,
                })
                .collect(),
        }
        .canonical_json();
        assert!(Index::parse(&boundary).unwrap().is_some());
    }

    #[test]
    fn premise_storage_chunked_report_reuses_cli_and_all_six_generated_gates() {
        use crate::args::{
            PackageCheckGeneratedOptions, PackagePublishPlanOptions, PackageTimingMode,
        };
        use crate::diagnostic::CommandExitCode;
        use crate::package_api::v1::{common_options, theorem_premise_report};
        use crate::package_artifacts::run_package_check_generated;
        use crate::package_publish::run_package_publish_plan;
        use crate::package_theorem_premise_report::run_package_theorem_premise_report;

        let root = TempRoot::new();
        let fixture =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/package/proofs");
        copy_fixture(&fixture, &root.0);
        let input_hashes = fixture_hashes(&root.0);
        let report = read_report(&root.0).unwrap();
        {
            let lock = TargetLock::acquire(&root.0).unwrap();
            let paths =
                write_chunked_report(&root.0, report.as_bytes(), report.len().div_ceil(8), &lock)
                    .unwrap();
            assert!(paths.len() > 1);
        }
        assert_eq!(read_report(&root.0).unwrap(), report);
        let checked = run_package_theorem_premise_report(theorem_premise_report(
            common_options(&root.0, true),
            true,
        ));
        assert_eq!(
            checked.exit_code(),
            CommandExitCode::Success,
            "{checked:#?}"
        );
        let published = run_package_publish_plan(PackagePublishPlanOptions {
            common: common_options(&root.0, true),
            check: true,
            timings: PackageTimingMode::Off,
        });
        assert_eq!(
            published.exit_code(),
            CommandExitCode::Success,
            "{published:#?}"
        );
        let generated = run_package_check_generated(PackageCheckGeneratedOptions {
            common: common_options(&root.0, true),
            timings: PackageTimingMode::Off,
        });
        assert_eq!(
            generated.exit_code(),
            CommandExitCode::Success,
            "{generated:#?}"
        );
        assert_eq!(input_hashes, fixture_hashes(&root.0));
        let lock_path = root.0.join("generated/package-lock.json");
        let lock_bytes = fs::read(&lock_path).unwrap();
        let mut changed_lock = lock_bytes.clone();
        changed_lock.push(b'\n');
        fs::write(&lock_path, changed_lock).unwrap();
        let stale = run_package_theorem_premise_report(theorem_premise_report(
            common_options(&root.0, true),
            true,
        ));
        assert_eq!(stale.exit_code(), CommandExitCode::PackageFailure);
        assert!(stale
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason_code == "theorem_premise_report_stale"));
        fs::write(lock_path, lock_bytes).unwrap();
        let mut index = Index::parse(&String::from_utf8(root.index_bytes()).unwrap())
            .unwrap()
            .unwrap();
        index.chunks.swap(0, 1);
        fs::write(
            root.0.join(PACKAGE_THEOREM_PREMISE_REPORT_PATH),
            index.canonical_json(),
        )
        .unwrap();
        let corrupted = run_package_theorem_premise_report(theorem_premise_report(
            common_options(&root.0, true),
            true,
        ));
        assert_eq!(corrupted.exit_code(), CommandExitCode::PackageFailure);
        assert!(corrupted
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason_code == "generated_artifact_read_failed"));
    }

    fn copy_fixture(from: &Path, to: &Path) {
        for entry in fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let target = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                fs::create_dir(&target).unwrap();
                copy_fixture(&entry.path(), &target);
            } else {
                fs::copy(entry.path(), target).unwrap();
            }
        }
    }

    fn fixture_hashes(root: &Path) -> std::collections::BTreeMap<PathBuf, PackageHash> {
        fn visit(
            root: &Path,
            path: &Path,
            hashes: &mut std::collections::BTreeMap<PathBuf, PackageHash>,
        ) {
            for entry in fs::read_dir(path).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                let relative = path.strip_prefix(root).unwrap();
                if relative == Path::new(PACKAGE_THEOREM_PREMISE_REPORT_PATH)
                    || relative.starts_with(CHUNK_DIRECTORY)
                {
                    continue;
                }
                if entry.file_type().unwrap().is_dir() {
                    visit(root, &path, hashes);
                } else {
                    hashes.insert(
                        relative.to_owned(),
                        package_file_hash(&fs::read(&path).unwrap()),
                    );
                }
            }
        }
        let mut hashes = std::collections::BTreeMap::new();
        visit(root, root, &mut hashes);
        hashes
    }

    #[test]
    #[cfg(unix)]
    fn premise_storage_rejects_symlinked_chunk_and_parent() {
        use std::os::unix::fs::symlink;
        let root = TempRoot::new();
        let lock = TargetLock::acquire(&root.0).unwrap();
        let report = b"immutable chunks";
        let paths = write_chunked_report(&root.0, report, 8, &lock).unwrap();
        let target = root.0.join(paths[0].as_str());
        let outside = root.0.join("outside");
        fs::write(&outside, &report[..8]).unwrap();
        fs::remove_file(&target).unwrap();
        symlink(&outside, &target).unwrap();
        assert!(read_report(&root.0).is_err());
        assert!(write_chunked_report(&root.0, report, 8, &lock).is_err());
        let chunks = root.0.join(CHUNK_DIRECTORY);
        let moved = root.0.join("moved-chunks");
        fs::rename(&chunks, &moved).unwrap();
        symlink(&moved, &chunks).unwrap();
        assert!(read_report(&root.0).is_err());
        assert!(write_chunked_report(&root.0, report, 8, &lock).is_err());
        assert_eq!(fs::read(outside).unwrap(), &report[..8]);
    }
}
