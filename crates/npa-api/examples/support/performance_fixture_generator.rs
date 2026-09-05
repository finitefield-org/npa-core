// This one source file is included by three examples. Each example deliberately
// uses only its generator/catalog subset, so unused items in one binary are not
// dead implementation paths in the shared support module.
#![allow(dead_code)]

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use crate::closed_private_tree::ClosedPrivateDirectory;

use npa_api::{JsonDocument, JsonValue};
use npa_cert::{
    build_module_cert_from_import_refs, encode_module_cert, verify_module_cert_with_import_refs,
    AxiomPolicy, CoreModule, ModuleCert, Name, VerifiedModule,
};
use npa_kernel::{Decl, Expr, Level, Reducibility};
use npa_package::{
    build_package_lock_from_artifacts, package_file_hash, parse_and_validate_manifest_str,
    PackageLockArtifact, PackagePath,
};
use sha2::{Digest, Sha256};

pub const GENERATOR_SCHEMA: &str = "npa.performance.fixture-generator.v1";
const MANIFEST_PATH: &str = "npa-package.toml";
const LOCK_PATH: &str = "generated/package-lock.json";
const EMPTY_SHA256: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
const MAX_GENERATED_FILE_BYTES: u64 = 68 * 1024 * 1024;

const NOTES: &str = "Blocking deterministic counters; elapsed and RSS advisory.";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureTuple {
    pub module_name: String,
    pub imports: Vec<String>,
    pub target_certificate_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureProfileDescriptor {
    pub name: &'static str,
    pub tuples: Vec<FixtureTuple>,
}

#[derive(Clone, Debug)]
pub struct GeneratedFixtureModule {
    pub module_name: String,
    pub imports: Vec<String>,
    pub certificate_path: String,
    pub certificate_bytes: Vec<u8>,
    pub certificate: ModuleCert,
    pub verified: VerifiedModule,
}

#[derive(Clone, Debug)]
pub struct GeneratedFixtureProfile {
    pub profile: &'static str,
    pub root: PathBuf,
    pub root_relative: PathBuf,
    pub descriptor_sha256: String,
    pub logical_identity_sha256: String,
    pub artifact_tree_sha256: String,
    pub module_count: u64,
    pub import_edge_count: u64,
    pub declaration_count: u64,
    pub name_table_entry_count: u64,
    pub level_table_node_count: u64,
    pub term_table_node_count: u64,
    pub tree_file_count: u64,
    pub certificate_bytes: u64,
    pub modules: Vec<GeneratedFixtureModule>,
    tree_files: BTreeSet<PathBuf>,
    tree_directories: BTreeSet<PathBuf>,
}

impl GeneratedFixtureProfile {
    pub fn oracle_tsv_row(&self) -> String {
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            GENERATOR_SCHEMA,
            self.profile,
            self.descriptor_sha256,
            self.logical_identity_sha256,
            self.artifact_tree_sha256,
            self.module_count,
            self.import_edge_count,
            self.declaration_count,
            self.name_table_entry_count,
            self.level_table_node_count,
            self.term_table_node_count,
            self.tree_file_count,
            self.certificate_bytes,
        )
    }
}

pub const ORACLE_TSV_HEADER: &str = "generator_schema\tprofile\tdescriptor_sha256\tlogical_identity_sha256\tartifact_tree_sha256\tmodule_count\timport_edge_count\tdeclaration_count\tname_table_entry_count\tlevel_table_node_count\tterm_table_node_count\ttree_file_count\tcertificate_bytes";

#[derive(Clone, Copy)]
struct SnapshotProfile {
    name: &'static str,
    code: &'static str,
    package_root: &'static str,
    bytes: u64,
}

#[derive(Clone, Copy)]
struct SnapshotCase {
    code: &'static str,
    lane: &'static str,
    audit: &'static str,
    disk: &'static str,
    process: &'static str,
    decode: &'static str,
}

const PROFILES: [SnapshotProfile; 4] = [
    SnapshotProfile {
        name: "representative-1000-certificates",
        code: "rep",
        package_root: "generated/representative-1000-certificates",
        bytes: 49_283_072,
    },
    SnapshotProfile {
        name: "synthetic-1kib",
        code: "1k",
        package_root: "generated/synthetic-1kib",
        bytes: 1_024,
    },
    SnapshotProfile {
        name: "synthetic-1mib",
        code: "1m",
        package_root: "generated/synthetic-1mib",
        bytes: 1_048_576,
    },
    SnapshotProfile {
        name: "synthetic-near-limit",
        code: "near",
        package_root: "generated/synthetic-near-limit",
        bytes: 67_108_000,
    },
];

const CASES: [SnapshotCase; 11] = [
    SnapshotCase {
        code: "api-pm0-dc0",
        lane: "api",
        audit: "off",
        disk: "off",
        process: "disabled",
        decode: "disabled",
    },
    SnapshotCase {
        code: "api-pm0-dcp",
        lane: "api",
        audit: "off",
        disk: "off",
        process: "disabled",
        decode: "process-local",
    },
    SnapshotCase {
        code: "api-pm0-dcpp",
        lane: "api",
        audit: "off",
        disk: "off",
        process: "disabled",
        decode: "process-local-and-persistent",
    },
    SnapshotCase {
        code: "api-pmp-dc0",
        lane: "api",
        audit: "off",
        disk: "off",
        process: "process-local",
        decode: "disabled",
    },
    SnapshotCase {
        code: "api-pmp-dcp",
        lane: "api",
        audit: "off",
        disk: "off",
        process: "process-local",
        decode: "process-local",
    },
    SnapshotCase {
        code: "api-pmp-dcpp",
        lane: "api",
        audit: "off",
        disk: "off",
        process: "process-local",
        decode: "process-local-and-persistent",
    },
    SnapshotCase {
        code: "cli-off",
        lane: "cli-local",
        audit: "off",
        disk: "off",
        process: "disabled",
        decode: "disabled",
    },
    SnapshotCase {
        code: "cli-audit-read",
        lane: "cli-local",
        audit: "read-through",
        disk: "off",
        process: "disabled",
        decode: "disabled",
    },
    SnapshotCase {
        code: "cli-audit-hit",
        lane: "cli-local",
        audit: "local-hit",
        disk: "off",
        process: "disabled",
        decode: "disabled",
    },
    SnapshotCase {
        code: "cli-disk-read",
        lane: "cli-local",
        audit: "off",
        disk: "read-through",
        process: "disabled",
        decode: "disabled",
    },
    SnapshotCase {
        code: "cli-disk-hit",
        lane: "cli-local",
        audit: "off",
        disk: "disk",
        process: "disabled",
        decode: "disabled",
    },
];

pub fn successor_manifest(v01: &str) -> Result<String, String> {
    let document =
        JsonDocument::parse(v01).map_err(|error| format!("v0.1 JSON at {}", error.offset))?;
    let scenarios = field(document.root(), "scenarios")?
        .array_elements()
        .ok_or("v0.1 scenarios must be an array")?;
    let mut rows = scenarios
        .iter()
        .map(|row| row.raw_slice().to_owned())
        .collect::<Vec<_>>();
    rows.extend(snapshot_rows());
    rows.extend(shared_payload_rows());
    Ok(format!(
        "{{\n  \"schema\": \"npa.performance.fixtures.v0.2\",\n  \"scenarios\": [\n    {}\n  ]\n}}\n",
        rows.join(",\n    ")
    ))
}

pub fn snapshot_rows() -> Vec<String> {
    let mut rows = Vec::with_capacity(40);
    for profile in PROFILES {
        for mode in ["raw", "snapshot"] {
            rows.push(snapshot_row(profile, CASES[0], "fast", mode, 1));
        }
    }
    for case in &CASES[1..6] {
        for mode in ["raw", "snapshot"] {
            rows.push(snapshot_row(PROFILES[0], *case, "fast", mode, 1));
        }
    }
    for verifier in ["fast", "reference"] {
        for case in &CASES[6..] {
            for mode in ["raw", "snapshot"] {
                rows.push(snapshot_row(PROFILES[0], *case, verifier, mode, 1));
            }
        }
    }
    for mode in ["raw", "snapshot"] {
        rows.push(snapshot_row(PROFILES[0], CASES[0], "fast", mode, 8));
    }
    assert_eq!(rows.len(), 40);
    rows
}

fn snapshot_row(
    profile: SnapshotProfile,
    case: SnapshotCase,
    verifier: &str,
    mode: &str,
    jobs: u64,
) -> String {
    let id = format!(
        "package-artifact-snapshot-{}-{}-{verifier}-{mode}-j{jobs}",
        profile.code, case.code
    );
    let group = format!(
        "package-artifact-snapshot-{}-{}-{verifier}-j{jobs}",
        profile.code, case.code
    );
    format!(
        "{{\"id\":\"{id}\",\"kind\":\"package-artifact-snapshot\",\"measurement_mode\":\"detailed\",\"warmup\":1,\"samples\":5,\"notes\":\"{NOTES}\",\"interleave_group\":\"{group}\",\"package_root\":\"{}\",\"execution_lane\":\"{}\",\"fixture_profile\":\"{}\",\"artifact_mode\":\"{mode}\",\"artifact_bytes\":{},\"verifier\":\"{verifier}\",\"audit_cache_policy\":\"{}\",\"disk_memo_policy\":\"{}\",\"process_memo_policy\":\"{}\",\"decode_cache_policy\":\"{}\",\"jobs\":{jobs}}}",
        profile.package_root, case.lane, profile.name, profile.bytes, case.audit, case.disk, case.process, case.decode
    )
}

pub fn shared_payload_rows() -> Vec<String> {
    let mut rows = Vec::with_capacity(47);
    for (profile, code, bytes) in [
        ("payload-1mib", "1m", 1_048_576u64),
        ("payload-16mib", "16m", 16_777_216),
        ("payload-near-limit", "near", 67_108_000),
    ] {
        for clones in [1u64, 8, 32, 256] {
            for (implementation, implementation_code) in
                [("legacy-model", "legacy"), ("shared-handle", "shared")]
            {
                rows.push(common_payload_row(
                    &format!("shared-payload-clone-{code}-c{clones}-{implementation_code}"),
                    "shared-payload-clone",
                    &format!("shared-payload-clone-{code}-c{clones}"),
                    &format!("\"implementation\":\"{implementation}\",\"fixture_profile\":\"{profile}\",\"payload_bytes\":{bytes},\"clone_count\":{clones}"),
                ));
            }
        }
    }
    for (id, phase, policy) in [
        ("shared-payload-cache-1m-cold-disabled", "cold", "disabled"),
        (
            "shared-payload-cache-1m-miss-process-local",
            "miss-insert",
            "process-local",
        ),
        (
            "shared-payload-cache-1m-hit-process-local",
            "hit",
            "process-local",
        ),
        (
            "shared-payload-cache-1m-miss-persistent",
            "miss-insert",
            "process-local-and-persistent",
        ),
        (
            "shared-payload-cache-1m-hit-persistent",
            "hit",
            "process-local-and-persistent",
        ),
    ] {
        rows.push(common_payload_row(id, "shared-payload-cache", "shared-payload-cache-1m", &format!("\"fixture_profile\":\"payload-1mib\",\"payload_bytes\":1048576,\"phase\":\"{phase}\",\"decode_cache_policy\":\"{policy}\"")));
    }
    for phase in ["miss", "hit"] {
        rows.push(common_payload_row(&format!("shared-payload-memo-multi-{phase}"), "shared-payload-memo", "shared-payload-memo-multi", &format!("\"fixture_profile\":\"payload-heavy-multi-module\",\"phase\":\"{phase}\",\"decode_cache_policy\":\"disabled\",\"process_memo_policy\":\"process-local\",\"jobs\":1")));
    }
    for entries in [1u64, 64, 1024] {
        for phase in ["snapshot", "first-cow"] {
            for (implementation, code) in [("legacy-model", "legacy"), ("shared-handle", "shared")]
            {
                rows.push(common_payload_row(&format!("shared-payload-session-s{entries}-{phase}-{code}"), "shared-payload-session", &format!("shared-payload-session-s{entries}-{phase}"), &format!("\"implementation\":\"{implementation}\",\"fixture_profile\":\"session-index\",\"session_entries\":{entries},\"phase\":\"{phase}\"")));
            }
        }
    }
    for jobs in [1u64, 8] {
        rows.push(common_payload_row(&format!("shared-payload-shard-multi-j{jobs}"), "shared-payload-shard", "shared-payload-shard-multi", &format!("\"fixture_profile\":\"payload-heavy-multi-module\",\"decode_cache_policy\":\"disabled\",\"process_memo_policy\":\"disabled\",\"jobs\":{jobs}")));
    }
    for (implementation, code) in [("legacy-model", "legacy"), ("shared-handle", "shared")] {
        rows.push(common_payload_row(&format!("shared-payload-small-1k-c256-{code}"), "shared-payload-small", "shared-payload-small-1k-c256", &format!("\"implementation\":\"{implementation}\",\"fixture_profile\":\"small-certificate\",\"payload_bytes\":1024,\"clone_count\":256")));
    }
    assert_eq!(rows.len(), 47);
    rows
}

fn common_payload_row(id: &str, kind: &str, group: &str, additional: &str) -> String {
    format!("{{\"id\":\"{id}\",\"kind\":\"{kind}\",\"measurement_mode\":\"detailed\",\"warmup\":1,\"samples\":7,\"notes\":\"{NOTES}\",\"interleave_group\":\"{group}\",{additional}}}")
}

pub fn fixture_profile_descriptor(profile: &str) -> Result<FixtureProfileDescriptor, String> {
    let descriptor = match profile {
        "representative-1000-certificates" => {
            let mut tuples = Vec::with_capacity(1_000);
            for layer in 0..40 {
                for slot in 0..25 {
                    let module_name =
                        format!("Perf.Snapshot.Representative.L{layer:02}.M{slot:02}");
                    let imports = if layer == 0 {
                        Vec::new()
                    } else {
                        vec![format!(
                            "Perf.Snapshot.Representative.L{:02}.M{slot:02}",
                            layer - 1
                        )]
                    };
                    tuples.push(FixtureTuple {
                        module_name,
                        imports,
                        target_certificate_bytes: if layer == 39 && slot == 24 {
                            49_355
                        } else {
                            49_283
                        },
                    });
                }
            }
            FixtureProfileDescriptor {
                name: "representative-1000-certificates",
                tuples,
            }
        }
        "synthetic-1kib" => {
            singleton_descriptor("synthetic-1kib", "Perf.Snapshot.Synthetic1Kib", 1_024)
        }
        "synthetic-1mib" => {
            singleton_descriptor("synthetic-1mib", "Perf.Snapshot.Synthetic1Mib", 1_048_576)
        }
        "synthetic-near-limit" => singleton_descriptor(
            "synthetic-near-limit",
            "Perf.Snapshot.SyntheticNearLimit",
            67_108_000,
        ),
        "payload-1mib" => {
            singleton_descriptor("payload-1mib", "Perf.Shared.Payload1Mib", 1_048_576)
        }
        "payload-16mib" => {
            singleton_descriptor("payload-16mib", "Perf.Shared.Payload16Mib", 16_777_216)
        }
        "payload-near-limit" => singleton_descriptor(
            "payload-near-limit",
            "Perf.Shared.PayloadNearLimit",
            67_108_000,
        ),
        "payload-heavy-multi-module" => {
            let mut tuples = Vec::with_capacity(64);
            for layer in 0..8 {
                for slot in 0..8 {
                    let mut imports = if layer == 0 {
                        Vec::new()
                    } else {
                        vec![
                            format!("Perf.Shared.Multi.L{:02}.M{slot:02}", layer - 1),
                            format!("Perf.Shared.Multi.L{:02}.M{:02}", layer - 1, (slot + 7) % 8),
                        ]
                    };
                    imports.sort_unstable();
                    imports.dedup();
                    tuples.push(FixtureTuple {
                        module_name: format!("Perf.Shared.Multi.L{layer:02}.M{slot:02}"),
                        imports,
                        target_certificate_bytes: 1_048_576,
                    });
                }
            }
            FixtureProfileDescriptor {
                name: "payload-heavy-multi-module",
                tuples,
            }
        }
        "session-index" => FixtureProfileDescriptor {
            name: "session-index",
            tuples: (0..1_024)
                .map(|index| FixtureTuple {
                    module_name: format!("Perf.Shared.Session.M{index:04}"),
                    imports: Vec::new(),
                    target_certificate_bytes: 1_024,
                })
                .collect(),
        },
        "small-certificate" => {
            singleton_descriptor("small-certificate", "Perf.Shared.SmallCertificate", 1_024)
        }
        _ => return Err(format!("unsupported generator-v1 profile '{profile}'")),
    };
    Ok(descriptor)
}

fn singleton_descriptor(
    name: &'static str,
    module_name: &str,
    target_certificate_bytes: u64,
) -> FixtureProfileDescriptor {
    FixtureProfileDescriptor {
        name,
        tuples: vec![FixtureTuple {
            module_name: module_name.to_owned(),
            imports: Vec::new(),
            target_certificate_bytes,
        }],
    }
}

pub fn materialize_fixture_profile(
    profile: &'static str,
    owner: &ClosedPrivateDirectory,
    root_relative: &Path,
) -> Result<GeneratedFixtureProfile, String> {
    let descriptor = fixture_profile_descriptor(profile)?;
    owner.create_directories(root_relative)?;
    let planned = planned_fixture_catalog(root_relative, &descriptor);
    let result = materialize_fixture_profile_inner(profile, owner, root_relative, &descriptor);
    if result.is_err() {
        let _ = cleanup_allowed_fixture(owner, root_relative, &planned.0, &planned.1);
    }
    result
}

fn materialize_fixture_profile_inner(
    profile: &'static str,
    owner: &ClosedPrivateDirectory,
    root_relative: &Path,
    descriptor: &FixtureProfileDescriptor,
) -> Result<GeneratedFixtureProfile, String> {
    let descriptor_digest = descriptor_digest(descriptor);
    let mut modules = Vec::with_capacity(descriptor.tuples.len());
    let mut verified_by_name = BTreeMap::<String, VerifiedModule>::new();
    for tuple in &descriptor.tuples {
        let imports = tuple
            .imports
            .iter()
            .map(|name| {
                verified_by_name.get(name).ok_or_else(|| {
                    format!("{} imports unavailable module {name}", tuple.module_name)
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (certificate, certificate_bytes) = exact_sized_certificate(tuple, &imports)?;
        let verified = verify_module_cert_with_import_refs(
            &certificate_bytes,
            &imports,
            &AxiomPolicy::normal(),
        )
        .map_err(debug_error)?;
        let certificate_path =
            format!("{}/certificate.npcert", tuple.module_name.replace('.', "/"));
        let relative = root_relative.join(&certificate_path);
        owner.create_directories(
            relative
                .parent()
                .ok_or_else(|| "certificate path has no parent".to_owned())?,
        )?;
        owner.create_new_file(&relative, &certificate_bytes)?;
        verified_by_name.insert(tuple.module_name.clone(), verified.clone());
        modules.push(GeneratedFixtureModule {
            module_name: tuple.module_name.clone(),
            imports: tuple.imports.clone(),
            certificate_path,
            certificate_bytes,
            certificate,
            verified,
        });
    }

    let manifest = package_manifest(&modules);
    owner.create_new_file(&root_relative.join(MANIFEST_PATH), manifest.as_bytes())?;
    let validated = parse_and_validate_manifest_str(&manifest).map_err(debug_error)?;
    let lock = build_package_lock_from_artifacts(
        &validated,
        PackagePath::new(MANIFEST_PATH),
        manifest.as_bytes(),
        modules.iter().map(|module| PackageLockArtifact {
            path: PackagePath::new(module.certificate_path.clone()),
            bytes: &module.certificate_bytes,
        }),
    )
    .map_err(debug_error)?;
    let lock_path = root_relative.join(LOCK_PATH);
    owner.create_directories(
        lock_path
            .parent()
            .ok_or_else(|| "lock path has no parent".to_owned())?,
    )?;
    let canonical_lock = lock.canonical_json().map_err(debug_error)?;
    owner.create_new_file(&lock_path, canonical_lock.as_bytes())?;

    let logical_identity_sha256 = hex(&logical_identity_digest(&descriptor_digest, &modules));
    let (tree_files, tree_directories) = owner.catalog_subtree_paths(root_relative)?;
    let (artifact_tree_sha256, tree_file_count) =
        artifact_tree_digest(owner, root_relative, &tree_files, &tree_directories)?;
    let generated = GeneratedFixtureProfile {
        profile,
        root: owner.path().join(root_relative),
        root_relative: root_relative.to_path_buf(),
        descriptor_sha256: hex(&descriptor_digest),
        logical_identity_sha256,
        artifact_tree_sha256,
        module_count: usize_to_u64(modules.len())?,
        import_edge_count: sum_usizes(modules.iter().map(|module| module.imports.len()))?,
        declaration_count: sum_usizes(
            modules
                .iter()
                .map(|module| module.certificate.declarations().len()),
        )?,
        name_table_entry_count: sum_usizes(
            modules
                .iter()
                .map(|module| module.certificate.name_table().len()),
        )?,
        level_table_node_count: sum_usizes(
            modules
                .iter()
                .map(|module| module.certificate.level_table().len()),
        )?,
        term_table_node_count: sum_usizes(
            modules
                .iter()
                .map(|module| module.certificate.term_table().len()),
        )?,
        tree_file_count,
        certificate_bytes: modules.iter().try_fold(0_u64, |total, module| {
            total
                .checked_add(usize_to_u64(module.certificate_bytes.len())?)
                .ok_or_else(|| "certificate byte total overflow".to_owned())
        })?,
        modules,
        tree_files,
        tree_directories,
    };
    validate_generated_shape(descriptor, &generated)?;
    Ok(generated)
}

fn planned_fixture_catalog(
    root: &Path,
    descriptor: &FixtureProfileDescriptor,
) -> (BTreeSet<PathBuf>, BTreeSet<PathBuf>) {
    let mut files = BTreeSet::from([root.join(MANIFEST_PATH), root.join(LOCK_PATH)]);
    let mut directories = BTreeSet::from([root.to_path_buf()]);
    for tuple in &descriptor.tuples {
        let file = root.join(format!(
            "{}/certificate.npcert",
            tuple.module_name.replace('.', "/")
        ));
        files.insert(file.clone());
        let mut parent = file.parent();
        while let Some(path) = parent {
            if !path.starts_with(root) {
                break;
            }
            directories.insert(path.to_path_buf());
            if path == root {
                break;
            }
            parent = path.parent();
        }
    }
    directories.insert(root.join("generated"));
    (files, directories)
}

fn cleanup_allowed_fixture(
    owner: &ClosedPrivateDirectory,
    root: &Path,
    allowed_files: &BTreeSet<PathBuf>,
    allowed_directories: &BTreeSet<PathBuf>,
) -> Result<(), String> {
    let (files, directories) = owner.catalog_subtree_paths(root)?;
    if !files.is_subset(allowed_files) || !directories.is_subset(allowed_directories) {
        return Err("partial fixture contains an entry outside its closed catalog".to_owned());
    }
    owner.remove_exact_subtree(root, &files, &directories)
}

pub fn remove_generated_fixture(
    owner: &ClosedPrivateDirectory,
    generated: &GeneratedFixtureProfile,
) -> Result<(), String> {
    owner.remove_exact_subtree(
        &generated.root_relative,
        &generated.tree_files,
        &generated.tree_directories,
    )
}

fn exact_sized_certificate(
    tuple: &FixtureTuple,
    imports: &[&VerifiedModule],
) -> Result<(ModuleCert, Vec<u8>), String> {
    let target = usize::try_from(tuple.target_certificate_bytes).map_err(display_error)?;
    let upper = target / 4_096 + 2;
    let mut low = 0usize;
    let mut high = upper;
    while low < high {
        let middle = low + (high - low).div_ceil(2);
        let length = encoded_candidate(tuple, imports, middle, 0, 0)?.1.len();
        if length <= target {
            low = middle;
        } else {
            high = middle - 1;
        }
    }
    let (base_certificate, base_bytes) = encoded_candidate(tuple, imports, low, 0, 0)?;
    if base_bytes.len() > target {
        return Err(format!(
            "{} minimum generator-v1 certificate is {} bytes, target is {target}",
            tuple.module_name,
            base_bytes.len()
        ));
    }
    if base_bytes.len() == target {
        return Ok((base_certificate, base_bytes));
    }
    let residual = target - base_bytes.len();
    let local_prefix = tuple.module_name.len() + 1;
    let prefix_a = local_prefix + adjustment_name(low + 1, 'q', 0).len();
    let prefix_b = local_prefix + adjustment_name(low + 2, 'r', 0).len();
    for a in 0..=4_095 {
        let delta_a = encoded_string_delta(prefix_a, a);
        if delta_a > residual {
            break;
        }
        let needed_b = residual - delta_a;
        if let Some(b) = invert_string_delta(prefix_b, needed_b) {
            let (certificate, bytes) = encoded_candidate(tuple, imports, low, a, b)?;
            if bytes.len() == target {
                return Ok((certificate, bytes));
            }
        }
    }
    Err(format!(
        "{} target {target} is not reachable by generator v1",
        tuple.module_name
    ))
}

fn encoded_candidate(
    tuple: &FixtureTuple,
    imports: &[&VerifiedModule],
    full_fillers: usize,
    adjustment_a: usize,
    adjustment_b: usize,
) -> Result<(ModuleCert, Vec<u8>), String> {
    let certificate = build_module_cert_from_import_refs(
        generator_module(tuple, full_fillers, adjustment_a, adjustment_b),
        imports,
    )
    .map_err(debug_error)?;
    let bytes = encode_module_cert(&certificate).map_err(debug_error)?;
    Ok((certificate, bytes))
}

fn generator_module(
    tuple: &FixtureTuple,
    full_fillers: usize,
    adjustment_a: usize,
    adjustment_b: usize,
) -> CoreModule {
    let mut declarations = Vec::with_capacity(tuple.imports.len() + full_fillers + 3);
    for (index, import) in tuple.imports.iter().enumerate() {
        declarations.push(Decl::Def {
            name: format!("i{index:04}"),
            universe_params: vec!["u".to_owned()],
            ty: generator_id_type(),
            value: Expr::konst(format!("{import}.d000000_anchor"), vec![Level::param("u")]),
            reducibility: Reducibility::Reducible,
        });
    }
    declarations.push(Decl::Def {
        name: format!("{}.d000000_anchor", tuple.module_name),
        universe_params: vec!["u".to_owned()],
        ty: generator_id_type(),
        value: generator_id_value(),
        reducibility: Reducibility::Reducible,
    });
    for index in 1..=full_fillers {
        declarations.push(generator_filler(
            format!("d{index:06}_{}", "p".repeat(4_096)),
            &tuple.module_name,
        ));
    }
    declarations.push(generator_filler(
        adjustment_name(full_fillers + 1, 'q', adjustment_a),
        &tuple.module_name,
    ));
    declarations.push(generator_filler(
        adjustment_name(full_fillers + 2, 'r', adjustment_b),
        &tuple.module_name,
    ));
    CoreModule {
        name: Name::from_dotted(&tuple.module_name),
        declarations,
    }
}

fn generator_filler(name: String, module_name: &str) -> Decl {
    Decl::Def {
        name,
        universe_params: vec!["u".to_owned()],
        ty: generator_id_type(),
        value: Expr::konst(
            format!("{module_name}.d000000_anchor"),
            vec![Level::param("u")],
        ),
        reducibility: Reducibility::Reducible,
    }
}

fn generator_id_type() -> Expr {
    Expr::pi(
        "A",
        Expr::sort(Level::param("u")),
        Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
    )
}

fn generator_id_value() -> Expr {
    Expr::lam(
        "A",
        Expr::sort(Level::param("u")),
        Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
    )
}

fn adjustment_name(index: usize, fill: char, count: usize) -> String {
    format!("d{index:06}_{}", fill.to_string().repeat(count))
}

fn encoded_string_delta(prefix_length: usize, extra: usize) -> usize {
    extra + uvar_length(prefix_length + extra) - uvar_length(prefix_length)
}

fn invert_string_delta(prefix_length: usize, target: usize) -> Option<usize> {
    let mut low = 0usize;
    let mut high = target;
    while low < high {
        let middle = low + (high - low) / 2;
        if encoded_string_delta(prefix_length, middle) < target {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    (encoded_string_delta(prefix_length, low) == target).then_some(low)
}

fn uvar_length(mut value: usize) -> usize {
    let mut length = 1;
    while value >= 0x80 {
        value >>= 7;
        length += 1;
    }
    length
}

fn package_manifest(modules: &[GeneratedFixtureModule]) -> String {
    let mut source = String::from(
        "schema = \"npa.package.v0.1\"\npackage = \"npa-performance-fixture\"\nversion = \"0.1.0\"\ncore_spec = \"npa.core.v0.1\"\nkernel_profile = \"npa.kernel.v0.1\"\ncertificate_format = \"npa.certificate.canonical.v0.1\"\nchecker_profile = \"npa.checker.reference.v0.1\"\n\n[policy]\nallow_custom_axioms = false\nallowed_axioms = []\n\n",
    );
    for module in modules {
        let hashes = module.certificate.hashes();
        source.push_str("[[modules]]\n");
        source.push_str(&format!("module = {:?}\n", module.module_name));
        source.push_str(&format!(
            "source = {:?}\n",
            format!("{}/source.npa", module.module_name.replace('.', "/"))
        ));
        source.push_str(&format!("certificate = {:?}\n", module.certificate_path));
        source.push_str("imports = [");
        for (index, import) in module.imports.iter().enumerate() {
            if index != 0 {
                source.push_str(", ");
            }
            source.push_str(&format!("{import:?}"));
        }
        source.push_str("]\n");
        source.push_str(&format!(
            "expected_source_hash = \"sha256:{EMPTY_SHA256}\"\n"
        ));
        source.push_str(&format!(
            "expected_certificate_file_hash = \"{}\"\n",
            prefixed_hash(package_file_hash(&module.certificate_bytes).as_bytes())
        ));
        source.push_str(&format!(
            "expected_export_hash = \"{}\"\n",
            prefixed_hash(&hashes.export_hash)
        ));
        source.push_str(&format!(
            "expected_axiom_report_hash = \"{}\"\n",
            prefixed_hash(&hashes.axiom_report_hash)
        ));
        source.push_str(&format!(
            "expected_certificate_hash = \"{}\"\n",
            prefixed_hash(&hashes.certificate_hash)
        ));
        source.push_str(
            "inductives = []\ndefinitions = []\ntheorems = []\naxioms = []\ntags = []\n\n",
        );
    }
    source
}

fn descriptor_digest(descriptor: &FixtureProfileDescriptor) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"npa.performance.fixture-generator.profile.v1\0");
    frame(&mut hasher, descriptor.name.as_bytes());
    for tuple in &descriptor.tuples {
        frame(&mut hasher, tuple.module_name.as_bytes());
        hasher.update(tuple.target_certificate_bytes.to_be_bytes());
        hasher.update((tuple.imports.len() as u64).to_be_bytes());
        for import in &tuple.imports {
            frame(&mut hasher, import.as_bytes());
        }
    }
    hasher.finalize().into()
}

#[cfg(test)]
pub fn descriptor_digest_for_test(descriptor: &FixtureProfileDescriptor) -> [u8; 32] {
    descriptor_digest(descriptor)
}

fn logical_identity_digest(
    descriptor_digest: &[u8; 32],
    modules: &[GeneratedFixtureModule],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"npa.performance.fixture-generator.logical.v1\0");
    hasher.update(descriptor_digest);
    for module in modules {
        frame(&mut hasher, module.module_name.as_bytes());
        hasher.update((module.imports.len() as u64).to_be_bytes());
        for import in &module.imports {
            frame(&mut hasher, import.as_bytes());
        }
        for count in [
            module.certificate.declarations().len(),
            module.certificate.name_table().len(),
            module.certificate.level_table().len(),
            module.certificate.term_table().len(),
        ] {
            hasher.update((count as u64).to_be_bytes());
        }
        hasher.update(module.certificate.hashes().export_hash);
        hasher.update(module.certificate.hashes().axiom_report_hash);
        hasher.update(module.certificate.hashes().certificate_hash);
    }
    hasher.finalize().into()
}

fn artifact_tree_digest(
    owner: &ClosedPrivateDirectory,
    root: &Path,
    expected_files: &BTreeSet<PathBuf>,
    expected_directories: &BTreeSet<PathBuf>,
) -> Result<(String, u64), String> {
    let (actual_files, actual_directories) = owner.catalog_subtree_paths(root)?;
    if &actual_files != expected_files || &actual_directories != expected_directories {
        return Err("fixture tree differs from its closed generated catalog".to_owned());
    }
    let mut hasher = Sha256::new();
    hasher.update(b"npa.performance.fixture-generator.tree.v1\0");
    for path in &actual_files {
        let relative = path
            .strip_prefix(root)
            .map_err(display_error)?
            .to_str()
            .ok_or_else(|| "fixture path is not UTF-8".to_owned())?
            .replace('\\', "/");
        let bytes = owner.read_regular_file(path, MAX_GENERATED_FILE_BYTES)?;
        frame(&mut hasher, relative.as_bytes());
        hasher.update(usize_to_u64(bytes.len())?.to_be_bytes());
        hasher.update(Sha256::digest(&bytes));
    }
    Ok((
        hex(&hasher.finalize().into()),
        usize_to_u64(actual_files.len())?,
    ))
}

/// Recompute the immutable generated-workload tree identity after warmup or a
/// measured sample. Cache roots and run output must be siblings of `root`, so
/// any mutation reported here is a workload mutation rather than cache work.
pub fn artifact_tree_identity(
    owner: &ClosedPrivateDirectory,
    generated: &GeneratedFixtureProfile,
) -> Result<(String, u64), String> {
    artifact_tree_digest(
        owner,
        &generated.root_relative,
        &generated.tree_files,
        &generated.tree_directories,
    )
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn validate_generated_shape(
    descriptor: &FixtureProfileDescriptor,
    generated: &GeneratedFixtureProfile,
) -> Result<(), String> {
    let expected_bytes = descriptor.tuples.iter().try_fold(0_u64, |total, tuple| {
        total
            .checked_add(tuple.target_certificate_bytes)
            .ok_or_else(|| "descriptor byte total overflow".to_owned())
    })?;
    if generated.module_count != descriptor.tuples.len() as u64
        || generated.import_edge_count
            != descriptor
                .tuples
                .iter()
                .map(|tuple| tuple.imports.len() as u64)
                .sum::<u64>()
        || generated.certificate_bytes != expected_bytes
        || generated
            .modules
            .iter()
            .zip(&descriptor.tuples)
            .any(|(module, tuple)| {
                module.certificate_bytes.len() as u64 != tuple.target_certificate_bytes
            })
    {
        return Err(format!("{} generated shape mismatch", descriptor.name));
    }
    Ok(())
}

fn prefixed_hash(hash: &[u8; 32]) -> String {
    format!("sha256:{}", hex(hash))
}

fn hex(hash: &[u8; 32]) -> String {
    let mut result = String::with_capacity(64);
    for byte in hash {
        use std::fmt::Write as _;
        write!(&mut result, "{byte:02x}").expect("writing to String cannot fail");
    }
    result
}

fn usize_to_u64(value: usize) -> Result<u64, String> {
    u64::try_from(value).map_err(display_error)
}

fn sum_usizes(mut values: impl Iterator<Item = usize>) -> Result<u64, String> {
    values.try_fold(0_u64, |total, value| {
        total
            .checked_add(usize_to_u64(value)?)
            .ok_or_else(|| "fixture count overflow".to_owned())
    })
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn debug_error(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

fn field<'a>(value: &'a JsonValue<'a>, name: &str) -> Result<&'a JsonValue<'a>, String> {
    value
        .object_members()
        .ok_or("root must be object")?
        .iter()
        .find(|member| member.key() == name)
        .map(|member| member.value())
        .ok_or_else(|| format!("missing {name}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn catalog_cardinality_and_order_are_closed() {
        let snapshot = snapshot_rows();
        let payload = shared_payload_rows();
        assert_eq!(snapshot.len(), 40);
        assert_eq!(payload.len(), 47);
        assert!(snapshot
            .first()
            .unwrap()
            .contains("snapshot-rep-api-pm0-dc0-fast-raw-j1"));
        assert!(snapshot
            .last()
            .unwrap()
            .contains("snapshot-rep-api-pm0-dc0-fast-snapshot-j8"));
        assert!(payload
            .first()
            .unwrap()
            .contains("shared-payload-clone-1m-c1-legacy"));
        assert!(payload
            .last()
            .unwrap()
            .contains("shared-payload-small-1k-c256-shared"));
    }

    #[test]
    fn fixture_descriptor_shapes_are_closed() {
        let representative =
            fixture_profile_descriptor("representative-1000-certificates").unwrap();
        assert_eq!(representative.tuples.len(), 1_000);
        assert_eq!(
            representative
                .tuples
                .iter()
                .map(|tuple| tuple.imports.len())
                .sum::<usize>(),
            975
        );
        assert_eq!(
            representative
                .tuples
                .iter()
                .map(|tuple| tuple.target_certificate_bytes)
                .sum::<u64>(),
            49_283_072
        );
        let multi = fixture_profile_descriptor("payload-heavy-multi-module").unwrap();
        assert_eq!(multi.tuples.len(), 64);
        assert_eq!(
            multi
                .tuples
                .iter()
                .map(|tuple| tuple.imports.len())
                .sum::<usize>(),
            112
        );
        let session = fixture_profile_descriptor("session-index").unwrap();
        assert_eq!(session.tuples.len(), 1_024);
        assert!(session.tuples.iter().all(|tuple| tuple.imports.is_empty()));
    }

    #[test]
    fn fixture_generator_small_certificate_is_exact_and_source_free() {
        let owner = ClosedPrivateDirectory::new("npa-performance-fixture-test").unwrap();
        let generated =
            materialize_fixture_profile("small-certificate", &owner, Path::new("fixture")).unwrap();
        assert_eq!(generated.module_count, 1);
        assert_eq!(generated.import_edge_count, 0);
        assert_eq!(generated.certificate_bytes, 1_024);
        assert_eq!(generated.modules[0].certificate_bytes.len(), 1_024);
        assert!(generated.root.join(MANIFEST_PATH).is_file());
        assert!(generated.root.join(LOCK_PATH).is_file());
        assert!(!generated
            .root
            .join("Perf/Shared/SmallCertificate/source.npa")
            .exists());
        assert_eq!(generated.descriptor_sha256.len(), 64);
        assert_eq!(generated.logical_identity_sha256.len(), 64);
        assert_eq!(generated.artifact_tree_sha256.len(), 64);
        remove_generated_fixture(&owner, &generated).unwrap();
        owner.remove_empty_root().unwrap();
    }
}
