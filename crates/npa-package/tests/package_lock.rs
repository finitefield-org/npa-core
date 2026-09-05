use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use npa_cert::Name;
use npa_package::{
    build_indexed_package_lock_graph,
    build_package_lock_and_snapshot_owned_artifacts as build_owned_snapshot_api,
    build_package_lock_and_snapshot_owned_artifacts_with_payload_observation,
    build_package_lock_from_artifacts as build_package_lock_from_artifacts_api,
    build_package_lock_from_artifacts_allowing_local_hash_updates,
    build_package_lock_from_package_root,
    build_package_lock_from_package_root_allowing_local_hash_updates, build_package_lock_graph,
    format_package_hash, package_file_hash, parse_manifest_str, parse_package_hash,
    parse_package_lock_json, validate_manifest,
    validate_observed_package_lock_against_manifest_graph,
    validate_package_lock_against_manifest_graph, OwnedPackageLockArtifact,
    PackageArtifactPreparationObservation, PackageHash, PackageId, PackageLockArtifact,
    PackageLockEntry, PackageLockEntryOrigin, PackageLockError, PackageLockErrorKind,
    PackageLockErrorReason, PackageLockImport, PackageLockManifest, PackageLockManifestReference,
    PackagePath, PackageVersion, PreparedArtifactObservationMode, PreparedArtifactRetentionPolicy,
    PreparedPackageArtifactView, ValidatedPackageManifest, PACKAGE_LOCK_SCHEMA,
};

const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const ONE_HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
const TWO_HASH: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
const THREE_HASH: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";
const FOUR_HASH: &str = "sha256:4444444444444444444444444444444444444444444444444444444444444444";
const FIVE_HASH: &str = "sha256:5555555555555555555555555555555555555555555555555555555555555555";
const SIX_HASH: &str = "sha256:6666666666666666666666666666666666666666666666666666666666666666";
const EQ_EXPORT_HASH: &str =
    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const EQ_CERT_HASH: &str =
    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const EQ_AXIOM_HASH: &str =
    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
const NAT_EXPORT_HASH: &str =
    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
const NAT_CERT_HASH: &str =
    "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
const NAT_AXIOM_HASH: &str =
    "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

fn expected_canonical_json() -> String {
    format!(
        concat!(
            r#"{{"schema":"npa.package.lock.v0.1","package":"npa-proof-corpus","version":"0.1.0","#,
            r#""manifest":{{"path":"npa-package.toml","file_hash":"{zero}"}},"entries":["#,
            r#"{{"module":"Proofs.Ai.Basic","origin":"local","certificate":"Proofs/Ai/Basic/certificate.npcert","#,
            r#""certificate_file_hash":"{one}","export_hash":"{two}","axiom_report_hash":"{three}","#,
            r#""certificate_hash":"{four}","imports":["#,
            r#"{{"module":"Std.Logic.Eq","export_hash":"{eq_export}","certificate_hash":"{eq_cert}"}},"#,
            r#"{{"module":"Std.Nat.Basic","export_hash":"{nat_export}","certificate_hash":"{nat_cert}"}}"#,
            r#"]}},"#,
            r#"{{"module":"Std.Logic.Eq","origin":"external","package":"npa-std","version":"0.1.0","#,
            r#""certificate":"vendor/npa-std/Std/Logic/Eq/certificate.npcert","certificate_file_hash":"{five}","#,
            r#""export_hash":"{eq_export}","axiom_report_hash":"{eq_axiom}","certificate_hash":"{eq_cert}","imports":[]}},"#,
            r#"{{"module":"Std.Nat.Basic","origin":"external","package":"npa-std","version":"0.1.0","#,
            r#""certificate":"vendor/npa-std/Std/Nat/Basic/certificate.npcert","certificate_file_hash":"{six}","#,
            r#""export_hash":"{nat_export}","axiom_report_hash":"{nat_axiom}","certificate_hash":"{nat_cert}","imports":[]}}"#,
            r#"]}}"#
        ),
        zero = ZERO_HASH,
        one = ONE_HASH,
        two = TWO_HASH,
        three = THREE_HASH,
        four = FOUR_HASH,
        five = FIVE_HASH,
        six = SIX_HASH,
        eq_export = EQ_EXPORT_HASH,
        eq_cert = EQ_CERT_HASH,
        eq_axiom = EQ_AXIOM_HASH,
        nat_export = NAT_EXPORT_HASH,
        nat_cert = NAT_CERT_HASH,
        nat_axiom = NAT_AXIOM_HASH,
    )
}

fn hash(value: &str) -> PackageHash {
    parse_package_hash(value, "test").unwrap()
}

fn import(module: &str, export_hash: &str, certificate_hash: &str) -> PackageLockImport {
    PackageLockImport {
        module: Name::from_dotted(module),
        export_hash: hash(export_hash),
        certificate_hash: hash(certificate_hash),
    }
}

fn external_entry(
    module: &str,
    certificate: &str,
    certificate_file_hash: &str,
    export_hash: &str,
    axiom_report_hash: &str,
    certificate_hash: &str,
) -> PackageLockEntry {
    PackageLockEntry {
        module: Name::from_dotted(module),
        origin: PackageLockEntryOrigin::External,
        certificate: PackagePath::new(certificate),
        certificate_file_hash: hash(certificate_file_hash),
        export_hash: hash(export_hash),
        axiom_report_hash: hash(axiom_report_hash),
        certificate_hash: hash(certificate_hash),
        imports: vec![],
        package: Some(PackageId::new("npa-std")),
        version: Some(PackageVersion::new("0.1.0")),
    }
}

fn unsorted_lock() -> PackageLockManifest {
    PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: PackageId::new("npa-proof-corpus"),
        version: PackageVersion::new("0.1.0"),
        manifest: PackageLockManifestReference {
            path: PackagePath::new("npa-package.toml"),
            file_hash: hash(ZERO_HASH),
        },
        entries: vec![
            external_entry(
                "Std.Nat.Basic",
                "vendor/npa-std/Std/Nat/Basic/certificate.npcert",
                SIX_HASH,
                NAT_EXPORT_HASH,
                NAT_AXIOM_HASH,
                NAT_CERT_HASH,
            ),
            PackageLockEntry {
                module: Name::from_dotted("Proofs.Ai.Basic"),
                origin: PackageLockEntryOrigin::Local,
                certificate: PackagePath::new("Proofs/Ai/Basic/certificate.npcert"),
                certificate_file_hash: hash(ONE_HASH),
                export_hash: hash(TWO_HASH),
                axiom_report_hash: hash(THREE_HASH),
                certificate_hash: hash(FOUR_HASH),
                imports: vec![
                    import("Std.Nat.Basic", NAT_EXPORT_HASH, NAT_CERT_HASH),
                    import("Std.Logic.Eq", EQ_EXPORT_HASH, EQ_CERT_HASH),
                ],
                package: None,
                version: None,
            },
            external_entry(
                "Std.Logic.Eq",
                "vendor/npa-std/Std/Logic/Eq/certificate.npcert",
                FIVE_HASH,
                EQ_EXPORT_HASH,
                EQ_AXIOM_HASH,
                EQ_CERT_HASH,
            ),
        ],
    }
}

fn assert_lock_error(
    error: &PackageLockError,
    kind: PackageLockErrorKind,
    reason: PackageLockErrorReason,
    path: &str,
    field: Option<&str>,
) {
    assert_eq!(error.kind, kind);
    assert_eq!(error.reason_code, reason);
    assert_eq!(error.reason_code.as_str(), reason.as_str());
    assert_eq!(error.path, path);
    assert_eq!(error.field.as_deref(), field);
}

fn assert_lock_error_module_context(error: &PackageLockError, module: &Name) {
    let module_name = module.as_dotted();
    assert_eq!(
        error.module.as_ref().map(|module| module.as_str()),
        Some(module_name.as_str())
    );
    assert!(
        error
            .to_string()
            .contains(&decorated_error_path(&error.path, module_name.as_str())),
        "display should include module context: {error}"
    );
}

fn decorated_error_path(path: &str, module: &str) -> String {
    match path.find('.') {
        Some(split) => format!("{} ({}){}", &path[..split], module, &path[split..]),
        None => format!("{path} ({module})"),
    }
}

fn lock_entry_index(lock: &PackageLockManifest, module: &Name) -> usize {
    lock.entries
        .iter()
        .position(|entry| &entry.module == module)
        .unwrap_or_else(|| panic!("lock entry exists for {}", module.as_dotted()))
}

fn assert_lock_error_kind_reason(
    error: &PackageLockError,
    kind: PackageLockErrorKind,
    reason: PackageLockErrorReason,
) {
    assert_eq!(error.kind, kind);
    assert_eq!(error.reason_code, reason);
    assert_eq!(error.reason_code.as_str(), reason.as_str());
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("npa-package crate lives under crates/")
        .to_path_buf()
}

fn proofs_root() -> PathBuf {
    let root = repo_root();
    let direct = root.join("proofs");
    if direct.join("npa-package.toml").exists() {
        return direct;
    }
    root.join("testdata/package/proofs")
}

fn read(path: PathBuf) -> Vec<u8> {
    fs::read(&path).unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
}

fn proof_manifest_bytes() -> Vec<u8> {
    read(proofs_root().join("npa-package.toml"))
}

fn proof_manifest_source() -> String {
    String::from_utf8(proof_manifest_bytes()).expect("proof manifest is UTF-8")
}

fn filtered_proof_fixture() -> ValidatedPackageManifest {
    let mut manifest =
        parse_manifest_str(&proof_manifest_source()).expect("proof package manifest should parse");
    let lock = parse_package_lock_json(
        &String::from_utf8(read(proofs_root().join("generated/package-lock.json")))
            .expect("proof package lock is UTF-8"),
    )
    .expect("proof package lock should parse");
    let removed = unsupported_proof_fixture_modules(&manifest, &lock);
    manifest
        .modules
        .retain(|module| !removed.contains(&module.module));
    validate_manifest(manifest).expect("filtered proof package manifest should validate")
}

fn proof_manifest() -> npa_package::PackageManifest {
    filtered_proof_fixture().into_manifest()
}

fn validated_proof_manifest() -> ValidatedPackageManifest {
    filtered_proof_fixture()
}

fn unsupported_proof_fixture_modules(
    manifest: &npa_package::PackageManifest,
    lock: &PackageLockManifest,
) -> BTreeSet<Name> {
    let root = proofs_root();
    let manifest_modules = manifest
        .modules
        .iter()
        .map(|module| module.module.clone())
        .chain(
            manifest
                .imports
                .as_deref()
                .unwrap_or(&[])
                .iter()
                .map(|import| import.module.clone()),
        )
        .collect::<BTreeSet<_>>();
    let mut removed = lock
        .entries
        .iter()
        .filter_map(|entry| {
            if !manifest_modules.contains(&entry.module) {
                return Some(entry.module.clone());
            }
            let bytes = match fs::read(root.join(entry.certificate.as_str())) {
                Ok(bytes) => bytes,
                Err(_) => return Some(entry.module.clone()),
            };
            npa_cert::decode_module_cert(&bytes)
                .is_err()
                .then(|| entry.module.clone())
        })
        .collect::<BTreeSet<_>>();

    let mut reverse = BTreeMap::<Name, Vec<Name>>::new();
    for entry in &lock.entries {
        for import in &entry.imports {
            reverse
                .entry(import.module.clone())
                .or_default()
                .push(entry.module.clone());
        }
    }
    let mut stack = removed.iter().cloned().collect::<Vec<_>>();
    while let Some(module) = stack.pop() {
        for dependent in reverse.get(&module).cloned().unwrap_or_default() {
            if removed.insert(dependent.clone()) {
                stack.push(dependent);
            }
        }
    }
    removed
}

fn proof_certificate_artifacts(
    validated: &ValidatedPackageManifest,
) -> BTreeMap<PackagePath, Vec<u8>> {
    let root = proofs_root();
    let manifest = validated.manifest();
    let mut artifacts = BTreeMap::new();
    for module in &manifest.modules {
        artifacts.insert(
            module.certificate.clone(),
            read(root.join(module.certificate.as_str())),
        );
    }
    for import in manifest.imports.as_deref().unwrap_or(&[]) {
        artifacts.insert(
            import.certificate.clone(),
            read(root.join(import.certificate.as_str())),
        );
    }
    artifacts
}

fn package_lock_artifacts(
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Vec<PackageLockArtifact<'_>> {
    artifacts
        .iter()
        .map(|(path, bytes)| PackageLockArtifact {
            path: path.clone(),
            bytes: bytes.as_slice(),
        })
        .collect()
}

fn build_proof_lock_from_artifacts(
    validated: &ValidatedPackageManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Result<PackageLockManifest, PackageLockError> {
    build_package_lock_from_artifacts_api(
        validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        package_lock_artifacts(artifacts),
    )
}

fn build_proof_lock_from_artifacts_allowing_local_hash_updates(
    validated: &ValidatedPackageManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
) -> Result<PackageLockManifest, PackageLockError> {
    build_package_lock_from_artifacts_allowing_local_hash_updates(
        validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        package_lock_artifacts(artifacts),
    )
}

fn tampered_certificate_hash(bytes: &[u8]) -> Vec<u8> {
    let cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    let mut parts = cert.into_parts();
    parts.hashes.certificate_hash[0] ^= 0x01;
    let cert = npa_cert::ModuleCert::from_parts(parts);
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_export_hash(bytes: &[u8]) -> Vec<u8> {
    let cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    let mut parts = cert.into_parts();
    parts.hashes.export_hash[0] ^= 0x01;
    let cert = npa_cert::ModuleCert::from_parts(parts);
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_axiom_report_hash(bytes: &[u8]) -> Vec<u8> {
    let cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    let mut parts = cert.into_parts();
    parts.hashes.axiom_report_hash[0] ^= 0x01;
    let cert = npa_cert::ModuleCert::from_parts(parts);
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_module_name(bytes: &[u8], module: &str) -> Vec<u8> {
    let cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    let mut parts = cert.into_parts();
    parts.header.module = Name::from_dotted(module);
    let cert = npa_cert::ModuleCert::from_parts(parts);
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_certificate_imports(
    bytes: &[u8],
    edit: impl FnOnce(&mut Vec<npa_cert::ImportEntry>),
) -> Vec<u8> {
    let cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    let mut parts = cert.into_parts();
    edit(&mut parts.imports);
    let cert = npa_cert::ModuleCert::from_parts(parts);
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn certificate_import(
    module: &str,
    export_hash: PackageHash,
    certificate_hash: PackageHash,
) -> npa_cert::ImportEntry {
    npa_cert::ImportEntry {
        module: Name::from_dotted(module),
        export_hash: export_hash.into_bytes(),
        certificate_hash: Some(certificate_hash.into_bytes()),
    }
}

fn first_module_with_manifest_imports(validated: &ValidatedPackageManifest) -> usize {
    validated
        .manifest()
        .modules
        .iter()
        .position(|module| !module.imports.is_empty())
        .expect("proof corpus has a module with imports")
}

#[test]
fn package_lock_canonical_json_sorts_entries_and_imports() {
    let canonical = unsorted_lock().canonical_json().unwrap();

    assert_eq!(canonical, expected_canonical_json());
}

#[test]
fn package_lock_canonical_json_round_trips_to_the_same_bytes() {
    let parsed = parse_package_lock_json(&expected_canonical_json()).unwrap();

    assert_eq!(parsed.entries[0].module.as_dotted(), "Proofs.Ai.Basic");
    assert_eq!(
        parsed.entries[0].imports[0].module.as_dotted(),
        "Std.Logic.Eq"
    );
    assert_eq!(
        parsed.entries[0].imports[1].module.as_dotted(),
        "Std.Nat.Basic"
    );
    assert_eq!(parsed.entries[1].origin, PackageLockEntryOrigin::External);
    assert_eq!(
        parsed.entries[1].package.as_ref().unwrap().as_str(),
        "npa-std"
    );
    assert_eq!(parsed.canonical_json().unwrap(), expected_canonical_json());
}

#[test]
fn package_lock_schema_rejects_unknown_fields() {
    let source = expected_canonical_json().replacen(
        r#""entries":["#,
        r#""source":"Proofs/Ai/Basic/source.npa","entries":["#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::LockSchema,
        PackageLockErrorReason::UnknownField,
        "$",
        Some("source"),
    );
}

#[test]
fn package_lock_schema_rejects_unknown_nested_fields() {
    let source = expected_canonical_json().replacen(
        r#""module":"Std.Logic.Eq","export_hash":"#,
        r#""module":"Std.Logic.Eq","source":"Std/Logic/Eq.npa","export_hash":"#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::LockSchema,
        PackageLockErrorReason::UnknownField,
        "entries[0].imports[0]",
        Some("source"),
    );
}

#[test]
fn package_lock_schema_rejects_duplicate_json_fields() {
    let source = expected_canonical_json().replacen(
        r#""schema":"npa.package.lock.v0.1","#,
        r#""schema":"npa.package.lock.v0.1","schema":"npa.package.lock.v0.1","#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::LockSchema,
        PackageLockErrorReason::DuplicateField,
        "$",
        Some("schema"),
    );
}

#[test]
fn package_lock_schema_rejects_duplicate_modules() {
    let source = expected_canonical_json().replacen(
        r#""module":"Std.Nat.Basic","origin":"external""#,
        r#""module":"Std.Logic.Eq","origin":"external""#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Duplicate,
        PackageLockErrorReason::DuplicateLockEntry,
        "entries[2].module",
        Some("module"),
    );
}

#[test]
fn package_lock_schema_rejects_duplicate_certificate_paths() {
    let source = expected_canonical_json().replacen(
        "vendor/npa-std/Std/Nat/Basic/certificate.npcert",
        "vendor/npa-std/Std/Logic/Eq/certificate.npcert",
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Duplicate,
        PackageLockErrorReason::DuplicateCertificatePath,
        "entries[2].certificate",
        Some("certificate"),
    );
}

#[test]
fn package_lock_schema_rejects_duplicate_imports() {
    let source = expected_canonical_json().replacen(
        r#""module":"Std.Nat.Basic","export_hash":"#,
        r#""module":"Std.Logic.Eq","export_hash":"#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Duplicate,
        PackageLockErrorReason::DuplicateImport,
        "entries[0].imports[1].module",
        Some("module"),
    );
}

#[test]
fn package_lock_schema_rejects_malformed_hashes() {
    let source = expected_canonical_json().replacen(ONE_HASH, "sha256:bad", 1);

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Hash,
        PackageLockErrorReason::InvalidHashFormat,
        "entries[0].certificate_file_hash",
        None,
    );
}

#[test]
fn package_lock_schema_rejects_malformed_paths() {
    let source = expected_canonical_json().replacen(
        "Proofs/Ai/Basic/certificate.npcert",
        "../certificate.npcert",
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Path,
        PackageLockErrorReason::InvalidPath,
        "entries[0].certificate",
        None,
    );
}

#[test]
fn package_lock_schema_rejects_malformed_package_identity() {
    let source = expected_canonical_json().replacen(
        r#""package":"npa-proof-corpus""#,
        r#""package":"NPA-Proof-Corpus""#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Domain,
        PackageLockErrorReason::InvalidPackageId,
        "package",
        None,
    );
}

#[test]
fn package_lock_schema_rejects_malformed_versions() {
    let source =
        expected_canonical_json().replacen(r#""version":"0.1.0""#, r#""version":"01.0.0""#, 1);

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Domain,
        PackageLockErrorReason::InvalidVersion,
        "version",
        None,
    );
}

#[test]
fn package_lock_schema_rejects_malformed_names() {
    let source = expected_canonical_json().replacen(
        r#""module":"Proofs.Ai.Basic""#,
        r#""module":"Proofs..Bad""#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Domain,
        PackageLockErrorReason::InvalidModuleName,
        "entries[0].module",
        None,
    );
}

#[test]
fn package_lock_schema_requires_external_package_and_version() {
    let source = expected_canonical_json().replacen(
        r#""origin":"external","package":"npa-std","version":"0.1.0""#,
        r#""origin":"external","version":"0.1.0""#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::LockSchema,
        PackageLockErrorReason::ExternalFieldRequired,
        "entries[1].package",
        Some("package"),
    );
}

#[test]
fn package_lock_schema_rejects_local_package_identity_fields() {
    let source = expected_canonical_json().replacen(
        r#""module":"Proofs.Ai.Basic","origin":"local","certificate":"#,
        r#""module":"Proofs.Ai.Basic","origin":"local","package":"npa-proof-corpus","certificate":"#,
        1,
    );

    let error = parse_package_lock_json(&source).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::LockSchema,
        PackageLockErrorReason::LocalFieldForbidden,
        "entries[0].package",
        Some("package"),
    );
}

#[test]
fn package_lock_builder_builds_source_free_lock_from_certificate_bytes() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);

    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let manifest = validated.manifest();

    assert_eq!(lock.schema, PACKAGE_LOCK_SCHEMA);
    assert_eq!(lock.package, manifest.package);
    assert_eq!(lock.version, manifest.version);
    assert_eq!(lock.manifest.path.as_str(), "npa-package.toml");
    assert_eq!(
        lock.manifest.file_hash,
        package_file_hash(&proof_manifest_bytes())
    );
    assert_eq!(
        lock.entries.len(),
        manifest.modules.len() + manifest.imports.as_deref().unwrap_or(&[]).len()
    );

    let eq_entry = lock
        .entries
        .iter()
        .find(|entry| entry.module.as_dotted() == "Proofs.Ai.Eq")
        .expect("lock should contain local Eq entry");
    let eq_module = manifest
        .modules
        .iter()
        .find(|module| module.module.as_dotted() == "Proofs.Ai.Eq")
        .expect("manifest should contain local Eq module");
    assert_eq!(eq_entry.origin, PackageLockEntryOrigin::Local);
    assert_eq!(
        eq_entry.certificate_file_hash,
        eq_module.expected_certificate_file_hash
    );
    assert_eq!(eq_entry.export_hash, eq_module.expected_export_hash);
    assert_eq!(
        eq_entry.axiom_report_hash,
        eq_module.expected_axiom_report_hash
    );
    assert_eq!(
        eq_entry.certificate_hash,
        eq_module.expected_certificate_hash
    );
    assert_eq!(
        eq_entry
            .imports
            .iter()
            .map(|import| import.module.as_dotted())
            .collect::<Vec<_>>(),
        vec!["Std.Logic.Eq", "Std.Nat.Basic"]
    );

    let std_eq_entry = lock
        .entries
        .iter()
        .find(|entry| entry.module.as_dotted() == "Std.Logic.Eq")
        .expect("lock should contain vendored Std.Logic.Eq entry");
    let std_eq_import = manifest
        .imports
        .as_deref()
        .unwrap()
        .iter()
        .find(|import| import.module.as_dotted() == "Std.Logic.Eq")
        .expect("manifest should contain Std.Logic.Eq import");
    assert_eq!(std_eq_entry.origin, PackageLockEntryOrigin::External);
    assert_eq!(
        std_eq_entry.package.as_ref().unwrap().as_str(),
        std_eq_import.package.as_str()
    );
    assert_eq!(
        std_eq_entry.version.as_ref().unwrap().as_str(),
        std_eq_import.version.as_str()
    );
    assert_eq!(std_eq_entry.imports, Vec::new());
    assert_eq!(std_eq_entry.export_hash, std_eq_import.export_hash);
    assert_eq!(
        std_eq_entry.certificate_hash,
        std_eq_import.certificate_hash
    );

    let canonical = lock.canonical_json().unwrap();
    assert_eq!(parse_package_lock_json(&canonical).unwrap(), lock);
}

#[test]
fn indexed_lock_graph_closure_and_layers_match_dependency_order() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let indexed = build_indexed_package_lock_graph(&lock).unwrap();
    assert_eq!(indexed.lock(), &lock);
    assert_eq!(indexed.entries(), lock.entries.as_slice());
    assert_eq!(
        indexed.graph().topological_order,
        lock_topological_modules(&indexed)
    );

    let root = indexed
        .graph()
        .topological_order
        .last()
        .expect("nonempty fixture")
        .clone();
    let membership = indexed
        .index()
        .dependency_closure(&BTreeSet::from([root.clone()]))
        .unwrap();
    let root_entry = indexed.index().entry_by_module(&root).unwrap();
    assert!(membership[root_entry]);
    let layers = indexed.index().topological_layers(&membership);
    assert!(!layers.is_empty());
    let mut seen = BTreeSet::new();
    for layer in layers {
        for entry in layer {
            for dependency in indexed.index().dependencies(entry).unwrap() {
                assert!(seen.contains(dependency));
            }
            seen.insert(entry);
        }
    }
    assert_eq!(
        seen.len(),
        membership.iter().filter(|selected| **selected).count()
    );
}

fn lock_topological_modules(indexed: &npa_package::IndexedPackageLockGraph) -> Vec<Name> {
    indexed
        .index()
        .topological_entries()
        .iter()
        .map(|entry| indexed.index().module_by_entry(*entry).unwrap().clone())
        .collect()
}

fn owned_artifacts(artifacts: &BTreeMap<PackagePath, Vec<u8>>) -> Vec<OwnedPackageLockArtifact> {
    artifacts
        .iter()
        .map(|(path, bytes)| OwnedPackageLockArtifact::from_vec(path.clone(), bytes.clone()))
        .collect()
}

fn build_owned_snapshot(
    validated: &ValidatedPackageManifest,
    artifacts: &BTreeMap<PackagePath, Vec<u8>>,
    retention_policy: PreparedArtifactRetentionPolicy,
    observation_mode: PreparedArtifactObservationMode,
    preparation: Option<&mut PackageArtifactPreparationObservation>,
) -> Result<npa_package::PackageLockArtifactSnapshots, PackageLockError> {
    build_owned_snapshot_api(
        validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        owned_artifacts(artifacts),
        retention_policy,
        observation_mode,
        preparation,
    )
}

fn assert_snapshot_work_oracles() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let expected_count = u64::try_from(artifacts.len()).unwrap();
    let mut success = PackageArtifactPreparationObservation::default();
    build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::RawOnly,
        PreparedArtifactObservationMode::Off,
        Some(&mut success),
    )
    .unwrap();
    assert_eq!(
        success,
        PackageArtifactPreparationObservation {
            artifact_file_hashes: expected_count,
            artifact_full_decodes: expected_count,
            overflowed: false,
        }
    );

    let mut malformed_manifest = proof_manifest();
    let malformed_path = malformed_manifest.modules[0].certificate.clone();
    let malformed_bytes = b"not a certificate".to_vec();
    malformed_manifest.modules[0].expected_certificate_file_hash =
        package_file_hash(&malformed_bytes);
    let malformed_validated = validate_manifest(malformed_manifest).unwrap();
    let mut malformed_artifacts = proof_certificate_artifacts(&malformed_validated);
    malformed_artifacts.insert(malformed_path, malformed_bytes);
    let mut failed = PackageArtifactPreparationObservation::default();
    let error = build_owned_snapshot(
        &malformed_validated,
        &malformed_artifacts,
        PreparedArtifactRetentionPolicy::RawOnly,
        PreparedArtifactObservationMode::Off,
        Some(&mut failed),
    )
    .unwrap_err();
    assert_lock_error_kind_reason(
        &error,
        PackageLockErrorKind::CertificateDecode,
        PackageLockErrorReason::CertificateDecodeFailed,
    );
    assert_eq!(error.path, "modules[0].certificate");
    assert_eq!(failed.artifact_file_hashes, 1);
    assert_eq!(failed.artifact_full_decodes, 1);
    assert!(!failed.overflowed);
}

#[test]
fn owned_lock_builder_matches_borrowed_lock_and_reuses_decoded_artifacts() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let expected = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let owned = artifacts
        .into_iter()
        .map(|(path, bytes)| OwnedPackageLockArtifact::from_vec(path, bytes))
        .collect::<Vec<_>>();
    let expected_count = owned.len() as u64;
    let mut preparation = PackageArtifactPreparationObservation::default();
    let mut payloads = npa_cert::CertificatePayloadObservation::default();
    let result = build_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
        &validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        owned,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        Some(&mut preparation),
        Some(&mut payloads),
    )
    .unwrap();
    let (actual, prepared) = result.into_parts();
    assert_eq!(actual, expected);
    assert_eq!(preparation.artifact_file_hashes, expected_count);
    assert_eq!(preparation.artifact_full_decodes, expected_count);
    assert_eq!(payloads.payloads_frozen, expected_count);
    assert_eq!(
        prepared.retention_observation().unwrap().admissions,
        expected_count
    );
    for entry in &actual.entries {
        assert!(matches!(
            prepared.get(&entry.certificate),
            Some(PreparedPackageArtifactView::Prepared(_))
        ));
    }
}

#[test]
fn snapshot_lock_error_oracle() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let first_path = validated.manifest().modules[0].certificate.clone();

    // Complete map validation precedes every hash/decode attempt, even when
    // the duplicated payload itself is malformed and later artifacts are absent.
    let duplicate = vec![
        OwnedPackageLockArtifact::from_vec(first_path.clone(), b"bad-a".to_vec()),
        OwnedPackageLockArtifact::from_vec(first_path.clone(), b"bad-b".to_vec()),
    ];
    let mut duplicate_work = PackageArtifactPreparationObservation::default();
    let duplicate_error = build_owned_snapshot_api(
        &validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        duplicate,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        Some(&mut duplicate_work),
    )
    .unwrap_err();
    assert_lock_error(
        &duplicate_error,
        PackageLockErrorKind::Duplicate,
        PackageLockErrorReason::DuplicateCertificatePath,
        "artifacts",
        Some("certificate"),
    );
    assert_eq!(
        duplicate_error.actual_value.as_deref(),
        Some(first_path.as_str())
    );
    assert_eq!(
        duplicate_work,
        PackageArtifactPreparationObservation::default()
    );

    // The first local entry's file-hash mismatch precedes malformed later
    // local/external inputs and preserves expected/actual orientation.
    let mut multi_fault = artifacts;
    let first_bytes = b"first local is malformed".to_vec();
    multi_fault.insert(first_path.clone(), first_bytes.clone());
    if let Some(import) = validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .first()
    {
        multi_fault.insert(
            import.certificate.clone(),
            b"later external is malformed".to_vec(),
        );
    }
    let mut work = PackageArtifactPreparationObservation::default();
    let error = build_owned_snapshot(
        &validated,
        &multi_fault,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        Some(&mut work),
    )
    .unwrap_err();
    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::CertificateFileHashMismatch,
        "modules[0].expected_certificate_file_hash",
        Some("expected_certificate_file_hash"),
    );
    let expected_hash =
        format_package_hash(&validated.manifest().modules[0].expected_certificate_file_hash);
    let actual_hash = format_package_hash(&package_file_hash(&first_bytes));
    assert_eq!(
        error.expected_value.as_deref(),
        Some(expected_hash.as_str())
    );
    assert_eq!(error.actual_value.as_deref(), Some(actual_hash.as_str()));
    assert_eq!(work.artifact_file_hashes, 1);
    assert_eq!(work.artifact_full_decodes, 0);
}

#[test]
fn snapshot_lock_hash_work_oracle() {
    assert_snapshot_work_oracles();
}

#[test]
fn snapshot_lock_decode_work_oracle() {
    assert_snapshot_work_oracles();
}

#[test]
fn local_lock_entry() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();

    for module in &validated.manifest().modules {
        let entry = lock
            .entries
            .iter()
            .find(|entry| entry.module == module.module)
            .expect("local lock entry");
        assert_eq!(entry.origin, PackageLockEntryOrigin::Local);
        assert_eq!(entry.certificate, module.certificate);
        assert_eq!(
            entry.certificate_file_hash,
            module.expected_certificate_file_hash
        );
        assert_eq!(entry.export_hash, module.expected_export_hash);
        assert_eq!(entry.axiom_report_hash, module.expected_axiom_report_hash);
        assert_eq!(entry.certificate_hash, module.expected_certificate_hash);
        assert_eq!(entry.package, None);
        assert_eq!(entry.version, None);
    }
}

#[test]
fn external_lock_entry() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();

    for import in validated.manifest().imports.as_deref().unwrap_or(&[]) {
        let entry = lock
            .entries
            .iter()
            .find(|entry| entry.module == import.module)
            .expect("external lock entry");
        assert_eq!(entry.origin, PackageLockEntryOrigin::External);
        assert_eq!(entry.certificate, import.certificate);
        assert_eq!(entry.export_hash, import.export_hash);
        assert_eq!(entry.certificate_hash, import.certificate_hash);
        assert_eq!(entry.package.as_ref(), Some(&import.package));
        assert_eq!(entry.version.as_ref(), Some(&import.version));
    }
}

#[test]
fn build_package_lock_from_artifacts() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    assert_eq!(
        lock.entries.len(),
        validated.manifest().modules.len()
            + validated.manifest().imports.as_deref().unwrap_or(&[]).len()
    );
    assert_eq!(
        lock.manifest.file_hash,
        package_file_hash(&proof_manifest_bytes())
    );
    validate_package_lock_against_manifest_graph(&validated, &lock).unwrap();
}

#[test]
fn owned_artifact_map_precedence() {
    let validated = validated_proof_manifest();
    let path = validated.manifest().modules[0].certificate.clone();
    let duplicate = vec![
        OwnedPackageLockArtifact::from_vec(path.clone(), b"invalid-first".to_vec()),
        OwnedPackageLockArtifact::from_vec(path.clone(), b"invalid-second".to_vec()),
    ];
    let mut preparation = PackageArtifactPreparationObservation::default();
    let error = build_owned_snapshot_api(
        &validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        duplicate,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        Some(&mut preparation),
    )
    .unwrap_err();
    assert_lock_error_kind_reason(
        &error,
        PackageLockErrorKind::Duplicate,
        PackageLockErrorReason::DuplicateCertificatePath,
    );
    assert_eq!(error.path, "artifacts");
    assert_eq!(error.actual_value.as_deref(), Some(path.as_str()));
    assert_eq!(
        preparation,
        PackageArtifactPreparationObservation::default()
    );
}

#[test]
fn owned_local_lock_derivation() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let (lock, prepared) = build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        None,
    )
    .unwrap()
    .into_parts();

    for module in &validated.manifest().modules {
        let entry = lock
            .entries
            .iter()
            .find(|entry| entry.module == module.module)
            .unwrap();
        let Some(PreparedPackageArtifactView::Prepared(snapshot)) =
            prepared.get(&module.certificate)
        else {
            panic!("local derivation should produce one prepared slot");
        };
        assert_eq!(snapshot.file_hash(), entry.certificate_file_hash);
        assert_eq!(snapshot.decoded_header().unwrap().module, module.module);
    }
}

#[test]
fn owned_external_lock_derivation() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let (lock, prepared) = build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        None,
    )
    .unwrap()
    .into_parts();

    for import in validated.manifest().imports.as_deref().unwrap_or(&[]) {
        let entry = lock
            .entries
            .iter()
            .find(|entry| entry.module == import.module)
            .unwrap();
        let Some(PreparedPackageArtifactView::Prepared(snapshot)) =
            prepared.get(&import.certificate)
        else {
            panic!("external derivation should produce one prepared slot");
        };
        assert_eq!(snapshot.file_hash(), entry.certificate_file_hash);
        assert_eq!(snapshot.decoded_header().unwrap().module, import.module);
    }
}

#[test]
fn package_lock_artifact_snapshots() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let snapshots = build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        None,
    )
    .unwrap();
    let (lock, prepared) = snapshots.into_parts();
    assert_eq!(lock.entries.len(), artifacts.len());
    assert_eq!(prepared.retained_decoded_entries(), artifacts.len());
    assert!(lock
        .entries
        .iter()
        .all(|entry| prepared.get(&entry.certificate).is_some()));
}

#[test]
fn owned_lock_finalization() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let expected = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let (actual, _) = build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::RawOnly,
        PreparedArtifactObservationMode::Off,
        None,
    )
    .unwrap()
    .into_parts();
    assert_eq!(actual, expected);
    assert!(actual
        .entries
        .windows(2)
        .all(|entries| entries[0].module <= entries[1].module));
    validate_package_lock_against_manifest_graph(&validated, &actual).unwrap();
}

#[test]
fn build_package_lock_and_snapshot_owned_artifacts() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let mut preparation = PackageArtifactPreparationObservation::default();
    let (lock, prepared) = build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::RawOnly,
        PreparedArtifactObservationMode::Off,
        Some(&mut preparation),
    )
    .unwrap()
    .into_parts();
    assert_eq!(preparation.artifact_file_hashes, artifacts.len() as u64);
    assert_eq!(preparation.artifact_full_decodes, artifacts.len() as u64);
    assert_eq!(prepared.retention_observation(), None);
    assert_eq!(prepared.retained_decoded_entries(), 0);
    for entry in &lock.entries {
        assert!(matches!(
            prepared.get(&entry.certificate),
            Some(PreparedPackageArtifactView::Hashed(_))
        ));
    }
}

#[test]
fn artifact_preparation_hash_attempts() {
    assert_snapshot_work_oracles();
}

#[test]
fn artifact_preparation_full_decode_attempts() {
    assert_snapshot_work_oracles();
}

#[test]
fn owned_builder_differential() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let borrowed = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let (owned, _) = build_owned_snapshot(
        &validated,
        &artifacts,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        None,
    )
    .unwrap()
    .into_parts();
    assert_eq!(owned, borrowed);

    let mut invalid = artifacts;
    let first = validated.manifest().modules[0].certificate.clone();
    invalid.insert(first, b"differential invalid certificate".to_vec());
    let borrowed_error = build_proof_lock_from_artifacts(&validated, &invalid).unwrap_err();
    let owned_error = build_owned_snapshot(
        &validated,
        &invalid,
        PreparedArtifactRetentionPolicy::FastCandidateV1,
        PreparedArtifactObservationMode::Aggregate,
        None,
    )
    .unwrap_err();
    assert_eq!(owned_error, borrowed_error);
}

#[test]
fn package_lock_builder_missing_certificate_file_fails_before_decode() {
    let mut manifest = proof_manifest();
    manifest.modules[0].certificate = PackagePath::new("missing/certificate.npcert");
    let validated = validate_manifest(manifest).unwrap();

    let error = build_package_lock_from_package_root(
        &validated,
        proofs_root(),
        PackagePath::new("npa-package.toml"),
    )
    .unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::ArtifactIo,
        PackageLockErrorReason::CertificateMissing,
        "modules[0].certificate",
        Some("certificate"),
    );
}

#[test]
fn package_lock_builder_rejects_invalid_manifest_path_before_filesystem_read() {
    let validated = validated_proof_manifest();

    let error = build_package_lock_from_package_root(
        &validated,
        proofs_root(),
        PackagePath::new("../npa-package.toml"),
    )
    .unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Path,
        PackageLockErrorReason::InvalidPath,
        "manifest.path",
        None,
    );
}

#[test]
fn package_lock_builder_stale_local_certificate_file_hash_is_rejected_before_decode() {
    let validated = validated_proof_manifest();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let manifest = validated.manifest();
    let first_path = manifest.modules[0].certificate.clone();
    let second_path = manifest.modules[1].certificate.clone();
    let stale_bytes = artifacts.get(&second_path).unwrap().clone();
    artifacts.insert(first_path, stale_bytes);

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::CertificateFileHashMismatch,
        "modules[0].expected_certificate_file_hash",
        Some("expected_certificate_file_hash"),
    );
}

#[test]
fn package_lock_builder_allowing_local_hash_updates_accepts_stale_local_manifest_hashes() {
    let mut manifest = proof_manifest();
    let stale_hash = hash(ZERO_HASH);
    manifest.modules[0].expected_certificate_file_hash = stale_hash;
    manifest.modules[0].expected_export_hash = stale_hash;
    manifest.modules[0].expected_axiom_report_hash = stale_hash;
    manifest.modules[0].expected_certificate_hash = stale_hash;
    let validated = validate_manifest(manifest).unwrap();
    let artifacts = proof_certificate_artifacts(&validated);

    let strict_error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();
    assert_lock_error(
        &strict_error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::CertificateFileHashMismatch,
        "modules[0].expected_certificate_file_hash",
        Some("expected_certificate_file_hash"),
    );

    let refreshed =
        build_proof_lock_from_artifacts_allowing_local_hash_updates(&validated, &artifacts)
            .expect("relaxed builder should derive local hashes from rebuilt certificates");
    let entry = refreshed
        .entries
        .iter()
        .find(|entry| entry.module == validated.manifest().modules[0].module)
        .expect("refreshed lock contains local module");

    assert_ne!(entry.certificate_file_hash, stale_hash);
    assert_ne!(entry.export_hash, stale_hash);
    assert_ne!(entry.axiom_report_hash, stale_hash);
    assert_ne!(entry.certificate_hash, stale_hash);
}

#[test]
fn package_lock_graph_validator_requires_local_manifest_hash_pins() {
    enum LocalPin {
        CertificateFile,
        Export,
        AxiomReport,
        Certificate,
    }

    for (pin, field, reason) in [
        (
            LocalPin::CertificateFile,
            "certificate_file_hash",
            PackageLockErrorReason::CertificateFileHashMismatch,
        ),
        (
            LocalPin::Export,
            "export_hash",
            PackageLockErrorReason::ExportHashMismatch,
        ),
        (
            LocalPin::AxiomReport,
            "axiom_report_hash",
            PackageLockErrorReason::AxiomReportHashMismatch,
        ),
        (
            LocalPin::Certificate,
            "certificate_hash",
            PackageLockErrorReason::CertificateHashMismatch,
        ),
    ] {
        let mut manifest = proof_manifest();
        let stale_hash = hash(ZERO_HASH);
        match pin {
            LocalPin::CertificateFile => {
                manifest.modules[0].expected_certificate_file_hash = stale_hash;
            }
            LocalPin::Export => manifest.modules[0].expected_export_hash = stale_hash,
            LocalPin::AxiomReport => {
                manifest.modules[0].expected_axiom_report_hash = stale_hash;
            }
            LocalPin::Certificate => manifest.modules[0].expected_certificate_hash = stale_hash,
        }
        let validated = validate_manifest(manifest).unwrap();
        let artifacts = proof_certificate_artifacts(&validated);
        let observed_lock =
            build_proof_lock_from_artifacts_allowing_local_hash_updates(&validated, &artifacts)
                .expect("observed lock derives current local hashes");
        let entry_index = lock_entry_index(&observed_lock, &validated.manifest().modules[0].module);

        let error = validate_package_lock_against_manifest_graph(&validated, &observed_lock)
            .expect_err("strict validation must retain local manifest hash pins");
        assert_lock_error(
            &error,
            PackageLockErrorKind::CertificateIdentity,
            reason,
            &format!("entries[{entry_index}].{field}"),
            Some(field),
        );
        validate_observed_package_lock_against_manifest_graph(&validated, &observed_lock)
            .expect("observer validation may report local manifest hash drift");
    }
}

#[test]
fn observed_package_lock_rejects_manifest_locator_and_external_identity_drift() {
    let validated = validated_proof_manifest();
    let artifacts = proof_certificate_artifacts(&validated);
    let lock = build_proof_lock_from_artifacts_allowing_local_hash_updates(&validated, &artifacts)
        .expect("build observed lock");
    let local_module = &validated.manifest().modules[0];
    let local_entry_index = lock_entry_index(&lock, &local_module.module);

    let mut changed = lock.clone();
    changed.entries[local_entry_index].certificate =
        PackagePath::new("moved/local-certificate.npcert");
    let error = validate_observed_package_lock_against_manifest_graph(&validated, &changed)
        .expect_err("observed lock must retain the local certificate locator");
    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::LockEntryMissing,
        &format!("entries[{local_entry_index}].certificate"),
        Some("certificate"),
    );

    let external_import = &validated.manifest().imports.as_deref().unwrap()[0];
    let external_entry_index = lock_entry_index(&lock, &external_import.module);
    let identity_drifts = [
        (
            "package",
            PackageId::new("different-package"),
            PackageVersion::new(external_import.version.as_str()),
            external_import.certificate.clone(),
        ),
        (
            "version",
            PackageId::new(external_import.package.as_str()),
            PackageVersion::new("9.9.9"),
            external_import.certificate.clone(),
        ),
        (
            "certificate",
            PackageId::new(external_import.package.as_str()),
            PackageVersion::new(external_import.version.as_str()),
            PackagePath::new("moved/external-certificate.npcert"),
        ),
    ];
    for (field, package, version, certificate) in identity_drifts {
        let mut changed = lock.clone();
        let entry = &mut changed.entries[external_entry_index];
        entry.package = Some(package);
        entry.version = Some(version);
        entry.certificate = certificate;

        let error = validate_observed_package_lock_against_manifest_graph(&validated, &changed)
            .unwrap_err();
        assert_lock_error(
            &error,
            PackageLockErrorKind::Graph,
            PackageLockErrorReason::LockEntryMissing,
            &format!("entries[{external_entry_index}].{field}"),
            Some(field),
        );
    }
}

#[test]
fn package_lock_root_builder_allowing_local_hash_updates_matches_strict_current_root() {
    let validated = validated_proof_manifest();
    let strict = build_package_lock_from_package_root(
        &validated,
        proofs_root(),
        PackagePath::new("npa-package.toml"),
    )
    .unwrap();
    let relaxed = build_package_lock_from_package_root_allowing_local_hash_updates(
        &validated,
        proofs_root(),
        PackagePath::new("npa-package.toml"),
    )
    .unwrap();

    assert_eq!(relaxed, strict);
}

#[test]
fn package_lock_builder_stale_local_canonical_certificate_hash_is_rejected() {
    let mut manifest = proof_manifest();
    let mut artifacts = proof_certificate_artifacts(&validate_manifest(manifest.clone()).unwrap());
    let certificate_path = manifest.modules[0].certificate.clone();
    let tampered = tampered_certificate_hash(artifacts.get(&certificate_path).unwrap());
    manifest.modules[0].expected_certificate_file_hash = package_file_hash(&tampered);
    artifacts.insert(certificate_path, tampered);
    let validated = validate_manifest(manifest).unwrap();

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::CertificateHashMismatch,
        "modules[0].expected_certificate_hash",
        Some("expected_certificate_hash"),
    );
}

#[test]
fn package_lock_builder_stale_local_axiom_report_hash_is_rejected() {
    let mut manifest = proof_manifest();
    let mut artifacts = proof_certificate_artifacts(&validate_manifest(manifest.clone()).unwrap());
    let certificate_path = manifest.modules[0].certificate.clone();
    let tampered = tampered_axiom_report_hash(artifacts.get(&certificate_path).unwrap());
    manifest.modules[0].expected_certificate_file_hash = package_file_hash(&tampered);
    artifacts.insert(certificate_path, tampered);
    let validated = validate_manifest(manifest).unwrap();

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::AxiomReportHashMismatch,
        "modules[0].expected_axiom_report_hash",
        Some("expected_axiom_report_hash"),
    );
}

#[test]
fn package_lock_builder_stale_external_certificate_module_is_rejected() {
    let validated = validated_proof_manifest();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let import = &validated.manifest().imports.as_deref().unwrap()[0];
    let tampered = tampered_module_name(
        artifacts.get(&import.certificate).unwrap(),
        "Std.Logic.NotEq",
    );
    artifacts.insert(import.certificate.clone(), tampered);

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::CertificateModuleMismatch,
        "imports[0].certificate",
        Some("module"),
    );
}

#[test]
fn package_lock_builder_stale_external_export_hash_is_rejected() {
    let validated = validated_proof_manifest();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let import = &validated.manifest().imports.as_deref().unwrap()[0];
    let tampered = tampered_export_hash(artifacts.get(&import.certificate).unwrap());
    artifacts.insert(import.certificate.clone(), tampered);

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::ExportHashMismatch,
        "imports[0].export_hash",
        Some("export_hash"),
    );
}

#[test]
fn package_lock_builder_stale_external_certificate_hash_is_rejected() {
    let validated = validated_proof_manifest();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let import = &validated.manifest().imports.as_deref().unwrap()[0];
    let tampered = tampered_certificate_hash(artifacts.get(&import.certificate).unwrap());
    artifacts.insert(import.certificate.clone(), tampered);

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::CertificateIdentity,
        PackageLockErrorReason::CertificateHashMismatch,
        "imports[0].certificate_hash",
        Some("certificate_hash"),
    );
}

#[test]
fn package_lock_builder_ignores_source_replay_and_meta_paths() {
    let mut manifest = proof_manifest();
    let original_validated = validate_manifest(manifest.clone()).unwrap();
    let artifacts = proof_certificate_artifacts(&original_validated);
    manifest.modules[0].source = PackagePath::new("missing/source/ignored.npa");
    manifest.modules[0].meta = Some(PackagePath::new("missing/meta/ignored.json"));
    manifest.modules[0].replay = Some(PackagePath::new("missing/replay/ignored.json"));
    let validated = validate_manifest(manifest).unwrap();

    build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
}

#[test]
fn package_lock_import_identity_accepts_interface_dependency_absent_from_manifest_direct_imports() {
    let mut manifest = proof_manifest();
    let external = manifest.imports.as_deref().unwrap()[0].clone();
    let module_index = manifest
        .modules
        .iter()
        .position(|module| module.imports.is_empty())
        .expect("proof corpus has an import-free module");
    let original_validated = validate_manifest(manifest.clone()).unwrap();
    let mut artifacts = proof_certificate_artifacts(&original_validated);
    let base_lock = build_proof_lock_from_artifacts(&original_validated, &artifacts).unwrap();
    let owner_module = manifest.modules[module_index].module.clone();
    let entry_index = lock_entry_index(&base_lock, &owner_module);
    let certificate_path = manifest.modules[module_index].certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports.push(certificate_import(
                &external.module.as_dotted(),
                external.export_hash,
                external.certificate_hash,
            ));
        });
    manifest.modules[module_index].expected_certificate_file_hash = package_file_hash(&tampered);
    artifacts.insert(certificate_path, tampered);
    let validated = validate_manifest(manifest).unwrap();

    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let entry = &lock.entries[entry_index];

    assert!(entry.imports.iter().any(|import| {
        import.module == external.module
            && import.export_hash == external.export_hash
            && import.certificate_hash == external.certificate_hash
    }));
}

#[test]
fn package_lock_import_identity_rejects_wrong_import_export_hash() {
    let mut manifest = proof_manifest();
    let base_validated = validate_manifest(manifest.clone()).unwrap();
    let module_index = first_module_with_manifest_imports(&base_validated);
    let mut artifacts = proof_certificate_artifacts(&base_validated);
    let base_lock = build_proof_lock_from_artifacts(&base_validated, &artifacts).unwrap();
    let owner_module = manifest.modules[module_index].module.clone();
    let entry_index = lock_entry_index(&base_lock, &owner_module);
    let certificate_path = manifest.modules[module_index].certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports[0].export_hash[0] ^= 0x01;
        });
    manifest.modules[module_index].expected_certificate_file_hash = package_file_hash(&tampered);
    artifacts.insert(certificate_path, tampered);
    let validated = validate_manifest(manifest).unwrap();

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::LockImportExportHashMismatch,
        &format!("entries[{entry_index}].imports[0].export_hash"),
        Some("export_hash"),
    );
    assert_lock_error_module_context(&error, &owner_module);
}

#[test]
fn package_lock_import_identity_rejects_wrong_import_certificate_hash() {
    let mut manifest = proof_manifest();
    let base_validated = validate_manifest(manifest.clone()).unwrap();
    let module_index = first_module_with_manifest_imports(&base_validated);
    let mut artifacts = proof_certificate_artifacts(&base_validated);
    let base_lock = build_proof_lock_from_artifacts(&base_validated, &artifacts).unwrap();
    let owner_module = manifest.modules[module_index].module.clone();
    let entry_index = lock_entry_index(&base_lock, &owner_module);
    let certificate_path = manifest.modules[module_index].certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports[0]
                .certificate_hash
                .as_mut()
                .expect("proof imports carry certificate hash")[0] ^= 0x01;
        });
    manifest.modules[module_index].expected_certificate_file_hash = package_file_hash(&tampered);
    artifacts.insert(certificate_path, tampered);
    let validated = validate_manifest(manifest).unwrap();

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::LockImportCertificateHashMismatch,
        &format!("entries[{entry_index}].imports[0].certificate_hash"),
        Some("certificate_hash"),
    );
    assert_lock_error_module_context(&error, &owner_module);
}

#[test]
fn package_lock_import_identity_rejects_manifest_import_absent_from_certificate() {
    let mut manifest = proof_manifest();
    let base_validated = validate_manifest(manifest.clone()).unwrap();
    let module_index = first_module_with_manifest_imports(&base_validated);
    let mut artifacts = proof_certificate_artifacts(&base_validated);
    let owner_module = manifest.modules[module_index].module.clone();
    let certificate_path = manifest.modules[module_index].certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports.remove(0);
        });
    manifest.modules[module_index].expected_certificate_file_hash = package_file_hash(&tampered);
    artifacts.insert(certificate_path, tampered);
    let validated = validate_manifest(manifest).unwrap();

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::CertificateImportMissing,
        &format!("modules[{module_index}].imports[0]"),
        Some("module"),
    );
    assert_lock_error_module_context(&error, &owner_module);
}

#[test]
fn package_lock_import_identity_rejects_external_import_outside_package_lock() {
    let manifest = proof_manifest();
    let validated = validate_manifest(manifest.clone()).unwrap();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let base_lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let external = manifest.imports.as_deref().unwrap()[0].clone();
    let entry_index = lock_entry_index(&base_lock, &external.module);
    let certificate_path = external.certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports.push(certificate_import(
                "Std.Unknown.Missing",
                hash(ZERO_HASH),
                hash(ONE_HASH),
            ));
        });
    artifacts.insert(certificate_path, tampered);

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::LockImportMissing,
        &format!("entries[{entry_index}].imports[0].module"),
        Some("module"),
    );
    assert_lock_error_module_context(&error, &external.module);
}

#[test]
fn package_lock_import_identity_rejects_external_import_to_local_entry() {
    let manifest = proof_manifest();
    let validated = validate_manifest(manifest.clone()).unwrap();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let base_lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let external = manifest.imports.as_deref().unwrap()[0].clone();
    let entry_index = lock_entry_index(&base_lock, &external.module);
    let local = manifest.modules[0].clone();
    let certificate_path = external.certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports.push(certificate_import(
                &local.module.as_dotted(),
                local.expected_export_hash,
                local.expected_certificate_hash,
            ));
        });
    artifacts.insert(certificate_path, tampered);

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::ExternalImportDependsOnLocal,
        &format!("entries[{entry_index}].imports[0].module"),
        Some("module"),
    );
    assert_lock_error_module_context(&error, &external.module);
}

#[test]
fn package_lock_import_identity_resolves_external_import_through_package_lock() {
    let manifest = proof_manifest();
    let validated = validate_manifest(manifest.clone()).unwrap();
    let mut artifacts = proof_certificate_artifacts(&validated);
    let imports = manifest.imports.as_deref().unwrap();
    let first_external = imports[0].clone();
    let second_external = imports[1].clone();
    let certificate_path = first_external.certificate.clone();
    let tampered =
        tampered_certificate_imports(artifacts.get(&certificate_path).unwrap(), |imports| {
            imports.push(certificate_import(
                &second_external.module.as_dotted(),
                second_external.export_hash,
                second_external.certificate_hash,
            ));
        });
    artifacts.insert(certificate_path, tampered);

    let lock = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap();
    let entry = lock
        .entries
        .iter()
        .find(|entry| entry.module == first_external.module)
        .expect("external lock entry exists");

    assert_eq!(entry.imports.len(), 1);
    assert_eq!(entry.imports[0].module, second_external.module);
    assert_eq!(entry.imports[0].export_hash, second_external.export_hash);
    assert_eq!(
        entry.imports[0].certificate_hash,
        second_external.certificate_hash
    );
}

#[test]
fn package_lock_topological_order_uses_lock_graph_dependencies() {
    let graph = build_package_lock_graph(&unsorted_lock()).unwrap();

    assert_eq!(
        graph
            .topological_order
            .iter()
            .map(Name::as_dotted)
            .collect::<Vec<_>>(),
        vec!["Std.Logic.Eq", "Std.Nat.Basic", "Proofs.Ai.Basic"]
    );
}

#[test]
fn package_lock_topological_order_rejects_lock_graph_cycles() {
    let mut lock = unsorted_lock();
    for entry in &mut lock.entries {
        match entry.module.as_dotted().as_str() {
            "Std.Logic.Eq" => {
                entry
                    .imports
                    .push(import("Std.Nat.Basic", NAT_EXPORT_HASH, NAT_CERT_HASH))
            }
            "Std.Nat.Basic" => {
                entry
                    .imports
                    .push(import("Std.Logic.Eq", EQ_EXPORT_HASH, EQ_CERT_HASH))
            }
            _ => {}
        }
    }

    let error = build_package_lock_graph(&lock).unwrap_err();

    assert_lock_error_kind_reason(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::LockImportCycle,
    );
    assert_eq!(
        error.actual_value.as_deref(),
        Some("Std.Logic.Eq -> Std.Nat.Basic -> Std.Logic.Eq")
    );
    assert_lock_error_module_context(&error, &Name::from_dotted("Std.Nat.Basic"));
}
