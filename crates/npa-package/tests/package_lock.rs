use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use npa_cert::Name;
use npa_package::{
    build_package_lock_from_artifacts, build_package_lock_from_package_root,
    build_package_lock_graph, package_file_hash, parse_manifest_str, parse_package_hash,
    parse_package_lock_json, validate_manifest, PackageHash, PackageId, PackageLockArtifact,
    PackageLockEntry, PackageLockEntryOrigin, PackageLockError, PackageLockErrorKind,
    PackageLockErrorReason, PackageLockImport, PackageLockManifest, PackageLockManifestReference,
    PackagePath, PackageVersion, ValidatedPackageManifest, PACKAGE_LOCK_SCHEMA,
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
    repo_root().join("proofs")
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
    build_package_lock_from_artifacts(
        validated,
        PackagePath::new("npa-package.toml"),
        &proof_manifest_bytes(),
        package_lock_artifacts(artifacts),
    )
}

fn tampered_certificate_hash(bytes: &[u8]) -> Vec<u8> {
    let mut cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    cert.hashes.certificate_hash[0] ^= 0x01;
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_export_hash(bytes: &[u8]) -> Vec<u8> {
    let mut cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    cert.hashes.export_hash[0] ^= 0x01;
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_axiom_report_hash(bytes: &[u8]) -> Vec<u8> {
    let mut cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    cert.hashes.axiom_report_hash[0] ^= 0x01;
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_module_name(bytes: &[u8], module: &str) -> Vec<u8> {
    let mut cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    cert.header.module = Name::from_dotted(module);
    npa_cert::encode_module_cert(&cert).expect("tampered certificate re-encodes")
}

fn tampered_certificate_imports(
    bytes: &[u8],
    edit: impl FnOnce(&mut Vec<npa_cert::ImportEntry>),
) -> Vec<u8> {
    let mut cert = npa_cert::decode_module_cert(bytes).expect("certificate decodes before tamper");
    edit(&mut cert.imports);
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
fn package_lock_import_identity_rejects_certificate_import_absent_from_manifest_graph() {
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

    let error = build_proof_lock_from_artifacts(&validated, &artifacts).unwrap_err();

    assert_lock_error(
        &error,
        PackageLockErrorKind::Graph,
        PackageLockErrorReason::ManifestImportMissing,
        &format!("entries[{entry_index}].imports[0].module"),
        Some("module"),
    );
    assert_lock_error_module_context(&error, &owner_module);
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
