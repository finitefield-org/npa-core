//! Package lock data model and canonical JSON parsing.
//!
//! A package lock is generated orchestration metadata. It records source-free
//! certificate identities for package graph verification, but it is not proof
//! evidence by itself.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::Path,
};

use npa_cert::Name;

use crate::{
    error::{PackageLockError, PackageLockResult},
    graph::ResolvedModuleImport,
    hash::{format_package_hash, package_file_hash, parse_package_hash, PackageHash},
    json::{parse_json, JsonMember, JsonValue},
    manifest::{PackageExternalImport, PackageModule, PackageVersion},
    name::{validate_package_id, PackageId},
    path::{validate_package_path, PackagePath},
    schema::PACKAGE_LOCK_SCHEMA,
    validate::{validate_package_version, ValidatedPackageManifest},
};

/// Generated `npa.package.lock.v0.1` package lock artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockManifest {
    /// Lock schema string; must equal [`PACKAGE_LOCK_SCHEMA`].
    pub schema: String,
    /// Package identity copied from the validated package manifest.
    pub package: PackageId,
    /// Exact package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Exact manifest path and file hash used to produce the lock.
    pub manifest: PackageLockManifestReference,
    /// Source-free certificate entries sorted canonically when serialized.
    pub entries: Vec<PackageLockEntry>,
}

impl PackageLockManifest {
    /// Serialize the lock as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageLockResult<String> {
        validate_package_lock_manifest(self)?;
        Ok(package_lock_json_unchecked(&normalized_package_lock(self)))
    }
}

/// Package manifest identity recorded inside a package lock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockManifestReference {
    /// Package-relative path to the manifest bytes.
    pub path: PackagePath,
    /// Exact SHA-256 hash of the manifest file bytes.
    pub file_hash: PackageHash,
}

/// Package lock entry origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageLockEntryOrigin {
    /// Certificate belongs to the local package.
    Local,
    /// Certificate belongs to an external hash-pinned package import.
    External,
}

impl PackageLockEntryOrigin {
    /// Return the lock JSON origin string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::External => "external",
        }
    }

    fn parse(value: &str, path: &str) -> PackageLockResult<Self> {
        match value {
            "local" => Ok(Self::Local),
            "external" => Ok(Self::External),
            _ => Err(PackageLockError::invalid_origin(path, value)),
        }
    }
}

/// One source-free certificate identity in a package lock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockEntry {
    /// Module provided by this certificate entry.
    pub module: Name,
    /// Whether the entry is local to the package or external.
    pub origin: PackageLockEntryOrigin,
    /// Package-relative path to the certificate bytes.
    pub certificate: PackagePath,
    /// Exact SHA-256 hash of the certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Canonical export hash declared by the certificate.
    pub export_hash: PackageHash,
    /// Canonical axiom report hash declared by the certificate.
    pub axiom_report_hash: PackageHash,
    /// Canonical certificate hash declared by the certificate.
    pub certificate_hash: PackageHash,
    /// Direct certificate import identities.
    pub imports: Vec<PackageLockImport>,
    /// External package identity; present only when [`Self::origin`] is external.
    pub package: Option<PackageId>,
    /// External package version; present only when [`Self::origin`] is external.
    pub version: Option<PackageVersion>,
}

/// One direct certificate import identity recorded in a package lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockImport {
    /// Imported module name.
    pub module: Name,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Certificate artifact bytes provided to the package lock builder.
#[derive(Clone, Debug)]
pub struct PackageLockArtifact<'a> {
    /// Package-relative certificate path.
    pub path: PackagePath,
    /// Exact certificate file bytes at [`Self::path`].
    pub bytes: &'a [u8],
}

/// Resolved package-lock import graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockGraph {
    /// Direct imports for each canonical, module-sorted package-lock entry.
    pub resolved_entry_imports: Vec<Vec<PackageLockResolvedImport>>,
    /// Deterministic certificate verification order, dependency before dependent.
    pub topological_order: Vec<Name>,
}

/// One package-lock import resolved to another canonical package-lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockResolvedImport {
    /// Imported module name.
    pub module: Name,
    /// Index into the canonical, module-sorted package-lock entry list.
    pub entry_index: usize,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Build a package lock from a validated manifest and explicit certificate bytes.
///
/// This builder reads no source, replay, metadata, theorem-index, or AI trace
/// paths. The manifest bytes are used only to record their exact file hash, and
/// each certificate artifact is decoded only far enough to extract module,
/// import, export, axiom-report, and certificate identity hashes.
pub fn build_package_lock_from_artifacts<'a>(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
) -> PackageLockResult<PackageLockManifest> {
    validate_lock_path(&manifest_path, "manifest.path")?;
    let manifest = validated.manifest();
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let mut entries = Vec::new();

    for (index, module) in manifest.modules.iter().enumerate() {
        let certificate_path = format!("modules[{index}].certificate");
        let bytes =
            certificate_artifact_bytes(&artifact_bytes, &module.certificate, &certificate_path)?;
        entries.push(local_lock_entry(index, module, bytes)?);
    }

    for (index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let certificate_path = format!("imports[{index}].certificate");
        let bytes =
            certificate_artifact_bytes(&artifact_bytes, &import.certificate, &certificate_path)?;
        entries.push(external_lock_entry(index, import, bytes)?);
    }

    let lock = PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        manifest: PackageLockManifestReference {
            path: manifest_path,
            file_hash: package_file_hash(manifest_bytes),
        },
        entries,
    };
    validate_package_lock_manifest(&lock)?;
    validate_package_lock_against_manifest_graph(validated, &lock)?;
    Ok(normalized_package_lock(&lock))
}

/// Build a package lock by reading only the manifest file and certificate files under a package root.
pub fn build_package_lock_from_package_root(
    validated: &ValidatedPackageManifest,
    package_root: impl AsRef<Path>,
    manifest_path: PackagePath,
) -> PackageLockResult<PackageLockManifest> {
    let package_root = package_root.as_ref();
    validate_lock_path(&manifest_path, "manifest.path")?;
    let manifest_bytes =
        read_package_artifact(package_root, &manifest_path, "manifest.path", "manifest")?;
    let mut certificate_buffers = Vec::<(PackagePath, Vec<u8>)>::new();
    let manifest = validated.manifest();

    for (index, module) in manifest.modules.iter().enumerate() {
        let path = format!("modules[{index}].certificate");
        let bytes = read_certificate_artifact(package_root, &module.certificate, &path)?;
        certificate_buffers.push((module.certificate.clone(), bytes));
    }

    for (index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let path = format!("imports[{index}].certificate");
        let bytes = read_certificate_artifact(package_root, &import.certificate, &path)?;
        certificate_buffers.push((import.certificate.clone(), bytes));
    }

    let artifacts = certificate_buffers
        .iter()
        .map(|(path, bytes)| PackageLockArtifact {
            path: path.clone(),
            bytes: bytes.as_slice(),
        });
    build_package_lock_from_artifacts(validated, manifest_path, &manifest_bytes, artifacts)
}

/// Validate a package lock against manifest-resolved imports and return its lock graph.
pub fn validate_package_lock_against_manifest_graph(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<PackageLockGraph> {
    let graph = build_package_lock_graph(lock)?;
    let normalized = normalized_package_lock(lock);
    validate_manifest_lock_entries(validated, &normalized)?;
    validate_local_certificate_imports(validated, &normalized)?;
    Ok(graph)
}

/// Build a resolved package-lock graph and deterministic verification order.
pub fn build_package_lock_graph(lock: &PackageLockManifest) -> PackageLockResult<PackageLockGraph> {
    validate_package_lock_manifest(lock)?;
    let normalized = normalized_package_lock(lock);
    let resolved_entry_imports = resolve_lock_entry_imports(&normalized.entries)?;
    let topological_order = lock_topological_order(&normalized.entries, &resolved_entry_imports)?;

    Ok(PackageLockGraph {
        resolved_entry_imports,
        topological_order,
    })
}

fn artifact_byte_map<'a>(
    artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
) -> PackageLockResult<BTreeMap<PackagePath, &'a [u8]>> {
    let mut artifact_bytes = BTreeMap::new();
    for artifact in artifacts {
        if artifact_bytes
            .insert(artifact.path.clone(), artifact.bytes)
            .is_some()
        {
            return Err(PackageLockError::duplicate_certificate_path(
                "artifacts",
                artifact.path.as_str(),
            ));
        }
    }
    Ok(artifact_bytes)
}

fn certificate_artifact_bytes<'a>(
    artifacts: &BTreeMap<PackagePath, &'a [u8]>,
    path: &PackagePath,
    error_path: &str,
) -> PackageLockResult<&'a [u8]> {
    artifacts
        .get(path)
        .copied()
        .ok_or_else(|| PackageLockError::certificate_missing(error_path, path.as_str()))
}

fn read_certificate_artifact(
    package_root: &Path,
    path: &PackagePath,
    error_path: &str,
) -> PackageLockResult<Vec<u8>> {
    match fs::read(package_root.join(path.as_str())) {
        Ok(bytes) => Ok(bytes),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Err(
            PackageLockError::certificate_missing(error_path, path.as_str()),
        ),
        Err(error) => Err(PackageLockError::artifact_read_failed(
            error_path,
            "certificate",
            path.as_str(),
            error.to_string(),
        )),
    }
}

fn read_package_artifact(
    package_root: &Path,
    path: &PackagePath,
    error_path: &str,
    field: &str,
) -> PackageLockResult<Vec<u8>> {
    fs::read(package_root.join(path.as_str())).map_err(|error| {
        PackageLockError::artifact_read_failed(error_path, field, path.as_str(), error.to_string())
    })
}

fn local_lock_entry(
    index: usize,
    module: &PackageModule,
    certificate_bytes: &[u8],
) -> PackageLockResult<PackageLockEntry> {
    let base_path = format!("modules[{index}]");
    let certificate_file_hash = package_file_hash(certificate_bytes);
    check_certificate_file_hash(
        format!("{base_path}.expected_certificate_file_hash"),
        "expected_certificate_file_hash",
        module.expected_certificate_file_hash,
        certificate_file_hash,
    )?;

    let cert = decode_lock_certificate(certificate_bytes, format!("{base_path}.certificate"))?;
    check_certificate_module(
        format!("{base_path}.certificate"),
        &module.module,
        &cert.header.module,
    )?;
    check_export_hash(
        format!("{base_path}.expected_export_hash"),
        "expected_export_hash",
        module.expected_export_hash,
        PackageHash::from(cert.hashes.export_hash),
    )?;
    check_axiom_report_hash(
        format!("{base_path}.expected_axiom_report_hash"),
        "expected_axiom_report_hash",
        module.expected_axiom_report_hash,
        PackageHash::from(cert.hashes.axiom_report_hash),
    )?;
    check_certificate_hash(
        format!("{base_path}.expected_certificate_hash"),
        "expected_certificate_hash",
        module.expected_certificate_hash,
        PackageHash::from(cert.hashes.certificate_hash),
    )?;

    Ok(PackageLockEntry {
        module: module.module.clone(),
        origin: PackageLockEntryOrigin::Local,
        certificate: module.certificate.clone(),
        certificate_file_hash,
        export_hash: PackageHash::from(cert.hashes.export_hash),
        axiom_report_hash: PackageHash::from(cert.hashes.axiom_report_hash),
        certificate_hash: PackageHash::from(cert.hashes.certificate_hash),
        imports: lock_imports(&cert.imports, &format!("{base_path}.certificate.imports"))?,
        package: None,
        version: None,
    })
}

fn external_lock_entry(
    index: usize,
    import: &PackageExternalImport,
    certificate_bytes: &[u8],
) -> PackageLockResult<PackageLockEntry> {
    let base_path = format!("imports[{index}]");
    let certificate_file_hash = package_file_hash(certificate_bytes);
    let cert = decode_lock_certificate(certificate_bytes, format!("{base_path}.certificate"))?;
    check_certificate_module(
        format!("{base_path}.certificate"),
        &import.module,
        &cert.header.module,
    )?;
    check_export_hash(
        format!("{base_path}.export_hash"),
        "export_hash",
        import.export_hash,
        PackageHash::from(cert.hashes.export_hash),
    )?;
    check_certificate_hash(
        format!("{base_path}.certificate_hash"),
        "certificate_hash",
        import.certificate_hash,
        PackageHash::from(cert.hashes.certificate_hash),
    )?;

    Ok(PackageLockEntry {
        module: import.module.clone(),
        origin: PackageLockEntryOrigin::External,
        certificate: import.certificate.clone(),
        certificate_file_hash,
        export_hash: PackageHash::from(cert.hashes.export_hash),
        axiom_report_hash: PackageHash::from(cert.hashes.axiom_report_hash),
        certificate_hash: PackageHash::from(cert.hashes.certificate_hash),
        imports: lock_imports(&cert.imports, &format!("{base_path}.certificate.imports"))?,
        package: Some(import.package.clone()),
        version: Some(import.version.clone()),
    })
}

fn decode_lock_certificate(
    certificate_bytes: &[u8],
    path: impl Into<String>,
) -> PackageLockResult<npa_cert::ModuleCert> {
    npa_cert::decode_module_cert(certificate_bytes)
        .map_err(|error| PackageLockError::certificate_decode_failed(path, format!("{error:?}")))
}

fn lock_imports(
    imports: &[npa_cert::ImportEntry],
    path: &str,
) -> PackageLockResult<Vec<PackageLockImport>> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            Ok(PackageLockImport {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: PackageHash::from(import.certificate_hash.ok_or_else(|| {
                    PackageLockError::import_certificate_hash_missing(format!(
                        "{path}[{index}].certificate_hash"
                    ))
                })?),
            })
        })
        .collect()
}

fn check_certificate_module(
    path: impl Into<String>,
    expected: &Name,
    actual: &Name,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::certificate_module_mismatch(
            path,
            expected.as_dotted(),
            actual.as_dotted(),
        ))
    }
}

fn check_certificate_file_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::certificate_file_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_export_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::export_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_axiom_report_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::axiom_report_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_certificate_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::certificate_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

/// Parse and validate a package lock from JSON.
pub fn parse_package_lock_json(source: &str) -> PackageLockResult<PackageLockManifest> {
    let root =
        parse_json(source).map_err(|error| PackageLockError::invalid_json(error.to_string()))?;
    let lock = parse_package_lock_value(&root)?;
    validate_package_lock_manifest(&lock)?;
    Ok(normalized_package_lock(&lock))
}

/// Validate a package lock data model without reading files or running checkers.
pub fn validate_package_lock_manifest(lock: &PackageLockManifest) -> PackageLockResult<()> {
    if lock.schema != PACKAGE_LOCK_SCHEMA {
        return Err(PackageLockError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_LOCK_SCHEMA,
            lock.schema.clone(),
        ));
    }
    validate_lock_package_id(&lock.package, "package")?;
    validate_lock_package_version(&lock.version, "version")?;
    validate_lock_path(&lock.manifest.path, "manifest.path")?;

    let mut modules = BTreeMap::<Name, usize>::new();
    let mut certificate_paths = BTreeMap::<String, usize>::new();
    for (entry_index, entry) in lock.entries.iter().enumerate() {
        let entry_path = format!("entries[{entry_index}]");
        validate_lock_module_name(&entry.module, format!("{entry_path}.module"))?;
        validate_lock_path(&entry.certificate, format!("{entry_path}.certificate"))?;
        if modules.insert(entry.module.clone(), entry_index).is_some() {
            return Err(PackageLockError::duplicate_lock_entry(
                format!("{entry_path}.module"),
                entry.module.as_dotted(),
            ));
        }
        if certificate_paths
            .insert(entry.certificate.as_str().to_owned(), entry_index)
            .is_some()
        {
            return Err(PackageLockError::duplicate_certificate_path(
                format!("{entry_path}.certificate"),
                entry.certificate.as_str(),
            ));
        }

        match entry.origin {
            PackageLockEntryOrigin::Local => {
                if let Some(package) = &entry.package {
                    return Err(PackageLockError::local_field_forbidden(
                        format!("{entry_path}.package"),
                        "package",
                        package.as_str(),
                    ));
                }
                if let Some(version) = &entry.version {
                    return Err(PackageLockError::local_field_forbidden(
                        format!("{entry_path}.version"),
                        "version",
                        version.as_str(),
                    ));
                }
            }
            PackageLockEntryOrigin::External => {
                let Some(package) = &entry.package else {
                    return Err(PackageLockError::external_field_required(
                        format!("{entry_path}.package"),
                        "package",
                    ));
                };
                let Some(version) = &entry.version else {
                    return Err(PackageLockError::external_field_required(
                        format!("{entry_path}.version"),
                        "version",
                    ));
                };
                validate_lock_package_id(package, format!("{entry_path}.package"))?;
                validate_lock_package_version(version, format!("{entry_path}.version"))?;
            }
        }

        validate_lock_imports(&entry.imports, &entry_path)?;
    }
    Ok(())
}

fn validate_lock_imports(imports: &[PackageLockImport], entry_path: &str) -> PackageLockResult<()> {
    let mut modules = BTreeSet::<Name>::new();
    for (import_index, import) in imports.iter().enumerate() {
        let import_path = format!("{entry_path}.imports[{import_index}]");
        validate_lock_module_name(&import.module, format!("{import_path}.module"))?;
        if !modules.insert(import.module.clone()) {
            return Err(PackageLockError::duplicate_import(
                format!("{import_path}.module"),
                import.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_manifest_lock_entries(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<()> {
    let entry_indices = lock_entry_indices(&lock.entries);
    let manifest = validated.manifest();

    for (module_index, module) in manifest.modules.iter().enumerate() {
        let Some(entry_index) = entry_indices.get(&module.module).copied() else {
            return Err(PackageLockError::lock_entry_missing(
                format!("modules[{module_index}].module"),
                module.module.as_dotted(),
            ));
        };
        let entry = &lock.entries[entry_index];
        if entry.origin != PackageLockEntryOrigin::Local {
            return Err(PackageLockError::lock_entry_origin_mismatch(
                format!("entries[{entry_index}].origin"),
                "local",
                entry.origin.as_str(),
            ));
        }
    }

    for (import_index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let Some(entry_index) = entry_indices.get(&import.module).copied() else {
            return Err(PackageLockError::lock_entry_missing(
                format!("imports[{import_index}].module"),
                import.module.as_dotted(),
            ));
        };
        let entry = &lock.entries[entry_index];
        if entry.origin != PackageLockEntryOrigin::External {
            return Err(PackageLockError::lock_entry_origin_mismatch(
                format!("entries[{entry_index}].origin"),
                "external",
                entry.origin.as_str(),
            ));
        }
    }

    Ok(())
}

fn validate_local_certificate_imports(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<()> {
    let entry_indices = lock_entry_indices(&lock.entries);
    let manifest = validated.manifest();

    for (module_index, module) in manifest.modules.iter().enumerate() {
        let entry_index = entry_indices
            .get(&module.module)
            .copied()
            .expect("validated manifest lock entry exists");
        let entry = &lock.entries[entry_index];
        compare_manifest_imports(
            module_index,
            entry_index,
            &module.module,
            &validated.graph().resolved_module_imports[module_index],
            &entry.imports,
        )?;
    }

    Ok(())
}

fn compare_manifest_imports(
    module_index: usize,
    entry_index: usize,
    owner_module: &Name,
    expected_imports: &[ResolvedModuleImport],
    actual_imports: &[PackageLockImport],
) -> PackageLockResult<()> {
    let owner_module_name = owner_module.as_dotted();
    let mut expected_by_module = BTreeMap::<Name, (usize, &ResolvedModuleImport)>::new();
    for (expected_index, expected) in expected_imports.iter().enumerate() {
        expected_by_module.insert(expected.module.clone(), (expected_index, expected));
    }

    let mut actual_modules = BTreeSet::<Name>::new();
    for (import_index, actual) in actual_imports.iter().enumerate() {
        let Some((_, expected)) = expected_by_module.get(&actual.module) else {
            return Err(PackageLockError::manifest_import_missing(
                format!("entries[{entry_index}].imports[{import_index}].module"),
                actual.module.as_dotted(),
            )
            .with_module(owner_module_name.clone()));
        };

        check_lock_import_export_hash(
            format!("entries[{entry_index}].imports[{import_index}].export_hash"),
            expected.export_hash,
            actual.export_hash,
        )
        .map_err(|error| error.with_module(owner_module_name.clone()))?;
        check_lock_import_certificate_hash(
            format!("entries[{entry_index}].imports[{import_index}].certificate_hash"),
            expected.certificate_hash,
            actual.certificate_hash,
        )
        .map_err(|error| error.with_module(owner_module_name.clone()))?;
        actual_modules.insert(actual.module.clone());
    }

    for (expected_index, expected) in expected_imports.iter().enumerate() {
        if !actual_modules.contains(&expected.module) {
            return Err(PackageLockError::certificate_import_missing(
                format!("modules[{module_index}].imports[{expected_index}]"),
                expected.module.as_dotted(),
            )
            .with_module(owner_module_name.clone()));
        }
    }

    Ok(())
}

fn resolve_lock_entry_imports(
    entries: &[PackageLockEntry],
) -> PackageLockResult<Vec<Vec<PackageLockResolvedImport>>> {
    let entry_indices = lock_entry_indices(entries);
    let mut resolved_entries = Vec::with_capacity(entries.len());

    for (entry_index, entry) in entries.iter().enumerate() {
        let owner_module_name = entry.module.as_dotted();
        let mut resolved_imports = Vec::with_capacity(entry.imports.len());
        for (import_index, import) in entry.imports.iter().enumerate() {
            let import_path = format!("entries[{entry_index}].imports[{import_index}]");
            let Some(import_entry_index) = entry_indices.get(&import.module).copied() else {
                return Err(PackageLockError::lock_import_missing(
                    format!("{import_path}.module"),
                    import.module.as_dotted(),
                )
                .with_module(owner_module_name.clone()));
            };
            let import_entry = &entries[import_entry_index];

            if entry.origin == PackageLockEntryOrigin::External
                && import_entry.origin == PackageLockEntryOrigin::Local
            {
                return Err(PackageLockError::external_import_depends_on_local(
                    format!("{import_path}.module"),
                    import.module.as_dotted(),
                )
                .with_module(owner_module_name.clone()));
            }

            check_lock_import_export_hash(
                format!("{import_path}.export_hash"),
                import_entry.export_hash,
                import.export_hash,
            )
            .map_err(|error| error.with_module(owner_module_name.clone()))?;
            check_lock_import_certificate_hash(
                format!("{import_path}.certificate_hash"),
                import_entry.certificate_hash,
                import.certificate_hash,
            )
            .map_err(|error| error.with_module(owner_module_name.clone()))?;

            resolved_imports.push(PackageLockResolvedImport {
                module: import.module.clone(),
                entry_index: import_entry_index,
                export_hash: import.export_hash,
                certificate_hash: import.certificate_hash,
            });
        }
        resolved_entries.push(resolved_imports);
    }

    Ok(resolved_entries)
}

fn lock_entry_indices(entries: &[PackageLockEntry]) -> BTreeMap<Name, usize> {
    entries
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.module.clone(), index))
        .collect()
}

fn lock_topological_order(
    entries: &[PackageLockEntry],
    resolved_entry_imports: &[Vec<PackageLockResolvedImport>],
) -> PackageLockResult<Vec<Name>> {
    let mut states = vec![LockVisitState::Unvisited; entries.len()];
    let mut stack = Vec::<usize>::new();
    let mut order = Vec::<Name>::new();

    for entry_index in 0..entries.len() {
        visit_lock_entry(
            entry_index,
            entries,
            resolved_entry_imports,
            &mut states,
            &mut stack,
            &mut order,
        )?;
    }

    Ok(order)
}

fn visit_lock_entry(
    entry_index: usize,
    entries: &[PackageLockEntry],
    resolved_entry_imports: &[Vec<PackageLockResolvedImport>],
    states: &mut [LockVisitState],
    stack: &mut Vec<usize>,
    order: &mut Vec<Name>,
) -> PackageLockResult<()> {
    match states[entry_index] {
        LockVisitState::Visited => return Ok(()),
        LockVisitState::Visiting => {
            return Err(PackageLockError::lock_import_cycle(
                format!("entries[{entry_index}].imports"),
                lock_cycle_path(entries, stack, entry_index),
            )
            .with_module(entries[entry_index].module.as_dotted()));
        }
        LockVisitState::Unvisited => {}
    }

    states[entry_index] = LockVisitState::Visiting;
    stack.push(entry_index);

    for import in &resolved_entry_imports[entry_index] {
        if states[import.entry_index] == LockVisitState::Visiting {
            return Err(PackageLockError::lock_import_cycle(
                format!("entries[{entry_index}].imports"),
                lock_cycle_path(entries, stack, import.entry_index),
            )
            .with_module(entries[entry_index].module.as_dotted()));
        }
        visit_lock_entry(
            import.entry_index,
            entries,
            resolved_entry_imports,
            states,
            stack,
            order,
        )?;
    }

    stack.pop();
    states[entry_index] = LockVisitState::Visited;
    order.push(entries[entry_index].module.clone());
    Ok(())
}

fn lock_cycle_path(entries: &[PackageLockEntry], stack: &[usize], repeated: usize) -> String {
    let start = stack
        .iter()
        .position(|entry_index| *entry_index == repeated)
        .unwrap_or(0);
    let mut cycle = stack[start..]
        .iter()
        .map(|entry_index| entries[*entry_index].module.as_dotted())
        .collect::<Vec<_>>();
    cycle.push(entries[repeated].module.as_dotted());
    cycle.join(" -> ")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LockVisitState {
    Unvisited,
    Visiting,
    Visited,
}

fn check_lock_import_export_hash(
    path: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::lock_import_export_hash_mismatch(
            path,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_lock_import_certificate_hash(
    path: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::lock_import_certificate_hash_mismatch(
            path,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn parse_package_lock_value(value: &JsonValue) -> PackageLockResult<PackageLockManifest> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, TOP_LEVEL_FIELDS)?;

    Ok(PackageLockManifest {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        version: PackageVersion::new(required_string(members, "$", "version")?),
        manifest: parse_manifest_reference(required_value(members, "$", "manifest")?)?,
        entries: required_array(members, "$", "entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_entry(index, value))
            .collect::<PackageLockResult<Vec<_>>>()?,
    })
}

fn parse_manifest_reference(value: &JsonValue) -> PackageLockResult<PackageLockManifestReference> {
    let path = "manifest";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, MANIFEST_REFERENCE_FIELDS)?;
    Ok(PackageLockManifestReference {
        path: PackagePath::new(required_string(members, path, "path")?),
        file_hash: required_hash(members, path, "file_hash")?,
    })
}

fn parse_entry(index: usize, value: &JsonValue) -> PackageLockResult<PackageLockEntry> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ENTRY_FIELDS)?;
    let origin_path = field_path(&path, "origin");
    let origin =
        PackageLockEntryOrigin::parse(&required_string(members, &path, "origin")?, &origin_path)?;

    Ok(PackageLockEntry {
        module: Name::from_dotted(required_string(members, &path, "module")?),
        origin,
        certificate: PackagePath::new(required_string(members, &path, "certificate")?),
        certificate_file_hash: required_hash(members, &path, "certificate_file_hash")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        axiom_report_hash: required_hash(members, &path, "axiom_report_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        imports: required_array(members, &path, "imports")?
            .iter()
            .enumerate()
            .map(|(import_index, value)| parse_import(&path, import_index, value))
            .collect::<PackageLockResult<Vec<_>>>()?,
        package: optional_string(members, &path, "package")?.map(PackageId::new),
        version: optional_string(members, &path, "version")?.map(PackageVersion::new),
    })
}

fn parse_import(
    entry_path: &str,
    import_index: usize,
    value: &JsonValue,
) -> PackageLockResult<PackageLockImport> {
    let path = format!("{entry_path}.imports[{import_index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, IMPORT_FIELDS)?;
    Ok(PackageLockImport {
        module: Name::from_dotted(required_string(members, &path, "module")?),
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
    })
}

const TOP_LEVEL_FIELDS: &[&str] = &["schema", "package", "version", "manifest", "entries"];
const MANIFEST_REFERENCE_FIELDS: &[&str] = &["path", "file_hash"];
const ENTRY_FIELDS: &[&str] = &[
    "module",
    "origin",
    "package",
    "version",
    "certificate",
    "certificate_file_hash",
    "export_hash",
    "axiom_report_hash",
    "certificate_hash",
    "imports",
];
const IMPORT_FIELDS: &[&str] = &["module", "export_hash", "certificate_hash"];

fn expect_object<'a>(value: &'a JsonValue, path: &str) -> PackageLockResult<&'a [JsonMember]> {
    value
        .object_members()
        .ok_or_else(|| PackageLockError::wrong_type(path, None, "object", value.kind().as_str()))
}

fn reject_unknown_fields(
    path: &str,
    members: &[JsonMember],
    allowed: &[&str],
) -> PackageLockResult<()> {
    let mut counts = BTreeMap::<&str, usize>::new();
    for member in members {
        *counts.entry(member.key()).or_insert(0) += 1;
    }

    if let Some((field, _)) = counts.iter().find(|(_, count)| **count > 1) {
        return Err(PackageLockError::duplicate_field(path, *field));
    }
    if let Some((field, _)) = counts
        .iter()
        .find(|(field, _)| !allowed.iter().any(|allowed| allowed == *field))
    {
        return Err(PackageLockError::unknown_field(path, *field));
    }
    Ok(())
}

fn required_value<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<&'a JsonValue> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
        .ok_or_else(|| PackageLockError::missing_field(path, field))
}

fn required_string(members: &[JsonMember], path: &str, field: &str) -> PackageLockResult<String> {
    let value = required_value(members, path, field)?;
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        PackageLockError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "string",
            value.kind().as_str(),
        )
    })
}

fn optional_string(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<Option<String>> {
    let Some(value) = members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
    else {
        return Ok(None);
    };
    value
        .string_value()
        .map(|value| Some(value.to_owned()))
        .ok_or_else(|| {
            PackageLockError::wrong_type(
                field_path(path, field),
                Some(field.to_owned()),
                "string",
                value.kind().as_str(),
            )
        })
}

fn required_array<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<&'a [JsonValue]> {
    let value = required_value(members, path, field)?;
    value.array_elements().ok_or_else(|| {
        PackageLockError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "array",
            value.kind().as_str(),
        )
    })
}

fn required_hash(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<PackageHash> {
    let field_path = field_path(path, field);
    let value = required_string(members, path, field)?;
    parse_package_hash(&value, &field_path)
        .map_err(|_| PackageLockError::invalid_hash_format(field_path, value))
}

fn validate_lock_module_name(name: &Name, path: impl Into<String>) -> PackageLockResult<()> {
    let path = path.into();
    if name.is_canonical() {
        Ok(())
    } else {
        Err(PackageLockError::invalid_module_name(
            path,
            name.as_dotted(),
        ))
    }
}

fn validate_lock_package_id(id: &PackageId, path: impl Into<String>) -> PackageLockResult<()> {
    let path = path.into();
    validate_package_id(id, &path)
        .map_err(|_| PackageLockError::invalid_package_id(path, id.as_str()))
}

fn validate_lock_package_version(
    version: &PackageVersion,
    path: impl Into<String>,
) -> PackageLockResult<()> {
    let path = path.into();
    validate_package_version(version, &path)
        .map_err(|_| PackageLockError::invalid_version(path, version.as_str()))
}

fn validate_lock_path(path: &PackagePath, error_path: impl Into<String>) -> PackageLockResult<()> {
    let error_path = error_path.into();
    validate_package_path(path, &error_path)
        .map_err(|_| PackageLockError::invalid_path(error_path, path.as_str()))
}

fn normalized_package_lock(lock: &PackageLockManifest) -> PackageLockManifest {
    let mut normalized = lock.clone();
    normalized
        .entries
        .sort_by(|left, right| left.module.cmp(&right.module));
    for entry in &mut normalized.entries {
        entry
            .imports
            .sort_by(|left, right| left.module.cmp(&right.module));
    }
    normalized
}

fn package_lock_json_unchecked(lock: &PackageLockManifest) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&lock.schema)),
        ("package", json_string(lock.package.as_str())),
        ("version", json_string(lock.version.as_str())),
        ("manifest", manifest_reference_json(&lock.manifest)),
        (
            "entries",
            json_array(lock.entries.iter().map(entry_json_unchecked).collect()),
        ),
    ])
}

fn manifest_reference_json(manifest: &PackageLockManifestReference) -> String {
    json_object_in_order(vec![
        ("path", json_string(manifest.path.as_str())),
        ("file_hash", hash_json(manifest.file_hash)),
    ])
}

fn entry_json_unchecked(entry: &PackageLockEntry) -> String {
    let mut fields = vec![
        ("module", json_string(&entry.module.as_dotted())),
        ("origin", json_string(entry.origin.as_str())),
    ];
    if entry.origin == PackageLockEntryOrigin::External {
        fields.push((
            "package",
            json_string(
                entry
                    .package
                    .as_ref()
                    .expect("validated external entry has package")
                    .as_str(),
            ),
        ));
        fields.push((
            "version",
            json_string(
                entry
                    .version
                    .as_ref()
                    .expect("validated external entry has version")
                    .as_str(),
            ),
        ));
    }
    fields.extend([
        ("certificate", json_string(entry.certificate.as_str())),
        (
            "certificate_file_hash",
            hash_json(entry.certificate_file_hash),
        ),
        ("export_hash", hash_json(entry.export_hash)),
        ("axiom_report_hash", hash_json(entry.axiom_report_hash)),
        ("certificate_hash", hash_json(entry.certificate_hash)),
        (
            "imports",
            json_array(entry.imports.iter().map(import_json).collect()),
        ),
    ]);
    json_object_in_order(fields)
}

fn import_json(import: &PackageLockImport) -> String {
    json_object_in_order(vec![
        ("module", json_string(&import.module.as_dotted())),
        ("export_hash", hash_json(import.export_hash)),
        ("certificate_hash", hash_json(import.certificate_hash)),
    ])
}

fn json_object_in_order(fields: Vec<(&str, String)>) -> String {
    let mut out = String::new();
    out.push('{');
    for (index, (key, value)) in fields.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&json_string(key));
        out.push(':');
        out.push_str(value);
    }
    out.push('}');
    out
}

fn json_array(values: Vec<String>) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(value);
    }
    out.push(']');
    out
}

fn hash_json(hash: PackageHash) -> String {
    json_string(&format_package_hash(&hash))
}

fn json_string(value: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{000c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            '\u{0000}'..='\u{001f}' => {
                out.push_str("\\u00");
                out.push(hex_digit((ch as u8) >> 4));
                out.push(hex_digit((ch as u8) & 0x0f));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + (value - 10)),
        _ => unreachable!("hex digit out of range"),
    }
}

fn field_path(path: &str, field: &str) -> String {
    if path == "$" {
        field.to_owned()
    } else {
        format!("{path}.{field}")
    }
}
