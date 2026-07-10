//! Implementation of `npa package build-certs`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    time::Instant,
};

use npa_api::{build_legacy_std_package_module_cert, LEGACY_STD_PACKAGE_PRODUCER_PROFILE};
use npa_cert::{AxiomPolicy, ModuleCert, Name, VerifiedModule, VerifierSession};
use npa_frontend::{
    compile_human_source_to_built_certificate_only_with_import_refs,
    compile_human_source_to_built_certificate_output_with_import_refs,
    compile_human_source_to_certificate_output_with_import_refs_and_axiom_policy,
    parse_human_module, FileId, HumanCompileOptions, HumanImportedSourceInterface, HumanItem,
    HumanName, HumanSourceDeclarationKind, HumanSourceDeclarationMetadata, HumanSourceInterface,
    HumanUniverseParam, Span, VerifiedImport,
};
use npa_package::{
    build_package_lock_from_artifacts, format_package_hash, package_build_check_cache_key,
    package_build_check_result_entry_json, package_file_hash, parse_and_validate_manifest_str,
    parse_package_build_check_result_entry_json, parse_package_lock_json,
    validate_package_lock_against_manifest_graph, PackageArtifactErrorReason,
    PackageBuildCheckCacheKeyInput, PackageBuildCheckCachedStatus, PackageBuildCheckImportIdentity,
    PackageBuildCheckResultEntry, PackageHash, PackageLockArtifact, PackageLockEntry,
    PackageLockEntryOrigin, PackageLockImport, PackageLockManifest, PackageLockManifestReference,
    PackageManifest, PackageModule, PackagePath, ResolvedModuleImportKind,
    ValidatedPackageManifest, PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR,
    PACKAGE_BUILD_CHECK_CACHE_SCHEMA, PACKAGE_BUILD_CHECK_RESULT_SCHEMA, PACKAGE_LOCK_SCHEMA,
};
use toml_edit::{DocumentMut, InlineTable, Table, Value};

use crate::args::{PackageBuildCertsOptions, PackageBuildCheckCacheMode, PackageCommonOptions};
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{join_package_path, render_package_path};
use crate::package::{load_package_root, LoadedPackageRoot, PACKAGE_MANIFEST_PATH};

const COMMAND: &str = "package build-certs";
const PACKAGE_LOCK_PATH: &str = "generated/package-lock.json";
const TERMINAL_CHECK_REUSE_MIN_SOURCE_BYTES: usize = 32 * 1024 * 1024;
static NEXT_BUILD_CHECK_CACHE_WRITE_TEMP: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug)]
struct CertificateArtifactBuffer {
    path: PackagePath,
    bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
struct LocalCertificateBuild {
    module_index: usize,
    module: Name,
    path: PackagePath,
    bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
struct PackageCertificateBuild {
    local_certificates: Vec<LocalCertificateBuild>,
    package_lock_json: String,
}

#[derive(Clone, Debug)]
struct LocalCertificateBuildIdentity {
    module_index: usize,
    source_hash: PackageHash,
}

#[derive(Clone, Debug)]
struct PackageCertificateCheckBuild {
    local_certificates: Vec<LocalCertificateBuildIdentity>,
    package_lock_json: String,
    diagnostic: Option<CommandDiagnostic>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct PackageCertificateRefreshBuild {
    local_modules: Vec<LocalModuleRefreshIdentity>,
    refreshed_manifest_source: String,
    package_lock_json: String,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct LocalModuleRefreshIdentity {
    module_index: usize,
    module: Name,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
    certificate_path: PackagePath,
    certificate_bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
struct ManifestHashRefreshIdentity {
    module_index: usize,
    module: Name,
    source_hash: PackageHash,
    certificate_file_hash: PackageHash,
    export_hash: PackageHash,
    axiom_report_hash: PackageHash,
    certificate_hash: PackageHash,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct RefreshAvailableModule {
    verified: Arc<VerifiedModule>,
    source_interface: HumanImportedSourceInterface,
    remaining_uses: usize,
    origin: RefreshImportOrigin,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RefreshImportOrigin {
    Local,
    External,
}

#[derive(Clone, Debug)]
struct PackageBuildCheckCacheSummary {
    mode: PackageBuildCheckCacheMode,
    hits: usize,
    misses: usize,
    stale: usize,
    schema_misses: usize,
    written: usize,
    live_builds: usize,
    trusted: bool,
    build_evidence: bool,
}

#[derive(Clone, Debug)]
struct PackageBuildCheckKeyedEntry {
    module: Name,
    key_input: PackageBuildCheckCacheKeyInput,
    cache_key: String,
}

#[derive(Clone, Debug)]
struct AvailableModule {
    verified: Arc<VerifiedModule>,
    source_interface: HumanImportedSourceInterface,
    remaining_uses: usize,
}

type DirectImportContext = (Vec<Arc<VerifiedModule>>, Vec<HumanImportedSourceInterface>);

#[derive(Debug)]
enum LocalModuleCheckBuild {
    Verified {
        certificate: ModuleCert,
        generated_bytes: Vec<u8>,
        verified: Box<VerifiedModule>,
        source_interface: Box<HumanSourceInterface>,
    },
    Unverified {
        certificate: ModuleCert,
        generated_bytes: Vec<u8>,
        source_interface: Option<Box<HumanSourceInterface>>,
    },
}

impl LocalModuleCheckBuild {
    fn certificate(&self) -> &ModuleCert {
        match self {
            Self::Verified { certificate, .. } | Self::Unverified { certificate, .. } => {
                certificate
            }
        }
    }

    fn generated_bytes(&self) -> &[u8] {
        match self {
            Self::Verified {
                generated_bytes, ..
            }
            | Self::Unverified {
                generated_bytes, ..
            } => generated_bytes,
        }
    }
}

#[derive(Clone, Debug)]
enum PackageBuildCheckCacheLookup {
    Hit(Box<PackageBuildCheckResultEntry>),
    Missing,
    SchemaMiss,
    Stale,
}

#[derive(Clone, Debug)]
struct PackageBuildCheckCacheRun {
    cache_dir: PathBuf,
    keyed_entries: Vec<PackageBuildCheckKeyedEntry>,
    lookups: Vec<PackageBuildCheckCacheLookup>,
    summary: PackageBuildCheckCacheSummary,
}

#[derive(Clone, Debug)]
struct PendingWrite {
    path: PackagePath,
    full_path: PathBuf,
    temp_path: PathBuf,
    reason_code: &'static str,
    module: Option<Name>,
    previous_bytes: Option<Vec<u8>>,
}

/// Run `package build-certs`.
pub fn run_package_build_certs(options: PackageBuildCertsOptions) -> CommandResult {
    if options.update_manifest_hashes {
        if options.build_check_cache.uses_local_store() {
            return CommandResult::failed(
                COMMAND,
                crate::fs::render_package_root(&options.common.root),
                vec![
                    CommandDiagnostic::error(DiagnosticKind::Usage, "unsupported_flag")
                        .with_field("--build-check-cache")
                        .with_actual_value(options.build_check_cache.as_str()),
                ],
            );
        }
        if options.check {
            return run_package_build_certs_refresh_check(options.common);
        }
        return run_package_build_certs_refresh_write(options.common);
    }
    if options.check {
        return run_package_build_certs_check_with_cache(options.common, options.build_check_cache);
    }
    if options.build_check_cache.uses_local_store() {
        return CommandResult::failed(
            COMMAND,
            crate::fs::render_package_root(&options.common.root),
            vec![
                CommandDiagnostic::error(DiagnosticKind::Usage, "unsupported_flag")
                    .with_field("--build-check-cache")
                    .with_actual_value(options.build_check_cache.as_str()),
            ],
        );
    }

    run_package_build_certs_write(options.common)
}

fn run_package_build_certs_refresh_check(options: PackageCommonOptions) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_write_mode_targets(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    let build = match build_package_certificates_refresh(&loaded) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    if let Some(diagnostic) = check_refreshed_package_build(&loaded, &build) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn run_package_build_certs_refresh_write(options: PackageCommonOptions) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_write_mode_targets(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    let build = match build_package_certificates_refresh(&loaded) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    if let Some(diagnostic) = write_refreshed_package_build(&loaded, &build) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn build_package_certificates_refresh(
    loaded: &LoadedPackageRoot,
) -> Result<PackageCertificateRefreshBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut artifacts = Vec::new();

    if let Some(diagnostic) = load_external_imports(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut artifacts,
    ) {
        return Err(Box::new(diagnostic));
    }

    let refresh_available_modules = available_modules
        .into_iter()
        .map(|(module, available)| {
            (
                module,
                RefreshAvailableModule {
                    verified: available.verified,
                    source_interface: available.source_interface,
                    remaining_uses: available.remaining_uses,
                    origin: RefreshImportOrigin::External,
                },
            )
        })
        .collect();
    let mut refresh_available_modules = refresh_available_modules;
    let mut local_modules = Vec::new();
    if let Some(diagnostic) = build_local_modules_for_refresh(
        loaded,
        &policy,
        &import_use_counts,
        &mut refresh_available_modules,
        &mut local_modules,
    ) {
        return Err(Box::new(diagnostic));
    }

    let refreshed_manifest_source =
        refresh_manifest_hash_fields(&loaded.manifest_source, &local_modules)?;
    let refreshed_validated = parse_and_validate_refreshed_manifest(&refreshed_manifest_source)?;
    validate_refreshed_manifest_unchanged_fields(&loaded.validated, &refreshed_validated)?;
    let package_lock_json = build_refreshed_package_lock(
        loaded,
        &refreshed_validated,
        &refreshed_manifest_source,
        &local_modules,
        &artifacts,
    )?;

    Ok(PackageCertificateRefreshBuild {
        local_modules,
        refreshed_manifest_source,
        package_lock_json,
    })
}

fn build_refreshed_package_lock(
    loaded: &LoadedPackageRoot,
    refreshed_validated: &ValidatedPackageManifest,
    refreshed_manifest_source: &str,
    local_modules: &[LocalModuleRefreshIdentity],
    external_artifacts: &[CertificateArtifactBuffer],
) -> Result<String, Box<CommandDiagnostic>> {
    let local_artifacts = local_modules.iter().map(|module| PackageLockArtifact {
        path: module.certificate_path.clone(),
        bytes: module.certificate_bytes.as_slice(),
    });
    let external_artifacts = external_artifacts
        .iter()
        .map(|artifact| PackageLockArtifact {
            path: artifact.path.clone(),
            bytes: artifact.bytes.as_slice(),
        });
    let refreshed_lock = build_package_lock_from_artifacts(
        refreshed_validated,
        loaded.manifest_path.clone(),
        refreshed_manifest_source.as_bytes(),
        local_artifacts.chain(external_artifacts),
    )
    .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))?;
    refreshed_lock
        .canonical_json()
        .map_err(|error| Box::new(CommandDiagnostic::from_package_lock_error(&error)))
}

fn check_refreshed_package_build(
    loaded: &LoadedPackageRoot,
    build: &PackageCertificateRefreshBuild,
) -> Option<CommandDiagnostic> {
    if loaded.manifest_source.as_bytes() != build.refreshed_manifest_source.as_bytes() {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "manifest_hashes_stale")
                .with_path(PACKAGE_MANIFEST_PATH)
                .with_hashes(
                    format_package_hash(&package_file_hash(
                        build.refreshed_manifest_source.as_bytes(),
                    )),
                    format_package_hash(&package_file_hash(loaded.manifest_source.as_bytes())),
                ),
        );
    }

    let local_modules = match refresh_modules_by_manifest_order(
        &build.local_modules,
        loaded.validated.manifest().modules.len(),
    ) {
        Ok(local_modules) => local_modules,
        Err(diagnostic) => return Some(*diagnostic),
    };
    for module in local_modules {
        let manifest_module = &loaded.validated.manifest().modules[module.module_index];
        if let Some(diagnostic) = check_local_certificate_file(
            loaded,
            module.module_index,
            manifest_module,
            &module.certificate_bytes,
        ) {
            return Some(diagnostic);
        }
    }

    check_package_lock(loaded, &build.package_lock_json)
}

fn refresh_modules_by_manifest_order(
    local_modules: &[LocalModuleRefreshIdentity],
    module_count: usize,
) -> Result<Vec<&LocalModuleRefreshIdentity>, Box<CommandDiagnostic>> {
    let mut modules_by_index = vec![None; module_count];
    for module in local_modules {
        if module.module_index >= module_count {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                    .with_module(module.module.as_dotted())
                    .with_actual_value(module.module_index.to_string()),
            ));
        }
        if modules_by_index[module.module_index].is_some() {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "duplicate_module_index")
                    .with_module(module.module.as_dotted())
                    .with_actual_value(module.module_index.to_string()),
            ));
        }
        modules_by_index[module.module_index] = Some(module);
    }
    modules_by_index
        .into_iter()
        .enumerate()
        .map(|(module_index, module)| {
            module.ok_or_else(|| {
                Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_missing")
                        .with_actual_value(module_index.to_string()),
                )
            })
        })
        .collect()
}

fn refresh_manifest_hash_fields(
    manifest_source: &str,
    identities: &[LocalModuleRefreshIdentity],
) -> Result<String, Box<CommandDiagnostic>> {
    let identities = identities
        .iter()
        .map(ManifestHashRefreshIdentity::from)
        .collect::<Vec<_>>();
    refresh_manifest_hash_fields_for_modules(manifest_source, &identities)
}

fn refresh_manifest_hash_fields_for_modules(
    manifest_source: &str,
    identities: &[ManifestHashRefreshIdentity],
) -> Result<String, Box<CommandDiagnostic>> {
    let mut document = manifest_source.parse::<DocumentMut>().map_err(|error| {
        manifest_refresh_failed(
            PACKAGE_MANIFEST_PATH,
            "toml",
            "valid TOML manifest",
            error.to_string(),
        )
    })?;
    let identities_by_index = manifest_refresh_identities_by_index(identities)?;
    let modules_item = document.get_mut("modules").ok_or_else(|| {
        manifest_refresh_failed("$.modules", "modules", "array of module tables", "missing")
    })?;
    if let Some(modules) = modules_item.as_array_of_tables_mut() {
        refresh_manifest_array_of_tables_hash_fields(&identities_by_index, modules)?;
    } else if let Some(modules) = modules_item.as_array_mut() {
        refresh_manifest_inline_array_hash_fields(&identities_by_index, modules)?;
    } else {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            "array of module tables",
            modules_item.type_name(),
        ));
    }

    Ok(preserve_manifest_source_layout(
        manifest_source,
        document.to_string(),
    ))
}

fn refresh_manifest_array_of_tables_hash_fields(
    identities_by_index: &[Option<&ManifestHashRefreshIdentity>],
    modules: &mut toml_edit::ArrayOfTables,
) -> Result<(), Box<CommandDiagnostic>> {
    if modules.len() != identities_by_index.len() {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            identities_by_index.len().to_string(),
            modules.len().to_string(),
        ));
    }

    for (module_index, identity) in identities_by_index.iter().copied().enumerate() {
        let path = format!("modules[{module_index}]");
        let table = modules.get_mut(module_index).ok_or_else(|| {
            manifest_refresh_failed(
                path.as_str(),
                "modules",
                "module table",
                "non-table array item",
            )
        })?;
        let identity = identity.ok_or_else(|| {
            manifest_refresh_failed(
                path.as_str(),
                "module_index",
                "identity for module index",
                "missing",
            )
        })?;
        refresh_manifest_module_table_hash_fields(table, module_index, identity)?;
    }

    Ok(())
}

fn refresh_manifest_inline_array_hash_fields(
    identities_by_index: &[Option<&ManifestHashRefreshIdentity>],
    modules: &mut toml_edit::Array,
) -> Result<(), Box<CommandDiagnostic>> {
    if modules.len() != identities_by_index.len() {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            identities_by_index.len().to_string(),
            modules.len().to_string(),
        ));
    }

    for (module_index, identity) in identities_by_index.iter().copied().enumerate() {
        let path = format!("modules[{module_index}]");
        let value = modules.get_mut(module_index).ok_or_else(|| {
            manifest_refresh_failed(path.as_str(), "modules", "inline module table", "missing")
        })?;
        let Some(table) = value.as_inline_table_mut() else {
            return Err(manifest_refresh_failed(
                path.as_str(),
                "modules",
                "inline module table",
                value.type_name(),
            ));
        };
        let identity = identity.ok_or_else(|| {
            manifest_refresh_failed(
                path.as_str(),
                "module_index",
                "identity for module index",
                "missing",
            )
        })?;
        refresh_manifest_inline_module_hash_fields(table, module_index, identity)?;
    }

    Ok(())
}

fn refresh_manifest_module_table_hash_fields(
    table: &mut Table,
    module_index: usize,
    identity: &ManifestHashRefreshIdentity,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}]");
    let module_item = table.get("module").ok_or_else(|| {
        manifest_refresh_failed(format!("{path}.module"), "module", "module name", "missing")
    })?;
    let Some(actual_module) = module_item.as_str() else {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            "string",
            module_item.type_name(),
        ));
    };
    let expected_module = identity.module.as_dotted();
    if actual_module != expected_module {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            expected_module,
            actual_module,
        ));
    }

    refresh_module_hash_field(
        table,
        module_index,
        "expected_source_hash",
        identity.source_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_certificate_file_hash",
        identity.certificate_file_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_export_hash",
        identity.export_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_axiom_report_hash",
        identity.axiom_report_hash,
    )?;
    refresh_module_hash_field(
        table,
        module_index,
        "expected_certificate_hash",
        identity.certificate_hash,
    )?;
    Ok(())
}

fn refresh_manifest_inline_module_hash_fields(
    table: &mut InlineTable,
    module_index: usize,
    identity: &ManifestHashRefreshIdentity,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}]");
    let module_value = table.get("module").ok_or_else(|| {
        manifest_refresh_failed(format!("{path}.module"), "module", "module name", "missing")
    })?;
    let Some(actual_module) = module_value.as_str() else {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            "string",
            module_value.type_name(),
        ));
    };
    let expected_module = identity.module.as_dotted();
    if actual_module != expected_module {
        return Err(manifest_refresh_failed(
            format!("{path}.module"),
            "module",
            expected_module,
            actual_module,
        ));
    }

    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_source_hash",
        identity.source_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_certificate_file_hash",
        identity.certificate_file_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_export_hash",
        identity.export_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_axiom_report_hash",
        identity.axiom_report_hash,
    )?;
    refresh_inline_module_hash_field(
        table,
        module_index,
        "expected_certificate_hash",
        identity.certificate_hash,
    )?;
    Ok(())
}

fn manifest_refresh_identities_by_index(
    identities: &[ManifestHashRefreshIdentity],
) -> Result<Vec<Option<&ManifestHashRefreshIdentity>>, Box<CommandDiagnostic>> {
    let mut identities_by_index = vec![None; identities.len()];
    for identity in identities {
        if identity.module_index >= identities.len() {
            return Err(manifest_refresh_failed(
                "$.modules",
                "module_index",
                format!("0..{}", identities.len()),
                identity.module_index.to_string(),
            ));
        }
        if identities_by_index[identity.module_index].is_some() {
            return Err(manifest_refresh_failed(
                "$.modules",
                "module_index",
                "unique module index",
                identity.module_index.to_string(),
            ));
        }
        identities_by_index[identity.module_index] = Some(identity);
    }
    Ok(identities_by_index)
}

fn refresh_module_hash_field(
    table: &mut Table,
    module_index: usize,
    field: &'static str,
    hash: PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}].{field}");
    let item = table.get_mut(field).ok_or_else(|| {
        manifest_refresh_failed(
            path.as_str(),
            field,
            "existing string hash field",
            "missing",
        )
    })?;
    let item_type = item.type_name();
    let Some(value) = item.as_value_mut() else {
        return Err(manifest_refresh_failed(
            path.as_str(),
            field,
            "string",
            item_type,
        ));
    };
    if !value.is_str() {
        return Err(manifest_refresh_failed(
            path.as_str(),
            field,
            "string",
            value.type_name(),
        ));
    }
    let refreshed_hash = format_package_hash(&hash);
    if value.as_str() == Some(refreshed_hash.as_str()) {
        return Ok(());
    }
    let decor = value.decor().clone();
    let mut replacement = Value::from(refreshed_hash);
    *replacement.decor_mut() = decor;
    *value = replacement;
    Ok(())
}

fn refresh_inline_module_hash_field(
    table: &mut InlineTable,
    module_index: usize,
    field: &'static str,
    hash: PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    let path = format!("modules[{module_index}].{field}");
    let value = table.get_mut(field).ok_or_else(|| {
        manifest_refresh_failed(
            path.as_str(),
            field,
            "existing string hash field",
            "missing",
        )
    })?;
    if !value.is_str() {
        return Err(manifest_refresh_failed(
            path.as_str(),
            field,
            "string",
            value.type_name(),
        ));
    }
    let refreshed_hash = format_package_hash(&hash);
    if value.as_str() == Some(refreshed_hash.as_str()) {
        return Ok(());
    }
    let decor = value.decor().clone();
    let mut replacement = Value::from(refreshed_hash);
    *replacement.decor_mut() = decor;
    *value = replacement;
    Ok(())
}

fn preserve_manifest_source_layout(original: &str, refreshed: String) -> String {
    let refreshed = preserve_manifest_trailing_newline(original, refreshed);
    match first_manifest_line_ending(original) {
        Some(ManifestLineEnding::Crlf) => normalize_manifest_line_endings_to_crlf(&refreshed),
        Some(ManifestLineEnding::Lf) | None => refreshed,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ManifestLineEnding {
    Lf,
    Crlf,
}

fn first_manifest_line_ending(source: &str) -> Option<ManifestLineEnding> {
    let bytes = source.as_bytes();
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'\n' {
            return Some(if index > 0 && bytes[index - 1] == b'\r' {
                ManifestLineEnding::Crlf
            } else {
                ManifestLineEnding::Lf
            });
        }
    }
    None
}

fn normalize_manifest_line_endings_to_crlf(source: &str) -> String {
    source.replace("\r\n", "\n").replace('\n', "\r\n")
}

fn preserve_manifest_trailing_newline(original: &str, mut refreshed: String) -> String {
    if original.ends_with('\n') {
        if !refreshed.ends_with('\n') {
            refreshed.push('\n');
        }
    } else {
        while refreshed.ends_with('\n') {
            refreshed.pop();
        }
    }
    refreshed
}

fn parse_and_validate_refreshed_manifest(
    refreshed_manifest_source: &str,
) -> Result<ValidatedPackageManifest, Box<CommandDiagnostic>> {
    parse_and_validate_manifest_str(refreshed_manifest_source).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::PackageManifest,
                "manifest_refresh_parse_failed",
            )
            .with_path(PACKAGE_MANIFEST_PATH)
            .with_actual_value(format!("{error:?}")),
        )
    })
}

fn validate_refreshed_manifest_unchanged_fields(
    original: &ValidatedPackageManifest,
    refreshed: &ValidatedPackageManifest,
) -> Result<(), Box<CommandDiagnostic>> {
    let original_manifest = original.manifest();
    let refreshed_manifest = refreshed.manifest();
    let mut normalized_refreshed = refreshed_manifest.clone();
    normalize_allowed_refresh_hash_fields(original_manifest, &mut normalized_refreshed)?;
    if &normalized_refreshed != original_manifest {
        return Err(manifest_refresh_failed(
            PACKAGE_MANIFEST_PATH,
            "unchanged_fields",
            "only local module hash pins changed",
            "refreshed manifest changed a non-refresh field",
        ));
    }
    Ok(())
}

fn normalize_allowed_refresh_hash_fields(
    original: &PackageManifest,
    refreshed: &mut PackageManifest,
) -> Result<(), Box<CommandDiagnostic>> {
    if refreshed.modules.len() != original.modules.len() {
        return Err(manifest_refresh_failed(
            "$.modules",
            "modules",
            original.modules.len().to_string(),
            refreshed.modules.len().to_string(),
        ));
    }
    for (module_index, original_module) in original.modules.iter().enumerate() {
        let refreshed_module = &mut refreshed.modules[module_index];
        if refreshed_module.module != original_module.module {
            return Err(manifest_refresh_failed(
                format!("modules[{module_index}].module"),
                "module",
                original_module.module.as_dotted(),
                refreshed_module.module.as_dotted(),
            ));
        }
        refreshed_module.expected_source_hash = original_module.expected_source_hash;
        refreshed_module.expected_certificate_file_hash =
            original_module.expected_certificate_file_hash;
        refreshed_module.expected_export_hash = original_module.expected_export_hash;
        refreshed_module.expected_axiom_report_hash = original_module.expected_axiom_report_hash;
        refreshed_module.expected_certificate_hash = original_module.expected_certificate_hash;
    }
    Ok(())
}

impl From<&LocalModuleRefreshIdentity> for ManifestHashRefreshIdentity {
    fn from(identity: &LocalModuleRefreshIdentity) -> Self {
        Self {
            module_index: identity.module_index,
            module: identity.module.clone(),
            source_hash: identity.source_hash,
            certificate_file_hash: identity.certificate_file_hash,
            export_hash: identity.export_hash,
            axiom_report_hash: identity.axiom_report_hash,
            certificate_hash: identity.certificate_hash,
        }
    }
}

fn manifest_refresh_failed(
    path: impl Into<String>,
    field: impl Into<String>,
    expected_value: impl Into<String>,
    actual_value: impl Into<String>,
) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(DiagnosticKind::PackageManifest, "manifest_refresh_failed")
            .with_path(path)
            .with_field(field)
            .with_expected_value(expected_value)
            .with_actual_value(actual_value),
    )
}

/// Run no-write certificate rebuild checking.
///
/// This command reads package source files, local certificate files, external
/// pinned certificate artifacts, and `generated/package-lock.json`. It builds
/// local certificates in memory through the untrusted frontend, verifies the
/// generated canonical certificate bytes through `npa-cert`, and compares the
/// results to the manifest and checked-in artifacts. It does not write files.
pub fn run_package_build_certs_check(options: PackageCommonOptions) -> CommandResult {
    run_package_build_certs_check_with_cache(options, PackageBuildCheckCacheMode::Off)
}

/// Run no-write certificate rebuild checking with optional read-through cache metadata.
pub fn run_package_build_certs_check_with_cache(
    options: PackageCommonOptions,
    build_check_cache: PackageBuildCheckCacheMode,
) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    let cache_cwd = if build_check_cache.uses_local_store() {
        match std::env::current_dir() {
            Ok(cwd) => Some(cwd),
            Err(error) => {
                return CommandResult::failed(
                    COMMAND,
                    loaded.root_display,
                    vec![CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "build_check_cache_cwd_unavailable",
                    )
                    .with_actual_value(error.to_string())],
                );
            }
        }
    } else {
        None
    };

    let build = match build_package_certificates_check(&loaded) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    let cache_run = if build_check_cache.uses_local_store() {
        let cache_cwd = cache_cwd.as_ref().expect("cache cwd captured above");
        Some(prepare_build_check_cache_run(
            &loaded,
            &build.local_certificates,
            cache_cwd,
        ))
    } else {
        None
    };

    if build.diagnostic.is_some() {
        return build_check_result_with_optional_cache(
            loaded.root_display,
            cache_run,
            build.diagnostic,
        );
    }

    if let Some(diagnostic) = check_package_lock(&loaded, &build.package_lock_json) {
        return build_check_result_with_optional_cache(
            loaded.root_display,
            cache_run,
            Some(diagnostic),
        );
    }

    build_check_result_with_optional_cache(loaded.root_display, cache_run, None)
}

/// Run certificate rebuild write mode.
///
/// This mode uses the same complete in-memory build as `--check`, then writes
/// only command-owned certificate artifacts and the generated package lock. No
/// target file is touched until every module has built successfully.
pub fn run_package_build_certs_write(options: PackageCommonOptions) -> CommandResult {
    let loaded = match load_package_root(&options.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };

    if let Some(diagnostic) = check_write_mode_targets(&loaded) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    let build = match build_package_certificates(&loaded) {
        Ok(build) => build,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, loaded.root_display, vec![*diagnostic]);
        }
    };

    if let Some(diagnostic) = write_package_build(&loaded, &build) {
        return CommandResult::failed(COMMAND, loaded.root_display, vec![diagnostic]);
    }

    CommandResult::passed(COMMAND, loaded.root_display)
}

fn check_write_mode_targets(loaded: &LoadedPackageRoot) -> Option<CommandDiagnostic> {
    for (module_index, module) in loaded.validated.manifest().modules.iter().enumerate() {
        let Some(forbidden_reason) =
            forbidden_local_certificate_write_reason(loaded, &module.certificate)
        else {
            continue;
        };
        return Some(
            CommandDiagnostic::error(
                DiagnosticKind::ArtifactIo,
                "certificate_write_target_forbidden",
            )
            .with_module(module.module.as_dotted())
            .with_path(render_package_path(&module.certificate))
            .with_field(format!("modules[{module_index}].certificate"))
            .with_expected_value("local module .npcert certificate artifact")
            .with_actual_value(forbidden_reason),
        );
    }
    None
}

fn forbidden_local_certificate_write_reason(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
) -> Option<&'static str> {
    if path == &loaded.manifest_path {
        return Some("package_manifest");
    }
    if path.as_str() == PACKAGE_LOCK_PATH {
        return Some("package_lock");
    }
    if loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .any(|import| import.certificate == *path)
    {
        return Some("external_import_certificate");
    }
    for module in &loaded.validated.manifest().modules {
        if module.source == *path {
            return Some("source_file");
        }
        if module.meta.as_ref() == Some(path) || module.replay.as_ref() == Some(path) {
            return Some("untrusted_sidecar");
        }
    }
    if !path.as_str().ends_with(".npcert") {
        return Some("non_npcert_certificate_path");
    }
    None
}

fn build_package_certificates(
    loaded: &LoadedPackageRoot,
) -> Result<PackageCertificateBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut artifacts = Vec::new();
    let mut local_certificates = Vec::new();

    if let Some(diagnostic) = load_external_imports(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut artifacts,
    ) {
        return Err(Box::new(diagnostic));
    }

    if let Some(diagnostic) = build_local_modules(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut artifacts,
        &mut local_certificates,
    ) {
        return Err(Box::new(diagnostic));
    }

    let regenerated_lock = match build_package_lock_from_artifacts(
        &loaded.validated,
        loaded.manifest_path.clone(),
        loaded.manifest_source.as_bytes(),
        artifacts.iter().map(|artifact| PackageLockArtifact {
            path: artifact.path.clone(),
            bytes: artifact.bytes.as_slice(),
        }),
    ) {
        Ok(lock) => lock,
        Err(error) => {
            return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
        }
    };

    let regenerated_lock_json = match regenerated_lock.canonical_json() {
        Ok(json) => json,
        Err(error) => {
            return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
        }
    };

    Ok(PackageCertificateBuild {
        local_certificates,
        package_lock_json: regenerated_lock_json,
    })
}

fn axiom_policy_for_package(loaded: &LoadedPackageRoot) -> AxiomPolicy {
    let mut policy = AxiomPolicy::normal();
    if !loaded.validated.manifest().policy.allow_custom_axioms {
        policy.allowlisted_axioms = loaded
            .validated
            .manifest()
            .policy
            .allowed_axioms
            .iter()
            .cloned()
            .collect();
    }
    policy
}

fn build_package_certificates_check(
    loaded: &LoadedPackageRoot,
) -> Result<PackageCertificateCheckBuild, Box<CommandDiagnostic>> {
    let policy = axiom_policy_for_package(loaded);
    let import_use_counts = package_build_import_use_counts(loaded);
    let mut available_modules = BTreeMap::new();
    let mut lock_entries = Vec::new();
    let mut local_certificates = Vec::new();

    if let Some(diagnostic) = load_external_imports_for_check(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut lock_entries,
    ) {
        return Err(Box::new(diagnostic));
    }

    if let Some(diagnostic) = build_local_modules_for_check(
        loaded,
        &policy,
        &import_use_counts,
        &mut available_modules,
        &mut lock_entries,
        &mut local_certificates,
    ) {
        return Ok(PackageCertificateCheckBuild {
            local_certificates,
            package_lock_json: String::new(),
            diagnostic: Some(diagnostic),
        });
    }

    let lock = PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: loaded.validated.manifest().package.clone(),
        version: loaded.validated.manifest().version.clone(),
        manifest: PackageLockManifestReference {
            path: loaded.manifest_path.clone(),
            file_hash: package_file_hash(loaded.manifest_source.as_bytes()),
        },
        entries: lock_entries,
    };
    if let Err(error) = validate_package_lock_against_manifest_graph(&loaded.validated, &lock) {
        return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
    }
    let package_lock_json = match lock.canonical_json() {
        Ok(json) => json,
        Err(error) => {
            return Err(Box::new(CommandDiagnostic::from_package_lock_error(&error)));
        }
    };

    Ok(PackageCertificateCheckBuild {
        local_certificates,
        package_lock_json,
        diagnostic: None,
    })
}

fn package_build_import_use_counts(loaded: &LoadedPackageRoot) -> BTreeMap<Name, usize> {
    let mut counts = BTreeMap::new();
    for imports in &loaded.validated.graph().resolved_module_imports {
        for import in imports {
            *counts.entry(import.module.clone()).or_insert(0) += 1;
        }
    }
    counts
}

fn load_external_imports_for_check(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    lock_entries: &mut Vec<PackageLockEntry>,
) -> Option<CommandDiagnostic> {
    let mut session = VerifierSession::new();
    for (index, import) in loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let bytes = match read_certificate_bytes(
            loaded,
            &import.certificate,
            format!("imports[{index}].certificate"),
        ) {
            Ok(bytes) => bytes,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let verified = match npa_cert::verify_module_cert(&bytes, &mut session, policy) {
            Ok(verified) => verified,
            Err(error) => {
                return Some(
                    CommandDiagnostic::error(
                        DiagnosticKind::Build,
                        "external_certificate_rejected",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(render_package_path(&import.certificate))
                    .with_actual_value(format!("{error:?}")),
                );
            }
        };

        if verified.module() != &import.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_field("module")
                    .with_expected_value(import.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }
        let actual_export_hash = PackageHash::from(verified.export_hash());
        if actual_export_hash != import.export_hash {
            return Some(hash_mismatch(
                "export_hash_mismatch",
                format!("imports[{index}].export_hash"),
                "export_hash",
                import.export_hash,
                actual_export_hash,
            ));
        }
        let actual_certificate_hash = PackageHash::from(verified.certificate_hash());
        if actual_certificate_hash != import.certificate_hash {
            return Some(hash_mismatch(
                "certificate_hash_mismatch",
                format!("imports[{index}].certificate_hash"),
                "certificate_hash",
                import.certificate_hash,
                actual_certificate_hash,
            ));
        }

        let decoded = match npa_cert::decode_module_cert(&bytes) {
            Ok(certificate) => certificate,
            Err(error) => {
                return Some(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackageLock,
                        "certificate_decode_failed",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_actual_value(format!("{error:?}")),
                );
            }
        };
        let imports = match package_lock_imports_for_certificate(
            &decoded.imports,
            &format!("imports[{index}].certificate.imports"),
            &import.module,
        ) {
            Ok(imports) => imports,
            Err(diagnostic) => return Some(*diagnostic),
        };
        lock_entries.push(PackageLockEntry {
            module: import.module.clone(),
            origin: PackageLockEntryOrigin::External,
            certificate: import.certificate.clone(),
            certificate_file_hash: package_file_hash(&bytes),
            export_hash: PackageHash::from(decoded.hashes.export_hash),
            axiom_report_hash: PackageHash::from(decoded.hashes.axiom_report_hash),
            certificate_hash: PackageHash::from(decoded.hashes.certificate_hash),
            imports,
            package: Some(import.package.clone()),
            version: Some(import.version.clone()),
        });

        let remaining_uses = import_use_counts
            .get(&import.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0 {
            available_modules.insert(
                import.module.clone(),
                AvailableModule {
                    source_interface: fallback_imported_source_interface(&verified),
                    verified: Arc::new(verified),
                    remaining_uses,
                },
            );
        }
    }
    None
}

fn build_local_modules_for_check(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    lock_entries: &mut Vec<PackageLockEntry>,
    local_certificates: &mut Vec<LocalCertificateBuildIdentity>,
) -> Option<CommandDiagnostic> {
    let compile_options = HumanCompileOptions::default();
    let progress_filter = std::env::var("NPA_PACKAGE_BUILD_CERTS_PROGRESS").ok();
    let check_hashes = std::env::var_os("NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS").is_none();
    for &module_index in &loaded.validated.graph().topological_order {
        let module = &loaded.validated.manifest().modules[module_index];
        let remaining_uses = import_use_counts
            .get(&module.module)
            .copied()
            .unwrap_or_default();
        let progress_started_at = Instant::now();
        let module_progress_name = module.module.as_dotted();
        let progress = match progress_filter.as_deref() {
            Some("1") => true,
            Some(filter) => module_progress_name.contains(filter),
            None => false,
        };
        if progress {
            eprintln!(
                "package build-certs check: start {}/{} {}",
                module_index + 1,
                loaded.validated.manifest().modules.len(),
                module_progress_name
            );
        }
        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let source_hash = package_file_hash(source.as_bytes());
        if check_hashes {
            if let Some(diagnostic) = check_generated_source_hash(module_index, module, source_hash)
            {
                return Some(diagnostic);
            }
        }
        if check_hashes
            && remaining_uses == 0
            && source.len() >= TERMINAL_CHECK_REUSE_MIN_SOURCE_BYTES
            && module.producer_profile.as_deref() != Some(LEGACY_STD_PACKAGE_PRODUCER_PROFILE)
        {
            if progress {
                eprintln!(
                    "package build-certs check: reuse checked terminal certificate {}",
                    module_progress_name
                );
            }
            drop(source);
            if let Some(diagnostic) = reuse_checked_terminal_certificate_for_check(
                loaded,
                module_index,
                module,
                lock_entries,
            ) {
                return Some(diagnostic);
            }
            if progress {
                eprintln!(
                    "package build-certs check: finish {} in {:.3}s",
                    module_progress_name,
                    progress_started_at.elapsed().as_secs_f64()
                );
            }
            trim_package_build_heap();
            continue;
        }
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                        .with_module(module.module.as_dotted()),
                );
            }
        };
        let (direct_verified_modules, direct_source_interfaces) =
            match take_direct_import_context(loaded, module_index, available_modules) {
                Ok(imports) => imports,
                Err(diagnostic) => return Some(*diagnostic),
            };
        let direct_verified_module_refs = direct_verified_modules
            .iter()
            .map(Arc::as_ref)
            .collect::<Vec<_>>();

        let built = if module.producer_profile.as_deref()
            == Some(LEGACY_STD_PACKAGE_PRODUCER_PROFILE)
        {
            let (certificate, generated_bytes, verified, source_interface) =
                match build_legacy_std_package_certificate(
                    module_index,
                    module,
                    &source,
                    &direct_verified_module_refs,
                    policy,
                ) {
                    Ok(output) => output,
                    Err(diagnostic) => return Some(*diagnostic),
                };
            LocalModuleCheckBuild::Verified {
                certificate,
                generated_bytes,
                verified: Box::new(verified),
                source_interface: Box::new(source_interface),
            }
        } else if remaining_uses == 0 {
            if progress {
                eprintln!(
                    "package build-certs check: compile certificate-only {}",
                    module_progress_name
                );
            }
            let output = match compile_human_source_to_built_certificate_only_with_import_refs(
                file_id,
                module.module.clone(),
                &source,
                &direct_verified_module_refs,
                &direct_source_interfaces,
                &compile_options,
            ) {
                Ok(output) => output,
                Err(error) => return Some(frontend_build_failed(module_index, module, error)),
            };
            if progress {
                eprintln!(
                    "package build-certs check: encode certificate-only {} after {:.3}s",
                    module_progress_name,
                    progress_started_at.elapsed().as_secs_f64()
                );
            }
            let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return Some(
                        CommandDiagnostic::error(
                            DiagnosticKind::Build,
                            "certificate_encode_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_actual_value(format!("{error:?}")),
                    );
                }
            };
            LocalModuleCheckBuild::Unverified {
                certificate: output.certificate,
                generated_bytes,
                source_interface: None,
            }
        } else {
            if progress {
                eprintln!(
                    "package build-certs check: compile with interface {}",
                    module_progress_name
                );
            }
            let output = match compile_human_source_to_built_certificate_output_with_import_refs(
                file_id,
                module.module.clone(),
                &source,
                &direct_verified_module_refs,
                &direct_source_interfaces,
                &compile_options,
            ) {
                Ok(output) => output,
                Err(error) => return Some(frontend_build_failed(module_index, module, error)),
            };
            if progress {
                eprintln!(
                    "package build-certs check: encode with interface {} after {:.3}s",
                    module_progress_name,
                    progress_started_at.elapsed().as_secs_f64()
                );
            }
            let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return Some(
                        CommandDiagnostic::error(
                            DiagnosticKind::Build,
                            "certificate_encode_failed",
                        )
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_actual_value(format!("{error:?}")),
                    );
                }
            };
            LocalModuleCheckBuild::Unverified {
                certificate: output.certificate,
                generated_bytes,
                source_interface: Some(Box::new(output.source_interface)),
            }
        };
        drop(source);
        let certificate = built.certificate();
        let generated_bytes = built.generated_bytes();

        if let Some(diagnostic) =
            check_generated_axiom_policy(loaded, module_index, module, certificate)
        {
            return Some(diagnostic);
        }

        if check_hashes {
            if let Some(diagnostic) =
                check_generated_manifest_hashes(module_index, module, certificate, generated_bytes)
            {
                return Some(diagnostic);
            }
        }

        if let Some(diagnostic) =
            check_local_certificate_file(loaded, module_index, module, generated_bytes)
        {
            local_certificates.push(LocalCertificateBuildIdentity {
                module_index,
                source_hash,
            });
            return Some(diagnostic);
        }

        let imports = match package_lock_imports_for_certificate(
            &certificate.imports,
            &format!("modules[{module_index}].certificate.imports"),
            &module.module,
        ) {
            Ok(imports) => imports,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let lock_entry = PackageLockEntry {
            module: module.module.clone(),
            origin: PackageLockEntryOrigin::Local,
            certificate: module.certificate.clone(),
            certificate_file_hash: package_file_hash(generated_bytes),
            export_hash: PackageHash::from(certificate.hashes.export_hash),
            axiom_report_hash: PackageHash::from(certificate.hashes.axiom_report_hash),
            certificate_hash: PackageHash::from(certificate.hashes.certificate_hash),
            imports,
            package: None,
            version: None,
        };
        if certificate.header.module != module.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_field("module")
                    .with_expected_value(module.module.as_dotted())
                    .with_actual_value(certificate.header.module.as_dotted()),
            );
        }
        let (export_hash, certificate_hash, verified, source_interface) = match built {
            LocalModuleCheckBuild::Verified {
                certificate,
                generated_bytes,
                verified,
                source_interface,
            } => {
                let export_hash = certificate.hashes.export_hash;
                let certificate_hash = certificate.hashes.certificate_hash;
                drop(generated_bytes);
                (
                    export_hash,
                    certificate_hash,
                    Some(*verified),
                    Some(*source_interface),
                )
            }
            LocalModuleCheckBuild::Unverified {
                certificate,
                generated_bytes,
                source_interface,
            } => {
                let export_hash = certificate.hashes.export_hash;
                let certificate_hash = certificate.hashes.certificate_hash;
                if remaining_uses > 0 {
                    let Some(source_interface) = source_interface else {
                        return Some(
                            CommandDiagnostic::error(
                                DiagnosticKind::Internal,
                                "source_interface_missing",
                            )
                            .with_module(module.module.as_dotted()),
                        );
                    };
                    if progress {
                        eprintln!(
                            "package build-certs check: verify {} remaining_uses={}",
                            module.module.as_dotted(),
                            remaining_uses
                        );
                    }
                    drop(certificate);
                    let verified = match npa_cert::verify_module_cert_with_import_refs(
                        &generated_bytes,
                        &direct_verified_module_refs,
                        policy,
                    ) {
                        Ok(verified) => verified,
                        Err(error) => {
                            return Some(
                                CommandDiagnostic::error(
                                    DiagnosticKind::Build,
                                    "certificate_rejected",
                                )
                                .with_module(module.module.as_dotted())
                                .with_path(format!("modules[{module_index}].certificate"))
                                .with_actual_value(format!("{error:?}")),
                            );
                        }
                    };
                    drop(generated_bytes);
                    (
                        export_hash,
                        certificate_hash,
                        Some(verified),
                        Some(*source_interface),
                    )
                } else {
                    drop(certificate);
                    drop(generated_bytes);
                    (export_hash, certificate_hash, None, None)
                }
            }
        };
        if progress {
            eprintln!(
                "package build-certs check: finish {} in {:.3}s",
                module.module.as_dotted(),
                progress_started_at.elapsed().as_secs_f64()
            );
        }

        drop(direct_verified_module_refs);
        drop(direct_verified_modules);
        drop(direct_source_interfaces);
        trim_package_build_heap();

        if let Some(verified) = verified.as_ref() {
            if verified.module() != &module.module {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].certificate"))
                        .with_field("module")
                        .with_expected_value(module.module.as_dotted())
                        .with_actual_value(verified.module().as_dotted()),
                );
            }
        }

        lock_entries.push(lock_entry);

        if remaining_uses > 0 {
            let Some(verified) = verified else {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "verified_module_missing")
                        .with_module(module.module.as_dotted()),
                );
            };
            let Some(source_interface) = source_interface else {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "source_interface_missing")
                        .with_module(module.module.as_dotted()),
                );
            };
            let imported_source_interface = HumanImportedSourceInterface {
                module: module.module.clone(),
                export_hash,
                certificate_hash: Some(certificate_hash),
                source_interface,
            };
            available_modules.insert(
                module.module.clone(),
                AvailableModule {
                    verified: Arc::new(verified),
                    source_interface: imported_source_interface,
                    remaining_uses,
                },
            );
        }
        local_certificates.push(LocalCertificateBuildIdentity {
            module_index,
            source_hash,
        });
    }
    None
}

fn load_external_imports(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
) -> Option<CommandDiagnostic> {
    let mut session = VerifierSession::new();
    for (index, import) in loaded
        .validated
        .manifest()
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let bytes = match read_certificate_bytes(
            loaded,
            &import.certificate,
            format!("imports[{index}].certificate"),
        ) {
            Ok(bytes) => bytes,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let verified = match npa_cert::verify_module_cert(&bytes, &mut session, policy) {
            Ok(verified) => verified,
            Err(error) => {
                return Some(
                    CommandDiagnostic::error(
                        DiagnosticKind::Build,
                        "external_certificate_rejected",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(render_package_path(&import.certificate))
                    .with_actual_value(format!("{error:?}")),
                );
            }
        };

        if verified.module() != &import.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(import.module.as_dotted())
                    .with_path(format!("imports[{index}].certificate"))
                    .with_field("module")
                    .with_expected_value(import.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }
        let actual_export_hash = PackageHash::from(verified.export_hash());
        if actual_export_hash != import.export_hash {
            return Some(hash_mismatch(
                "export_hash_mismatch",
                format!("imports[{index}].export_hash"),
                "export_hash",
                import.export_hash,
                actual_export_hash,
            ));
        }
        let actual_certificate_hash = PackageHash::from(verified.certificate_hash());
        if actual_certificate_hash != import.certificate_hash {
            return Some(hash_mismatch(
                "certificate_hash_mismatch",
                format!("imports[{index}].certificate_hash"),
                "certificate_hash",
                import.certificate_hash,
                actual_certificate_hash,
            ));
        }

        let remaining_uses = import_use_counts
            .get(&import.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0 {
            available_modules.insert(
                import.module.clone(),
                AvailableModule {
                    source_interface: fallback_imported_source_interface(&verified),
                    verified: Arc::new(verified),
                    remaining_uses,
                },
            );
        }
        artifacts.push(CertificateArtifactBuffer {
            path: import.certificate.clone(),
            bytes,
        });
    }
    None
}

fn build_local_modules_for_refresh(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
    local_modules: &mut Vec<LocalModuleRefreshIdentity>,
) -> Option<CommandDiagnostic> {
    let compile_options = HumanCompileOptions::default();
    for &module_index in &loaded.validated.graph().topological_order {
        let module = &loaded.validated.manifest().modules[module_index];
        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let source_hash = package_file_hash(source.as_bytes());
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                        .with_module(module.module.as_dotted()),
                );
            }
        };
        let (direct_verified_modules, direct_source_interfaces) =
            match take_refresh_direct_import_context(loaded, module_index, available_modules) {
                Ok(imports) => imports,
                Err(diagnostic) => return Some(*diagnostic),
            };
        let expected_imports = match package_lock_imports_for_source_interfaces(
            &direct_source_interfaces,
            &format!("modules[{module_index}].imports"),
            &module.module,
        ) {
            Ok(imports) => imports,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let direct_verified_module_refs = direct_verified_modules
            .iter()
            .map(Arc::as_ref)
            .collect::<Vec<_>>();

        let (certificate, generated_bytes, verified, source_interface) =
            if module.producer_profile.as_deref() == Some(LEGACY_STD_PACKAGE_PRODUCER_PROFILE) {
                match build_legacy_std_package_certificate(
                    module_index,
                    module,
                    &source,
                    &direct_verified_module_refs,
                    policy,
                ) {
                    Ok(output) => output,
                    Err(diagnostic) => return Some(*diagnostic),
                }
            } else {
                let output =
                match compile_human_source_to_certificate_output_with_import_refs_and_axiom_policy(
                    file_id,
                    module.module.clone(),
                    &source,
                    &direct_verified_module_refs,
                    &direct_source_interfaces,
                    &compile_options,
                    policy,
                ) {
                    Ok(output) => output,
                    Err(error) => return Some(frontend_build_failed(module_index, module, error)),
                };
                let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        return Some(
                            CommandDiagnostic::error(
                                DiagnosticKind::Build,
                                "certificate_encode_failed",
                            )
                            .with_module(module.module.as_dotted())
                            .with_path(format!("modules[{module_index}].certificate"))
                            .with_actual_value(format!("{error:?}")),
                        );
                    }
                };
                (
                    output.certificate,
                    generated_bytes,
                    output.verified_module,
                    output.source_interface,
                )
            };
        drop(source);

        if let Some(diagnostic) =
            check_generated_axiom_policy(loaded, module_index, module, &certificate)
        {
            return Some(diagnostic);
        }
        if verified.module() != &module.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_field("module")
                    .with_expected_value(module.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }
        if let Some(diagnostic) = check_refreshed_certificate_import_identities(
            module_index,
            &module.module,
            &expected_imports,
            &certificate.imports,
        ) {
            return Some(diagnostic);
        }

        let certificate_file_hash = package_file_hash(&generated_bytes);
        let export_hash = PackageHash::from(certificate.hashes.export_hash);
        let axiom_report_hash = PackageHash::from(certificate.hashes.axiom_report_hash);
        let certificate_hash = PackageHash::from(certificate.hashes.certificate_hash);
        let remaining_uses = import_use_counts
            .get(&module.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0 {
            let imported_source_interface = HumanImportedSourceInterface {
                module: module.module.clone(),
                export_hash: certificate.hashes.export_hash,
                certificate_hash: Some(certificate.hashes.certificate_hash),
                source_interface,
            };
            let verified = Arc::new(verified);
            available_modules.insert(
                module.module.clone(),
                RefreshAvailableModule {
                    verified,
                    source_interface: imported_source_interface,
                    remaining_uses,
                    origin: RefreshImportOrigin::Local,
                },
            );
        }
        local_modules.push(LocalModuleRefreshIdentity {
            module_index,
            module: module.module.clone(),
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
            certificate_path: module.certificate.clone(),
            certificate_bytes: generated_bytes,
        });
    }
    None
}

fn build_local_modules(
    loaded: &LoadedPackageRoot,
    policy: &AxiomPolicy,
    import_use_counts: &BTreeMap<Name, usize>,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
    artifacts: &mut Vec<CertificateArtifactBuffer>,
    local_certificates: &mut Vec<LocalCertificateBuild>,
) -> Option<CommandDiagnostic> {
    let compile_options = HumanCompileOptions::default();
    for &module_index in &loaded.validated.graph().topological_order {
        let module = &loaded.validated.manifest().modules[module_index];
        let source = match read_source(loaded, module_index, module) {
            Ok(source) => source,
            Err(diagnostic) => return Some(*diagnostic),
        };
        let file_id = match u32::try_from(module_index) {
            Ok(index) => FileId(index),
            Err(_) => {
                return Some(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                        .with_module(module.module.as_dotted()),
                );
            }
        };
        let (direct_verified_modules, direct_source_interfaces) =
            match take_direct_import_context(loaded, module_index, available_modules) {
                Ok(imports) => imports,
                Err(diagnostic) => return Some(*diagnostic),
            };
        let direct_verified_module_refs = direct_verified_modules
            .iter()
            .map(Arc::as_ref)
            .collect::<Vec<_>>();

        let (certificate, generated_bytes, verified, source_interface) =
            if module.producer_profile.as_deref() == Some(LEGACY_STD_PACKAGE_PRODUCER_PROFILE) {
                match build_legacy_std_package_certificate(
                    module_index,
                    module,
                    &source,
                    &direct_verified_module_refs,
                    policy,
                ) {
                    Ok(output) => output,
                    Err(diagnostic) => return Some(*diagnostic),
                }
            } else {
                let output =
                match compile_human_source_to_certificate_output_with_import_refs_and_axiom_policy(
                    file_id,
                    module.module.clone(),
                    &source,
                    &direct_verified_module_refs,
                    &direct_source_interfaces,
                    &compile_options,
                    policy,
                ) {
                    Ok(output) => output,
                    Err(error) => return Some(frontend_build_failed(module_index, module, error)),
                };
                let generated_bytes = match npa_cert::encode_module_cert(&output.certificate) {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        return Some(
                            CommandDiagnostic::error(
                                DiagnosticKind::Build,
                                "certificate_encode_failed",
                            )
                            .with_module(module.module.as_dotted())
                            .with_path(format!("modules[{module_index}].certificate"))
                            .with_actual_value(format!("{error:?}")),
                        );
                    }
                };
                (
                    output.certificate,
                    generated_bytes,
                    output.verified_module,
                    output.source_interface,
                )
            };

        if let Some(diagnostic) =
            check_generated_axiom_policy(loaded, module_index, module, &certificate)
        {
            return Some(diagnostic);
        }

        if std::env::var_os("NPA_SKIP_PACKAGE_BUILD_HASH_CHECKS").is_none() {
            if let Some(diagnostic) = check_generated_manifest_hashes(
                module_index,
                module,
                &certificate,
                &generated_bytes,
            ) {
                return Some(diagnostic);
            }
        }

        if verified.module() != &module.module {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_field("module")
                    .with_expected_value(module.module.as_dotted())
                    .with_actual_value(verified.module().as_dotted()),
            );
        }

        let imported_source_interface = HumanImportedSourceInterface {
            module: module.module.clone(),
            export_hash: certificate.hashes.export_hash,
            certificate_hash: Some(certificate.hashes.certificate_hash),
            source_interface,
        };
        let remaining_uses = import_use_counts
            .get(&module.module)
            .copied()
            .unwrap_or_default();
        if remaining_uses > 0 {
            available_modules.insert(
                module.module.clone(),
                AvailableModule {
                    verified: Arc::new(verified),
                    source_interface: imported_source_interface,
                    remaining_uses,
                },
            );
        }
        local_certificates.push(LocalCertificateBuild {
            module_index,
            module: module.module.clone(),
            path: module.certificate.clone(),
            bytes: generated_bytes.clone(),
        });
        artifacts.push(CertificateArtifactBuffer {
            path: module.certificate.clone(),
            bytes: generated_bytes,
        });
    }
    None
}

fn check_local_certificate_file(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    generated_bytes: &[u8],
) -> Option<CommandDiagnostic> {
    let checked_in_bytes = match read_certificate_bytes(
        loaded,
        &module.certificate,
        format!("modules[{module_index}].certificate"),
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return Some(*diagnostic),
    };
    if checked_in_bytes != generated_bytes {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "build_certificate_changed")
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&module.certificate))
                .with_hashes(
                    format_package_hash(&package_file_hash(&checked_in_bytes)),
                    format_package_hash(&package_file_hash(generated_bytes)),
                ),
        );
    }
    None
}

fn package_lock_imports_for_certificate(
    imports: &[npa_cert::ImportEntry],
    path: &str,
    owner_module: &Name,
) -> Result<Vec<PackageLockImport>, Box<CommandDiagnostic>> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            let certificate_hash = import.certificate_hash.ok_or_else(|| {
                Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackageLock,
                        "import_certificate_hash_missing",
                    )
                    .with_module(owner_module.as_dotted())
                    .with_path(format!("{path}[{index}].certificate_hash")),
                )
            })?;
            Ok(PackageLockImport {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: PackageHash::from(certificate_hash),
            })
        })
        .collect()
}

fn package_lock_imports_for_source_interfaces(
    imports: &[HumanImportedSourceInterface],
    path: &str,
    owner_module: &Name,
) -> Result<Vec<PackageLockImport>, Box<CommandDiagnostic>> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            let certificate_hash = import.certificate_hash.ok_or_else(|| {
                Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::HashMismatch,
                        "refreshed_import_identity_mismatch",
                    )
                    .with_module(owner_module.as_dotted())
                    .with_path(format!("{path}[{index}].certificate_hash"))
                    .with_field("certificate_hash")
                    .with_expected_value("live import certificate hash")
                    .with_actual_value("<missing>"),
                )
            })?;
            Ok(PackageLockImport {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: PackageHash::from(certificate_hash),
            })
        })
        .collect()
}

fn take_refresh_direct_import_context(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, RefreshAvailableModule>,
) -> Result<DirectImportContext, Box<CommandDiagnostic>> {
    let mut direct_verified_modules = Vec::new();
    let mut direct_source_interfaces = Vec::new();

    for (import_index, import) in loaded.validated.graph().resolved_module_imports[module_index]
        .iter()
        .enumerate()
    {
        let path = format!("modules[{module_index}].imports[{import_index}]");
        let is_last_use = {
            let Some(available) = available_modules.get_mut(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "import_identity_unavailable",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(path),
                ));
            };

            check_refresh_available_module_identity(import, available, &path)?;
            if available.remaining_uses <= 1 {
                true
            } else {
                available.remaining_uses -= 1;
                direct_verified_modules.push(Arc::clone(&available.verified));
                direct_source_interfaces.push(available.source_interface.clone());
                false
            }
        };

        if is_last_use {
            let Some(available) = available_modules.remove(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::Internal,
                        "import_identity_unavailable",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(path),
                ));
            };
            direct_verified_modules.push(available.verified);
            direct_source_interfaces.push(available.source_interface);
        }
    }

    Ok((direct_verified_modules, direct_source_interfaces))
}

fn check_refresh_available_module_identity(
    import: &npa_package::ResolvedModuleImport,
    available: &RefreshAvailableModule,
    path: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    match import.kind {
        ResolvedModuleImportKind::External { .. } => {
            if available.origin != RefreshImportOrigin::External {
                return Err(Box::new(refresh_import_origin_mismatch(
                    path,
                    &import.module,
                    "external",
                    available.origin,
                )));
            }
            let actual_export_hash = PackageHash::from(available.verified.export_hash());
            if actual_export_hash != import.export_hash {
                return Err(Box::new(hash_mismatch(
                    "export_hash_mismatch",
                    format!("{path}.export_hash"),
                    "export_hash",
                    import.export_hash,
                    actual_export_hash,
                )));
            }
            let actual_certificate_hash = PackageHash::from(available.verified.certificate_hash());
            if actual_certificate_hash != import.certificate_hash {
                return Err(Box::new(hash_mismatch(
                    "certificate_hash_mismatch",
                    format!("{path}.certificate_hash"),
                    "certificate_hash",
                    import.certificate_hash,
                    actual_certificate_hash,
                )));
            }
        }
        ResolvedModuleImportKind::Local { .. } => {
            if available.origin != RefreshImportOrigin::Local {
                return Err(Box::new(refresh_import_origin_mismatch(
                    path,
                    &import.module,
                    "local",
                    available.origin,
                )));
            }
            let verified_export_hash = PackageHash::from(available.verified.export_hash());
            let interface_export_hash = PackageHash::from(available.source_interface.export_hash);
            if verified_export_hash != interface_export_hash {
                return Err(Box::new(refreshed_import_identity_hash_mismatch(
                    format!("{path}.export_hash"),
                    "export_hash",
                    verified_export_hash,
                    interface_export_hash,
                )));
            }
            let Some(interface_certificate_hash) = available.source_interface.certificate_hash
            else {
                return Err(Box::new(
                    CommandDiagnostic::error(
                        DiagnosticKind::HashMismatch,
                        "refreshed_import_identity_mismatch",
                    )
                    .with_module(import.module.as_dotted())
                    .with_path(format!("{path}.certificate_hash"))
                    .with_field("certificate_hash")
                    .with_expected_value("live verified certificate hash")
                    .with_actual_value("<missing>"),
                ));
            };
            let verified_certificate_hash =
                PackageHash::from(available.verified.certificate_hash());
            let interface_certificate_hash = PackageHash::from(interface_certificate_hash);
            if verified_certificate_hash != interface_certificate_hash {
                return Err(Box::new(refreshed_import_identity_hash_mismatch(
                    format!("{path}.certificate_hash"),
                    "certificate_hash",
                    verified_certificate_hash,
                    interface_certificate_hash,
                )));
            }
        }
    }
    Ok(())
}

fn check_refreshed_certificate_import_identities(
    module_index: usize,
    module: &Name,
    expected: &[PackageLockImport],
    actual: &[npa_cert::ImportEntry],
) -> Option<CommandDiagnostic> {
    let mut expected_by_module: BTreeMap<Name, (usize, &PackageLockImport)> = BTreeMap::new();
    for (import_index, expected) in expected.iter().enumerate() {
        if let Some((_, existing)) = expected_by_module.get(&expected.module).copied() {
            if existing.export_hash != expected.export_hash {
                return Some(refreshed_import_identity_hash_mismatch(
                    format!("modules[{module_index}].imports[{import_index}].export_hash"),
                    "export_hash",
                    existing.export_hash,
                    expected.export_hash,
                ));
            }
            if existing.certificate_hash != expected.certificate_hash {
                return Some(refreshed_import_identity_hash_mismatch(
                    format!("modules[{module_index}].imports[{import_index}].certificate_hash"),
                    "certificate_hash",
                    existing.certificate_hash,
                    expected.certificate_hash,
                ));
            }
            continue;
        }
        expected_by_module.insert(expected.module.clone(), (import_index, expected));
    }

    let mut actual_by_module = BTreeMap::new();
    for (import_index, actual) in actual.iter().enumerate() {
        if actual_by_module
            .insert(actual.module.clone(), (import_index, actual))
            .is_some()
        {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "refreshed_import_identity_mismatch",
                )
                .with_module(module.as_dotted())
                .with_path(format!(
                    "modules[{module_index}].certificate.imports[{import_index}].module"
                ))
                .with_field("module")
                .with_expected_value("unique import module")
                .with_actual_value(actual.module.as_dotted()),
            );
        }
    }

    if expected_by_module.len() != actual_by_module.len() {
        return Some(
            CommandDiagnostic::error(
                DiagnosticKind::HashMismatch,
                "refreshed_import_identity_mismatch",
            )
            .with_module(module.as_dotted())
            .with_path(format!("modules[{module_index}].certificate.imports"))
            .with_field("imports")
            .with_expected_value(expected_by_module.len().to_string())
            .with_actual_value(actual_by_module.len().to_string()),
        );
    }

    for (expected_import_index, expected) in expected_by_module.values().copied() {
        let Some((actual_import_index, actual)) = actual_by_module.get(&expected.module).copied()
        else {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "refreshed_import_identity_mismatch",
                )
                .with_module(module.as_dotted())
                .with_path(format!(
                    "modules[{module_index}].certificate.imports[{expected_import_index}].module"
                ))
                .with_field("module")
                .with_expected_value(expected.module.as_dotted())
                .with_actual_value("<missing>"),
            );
        };
        let path = format!("modules[{module_index}].certificate.imports[{actual_import_index}]");
        let actual_export_hash = PackageHash::from(actual.export_hash);
        if expected.export_hash != actual_export_hash {
            return Some(refreshed_import_identity_hash_mismatch(
                format!("{path}.export_hash"),
                "export_hash",
                expected.export_hash,
                actual_export_hash,
            ));
        }
        let Some(actual_certificate_hash) = actual.certificate_hash else {
            return Some(
                CommandDiagnostic::error(
                    DiagnosticKind::HashMismatch,
                    "refreshed_import_identity_mismatch",
                )
                .with_module(module.as_dotted())
                .with_path(format!("{path}.certificate_hash"))
                .with_field("certificate_hash")
                .with_expected_value(format_package_hash(&expected.certificate_hash))
                .with_actual_value("<missing>"),
            );
        };
        let actual_certificate_hash = PackageHash::from(actual_certificate_hash);
        if expected.certificate_hash != actual_certificate_hash {
            return Some(refreshed_import_identity_hash_mismatch(
                format!("{path}.certificate_hash"),
                "certificate_hash",
                expected.certificate_hash,
                actual_certificate_hash,
            ));
        }
    }

    None
}

fn refreshed_import_identity_hash_mismatch(
    path: String,
    field: &'static str,
    expected: PackageHash,
    actual: PackageHash,
) -> CommandDiagnostic {
    hash_mismatch(
        "refreshed_import_identity_mismatch",
        path,
        field,
        expected,
        actual,
    )
}

fn refresh_import_origin_mismatch(
    path: &str,
    module: &Name,
    expected_origin: &'static str,
    actual_origin: RefreshImportOrigin,
) -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::HashMismatch,
        "refreshed_import_identity_mismatch",
    )
    .with_module(module.as_dotted())
    .with_path(format!("{path}.origin"))
    .with_field("origin")
    .with_expected_value(expected_origin)
    .with_actual_value(actual_origin.as_str())
}

impl RefreshImportOrigin {
    fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::External => "external",
        }
    }
}

fn take_direct_import_context(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    available_modules: &mut BTreeMap<Name, AvailableModule>,
) -> Result<DirectImportContext, Box<CommandDiagnostic>> {
    let mut direct_verified_modules = Vec::new();
    let mut direct_source_interfaces = Vec::new();

    for (import_index, import) in loaded.validated.graph().resolved_module_imports[module_index]
        .iter()
        .enumerate()
    {
        let path = format!("modules[{module_index}].imports[{import_index}]");
        let is_last_use = {
            let Some(available) = available_modules.get_mut(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "import_not_built")
                        .with_module(import.module.as_dotted())
                        .with_path(path),
                ));
            };

            let actual_export_hash = PackageHash::from(available.verified.export_hash());
            if actual_export_hash != import.export_hash {
                return Err(Box::new(hash_mismatch(
                    "export_hash_mismatch",
                    format!("{path}.export_hash"),
                    "export_hash",
                    import.export_hash,
                    actual_export_hash,
                )));
            }
            let actual_certificate_hash = PackageHash::from(available.verified.certificate_hash());
            if actual_certificate_hash != import.certificate_hash {
                return Err(Box::new(hash_mismatch(
                    "certificate_hash_mismatch",
                    format!("{path}.certificate_hash"),
                    "certificate_hash",
                    import.certificate_hash,
                    actual_certificate_hash,
                )));
            }

            if available.remaining_uses <= 1 {
                true
            } else {
                available.remaining_uses -= 1;
                direct_verified_modules.push(Arc::clone(&available.verified));
                direct_source_interfaces.push(available.source_interface.clone());
                false
            }
        };

        if is_last_use {
            let Some(available) = available_modules.remove(&import.module) else {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Internal, "import_not_built")
                        .with_module(import.module.as_dotted())
                        .with_path(path),
                ));
            };
            direct_verified_modules.push(available.verified);
            direct_source_interfaces.push(available.source_interface);
        }
    }

    Ok((direct_verified_modules, direct_source_interfaces))
}

fn build_legacy_std_package_certificate(
    module_index: usize,
    module: &PackageModule,
    source: &str,
    direct_verified_modules: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<(ModuleCert, Vec<u8>, VerifiedModule, HumanSourceInterface), Box<CommandDiagnostic>> {
    validate_legacy_std_source_skeleton(module_index, module, source)?;
    let direct_verified_module_values = direct_verified_modules
        .iter()
        .map(|module| (*module).clone())
        .collect::<Vec<_>>();
    let certificate = match build_legacy_std_package_module_cert(
        &module.module,
        &direct_verified_module_values,
    ) {
        Some(Ok(certificate)) => certificate,
        Some(Err(error)) => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_build_failed")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate"))
                    .with_actual_value(format!("{error:?}")),
            ));
        }
        None => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Build, "unsupported_legacy_std_module")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].producer_profile"))
                    .with_field("producer_profile")
                    .with_expected_value(LEGACY_STD_PACKAGE_PRODUCER_PROFILE)
                    .with_actual_value(
                        module
                            .producer_profile
                            .as_deref()
                            .unwrap_or("<missing-producer-profile>"),
                    ),
            ));
        }
    };
    let verified = npa_cert::verify_built_module_cert_with_import_refs(
        &certificate,
        direct_verified_modules,
        policy,
    )
    .map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_rejected")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_actual_value(format!("{error:?}")),
        )
    })?;
    let generated_bytes = npa_cert::encode_module_cert(&certificate).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_encode_failed")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_actual_value(format!("{error:?}")),
        )
    })?;
    let source_interface = fallback_imported_source_interface(&verified).source_interface;
    Ok((certificate, generated_bytes, verified, source_interface))
}

fn validate_legacy_std_source_skeleton(
    module_index: usize,
    module: &PackageModule,
    source: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    let file_id = match u32::try_from(module_index) {
        Ok(index) => FileId(index),
        Err(_) => {
            return Err(Box::new(
                CommandDiagnostic::error(DiagnosticKind::Internal, "module_index_out_of_range")
                    .with_module(module.module.as_dotted()),
            ));
        }
    };
    let parsed = parse_human_module(file_id, source).map_err(|error| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "source_skeleton_parse_failed")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].source"))
                .with_field("source_skeleton")
                .with_actual_value(error.message),
        )
    })?;
    let mut actual_imports = Vec::new();
    for item in parsed.items {
        match item {
            HumanItem::Import { module, .. } => {
                actual_imports.push(Name::from_dotted(module.as_dotted()));
            }
            other => {
                return Err(Box::new(
                    CommandDiagnostic::error(DiagnosticKind::Build, "source_skeleton_has_items")
                        .with_module(module.module.as_dotted())
                        .with_path(format!("modules[{module_index}].source"))
                        .with_field("source_skeleton")
                        .with_expected_value("imports and comments only")
                        .with_actual_value(format!("{:?}", other.span())),
                ));
            }
        }
    }
    if actual_imports != module.imports {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Build, "source_imports_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].source"))
                .with_field("imports")
                .with_expected_value(format!("{:?}", module.imports))
                .with_actual_value(format!("{actual_imports:?}")),
        ));
    }
    Ok(())
}

fn read_source(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
) -> Result<String, Box<CommandDiagnostic>> {
    let path = join_package_path(
        &loaded.root,
        &module.source,
        format!("modules[{module_index}].source"),
    )?;
    fs::read_to_string(path).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "source_missing")
                .with_module(module.module.as_dotted())
                .with_path(render_package_path(&module.source)),
        )
    })
}

fn read_certificate_bytes(
    loaded: &LoadedPackageRoot,
    path: &PackagePath,
    manifest_field_path: impl Into<String>,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let path = path.clone();
    let full_path = join_package_path(&loaded.root, &path, manifest_field_path)?;
    fs::read(full_path).map_err(|_| {
        Box::new(
            CommandDiagnostic::error(DiagnosticKind::ArtifactIo, "certificate_missing")
                .with_path(render_package_path(&path)),
        )
    })
}

fn check_generated_axiom_policy(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    certificate: &ModuleCert,
) -> Option<CommandDiagnostic> {
    let package_policy = &loaded.validated.manifest().policy;
    if package_policy.allow_custom_axioms {
        return None;
    }

    let allowed_axioms = package_policy
        .allowed_axioms
        .iter()
        .collect::<BTreeSet<&Name>>();
    for axiom in &certificate.axiom_report.module_axioms {
        let Some(name) = certificate.name_table.get(axiom.name) else {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_axiom_name_missing")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].certificate")),
            );
        };
        if name.as_dotted().contains("sorry") || !allowed_axioms.contains(name) {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "disallowed_axiom")
                    .with_module(module.module.as_dotted())
                    .with_path(format!("modules[{module_index}].axioms"))
                    .with_field("axioms")
                    .with_expected_value("allowed axiom or allow_custom_axioms = true")
                    .with_actual_value(name.as_dotted()),
            );
        }
    }
    None
}

fn check_generated_manifest_hashes(
    module_index: usize,
    module: &PackageModule,
    certificate: &ModuleCert,
    certificate_bytes: &[u8],
) -> Option<CommandDiagnostic> {
    let actual_file_hash = package_file_hash(certificate_bytes);
    if actual_file_hash != module.expected_certificate_file_hash {
        return Some(hash_mismatch(
            "certificate_file_hash_mismatch",
            format!("modules[{module_index}].expected_certificate_file_hash"),
            "expected_certificate_file_hash",
            module.expected_certificate_file_hash,
            actual_file_hash,
        ));
    }

    let actual_export_hash = PackageHash::from(certificate.hashes.export_hash);
    if actual_export_hash != module.expected_export_hash {
        return Some(hash_mismatch(
            "export_hash_mismatch",
            format!("modules[{module_index}].expected_export_hash"),
            "expected_export_hash",
            module.expected_export_hash,
            actual_export_hash,
        ));
    }

    let actual_axiom_report_hash = PackageHash::from(certificate.hashes.axiom_report_hash);
    if actual_axiom_report_hash != module.expected_axiom_report_hash {
        return Some(hash_mismatch(
            "axiom_report_hash_mismatch",
            format!("modules[{module_index}].expected_axiom_report_hash"),
            "expected_axiom_report_hash",
            module.expected_axiom_report_hash,
            actual_axiom_report_hash,
        ));
    }

    let actual_certificate_hash = PackageHash::from(certificate.hashes.certificate_hash);
    if actual_certificate_hash != module.expected_certificate_hash {
        return Some(hash_mismatch(
            "certificate_hash_mismatch",
            format!("modules[{module_index}].expected_certificate_hash"),
            "expected_certificate_hash",
            module.expected_certificate_hash,
            actual_certificate_hash,
        ));
    }

    None
}

fn check_generated_source_hash(
    module_index: usize,
    module: &PackageModule,
    source_hash: PackageHash,
) -> Option<CommandDiagnostic> {
    if source_hash != module.expected_source_hash {
        return Some(hash_mismatch(
            "source_hash_mismatch",
            format!("modules[{module_index}].expected_source_hash"),
            "expected_source_hash",
            module.expected_source_hash,
            source_hash,
        ));
    }
    None
}

fn reuse_checked_terminal_certificate_for_check(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    module: &PackageModule,
    lock_entries: &mut Vec<PackageLockEntry>,
) -> Option<CommandDiagnostic> {
    let bytes = match read_certificate_bytes(
        loaded,
        &module.certificate,
        format!("modules[{module_index}].certificate"),
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => return Some(*diagnostic),
    };
    let certificate = match npa_cert::decode_module_cert(&bytes) {
        Ok(certificate) => certificate,
        Err(error) => {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::Build, "certificate_decode_failed")
                    .with_module(module.module.as_dotted())
                    .with_path(render_package_path(&module.certificate))
                    .with_actual_value(format!("{error:?}")),
            );
        }
    };
    if let Some(diagnostic) =
        check_generated_axiom_policy(loaded, module_index, module, &certificate)
    {
        return Some(diagnostic);
    }
    if let Some(diagnostic) =
        check_generated_manifest_hashes(module_index, module, &certificate, &bytes)
    {
        return Some(diagnostic);
    }
    if certificate.header.module != module.module {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::Build, "certificate_module_mismatch")
                .with_module(module.module.as_dotted())
                .with_path(format!("modules[{module_index}].certificate"))
                .with_field("module")
                .with_expected_value(module.module.as_dotted())
                .with_actual_value(certificate.header.module.as_dotted()),
        );
    }
    let imports = match package_lock_imports_for_certificate(
        &certificate.imports,
        &format!("modules[{module_index}].certificate.imports"),
        &module.module,
    ) {
        Ok(imports) => imports,
        Err(diagnostic) => return Some(*diagnostic),
    };
    lock_entries.push(PackageLockEntry {
        module: module.module.clone(),
        origin: PackageLockEntryOrigin::Local,
        certificate: module.certificate.clone(),
        certificate_file_hash: package_file_hash(&bytes),
        export_hash: PackageHash::from(certificate.hashes.export_hash),
        axiom_report_hash: PackageHash::from(certificate.hashes.axiom_report_hash),
        certificate_hash: PackageHash::from(certificate.hashes.certificate_hash),
        imports,
        package: None,
        version: None,
    });
    None
}

fn check_package_lock(
    loaded: &LoadedPackageRoot,
    regenerated_lock_json: &str,
) -> Option<CommandDiagnostic> {
    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    let full_lock_path = match join_package_path(&loaded.root, &lock_path, "package_lock.path") {
        Ok(path) => path,
        Err(diagnostic) => return Some(*diagnostic),
    };
    let lock_source = match fs::read_to_string(&full_lock_path) {
        Ok(source) => source,
        Err(_) => {
            return Some(
                CommandDiagnostic::error(DiagnosticKind::PackageLock, "package_lock_missing")
                    .with_path(PACKAGE_LOCK_PATH),
            );
        }
    };
    if let Err(error) = parse_package_lock_json(&lock_source) {
        return Some(
            CommandDiagnostic::from_package_lock_error(&error).with_path(PACKAGE_LOCK_PATH),
        );
    }
    if lock_source != regenerated_lock_json {
        return Some(
            CommandDiagnostic::error(DiagnosticKind::HashMismatch, "package_lock_stale")
                .with_path(PACKAGE_LOCK_PATH)
                .with_hashes(
                    format_package_hash(&package_file_hash(regenerated_lock_json.as_bytes())),
                    format_package_hash(&package_file_hash(lock_source.as_bytes())),
                ),
        );
    }
    None
}

fn prepare_build_check_cache_run(
    loaded: &LoadedPackageRoot,
    certificates: &[LocalCertificateBuildIdentity],
    cache_cwd: &Path,
) -> PackageBuildCheckCacheRun {
    let keyed_entries = package_build_check_cache_key_inputs(loaded, certificates);
    let cache_dir = cache_cwd.join(PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR);
    let lookups = keyed_entries
        .iter()
        .map(|entry| read_package_build_check_cache_lookup(&cache_dir, &entry.cache_key))
        .collect::<Vec<_>>();
    let mut summary = PackageBuildCheckCacheSummary::new(PackageBuildCheckCacheMode::ReadThrough);
    summary.live_builds = certificates.len();
    PackageBuildCheckCacheRun {
        cache_dir,
        keyed_entries,
        lookups,
        summary,
    }
}

fn build_check_result_with_optional_cache(
    root_display: String,
    cache_run: Option<PackageBuildCheckCacheRun>,
    diagnostic: Option<CommandDiagnostic>,
) -> CommandResult {
    let status = if diagnostic.is_some() {
        PackageBuildCheckCachedStatus::Rejected
    } else {
        PackageBuildCheckCachedStatus::Accepted
    };
    let reason = diagnostic
        .as_ref()
        .map(|diagnostic| diagnostic.reason_code.clone());

    let mut diagnostics = Vec::new();
    if let Some(diagnostic) = diagnostic {
        diagnostics.push(diagnostic);
    }
    if let Some(run) = cache_run {
        let summary = finalize_build_check_cache_run(run, status, reason.as_deref());
        diagnostics.push(package_build_check_cache_summary_diagnostic(&summary));
    }

    if status == PackageBuildCheckCachedStatus::Rejected {
        CommandResult::failed(COMMAND, root_display, diagnostics)
    } else {
        let mut result = CommandResult::passed(COMMAND, root_display);
        result.diagnostics = diagnostics;
        result
    }
}

fn finalize_build_check_cache_run(
    mut run: PackageBuildCheckCacheRun,
    status: PackageBuildCheckCachedStatus,
    diagnostic_reason: Option<&str>,
) -> PackageBuildCheckCacheSummary {
    for (keyed, lookup) in run.keyed_entries.iter().zip(run.lookups.iter()) {
        let expected_entry =
            package_build_check_cache_result_entry(keyed, status, diagnostic_reason);
        match lookup {
            PackageBuildCheckCacheLookup::Hit(entry)
                if package_build_check_cache_entries_equal(entry, &expected_entry) =>
            {
                run.summary.hits += 1;
            }
            PackageBuildCheckCacheLookup::Hit(_entry) => {
                run.summary.stale += 1;
                if write_package_build_check_cache_entry(&run.cache_dir, &expected_entry) {
                    run.summary.written += 1;
                }
            }
            PackageBuildCheckCacheLookup::Missing => {
                run.summary.misses += 1;
                if write_package_build_check_cache_entry(&run.cache_dir, &expected_entry) {
                    run.summary.written += 1;
                }
            }
            PackageBuildCheckCacheLookup::SchemaMiss => {
                run.summary.schema_misses += 1;
                if write_package_build_check_cache_entry(&run.cache_dir, &expected_entry) {
                    run.summary.written += 1;
                }
            }
            PackageBuildCheckCacheLookup::Stale => {
                run.summary.stale += 1;
                if write_package_build_check_cache_entry(&run.cache_dir, &expected_entry) {
                    run.summary.written += 1;
                }
            }
        }
    }
    run.summary
}

fn package_build_check_cache_entries_equal(
    actual: &PackageBuildCheckResultEntry,
    expected: &PackageBuildCheckResultEntry,
) -> bool {
    package_build_check_result_entry_json(actual) == package_build_check_result_entry_json(expected)
}

fn package_build_check_cache_key_inputs(
    loaded: &LoadedPackageRoot,
    certificates: &[LocalCertificateBuildIdentity],
) -> Vec<PackageBuildCheckKeyedEntry> {
    let manifest = loaded.validated.manifest();
    certificates
        .iter()
        .map(|certificate| {
            let module = &manifest.modules[certificate.module_index];
            let direct_imports = loaded.validated.graph().resolved_module_imports
                [certificate.module_index]
                .iter()
                .map(|import| PackageBuildCheckImportIdentity {
                    module: import.module.clone(),
                    export_hash: import.export_hash,
                    certificate_hash: import.certificate_hash,
                })
                .collect::<Vec<_>>();
            let key_input = PackageBuildCheckCacheKeyInput {
                schema: PACKAGE_BUILD_CHECK_CACHE_SCHEMA.to_owned(),
                tool_version: env!("CARGO_PKG_VERSION").to_owned(),
                tool_build_hash: package_build_check_tool_build_hash(),
                core_spec: manifest.core_spec.clone(),
                certificate_format: manifest.certificate_format.clone(),
                module: module.module.clone(),
                source_hash: certificate.source_hash,
                expected_source_hash: module.expected_source_hash,
                direct_imports,
                compiler_options: package_build_check_compiler_options(module),
                package_metadata_mode: "check".to_owned(),
                producer_profile: module.producer_profile.clone(),
                expected_certificate_file_hash: module.expected_certificate_file_hash,
                expected_export_hash: module.expected_export_hash,
                expected_axiom_report_hash: module.expected_axiom_report_hash,
                expected_certificate_hash: module.expected_certificate_hash,
            };
            let cache_key = package_build_check_cache_key(&key_input);
            PackageBuildCheckKeyedEntry {
                module: module.module.clone(),
                key_input,
                cache_key,
            }
        })
        .collect()
}

fn package_build_check_compiler_options(module: &PackageModule) -> Vec<String> {
    let mut options = vec![
        "frontend=human".to_owned(),
        "human_compile_options=default".to_owned(),
        "axiom_policy=package".to_owned(),
    ];
    if module.producer_profile.as_deref() == Some(LEGACY_STD_PACKAGE_PRODUCER_PROFILE) {
        options.push(format!(
            "producer_profile={LEGACY_STD_PACKAGE_PRODUCER_PROFILE}"
        ));
    }
    options
}

fn package_build_check_tool_build_hash() -> PackageHash {
    package_file_hash(
        format!(
            "schema=npa.package.build_check_tool_identity.v0.1\ncommand={COMMAND}\nversion={}\n",
            env!("CARGO_PKG_VERSION")
        )
        .as_bytes(),
    )
}

fn read_package_build_check_cache_lookup(
    cache_dir: &Path,
    cache_key: &str,
) -> PackageBuildCheckCacheLookup {
    let path = package_build_check_cache_entry_path(cache_dir, cache_key);
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return PackageBuildCheckCacheLookup::Missing;
        }
        Err(_) => return PackageBuildCheckCacheLookup::Stale,
    };
    match parse_package_build_check_result_entry_json(&source) {
        Ok(entry) if entry.cache_key == cache_key => {
            PackageBuildCheckCacheLookup::Hit(Box::new(entry))
        }
        Ok(_) => PackageBuildCheckCacheLookup::Stale,
        Err(error) if error.reason_code == PackageArtifactErrorReason::UnsupportedSchema => {
            PackageBuildCheckCacheLookup::SchemaMiss
        }
        Err(_) => PackageBuildCheckCacheLookup::Stale,
    }
}

fn write_package_build_check_cache_entry(
    cache_dir: &Path,
    entry: &PackageBuildCheckResultEntry,
) -> bool {
    if fs::create_dir_all(cache_dir).is_err() {
        return false;
    }
    let path = package_build_check_cache_entry_path(cache_dir, &entry.cache_key);
    let temp_index = NEXT_BUILD_CHECK_CACHE_WRITE_TEMP.fetch_add(1, Ordering::SeqCst);
    let temp_path = cache_dir.join(format!(
        ".{}.{}.tmp",
        entry.cache_key.trim_start_matches("sha256:"),
        temp_index
    ));
    let json = package_build_check_result_entry_json(entry);
    if fs::write(&temp_path, json).is_err() {
        return false;
    }
    match fs::rename(&temp_path, &path) {
        Ok(()) => true,
        Err(_) => {
            let _ = fs::remove_file(temp_path);
            false
        }
    }
}

fn package_build_check_cache_entry_path(cache_dir: &Path, cache_key: &str) -> PathBuf {
    cache_dir.join(format!("{cache_key}.json"))
}

fn package_build_check_cache_result_entry(
    keyed: &PackageBuildCheckKeyedEntry,
    status: PackageBuildCheckCachedStatus,
    diagnostic_reason: Option<&str>,
) -> PackageBuildCheckResultEntry {
    PackageBuildCheckResultEntry {
        schema: PACKAGE_BUILD_CHECK_RESULT_SCHEMA.to_owned(),
        cache_key: keyed.cache_key.clone(),
        trusted: false,
        build_evidence: false,
        key_input: keyed.key_input.clone(),
        status,
        diagnostic_reason: diagnostic_reason.map(ToOwned::to_owned),
        trust_boundary: format!(
            "cache entry for {} is not proof evidence or build evidence; live build comparison dominates",
            keyed.module.as_dotted()
        ),
    }
}

impl PackageBuildCheckCacheSummary {
    fn new(mode: PackageBuildCheckCacheMode) -> Self {
        Self {
            mode,
            hits: 0,
            misses: 0,
            stale: 0,
            schema_misses: 0,
            written: 0,
            live_builds: 0,
            trusted: false,
            build_evidence: false,
        }
    }

    fn diagnostic_value(&self) -> String {
        format!(
            "mode={};hits={};misses={};stale={};schema_misses={};written={};live_builds={};trusted={};build_evidence={}",
            self.mode.as_str(),
            self.hits,
            self.misses,
            self.stale,
            self.schema_misses,
            self.written,
            self.live_builds,
            self.trusted,
            self.build_evidence
        )
    }
}

fn package_build_check_cache_summary_diagnostic(
    summary: &PackageBuildCheckCacheSummary,
) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "build_check_cache_summary",
    )
    .with_field("build_check_cache")
    .with_actual_value(summary.diagnostic_value())
}

fn write_package_build(
    loaded: &LoadedPackageRoot,
    build: &PackageCertificateBuild,
) -> Option<CommandDiagnostic> {
    let mut pending = Vec::new();
    for certificate in &build.local_certificates {
        match prepare_pending_write(
            &loaded.root,
            &certificate.path,
            format!("modules[{}].certificate", certificate.module_index),
            &certificate.bytes,
            "certificate_write_failed",
            Some(certificate.module.clone()),
        ) {
            Ok(Some(write)) => pending.push(write),
            Ok(None) => {}
            Err(diagnostic) => {
                cleanup_pending_writes(&pending);
                return Some(*diagnostic);
            }
        }
    }

    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    match prepare_pending_write(
        &loaded.root,
        &lock_path,
        "package_lock.path",
        build.package_lock_json.as_bytes(),
        "package_lock_write_failed",
        None,
    ) {
        Ok(Some(write)) => pending.push(write),
        Ok(None) => {}
        Err(diagnostic) => {
            cleanup_pending_writes(&pending);
            return Some(*diagnostic);
        }
    }

    commit_pending_writes(&pending)
}

fn write_refreshed_package_build(
    loaded: &LoadedPackageRoot,
    build: &PackageCertificateRefreshBuild,
) -> Option<CommandDiagnostic> {
    let mut pending = Vec::new();
    let local_modules = match refresh_modules_by_manifest_order(
        &build.local_modules,
        loaded.validated.manifest().modules.len(),
    ) {
        Ok(local_modules) => local_modules,
        Err(diagnostic) => return Some(*diagnostic),
    };

    for module in local_modules {
        match prepare_pending_write(
            &loaded.root,
            &module.certificate_path,
            format!("modules[{}].certificate", module.module_index),
            &module.certificate_bytes,
            "certificate_write_failed",
            Some(module.module.clone()),
        ) {
            Ok(Some(write)) => pending.push(write),
            Ok(None) => {}
            Err(diagnostic) => {
                cleanup_pending_writes(&pending);
                return Some(*diagnostic);
            }
        }
    }

    let manifest_path = PackagePath::new(PACKAGE_MANIFEST_PATH);
    match prepare_pending_write(
        &loaded.root,
        &manifest_path,
        "$.manifest",
        build.refreshed_manifest_source.as_bytes(),
        "manifest_write_failed",
        None,
    ) {
        Ok(Some(write)) => pending.push(write),
        Ok(None) => {}
        Err(diagnostic) => {
            cleanup_pending_writes(&pending);
            return Some(*diagnostic);
        }
    }

    let lock_path = PackagePath::new(PACKAGE_LOCK_PATH);
    match prepare_pending_write(
        &loaded.root,
        &lock_path,
        "package_lock.path",
        build.package_lock_json.as_bytes(),
        "package_lock_write_failed",
        None,
    ) {
        Ok(Some(write)) => pending.push(write),
        Ok(None) => {}
        Err(diagnostic) => {
            cleanup_pending_writes(&pending);
            return Some(*diagnostic);
        }
    }

    commit_pending_writes(&pending)
}

fn prepare_pending_write(
    root: &Path,
    package_path: &PackagePath,
    manifest_field_path: impl Into<String>,
    bytes: &[u8],
    reason_code: &'static str,
    module: Option<Name>,
) -> Result<Option<PendingWrite>, Box<CommandDiagnostic>> {
    let full_path = join_package_path(root, package_path, manifest_field_path)?;
    let previous_bytes = match fs::read(&full_path) {
        Ok(existing) if existing == bytes => return Ok(None),
        Ok(existing) => Some(existing),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(_) => {
            return Err(Box::new(write_artifact_diagnostic(
                reason_code,
                package_path,
                module.as_ref(),
            )));
        }
    };

    if let Some(parent) = full_path.parent() {
        if fs::create_dir_all(parent).is_err() {
            return Err(Box::new(write_artifact_diagnostic(
                reason_code,
                package_path,
                module.as_ref(),
            )));
        }
    }

    let temp_path = temporary_write_path(&full_path);
    if fs::write(&temp_path, bytes).is_err() {
        return Err(Box::new(write_artifact_diagnostic(
            reason_code,
            package_path,
            module.as_ref(),
        )));
    }

    Ok(Some(PendingWrite {
        path: package_path.clone(),
        full_path,
        temp_path,
        reason_code,
        module,
        previous_bytes,
    }))
}

fn commit_pending_writes(pending: &[PendingWrite]) -> Option<CommandDiagnostic> {
    let mut committed = Vec::new();
    for write in pending {
        if fs::rename(&write.temp_path, &write.full_path).is_err() {
            cleanup_pending_writes(pending);
            rollback_pending_writes(&committed);
            return Some(write_artifact_diagnostic(
                write.reason_code,
                &write.path,
                write.module.as_ref(),
            ));
        }
        committed.push(write);
    }
    None
}

fn cleanup_pending_writes(pending: &[PendingWrite]) {
    for write in pending {
        let _ = fs::remove_file(&write.temp_path);
    }
}

fn rollback_pending_writes(committed: &[&PendingWrite]) {
    for write in committed.iter().rev() {
        match &write.previous_bytes {
            Some(bytes) => {
                let _ = fs::write(&write.full_path, bytes);
            }
            None => {
                let _ = fs::remove_file(&write.full_path);
            }
        }
    }
}

fn temporary_write_path(path: &Path) -> PathBuf {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("artifact");
    path.with_file_name(format!(".{file_name}.npa-build-certs.tmp"))
}

fn write_artifact_diagnostic(
    reason_code: &'static str,
    path: &PackagePath,
    module: Option<&Name>,
) -> CommandDiagnostic {
    let diagnostic =
        CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason_code).with_path(path.as_str());
    if let Some(module) = module {
        diagnostic.with_module(module.as_dotted())
    } else {
        diagnostic
    }
}

fn fallback_imported_source_interface(verified: &VerifiedModule) -> HumanImportedSourceInterface {
    let import = VerifiedImport::from(verified);
    let empty_span = Span::empty(FileId(0));
    let mut source_interface = HumanSourceInterface::new(import.module.clone());
    source_interface.declarations = import
        .exports
        .iter()
        .map(|export| HumanSourceDeclarationMetadata {
            kind: HumanSourceDeclarationKind::Imported,
            name: HumanName::new(export.name.0.clone(), empty_span),
            universe_params: export
                .universe_params
                .iter()
                .cloned()
                .map(|name| HumanUniverseParam {
                    name,
                    span: empty_span,
                })
                .collect(),
            binders: Vec::new(),
            decl_interface_hash: Some(export.decl_interface_hash),
            span: empty_span,
        })
        .collect();

    HumanImportedSourceInterface {
        module: import.module,
        export_hash: import.export_hash,
        certificate_hash: import.certificate_hash,
        source_interface,
    }
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn trim_package_build_heap() {
    // SAFETY: `malloc_trim(0)` asks glibc's allocator to return free heap pages
    // to the OS. It does not inspect or mutate Rust-owned live objects, and this
    // CLI-only call is a memory-pressure mitigation after large temporary proof
    // verification structures have been dropped.
    unsafe {
        libc::malloc_trim(0);
    }
}

#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
fn trim_package_build_heap() {}

fn frontend_build_failed(
    module_index: usize,
    module: &PackageModule,
    error: npa_frontend::HumanDiagnostic,
) -> CommandDiagnostic {
    let phase = error
        .payload
        .as_ref()
        .and_then(|payload| payload.phase)
        .map(|phase| phase.as_str())
        .unwrap_or("human_frontend");
    CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
        .with_module(module.module.as_dotted())
        .with_path(format!("modules[{module_index}].source"))
        .with_field(phase)
        .with_actual_value(error.message)
}

fn hash_mismatch(
    reason_code: &'static str,
    path: String,
    field: &'static str,
    expected: PackageHash,
    actual: PackageHash,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::HashMismatch, reason_code)
        .with_path(path)
        .with_field(field)
        .with_hashes(format_package_hash(&expected), format_package_hash(&actual))
}

#[cfg(test)]
mod tests {
    use super::{
        check_refreshed_certificate_import_identities, format_package_hash,
        normalize_allowed_refresh_hash_fields, parse_and_validate_manifest_str,
        refresh_manifest_hash_fields_for_modules, DiagnosticKind, ManifestHashRefreshIdentity,
        Name, PackageHash, PackageLockImport,
    };

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_updates_only_source_hash() {
        let old_source_hash = hash(1);
        let refreshed_source_hash = hash(2);
        let certificate_file_hash = hash(3);
        let export_hash = hash(4);
        let axiom_report_hash = hash(5);
        let certificate_hash = hash(6);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            refreshed_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            old_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );

        let refreshed_source = refresh_manifest_hash_fields_for_modules(
            &manifest_source,
            std::slice::from_ref(&identity),
        )
        .unwrap();

        assert!(refreshed_source.ends_with('\n'));
        assert!(refreshed_source.contains("# package comment"));
        assert!(refreshed_source.contains("# source pin"));
        assert!(refreshed_source.contains(&format!(
            "expected_source_hash = \"{}\"",
            format_package_hash(&refreshed_source_hash)
        )));
        assert!(!refreshed_source.contains(&format_package_hash(&old_source_hash)));
        let no_newline_source = manifest_source.trim_end_matches('\n').to_owned();
        let no_newline_refreshed = refresh_manifest_hash_fields_for_modules(
            &no_newline_source,
            std::slice::from_ref(&identity),
        )
        .unwrap();
        assert!(!no_newline_refreshed.ends_with('\n'));

        let crlf_source = manifest_source.replace('\n', "\r\n");
        let crlf_refreshed =
            refresh_manifest_hash_fields_for_modules(&crlf_source, std::slice::from_ref(&identity))
                .unwrap();
        assert!(crlf_refreshed.ends_with("\r\n"));
        assert!(!crlf_refreshed.replace("\r\n", "").contains('\n'));
        assert!(crlf_refreshed.contains(&format!(
            "expected_source_hash = \"{}\"",
            format_package_hash(&refreshed_source_hash)
        )));

        let original = parse_and_validate_manifest_str(&manifest_source).unwrap();
        let refreshed = parse_and_validate_manifest_str(&refreshed_source).unwrap();
        assert_eq!(
            refreshed.manifest().modules[0].expected_source_hash,
            refreshed_source_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_certificate_file_hash,
            certificate_file_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_export_hash,
            export_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_axiom_report_hash,
            axiom_report_hash
        );
        assert_eq!(
            refreshed.manifest().modules[0].expected_certificate_hash,
            certificate_hash
        );
        let mut normalized_refreshed = refreshed.manifest().clone();
        normalize_allowed_refresh_hash_fields(original.manifest(), &mut normalized_refreshed)
            .unwrap();
        assert_eq!(&normalized_refreshed, original.manifest());
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_rejects_non_string_hash_field() {
        let identity = refresh_identity(
            0,
            "Fixture.A",
            hash(11),
            hash(12),
            hash(13),
            hash(14),
            hash(15),
        );
        let manifest_source =
            fixture_manifest_source("Fixture.A", hash(1), hash(12), hash(13), hash(14), hash(15));
        let malformed_source = manifest_source.replace(
            &format!(
                "expected_source_hash = \"{}\" # source pin",
                format_package_hash(&hash(1))
            ),
            "expected_source_hash = 1 # source pin",
        );

        let error =
            refresh_manifest_hash_fields_for_modules(&malformed_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(
            error.path.as_deref(),
            Some("modules[0].expected_source_hash")
        );
        assert_eq!(error.field.as_deref(), Some("expected_source_hash"));
        assert_eq!(error.expected_value.as_deref(), Some("string"));
        assert_eq!(error.actual_value.as_deref(), Some("integer"));
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_rejects_missing_hash_field() {
        let identity = refresh_identity(
            0,
            "Fixture.A",
            hash(16),
            hash(17),
            hash(18),
            hash(19),
            hash(20),
        );
        let missing_line = format!(
            "expected_certificate_hash = \"{}\"\n",
            format_package_hash(&hash(20))
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            hash(16),
            hash(17),
            hash(18),
            hash(19),
            hash(20),
        );
        let malformed_source = manifest_source.replace(&missing_line, "");

        let error =
            refresh_manifest_hash_fields_for_modules(&malformed_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(
            error.path.as_deref(),
            Some("modules[0].expected_certificate_hash")
        );
        assert_eq!(error.field.as_deref(), Some("expected_certificate_hash"));
        assert_eq!(
            error.expected_value.as_deref(),
            Some("existing string hash field")
        );
        assert_eq!(error.actual_value.as_deref(), Some("missing"));
    }

    #[test]
    fn package_build_certs_write_refresh_manifest_rewrite_rejects_duplicate_hash_field() {
        let source_hash = hash(21);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            hash(22),
            hash(23),
            hash(24),
            hash(25),
            hash(26),
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            source_hash,
            hash(23),
            hash(24),
            hash(25),
            hash(26),
        );
        let duplicate_source = manifest_source.replace(
            &format!(
                "expected_source_hash = \"{}\" # source pin",
                format_package_hash(&source_hash)
            ),
            &format!(
                "expected_source_hash = \"{}\" # source pin\nexpected_source_hash = \"{}\"",
                format_package_hash(&source_hash),
                format_package_hash(&source_hash)
            ),
        );

        let error =
            refresh_manifest_hash_fields_for_modules(&duplicate_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(error.path.as_deref(), Some("npa-package.toml"));
        assert_eq!(error.field.as_deref(), Some("toml"));
    }

    #[test]
    fn package_build_certs_write_refresh_manifest_rewrite_rejects_module_order_mismatch() {
        let identity = refresh_identity(
            0,
            "Fixture.B",
            hash(31),
            hash(32),
            hash(33),
            hash(34),
            hash(35),
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            hash(30),
            hash(32),
            hash(33),
            hash(34),
            hash(35),
        );

        let error =
            refresh_manifest_hash_fields_for_modules(&manifest_source, &[identity]).unwrap_err();

        assert_eq!(error.kind, DiagnosticKind::PackageManifest);
        assert_eq!(error.reason_code, "manifest_refresh_failed");
        assert_eq!(error.path.as_deref(), Some("modules[0].module"));
        assert_eq!(error.field.as_deref(), Some("module"));
        assert_eq!(error.expected_value.as_deref(), Some("Fixture.B"));
        assert_eq!(error.actual_value.as_deref(), Some("Fixture.A"));
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_preserves_fresh_crlf_manifest() {
        let source_hash = hash(41);
        let certificate_file_hash = hash(42);
        let export_hash = hash(43);
        let axiom_report_hash = hash(44);
        let certificate_hash = hash(45);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );
        let manifest_source = fixture_manifest_source(
            "Fixture.A",
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        )
        .replace('\n', "\r\n");

        let refreshed_source = refresh_manifest_hash_fields_for_modules(
            &manifest_source,
            std::slice::from_ref(&identity),
        )
        .unwrap();

        assert_eq!(refreshed_source, manifest_source);
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_accepts_empty_modules_array() {
        let manifest_source = empty_modules_array_manifest_source();

        let refreshed_source = refresh_manifest_hash_fields_for_modules(&manifest_source, &[])
            .expect("empty modules array should refresh");

        assert_eq!(refreshed_source, manifest_source);
        let parsed = parse_and_validate_manifest_str(&refreshed_source).unwrap();
        assert!(parsed.manifest().modules.is_empty());
    }

    #[test]
    fn package_build_certs_check_refresh_manifest_rewrite_updates_inline_module_array() {
        let old_source_hash = hash(46);
        let refreshed_source_hash = hash(47);
        let certificate_file_hash = hash(48);
        let export_hash = hash(49);
        let axiom_report_hash = hash(50);
        let certificate_hash = hash(51);
        let identity = refresh_identity(
            0,
            "Fixture.A",
            refreshed_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );
        let manifest_source = inline_module_array_manifest_source(
            "Fixture.A",
            old_source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        );

        let refreshed_source = refresh_manifest_hash_fields_for_modules(
            &manifest_source,
            std::slice::from_ref(&identity),
        )
        .expect("inline module array should refresh");

        assert!(refreshed_source.contains("modules = ["));
        assert!(refreshed_source.contains("{ module = \"Fixture.A\""));
        assert!(!refreshed_source.contains("[[modules]]"));
        assert!(refreshed_source.contains(&format!(
            "expected_source_hash = \"{}\"",
            format_package_hash(&refreshed_source_hash)
        )));
        assert!(!refreshed_source.contains(&format_package_hash(&old_source_hash)));
        let parsed = parse_and_validate_manifest_str(&refreshed_source).unwrap();
        assert_eq!(
            parsed.manifest().modules[0].expected_source_hash,
            refreshed_source_hash
        );
    }

    #[test]
    fn package_build_certs_check_refresh_import_identity_allows_certificate_import_order() {
        let owner = Name::from_dotted("Fixture.C");
        let expected = vec![
            lock_import("Fixture.A", 51, 52),
            lock_import("Fixture.B", 53, 54),
        ];
        let actual = vec![
            certificate_import("Fixture.B", 53, 54),
            certificate_import("Fixture.A", 51, 52),
        ];

        let diagnostic =
            check_refreshed_certificate_import_identities(2, &owner, &expected, &actual);

        assert!(diagnostic.is_none());
    }

    #[test]
    fn package_build_certs_check_refresh_import_identity_deduplicates_expected_imports() {
        let owner = Name::from_dotted("Fixture.C");
        let expected = vec![
            lock_import("Fixture.A", 55, 56),
            lock_import("Fixture.A", 55, 56),
        ];
        let actual = vec![certificate_import("Fixture.A", 55, 56)];

        let diagnostic =
            check_refreshed_certificate_import_identities(2, &owner, &expected, &actual);

        assert!(diagnostic.is_none());
    }

    fn fixture_manifest_source(
        module: &str,
        source_hash: PackageHash,
        certificate_file_hash: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
    ) -> String {
        format!(
            r#"schema = "npa.package.v0.1" # package comment
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"

[policy]
allow_custom_axioms = false
allowed_axioms = []

[[modules]]
module = "{module}"
source = "Fixture/A/source.npa"
certificate = "Fixture/A/certificate.npcert"
imports = []
expected_source_hash = "{}" # source pin
expected_certificate_file_hash = "{}"
expected_export_hash = "{}"
expected_axiom_report_hash = "{}"
expected_certificate_hash = "{}"
"#,
            format_package_hash(&source_hash),
            format_package_hash(&certificate_file_hash),
            format_package_hash(&export_hash),
            format_package_hash(&axiom_report_hash),
            format_package_hash(&certificate_hash),
        )
    }

    fn inline_module_array_manifest_source(
        module: &str,
        source_hash: PackageHash,
        certificate_file_hash: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
    ) -> String {
        format!(
            r#"schema = "npa.package.v0.1" # package comment
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = [{{ module = "{module}", source = "Fixture/A/source.npa", certificate = "Fixture/A/certificate.npcert", imports = [], expected_source_hash = "{}", expected_certificate_file_hash = "{}", expected_export_hash = "{}", expected_axiom_report_hash = "{}", expected_certificate_hash = "{}" }}]

[policy]
allow_custom_axioms = false
allowed_axioms = []
"#,
            format_package_hash(&source_hash),
            format_package_hash(&certificate_file_hash),
            format_package_hash(&export_hash),
            format_package_hash(&axiom_report_hash),
            format_package_hash(&certificate_hash),
        )
    }

    fn empty_modules_array_manifest_source() -> String {
        r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
modules = []

[policy]
allow_custom_axioms = false
allowed_axioms = []
"#
        .to_owned()
    }

    fn refresh_identity(
        module_index: usize,
        module: &str,
        source_hash: PackageHash,
        certificate_file_hash: PackageHash,
        export_hash: PackageHash,
        axiom_report_hash: PackageHash,
        certificate_hash: PackageHash,
    ) -> ManifestHashRefreshIdentity {
        ManifestHashRefreshIdentity {
            module_index,
            module: Name::from_dotted(module),
            source_hash,
            certificate_file_hash,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        }
    }

    fn hash(byte: u8) -> PackageHash {
        PackageHash::new([byte; 32])
    }

    fn lock_import(
        module: &str,
        export_hash_seed: u8,
        certificate_hash_seed: u8,
    ) -> PackageLockImport {
        PackageLockImport {
            module: Name::from_dotted(module),
            export_hash: hash(export_hash_seed),
            certificate_hash: hash(certificate_hash_seed),
        }
    }

    fn certificate_import(
        module: &str,
        export_hash_seed: u8,
        certificate_hash_seed: u8,
    ) -> npa_cert::ImportEntry {
        npa_cert::ImportEntry {
            module: Name::from_dotted(module),
            export_hash: hash(export_hash_seed).into_bytes(),
            certificate_hash: Some(hash(certificate_hash_seed).into_bytes()),
        }
    }
}
