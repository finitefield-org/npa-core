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
    package_build_check_result_entry_json, package_file_hash,
    parse_package_build_check_result_entry_json, parse_package_lock_json,
    validate_package_lock_against_manifest_graph, PackageArtifactErrorReason,
    PackageBuildCheckCacheKeyInput, PackageBuildCheckCachedStatus, PackageBuildCheckImportIdentity,
    PackageBuildCheckResultEntry, PackageHash, PackageLockArtifact, PackageLockEntry,
    PackageLockEntryOrigin, PackageLockImport, PackageLockManifest, PackageLockManifestReference,
    PackageModule, PackagePath, PACKAGE_BUILD_CHECK_CACHE_LAYOUT_DIR,
    PACKAGE_BUILD_CHECK_CACHE_SCHEMA, PACKAGE_BUILD_CHECK_RESULT_SCHEMA, PACKAGE_LOCK_SCHEMA,
};

use crate::args::{PackageBuildCertsOptions, PackageBuildCheckCacheMode, PackageCommonOptions};
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{join_package_path, render_package_path};
use crate::package::{load_package_root, LoadedPackageRoot};

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
}

/// Run `package build-certs`.
pub fn run_package_build_certs(options: PackageBuildCertsOptions) -> CommandResult {
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

fn prepare_pending_write(
    root: &Path,
    package_path: &PackagePath,
    manifest_field_path: impl Into<String>,
    bytes: &[u8],
    reason_code: &'static str,
    module: Option<Name>,
) -> Result<Option<PendingWrite>, Box<CommandDiagnostic>> {
    let full_path = join_package_path(root, package_path, manifest_field_path)?;
    match fs::read(&full_path) {
        Ok(existing) if existing == bytes => return Ok(None),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(_) => {
            return Err(Box::new(write_artifact_diagnostic(
                reason_code,
                package_path,
                module.as_ref(),
            )));
        }
    }

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
    }))
}

fn commit_pending_writes(pending: &[PendingWrite]) -> Option<CommandDiagnostic> {
    for write in pending {
        if fs::rename(&write.temp_path, &write.full_path).is_err() {
            cleanup_pending_writes(pending);
            return Some(write_artifact_diagnostic(
                write.reason_code,
                &write.path,
                write.module.as_ref(),
            ));
        }
    }
    None
}

fn cleanup_pending_writes(pending: &[PendingWrite]) {
    for write in pending {
        let _ = fs::remove_file(&write.temp_path);
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
